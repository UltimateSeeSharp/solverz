//! CUDA engine: the layered solver with each layer computed by the kernel in `layered.cu`,
//! compiled at startup by NVRTC. Layers stay on the GPU; the layout is `Layered`'s, so layers
//! compare word for word with the CPU engine.

use crate::layered::{Layered, MAX_NUMBERS};
use crate::Outcome;
use cudarc::driver::{CudaContext, CudaFunction, CudaStream, LaunchConfig, PushKernelArg};
use cudarc::nvrtc::compile_ptx;
use std::sync::Arc;

const KERNEL_SOURCE: &str = include_str!("layered.cu");
const KERNEL_NAME: &str = "layer";
const THREADS_PER_BLOCK: u32 = 256;
const BINOM_STRIDE: usize = MAX_NUMBERS + 2;

pub struct Cuda {
    stream: Arc<CudaStream>,
    layer: CudaFunction,
    pub device: String,
}

fn err(e: impl std::fmt::Debug) -> String {
    format!("{e:?}")
}

impl Cuda {
    pub fn new() -> Result<Self, String> {
        let ctx = CudaContext::new(0).map_err(err)?;
        let module = ctx.load_module(compile_ptx(KERNEL_SOURCE).map_err(err)?).map_err(err)?;
        let layer = module.load_function(KERNEL_NAME).map_err(err)?;
        let (free, total) = ctx.mem_get_info().map_err(err)?;
        let device = format!("{} ({} of {} MiB free)", ctx.name().map_err(err)?, free >> 20, total >> 20);
        Ok(Cuda { stream: ctx.default_stream(), layer, device })
    }
}

impl Layered {
    /// Same as `run`, with every layer computed on the GPU. Layers are copied back only for
    /// `on_layer` (pass `None` to skip) and for the final layer, which is returned.
    pub fn run_cuda(&self, cuda: &Cuda, mut on_layer: Option<&mut dyn FnMut(usize, &[u32])>) -> Result<Vec<u32>, String> {
        let stream = &cuda.stream;
        let n = self.n();
        let numbers: Vec<u32> = self.numbers.iter().map(|&x| x as u32).collect();
        let binom: Vec<u64> = self.binom.iter().flat_map(|row| row.iter().copied()).collect();
        assert_eq!(binom.len() % BINOM_STRIDE, 0, "binomial rows have the kernel's stride");
        // Device buffers must not be empty.
        let d_numbers = stream.clone_htod(if numbers.is_empty() { &[0u32][..] } else { &numbers }).map_err(err)?;
        let d_binom = stream.clone_htod(&binom).map_err(err)?;
        let mut prev = stream.alloc_zeros::<u32>(1).map_err(err)?;
        for k in 0..n {
            let rows = self.layer_len(k) as u64;
            let mut cur = stream.alloc_zeros::<u32>(rows as usize * self.words_per_row).map_err(err)?;
            let cfg = LaunchConfig {
                grid_dim: (rows.div_ceil(THREADS_PER_BLOCK as u64) as u32, 1, 1),
                block_dim: (THREADS_PER_BLOCK, 1, 1),
                shared_mem_bytes: 0,
            };
            let (n32, k32, gap32, words32) = (n as u32, k as u32, self.max_gap as u32, self.words_per_row as u32);
            let mut launch = stream.launch_builder(&cuda.layer);
            launch.arg(&d_numbers).arg(&d_binom).arg(&prev).arg(&mut cur);
            launch.arg(&n32).arg(&k32).arg(&rows).arg(&gap32).arg(&words32);
            // SAFETY: the argument list matches `layer` in layered.cu, and every buffer is sized for
            // the rows the kernel touches (prev: layer k - 1, cur: layer k).
            unsafe { launch.launch(cfg) }.map_err(err)?;
            if let Some(f) = on_layer.as_mut() {
                f(k, &stream.clone_dtoh(&cur).map_err(err)?);
            }
            prev = cur;
        }
        stream.clone_dtoh(&prev).map_err(err)
    }

    pub fn openings_cuda(&self, cuda: &Cuda) -> Result<Vec<(u64, Outcome)>, String> {
        if self.n() == 0 {
            return Ok(Vec::new());
        }
        let last = self.run_cuda(cuda, None)?;
        Ok(self.openings_from(&last))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interval;

    const FULL_TABLE_MAX_N: u64 = 12;
    const OPENINGS_MAX_N: u64 = 20;
    const SUBSET_UNIVERSE: u64 = 8;

    /// CUDA tests skip (with a message) on machines without a usable device.
    fn cuda() -> Option<Cuda> {
        Cuda::new().map_err(|e| eprintln!("no CUDA device, skipping: {e}")).ok()
    }

    #[test]
    fn every_layer_matches_cpu() {
        let Some(cuda) = cuda() else { return };
        for n in 0..=FULL_TABLE_MAX_N {
            let layered = Layered::new(&interval(n));
            let mut cpu: Vec<Vec<u32>> = Vec::new();
            layered.run(|_, layer| cpu.push(layer.to_vec()));
            let mut check = |k: usize, layer: &[u32]| assert_eq!(layer, &cpu[k][..], "n {n} layer {k}");
            layered.run_cuda(&cuda, Some(&mut check)).unwrap();
        }
    }

    #[test]
    fn openings_match_cpu() {
        let Some(cuda) = cuda() else { return };
        for n in 0..=OPENINGS_MAX_N {
            let layered = Layered::new(&interval(n));
            assert_eq!(layered.openings_cuda(&cuda).unwrap(), layered.openings(), "n {n}");
        }
        for bits in 0u32..(1 << SUBSET_UNIVERSE) {
            let set: Vec<u64> = (1..=SUBSET_UNIVERSE).filter(|&x| bits >> (x - 1) & 1 == 1).collect();
            let layered = Layered::new(&set);
            assert_eq!(layered.openings_cuda(&cuda).unwrap(), layered.openings(), "set {set:?}");
        }
    }
}
