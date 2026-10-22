//! GPU engine: the tiled solver with each tile computed by the compute shader `tile.wgsl` (wgpu,
//! through the existing graphics driver). Layout, tile order and openings come from `Tiled`; the
//! shader mirrors `layered::evaluate_row`. Each tile uploads only its input tiles.

use crate::layered::{binomials, MAX_NUMBERS};
use crate::tiled::{Layout, Tiled};
use crate::Outcome;
use wgpu::util::DeviceExt;

const SHADER: &str = include_str!("tile.wgsl");
const WORKGROUP_SIZE: usize = 64;
// Shader params layout: header fields, then top takes, then top input bases.
const P_HEADER: usize = 8;
const P_TOP_TAKE: usize = P_HEADER;
const P_TOP_BASE: usize = P_TOP_TAKE + MAX_NUMBERS;
const PARAMS_LEN: usize = P_TOP_BASE + MAX_NUMBERS;
const BYTES_PER_WORD: u64 = 4;

pub struct Gpu {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    binom: wgpu::Buffer,
    max_groups: usize,
    pub adapter: String,
}

impl Gpu {
    pub fn new() -> Result<Self, String> {
        pollster::block_on(Self::init())
    }

    async fn init() -> Result<Self, String> {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
        let adapter = instance
            .request_adapter(&wgpu::RequestAdapterOptions {
                power_preference: wgpu::PowerPreference::HighPerformance,
                ..Default::default()
            })
            .await
            .map_err(|e| e.to_string())?;
        let limits = adapter.limits();
        let (device, queue) = adapter
            .request_device(&wgpu::DeviceDescriptor {
                label: Some("catch-up"),
                required_features: wgpu::Features::empty(),
                required_limits: limits.clone(),
                memory_hints: wgpu::MemoryHints::Performance,
                trace: wgpu::Trace::Off,
            })
            .await
            .map_err(|e| e.to_string())?;
        let module = device.create_shader_module(wgpu::ShaderModuleDescriptor {
            label: Some("tile"),
            source: wgpu::ShaderSource::Wgsl(SHADER.into()),
        });
        let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
            label: Some("tile"),
            layout: None,
            module: &module,
            entry_point: Some("main"),
            compilation_options: Default::default(),
            cache: None,
        });
        let flat: Vec<u32> = binomials().iter().flatten().map(|&c| u32::try_from(c).expect("binomial fits u32")).collect();
        let binom = storage(&device, "binom", &flat);
        let info = adapter.get_info();
        Ok(Gpu {
            device,
            queue,
            pipeline,
            binom,
            max_groups: limits.max_compute_workgroups_per_dimension as usize,
            adapter: format!("{} ({:?})", info.name, info.backend),
        })
    }

    /// Runs the shader on one tile of `rows` rows and copies the result into `out`.
    fn tile(&self, numbers: &wgpu::Buffer, params: &mut [u32; PARAMS_LEN], inputs: &[u32], rows: usize, out: &mut [u32]) {
        let groups = rows.div_ceil(WORKGROUP_SIZE);
        let groups_x = groups.min(self.max_groups);
        let groups_y = groups.div_ceil(groups_x);
        params[7] = (groups_x * WORKGROUP_SIZE) as u32;
        let params_buf = storage(&self.device, "params", params);
        // Bindings must be non-empty.
        let inputs_buf = storage(&self.device, "inputs", if inputs.is_empty() { &[0] } else { inputs });
        let size = out.len() as u64 * BYTES_PER_WORD;
        let out_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("out"),
            size,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("staging"),
            size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let layout = self.pipeline.get_bind_group_layout(0);
        let bind = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("tile"),
            layout: &layout,
            entries: &[
                entry(0, &params_buf),
                entry(1, numbers),
                entry(2, &self.binom),
                entry(3, &inputs_buf),
                entry(4, &out_buf),
            ],
        });
        let mut encoder = self.device.create_command_encoder(&wgpu::CommandEncoderDescriptor { label: Some("tile") });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor { label: Some("tile"), timestamp_writes: None });
            pass.set_pipeline(&self.pipeline);
            pass.set_bind_group(0, &bind, &[]);
            pass.dispatch_workgroups(groups_x as u32, groups_y as u32, 1);
        }
        encoder.copy_buffer_to_buffer(&out_buf, 0, &staging, 0, size);
        self.queue.submit(Some(encoder.finish()));
        let slice = staging.slice(..);
        slice.map_async(wgpu::MapMode::Read, |r| r.expect("map staging buffer"));
        self.device.poll(wgpu::PollType::Wait).expect("GPU poll");
        out.copy_from_slice(bytemuck::cast_slice(&slice.get_mapped_range()));
        staging.unmap();
    }
}

fn storage(device: &wgpu::Device, label: &str, data: &[u32]) -> wgpu::Buffer {
    device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
        label: Some(label),
        contents: bytemuck::cast_slice(data),
        usage: wgpu::BufferUsages::STORAGE,
    })
}

fn entry(binding: u32, buffer: &wgpu::Buffer) -> wgpu::BindGroupEntry<'_> {
    wgpu::BindGroupEntry { binding, resource: buffer.as_entire_binding() }
}

impl Tiled {
    /// Same as `run`, with every tile computed on the GPU.
    pub fn run_gpu(&self, gpu: &Gpu, mut on_layer: impl FnMut(usize, &Layout, &[u32])) -> (Layout, Vec<u32>) {
        let low_numbers: Vec<u32> = self.numbers[..self.low].iter().map(|&x| x as u32).collect();
        let numbers = storage(&gpu.device, "numbers", if low_numbers.is_empty() { &[0] } else { &low_numbers });
        let mut prev_layout = Layout { offsets: Vec::new(), rows: 0 };
        let mut prev: Vec<u32> = Vec::new();
        for k in 0..self.n() {
            let layout = self.layout(k);
            let mut cur = vec![0u32; layout.rows * self.words];
            for (pattern, offset) in layout.offsets.iter().enumerate() {
                let Some(offset) = *offset else { continue };
                let t = pattern.count_ones() as usize;
                let m = k - t;
                let rows = self.tile_rows(k, t);
                let mut params = [0u32; PARAMS_LEN];
                let mut inputs: Vec<u32> = Vec::new();
                // Tile T of layer k − 1 (low moves), then tiles T − b (top moves).
                if m > 0 {
                    let start = prev_layout.offsets[pattern].expect("tile T exists");
                    inputs.extend_from_slice(&prev[start * self.words..(start + self.tile_rows(k - 1, t)) * self.words]);
                }
                let mut p = pattern;
                for q in 0..t {
                    let b = p.trailing_zeros() as usize;
                    p &= p - 1;
                    let start = prev_layout.offsets[pattern & !(1 << b)].expect("tile T − b exists");
                    params[P_TOP_TAKE + q] = self.numbers[self.low + b] as u32;
                    params[P_TOP_BASE + q] = (inputs.len() / self.words) as u32;
                    inputs.extend_from_slice(&prev[start * self.words..(start + rows) * self.words]);
                }
                params[..7].copy_from_slice(&[m as u32, t as u32, self.low as u32, self.max_gap as u32, self.words as u32, rows as u32, 0]);
                gpu.tile(&numbers, &mut params, &inputs, rows, &mut cur[offset * self.words..(offset + rows) * self.words]);
            }
            on_layer(k, &layout, &cur);
            prev = cur;
            prev_layout = layout;
        }
        (prev_layout, prev)
    }

    pub fn openings_gpu(&self, gpu: &Gpu) -> Vec<(u64, Outcome)> {
        if self.n() == 0 {
            return Vec::new();
        }
        let (layout, last) = self.run_gpu(gpu, |_, _, _| {});
        self.openings_from(&layout, &last)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interval;

    const FULL_TABLE_MAX_N: u64 = 10;
    const OPENINGS_MAX_N: u64 = 18;

    /// GPU tests skip (with a message) on machines without a usable adapter.
    fn gpu() -> Option<Gpu> {
        Gpu::new().map_err(|e| eprintln!("no GPU, skipping: {e}")).ok()
    }

    #[test]
    fn every_layer_matches_cpu() {
        let Some(gpu) = gpu() else { return };
        for n in 0..=FULL_TABLE_MAX_N {
            for top in [0, 1, 3, n as usize].into_iter().filter(|&t| t <= n as usize) {
                let tiled = Tiled::new(&interval(n), top);
                let mut cpu_layers: Vec<Vec<u32>> = Vec::new();
                tiled.run(|_, _, layer| cpu_layers.push(layer.to_vec()));
                tiled.run_gpu(&gpu, |k, _, layer| assert_eq!(layer, &cpu_layers[k][..], "n {n} top {top} layer {k}"));
            }
        }
    }

    #[test]
    fn openings_match_cpu() {
        let Some(gpu) = gpu() else { return };
        for n in 0..=OPENINGS_MAX_N {
            let tiled = Tiled::new(&interval(n), (n as usize).min(6));
            assert_eq!(tiled.openings_gpu(&gpu), tiled.openings(), "n {n}");
        }
    }
}
