//! Compact tiled engine on the GPU, for sets too large for two whole layers in VRAM. Tiles as in
//! `Tiled`, but a row keeps only the gaps of one parity: scores only grow, so the gap
//! g = s_opp − s_me ≡ s_opp + s_me = taken (mod 2), and the mask fixes what was taken. Cell i of a
//! row is gap p + 2i (p its parity); cells are packed in base 3, 5 per byte, so a row is one word
//! up to max gap 39 (2-bit cells would double the storage for N = 32..39). Each output tile is one
//! launch of `tile` (`tiled.cu`), which evaluates all cells of a row at once on bit planes. Layers
//! are stored tile by tile, zstd-compressed (lossless, checksummed), in host RAM up to its budget
//! and in a file beyond; input tiles are cached in VRAM uncompressed, output
//! tiles run in popcount order, and the cache evicts the tile needed farthest ahead (the schedule
//! is known). Three streams overlap upload, compute and download; threads overlap file I/O.

use crate::layered::{binomials_upto, decode, rank};
use crate::Outcome;
use cudarc::driver::sys::CUevent_flags;
use cudarc::driver::{
    CudaContext, CudaEvent, CudaFunction, CudaSlice, CudaStream, DevicePtr, DeviceRepr, LaunchConfig,
    PinnedHostSlice, PushKernelArg,
};
use cudarc::nvrtc::{compile_ptx_with_opts, CompileOptions};
use rayon::prelude::*;
use std::collections::{BTreeSet, HashMap};
use std::fs::{File, OpenOptions};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc};
use std::time::Instant;

const KERNEL_SOURCE: &str = include_str!("tiled.cu");
const KERNEL_NAME: &str = "tile";
const THREADS_PER_BLOCK: u32 = 256;
pub const MAX_NUMBERS: usize = 40;
pub const MAX_TOP: usize = 16;
const BINOM_STRIDE: usize = MAX_NUMBERS + 2;
/// Cells of a row unpacked into a u64, 2 bits each.
const MAX_CELLS: usize = 32;
const CELLS_PER_BYTE: usize = 5;
const BYTES_PER_WORD: usize = 4;
const CELLS_PER_WORD: usize = CELLS_PER_BYTE * BYTES_PER_WORD;
const BASE: u32 = 3;
/// Stored tiles are cut into chunks of this many words, compressed independently so that all
/// threads share the work; a multiple of every row length.
const CHUNK_WORDS: usize = 1 << 16;
/// Page-locked host memory with default caching.
const PINNED_FLAGS: u32 = 0;
/// zstd's fastest regular level: layers compress to ~15% (N = 28) at several 100 MB/s per thread.
const ZSTD_LEVEL: i32 = 1;
/// Pinned staging buffers for uploads and for downloads.
const IN_STAGING: usize = 4;
const OUT_STAGING: usize = 3;
/// VRAM kept free beyond the cache and the output tiles in flight.
const VRAM_RESERVE_BYTES: usize = 512 << 20;
/// Largest tile; above it the staging buffers get unreasonable (raise `--top`).
const MAX_TILE_BYTES: usize = 1 << 30;
const GB: f64 = 1e9;
const DEFAULT_VRAM_CACHE_BYTES: usize = 6_000_000_000;
const DEFAULT_RAM_BYTES: usize = 16_000_000_000;
const DEFAULT_SPILL_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../scratch/tiled-cuda");

/// Resource limits and reporting.
pub struct Config {
    /// Input tiles cached on the GPU (capped by free VRAM).
    pub vram_cache_bytes: usize,
    /// Layers held in host RAM; a layer that would exceed it goes to a file in `spill_dir`.
    pub ram_bytes: usize,
    pub spill_dir: PathBuf,
    /// Print one line per layer to stderr.
    pub progress: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            vram_cache_bytes: DEFAULT_VRAM_CACHE_BYTES,
            ram_bytes: DEFAULT_RAM_BYTES,
            spill_dir: PathBuf::from(DEFAULT_SPILL_DIR),
            progress: false,
        }
    }
}

/// Traffic of one run, in bytes.
#[derive(Default, Debug)]
pub struct Stats {
    /// Uploaded to the GPU (input tiles, counting re-fetches after eviction).
    pub fetched: u64,
    pub disk_read: u64,
    pub disk_written: u64,
    /// Largest total of the layer files that existed at once.
    pub peak_disk: u64,
    /// Compressed size of all layers (RAM and file).
    pub stored: u64,
    /// GPU time spent in the kernel, summed over launches.
    pub kernel_ms: f64,
}

pub struct Gpu {
    ctx: Arc<CudaContext>,
    upload: Arc<CudaStream>,
    compute: Arc<CudaStream>,
    download: Arc<CudaStream>,
    tile: CudaFunction,
    pub device: String,
}

fn err(e: impl std::fmt::Debug) -> String {
    format!("{e:?}")
}

/// A closed channel means the other side stopped: workers then exit quietly, and the error that
/// stopped them is reported instead.
fn stopped<E>(_: E) -> String {
    "pipeline thread stopped".to_string()
}

impl Gpu {
    pub fn new() -> Result<Self, String> {
        let ctx = CudaContext::new(0).map_err(err)?;
        let defines = [
            format!("-DMAX_NUMBERS={MAX_NUMBERS}"),
            format!("-DMAX_TOP={MAX_TOP}"),
            format!("-DBINOM_STRIDE={BINOM_STRIDE}"),
        ];
        let opts = CompileOptions { options: defines.to_vec(), ..Default::default() };
        let module = ctx.load_module(compile_ptx_with_opts(KERNEL_SOURCE, opts).map_err(err)?).map_err(err)?;
        let tile = module.load_function(KERNEL_NAME).map_err(err)?;
        let (free, total) = ctx.mem_get_info().map_err(err)?;
        let device = format!("{} ({} of {} MiB free)", ctx.name().map_err(err)?, free >> 20, total >> 20);
        let (upload, compute, download) =
            (ctx.new_stream().map_err(err)?, ctx.new_stream().map_err(err)?, ctx.new_stream().map_err(err)?);
        Ok(Gpu { ctx, upload, compute, download, tile, device })
    }

    /// Marks the work queued on `stream` so far; the waiting thread sleeps instead of spinning.
    fn mark(&self, stream: &CudaStream) -> Result<CudaEvent, String> {
        stream.record_event(Some(CUevent_flags::CU_EVENT_BLOCKING_SYNC)).map_err(err)
    }
}

/// Kernel argument; layout matches `TileInputs` in tiled.cu.
#[repr(C)]
#[derive(Clone, Copy)]
struct TileInputs {
    same: u64,
    top: [u64; MAX_TOP],
    top_takes: [u32; MAX_TOP],
}

// SAFETY: plain old data with the C layout of `TileInputs` in tiled.cu.
unsafe impl DeviceRepr for TileInputs {}

/// A pinned host buffer and the GPU copy that last used it.
struct Staged {
    host: PinnedHostSlice<u32>,
    busy: Option<CudaEvent>,
}

impl Staged {
    fn wait(&mut self) -> Result<(), String> {
        if let Some(e) = self.busy.take() {
            e.synchronize().map_err(err)?;
        }
        Ok(())
    }
}

impl Drop for Staged {
    /// Never free host memory a copy still uses (error paths drop buffers mid-flight).
    fn drop(&mut self) {
        let _ = self.wait();
    }
}

/// A stored tile: its chunks of `CHUNK_WORDS`, each a zstd frame with a checksum.
enum Stored {
    Ram(Vec<Vec<u8>>),
    /// Byte offset in the layer file, then each chunk's length; chunks are contiguous.
    File(u64, Vec<usize>),
}

/// One layer, tile by tile, compressed: in RAM up to `ram_limit` bytes, the rest appended to a file.
pub struct Layer {
    k: usize,
    tiles: Vec<Option<Stored>>,
    /// Uncompressed size.
    words: usize,
    ram_limit: usize,
    ram_bytes: usize,
    disk_bytes: usize,
    spill_dir: PathBuf,
    file: Option<(File, PathBuf)>,
}

static LAYER_FILES: AtomicUsize = AtomicUsize::new(0);

fn as_bytes(words: &[u32]) -> &[u8] {
    // SAFETY: any u32 slice is a valid byte slice of four times the length.
    unsafe { std::slice::from_raw_parts(words.as_ptr().cast(), std::mem::size_of_val(words)) }
}

fn as_bytes_mut(words: &mut [u32]) -> &mut [u8] {
    // SAFETY: as in `as_bytes`; every byte pattern is a valid u32.
    unsafe { std::slice::from_raw_parts_mut(words.as_mut_ptr().cast(), std::mem::size_of_val(words)) }
}

#[cfg(windows)]
fn read_at(file: &File, mut buf: &mut [u8], mut offset: u64) -> std::io::Result<()> {
    use std::os::windows::fs::FileExt;
    while !buf.is_empty() {
        let n = file.seek_read(buf, offset)?;
        if n == 0 {
            return Err(std::io::ErrorKind::UnexpectedEof.into());
        }
        buf = &mut buf[n..];
        offset += n as u64;
    }
    Ok(())
}

#[cfg(windows)]
fn write_at(file: &File, mut buf: &[u8], mut offset: u64) -> std::io::Result<()> {
    use std::os::windows::fs::FileExt;
    while !buf.is_empty() {
        let n = file.seek_write(buf, offset)?;
        buf = &buf[n..];
        offset += n as u64;
    }
    Ok(())
}

#[cfg(unix)]
fn read_at(file: &File, buf: &mut [u8], offset: u64) -> std::io::Result<()> {
    std::os::unix::fs::FileExt::read_exact_at(file, buf, offset)
}

#[cfg(unix)]
fn write_at(file: &File, buf: &[u8], offset: u64) -> std::io::Result<()> {
    std::os::unix::fs::FileExt::write_all_at(file, buf, offset)
}

impl Layer {
    /// Whether any tile is in the file.
    pub fn on_disk(&self) -> bool {
        self.file.is_some()
    }

    fn ram_bytes(&self) -> usize {
        self.ram_bytes
    }

    fn disk_bytes(&self) -> usize {
        self.disk_bytes
    }

    /// Compressed bytes of a tile in the file (0 if in RAM).
    fn file_bytes(&self, pattern: usize) -> usize {
        match &self.tiles[pattern] {
            Some(Stored::File(_, lens)) => lens.iter().sum(),
            _ => 0,
        }
    }

    /// Compresses a tile on all threads and keeps it in RAM if the limit allows, else in the file.
    fn store(&mut self, pattern: usize, data: &[u32]) -> Result<(), String> {
        let chunks: Vec<Vec<u8>> = data
            .par_chunks(CHUNK_WORDS)
            .map_init(compressor, |c, chunk| c.as_mut().map_err(err)?.compress(as_bytes(chunk)).map_err(err))
            .collect::<Result<_, String>>()?;
        let len: usize = chunks.iter().map(Vec::len).sum();
        let stored = if self.ram_bytes + len <= self.ram_limit {
            self.ram_bytes += len;
            Stored::Ram(chunks)
        } else {
            if self.file.is_none() {
                std::fs::create_dir_all(&self.spill_dir).map_err(err)?;
                let id = LAYER_FILES.fetch_add(1, Ordering::Relaxed);
                let path = self.spill_dir.join(format!("layer-{}-{id}.bin", std::process::id()));
                let file = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(&path).map_err(err)?;
                self.file = Some((file, path));
            }
            let (file, _) = self.file.as_ref().expect("file just created");
            let offset = self.disk_bytes as u64;
            write_at(file, &chunks.concat(), offset).map_err(err)?;
            self.disk_bytes += len;
            Stored::File(offset, chunks.iter().map(Vec::len).collect())
        };
        self.tiles[pattern] = Some(stored);
        Ok(())
    }

    /// Decompresses a tile into `out` (its exact size) on all threads.
    fn load(&self, pattern: usize, out: &mut [u32]) -> Result<(), String> {
        let read;
        let chunks: Vec<&[u8]> = match self.tiles[pattern].as_ref().expect("tile stored") {
            Stored::Ram(chunks) => chunks.iter().map(Vec::as_slice).collect(),
            Stored::File(offset, lens) => {
                let (file, _) = self.file.as_ref().expect("layer has a file");
                let mut bytes = vec![0u8; lens.iter().sum()];
                read_at(file, &mut bytes, *offset).map_err(err)?;
                read = bytes;
                let mut rest = read.as_slice();
                lens.iter()
                    .map(|&len| {
                        let (chunk, tail) = rest.split_at(len);
                        rest = tail;
                        chunk
                    })
                    .collect()
            }
        };
        assert_eq!(chunks.len(), out.len().div_ceil(CHUNK_WORDS), "chunk count");
        chunks.into_par_iter().zip(out.par_chunks_mut(CHUNK_WORDS)).try_for_each_init(decompressor, |d, (src, dst)| {
            let want = std::mem::size_of_val(dst);
            let got = d.as_mut().map_err(err)?.decompress_to_buffer(src, as_bytes_mut(dst)).map_err(err)?;
            if got == want { Ok(()) } else { Err(format!("chunk decompressed to {got} bytes, expected {want}")) }
        })
    }
}

fn compressor() -> std::io::Result<zstd::bulk::Compressor<'static>> {
    let mut c = zstd::bulk::Compressor::new(ZSTD_LEVEL)?;
    c.include_checksum(true)?;
    Ok(c)
}

fn decompressor() -> std::io::Result<zstd::bulk::Decompressor<'static>> {
    zstd::bulk::Decompressor::new()
}

impl Drop for Layer {
    fn drop(&mut self) {
        if let Some((_, path)) = &self.file {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// One output tile: the input tiles to evict and to fetch first, then the launch.
struct Step {
    pattern: usize,
    evict: Vec<usize>,
    fetch: Vec<usize>,
}

pub struct TiledCuda {
    numbers: Vec<u64>,
    top: usize,
    low: usize,
    max_gap: usize,
    cells: usize,
    words: usize,
    total_parity: usize,
    binom: Vec<Vec<u64>>,
}

impl TiledCuda {
    /// `top` = how many of the highest positions define the tiles, as in `Tiled`.
    pub fn new(numbers: &[u64], top: usize) -> Self {
        assert!(numbers.len() <= MAX_NUMBERS, "at most {MAX_NUMBERS} numbers");
        assert!(numbers.iter().all(|&x| x > 0), "numbers must be positive");
        assert!(top <= numbers.len().min(MAX_TOP), "top must be at most the number count and {MAX_TOP}");
        let max_gap = numbers.iter().copied().max().unwrap_or(0) as usize;
        let cells = max_gap / 2 + 1;
        assert!(cells <= MAX_CELLS, "max gap at most {}", 2 * MAX_CELLS - 1);
        TiledCuda {
            numbers: numbers.to_vec(),
            top,
            low: numbers.len() - top,
            max_gap,
            cells,
            words: cells.div_ceil(CELLS_PER_WORD),
            total_parity: (numbers.iter().sum::<u64>() % 2) as usize,
            binom: binomials_upto(MAX_NUMBERS),
        }
    }

    pub fn n(&self) -> usize {
        self.numbers.len()
    }

    /// Positions stored: every mask, at the gaps of its parity.
    pub fn positions(&self) -> u64 {
        // Masks by parity of their sum.
        let (mut even, mut odd) = (1u64, 0u64);
        for &x in &self.numbers {
            (even, odd) = if x % 2 == 1 { (even + odd, even + odd) } else { (2 * even, 2 * odd) };
        }
        let cells = |p: usize| if p > self.max_gap { 0 } else { ((self.max_gap - p) / 2 + 1) as u64 };
        even * cells(self.total_parity) + odd * cells(self.total_parity ^ 1)
    }

    /// Rows of tile (k, T) with |T| = t: low masks with k − t bits.
    fn tile_rows(&self, k: usize, t: usize) -> usize {
        if t > k || k - t > self.low { 0 } else { self.binom[self.low][k - t] as usize }
    }

    fn tile_words(&self, k: usize, pattern: usize) -> usize {
        self.tile_rows(k, pattern.count_ones() as usize) * self.words
    }

    fn max_tile_words(&self) -> usize {
        (0..=self.low).map(|m| self.binom[self.low][m] as usize).max().unwrap_or(1) * self.words
    }

    /// Tiles of layer k in computing order: by number of top positions left, then pattern.
    fn schedule(&self, k: usize) -> Vec<usize> {
        let mut order: Vec<usize> = (0..1usize << self.top).filter(|&p| self.tile_words(k, p) > 0).collect();
        order.sort_by_key(|&p| (p.count_ones(), p));
        order
    }

    /// Tiles of layer k − 1 that tile (k, pattern) reads: `pattern` for low moves (if any low
    /// number is left), then pattern − b for each top bit b, ascending.
    fn inputs(&self, k: usize, pattern: usize) -> Vec<usize> {
        let t = pattern.count_ones() as usize;
        let mut inputs = Vec::with_capacity(t + 1);
        if k > t {
            inputs.push(pattern);
        }
        let mut p = pattern;
        while p != 0 {
            inputs.push(pattern & !(1 << p.trailing_zeros()));
            p &= p - 1;
        }
        inputs
    }

    /// The most input words any tile of layer k needs at once.
    fn working_set_words(&self, k: usize) -> usize {
        let input_words = |ins: Vec<usize>| ins.iter().map(|&q| self.tile_words(k - 1, q)).sum();
        if k == 0 { 0 } else { self.schedule(k).into_iter().map(|p| input_words(self.inputs(k, p))).max().unwrap_or(0) }
    }

    /// Fetches and evictions for layer k with `cache_words` of VRAM: Belady's rule, evict the
    /// cached tile whose next use is farthest ahead (or never).
    fn plan(&self, k: usize, cache_words: usize) -> Result<Vec<Step>, String> {
        let order = self.schedule(k);
        let inputs: Vec<Vec<usize>> = order.iter().map(|&p| if k == 0 { Vec::new() } else { self.inputs(k, p) }).collect();
        let mut uses: Vec<Vec<usize>> = vec![Vec::new(); 1 << self.top];
        for (i, ins) in inputs.iter().enumerate() {
            for &q in ins {
                uses[q].push(i);
            }
        }
        let mut used_count = vec![0usize; 1 << self.top];
        let mut key: Vec<Option<usize>> = vec![None; 1 << self.top];
        let mut cached: BTreeSet<(usize, usize)> = BTreeSet::new();
        let mut used = 0;
        let mut steps = Vec::with_capacity(order.len());
        for (i, (&pattern, ins)) in order.iter().zip(&inputs).enumerate() {
            let mut step = Step { pattern, evict: Vec::new(), fetch: Vec::new() };
            for &q in ins {
                if key[q].is_some() {
                    continue;
                }
                let need = self.tile_words(k - 1, q);
                while used + need > cache_words {
                    let Some(&(next, victim)) = cached.last() else {
                        return Err(format!("tile of {} MB exceeds the VRAM cache; raise --top", (need * BYTES_PER_WORD) >> 20));
                    };
                    if next == i {
                        let ws = self.working_set_words(k) * BYTES_PER_WORD;
                        return Err(format!("layer {k} needs {} MB of input tiles at once; raise --top", ws >> 20));
                    }
                    cached.remove(&(next, victim));
                    key[victim] = None;
                    used -= self.tile_words(k - 1, victim);
                    step.evict.push(victim);
                }
                cached.insert((i, q));
                key[q] = Some(i);
                used += need;
                step.fetch.push(q);
            }
            for &q in ins {
                used_count[q] += 1;
                let next = uses[q].get(used_count[q]).copied().unwrap_or(usize::MAX);
                cached.remove(&(key[q].expect("input is cached"), q));
                cached.insert((next, q));
                key[q] = Some(next);
            }
            steps.push(step);
        }
        Ok(steps)
    }

    /// Empty layer k, which may keep what RAM is left next to `ram_in_use`.
    fn new_layer(&self, k: usize, ram_in_use: usize, config: &Config) -> Layer {
        Layer {
            k,
            tiles: (0..1 << self.top).map(|_| None).collect(),
            words: self.schedule(k).into_iter().map(|p| self.tile_words(k, p)).sum(),
            ram_limit: config.ram_bytes.saturating_sub(ram_in_use),
            ram_bytes: 0,
            disk_bytes: 0,
            spill_dir: config.spill_dir.clone(),
            file: None,
        }
    }

    fn cell(row: &[u32], i: usize) -> u32 {
        let j = i % CELLS_PER_WORD;
        let byte = (row[i / CELLS_PER_WORD] >> (8 * (j / CELLS_PER_BYTE))) & 0xff;
        byte / BASE.pow((j % CELLS_PER_BYTE) as u32) % BASE
    }

    fn parity(&self, mask: u64) -> usize {
        let sum: u64 = (0..self.n()).filter(|&i| mask >> i & 1 == 1).map(|i| self.numbers[i]).sum();
        self.total_parity ^ (sum % 2) as usize
    }

    /// Mover's value with `mask` left, trailing by `gap`; `None` for a gap of the other parity,
    /// which no game reaches and the layer does not store.
    pub fn get(&self, layer: &Layer, mask: u64, gap: usize) -> Result<Option<Outcome>, String> {
        assert_eq!(mask.count_ones() as usize, layer.k, "mask belongs to layer {}", layer.k);
        if gap > self.max_gap || gap % 2 != self.parity(mask) {
            return Ok(None);
        }
        let low_mask = mask & ((1u64 << self.low) - 1);
        let pattern = (mask >> self.low) as usize;
        let mut tile = vec![0u32; self.tile_words(layer.k, pattern)];
        layer.load(pattern, &mut tile)?;
        Ok(Some(decode(Self::cell(&tile[rank(&self.binom, low_mask) * self.words..], gap / 2))))
    }

    /// Computes layers 0..=n−1, calling `on_layer` after each; returns layer n − 1.
    pub fn run(&self, gpu: &Gpu, config: &Config, mut on_layer: impl FnMut(&Layer)) -> Result<(Layer, Stats), String> {
        let mut stats = Stats::default();
        let max_tile = self.max_tile_words();
        assert_eq!(CHUNK_WORDS % self.words, 0, "rows never straddle chunks");
        if max_tile * BYTES_PER_WORD > MAX_TILE_BYTES {
            return Err(format!("tiles up to {} MB; raise --top", (max_tile * BYTES_PER_WORD) >> 20));
        }
        let (free, _) = gpu.ctx.mem_get_info().map_err(err)?;
        let reserve = OUT_STAGING * max_tile * BYTES_PER_WORD + VRAM_RESERVE_BYTES;
        let cache_words = config.vram_cache_bytes.min(free.saturating_sub(reserve)) / BYTES_PER_WORD;

        let numbers: Vec<u32> = self.numbers[..self.low].iter().map(|&x| x as u32).collect();
        let binom: Vec<u64> = self.binom.iter().flat_map(|row| row.iter().copied()).collect();
        assert_eq!(binom.len(), (MAX_NUMBERS + 1) * BINOM_STRIDE, "binomial rows have the kernel's stride");
        // Device buffers must not be empty.
        let d_numbers = gpu.compute.clone_htod(if numbers.is_empty() { &[0u32][..] } else { &numbers }).map_err(err)?;
        let d_binom = gpu.compute.clone_htod(&binom).map_err(err)?;
        let staging = |flags: u32, count: usize| -> Result<Vec<Staged>, String> {
            (0..count)
                // SAFETY: staging contents are always written (file read, RAM copy, download) before use.
                .map(|_| Ok(Staged { host: unsafe { gpu.ctx.alloc_pinned_with_flags(max_tile, flags) }.map_err(err)?, busy: None }))
                .collect()
        };
        // Plain pinned memory, not write-combined: decompression reads back what it just wrote, and
        // uncached reads made it ~80× slower.
        let mut pools = (staging(PINNED_FLAGS, IN_STAGING)?, staging(PINNED_FLAGS, OUT_STAGING)?);

        let mut prev: Option<Layer> = None;
        for k in 0..self.n() {
            let start = Instant::now();
            let plan = self.plan(k, cache_words)?;
            let out = self.new_layer(k, prev.as_ref().map_or(0, Layer::ram_bytes), config);
            let fetched: u64 = plan.iter().flat_map(|s| &s.fetch).map(|&q| (self.tile_words(k - 1, q) * BYTES_PER_WORD) as u64).sum();
            stats.fetched += fetched;
            if let Some(layer) = &prev {
                stats.disk_read += plan.iter().flat_map(|s| &s.fetch).map(|&q| layer.file_bytes(q) as u64).sum::<u64>();
            }
            let (out, kernel_ms) = self.compute_layer(gpu, k, &plan, prev.as_ref(), out, &mut pools, &d_numbers, &d_binom)?;
            stats.kernel_ms += kernel_ms;
            stats.disk_written += out.disk_bytes() as u64;
            stats.stored += (out.ram_bytes() + out.disk_bytes()) as u64;
            let disk_now = prev.as_ref().map_or(0, Layer::disk_bytes) + out.disk_bytes();
            stats.peak_disk = stats.peak_disk.max(disk_now as u64);
            if config.progress {
                eprintln!(
                    "  layer {k:2}: {:5} tiles, {:6.2} GB -> {:5.2} GB in RAM + {:5.2} GB in file, fetched {:6.2} GB, {:7} ms ({:7.0} ms in kernels)",
                    plan.len(),
                    (out.words * BYTES_PER_WORD) as f64 / GB,
                    out.ram_bytes() as f64 / GB,
                    out.disk_bytes() as f64 / GB,
                    fetched as f64 / GB,
                    start.elapsed().as_millis(),
                    kernel_ms
                );
            }
            on_layer(&out);
            prev = Some(out);
        }
        let last = match prev {
            Some(layer) => layer,
            None => self.new_layer(0, 0, config),
        };
        Ok((last, stats))
    }

    /// Runs one layer's plan: a reader thread stages input tiles, this thread uploads, launches and
    /// downloads, a writer thread stores the output tiles. Returns the layer and its kernel time.
    #[allow(clippy::too_many_arguments)]
    fn compute_layer(
        &self,
        gpu: &Gpu,
        k: usize,
        plan: &[Step],
        input: Option<&Layer>,
        mut output: Layer,
        pools: &mut (Vec<Staged>, Vec<Staged>),
        d_numbers: &CudaSlice<u32>,
        d_binom: &CudaSlice<u64>,
    ) -> Result<(Layer, f64), String> {
        let (free_in_tx, free_in_rx) = mpsc::channel::<Staged>();
        let (loaded_tx, loaded_rx) = mpsc::sync_channel::<(usize, Staged)>(IN_STAGING);
        let (free_out_tx, free_out_rx) = mpsc::channel::<Staged>();
        let (done_tx, done_rx) = mpsc::channel::<(usize, usize, Staged)>();
        for b in pools.0.drain(..) {
            free_in_tx.send(b).map_err(err)?;
        }
        for b in pools.1.drain(..) {
            free_out_tx.send(b).map_err(err)?;
        }
        let fetches: Vec<usize> = plan.iter().flat_map(|s| s.fetch.iter().copied()).collect();
        let mut cache: HashMap<usize, CudaSlice<u32>> = HashMap::new();
        let mut timings: Vec<(CudaEvent, CudaEvent)> = Vec::with_capacity(plan.len());

        let (result, reader, writer) = std::thread::scope(|s| {
            let reader = s.spawn(move || -> Result<mpsc::Receiver<Staged>, String> {
                for q in fetches {
                    let Ok(mut buf) = free_in_rx.recv() else { break };
                    buf.wait()?;
                    let len = self.tile_words(k - 1, q);
                    input.expect("layer k − 1 exists").load(q, &mut buf.host.as_mut_slice().map_err(err)?[..len])?;
                    if loaded_tx.send((q, buf)).is_err() {
                        break;
                    }
                }
                Ok(free_in_rx)
            });
            let writer = s.spawn(move || -> Result<Layer, String> {
                for (pattern, len, mut buf) in done_rx {
                    buf.wait()?;
                    output.store(pattern, &buf.host.as_slice().map_err(err)?[..len])?;
                    if free_out_tx.send(buf).is_err() {
                        break;
                    }
                }
                Ok(output)
            });

            // Owns the channel ends the workers wait on, so they close when it returns.
            let (free_in_tx, loaded_rx, done_tx) = (free_in_tx, loaded_rx, done_tx);
            let result = (|| -> Result<(), String> {
                for step in plan {
                    for v in &step.evict {
                        cache.remove(v); // freed once its last reader is done
                    }
                    for &q in &step.fetch {
                        let (got, mut buf) = loaded_rx.recv().map_err(stopped)?;
                        assert_eq!(got, q, "reader follows the plan");
                        let len = self.tile_words(k - 1, q);
                        // SAFETY: the copy below writes every element.
                        let mut dev = unsafe { gpu.upload.alloc::<u32>(len) }.map_err(err)?;
                        gpu.upload.memcpy_htod(&buf.host.as_slice().map_err(err)?[..len], &mut dev).map_err(err)?;
                        buf.busy = Some(gpu.mark(&gpu.upload)?);
                        free_in_tx.send(buf).map_err(stopped)?;
                        cache.insert(q, dev);
                    }
                    let (out, timing) = self.launch(gpu, k, step.pattern, &cache, d_numbers, d_binom)?;
                    timings.push(timing);
                    let mut buf = free_out_rx.recv().map_err(stopped)?;
                    buf.wait()?;
                    let len = out.len();
                    gpu.download.memcpy_dtoh(&out, &mut buf.host.as_mut_slice().map_err(err)?[..len]).map_err(err)?;
                    buf.busy = Some(gpu.mark(&gpu.download)?);
                    done_tx.send((step.pattern, len, buf)).map_err(stopped)?;
                }
                Ok(())
            })();
            drop((free_in_tx, loaded_rx, done_tx));
            (result, reader.join().expect("reader thread"), writer.join().expect("writer thread"))
        });
        drop(cache);
        let free_in_rx = reader?;
        let output = writer?;
        result?;
        pools.0.extend(free_in_rx.try_iter());
        pools.1.extend(free_out_rx.try_iter());
        assert_eq!((pools.0.len(), pools.1.len()), (IN_STAGING, OUT_STAGING), "every staging buffer returned");
        let kernel_ms = timings.iter().map(|(a, b)| a.elapsed_ms(b).map(f64::from)).sum::<Result<f64, _>>().map_err(err)?;
        Ok((output, kernel_ms))
    }

    /// Launches tile (k, pattern) on the compute stream; returns its device buffer and the events
    /// around the launch.
    fn launch(
        &self,
        gpu: &Gpu,
        k: usize,
        pattern: usize,
        cache: &HashMap<usize, CudaSlice<u32>>,
        d_numbers: &CudaSlice<u32>,
        d_binom: &CudaSlice<u64>,
    ) -> Result<(CudaSlice<u32>, (CudaEvent, CudaEvent)), String> {
        let stream = &gpu.compute;
        let t = pattern.count_ones() as usize;
        let m = k - t;
        let rows = self.tile_rows(k, t) as u64;
        // SAFETY: the kernel writes every word of every row.
        let mut out = unsafe { stream.alloc::<u32>(rows as usize * self.words) }.map_err(err)?;
        let mut args = TileInputs { same: 0, top: [0; MAX_TOP], top_takes: [0; MAX_TOP] };
        // Guards order the reads after the uploads and record them for eviction; held until launched.
        let mut guards = Vec::with_capacity(t + 1);
        let mut inputs = self.inputs(k, pattern).into_iter();
        if m > 0 {
            let (ptr, guard) = cache[&inputs.next().expect("same-pattern input")].device_ptr(stream);
            args.same = ptr;
            guards.push(guard);
        }
        let mut p = pattern;
        for q in 0..t {
            let b = p.trailing_zeros() as usize;
            p &= p - 1;
            let (ptr, guard) = cache[&inputs.next().expect("top input")].device_ptr(stream);
            args.top[q] = ptr;
            args.top_takes[q] = self.numbers[self.low + b] as u32;
            guards.push(guard);
        }
        let cfg = LaunchConfig {
            grid_dim: (rows.div_ceil(THREADS_PER_BLOCK as u64) as u32, 1, 1),
            block_dim: (THREADS_PER_BLOCK, 1, 1),
            shared_mem_bytes: 0,
        };
        let (low, m32, t32) = (self.low as u32, m as u32, t as u32);
        let (parity, gap, cells, words) = (self.total_parity as u32, self.max_gap as u32, self.cells as u32, self.words as u32);
        let mut launch = stream.launch_builder(&gpu.tile);
        launch.record_kernel_launch(CUevent_flags::CU_EVENT_DEFAULT);
        launch.arg(d_numbers).arg(d_binom).arg(&args).arg(&mut out);
        launch.arg(&low).arg(&m32).arg(&t32).arg(&rows).arg(&parity).arg(&gap).arg(&cells).arg(&words);
        // SAFETY: the argument list matches `tile` in tiled.cu; `same` holds the rows of tile
        // (k − 1, pattern), each `top[q]` the `rows` rows of tile (k − 1, pattern − b_q), and `out`
        // has `rows` rows; all of them stay allocated until the guards record this launch.
        let timing = unsafe { launch.launch(cfg) }.map_err(err)?.expect("launch recorded");
        drop(guards);
        Ok((out, timing))
    }

    /// Player 1's outcome after each possible opening pick.
    pub fn openings(&self, gpu: &Gpu, config: &Config) -> Result<(Vec<(u64, Outcome)>, Stats), String> {
        let n = self.n();
        if n == 0 {
            return Ok((Vec::new(), Stats::default()));
        }
        let (last, stats) = self.run(gpu, config, |_| {})?;
        let full = (1u64 << n) - 1;
        let openings = (0..n)
            .map(|i| {
                // After the opening the opponent moves, trailing by the number taken.
                let x = self.numbers[i];
                let o = self.get(&last, full & !(1 << i), x as usize)?.expect("gap x has the parity of taking x");
                Ok((x, o.neg()))
            })
            .collect::<Result<_, String>>()?;
        Ok((openings, stats))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interval;
    use crate::layered::Layered;
    use crate::tiled::Tiled;

    const FULL_TABLE_MAX_N: u64 = 12;
    const OPENINGS_MAX_N: u64 = 20;
    const SUBSET_UNIVERSE: u64 = 8;
    const PLAN_MAX_N: u64 = 16;
    /// Beyond this the ~50 µs per tile dominates test time.
    const MAX_TEST_TOP: usize = 12;

    /// CUDA tests skip (with a message) on machines without a usable device.
    fn gpu() -> Option<Gpu> {
        Gpu::new().map_err(|e| eprintln!("no CUDA device, skipping: {e}")).ok()
    }

    fn tops(n: usize) -> Vec<usize> {
        let mut tops = vec![0, 1, n / 2, n.min(MAX_TEST_TOP)];
        tops.retain(|&t| t <= n);
        tops.dedup();
        tops
    }

    /// Smallest VRAM cache every layer can run with: forces evictions.
    fn tight(engine: &TiledCuda) -> Config {
        let words = (0..engine.n()).map(|k| engine.working_set_words(k)).max().unwrap_or(0);
        Config { vram_cache_bytes: words.max(1) * BYTES_PER_WORD, ..Config::default() }
    }

    #[test]
    fn plan_keeps_inputs_cached_within_budget() {
        for n in 0..=PLAN_MAX_N as usize {
            for top in tops(n) {
                let engine = TiledCuda::new(&interval(n as u64), top);
                for k in 1..n {
                    let ws = engine.working_set_words(k);
                    for cache in [ws, 2 * ws, usize::MAX] {
                        let plan = engine.plan(k, cache).unwrap();
                        let mut cached = std::collections::HashSet::new();
                        let mut used = 0;
                        for step in &plan {
                            for v in &step.evict {
                                assert!(cached.remove(v));
                                used -= engine.tile_words(k - 1, *v);
                            }
                            for &q in &step.fetch {
                                assert!(cached.insert(q));
                                used += engine.tile_words(k - 1, q);
                            }
                            assert!(used <= cache, "n {n} top {top} k {k}");
                            assert!(engine.inputs(k, step.pattern).iter().all(|q| cached.contains(q)));
                        }
                        let fetched: usize = plan.iter().map(|s| s.fetch.len()).sum();
                        if cache == usize::MAX {
                            assert_eq!(fetched, engine.schedule(k - 1).len(), "each input fetched once");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn positions_count_reachable_cells() {
        for n in 0..=FULL_TABLE_MAX_N {
            let engine = TiledCuda::new(&interval(n), 0);
            let count: u64 = (0u64..1 << n).map(|mask| (0..=n as usize).filter(|&g| g % 2 == engine.parity(mask)).count() as u64).sum();
            assert_eq!(engine.positions(), count, "n {n}");
        }
    }

    #[test]
    fn stored_tiles_round_trip_and_detect_corruption() {
        let engine = TiledCuda::new(&interval(12), 2);
        let (k, pattern) = (6, 0);
        // Two and a half chunks of words that compress poorly.
        let data: Vec<u32> = (0..5 * CHUNK_WORDS as u32 / 2).map(|i| i.wrapping_mul(2654435761)).collect();
        for ram_bytes in [usize::MAX, 0] {
            let mut layer = engine.new_layer(k, 0, &Config { ram_bytes, ..Config::default() });
            layer.store(pattern, &data).unwrap();
            assert_eq!(layer.on_disk(), ram_bytes == 0);
            let mut back = vec![0; data.len()];
            layer.load(pattern, &mut back).unwrap();
            assert_eq!(back, data);
            match layer.tiles[pattern].as_mut().unwrap() {
                Stored::Ram(chunks) => {
                    let mid = chunks[1].len() / 2;
                    chunks[1][mid] ^= 0xff;
                }
                Stored::File(offset, lens) => {
                    let at = *offset + (lens[0] + lens[1] / 2) as u64;
                    let file = &layer.file.as_ref().unwrap().0;
                    let mut byte = [0u8];
                    read_at(file, &mut byte, at).unwrap();
                    write_at(file, &[byte[0] ^ 0xff], at).unwrap();
                }
            }
            assert!(layer.load(pattern, &mut back).is_err(), "ram_bytes {ram_bytes}");
        }
    }

    #[test]
    fn every_layer_matches_tiled() {
        let Some(gpu) = gpu() else { return };
        for n in 0..=FULL_TABLE_MAX_N {
            let numbers = interval(n);
            for top in tops(n as usize) {
                let tiled = Tiled::new(&numbers, top);
                let mut reference: Vec<(crate::tiled::Layout, Vec<u32>)> = Vec::new();
                tiled.run(|_, layout, layer| {
                    reference.push((crate::tiled::Layout { offsets: layout.offsets.clone(), rows: layout.rows }, layer.to_vec()))
                });
                let engine = TiledCuda::new(&numbers, top);
                // Default resources; a tight VRAM cache with every layer in a file; layers split
                // between RAM and file (half the largest compressed layer, known after the first run).
                let mut largest = 0;
                for config in 0..3 {
                    let config = match config {
                        0 => Config::default(),
                        1 => Config { ram_bytes: 0, ..tight(&engine) },
                        _ => Config { ram_bytes: largest / 2, ..tight(&engine) },
                    };
                    let (mut layers, mut split) = (0, 0);
                    engine
                        .run(&gpu, &config, |layer| {
                            let k = layer.k;
                            let (layout, cpu) = &reference[k];
                            for mask in (0u64..1 << n).filter(|m| m.count_ones() as usize == k) {
                                for g in 0..=n as usize {
                                    let got = engine.get(layer, mask, g).unwrap();
                                    if g % 2 == engine.parity(mask) {
                                        let want = tiled.get(cpu, tiled.locate(layout, mask), g);
                                        assert_eq!(got, Some(want), "n {n} top {top} mask {mask:b} gap {g}");
                                    } else {
                                        assert_eq!(got, None);
                                    }
                                }
                            }
                            assert!(layer.ram_bytes() <= config.ram_bytes);
                            assert_eq!(layer.on_disk(), layer.disk_bytes() > 0);
                            split += (layer.ram_bytes() > 0 && layer.on_disk()) as usize;
                            largest = largest.max(layer.ram_bytes() + layer.disk_bytes());
                            layers += 1;
                        })
                        .unwrap();
                    assert_eq!(layers, n);
                    if config.ram_bytes == largest / 2 && top > 0 && n >= 4 {
                        assert!(split > 0, "n {n} top {top}: some layer is split");
                    }
                }
            }
        }
    }

    #[test]
    fn openings_match_layered() {
        let Some(gpu) = gpu() else { return };
        for n in 0..=OPENINGS_MAX_N {
            let expected = Layered::new(&interval(n)).openings();
            for top in tops(n as usize) {
                let engine = TiledCuda::new(&interval(n), top);
                assert_eq!(engine.openings(&gpu, &Config::default()).unwrap().0, expected, "n {n} top {top}");
            }
        }
        for bits in 0u32..(1 << SUBSET_UNIVERSE) {
            let set: Vec<u64> = (1..=SUBSET_UNIVERSE).filter(|&x| bits >> (x - 1) & 1 == 1).collect();
            let expected = Layered::new(&set).openings();
            for top in 0..=set.len() {
                let engine = TiledCuda::new(&set, top);
                assert_eq!(engine.openings(&gpu, &tight(&engine)).unwrap().0, expected, "set {set:?} top {top}");
            }
        }
    }
}
