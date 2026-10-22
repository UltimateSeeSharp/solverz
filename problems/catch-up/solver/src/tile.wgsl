// One output tile of the tiled solver: one thread per row (one set of low numbers left).
// Mirrors `layered::evaluate_row` and the indexing of `Tiled::fill_tile`.

const LOSS: u32 = 0u;
const DRAW: u32 = 1u;
const WIN: u32 = 2u;
const GAPS_PER_WORD: u32 = 16u;
const BINOM_STRIDE: u32 = 34u; // row length of `binomials()`: MAX_NUMBERS + 2

// params layout (see gpu.rs): header, then top takes, then top input bases
const P_LOW_BITS: u32 = 0u;   // m: low numbers left in this tile
const P_TOP_BITS: u32 = 1u;   // t: top numbers left
const P_LOW: u32 = 2u;        // number of low positions
const P_MAX_GAP: u32 = 3u;
const P_WORDS: u32 = 4u;      // u32 words per row
const P_ROWS: u32 = 5u;       // rows in this tile
const P_SAME_BASE: u32 = 6u;  // first input row of tile T (layer k − 1)
const P_STRIDE: u32 = 7u;     // threads per dispatch row (2D dispatch)
const P_TOP_TAKE: u32 = 8u;   // 32 entries
const P_TOP_BASE: u32 = 40u;  // 32 entries: first input row of tile T − b

@group(0) @binding(0) var<storage, read> params: array<u32>;
@group(0) @binding(1) var<storage, read> numbers: array<u32>; // numbers at low positions
@group(0) @binding(2) var<storage, read> binom: array<u32>;
@group(0) @binding(3) var<storage, read> inputs: array<u32>;
@group(0) @binding(4) var<storage, read_write> out: array<u32>;

fn choose(p: u32, i: u32) -> u32 {
    return binom[p * BINOM_STRIDE + i];
}

fn cell(row: u32, gap: u32, words: u32) -> u32 {
    return (inputs[row * words + gap / GAPS_PER_WORD] >> (2u * (gap % GAPS_PER_WORD))) & 3u;
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
    let m = params[P_LOW_BITS];
    let t = params[P_TOP_BITS];
    let low = params[P_LOW];
    let max_gap = params[P_MAX_GAP];
    let words = params[P_WORDS];
    let r = id.y * params[P_STRIDE] + id.x;
    if (r >= params[P_ROWS]) {
        return;
    }

    // Unrank r (colex) into the m low positions, ascending.
    var pos: array<u32, 32>;
    var rem = r;
    var p = low;
    for (var i = m; i > 0u; i = i - 1u) {
        p = p - 1u;
        while (choose(p, i) > rem) {
            p = p - 1u;
        }
        pos[i - 1u] = p;
        rem = rem - choose(p, i);
    }

    // Moves: removing low bit j reads tile T at the reduced rank; removing top bit q reads tile T − b at row r.
    var takes: array<u32, 32>;
    var preds: array<u32, 32>;
    var sum = 0u;
    var below = 0u;
    var above = 0u;
    for (var i = 1u; i < m; i++) {
        above += choose(pos[i], i);
    }
    for (var j = 0u; j < m; j++) {
        preds[j] = params[P_SAME_BASE] + below + above;
        below += choose(pos[j], j + 1u);
        if (j + 1u < m) {
            above -= choose(pos[j + 1u], j + 1u);
        }
        takes[j] = numbers[pos[j]];
        sum += takes[j];
    }
    for (var q = 0u; q < t; q++) {
        takes[m + q] = params[P_TOP_TAKE + q];
        preds[m + q] = params[P_TOP_BASE + q] + r;
        sum += takes[m + q];
    }

    let k = m + t;
    var word = 0u;
    for (var g = 0u; g <= max_gap; g++) {
        var v = LOSS;
        if (sum < g) {
            v = LOSS; // cannot catch up even by taking everything
        } else if (k == 0u) {
            v = DRAW; // no numbers left, scores level
        } else {
            var best = LOSS;
            for (var j = 0u; j < k; j++) {
                let x = takes[j];
                var o: u32;
                if (x >= g) {
                    o = WIN - cell(preds[j], x - g, words); // caught up: opponent trails by x − g
                } else {
                    o = cell(preds[j], g - x, words); // still behind: same mover
                }
                best = max(best, o);
                if (best == WIN) {
                    break;
                }
            }
            v = best;
        }
        word = word | (v << (2u * (g % GAPS_PER_WORD)));
        if (g % GAPS_PER_WORD == GAPS_PER_WORD - 1u || g == max_gap) {
            out[r * words + g / GAPS_PER_WORD] = word;
            word = 0u;
        }
    }
}
