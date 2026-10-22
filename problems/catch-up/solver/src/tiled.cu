// One output tile (k, T) of the compact tiled solver: one thread per row, rows in colex order of
// the low mask. Computes `Tiled::fill_tile` and `layered::evaluate_row`, except that a row stores
// only the gaps g ≡ taken (mod 2) (cell i = gap p + 2i, p the row's parity): no other gap occurs.
// All cells of a row are evaluated at once on two bit planes, win (bit i: cell i is WIN) and draw.
// Cells are stored in base 3, 5 per byte. MAX_NUMBERS, MAX_TOP and BINOM_STRIDE come from
// tiled_cuda.rs at compile time.
//
// Move x from cell i (gap g = p + 2i), d = x - p, h = d / 2:
//   i <= h (x >= g, caught up): opponent trails by x - g, cell h - i of the successor, negated;
//   i >  h (x <  g, behind):   same mover trails by g - x, cell i - ceil(d / 2) of the successor.
// The successor's parity is p ^ (x & 1), so these are its cells for exactly those gaps.

#define CELLS_PER_BYTE 5u // 3^5 = 243 ≤ 256
#define BYTES_PER_WORD 4u
#define DIGITS 243u
#define CHUNK_MASK 31u    // one byte's 5 cells on a bit plane
#define PLANE_BITS 32u

typedef unsigned int u32;
typedef unsigned long long u64;

struct TileInputs {
    const u32* same;          // tile (k − 1, T): low moves, at the reduced low rank
    const u32* top[MAX_TOP];  // tiles (k − 1, T − b): top moves, at the same row
    u32 top_takes[MAX_TOP];   // the number at each top position b of T, ascending
};

// Lanes 0..n-1 of a plane.
__device__ __forceinline__ u32 lanes(u32 n) {
    return n >= PLANE_BITS ? ~0u : (1u << n) - 1u;
}

__device__ __forceinline__ u32 shl(u32 v, u32 s) {
    return (u32)((u64)v << s); // s may be 32
}

extern "C" __global__ void tile(
    const u32* __restrict__ numbers, // numbers[p] for low positions 0..low
    const u64* __restrict__ binom,   // binom[p * BINOM_STRIDE + i] = C(p, i)
    TileInputs in,
    u32* __restrict__ out,
    u32 low, u32 m, u32 t, u64 rows, u32 total_parity, u32 max_gap, u32 cells, u32 words)
{
    // unpack[d] = byte d's 5 cells: win plane in bits 0..4, draw plane in bits 16..20.
    // digits[b] = sum of 3^c over the bits c of b, so a byte packs as 2 digits[win] + digits[draw].
    __shared__ u32 unpack[DIGITS];
    __shared__ u32 digits[CHUNK_MASK + 1];
    for (u32 d = threadIdx.x; d < DIGITS; d += blockDim.x) {
        u32 v = d, win = 0, draw = 0;
        for (u32 c = 0; c < CELLS_PER_BYTE; ++c) {
            win |= (v % 3u == 2u) << c;
            draw |= (v % 3u == 1u) << c;
            v /= 3u;
        }
        unpack[d] = win | draw << 16;
    }
    for (u32 b = threadIdx.x; b <= CHUNK_MASK; b += blockDim.x) {
        u32 sum = 0, power = 1;
        for (u32 c = 0; c < CELLS_PER_BYTE; ++c, power *= 3u) sum += (b >> c & 1u) * power;
        digits[b] = sum;
    }
    __syncthreads();

    u64 r = (u64)blockIdx.x * blockDim.x + threadIdx.x;
    if (r >= rows) return;
    u32 k = m + t;
    u32 bytes = (cells + CELLS_PER_BYTE - 1) / CELLS_PER_BYTE;

    // Unrank r into the m low positions, ascending.
    u32 pos[MAX_NUMBERS];
    u64 rem = r;
    u32 p = low;
    for (u32 i = m; i > 0; --i) {
        --p;
        while (binom[p * BINOM_STRIDE + i] > rem) --p;
        pos[i - 1] = p;
        rem -= binom[p * BINOM_STRIDE + i];
    }

    u32 sum = 0;
    for (u32 j = 0; j < m; ++j) sum += numbers[pos[j]];
    for (u32 q = 0; q < t; ++q) sum += in.top_takes[q];
    u32 par = total_parity ^ (sum & 1u); // parity of the amount taken so far
    // Cells with g ≤ max_gap and g ≤ sum; the others lose (cannot catch up even by taking everything).
    u32 limit = min(max_gap, sum);
    u32 live = limit < par ? 0u : lanes((limit - par) / 2u + 1u);

    u32 win = 0, draw = 0;
    if (k == 0) {
        draw = live; // no numbers left, scores level
    } else {
        // Removing the j-th set bit: bits below keep their index, bits above drop by one.
        u64 below = 0, above = 0;
        for (u32 i = 1; i < m; ++i) above += binom[pos[i] * BINOM_STRIDE + i];
        for (u32 j = 0; j < k && (win & live) != live; ++j) {
            const u32* src;
            u32 x;
            if (j < m) {
                src = in.same + (below + above) * words;
                below += binom[pos[j] * BINOM_STRIDE + j + 1];
                if (j + 1 < m) above -= binom[pos[j + 1] * BINOM_STRIDE + j + 1];
                x = numbers[pos[j]];
            } else {
                src = in.top[j - m] + r * words;
                x = in.top_takes[j - m];
            }
            u32 sw = 0, sd = 0; // successor's planes
            for (u32 b = 0; b < bytes; ++b) {
                u32 u = unpack[(src[b / BYTES_PER_WORD] >> (8u * (b % BYTES_PER_WORD))) & 0xffu];
                sw |= shl(u & CHUNK_MASK, CELLS_PER_BYTE * b);
                sd |= shl(u >> 16, CELLS_PER_BYTE * b);
            }
            u32 d = x - par;
            u32 h = d / 2u;
            u32 caught = lanes(h + 1u);
            // Caught up: reverse cells 0..h, then negate (win ↔ loss); draw stays draw.
            u32 rw = __brev(sw) >> (PLANE_BITS - 1u - h);
            u32 rd = __brev(sd) >> (PLANE_BITS - 1u - h);
            u32 c = (d + 1u) / 2u;
            u32 mw = (~(rw | rd) & caught) | (shl(sw, c) & ~caught);
            u32 md = (rd & caught) | (shl(sd, c) & ~caught);
            win |= mw;
            draw = (draw | md) & ~win;
        }
    }
    win &= live;
    draw &= live;

    u32 word = 0;
    for (u32 b = 0; b < bytes; ++b) {
        u32 shift = CELLS_PER_BYTE * b;
        u32 byte = 2u * digits[(win >> shift) & CHUNK_MASK] + digits[(draw >> shift) & CHUNK_MASK];
        word |= byte << (8u * (b % BYTES_PER_WORD));
        if (b % BYTES_PER_WORD == BYTES_PER_WORD - 1 || b == bytes - 1) {
            out[r * words + b / BYTES_PER_WORD] = word;
            word = 0;
        }
    }
}
