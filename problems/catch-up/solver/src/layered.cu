// One layer of the layered solver: one thread per mask with k bits, in colex rank order.
// Mirrors `Layered::fill_row` and `layered::evaluate_row`; the layout matches `Layered`'s.

#define LOSS 0u
#define DRAW 1u
#define WIN 2u
#define GAPS_PER_WORD 16u
#define MAX_NUMBERS 32
#define BINOM_STRIDE 34u // row length of `binomials()`: MAX_NUMBERS + 2

typedef unsigned int u32;
typedef unsigned long long u64;

extern "C" __global__ void layer(
    const u32* __restrict__ numbers, // numbers[p] for positions 0..n
    const u64* __restrict__ binom,   // binom[p * BINOM_STRIDE + i] = C(p, i)
    const u32* __restrict__ prev,    // layer k - 1
    u32* __restrict__ cur,           // layer k
    u32 n, u32 k, u64 rows, u32 max_gap, u32 words)
{
    u64 r = (u64)blockIdx.x * blockDim.x + threadIdx.x;
    if (r >= rows) return;

    // Unrank r into the k set positions, ascending.
    u32 pos[MAX_NUMBERS];
    u64 rem = r;
    u32 p = n;
    for (u32 i = k; i > 0; --i) {
        --p;
        while (binom[p * BINOM_STRIDE + i] > rem) --p;
        pos[i - 1] = p;
        rem -= binom[p * BINOM_STRIDE + i];
    }

    // Removing the j-th set bit: bits below keep their index, bits above drop by one.
    u64 pred[MAX_NUMBERS];
    u32 takes[MAX_NUMBERS];
    u64 below = 0, above = 0;
    u32 sum = 0;
    for (u32 i = 1; i < k; ++i) above += binom[pos[i] * BINOM_STRIDE + i];
    for (u32 j = 0; j < k; ++j) {
        pred[j] = below + above;
        below += binom[pos[j] * BINOM_STRIDE + j + 1];
        if (j + 1 < k) above -= binom[pos[j + 1] * BINOM_STRIDE + j + 1];
        takes[j] = numbers[pos[j]];
        sum += takes[j];
    }

    u32 word = 0;
    for (u32 g = 0; g <= max_gap; ++g) {
        u32 v;
        if (sum < g) {
            v = LOSS; // cannot catch up even by taking everything
        } else if (k == 0) {
            v = DRAW; // no numbers left, scores level
        } else {
            u32 best = LOSS;
            for (u32 j = 0; j < k; ++j) {
                u32 x = takes[j];
                u32 gap = x >= g ? x - g : g - x;
                u32 c = (prev[pred[j] * words + gap / GAPS_PER_WORD] >> (2u * (gap % GAPS_PER_WORD))) & 3u;
                // Caught up: the opponent trails by x - g. Still behind: same mover, gap g - x.
                u32 o = x >= g ? WIN - c : c;
                if (o > best) best = o;
                if (best == WIN) break;
            }
            v = best;
        }
        word |= v << (2u * (g % GAPS_PER_WORD));
        if (g % GAPS_PER_WORD == GAPS_PER_WORD - 1 || g == max_gap) {
            cur[r * words + g / GAPS_PER_WORD] = word;
            word = 0;
        }
    }
}
