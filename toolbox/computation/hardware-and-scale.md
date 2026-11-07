# Hardware and scale
What compute buys and what fits this PC: GPU and FPGA kernels, distributed runs, and the sizing rule.

### T152 GPU and FPGA kernels
`find` `compute` · stage: search · signals: integers, dynamics
aka: GPU brute force, CUDA, bit-parallel arithmetic, FPGA, custom datapaths, Collatz verification, van der Waerden number W(2,6)=1132, Dedekind number D(9), sieves, iteration of maps, palindrome heuristic
- What: thousands of simple threads run bit-parallel arithmetic; FPGAs build a custom datapath for one inner loop.
- Fits when: uniform, branch-light kernels (sieves, iteration of maps, candidate filtering), one GPU job at a time here; FPGAs do not fit this PC, but their preprocessing ideas transfer (unavoidable patterns, palindrome heuristic).
- Lean: accelerator output is a filter or a witness; re-check witnesses in Lean.
- Example: Collatz verified to 2^71, with a 1,335× speedup from CPU to GPU ([Bařina](https://www.fit.vut.cz/research/result/c197809/)); W(2,6)=1132, with FPGAs in the last phase ([Kouril–Paul](https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/1132.pdf)); D(9) on FPGAs ([Van Hirtum et al.](https://arxiv.org/abs/2304.03039)).
- See also: T38, T42, T153, T154

### T153 Volunteer and grid computing
`find` `compute` `bound` · stage: search
aka: BOINC, PrimeGrid, Charity Engine, distributed.net, Condor, master-worker branch-and-bound, scavenged cycles, Sierpiński problem, Riesel problem, Golomb rulers
- What: problems split into millions of independent tasks on donated machines; master-worker branch-and-bound on scavenged cycles.
- Fits when: problems split into millions of independent tasks; long ILP or tree searches.
- Lean: — (it shows what does not fit one PC).
- Example: Sierpiński and Riesel searches ([PrimeGrid](https://www.primegrid.com/)); optimal Golomb rulers with 24+ marks ([distributed.net](https://www.distributed.net/OGR)); sums of three cubes (T40); the football pool problem on Condor (T26).
- See also: T26, T40, T154

### T154 One-PC sizing rule
`find` `prove` `bound` `compute` · stage: judge
aka: compute budget, thread-hours, certificate size, disk writes, feasibility estimate, CPU-years, what fits one PC
- What: estimate thread-hours, RAM, disk writes and certificate bytes before starting, against the machine in the user's CLAUDE.md (This machine).
- Fits when: every experiment.
- Lean: add the kernel's check time to the budget; it often dominates.
- Example: fits: Hex 8×8 (301 h on one desktop) ([Henderson–Arneson–Hayward](https://www.ijcai.org/Abstract/09/091)) and the Erdős–Szekeres hexagon case (about 1 GHz-hour) ([Marić](https://research.matf.bg.ac.rs/handle/123456789/597)); fits to solve, but a kernel-only check does not: R(4,4)=18 (6.5 h, 85.5 GB of LRAT) and Keller G(7,3) (51 h) ([Szeider 2026](https://arxiv.org/abs/2607.00815)); borderline: the empty hexagon (17,300 CPU-hours, about 7 weeks) ([Heule–Scheucher](https://arxiv.org/abs/2403.00737)); does not fit: Boolean Pythagorean triples (800 cores for 2 days, 200 TB) ([Heule–Kullmann–Marek](https://arxiv.org/abs/1605.00723)), Schur number 5 (CPU-years, 2 PB) ([Heule](https://arxiv.org/abs/1711.08076)), Rubik's God's number (35 CPU-years) ([cube20.org](https://www.cube20.org/)).
- See also: T3, T5, T152, T153
