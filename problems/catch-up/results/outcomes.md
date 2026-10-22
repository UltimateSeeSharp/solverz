# Catch-Up outcomes, N = 1..24

Optimal-play value on {1..N} for player 1, and player 1's outcome after each opening pick.

- Date: 2026-10-22
- Solver: `problems/catch-up/solver` at commit 054d108 (run on the identical working tree just before that commit)
- Command: `cargo run --release -p catch-up -- 24`
- Machine: AMD Ryzen 7 3700X, 32 GB RAM, single thread; rustc 1.99.1
- Total time: about 34 s
- Columns: `positions` = distinct positions evaluated (deterministic), `ms` = wall time for that N

| N | total even | value (P1) | openings that win | draw | lose | positions | ms |
|---|---|---|---|---|---|---|---|
| 1 | false | Win | 1 | - | - | 0 | 0 |
| 2 | false | Win | 2 | - | 1 | 1 | 0 |
| 3 | true | Draw | - | 1,3 | 2 | 6 | 0 |
| 4 | true | Draw | - | 1,2 | 3,4 | 14 | 0 |
| 5 | false | Win | 3 | - | 1,2,4,5 | 29 | 0 |
| 6 | false | Win | 2 | - | 1,3,4,5,6 | 65 | 0 |
| 7 | true | Draw | - | 1,2,3,4 | 5,6,7 | 245 | 0 |
| 8 | true | Draw | - | 1,2,3,4,5,6,7,8 | - | 703 | 0 |
| 9 | false | Loss | - | - | 1,2,3,4,5,6,7,8,9 | 327 | 0 |
| 10 | false | Loss | - | - | 1,2,3,4,5,6,7,8,9,10 | 660 | 0 |
| 11 | true | Draw | - | 1,2,3,4,5,6,7,8,9,11 | 10 | 9035 | 0 |
| 12 | true | Draw | - | 1,2,3,4,5,6,7,8,9,10,11,12 | - | 20636 | 0 |
| 13 | false | Win | 1 | - | 2,3,4,5,6,7,8,9,10,11,12,13 | 2373 | 0 |
| 14 | false | Loss | - | - | 1,2,3,4,5,6,7,8,9,10,11,12,13,14 | 5799 | 0 |
| 15 | true | Draw | - | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15 | - | 225476 | 7 |
| 16 | true | Draw | - | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16 | - | 490202 | 17 |
| 17 | false | Win | 3 | - | 1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17 | 28546 | 0 |
| 18 | false | Loss | - | - | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18 | 54673 | 1 |
| 19 | true | Draw | - | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19 | - | 4827201 | 224 |
| 20 | true | Draw | - | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20 | - | 10238091 | 574 |
| 21 | false | Win | 3 | - | 1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21 | 271021 | 12 |
| 22 | false | Win | 2 | - | 1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22 | 469544 | 28 |
| 23 | true | Draw | - | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23 | - | 95451689 | 11598 |
| 24 | true | Draw | - | 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24 | - | 199721295 | 21317 |
