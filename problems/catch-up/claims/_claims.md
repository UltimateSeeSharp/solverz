# Claims

| ID | Claim | Uses | Status | Lean | Approved |
|---|---|---|---|---|---|
| [C1](C1.md) | Main conjecture | — | open | — | 2026-10-22 |
| [C2](C2.md) | Every opening draws | — | open | — | — |
| [C3](C3.md) | Parity law | — | verified | `CatchUp.parity_law`, `CatchUp.even_sum_of_value_eq_draw` (`CatchUp/Parity.lean`) | — |
| [C4](C4.md) | Near-intervals draw | — | open | — | — |
| [C5](C5.md) | Moderate gaps draw | — | open | — | — |
| [C6](C6.md) | Best by membership | — | verified | `CatchUp.Outcome.best_eq_win_iff`, `_draw_iff`, `_loss_iff` (`CatchUp/Best.lean`) | — |
| [C7](C7.md) | Endgames with ≤ 2 numbers | C6 | proved | — | — |
| [C8](C8.md) | Pair sets draw | — | refuted | — | — |
| [C9](C9.md) | Far-apart pairs | C6 | proved | — | — |
| [C10](C10.md) | Reductions within C8 | C6 | proved | — | — |
| [C11](C11.md) | Two pairs | C6, C7, C10 | proved | — | — |
| [C12](C12.md) | Even blocks draw | — | open | — | — |
| [C13](C13.md) | High sets are the rounds game | C6 | verified | `CatchUp.valueAux_map_add`, rounds game `CatchUp.roundsValue` (`CatchUp/Rounds.lean`) | — |
| [C14](C14.md) | Greedy bound | — | verified | `CatchUp.neg_altSum_le_greedyWorst`, per round `CatchUp.altSum_round`, `CatchUp.altSum_top_two` (`CatchUp/AltSum.lean`) | — |
| [C15](C15.md) | Always-max on pair sets | — | proved | — | — |
| [C16](C16.md) | High pair sets draw | C13, C15 | proved | blocks only: `CatchUp.block_draw_high` (`CatchUp/Blocks.lean`, via C23) | — |
| [C17](C17.md) | Rows of high blocks | C13 | open | draw entries of blocks at a ≥ 6p − 2: `CatchUp.block_row_draw_linear` (`CatchUp/Linear.lean`) | — |
| [C18](C18.md) | Catch-up potential step | C13, C14 | verified | `CatchUp.potential_le_roundsMargin` (guarantee form) | — |
| [C19](C19.md) | Top-run lemma | C18 | open | — | — |
| [C20](C20.md) | Matching bound | — | verified | `CatchUp.roundsMargin_le_matchCost` (`CatchUp/Matching.lean`) | — |
| [C21](C21.md) | High pair sets at linear height | C15, C20, C22 | proved | blocks only: `CatchUp.block_draw_linear` (`CatchUp/Linear.lean`, via C23) | — |
| [C22](C22.md) | Strategy transfer | — | verified | `CatchUp.valueAux_transfer` (`CatchUp/Transfer.lean`, draw threshold) | — |
| [C23](C23.md) | Depth invariant | C13 | verified | `CatchUp.depth_class_roundsMargin` (`CatchUp/Depth.lean`) | — |
| [C24](C24.md) | Blocks at the doubling-free height | C20, C22, C23, C25 | verified | `CatchUp.block_draw_hyb2`, `CatchUp.block_row_draw_hyb2` (`CatchUp/Hyb2.lean`) | — |
| [C25](C25.md) | Hyb2's debt bound | C20 | verified | `CatchUp.potW_z_round`, `CatchUp.potW_y_round` (`CatchUp/Hyb2.lean`) | — |
| [C26](C26.md) | Token lemma | C6 | verified | `CatchUp.token_lemma` (`CatchUp/Token.lean`) | — |
| [C27](C27.md) | Two block families suffice | C26, C12 | verified | `CatchUp.conjecture_of_two_families` (`CatchUp/Token.lean`) | — |
| [C28](C28.md) | Level law | C6 | verified | `CatchUp.level_law` (`CatchUp/Token.lean`) | — |
| [C29](C29.md) | One family at height 2 | C26 | verified | `CatchUp.conjecture_of_height_two` (`CatchUp/Token.lean`) | — |
| [C30](C30.md) | Two-token lemma | C6 | verified | `CatchUp.level_option_ne_loss`, `CatchUp.two_token` (`CatchUp/Token.lean`) | — |
| [C31](C31.md) | One-sided roots | C30, C29 | verified | `CatchUp.conjecture_of_leader_pair`, `CatchUp.conjecture_of_suffix_pair`, `CatchUp.conjecture_le_three` (`CatchUp/Token.lean`) | — |
| [C32](C32.md) | TI at real heights | — | open | — | — |
| [C33](C33.md) | Sign lemma | — | proved | — | — |
| [C34](C34.md) | Far blocks are a margin tolerance | C33 | open | — | — |
| [C35](C35.md) | Sliding quadruple (Const) | C34 | open | — | — |
| [C36](C36.md) | Twins with a tie-break (TD's first cell) | — | open | — | — |
| [C37](C37.md) | Gap bound (LG) | C33, C38 | open | — | — |
| [C38](C38.md) | Margin two-token lemma | — | proved | — | — |
| [C39](C39.md) | Induction by four on drawn sets | — | refuted | — | — |
| [C40](C40.md) | Induction by four on complete sets | — | refuted | — | — |
| [C41](C41.md) | Complete even-sum sets are draws | — | refuted | — | — |
| [C42](C42.md) | A top pair acts locally on gaps | — | refuted | — | — |
| [C43](C43.md) | Fixed hole bounds under drawing play | — | refuted | — | — |
| [C44](C44.md) | Forced partner reply | — | refuted | — | — |
| [C45](C45.md) | Pair sets draw | — | refuted | — | — |
| [C46](C46.md) | Opening the top quadruple early never helps | — | refuted | — | — |
| [C47](C47.md) | A block's drawn band never shrinks as its height decreases | — | refuted | — | — |
| [C48](C48.md) | The mover at a tie never loses the rounds game | — | refuted | — | — |
| [C49](C49.md) | C23's depth class on {1..N} | — | refuted | — | — |
| [C50](C50.md) | The level law off ties | — | refuted | — | — |
| [C51](C51.md) | Values monotone in the deficit | — | refuted | — | — |
| [C52](C52.md) | Debt thresholds on high sets | — | refuted | — | — |
| [C53](C53.md) | Symmetric sets draw | — | refuted | — | — |
| [C54](C54.md) | Escalation answers | — | refuted | — | — |
| [C55](C55.md) | One strategy for all heights | — | refuted | — | — |
| [C56](C56.md) | A defender that closes the moved quadruple at once | — | refuted | — | — |
| [C57](C57.md) | Sliding a quadruple above any drawn base | — | refuted | — | — |
| [C58](C58.md) | Near ties stay drawn across a breakpoint | — | refuted | — | — |
| [C59](C59.md) | Gap potentials for LG | — | refuted | — | — |
| [C60](C60.md) | Pairing bound (sharper C37) | — | refuted | — | — |
