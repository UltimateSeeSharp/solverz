# Claims

| ID | Claim | Uses | Status | Lean | Approved |
|---|---|---|---|---|---|
| [C1](C1.md) | Main conjecture | — | open | N ≤ 12: `CatchUp.conjecture_le_twelve` (`CatchUp/Small.lean`) | 2026-10-22 |
| [C2](C2.md) | Every opening draws | — | open | — | — |
| [C3](C3.md) | Parity law | — | verified | `CatchUp.parity_law`, `CatchUp.even_sum_of_value_eq_draw` (`CatchUp/Parity.lean`) | — |
| [C4](C4.md) | Near-intervals draw | — | open | — | — |
| [C5](C5.md) | Moderate gaps draw | — | open | — | — |
| [C6](C6.md) | Best by membership | — | verified | `CatchUp.Outcome.best_eq_win_iff`, `_draw_iff`, `_loss_iff` (`CatchUp/Best.lean`) | — |
| [C7](C7.md) | Endgames with ≤ 2 numbers | C6 | verified | `CatchUp.valueAux_pair_gap` and two more (`CatchUp/Endgames.lean`) | — |
| [C8](C8.md) | Pair sets draw | — | refuted | — | — |
| [C9](C9.md) | Far-apart pairs | C6 | proved | — | — |
| [C10](C10.md) | Reductions within C8 | C6 | proved | (b) for any set in margins: `CatchUp.margin_tie_le_zero_of_partner` | — |
| [C11](C11.md) | Two pairs | C6, C7, C10 | verified | `CatchUp.value_two_pairs` (`CatchUp/Endgames.lean`, a ≥ 1) | — |
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
| [C33](C33.md) | Sign lemma | — | verified | sets: `CatchUp.valueAux_eq_ofMargin` (`CatchUp/GameMargin.lean`) | — |
| [C34](C34.md) | Far blocks are a margin tolerance | C33 | open | — | — |
| [C35](C35.md) | Sliding quadruple (Const) | C34 | open | — | — |
| [C36](C36.md) | Twins with a tie-break (TD's first cell) | — | open | — | — |
| [C37](C37.md) | Gap bound (LG) | C33, C38 | open | reduction (3): `CatchUp.conjecture_of_margin_le_one` | — |
| [C38](C38.md) | Margin two-token lemma | — | verified | sets: `CatchUp.margin_two_token` (`CatchUp/GameMargin.lean`) | — |
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
| [C61](C61.md) | Exits of smallest-first play are non-losing (EX) | — | open | — | — |
| [C62](C62.md) | Twins with a tie-break at every height | C21 | open | — | — |
| [C63](C63.md) | Peel below height 1 | C28, C62 | proved | — | — |
| [C64](C64.md) | Adjacent-hole copying | — | refuted | counterexample: `CatchUp/AdjacentHoleExchangeObstruction.lean` | — |
| [C65](C65.md) | Pair deletions forbid neighbor jumps | — | refuted | counterexample: `CatchUp/AdjacentHoleExchangeObstruction.lean` | — |
| [C66](C66.md) | Geometry-free first-pair transfer | — | refuted | counterexample: `CatchUp/FirstPairDescentObstruction.lean` | — |
| [C67](C67.md) | No short cycles in the shifted reply graph | — | refuted | counterexample: `CatchUp/ShiftedReplyCycle.lean` | — |
| [C68](C68.md) | A prepaid pair reserve from the first pick | — | refuted | counterexample: `CatchUp/TurnReserveInitialization.lean` | — |
| [C69](C69.md) | Integer peel above height 1 | — | refuted | counterexample: `CatchUp/AdjacentPairGeometryObstruction.lean` | — |
| [C70](C70.md) | Small numbers guard non-loss | — | refuted | counterexample: `CatchUp/UnitGuardObstruction.lean`, `CatchUp/NearDeficitGuardObstruction.lean` | — |
| [C71](C71.md) | Upper-only exact-sum descent | — | refuted | counterexample: `CatchUp/Earlier/UniformExactSumDescentObstruction.lean` | — |
| [C72](C72.md) | Balancing in one turn | — | refuted | counterexample: `CatchUp/WholeTurn.lean` | — |
| [C73](C73.md) | Lower-ray endpoints | C77 | verified | `pair_deletion_position_top_value_ne_loss` (`CatchUp/Earlier/DeficitWinningBound.lean`), `…_penultimate_value_ne_loss` (`CatchUp/LowerRayEndpoints.lean`), `…_antepenultimate_value_ne_loss_of_opening_one_draw` (`CatchUp/LowerRayAntepenultimateDescent.lean`), `…_fourth_from_top_value_ne_loss` (`CatchUp/LowerRayFourthEndpoint.lean`), `…_fifth_from_top_value_ne_loss` (`CatchUp/LowerRayFifthEndpoint.lean`) | — |
| [C74](C74.md) | Interior and boundary of the lower ray | — | verified | `value_Icc_eq_draw_of_lower_ray_interior_and_boundary` (`CatchUp/LowerRayInteriorReduction.lean`); for every N ⇒ C1: `CatchUp.conjecture_of_lower_ray` (`CatchUp/LowerRay.lean`) | — |
| [C75](C75.md) | Every opening draws iff every pair is neutral | — | verified | `every_opening_draw_Icc_iff_every_pair_neutral` (`CatchUp/Earlier/ReplyDigraphReduction.lean`) | — |
| [C76](C76.md) | Three pairs draw at deficit 1 | — | verified | `TiedFour.three_pairs_one_draw` (`CatchUp/TiedFour.lean`) | — |
| [C77](C77.md) | Exact-sum lemmas | — | verified | `Position.value_ne_loss_of_deficit_is_max` (`CatchUp/Earlier/DeficitWinningBound.lean`), `Position.value_ne_loss_of_exact_sum_residuals` (`CatchUp/ExactSumResiduals.lean`), `Position.exists_winning_opening_gt_max_of_loss_of_exact_sum` (`CatchUp/ExactSumLossObstruction.lean`) | — |
| [C78](C78.md) | Increasing turns | — | verified | `Increasing.check_iff`, `Increasing.first_pair_draw_iff` (`CatchUp/Increasing.lean`) | — |
| [C79](C79.md) | Explicit certificates grow exponentially | — | verified | `initial_certificate_exponential` (`CatchUp/Earlier/CertificateComplexityHighCounters.lean`) | — |
| [C80](C80.md) | Score shift | — | verified | `CatchUp.value_aux_add_scores` (`CatchUp/Executable.lean`) | — |
| [C81](C81.md) | Dense pair deletions never lose | — | open | — | — |
| [C82](C82.md) | Second start draws | — | open | — | — |
| [C83](C83.md) | Lower-ray boundary | — | open | — | — |
| [C84](C84.md) | Rank-perturbed intervals draw (DI) | — | open | — | — |
| [C85](C85.md) | Partially collapsed blocks draw (PBT) | — | open | — | — |
| [C86](C86.md) | The draw band at every height (BAND) | — | open | p ≤ 4: `CatchUp.band_draw_le_four`; C86 ⇒ C1: `CatchUp.conjecture_of_band` (`CatchUp/Band.lean`) | — |
| [C87](C87.md) | The band on aligned dense pair sets (BAND-PD) | — | open | — | — |
| [C88](C88.md) | Only the diagonal flips across heights (BANDSTEP) | — | refuted | — | — |
| [C89](C89.md) | Pair-deleted sets never lose below half their size (NLB*) | — | refuted | counterexample: `CatchUp.pair_deleted_loss_19` (`CatchUp/PairDeletions.lean`) | — |
| [C90](C90.md) | Maximum companion | — | verified | `CatchUp.reply_edge_from_max_has_companion`, `…_not_unique` (`CatchUp/ReplyMaximumCompanion.lean`) | — |
| [C91](C91.md) | The lower ray, successor form | — | verified | `value_Icc_eq_draw_of_interior_successor_nonwin`, `pair_deletion_position_value_ne_loss_of_successor_value_ne_win` (`CatchUp/Earlier/LowerRaySuccessor.lean`) | — |
| [C92](C92.md) | The lower ray, canonical exact-deficit form | C28 | verified | `value_Icc_eq_draw_of_exact_deficit_canonical_openings` (`CatchUp/Earlier/LowerRayExactDeficit.lean`) | — |
| [C93](C93.md) | Four consecutive numbers | — | verified | `CatchUpSearch.TopFourClassification.value_top_four`, `value_top_four_deficit_four` (`CatchUp/Earlier/TopFourClassification.lean`) | — |
| [C94](C94.md) | Pair sets at small deficits | — | verified | `DeficitTwo.three_pairs_three_win_iff`, `CanonicalFour.four_four_win_iff`, `AnchorFour.win_requires_four_and_eight`, `FivePair.first_pair_fifteen_nonloss` and more (`CatchUp/DeficitTwo.lean`, `CanonicalSmall`, `CanonicalFour`, `CanonicalFive`, `AnchorFour`, `AnchorFive`, `FivePair`) | — |
| [C95](C95.md) | Three-number endgames | — | verified | `TiedFour.three_close_nonwin_iff`, `…_nonloss_iff` (`CatchUp/ThreePairClose.lean`), `AdjacentPairRepair.orphan_minus_draw_iff` (`CatchUp/AdjacentPairGeometryRepair.lean`), `CatchUpSearch.ThreeCounterSafety.can_avoid_loss_three_counters` (`CatchUp/Earlier/ThreeCounterSafety.lean`) | — |
| [C96](C96.md) | Turns as sets | — | verified | `exists_completed_turn_iff_sum_lt_deficit_add_max`, `Position.value_eq_draw_iff_turn_sets` (`CatchUp/CompletedTurn.lean`) | — |
| [C97](C97.md) | Crossing deficits | C96 | verified | `PairEntranceShadow.reserve_reply_outcome` (`CatchUp/PairEntranceShadow.lean`), `DeficitCrossing.nonloss_of_loss_and_midpoint_turn` (`CatchUp/DeficitCrossing.lean`), `DeficitCrossingEntry.nonloss_iff_entry` (`CatchUp/DeficitCrossingEntry.lean`) | — |
| [C98](C98.md) | Five pairs never win at deficit 3 | — | refuted | counterexample: `FiveThree.not_uniform_five_three` (`CatchUp/FiveThree.lean`) | — |
| [C99](C99.md) | Dense intervals never lose (CU-L003) | — | open | partial: `CatchUp.DenseLossFrontier.loss_frontier`, `CatchUp.even_dense_loss_forces_upper_or_odd_prefix_endpoint` (`CatchUp/PrefixBlockedDenseEndpoints.lean`) | — |
| [C100](C100.md) | Dense intervals give C1 | C31, C99 | open | — | — |
| [C101](C101.md) | The ray point b = 6 | C77 | open | frontier: `CatchUp.RootUpperEightFrontier.interval_parent_loss_frontier`, `CatchUp.RootUpperEightCriterion.interval_reserve_nonwin_iff_core_nonloss` | — |
| [C102](C102.md) | Copying repaired with a score debt ≤ 2 | C33 | open | one instance: `CatchUp.TwoBuffer.mandatory_protocol` (`CatchUp/TwoBufferMandatory.lean`) | — |
| [C103](C103.md) | C74's boundary shrinks | C74, C77 | open | — | — |
