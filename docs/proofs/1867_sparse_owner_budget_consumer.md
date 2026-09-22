# 1867 - Sparse correction owner and node-card budget consumer

Date: 2026-09-23.

Status: Formally verified in Lean; quantitative consumer wiring.

`sparseWindowedMellinCorrection` names one source-indexed sparse correction
chosen from record 1866 and exposes its support-card and evaluation readbacks.
The new `sparseWindowedMellinCorrection_weighted_budget_le_node_card`
consumer feeds that owner into the uniform coefficient/basis estimate and
replaces the support cardinality by `nodes.card`.

Verification: WSL focused builds `sparse-owner-1867a.log` and
`sparse-budget-1867b.log`; successful footers, zero `error:` lines, zero
`sorryAx`, and paired Audit declarations with only
`[propext, Classical.choice, Quot.sound]`.

This still assumes the actual per-coefficient and per-basis seminorm bounds.
It does not prove that their product is below the strict-contraction budget,
and it gives no positivity or RH conclusion.
