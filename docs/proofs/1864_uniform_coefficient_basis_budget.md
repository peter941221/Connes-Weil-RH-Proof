# 1864 - Uniform finite coefficient/basis budget

Date: 2026-09-23.

Status: Formally verified in Lean; quantitative termwise reduction.

`source_combination_seminorm_zero_zero_le_card_mul_uniform_budget` bounds the
exact finite coefficient-weighted source seminorm by
`card(support) * coeffBound * basisBound` under explicit per-term bounds.
`strict_base_contraction_of_uniform_coeff_basis_budget` consumes the resulting
finite inequality and proves the required strict base contraction.

Verification: WSL focused build `uniform-budget-1864c.log`; successful footer,
zero `error:` lines, zero `sorryAx`, and paired Audit declarations with only
`[propext, Classical.choice, Quot.sound]`.

The actual coefficient and basis bounds for the selected
`windowedMellinRightInverse` are not proved here. No positivity or RH
conclusion is asserted.
