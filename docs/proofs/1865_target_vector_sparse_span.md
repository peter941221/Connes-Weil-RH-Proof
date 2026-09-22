# 1865 - Target-vector sparse span certificate

Date: 2026-09-23.

Status: Formally verified in Lean; finite-dimensional source-selection
boundary.

`exists_windowedMellin_target_vector_sparse_coefficients` applies the finite
dimensional span lemma to the windowed Mellin vector range. For every target
assignment it produces a target-vector Finsupp with support cardinality at
most the number of Mellin nodes, support contained in the genuine windowed
vector range, and a sum equal to the target.

Verification: WSL focused build `sparse-target-vectors-1865b.log`; successful
footer, zero `error:` lines, zero `sorryAx`, and paired Audit declarations with
only `[propext, Classical.choice, Quot.sound]`.

This is not yet a source-indexed coefficient budget. The next bridge must pick
one source preimage for every selected target vector and use an injective
`Finsupp.embDomain` transport before the seminorm budget can consume it.
