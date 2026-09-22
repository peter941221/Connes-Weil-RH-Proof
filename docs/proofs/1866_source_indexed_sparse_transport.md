# 1866 - Source-indexed sparse Mellin transport

Date: 2026-09-23.

Status: Formally verified in Lean; source-test coefficient transport.

`exists_windowedMellin_source_sparse_coefficients` transports the sparse
target-vector certificate back to the genuine
`WindowedPositiveIntervalCompactTest a b` index type. It chooses one source
preimage for each selected target vector, proves those choices injective from
target-vector equality, and uses `Finsupp.comapDomain` plus
`Finsupp.embDomain` to preserve both the target sum and support cardinality.
The resulting source support is still bounded by `nodes.card`.

Verification: WSL focused build `source-sparse-1866e.log`; successful footer,
zero `error:` lines, zero `sorryAx`, and the paired Audit declaration with
only `[propext, Classical.choice, Quot.sound]`.

This closes the source-indexing adapter, not the quantitative estimate. The
actual coefficients of `windowedMellinRightInverse` and the selected basis
seminorm bounds are still needed before the uniform finite budget can imply
strict contraction. No positivity or RH conclusion is asserted.
