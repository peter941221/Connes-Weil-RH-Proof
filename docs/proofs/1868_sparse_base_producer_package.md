# 1868 - Sparse base producer package

Date: 2026-09-23.

Status: Formally verified in Lean; producer-facing sparse base package.

`exists_sparse_base_with_unit_targets_and_quadratic_decay` converts the named
sparse source correction into a `CompactLogTest` base on the requested log
window. It returns the source support-card bound, support inclusion, unit
Laplace targets at all selected nodes, and the uniform quadratic vertical-tail
bound in one package.

Verification: WSL focused build `sparse-base-1868b.log`; successful footer,
zero `error:` lines, zero `sorryAx`, and the paired Audit declaration with
only `[propext, Classical.choice, Quot.sound]`.

This does not replace the existing affine producer yet and does not prove the
coefficient/basis budget. Strict contraction, detector-specific signed
semi-local positivity, and RH remain open.
