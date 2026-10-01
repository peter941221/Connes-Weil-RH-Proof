# 2391 — directed accumulation order lemma

Date: 2026-10-02.

The finite-sum part of the 2385 accumulation step is now formally audited.
The single-span lemma and its nested span version show the order-theoretic
implication: termwise upper bounds, followed by span upper bounds, imply the
final finite-sum upper bound.

The audit was run in a WSL-native build copy using the repository's current
source and the locked Mathlib package cache.  Both declarations report only
`[propext, Classical.choice, Quot.sound]`.  This does not certify that the
MPFR/binary64 values stored by the replay are the corresponding mathematical
terms, and it does not import any numeric value into Lean.

The required Mathlib brick check was rerun on 2026-10-02 and completed with
its existing result artifact at `results/2049_mathlib_brick_check.json`.  That
check is a library inventory, not a replacement for the source audit.

The partition equality is now also proved in Lean by
`finite_sum_eq_contiguous_partition2394`: contiguous span starts, lengths,
and endpoint coverage imply the exact finite-sum decomposition.  This closes
the analytic/index identity; it does not prove the stored MPFR terms dominate
the mathematical terms.
