# Record 1807 — C3' even/odd discriminant route audit

Date: 2026-09-22.

Status: formal route audit complete. The detector-specific C3' signed budget
and RH remain open.

## Formal result

`ConnesWeilRH/Dev/C1P2EvenOddGateDecomposition.lean` now proves:

- `ICgate_sumTest_add`, the exact same-owner gate additivity for pointwise
  sums;
- `ICgate_pairTest_zero_of_even_odd`, the polarized pair gate vanishes when
  the first input is even and the second is odd;
- `twoSpan_discriminant_pos_of_even_odd_positive`, which states that positive
  diagonal gates plus the vanishing cross gate force a strictly positive
  two-span discriminant.

The paired Audit module prints only the standard axioms.

## Route consequence

The result rules out proving the C3' determinant inequality for arbitrary
`CompactLogTest` pairs from the existing owner fields alone. It does not give
an unconditional counterexample to the selected detector, because the
theorem retains the positive-diagonal hypotheses and does not assert that the
selected detector decomposes into such a pair.

Therefore the live producer must add a genuine detector-specific phase-lock,
real-sector, or equivalent physical-kernel constraint. A generic absolute
value or sigma-margin argument cannot close the C3' budget without that extra
structure.

## Verification

Focused ext4 build: `1807_even_odd_discriminant_final.log`, 3807 jobs,
zero `error:` lines, zero `sorryAx`, and only
`[propext, Classical.choice, Quot.sound]` for the new audited declarations.
