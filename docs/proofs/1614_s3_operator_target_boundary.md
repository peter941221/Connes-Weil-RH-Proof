# 1614 — Exact S3 operator-target boundary

Date: 2026-09-18

## Result

The committed definitions distinguish the ambient leakage operator from the
source-compressed S3 gate:

- `sourceRootCompletedRightCommutatorLeftLeg owner lambda` is definitionally
  the ambient operator `C ∘ E ∘ (I - Q) ∘ E`;
- the S3 survivor gate is the source-compressed square sum of
  `J† ∘ C ∘ J` (equivalently the completed source Gram after the exact
  prolate remainder split).

The formal non-Hilbert--Schmidt theorem for the ambient leakage operator is
therefore a guard against an ambient Hilbert--Schmidt shortcut, not a
counterexample to the source-compressed target. Conversely, the existing
source-basis leakage theorem for `((I - P) ∘ C ∘ J)` does not discharge the
ambient right-leg consumer used by the S3 band-root assembly.

## Evidence

The definition and the exact Fourier-leakage normal form are in
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSRootCompletedFirstJet.lean`.
The source-compressed target and its equivalence to the Hardy-compressed
root energy are in `C1G8R3GateAmbientNormalForm.lean`. The ambient obstruction
is proved by `sourceRootCompletedRightCommutatorLeftLeg_not_hilbertSchmidt`
and `sourceRootCompletedBandRoot_not_hilbertSchmidt`.

Status: formal route audit; S3 remains open. This record supplies no
positivity or Hilbert--Schmidt conclusion.
