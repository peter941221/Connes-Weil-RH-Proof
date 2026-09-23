# 1895 - C3' phase-swap symmetry

Date: 2026-09-23.

Status: formally verified in Lean. This is an algebraic same-owner interface,
not a positivity theorem and not an RH proof.

The carrier transport module now proves the following exchange identities for
every real carrier frequency and every pair of compact-log tests:

```text
carrierPairArchimedeanTermPhase gamma u v
  = carrierPairArchimedeanTermPhase gamma v u

carrierPairPrimePhaseSum gamma u v
  = carrierPairPrimePhaseSum gamma v u

carrierArchimedeanDeterminantPhase gamma u v
  = carrierArchimedeanDeterminantPhase gamma v u

carrierMixedDeterminantPhase gamma u v
  = carrierMixedDeterminantPhase gamma v u

carrierPrimeDeterminantPhase gamma u v
  = carrierPrimeDeterminantPhase gamma v u
```

The first two identities transport the existing pair-test commutation laws
through the carrier phase owner. The determinant identities then follow by
unfolding the determinant definitions and ring normalization. No visible
prime set is replaced, and no absolute-value majorant is introduced.

This removes an ordering/interface gap for future directed-pair sign
arguments. It does not establish the required detector-specific signs:
`A_u <= 0 <= A_v`, `P_u <= 0 <= P_v`, or the nonnegative directed product.
The C3' signed budget and RH therefore remain open.

Verification: WSL focused build
`c3-swap-1895e.log`; successful footer for 3788 jobs, zero `error:` lines,
zero `sorryAx`, and the paired Audit declarations use only
`[propext, Classical.choice, Quot.sound]`.
