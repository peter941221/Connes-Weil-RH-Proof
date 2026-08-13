# 1000 - Sonin-window witness kernel

Date: 2026-08-12. Status: corrected typed kernel, build-verified and
axiom-clean. It records open analytic targets; it does not close a Sonin
witness or claim RH.

## Verified interfaces

For `lambda : CCM24SoninScale`, `Dev/SoninWindowWitness.lean` provides:

```text
archimedeanSoninCarrier_nontrivial lambda
  := exists u : sourceSoninCarrier lambda, u != 0

windowT lambda
  := Ioo (log lambda) (log lambda + log 2)

soninWindowRestriction lambda
  : L2(R) ->L L2(volume.restrict (windowT lambda))

archimedeanSonin_window_mass lambda
  := exists u : sourceSoninCarrier lambda,
       u != 0 and soninWindowRestriction lambda u != 0

archimedeanScatteringToeplitzKernel_nontrivial
  := exists psi in H+, psi != 0 and P+(m * psi) = 0.
```

The window condition is a restriction-map condition, not a point-value
condition. An `Lp` vector is an almost-everywhere equivalence class, so a
nonzero value at one chosen point cannot certify nonzero mass.

`Dev/PaleyWindowProbe.lean` proves that the ambient radial indicator has
nonzero restricted norm. It does not lie in the full Sonin carrier because its
Hardy--Titchmarsh support condition remains unproved.

## What the kernel does not prove

The following implications remain separate open theorems:

```text
nonzero Sonin vector
  -> nonzero restriction to windowT

nonzero scattering Toeplitz kernel
  -> sourceSoninCarrier witness
  -> nonzero restriction to windowT.
```

The first needs a determining-set or unique-continuation theorem. The second
needs an exact Fourier/Hardy transport theorem. Neither follows from the
current projection infrastructure.

## Closed infrastructure

The following declarations have focused WSL build and axiom audits with only
`[propext, Classical.choice, Quot.sound]`:

```text
windowT_nonempty
archimedeanSonin_membership_pred_of_radial_and_involutive
soninWindowIndicator_mem_radial
soninWindowIndicator_ne_zero
soninWindowIndicator_restriction_ne_zero
scattering_toeplitz_kernel_image_mem_negative.
```

The exact `+-1` eigenvector subroute remains unsuitable for a generic L2
witness. The scattering phase is nonconstant, so that construction would need
mass on a phase level set.

## Route consequence

An actual `sourceSoninCarrier` witness with nonzero window restriction feeds
the exact `{2}` coframe strip identity and proves
`twoOuterNonzeroObligation`. That result rejects the current
infinite-carrier Gate-3U cancellation route for `{2}`. It does not prove RH.

## Next proof work

1. Formalize the Toeplitz-kernel to Sonin-carrier transport.

2. Construct a nonzero kernel vector using a prolate/Sonin spectral theorem.

3. Prove nonzero restriction to the log-2 window and consume the existing
   coframe identity.
