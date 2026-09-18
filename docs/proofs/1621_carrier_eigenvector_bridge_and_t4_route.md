# 1621 — The carrier obligation is a radial fixed-point problem: machine-checked bridge, half-phase unitary, and the T4 route

Date: 2026-09-18.

Status: FORMAL bridge + PAPER computation. No witness, no estimate; the
carrier stays OPEN and RH is not claimed in either direction.

Consumer (named): the same-owner healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); the carrier is
the base of the S3 face ([1620](1620_s3_reduction_layer_complete.md)).

## 1. What landed (machine-checked)

`ConnesWeilRH/Dev/SoninCarrierEigenvectorBridge.lean` with audit twin
`SoninCarrierEigenvectorBridgeAudit.lean`, five declarations, standard axioms,
no `sorry`. The main theorem:

```text
archimedeanSoninCarrier_nontrivial lambda
  <->  exists u != 0, u in Radial(lambda)
         and (H u = u or H u = -u),
```

where `H = ccm24ArchimedeanHardyTitchmarsh`
(`CCM24HardyTitchmarsh.lean:331`). Forward direction: symmetrization
`u + H u` (or `u - H u`) of a nonzero carrier element is nonzero, radial, and
`H`-fixed; backward direction: the committed membership reduction
`archimedeanSonin_membership_pred_of_radial_and_involutive`
(`SoninWindowWitness.lean:124`).

So the base obligation is no longer an intersection of two support conditions;
it is a single fixed-point equation for one involutive operator, with the
support condition kept on the eigenvector.

## 2. Status of the base, unchanged (law F33)

`archimedeanSoninCarrier_nontrivial` is a `noncomputable def … : Prop`
(`SoninWindowWitness.lean:44`), and the committed source layer consumes it as
the hypothesis `(hsource : ∃ y, y ≠ 0)`
(`CCM24FiniteSFixedFullBoundaryInjectivityGuard.lean:103`). Records 1586–1589
therefore remain a CONDITIONAL reduction, as filed by
[1590](1590_carrier_base_obligation_is_a_de_branges_existence_and_1331_erratum.md).
This record changes the shape of the missing input, not its status.

## 3. The half-phase unitary (paper computation)

Committed facts used: the definition and spectral readback of `H`
(`:331–345`),

```text
F (H u) = m . (R (F u)),      m = ccm24ArchimedeanScatteringPhase,
R = ccm24LogSpectralReflection  (u |-> u(-.)),
F = Lp.fourierTransformₗᵢ ℝ ℂ,
```

and the phase laws `m(-xi) = conj (m xi)` and `m * conj m = 1` used inside the
committed involutivity proof `ccm24ArchimedeanSpectralScattering_involutive`
(`:298–327`), which give `m(-xi) = m(xi)^{-1}` wherever `m` is unimodular.

Let `U := F⁻¹ ∘L M_{m^{-1/2}} ∘L F` (multiplication by a measurable unimodular
half-phase; `U` is a linear isometry and `U⁻¹ = F⁻¹ M_{m^{1/2}} F`). Then, as
multiplication operators on the spectral variable,

```text
U H U⁻¹ = F⁻¹ (M_{m^{-1/2}} M_m R M_{m^{1/2}}) F
        = F⁻¹ (M_{m^{1/2}} R M_{m^{1/2}}) F
        = F⁻¹ R F,
```

because `(M_{m^{1/2}} R M_{m^{1/2}} phi)(xi) = m(xi)^{1/2} m(-xi)^{1/2}
phi(-xi) = phi(-xi)`. Since the Fourier transform commutes with the reflection
`u ↦ u(-.)` (both coordinates carry the same reflection operator), the
conjugate `F⁻¹ R F` is that reflection. Hence:

```text
H is unitarily equivalent to the pure reflection:
fixed points of H  <->  even vectors in the half-phase frame U.
```

Two honest caveats, both convention-level and both flagged for any future
formalization: (i) the branch of `m^{±1/2}` is not canonical, but conjugation
by `U` is insensitive to the overall sign, so `U H U⁻¹ = R` is branch-free;
(ii) the last step uses the standard reflection covariance of the unitary
Fourier transform, which is not yet a committed lemma in this tree.

## 4. Consequences for the shape of the obligation

1. `H` is a self-adjoint unitary (an isometric involution), so its spectrum is
   contained in `{±1}`; the `±1` eigenspaces are automatically nonzero because
   `H` is not a scalar operator. The whole carrier content therefore sits in
   the RADIAL containment: a nonzero `±1` eigenvector must be supported on the
   half-line `[log λ, ∞)`.
2. In the half-phase frame the fixed-point condition becomes evenness, and the
   radial condition becomes a phase-modulated Hardy (model-space) membership
   `m^{-1/2} . F phi ∈ H²(λ)` for the even vector `phi`. This is the same
   Sonin/de Branges object as in 1590: the carrier is `W` up to the scale
   character, and `W != {0}` is a classical entire-function existence, not a
   rigidity (law F34, 1590 sections 4–5).
3. The productive route remains T4 of [1003](1003_psp_inner_outer_attack_plan.md):
   construct the kernel vector from the prolate/Sonin spectral problem — the
   Connes–Moscovici negative prolate eigenfunction is the standard candidate.
   With the bridge above, the target can be stated as ONE equation for the
   involutive `H` instead of an intersection of two support conditions. Every
   intermediate step (domain, spectral sign, carrier transport, window
   restriction) is an independent theorem and none of them is formalized.

## 5. Ledger

```text
+---------------------------------------------+-----------------------------------+
| object                                      | status after this record          |
+---------------------------------------------+-----------------------------------+
| carrier <-> radial ±1 eigenvector of H      | FORMAL (bridge + audit, 5 decls)  |
| base obligation archimedeanSoninCarrier_... | OPEN (a def, not a theorem; F33)  |
| H unitarily equivalent to the reflection    | PAPER (half-phase computation)    |
| carrier = de Branges/Sonin W                | 1590 (unchanged)                  |
| T4 prolate construction                     | OPEN, the productive route        |
| (star) / B4 / rho5 / S3 / StripDensity      | OPEN (unchanged)                  |
| RH                                          | NOT claimed                       |
+---------------------------------------------+-----------------------------------+
```

## 6. Acceptance

Same wave build:
`/home/peter/rh/build-logs/1618_strip_confinement_carrier_bridge.log` —
`Build completed successfully (4076 jobs)`, zero `error:` lines, zero
`sorryAx`, five standard axiom prints for this module (14 in the wave), no
warning in the new modules.