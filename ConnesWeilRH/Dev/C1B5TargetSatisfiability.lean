/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1Stage3ProjectionOperatorFamily

/-!
# C1B5TargetSatisfiability - Stage-0 target audit for the B5 producer campaign

Record 1225 section 3.  Two things are established here, both by pure
composition of committed theorems; no new analysis is performed.

`L1`/`L2`/`L3` (the kill lemmas).  Healthy detector data forces strict
negativity `qw g < 0` (`weilSquareSumPositive_iff_spectralWeilValue_neg` plus
the center-`2` readback), while a `ProjectionCutoffLimitContracts` instance
forces `0 <= qw g` through unconditional operator positivity.  Hence the
bundled B5 producer conjunction

```text
  HealthyYoshidaDetectorData rho.1 g /\
    Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis)
```

has NO witness for any `rho` and any `g`: the premise of
`sourceRH_of_healthyDetector_p2ProjectionCutoffLimitContracts` can hold only
vacuously (when no right-of-line source zero exists), so it admits no
constructive production program.  This reclassifies the closed 1224 Stage-B
evidence: the model readout `FP_inf != qw` on the detector twin was forced by
sign, not diagnosed by rank.

`L4` (the re-point).  The SAME contract family, universally quantified over
the healthy triple-vanishing class - a proposition whose instances can be
true, since the detector obstruction lives outside that quantifier - composes
with the committed detector existence and
`healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg` to reach
`SourceRH` with no hypothesis except the universal contract itself.

This module claims no witness of either the bundled or the universal
conjunction, proves no sign of `qw` for any concrete test, and is NOT an RH
proof.  RH is not claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1B5TargetSatisfiability

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CC20Concrete
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open Dev.C1Stage3ProjectionOperatorFamily

noncomputable section

/-- `L1`.  Detector data forces strict negativity of the same-owner `qw`,
independently of which zero it detects: the sign field reads through the
proved center-`2` chain. -/
theorem qw_neg_of_healthyDetectorData {rho : ℂ} {g : CompactLogTest}
    (hg : HealthyYoshidaDetectorData rho g) :
    C1SameOwnerWeil.qw g < 0 := by
  have hspectral :
      C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0 :=
    (weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
      hg.weilSquareSumPositive
  rw [C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo g]
  exact hspectral

/-- `L2`.  No test carries both healthy detector data and a
`ProjectionCutoffLimitContracts` instance: the contract reads back `0 <= qw`
through unconditional positivity (`cutoffProjectionOperator_isPositive`),
while detector data forces `qw < 0`. -/
theorem not_healthy_of_projectionCutoffContracts
    {ν : Type*} {rho : ℂ} {g : CompactLogTest}
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (hcontracts :
      Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis))
    (hg : HealthyYoshidaDetectorData rho g) : False := by
  obtain ⟨hc⟩ := hcontracts
  have hge : 0 ≤ C1SameOwnerWeil.qw g :=
    qw_nonnegative_of_projectionCutoffLimitContracts g lambda S globalBasis hc
  have hlt : C1SameOwnerWeil.qw g < 0 := qw_neg_of_healthyDetectorData hg
  linarith

/-- `L3`.  For every right-of-line source zero the bundled B5 producer
existential has no witness; the premise of
`sourceRH_of_healthyDetector_p2ProjectionCutoffLimitContracts` is therefore
vacuous truth in disguise, not a constructive obligation.  Note that `hright`
is not needed for the refutation itself (it strengthens the consumer
context): the conjunction is false for every `rho : ℂ`. -/
theorem no_rightZero_b5Producer_witness
    {ν : Type*} (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (rho : sourceNontrivialZeroSet) (_hright : (1 / 2 : Real) < rho.1.re) :
    ¬ ∃ g : CompactLogTest,
        HealthyYoshidaDetectorData rho.1 g ∧
          Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis) := by
  rintro ⟨g, hg, hcontracts⟩
  exact not_healthy_of_projectionCutoffContracts lambda S globalBasis hcontracts hg

/-- `L4`.  The re-point: the same contract family, universally quantified
over the healthy triple-vanishing class, discharges the committed capstone
premise together with the committed right-zero detector existence and reaches
`SourceRH`.  The obligation transferred by this theorem is precisely

```text
  forall g, CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g ->
    Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis),
```

a per-vanishing-test positive-trace readback, never a conjunction that has
to carry both signs at once.  No instance of the premise is claimed here. -/
theorem sourceRH_of_all_vanishing_projectionContracts
    {ν : Type*}
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (globalBasis : HilbertBasis ν ℂ projectionCarrier)
    (hcontracts : ∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g →
          Nonempty (ProjectionCutoffLimitContracts g lambda S globalBasis)) :
    RHDefinitionBridge.standard.SourceRH :=
  healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg
    (fun rho hright =>
      exists_healthyDetectorData_of_sourceNontrivialZero_right rho
        (by linarith) hright)
    (fun g hvanishing => by
      obtain ⟨hc⟩ := hcontracts g hvanishing
      have hqw : 0 ≤ C1SameOwnerWeil.qw g :=
        qw_nonnegative_of_projectionCutoffLimitContracts g lambda S globalBasis hc
      rw [← C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo g]
      exact hqw)

end
end C1B5TargetSatisfiability
end Source
end ConnesWeilRH
