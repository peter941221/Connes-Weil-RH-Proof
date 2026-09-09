/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriP2Bridge
import ConnesWeilRH.Dev.C1B5TargetSatisfiability

/-!
# C1AggregateSocketSatisfiability - Stage-0 target audit for the 1209 signed-tail recon

Record 1226 section 4.  Two things are established here, both by pure
composition of committed theorems; no new analysis is performed.

`A1`/`A1b`/`A2` (the kill lemmas).  The aggregate Route-1 socket forces
`0 <= qw g` unconditionally: `qw_nonneg_of_bombieriQuadraticAggregateP2BridgeData`
reads the signed repayment lower bound through the unconditional finite-form
positivity `bombieriHMatrix_quadraticForm_eq_ofReal_nonneg`, with no eigen
relation, no healthiness, and no spectral hypothesis.  Healthy detector data
forces `qw g < 0` (record 1225 `L1`).  Hence the bundled consumer conjunction

```text
  HealthyYoshidaDetectorData rho.1 g /\
    Nonempty (BombieriQuadraticAggregateP2BridgeData g)
```

of `sourceRH_of_right_bombieriQuadraticAggregateP2BridgeData` has NO witness
for any `rho` and any `g`, and the signed-tail producer obligation
(`spectralTail_ge_neg_quadratic`, the exit (a) named by record 1209) is
refuted for every healthy test at every finite-parameter choice
`(gamma, z, t, N)`.  This completes the `not_..._of_healthyDetectorData`
guard family of `C1BombieriP2Bridge` (which already exists for all five
sibling sockets but was missing for the aggregate one) and supersedes the
record 1209 fourth-order no-go IN THE CONSUMER CONTEXT: the spectral
hypotheses there are unnecessary for the route ruling.

`A4` (the re-point marker).  The same socket family, universally quantified
over the healthy triple-vanishing class - the non-bundled shape whose
instances can be true - composes with the committed detector existence and
`healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg` to reach
`SourceRH`, mirroring record 1225 `L4` on the projection side.  This
theorem is a formal re-point marker only: no instance of its premise is
claimed, and record 1226 section 3 C3 records that the per-instance
obligation instance-reduces to the gate sign plus unaudited field1
realizability plumbing.

This module claims no witness of either the bundled or the universal
conjunction, proves no sign of `qw` for any concrete test, and is NOT an RH
proof.  RH is not claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1AggregateSocketSatisfiability

open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CC20Concrete
open CCM25Concrete.CompactLogConvolution
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1BombieriP2Bridge

noncomputable section

/-- `A1`.  The unconditional aggregate-socket guard completing the
`not_..._of_healthyDetectorData` family: the socket reads back
`0 <= qw g` through the committed unconditional finite-form positivity,
while detector data forces `qw g < 0`.  No `FourthOrderSpectralTail`,
prefix anchor, or geometric budget hypothesis is consumed (record 1226
section 2, K1-K3). -/
theorem not_bombieriQuadraticAggregateP2BridgeData_of_healthyDetectorData
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g)
    (p : BombieriQuadraticAggregateP2BridgeData g) : False := by
  have hge : 0 ≤ C1SameOwnerWeil.qw g :=
    qw_nonneg_of_bombieriQuadraticAggregateP2BridgeData p
  have hlt : C1SameOwnerWeil.qw g < 0 :=
    C1B5TargetSatisfiability.qw_neg_of_healthyDetectorData hdata
  exact (not_lt_of_ge hge) hlt

/-- `A1b`.  Household nonempty form of `A1`, mirroring the existing
`not_nonempty_bombieriQuadraticP2BridgeData_of_healthyDetectorData` of
record 1208. -/
theorem not_nonempty_bombieriQuadraticAggregateP2BridgeData_of_healthyDetectorData
    {rho : Complex} {g : CompactLogTest}
    (hdata : HealthyYoshidaDetectorData rho g) :
    ¬ Nonempty (BombieriQuadraticAggregateP2BridgeData g) := by
  intro hp
  obtain ⟨p⟩ := hp
  exact not_bombieriQuadraticAggregateP2BridgeData_of_healthyDetectorData hdata p

/-- `A2`.  For every right-of-line source zero the bundled aggregate
producer existential has no witness; the premise of
`sourceRH_of_right_bombieriQuadraticAggregateP2BridgeData` is therefore
vacuous truth in disguise, not a constructive obligation.  As in record
1225 `L3`, the `hright` hypothesis strengthens only the consumer context:
the conjunction is false for every `rho`. -/
theorem no_rightZero_aggregateProducer_witness
    (rho : sourceNontrivialZeroSet) (_hright : (1 / 2 : Real) < rho.1.re) :
    ¬ ∃ g : CompactLogTest,
        HealthyYoshidaDetectorData rho.1 g ∧
          Nonempty (BombieriQuadraticAggregateP2BridgeData g) := by
  rintro ⟨g, hdata, hp⟩
  exact not_nonempty_bombieriQuadraticAggregateP2BridgeData_of_healthyDetectorData
    hdata hp

/-- `A4`.  The re-point marker: the aggregate socket family, universally
quantified over the healthy triple-vanishing class, discharges the
committed capstone premise together with the committed right-zero detector
existence and reaches `SourceRH`.  The transferred obligation is precisely

```text
  forall g, CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g ->
    Nonempty (BombieriQuadraticAggregateP2BridgeData g),
```

a per-vanishing-test signed-repayment contract, never a conjunction that
has to carry both signs at once.  No instance of the premise is claimed
here; record 1226 section 3 C3 flags the field1 realizability question as
unaudited. -/
theorem sourceRH_of_all_vanishing_aggregateSockets
    (hsockets : ∀ g : CompactLogTest,
        CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g →
          Nonempty (BombieriQuadraticAggregateP2BridgeData g)) :
    RHDefinitionBridge.standard.SourceRH :=
  healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg
    (fun rho hright =>
      exists_healthyDetectorData_of_sourceNontrivialZero_right rho
        (by linarith) hright)
    (fun g hvanishing => by
      obtain ⟨p⟩ := hsockets g hvanishing
      have hqw : 0 ≤ C1SameOwnerWeil.qw g :=
        qw_nonneg_of_bombieriQuadraticAggregateP2BridgeData p
      rw [← C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo g]
      exact hqw)

end
end C1AggregateSocketSatisfiability
end Source
end ConnesWeilRH
