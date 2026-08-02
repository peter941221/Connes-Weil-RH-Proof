/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary

/-!
# Complete coupled signed scalar owner

Proof 695 packages the route-level signed scalar object that remains after
the positive radial Cauchy producer was rejected by Proof 694.  The owner
stores one target for every route index and requires an exact identification
with the already defined complete adjoint coboundary target.  Consequently
the outer, reflected, second-support, and prolate branches stay coupled in
every readback.

The compact-support part is intentionally an explicit source contract.  If a
source theorem supplies eventual vanishing of the signed paired scalar, this
module turns it into an exact finite-prefix truncation before any norm is
taken.  It does not assert that the complete coupled target has compact
support, and it does not provide the missing Gate 3U uniform bound.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSignedScalarOwner

open MeasureTheory Filter Function Set Topology
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPointwiseAlternatingPrimitive
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedScalarCorrelation
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorPairedCorrelationCoboundary

/-! ## The complete coupled owner -/

/-- A route-level scalar owner with one complete coupled target per route.
The equality field is the semantic guard: a consumer cannot silently replace
the target by one of the physical branch factors. -/
structure SuffixCompleteCoupledSignedScalarOwner where
  routeOwner : SelectedWeilSquare.SelectedWeilSquareOwner
  target : RouteFiniteHorizonIndex →
    sourceSoninCarrier unitSoninScale →L[Complex] finiteSCarrier
  target_eq_complete : ∀ index : RouteFiniteHorizonIndex,
    target index =
      routePrimeLogAdjointCoboundaryTarget routeOwner index

/-- The canonical owner for the actual route target. -/
noncomputable def canonicalSuffixCompleteCoupledSignedScalarOwner
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledSignedScalarOwner :=
  { routeOwner := owner
    target := routePrimeLogAdjointCoboundaryTarget owner
    target_eq_complete := fun _ => rfl }

theorem target_eq_complete_coboundary
    (signedOwner : SuffixCompleteCoupledSignedScalarOwner)
    (index : RouteFiniteHorizonIndex) :
    signedOwner.target index =
      routePrimeLogAdjointCoboundaryTarget signedOwner.routeOwner index :=
  signedOwner.target_eq_complete index

/-! ## Signed paired scalar readback -/

/-- One adjacent signed scalar pair against the complete coupled target. -/
noncomputable def signedScalarPairedCorrelation
    (signedOwner : SuffixCompleteCoupledSignedScalarOwner)
    (index : RouteFiniteHorizonIndex) (j : Nat)
    (u : finiteSCarrier) (v : sourceSoninCarrier unitSoninScale) : Complex :=
  inner Complex
      (cc20GlobalLogTranslation
        ((2 * j : Nat) * Real.log index.prime) u)
      (signedOwner.target index v)

/-- The packaged signed pair is exactly the existing route pair. -/
theorem signedScalarPairedCorrelation_eq_routePrimeLogPairedScalarCorrelation
    (signedOwner : SuffixCompleteCoupledSignedScalarOwner)
    (index : RouteFiniteHorizonIndex) (j : Nat)
    (u : finiteSCarrier) (v : sourceSoninCarrier unitSoninScale) :
    signedScalarPairedCorrelation signedOwner index j u v =
      routePrimeLogPairedScalarCorrelation signedOwner.routeOwner index j u v := by
  unfold signedScalarPairedCorrelation
  rw [signedOwner.target_eq_complete index]
  exact
    (routePrimeLogPairedScalarCorrelation_eq_adjointCoboundary
      signedOwner.routeOwner index j u v).symm

/-- The adjacent pair is the one-step coboundary on the complete target.
The coboundary is already part of the owner target, so this theorem does not
apply a second coboundary. -/
theorem signedScalarPairedCorrelation_eq_adjointCoboundary
    (signedOwner : SuffixCompleteCoupledSignedScalarOwner)
    (index : RouteFiniteHorizonIndex) (j : Nat)
    (u : finiteSCarrier) (v : sourceSoninCarrier unitSoninScale) :
    signedScalarPairedCorrelation signedOwner index j u v =
      inner Complex
        (cc20GlobalLogTranslation
          ((2 * j : Nat) * Real.log index.prime) u)
        (routePrimeLogAdjointCoboundaryTarget
          signedOwner.routeOwner index v) := by
  unfold signedScalarPairedCorrelation
  rw [signedOwner.target_eq_complete index]

/-! ## Compact-support cancellation contract -/

/-- Source contract for compact-support cancellation at the signed scalar
level.  It is deliberately stated on the complete paired scalar and not on
individual physical branches. -/
def SuffixCompleteCoupledRouteCompactSupportScalarCancellation
    (signedOwner : SuffixCompleteCoupledSignedScalarOwner) : Prop :=
  ∀ u : finiteSCarrier, ∀ v : sourceSoninCarrier unitSoninScale,
    ∀ index : RouteFiniteHorizonIndex, ∃ cutoff : Nat, ∀ j : Nat,
      cutoff ≤ j → signedScalarPairedCorrelation signedOwner index j u v = 0

/-- A compact-support cancellation contract gives the corresponding route
pair vanishing without changing its complete coupled target. -/
theorem routePrimeLogPairedScalarCorrelation_eq_zero_of_compactSupportCancellation
    {signedOwner : SuffixCompleteCoupledSignedScalarOwner}
    (hcancel :
      SuffixCompleteCoupledRouteCompactSupportScalarCancellation signedOwner)
    (u : finiteSCarrier) (v : sourceSoninCarrier unitSoninScale)
    (index : RouteFiniteHorizonIndex) :
    ∃ cutoff : Nat, ∀ j : Nat, cutoff ≤ j →
      routePrimeLogPairedScalarCorrelation signedOwner.routeOwner index j u v = 0 := by
  obtain ⟨cutoff, hzero⟩ := hcancel u v index
  refine ⟨cutoff, ?_⟩
  intro j hj
  rw [← signedScalarPairedCorrelation_eq_routePrimeLogPairedScalarCorrelation
    signedOwner index j u v]
  exact hzero j hj

/-! ## Finite-prefix truncation before taking norms -/

theorem sum_range_eq_cutoff_of_tail_zero
    {A : Type*} [AddCommMonoid A]
    (term : Nat → A) (cutoff N : Nat) (hcutoff : cutoff ≤ N)
    (hzero : ∀ j : Nat, cutoff ≤ j → term j = 0) :
    ∑ j ∈ Finset.range N, term j =
      ∑ j ∈ Finset.range cutoff, term j := by
  induction N, hcutoff using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
      rw [Finset.sum_range_succ, ih,
        hzero N (by omega), add_zero]

/-- The signed paired prefix is exactly its compact-support-truncated prefix.
The equality is scalar and is established before any norm or triangle
inequality is introduced. -/
theorem sum_signedScalarPairedCorrelation_eq_cutoff_of_compactSupportCancellation
    {signedOwner : SuffixCompleteCoupledSignedScalarOwner}
    (hcancel :
      SuffixCompleteCoupledRouteCompactSupportScalarCancellation signedOwner)
    (u : finiteSCarrier) (v : sourceSoninCarrier unitSoninScale)
    (index : RouteFiniteHorizonIndex) :
    ∃ cutoff : Nat, ∀ N : Nat, cutoff ≤ N →
      (∑ j ∈ Finset.range N,
          signedScalarPairedCorrelation signedOwner index j u v) =
        ∑ j ∈ Finset.range cutoff,
          signedScalarPairedCorrelation signedOwner index j u v := by
  obtain ⟨cutoff, hzero⟩ := hcancel u v index
  refine ⟨cutoff, ?_⟩
  intro N hN
  exact sum_range_eq_cutoff_of_tail_zero
    (fun j => signedScalarPairedCorrelation signedOwner index j u v)
    cutoff N hN hzero

/-- The same truncation is available for the existing route pair, so a later
consumer may apply compact support first and only then take its norm. -/
theorem sum_routePrimeLogPairedScalarCorrelation_eq_cutoff_of_compactSupportCancellation
    {signedOwner : SuffixCompleteCoupledSignedScalarOwner}
    (hcancel :
      SuffixCompleteCoupledRouteCompactSupportScalarCancellation signedOwner)
    (u : finiteSCarrier) (v : sourceSoninCarrier unitSoninScale)
    (index : RouteFiniteHorizonIndex) :
    ∃ cutoff : Nat, ∀ N : Nat, cutoff ≤ N →
      (∑ j ∈ Finset.range N,
          routePrimeLogPairedScalarCorrelation signedOwner.routeOwner index j u v) =
        ∑ j ∈ Finset.range cutoff,
          routePrimeLogPairedScalarCorrelation signedOwner.routeOwner index j u v := by
  obtain ⟨cutoff, hzero⟩ :=
    sum_signedScalarPairedCorrelation_eq_cutoff_of_compactSupportCancellation
      hcancel u v index
  refine ⟨cutoff, ?_⟩
  intro N hN
  calc
    ∑ j ∈ Finset.range N,
        routePrimeLogPairedScalarCorrelation signedOwner.routeOwner index j u v =
      ∑ j ∈ Finset.range N,
        signedScalarPairedCorrelation signedOwner index j u v := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact
            (signedScalarPairedCorrelation_eq_routePrimeLogPairedScalarCorrelation
              signedOwner index j u v).symm
    _ = ∑ j ∈ Finset.range cutoff,
        signedScalarPairedCorrelation signedOwner index j u v := hzero N hN
    _ = ∑ j ∈ Finset.range cutoff,
        routePrimeLogPairedScalarCorrelation signedOwner.routeOwner index j u v := by
          apply Finset.sum_congr rfl
          intro j _hj
          exact signedScalarPairedCorrelation_eq_routePrimeLogPairedScalarCorrelation
            signedOwner index j u v

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSignedScalarOwner
end CCM25Concrete
end Source
end ConnesWeilRH
