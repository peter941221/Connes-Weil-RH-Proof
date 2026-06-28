/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact

/-!
# CCM25 source prime-power support record

This module makes the next finite-prime target more concrete than
`ExactSupportAtLambda`. It names the source prime-power predicate, source atom
visibility for `F_g`, and the restricted lambda cut
`1 < n` and `(n : Real) <= lambda^2`.

It still does not prove that CCM25 supplies this record. It proves only that
such a record is strong enough to create the fixed-window exact-support
certificate used by `FinitePrimeExact`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerSupport

def SourceLambdaCut (lambda : ℝ) (n : ℕ) : Prop :=
  1 < n ∧ (n : ℝ) ≤ lambda ^ 2

structure SourcePrimePowerSupportSkeletonAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  sourcePrimePowerIndex : ℕ → Prop
  sourceAtomVisible : ℕ → TestFunction → Prop
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        sourcePrimePowerIndex n ∧
          sourceAtomVisible n (W.convolutionStar f g)
  globalExact :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        sourcePrimePowerIndex n ∧
          sourceAtomVisible n (W.convolutionStar f g)
  restrictedExact :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        sourcePrimePowerIndex n ∧
          sourceAtomVisible n (W.convolutionStar f g) ∧
            SourceLambdaCut lambda n
  visibleAtomsInLambdaCut :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        SourceLambdaCut lambda n

structure SourcePrimePowerSupportAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  sourcePrimePowerIndex : ℕ → Prop
  sourceAtomVisible : ℕ → TestFunction → Prop
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        sourcePrimePowerIndex n ∧
          sourceAtomVisible n (W.convolutionStar f g)
  globalExact :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        sourcePrimePowerIndex n ∧
          sourceAtomVisible n (W.convolutionStar f g)
  restrictedExact :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        sourcePrimePowerIndex n ∧
          sourceAtomVisible n (W.convolutionStar f g) ∧
            SourceLambdaCut lambda n
  visibleAtomsInLambdaCut :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        SourceLambdaCut lambda n
  termNormalization :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g

def source_prime_power_support_of_skeleton
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (hS : SourcePrimePowerSupportSkeletonAtLambda W f g lambda)
    (hT : WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g) :
    SourcePrimePowerSupportAtLambda W f g lambda where
  oneLtLambda := hS.oneLtLambda
  sourcePrimePowerIndex := hS.sourcePrimePowerIndex
  sourceAtomVisible := hS.sourceAtomVisible
  visibleIff := hS.visibleIff
  globalExact := hS.globalExact
  restrictedExact := hS.restrictedExact
  visibleAtomsInLambdaCut := hS.visibleAtomsInLambdaCut
  termNormalization := hT

def exact_support_of_source_prime_power_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerSupportAtLambda W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda where
  oneLtLambda := h.oneLtLambda
  sourcePrimePowerIndex := h.sourcePrimePowerIndex
  sourceAtomVisible := fun n => h.sourceAtomVisible n (W.convolutionStar f g)
  sourceInLambdaCut := SourceLambdaCut lambda
  sourceVisibleIff := h.visibleIff
  globalExact := h.globalExact
  restrictedExact := h.restrictedExact
  visibleAtomsInLambdaCut := h.visibleAtomsInLambdaCut
  termNormalization := h.termNormalization

theorem visibility_at_lambda_of_source_prime_power_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerSupportAtLambda W f g lambda) :
    FinitePrimeExact.FinitePrimeVisibilityAtLambdaStatement W f g lambda :=
  FinitePrimeExact.visibility_at_lambda_of_exact_support
    (exact_support_of_source_prime_power_support h)

end PrimePowerSupport
end CCM25Concrete
end Source
end ConnesWeilRH
