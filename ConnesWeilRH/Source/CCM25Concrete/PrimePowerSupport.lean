/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerTest

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

theorem source_lambda_cut_one_lt
    {lambda : ℝ} {n : ℕ}
    (h : SourceLambdaCut lambda n) :
    1 < n :=
  h.1

theorem source_lambda_cut_le_lambda_sq
    {lambda : ℝ} {n : ℕ}
    (h : SourceLambdaCut lambda n) :
    (n : ℝ) ≤ lambda ^ 2 :=
  h.2

structure SourceGlobalIndexData
    (sourcePrimePowerIndex : ℕ → Prop)
    (sourceAtomVisible : ℕ → Prop) (n : ℕ) where
  primePowerIndex : sourcePrimePowerIndex n
  atomVisible : sourceAtomVisible n

structure SourceVisibleAtomData
    (sourcePrimePowerIndex : ℕ → Prop)
    (sourceAtomVisible : ℕ → Prop) (n : ℕ) where
  primePowerIndex : sourcePrimePowerIndex n
  atomVisible : sourceAtomVisible n

structure SourceRestrictedIndexData
    (sourcePrimePowerIndex : ℕ → Prop)
    (sourceAtomVisible : ℕ → Prop) (lambda : ℝ) (n : ℕ) where
  primePowerIndex : sourcePrimePowerIndex n
  atomVisible : sourceAtomVisible n
  lambdaCut : SourceLambdaCut lambda n

structure SourcePrimePowerSupportSkeletonAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  sourcePrimePowerIndex : ℕ → Prop
  sourceAtomVisible : ℕ → TestFunction → Prop
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        SourceVisibleAtomData sourcePrimePowerIndex
          (fun n => sourceAtomVisible n (W.convolutionStar f g)) n
  globalExact :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        SourceGlobalIndexData sourcePrimePowerIndex
          (fun n => sourceAtomVisible n (W.convolutionStar f g)) n
  restrictedExact :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        SourceRestrictedIndexData sourcePrimePowerIndex
          (fun n => sourceAtomVisible n (W.convolutionStar f g)) lambda n
  visibleAtomsInLambdaCut :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        SourceLambdaCut lambda n

structure SourcePrimePowerArithmeticSupportSkeletonAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        SourceVisibleAtomData PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible n
  globalExact :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        SourceGlobalIndexData PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible n
  restrictedExact :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        SourceRestrictedIndexData PrimePowerArithmetic.SourcePrimePowerIndex
          sourceTest.sourceAtomVisible lambda n
  visibleAtomsInLambdaCut :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        SourceLambdaCut lambda n

def support_skeleton_of_arithmetic_support_skeleton
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h :
      SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda) :
    SourcePrimePowerSupportSkeletonAtLambda W f g lambda where
  oneLtLambda := h.oneLtLambda
  sourcePrimePowerIndex := PrimePowerArithmetic.SourcePrimePowerIndex
  sourceAtomVisible := fun n _ => h.sourceTest.sourceAtomVisible n
  visibleIff := h.visibleIff
  globalExact := h.globalExact
  restrictedExact := h.restrictedExact
  visibleAtomsInLambdaCut := h.visibleAtomsInLambdaCut

theorem support_skeleton_index_of_arithmetic_support_skeleton
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h :
      SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda) :
    (support_skeleton_of_arithmetic_support_skeleton h).sourcePrimePowerIndex =
      PrimePowerArithmetic.SourcePrimePowerIndex :=
  rfl

structure SourcePrimePowerSupportAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  sourcePrimePowerIndex : ℕ → Prop
  sourceAtomVisible : ℕ → TestFunction → Prop
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        SourceVisibleAtomData sourcePrimePowerIndex
          (fun n => sourceAtomVisible n (W.convolutionStar f g)) n
  globalExact :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        SourceGlobalIndexData sourcePrimePowerIndex
          (fun n => sourceAtomVisible n (W.convolutionStar f g)) n
  restrictedExact :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        SourceRestrictedIndexData sourcePrimePowerIndex
          (fun n => sourceAtomVisible n (W.convolutionStar f g)) lambda n
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
  sourceVisibleIff := by
    intro n
    constructor
    · intro hn
      let hdata := (h.visibleIff n).1 hn
      exact ⟨hdata.primePowerIndex, hdata.atomVisible⟩
    · intro hn
      exact (h.visibleIff n).2
        { primePowerIndex := hn.1
          atomVisible := hn.2 }
  globalExact := by
    intro n
    constructor
    · intro hn
      let hdata := (h.globalExact n).1 hn
      exact ⟨hdata.primePowerIndex, hdata.atomVisible⟩
    · intro hn
      exact (h.globalExact n).2
        { primePowerIndex := hn.1
          atomVisible := hn.2 }
  restrictedExact := by
    intro n
    constructor
    · intro hn
      let hdata := (h.restrictedExact n).1 hn
      exact ⟨hdata.primePowerIndex, hdata.atomVisible, hdata.lambdaCut⟩
    · intro hn
      exact (h.restrictedExact n).2
        { primePowerIndex := hn.1
          atomVisible := hn.2.1
          lambdaCut := hn.2.2 }
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
