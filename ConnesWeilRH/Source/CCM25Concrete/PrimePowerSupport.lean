/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact
import ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerTest

/-!
# CCM25 source prime-power support record

This module makes the next finite-prime target more concrete than
`ExactSupportAtLambda`. It fixes prime-power support to Mathlib's `IsPrimePow`,
names source atom visibility for `F_g`, and records the restricted lambda cut
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

theorem source_lambda_cut_iff
    {lambda : ℝ} {n : ℕ} :
    SourceLambdaCut lambda n ↔ 1 < n ∧ (n : ℝ) ≤ lambda ^ 2 :=
  Iff.rfl

theorem source_lambda_cut_of_bounds
    {lambda : ℝ} {n : ℕ}
    (hone : 1 < n) (hle : (n : ℝ) ≤ lambda ^ 2) :
    SourceLambdaCut lambda n :=
  ⟨hone, hle⟩

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

theorem source_lambda_cut_one_lt_of_bounds
    {lambda : ℝ} {n : ℕ}
    (hone : 1 < n) (hle : (n : ℝ) ≤ lambda ^ 2) :
    1 < n :=
  (source_lambda_cut_of_bounds hone hle).1

theorem source_lambda_cut_le_lambda_sq_of_bounds
    {lambda : ℝ} {n : ℕ}
    (hone : 1 < n) (hle : (n : ℝ) ≤ lambda ^ 2) :
    (n : ℝ) ≤ lambda ^ 2 :=
  (source_lambda_cut_of_bounds hone hle).2

structure SourceGlobalIndexData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  primePowerIndex : IsPrimePow n
  atomVisible : W.finitePrimeAtomVisible n (W.convolutionStar f g)

structure SourceVisibleAtomData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  primePowerIndex : IsPrimePow n
  atomVisible : W.finitePrimeAtomVisible n (W.convolutionStar f g)

structure SourceRestrictedIndexData
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) (n : ℕ) where
  primePowerIndex : IsPrimePow n
  atomVisible : W.finitePrimeAtomVisible n (W.convolutionStar f g)
  lambdaCut : SourceLambdaCut lambda n

theorem source_visible_atom_prime_power_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceVisibleAtomData W f g n) :
    IsPrimePow n :=
  h.primePowerIndex

theorem source_visible_atom_visible
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceVisibleAtomData W f g n) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) :=
  h.atomVisible

theorem source_visible_atom_one_lt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceVisibleAtomData W f g n) :
    1 < n :=
  IsPrimePow.one_lt h.primePowerIndex

theorem source_global_index_to_visible_atom_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceGlobalIndexData W f g n) :
    SourceVisibleAtomData W f g n where
  primePowerIndex := h.primePowerIndex
  atomVisible := h.atomVisible

theorem source_global_index_prime_power_index
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceGlobalIndexData W f g n) :
    IsPrimePow n :=
  h.primePowerIndex

theorem source_global_index_visible
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceGlobalIndexData W f g n) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) :=
  h.atomVisible

theorem source_global_index_one_lt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceGlobalIndexData W f g n) :
    1 < n :=
  IsPrimePow.one_lt h.primePowerIndex

theorem source_visible_atom_to_global_index_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceVisibleAtomData W f g n) :
    SourceGlobalIndexData W f g n where
  primePowerIndex := h.primePowerIndex
  atomVisible := h.atomVisible

theorem source_restricted_index_to_global_index_data
    {W : WeilFormSymbols} {f g : TestFunction}
    {lambda : ℝ} {n : ℕ}
    (h : SourceRestrictedIndexData W f g lambda n) :
    SourceGlobalIndexData W f g n where
  primePowerIndex := h.primePowerIndex
  atomVisible := h.atomVisible

theorem source_restricted_index_to_visible_atom_data
    {W : WeilFormSymbols} {f g : TestFunction}
    {lambda : ℝ} {n : ℕ}
    (h : SourceRestrictedIndexData W f g lambda n) :
    SourceVisibleAtomData W f g n where
  primePowerIndex := h.primePowerIndex
  atomVisible := h.atomVisible

theorem source_restricted_index_prime_power_index
    {W : WeilFormSymbols} {f g : TestFunction}
    {lambda : ℝ} {n : ℕ}
    (h : SourceRestrictedIndexData W f g lambda n) :
    IsPrimePow n :=
  h.primePowerIndex

theorem source_restricted_index_visible
    {W : WeilFormSymbols} {f g : TestFunction}
    {lambda : ℝ} {n : ℕ}
    (h : SourceRestrictedIndexData W f g lambda n) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) :=
  h.atomVisible

theorem source_restricted_index_lambda_cut
    {W : WeilFormSymbols} {f g : TestFunction}
    {lambda : ℝ} {n : ℕ}
    (h : SourceRestrictedIndexData W f g lambda n) :
    SourceLambdaCut lambda n :=
  h.lambdaCut

theorem source_restricted_index_one_lt
    {W : WeilFormSymbols} {f g : TestFunction}
    {lambda : ℝ} {n : ℕ}
    (h : SourceRestrictedIndexData W f g lambda n) :
    1 < n :=
  h.lambdaCut.1

theorem source_restricted_index_le_lambda_sq
    {W : WeilFormSymbols} {f g : TestFunction}
    {lambda : ℝ} {n : ℕ}
    (h : SourceRestrictedIndexData W f g lambda n) :
    (n : ℝ) ≤ lambda ^ 2 :=
  h.lambdaCut.2

structure SourcePrimePowerSupportSkeletonAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        SourceVisibleAtomData W f g n
  globalIndexData :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet →
        SourceGlobalIndexData W f g n
  routeVisibleGlobalIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        n ∈ W.globalPrimeIndexSet
  restrictedIndexData :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda →
        SourceRestrictedIndexData W f g lambda n
  routeVisibleRestrictedIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        1 < n → (n : ℝ) ≤ lambda ^ 2 →
        n ∈ W.restrictedPrimeIndexSet lambda

namespace SourcePrimePowerSupportSkeletonAtLambda

theorem globalExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerSupportSkeletonAtLambda W f g lambda)
    (n : ℕ) :
    n ∈ W.globalPrimeIndexSet ↔
      SourceGlobalIndexData W f g n := by
  constructor
  · exact h.globalIndexData n
  · intro hdata
    exact h.routeVisibleGlobalIndex n ((h.visibleIff n).2
      (source_global_index_to_visible_atom_data hdata))

theorem restrictedExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerSupportSkeletonAtLambda W f g lambda)
    (n : ℕ) :
    n ∈ W.restrictedPrimeIndexSet lambda ↔
      SourceRestrictedIndexData W f g lambda n := by
  constructor
  · exact h.restrictedIndexData n
  · intro hdata
    exact h.routeVisibleRestrictedIndex n ((h.visibleIff n).2
      (source_restricted_index_to_visible_atom_data hdata))
      hdata.lambdaCut.1 hdata.lambdaCut.2

end SourcePrimePowerSupportSkeletonAtLambda

structure SourcePrimePowerArithmeticSupportSkeletonAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g
  visibleArithmeticData :
    PrimePowerArithmetic.SourceVisibleFinitePrimeArithmeticData
      W f g sourceTest
  globalIndexData :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet →
        SourceGlobalIndexData W f g n
  routeVisibleGlobalIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        n ∈ W.globalPrimeIndexSet
  restrictedIndexData :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda →
        SourceRestrictedIndexData W f g lambda n
  routeVisibleRestrictedIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        1 < n → (n : ℝ) ≤ lambda ^ 2 →
        n ∈ W.restrictedPrimeIndexSet lambda

namespace SourcePrimePowerArithmeticSupportSkeletonAtLambda

def sourceVisibleArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda)
    (n : ℕ)
    (hn : h.sourceTest.sourceAtomVisible n) :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticData W f g n :=
  h.visibleArithmeticData.atVisibleIndex n hn

theorem restrictedPrimeIndexCoverage
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda) :
    WeilFormSymbols.RestrictedPrimeIndexCoverageStatement W lambda
      (W.convolutionStar f g) := by
  intro n hvisible hOne hCutoff
  exact h.routeVisibleRestrictedIndex n hvisible hOne hCutoff

theorem globalPrimeIndexCoverage
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda) :
    WeilFormSymbols.GlobalPrimeIndexCoverageStatement W (W.convolutionStar f g) := by
  intro n hvisible
  exact h.routeVisibleGlobalIndex n hvisible

theorem globalExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda)
    (n : ℕ) :
    n ∈ W.globalPrimeIndexSet ↔
      SourceGlobalIndexData W f g n := by
  constructor
  · exact h.globalIndexData n
  · intro hdata
    exact h.routeVisibleGlobalIndex n hdata.atomVisible

theorem restrictedExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda)
    (n : ℕ) :
    n ∈ W.restrictedPrimeIndexSet lambda ↔
      SourceRestrictedIndexData W f g lambda n := by
  constructor
  · exact h.restrictedIndexData n
  · intro hdata
    exact h.routeVisibleRestrictedIndex n hdata.atomVisible
      hdata.lambdaCut.1 hdata.lambdaCut.2

theorem sourceVisibleGlobalIndex
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda)
    (n : ℕ)
    (hvisible : W.finitePrimeAtomVisible n (W.convolutionStar f g)) :
    n ∈ W.globalPrimeIndexSet :=
  h.routeVisibleGlobalIndex n hvisible

theorem sourceVisiblePrimePower
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda)
    (n : ℕ)
    (hvisible : W.finitePrimeAtomVisible n (W.convolutionStar f g)) :
    IsPrimePow n :=
  (h.sourceVisibleArithmeticData n
    ((PrimePowerTest.route_visibility_iff_source_visibility h.sourceTest n).1
      hvisible)).sourcePrimePowerIndex

theorem visibleIff
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda)
    (n : ℕ) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
      SourceVisibleAtomData W f g n := by
  constructor
  · intro hvisible
    exact
      { primePowerIndex := h.sourceVisiblePrimePower n hvisible
        atomVisible := hvisible }
  · intro hdata
    exact hdata.atomVisible

end SourcePrimePowerArithmeticSupportSkeletonAtLambda

def support_skeleton_of_arithmetic_support_skeleton
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h :
      SourcePrimePowerArithmeticSupportSkeletonAtLambda W f g lambda) :
    SourcePrimePowerSupportSkeletonAtLambda W f g lambda where
  oneLtLambda := h.oneLtLambda
  visibleIff := h.visibleIff
  globalIndexData := h.globalIndexData
  routeVisibleGlobalIndex := h.routeVisibleGlobalIndex
  restrictedIndexData := h.restrictedIndexData
  routeVisibleRestrictedIndex := h.routeVisibleRestrictedIndex

/--
Goal 0D concrete fixed-lambda support data.

This keeps the existing fixed-lambda arithmetic support skeleton, but forces
its source-test interface to be the concrete common source test from Goal
0A/0B.  Thus the lambda cut is attached to the concrete common visibility
predicate instead of an unrelated `sourceAtomVisible` field.
-/
structure ConcreteCommonFixedLambdaPrimePowerSupport
    (W : WeilFormSymbols)
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (lambda : ℝ) where
  support :
    SourcePrimePowerArithmeticSupportSkeletonAtLambda
      W common.sourceTest common.sourceTest lambda
  sourceTestReadOff :
    support.sourceTest = common.toSourceTestEvaluationInterface

namespace ConcreteCommonFixedLambdaPrimePowerSupport

theorem one_lt_lambda
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (h : ConcreteCommonFixedLambdaPrimePowerSupport W common lambda) :
    1 < lambda :=
  h.support.oneLtLambda

theorem source_test_eq_common
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (h : ConcreteCommonFixedLambdaPrimePowerSupport W common lambda) :
    h.support.sourceTest = common.toSourceTestEvaluationInterface :=
  h.sourceTestReadOff

theorem support_visibility_iff_common_visibility
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (h : ConcreteCommonFixedLambdaPrimePowerSupport W common lambda)
    (n : ℕ) :
    h.support.sourceTest.sourceAtomVisible n ↔ common.sourceAtomVisible n := by
  rw [h.sourceTestReadOff]
  rfl

theorem route_visibility_iff_common_visible_atom_data
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (h : ConcreteCommonFixedLambdaPrimePowerSupport W common lambda)
    (n : ℕ) :
    W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest) ↔
      SourceVisibleAtomData W common.sourceTest common.sourceTest n := by
  rw [h.support.visibleIff n]

theorem global_exact_common_visible_atom_data
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (h : ConcreteCommonFixedLambdaPrimePowerSupport W common lambda)
    (n : ℕ) :
    n ∈ W.globalPrimeIndexSet ↔
      SourceGlobalIndexData W common.sourceTest common.sourceTest n := by
  rw [h.support.globalExact n]

theorem restricted_exact_common_visible_atom_data
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (h : ConcreteCommonFixedLambdaPrimePowerSupport W common lambda)
    (n : ℕ) :
    n ∈ W.restrictedPrimeIndexSet lambda ↔
      SourceRestrictedIndexData W common.sourceTest common.sourceTest lambda n := by
  rw [h.support.restrictedExact n]

end ConcreteCommonFixedLambdaPrimePowerSupport

structure SourcePrimePowerSupportAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  visibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        SourceVisibleAtomData W f g n
  globalIndexData :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet →
        SourceGlobalIndexData W f g n
  routeVisibleGlobalIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        n ∈ W.globalPrimeIndexSet
  restrictedIndexData :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda →
        SourceRestrictedIndexData W f g lambda n
  routeVisibleRestrictedIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        1 < n → (n : ℝ) ≤ lambda ^ 2 →
        n ∈ W.restrictedPrimeIndexSet lambda
  termNormalization :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g

namespace SourcePrimePowerSupportAtLambda

theorem globalExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerSupportAtLambda W f g lambda)
    (n : ℕ) :
    n ∈ W.globalPrimeIndexSet ↔
      SourceGlobalIndexData W f g n := by
  constructor
  · exact h.globalIndexData n
  · intro hdata
    exact h.routeVisibleGlobalIndex n ((h.visibleIff n).2
      (source_global_index_to_visible_atom_data hdata))

theorem restrictedExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerSupportAtLambda W f g lambda)
    (n : ℕ) :
    n ∈ W.restrictedPrimeIndexSet lambda ↔
      SourceRestrictedIndexData W f g lambda n := by
  constructor
  · exact h.restrictedIndexData n
  · intro hdata
    exact h.routeVisibleRestrictedIndex n ((h.visibleIff n).2
      (source_restricted_index_to_visible_atom_data hdata))
      hdata.lambdaCut.1 hdata.lambdaCut.2

end SourcePrimePowerSupportAtLambda

def source_prime_power_support_of_skeleton
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (hS : SourcePrimePowerSupportSkeletonAtLambda W f g lambda)
    (hT : WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g) :
    SourcePrimePowerSupportAtLambda W f g lambda where
  oneLtLambda := hS.oneLtLambda
  visibleIff := hS.visibleIff
  globalIndexData := hS.globalIndexData
  routeVisibleGlobalIndex := hS.routeVisibleGlobalIndex
  restrictedIndexData := hS.restrictedIndexData
  routeVisibleRestrictedIndex := hS.routeVisibleRestrictedIndex
  termNormalization := hT

def exact_support_of_source_prime_power_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourcePrimePowerSupportAtLambda W f g lambda) :
    FinitePrimeExact.ExactSupportAtLambda W f g lambda where
  oneLtLambda := h.oneLtLambda
  sourceVisiblePrimePower := by
    intro n
    intro hn
    exact ((h.visibleIff n).1 hn).primePowerIndex
  globalIndexData := by
    intro n hn
    let hdata := h.globalIndexData n hn
    exact
      ⟨hdata.primePowerIndex,
        (h.visibleIff n).2
          (source_global_index_to_visible_atom_data hdata)⟩
  routeVisibleGlobalIndex := h.routeVisibleGlobalIndex
  restrictedIndexData := by
    intro n hn
    let hdata := h.restrictedIndexData n hn
    exact
      ⟨hdata.primePowerIndex,
        (h.visibleIff n).2
          (source_restricted_index_to_visible_atom_data hdata),
        hdata.lambdaCut⟩
  routeVisibleRestrictedIndex := h.routeVisibleRestrictedIndex
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
