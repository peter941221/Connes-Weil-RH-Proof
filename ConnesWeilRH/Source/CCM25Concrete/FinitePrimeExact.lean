/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrime

/-!
# CCM25 finite-prime exact support at a fixed lambda

This module is deliberately fixed-`lambda`. The current broad interface has a
`forall lambda` visibility statement, but the source restricted formula is a
lambda-window cut. Proving exact support one fixed window at a time prevents a
future proof from silently treating one-way coverage as exact support for every
cutoff.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FinitePrimeExact

def FinitePrimeVisibilityAtLambdaStatement
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) : Prop :=
  let F := W.convolutionStar f g
  WeilFormSymbols.GlobalPrimeIndexCoverageStatement W F ∧
    WeilFormSymbols.RestrictedPrimeIndexCoverageStatement W lambda F ∧
      WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g

structure ExactSupportAtLambda
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  sourceVisiblePrimePower :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        IsPrimePow n
  globalIndexData :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet →
        IsPrimePow n ∧
          W.finitePrimeAtomVisible n (W.convolutionStar f g)
  routeVisibleGlobalIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        n ∈ W.globalPrimeIndexSet
  restrictedIndexData :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda →
        IsPrimePow n ∧
          W.finitePrimeAtomVisible n (W.convolutionStar f g) ∧
          1 < n ∧ (n : ℝ) ≤ lambda ^ 2
  routeVisibleRestrictedIndex :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        1 < n → (n : ℝ) ≤ lambda ^ 2 →
        n ∈ W.restrictedPrimeIndexSet lambda
  termNormalization :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g

namespace ExactSupportAtLambda

theorem globalExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda)
    (n : ℕ) :
    n ∈ W.globalPrimeIndexSet ↔
      IsPrimePow n ∧
        W.finitePrimeAtomVisible n (W.convolutionStar f g) := by
  constructor
  · exact h.globalIndexData n
  · intro hdata
    exact h.routeVisibleGlobalIndex n hdata.2

theorem restrictedExact
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda)
    (n : ℕ) :
    n ∈ W.restrictedPrimeIndexSet lambda ↔
      IsPrimePow n ∧
        W.finitePrimeAtomVisible n (W.convolutionStar f g) ∧
        1 < n ∧ (n : ℝ) ≤ lambda ^ 2 := by
  constructor
  · exact h.restrictedIndexData n
  · intro hdata
    exact h.routeVisibleRestrictedIndex n hdata.2.1
      hdata.2.2.1 hdata.2.2.2

end ExactSupportAtLambda

theorem global_coverage_of_exact_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda) :
    WeilFormSymbols.GlobalPrimeIndexCoverageStatement W
      (W.convolutionStar f g) := by
  intro n hn
  exact h.routeVisibleGlobalIndex n hn

theorem restricted_coverage_of_exact_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda) :
    WeilFormSymbols.RestrictedPrimeIndexCoverageStatement W lambda
      (W.convolutionStar f g) := by
  intro n hn hOne hCutoff
  exact h.routeVisibleRestrictedIndex n hn hOne hCutoff

theorem term_normalization_of_exact_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g :=
  h.termNormalization

theorem visibility_at_lambda_of_exact_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda) :
    FinitePrimeVisibilityAtLambdaStatement W f g lambda :=
  ⟨global_coverage_of_exact_support h,
    restricted_coverage_of_exact_support h,
    term_normalization_of_exact_support h⟩

end FinitePrimeExact
end CCM25Concrete
end Source
end ConnesWeilRH
