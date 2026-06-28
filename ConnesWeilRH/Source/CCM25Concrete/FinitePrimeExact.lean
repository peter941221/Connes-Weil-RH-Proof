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
  sourcePrimePowerIndex : ℕ → Prop
  sourceAtomVisible : ℕ → Prop
  sourceInLambdaCut : ℕ → Prop
  sourceVisibleIff :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
        sourcePrimePowerIndex n ∧ sourceAtomVisible n
  globalExact :
    ∀ n : ℕ,
      n ∈ W.globalPrimeIndexSet ↔
        sourcePrimePowerIndex n ∧ sourceAtomVisible n
  restrictedExact :
    ∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda ↔
        sourcePrimePowerIndex n ∧ sourceAtomVisible n ∧
          sourceInLambdaCut n
  visibleAtomsInLambdaCut :
    ∀ n : ℕ,
      W.finitePrimeAtomVisible n (W.convolutionStar f g) →
        sourceInLambdaCut n
  termNormalization :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g

theorem global_coverage_of_exact_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda) :
    WeilFormSymbols.GlobalPrimeIndexCoverageStatement W
      (W.convolutionStar f g) := by
  intro n hn
  exact (h.globalExact n).2 ((h.sourceVisibleIff n).1 hn)

theorem restricted_coverage_of_exact_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda) :
    WeilFormSymbols.RestrictedPrimeIndexCoverageStatement W lambda
      (W.convolutionStar f g) := by
  intro n hn
  let hvisible := (h.sourceVisibleIff n).1 hn
  exact (h.restrictedExact n).2
    ⟨hvisible.1, hvisible.2, h.visibleAtomsInLambdaCut n hn⟩

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

theorem restricted_index_set_eq_global_of_exact_support
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : ExactSupportAtLambda W f g lambda) :
    W.restrictedPrimeIndexSet lambda = W.globalPrimeIndexSet := by
  apply Finset.ext
  intro n
  constructor
  · intro hn
    let hsource := (h.restrictedExact n).1 hn
    exact (h.globalExact n).2 ⟨hsource.1, hsource.2.1⟩
  · intro hn
    let hsource := (h.globalExact n).1 hn
    let hvisible := (h.sourceVisibleIff n).2 hsource
    exact (h.restrictedExact n).2
      ⟨hsource.1, hsource.2, h.visibleAtomsInLambdaCut n hvisible⟩

end FinitePrimeExact
end CCM25Concrete
end Source
end ConnesWeilRH
