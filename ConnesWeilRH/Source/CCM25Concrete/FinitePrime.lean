/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25

/-!
# CCM25 finite-prime spine

This small module exposes the current finite-prime coverage and pointwise-term
rows. It also names the stronger exact-support targets that the current
one-way coverage interface does not prove.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FinitePrime

def GlobalPrimeSupportExactStatement
    (W : WeilFormSymbols) (F : TestFunction) : Prop :=
  ∀ n : ℕ, n ∈ W.globalPrimeIndexSet ↔ W.finitePrimeAtomVisible n F

def RestrictedPrimeSupportExactStatement
    (W : WeilFormSymbols) (lambda : ℝ) (F : TestFunction) : Prop :=
  ∀ n : ℕ,
    n ∈ W.restrictedPrimeIndexSet lambda ↔
      W.finitePrimeAtomVisible n F ∧ n ∈ W.globalPrimeIndexSet

def FinitePrimeExactSupportStatement
    (W : WeilFormSymbols) (f g : TestFunction) : Prop :=
  let F := W.convolutionStar f g
  GlobalPrimeSupportExactStatement W F ∧
    ∀ lambda : ℝ,
      1 < lambda → RestrictedPrimeSupportExactStatement W lambda F

theorem global_prime_index_coverage_statement
    (ccm25 : CCM25Interface) (f g : TestFunction) :
    WeilFormSymbols.GlobalPrimeIndexCoverageStatement
      ccm25.weilSymbols
      (ccm25.weilSymbols.convolutionStar f g) :=
  (ccm25.finitePrimeNormalization f g).1

theorem restricted_prime_index_coverage_statement
    (ccm25 : CCM25Interface) (f g : TestFunction)
    {lambda : ℝ} (hlambda : 1 < lambda) :
    WeilFormSymbols.RestrictedPrimeIndexCoverageStatement
      ccm25.weilSymbols lambda
      (ccm25.weilSymbols.convolutionStar f g) :=
  (ccm25.finitePrimeNormalization f g).2.1 lambda hlambda

theorem finite_prime_term_normalization_statement
    (ccm25 : CCM25Interface) (f g : TestFunction) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement
      ccm25.weilSymbols f g :=
  (ccm25.finitePrimeNormalization f g).2.2

theorem finite_prime_visibility_statement
    (ccm25 : CCM25Interface) (f g : TestFunction) :
    WeilFormSymbols.FinitePrimeVisibilityStatement
      ccm25.weilSymbols f g :=
  ccm25.finitePrimeNormalization f g

end FinitePrime
end CCM25Concrete
end Source
end ConnesWeilRH
