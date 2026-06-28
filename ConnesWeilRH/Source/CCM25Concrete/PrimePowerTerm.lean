/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport

/-!
# CCM25 pointwise finite-prime term normalization

This module isolates the local finite-prime atom before any finite sum is
formed. The local atom is the source `Lambda(n) * <g|T(n)g>` normalization; the
minus sign belongs to the surrounding `Psi` or `QW_lambda` formula.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerTerm

structure SourcePrimePowerTermAtIndex
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  sourcePrimePowerIndex : Prop
  sourceAtomVisible :
    W.finitePrimeAtomVisible n (W.convolutionStar f g)
  normalized :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g

structure SourcePrimePowerTermNormalization
    (W : WeilFormSymbols) (f g : TestFunction) where
  atIndex : ∀ n : ℕ, SourcePrimePowerTermAtIndex W f g n

theorem finite_prime_term_normalization_of_source_terms
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourcePrimePowerTermNormalization W f g) :
    WeilFormSymbols.FinitePrimeTermNormalizationStatement W f g := by
  intro n
  exact (h.atIndex n).normalized

end PrimePowerTerm
end CCM25Concrete
end Source
end ConnesWeilRH
