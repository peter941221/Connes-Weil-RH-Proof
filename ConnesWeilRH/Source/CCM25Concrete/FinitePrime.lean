/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic

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

end FinitePrime
end CCM25Concrete
end Source
end ConnesWeilRH
