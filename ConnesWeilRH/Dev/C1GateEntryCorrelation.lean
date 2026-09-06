/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1GateMatrixParity

/-!
# Record 1219 E1: the gate entry as a correlation-readout obligation

Formula brick of the entrywise envelope campaign (prereg
1219_entrywise_envelope_preregistration.md).  Pure structure, no
numerics: it pins the entrywise containment target

`MLo_q28M i j <= gateMatrix (classTestFamily 2 htwo) i j <= MHi_q28M i j`

to the gate functional decomposition (archimedean term + finite visible
prime sum) of the pair test, whose readout is the REAL correlation of
the class window cores (landed as `classPairTest_apply`), and bounds
the visible prime-power indices by the support.  Bricks E2-E5
(certified correlation envelopes, archimedean quadrature, log readouts,
exact assembly) discharge the reduced obligation.

RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1GateEntryCorrelation

open Set
open MeasureTheory
open scoped BigOperators
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1LocalConfigurationDomination
open C1GateMatrixRepresentation
open C1ClassWindowObjects
open C1ClassGramOwner
open C1GateMatrixParity

/-- The gate entry IS the gate functional of the pair test. -/
theorem gate_entry_eq (a : ℝ) (ha : 0 < a) (i j : Fin 8) :
    gateMatrix (classTestFamily a ha) i j =
      ICgate (pairTest (classTestFamily a ha) i j) := rfl

/-- The gate functional splits into the archimedean term and the finite
visible prime sum. -/
theorem ICgate_eq (F : CompactLogTest) :
    ICgate F = archimedeanTerm F + finitePrimeSum F := rfl

/-- The class pair test is supported in `(-2a, 2a)`. -/
theorem classPairTest_support (a : ℝ) (ha : 0 < a) (i j : Fin 8) :
    Function.support (pairTest (classTestFamily a ha) i j).test
      ⊆ Set.Ioo (-(2 * a)) (2 * a) :=
  pairTest_support (classTestFamily a ha)
    (fun i => classTestFamily_support a ha i) i j

/-- A visible prime power of the class pair test satisfies
`|log n| < 2a`: a nonzero prime term forces the even part of the pair
test to be nonzero at `log n`, so `log n` (or its negation) meets the
support. -/
theorem visiblePrime_abs_log_lt (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    {n : ℕ}
    (hn : n ∈ globalPrimeIndexSet (pairTest (classTestFamily a ha) i j)) :
    |Real.log n| < 2 * a := by
  obtain ⟨_, hterm⟩ := mem_globalPrimeIndexSet_iff _ n |>.mp hn
  have htest : (pairTest (classTestFamily a ha) i j).test (Real.log n)
      + (pairTest (classTestFamily a ha) i j).test (-Real.log n) ≠ 0 := by
    intro hzero
    exact hterm (by
      simp only [finitePrimeTermComplex, hzero]
      simp)
  have hsup : (pairTest (classTestFamily a ha) i j).test (Real.log n) ≠ 0 ∨
      (pairTest (classTestFamily a ha) i j).test (-Real.log n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [hcon.1, hcon.2, add_zero] at htest
    exact htest rfl
  rcases hsup with h | h
  · have hmem := classPairTest_support a ha i j
      (Function.mem_support.mpr h)
    rw [mem_Ioo] at hmem
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  · have hmem := classPairTest_support a ha i j
      (Function.mem_support.mpr h)
    rw [mem_Ioo] at hmem
    rw [abs_lt]
    constructor
    · linarith
    · linarith

end C1GateEntryCorrelation
end Source
end ConnesWeilRH
