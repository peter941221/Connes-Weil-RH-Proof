/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1GateMatrixRepresentation
import ConnesWeilRH.Dev.C1ClassGramParity
import ConnesWeilRH.Dev.C1HealthyDetectorArchRescue

/-!
# Record 1215 (D1): exact parity zeros of the class gate matrix

The class bump is even and the first eight Legendre factors have the
standard parity, so the pair correlation `C_ij(x)` of the class family
(the `pairTest` of the packaged windows) satisfies the clean sign law

    C_ij(-x) = (-1)^(i+j) * C_ij(x),

proved by reflecting the convolution integral (`integral_neg_eq_self`)
against the 1127 window parity (`classWindowFun_neg`).  In particular,
for `i + j` odd the pair test is an odd function and vanishes at the
origin, so the archimedean readout (`F(0)` and the even part
`F(y) + F(-y)`) and every prime-power readout (the same even part at
`y = log n`) vanish identically.  By the 1080 odd kill
(`archimedeanTerm_eq_zero_of_test_odd`) and termwise prime killing,

    ICgate (pairTest (classTestFamily a ha) i j) = 0   for i + j odd,

i.e. `gateMatrix (classTestFamily a ha) i j = 0`: 16 of the 32 entries of
the (2,8) gate matrix are EXACT zeros, and the numeric box regeneration
of record 1215 (D5) only has to enclose the 12 same-parity entries.
Record 1216 verified the corresponding numerics: the true gate matrix
reproduces the committed same-parity values to 1.4e-12 while every
mixed-parity entry is <= 5.4e-17 (the committed 1112 single-sided prime
readout had +-0.35 there, which is what fractured the hM slot).

RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1GateMatrixParity

open MeasureTheory
open scoped BigOperators
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1LocalConfigurationDomination
open C1GateMatrixRepresentation
open C1ClassWindowObjects
open C1ClassGramOwner
open C1ClassGramParity
open C1HealthyDetectorArchRescue

noncomputable section

/-! ### The class pair test evaluates to the real correlation -/

/-- The pair test of the class family evaluates to the complex cast of the
real correlation of the window cores. -/
theorem classPairTest_apply (a : ℝ) (ha : 0 < a) (i j : Fin 8) (x : ℝ) :
    (pairTest (classTestFamily a ha) i j).test x =
      ∫ t : ℝ, ((classWindowFun a (i : ℕ) (-t) : ℝ) : ℂ) *
        ((classWindowFun a (j : ℕ) (x - t) : ℝ) : ℂ) := by
  rw [pairTest, CompactLogTest.convolution_apply]
  simp only [classTestFamily, classWindowTest_apply,
    CompactLogTest.involution_apply, Complex.star_def, Complex.conj_ofReal]

/-! ### The parity sign law -/

private theorem sign_of_odd (i j : Fin 8) (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    (((-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ) = -1 := by
  have hreal : (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) = -1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    simp [pow_add]
  rw [hreal]
  simp

/-- The class correlation carries the Legendre parity sign: reflecting the
argument multiplies the value by `(-1)^(i+j)`. -/
theorem classPairTest_neg (a : ℝ) (ha : 0 < a) (i j : Fin 8) (x : ℝ) :
    (pairTest (classTestFamily a ha) i j).test (-x) =
      (((-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ) *
        (pairTest (classTestFamily a ha) i j).test x := by
  have hparity : ∀ t : ℝ, classWindowFun a (i : ℕ) t =
      (-1 : ℝ) ^ (i : ℕ) * classWindowFun a (i : ℕ) (-t) := by
    intro t
    have hinv : (-1 : ℝ) ^ (i : ℕ) * (-1 : ℝ) ^ (i : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, sq, neg_one_mul, neg_neg, one_pow]
    rw [classWindowFun_neg a i t, ← mul_assoc, hinv, one_mul]
  have hparity2 : ∀ t : ℝ, classWindowFun a (j : ℕ) (-x + t) =
      (-1 : ℝ) ^ (j : ℕ) * classWindowFun a (j : ℕ) (x - t) := by
    intro t
    rw [show (-x + t : ℝ) = -(x - t) by ring, classWindowFun_neg a j (x - t)]
  rw [classPairTest_apply, classPairTest_apply]
  have hsubst : (∫ t : ℝ, ((classWindowFun a (i : ℕ) (-t) : ℝ) : ℂ) *
      ((classWindowFun a (j : ℕ) (-x - t) : ℝ) : ℂ)) =
      ∫ t : ℝ, ((classWindowFun a (i : ℕ) t : ℝ) : ℂ) *
        ((classWindowFun a (j : ℕ) (-x + t) : ℝ) : ℂ) := by
    rw [← integral_neg_eq_self (fun t : ℝ =>
      ((classWindowFun a (i : ℕ) (-t) : ℝ) : ℂ) *
        ((classWindowFun a (j : ℕ) (-x - t) : ℝ) : ℂ)) volume]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [neg_neg, sub_neg_eq_add]
  rw [hsubst]
  have hpt : ∀ t : ℝ, ((classWindowFun a (i : ℕ) t : ℝ) : ℂ) *
      ((classWindowFun a (j : ℕ) (-x + t) : ℝ) : ℂ) =
      (((-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ) *
        (((classWindowFun a (i : ℕ) (-t) : ℝ) : ℂ) *
          ((classWindowFun a (j : ℕ) (x - t) : ℝ) : ℂ)) := by
    intro t
    rw [hparity t, hparity2 t, pow_add]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall fun t => hpt t),
    integral_const_mul]

/-- The odd-parity specialization: the pair test is an odd function. -/
theorem classPairTest_neg_of_odd (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) (x : ℝ) :
    (pairTest (classTestFamily a ha) i j).test (-x) =
      -(pairTest (classTestFamily a ha) i j).test x := by
  rw [classPairTest_neg, sign_of_odd i j hodd]
  ring

/-- The preregistered D1 clause: the even part vanishes pointwise. -/
theorem classPairTest_even_add_zero_of_odd (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) (x : ℝ) :
    (pairTest (classTestFamily a ha) i j).test x +
      (pairTest (classTestFamily a ha) i j).test (-x) = 0 := by
  rw [classPairTest_neg_of_odd a ha i j hodd x]
  ring

/-- The preregistered D1 clause: the value at the origin vanishes. -/
theorem classPairTest_at_zero_of_odd (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    (pairTest (classTestFamily a ha) i j).test 0 = 0 := by
  have hodd' := classPairTest_neg_of_odd a ha i j hodd 0
  simp only [neg_zero] at hodd'
  have h3 : -(pairTest (classTestFamily a ha) i j).test 0 +
      (pairTest (classTestFamily a ha) i j).test 0 = 0 := neg_add_cancel _
  rw [← hodd'] at h3
  have h4 : (2 : ℂ) * (pairTest (classTestFamily a ha) i j).test 0 = 0 := by
    rw [two_mul]
    exact h3
  exact ((mul_eq_zero (b := (pairTest (classTestFamily a ha) i j).test 0)).mp
    h4).resolve_left (by norm_num)

/-! ### The functional kills -/

/-- The 1080 odd kill applies verbatim to the mixed-parity class pairs. -/
theorem archimedeanTerm_classPairTest_zero_of_odd (a : ℝ) (ha : 0 < a)
    (i j : Fin 8) (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    archimedeanTerm (pairTest (classTestFamily a ha) i j) = 0 :=
  archimedeanTerm_eq_zero_of_test_odd _
    (classPairTest_neg_of_odd a ha i j hodd)

/-- Every visible prime-power term reads only the even part, which vanishes
on mixed-parity class pairs. -/
theorem finitePrimeSum_classPairTest_zero_of_odd (a : ℝ) (ha : 0 < a)
    (i j : Fin 8) (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    finitePrimeSum (pairTest (classTestFamily a ha) i j) = 0 := by
  have hterm : ∀ n : ℕ, finitePrimeTerm
      (pairTest (classTestFamily a ha) i j) n = 0 := by
    intro n
    have hpair : (pairTest (classTestFamily a ha) i j).test (Real.log n) +
        (pairTest (classTestFamily a ha) i j).test (-Real.log n) = 0 :=
      classPairTest_even_add_zero_of_odd a ha i j hodd _
    have hzero : finitePrimeTermComplex
        (pairTest (classTestFamily a ha) i j) n = 0 := by
      simp only [finitePrimeTermComplex, hpair]
      simp
    simp [finitePrimeTerm, hzero]
  rw [finitePrimeSum]
  exact Finset.sum_eq_zero (fun n _ => hterm n)

/-- D1 headline: the gate functional is identically zero on mixed-parity
class pairs. -/
theorem ICgate_classPairTest_zero_of_odd (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    ICgate (pairTest (classTestFamily a ha) i j) = 0 := by
  rw [ICgate, archimedeanTerm_classPairTest_zero_of_odd a ha i j hodd,
    finitePrimeSum_classPairTest_zero_of_odd a ha i j hodd]
  ring

/-- D5-facing corollary: the mixed-parity gate matrix entries are exact
zeros. -/
theorem gateMatrix_zero_of_odd (a : ℝ) (ha : 0 < a) (i j : Fin 8)
    (hodd : Odd ((i : ℕ) + (j : ℕ))) :
    gateMatrix (classTestFamily a ha) i j = 0 := by
  simpa [gateMatrix] using ICgate_classPairTest_zero_of_odd a ha i j hodd

end
end C1GateMatrixParity
end Source
end ConnesWeilRH
