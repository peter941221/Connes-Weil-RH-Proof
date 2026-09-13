/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1SameOwnerWeil

/-!
# C1PsiBlindness - the odd-annihilation bundle for the Weil functional

Record 1406 kill (a) stated, at MODEL level, that every readout of `psi`
pairs `y` with `-y`: the pole pairs `laplaceAt` at `+-(1/2)`, the prime
term reads `F (log n) + F (-log n)`, and the archimedean numerator reads
`F y + F (-y)` and `F 0`. This leaf machine-checks the exact consequence
that made the Chuk sector objection die: **an odd test is invisible to
`psi`** — `poleTerm`, `archimedeanTerm`, `finitePrimeSum`, and hence
`psi`, all vanish on every odd `CompactLogTest`. Combined with the `.re`
readouts (pure-imaginary inputs have zero real part) this covers the
cross-correlation term `F_d = 2 *i* odd(C)` of a sector decomposition:
`psi F_d = 0`.

Scope: this is the annihilation half only. The full 1406 kill (a) for a
concrete owner additionally needs the sector decomposition of
`convolutionSquare` (a future brick). No sign theorem, no positivity
statement, no RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1PsiBlindness

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil

/-- An odd test vanishes at the origin. -/
theorem test_eq_zero_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) : f.test 0 = 0 := by
  have h : f.test 0 = -f.test 0 := by simpa using hodd 0
  have h1 : f.test 0 + f.test 0 = 0 :=
    (congr_arg (fun t => f.test 0 + t) h).trans
      (by abel : f.test 0 + -f.test 0 = 0)
  have h2 : (2 : ℂ) * f.test 0 = 0 := by rwa [two_mul]
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Oddness reflected through the bilateral Laplace transform:
`laplaceAt f (-s) = -laplaceAt f s`. This is the additive-coordinate twin
of `laplaceAt_involution` for the odd sector; the `let`-bound helper is
what makes the negation substitution a first-order rewrite (same shape as
`CC20YoshidaFullProduct.laplaceAt_involution`). -/
theorem laplaceAt_neg_eq_neg_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) (s : ℂ) :
    laplaceAt f (-s) = -laplaceAt f s := by
  unfold laplaceAt
  simp only [exponentialWeight_apply]
  let paired : ℝ → ℂ := fun x => Complex.exp (s * (x : ℂ)) * f.test (-x)
  have hrewrite : (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * f.test x) =
      fun x => paired (-x) := by
    funext x
    dsimp [paired]
    have harg : (s : ℂ) * Complex.ofReal (-x) = (-s) * Complex.ofReal x := by
      push_cast
      ring
    rw [harg, neg_neg]
  rw [hrewrite, integral_neg_eq_self]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  dsimp [paired]
  rw [hodd x]
  simp only [mul_neg]

/-- The pole functional annihilates odd tests. -/
theorem poleTerm_eq_zero_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) : poleTerm f = 0 := by
  have h := laplaceAt_neg_eq_neg_of_odd f hodd ((1 : ℂ) / 2)
  unfold poleTerm
  have hnegarg : ((-1 : ℂ) / 2 : ℂ) = -((1 : ℂ) / 2) := by ring
  rw [show ((-1 : ℂ) / 2 : ℂ) = -((1 : ℂ) / 2) from hnegarg, h]
  simp

/-- The complex prime-power term annihilates odd tests. -/
theorem finitePrimeTermComplex_eq_zero_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) (n : Nat) :
    finitePrimeTermComplex f n = 0 := by
  unfold finitePrimeTermComplex
  rw [hodd (Real.log n)]
  simp

/-- The full finite prime-power sum annihilates odd tests. -/
theorem finitePrimeSum_eq_zero_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) :
    finitePrimeSum f = 0 := by
  unfold finitePrimeSum
  apply Finset.sum_eq_zero
  intro n hn
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_eq_zero_of_odd f hodd n]
  simp

/-- The archimedean numerator of an odd test is pointwise zero. -/
theorem archimedeanNumerator_eq_zero_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) (y : Real) :
    archimedeanNumerator f y = 0 := by
  have h0 := test_eq_zero_of_odd f hodd
  unfold archimedeanNumerator
  rw [hodd y, h0]
  simp

/-- The direct archimedean integrand of an odd test is pointwise zero. -/
theorem archimedeanIntegrand_eq_zero_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) (y : Real) :
    archimedeanIntegrand f y = 0 := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_eq_zero_of_odd f hodd y]
  simp

/-- The archimedean functional annihilates odd tests. -/
theorem archimedeanTerm_eq_zero_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) :
    archimedeanTerm f = 0 := by
  have h0 := test_eq_zero_of_odd f hodd
  have hint : (∫ y in Set.Ioi (0 : Real), archimedeanIntegrand f y) = 0 := by
    have heq : (fun y : Real => archimedeanIntegrand f y) = fun _ => 0 :=
      funext fun y => archimedeanIntegrand_eq_zero_of_odd f hodd y
    rw [heq]
    simp
  unfold archimedeanTerm
  rw [h0, hint]
  simp

/-- **The odd-annihilation bundle**: `psi` is blind to odd tests. This is
the machine-checked core of record 1406 kill (a): the cross-correlation
part of a sector decomposition is imaginary-odd, hence invisible. -/
theorem psi_eq_zero_of_odd (f : CompactLogTest)
    (hodd : ∀ x : Real, f.test (-x) = -f.test x) : psi f = 0 := by
  unfold psi
  rw [poleTerm_eq_zero_of_odd f hodd, archimedeanTerm_eq_zero_of_odd f hodd,
    finitePrimeSum_eq_zero_of_odd f hodd]
  simp

end C1PsiBlindness
end Source
end ConnesWeilRH
