/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Bombieri section-7 kernel readback

Certified entry formulas for the finite-certificate lane, read back from
E. Bombieri, "Remarks on Weil's quadratic functional in the theory of prime
numbers, I", section 7 (book page 203 of the on-disk scan; design record
`docs/proofs/1043`, section 6y).  The kernel is the normalized sinc, the
corrected kernel `K*` carries two rank-correction terms, and the master lemma
below splits `K` on an arbitrary `a + b * I` argument into an explicit
real/imaginary pair, reducing every later closed-form identity (the symmetry
law (7.1), the Lemma-10 Gram identity) to real algebra.

No numerical datum enters this leaf: only exact identities are proven.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7Readback

/-- Bombieri's normalized sinc kernel `K(x) = sin x / x` with the removable
value `1` at the origin (book p.203, display above (7.1)). -/
noncomputable def bombieriK (z : Complex) : Complex :=
  if z = 0 then 1 else Complex.sin z / z

/-- The corrected kernel `K*(x, y, t)` of Bombieri section 7, verbatim from
the book p.203 display: the sinc in `t * (x - y)` minus two correction terms
with prefactor `t / sinh t` and coefficients `(1/2 +- i y)`. -/
noncomputable def bombieriKstar (x y t : Real) : Complex :=
  bombieriK (t * (x - y))
    - t / Real.sinh t * ((1 / 2 + (y : Complex) * Complex.I)
        * bombieriK (t * ((Complex.I : Complex) / 2 - (y : Complex)))
        * bombieriK (t * ((Complex.I : Complex) / 2 + (x : Complex))))
    - t / Real.sinh t * ((1 / 2 - (y : Complex) * Complex.I)
        * bombieriK (t * ((Complex.I : Complex) / 2 + (y : Complex)))
        * bombieriK (t * ((Complex.I : Complex) / 2 - (x : Complex))))

/-- The removable value at the origin. -/
theorem bombieriK_zero : bombieriK 0 = 1 := by
  simp [bombieriK]

/-- The normalized sinc has real coefficients: conjugation commutes with
`bombieriK`.  This is the star-compatibility needed when the two correction
terms in `K*` are paired. -/
theorem bombieriK_star (z : Complex) :
    (starRingEnd ℂ) (bombieriK z) =
      bombieriK ((starRingEnd ℂ) z) := by
  unfold bombieriK
  by_cases hz : z = 0
  · simp [hz]
  · have hsz : (starRingEnd ℂ) z ≠ 0 := star_ne_zero.mpr hz
    rw [if_neg hz, if_neg hsz]
    rw [map_div₀, ← Complex.sin_conj]

/-- The normalized sinc is even. -/
theorem bombieriK_neg (z : Complex) : bombieriK (-z) = bombieriK z := by
  unfold bombieriK
  by_cases hz : z = 0
  · simp [hz]
  · have hneg : -z ≠ 0 := neg_ne_zero.mpr hz
    rw [if_neg hneg, if_neg hz, Complex.sin_neg]
    simp

/-- The corrected kernel `K*` is real on real arguments.  Conjugation swaps
the two correction factors; the normalized sinc's evenness and
star-compatibility close the swap exactly. -/
theorem bombieriKstar_star (x y t : Real) :
    (starRingEnd ℂ) (bombieriKstar x y t) = bombieriKstar x y t := by
  unfold bombieriKstar
  simp only [map_sub, map_mul, map_div₀, map_add, map_ofNat,
    bombieriK_star, ← starRingEnd_apply, Complex.conj_ofReal, Complex.conj_I]
  have h1 : (↑t : Complex) * (-Complex.I / 2 - (↑y : Complex)) =
      -((↑t : Complex) * (Complex.I / 2 + (↑y : Complex))) := by ring
  have h2 : (↑t : Complex) * (-Complex.I / 2 + (↑x : Complex)) =
      -((↑t : Complex) * (Complex.I / 2 - (↑x : Complex))) := by ring
  have h3 : (↑t : Complex) * (-Complex.I / 2 + (↑y : Complex)) =
      -((↑t : Complex) * (Complex.I / 2 - (↑y : Complex))) := by ring
  have h4 : (↑t : Complex) * (-Complex.I / 2 - (↑x : Complex)) =
      -((↑t : Complex) * (Complex.I / 2 + (↑x : Complex))) := by ring
  rw [h1, h2, h3, h4, bombieriK_neg, bombieriK_neg,
    bombieriK_neg, bombieriK_neg]
  simp only [map_one]
  ring

/-- Master readback: the kernel on a general `a + b * I` argument is the
explicit real/imaginary pair obtained by multiplying `sin (a + b I)` by the
inverse `(a - b I) / (a^2 + b^2)`.  Every later closed-form identity
for `K*` reduces to real algebra through this lemma. -/
theorem bombieriK_re_add_mulI (a b : Real) (hab : a ≠ 0 ∨ b ≠ 0) :
    bombieriK ((a : Complex) + (b : Real) * Complex.I)
        = Complex.ofReal
            ((Real.sin a * Real.cosh b * a + Real.cos a * Real.sinh b * b)
              / (a * a + b * b))
          + Complex.ofReal
            ((Real.cos a * Real.sinh b * a - Real.sin a * Real.cosh b * b)
              / (a * a + b * b)) * Complex.I := by
  unfold bombieriK
  have hzne : ((a : Complex) + (b : Real) * Complex.I) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp at hre him
    rcases hab with ha | hb
    · exact ha hre
    · exact hb him
  rw [if_neg hzne]
  have hpos : (0 : Real) < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
  have hcos : Complex.cos ((b : Real) * Complex.I)
      = Complex.ofReal (Real.cosh b) := by
    rw [Complex.cos_mul_I, Complex.ofReal_cosh]
  have hsinI : Complex.sin ((b : Real) * Complex.I)
      = Complex.ofReal (Real.sinh b) * Complex.I := by
    rw [Complex.sin_mul_I, Complex.ofReal_sinh]
  have hsin : Complex.sin (((a : Complex) + (b : Real) * Complex.I))
        = (Complex.ofReal (Real.sin a * Real.cosh b)
            + Complex.ofReal (Real.cos a * Real.sinh b) * Complex.I) := by
    rw [Complex.sin_add, hcos, hsinI]
    push_cast
    ring
  rw [hsin, div_eq_iff hzne]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    field_simp [show a ^ 2 + b ^ 2 ≠ 0 from ne_of_gt hpos]
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    field_simp [show a ^ 2 + b ^ 2 ≠ 0 from ne_of_gt hpos]

/-- The kernel value at a real argument, with the removable point excluded. -/
theorem bombieriK_ofReal {a : Real} (ha : a ≠ 0) :
    bombieriK ((a : Complex)) = ((Real.sin a / a : Real) : Complex) := by
  unfold bombieriK
  rw [if_neg (by exact_mod_cast ha)]
  rw [← Complex.ofReal_sin]
  exact (Complex.ofReal_div (Real.sin a) a).symm

/-- The kernel value at a purely imaginary argument `b * I`: the `i` factors
cancel and the value is real. -/
theorem bombieriK_mul_I {b : Real} (hb : b ≠ 0) :
    bombieriK ((b : Real) * Complex.I)
      = ((Real.sinh b / b : Real) : Complex) := by
  unfold bombieriK
  have hzne : (((b : Real) * Complex.I : Complex)) ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp at him
    exact hb him
  rw [if_neg hzne, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [div_eq_iff hzne]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    first
      | done
      | ring_nf; field_simp [hb]
      | field_simp [hb]; ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    first
      | done
      | ring_nf; field_simp [hb]
      | field_simp [hb]; ring

end C1BombieriSection7Readback
end Source
end ConnesWeilRH
