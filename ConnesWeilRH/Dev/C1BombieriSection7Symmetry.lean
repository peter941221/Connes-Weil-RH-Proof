/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7DiagSymmetry

/-!
# The full Bombieri symmetry law (7.1)

Off-diagonal slice.  The symmetry law of Bombieri, section 7 (book p.203,
design record `docs/proofs/1043` section 6y):

```
(1/4 + x^2) K*(x,y;t) = (1/4 + xy) K(t(x-y))
                        - (cosh t cos(t(x-y)) - cos(t(x+y))) / (2 t sinh t)
```

Proof route (the real collapse certified out-of-tree at 3.7e-40 worst
deviation over random angles satisfying the three Pythagorean relations,
then mirrored as exact algebra here):

* `wCollapse` -- the cosine pair `cosh t cos(t(x-y)) - cos(t(x+y))` is
  `2` times the atom combination `sin(ty) sin(tx) cosh^2(t/2)
  + cos(ty) cos(tx) sinh^2(t/2)`; this is where the hyperbolic Pythagorean
  identity `cosh^2 = sinh^2 + 1` enters.
* `bombieri7_core` -- the scalar engine: with the two kernel-pair products
  routed through `bombieriK_genPair`, the correction fold is the real
  quantity `(Pa Pb + Qa Qb - 2 y (Pa Qb - Qa Pb)) / (Da Db)`, and the law
  reduces to the displayed scalar identity.
* `bombieriKstar_symmetryLaw` -- the assembly: route the four correction
  kernels through the master split and the two products through
  `bombieriK_genPair`; the `(1/2 +- iy)` coefficients cancel the imaginary
  parts and the scalar engine finishes.
* `bombieriKstar_symmetric` -- the law's punchline corollary
  `(1/4 + x^2) K*(x,y;t) = (1/4 + y^2) K*(y,x;t)` (both sides equal the
  common right-hand side, using that the sinc is odd and the cosine pair
  even under `x <-> y`).

No numerical datum enters any leaf: only exact identities are proven.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7Symmetry

open ConnesWeilRH.Source.C1BombieriSection7Readback
open ConnesWeilRH.Source.C1BombieriSection7DiagSymmetry

private theorem cosXY (t x y : Real) :
    Real.cos (t * (x - y)) = Real.cos (t * x - t * y) :=
  congrArg Real.cos (by ring)

private theorem sinXY (t x y : Real) :
    Real.sin (t * (x - y)) = Real.sin (t * x - t * y) :=
  congrArg Real.sin (by ring)

private theorem cosSum (t x y : Real) :
    Real.cos (t * (x + y)) = Real.cos (t * x + t * y) :=
  congrArg Real.cos (by ring)

/-- The cosine pair of the law (7.1) in atom form. -/
private theorem wCollapse (t x y : Real) :
    Real.cosh t * Real.cos (t * x - t * y) - Real.cos (t * x + t * y)
      = 2 * (Real.sin (t * y) * Real.sin (t * x) * Real.cosh (t / 2) ^ 2
            + Real.cos (t * y) * Real.cos (t * x) * Real.sinh (t / 2) ^ 2) := by
  have hpow : (2 : Real) * (t / 2) = t := by ring
  have h2 := Real.cosh_two_mul (t / 2)
  rw [hpow] at h2
  rw [Real.cos_sub, Real.cos_add, h2]
  ring_nf
  simp only [Real.cosh_sq]
  ring

set_option maxHeartbeats 1000000 in -- field_simp clears four distinct real denominators over the fully expanded atom products
/-- Scalar engine of the law (7.1): with the two correction products
routed through `bombieriK_genPair` and the fold
`(1/2 + iy) AB + (1/2 - iy) CD = (u - 2 y v)` (imaginary parts cancel),
the law reduces to this real identity. -/
theorem bombieri7_core (x y t : Real) (ht : t ≠ 0) (hxy : x ≠ y) :
    (1 / 4 + x ^ 2) * (t / Real.sinh t)
        * ((Real.sin (t * y) * Real.cosh (t / 2) * (t * y)
              + Real.cos (t * y) * Real.sinh (t / 2) * (t / 2))
              * (Real.sin (t * x) * Real.cosh (t / 2) * (t * x)
                + Real.cos (t * x) * Real.sinh (t / 2) * (t / 2))
            + (Real.cos (t * y) * Real.sinh (t / 2) * (t * y)
              - Real.sin (t * y) * Real.cosh (t / 2) * (t / 2))
              * (Real.cos (t * x) * Real.sinh (t / 2) * (t * x)
                - Real.sin (t * x) * Real.cosh (t / 2) * (t / 2))
            - 2 * y
              * ((Real.sin (t * y) * Real.cosh (t / 2) * (t * y)
                    + Real.cos (t * y) * Real.sinh (t / 2) * (t / 2))
                  * (Real.cos (t * x) * Real.sinh (t / 2) * (t * x)
                    - Real.sin (t * x) * Real.cosh (t / 2) * (t / 2))
                - (Real.cos (t * y) * Real.sinh (t / 2) * (t * y)
                  - Real.sin (t * y) * Real.cosh (t / 2) * (t / 2))
                  * (Real.sin (t * x) * Real.cosh (t / 2) * (t * x)
                    + Real.cos (t * x) * Real.sinh (t / 2) * (t / 2))))
      / (((t * y) * (t * y) + (t / 2) * (t / 2))
        * ((t * x) * (t * x) + (t / 2) * (t / 2)))
      = x * (x - y) * Real.sin (t * (x - y)) / (t * (x - y))
        + (Real.cosh t * Real.cos (t * (x - y)) - Real.cos (t * (x + y)))
          / (2 * t * Real.sinh t) := by
  have htv : t / 2 ≠ 0 := by
    intro h0
    apply ht
    have h2 := congrArg (fun q : Real => 2 * q) h0
    simpa using h2
  have hshNe : Real.sinh t ≠ 0 := by
    intro h0
    apply ht
    rw [Real.sinh_eq] at h0
    have h1 : Real.exp t = Real.exp (-t) := by
      have h2 := (div_eq_iff (by norm_num : (2 : Real) ≠ 0)).mp h0
      rw [zero_mul] at h2
      exact sub_eq_zero.mp h2
    have h3 : t = -t := Real.exp_injective h1
    linarith
  have hsxy : t * (x - y) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact ht h
    · exact hxy (sub_eq_zero.mp h)
  have hDa : (t * y) * (t * y) + (t / 2) * (t / 2) ≠ 0 := by
    have hpos : (0 : Real) < (t * y) * (t * y) + (t / 2) * (t / 2) := by
      nlinarith [sq_pos_of_ne_zero htv, sq_nonneg (t * y)]
    exact ne_of_gt hpos
  have hDb : (t * x) * (t * x) + (t / 2) * (t / 2) ≠ 0 := by
    have hpos : (0 : Real) < (t * x) * (t * x) + (t / 2) * (t / 2) := by
      nlinarith [sq_pos_of_ne_zero htv, sq_nonneg (t * x)]
    exact ne_of_gt hpos
  rw [cosXY, cosSum, sinXY, wCollapse, Real.sin_sub]
  -- The two hyperbolic substitutions, stated before the atoms are frozen
  -- so that `set` rewrites them along with the goal: `cosh^2 = sinh^2 + 1`
  -- and the doubling dissolving the bare `sinh t` into the half arguments
  -- (the cleared equation mixes both, and `ring` needs matching atoms).
  have hchsq : Real.cosh (t / 2) ^ 2 = Real.sinh (t / 2) ^ 2 + 1 :=
    Real.cosh_sq (t / 2)
  have hshEq : Real.sinh t = 2 * Real.sinh (t / 2) * Real.cosh (t / 2) := by
    have h2 := Real.sinh_two_mul (t / 2)
    have hpow : (2 : Real) * (t / 2) = t := by ring
    rw [hpow] at h2
    exact h2
  -- Freeze the trigonometric atoms: `field_simp`'s inner simp would
  -- otherwise reorder products (and the halving division) INSIDE the
  -- `Real.sin` / `Real.cos` / `Real.sinh` arguments, splitting each atom
  -- in two and leaving the final `ring` an unsolvable mixed form.
  set sx : Real := Real.sin (t * x) with hsx_def
  set cx : Real := Real.cos (t * x) with hcx_def
  set sy : Real := Real.sin (t * y) with hsy_def
  set cy : Real := Real.cos (t * y) with hcy_def
  set ch : Real := Real.cosh (t / 2) with hch_def
  set sh : Real := Real.sinh (t / 2) with hsh_def
  field_simp [ht, hsxy, hshNe, hDa, hDb]
  ring_nf
  rw [hchsq, hshEq]
  ring

set_option maxRecDepth 8000 in -- field_simp over the unfolded kernel products recurses deeply
set_option maxHeartbeats 1000000 in -- four correction-kernel bridges plus two genPair rewrites exceed the default budget
/-- The full symmetry law (7.1), off-diagonal form: for `t ≠ 0` and
`x ≠ y`,
`(1/4 + x^2) K*(x,y;t) = (1/4 + xy) K(t(x-y))
  - (cosh t cos(t(x-y)) - cos(t(x+y))) / (2 t sinh t)`. -/
theorem bombieriKstar_symmetryLaw (x y t : Real) (ht : t ≠ 0) (hxy : x ≠ y) :
    (1 / 4 + x ^ 2) * bombieriKstar x y t
      = (1 / 4 + x * y) * bombieriK (((t * (x - y) : Real) : Complex))
        - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
              - Real.cos (t * (x + y)))
            / (2 * t * Real.sinh t)) := by
  unfold bombieriKstar
  -- Inside a complex ambient, `binop%` re-elaborates the definition's real
  -- scalars at type `Complex`: `1/4` and `1/2` become complex numeral
  -- divisions `(1:Complex)/(4:Complex)`, `x ^ 2` becomes a complex power of
  -- a cast, `t / Real.sinh t` becomes a cast-level complex division, and the
  -- leading argument `t * (x - y)` becomes `↑t * (↑x - ↑y)`.  The projection
  -- rules (`div_re` etc.) would explode each of those into unmatchable
  -- `Complex.re 1` / `Complex.normSq` fragments, so pull every one back into
  -- a single `Complex.ofReal` block before anything else fires.
  have hsync : ((t : Complex) * ((x : Complex) - (y : Complex)))
      = (((t * (x - y) : Real) : Complex)) := by
    push_cast
    ring
  have h14 : ((1 : Complex) / (4 : Complex))
      = ((1 / 4 : Real) : Complex) := by
    push_cast
    ring
  have h12 : ((1 : Complex) / (2 : Complex))
      = ((1 / 2 : Real) : Complex) := by
    push_cast
    ring
  have htsh : ((t : Complex) / ((Real.sinh t : Real) : Complex))
      = ((t / Real.sinh t : Real) : Complex) :=
    (Complex.ofReal_div t (Real.sinh t)).symm
  rw [h14, h12, htsh, ← Complex.ofReal_pow, hsync]
  have hsxy : t * (x - y) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact ht h
    · exact hxy (sub_eq_zero.mp h)
  have htv : t / 2 ≠ 0 := by
    intro h0
    apply ht
    have h2 := congrArg (fun q : Real => 2 * q) h0
    simpa using h2
  have hshNe : Real.sinh t ≠ 0 := by
    intro h0
    apply ht
    rw [Real.sinh_eq] at h0
    have h1 : Real.exp t = Real.exp (-t) := by
      have h2 := (div_eq_iff (by norm_num : (2 : Real) ≠ 0)).mp h0
      rw [zero_mul] at h2
      exact sub_eq_zero.mp h2
    have h3 : t = -t := Real.exp_injective h1
    linarith
  have hDa : (t * y) * (t * y) + (t / 2) * (t / 2) ≠ 0 := by
    have hpos : (0 : Real) < (t * y) * (t * y) + (t / 2) * (t / 2) := by
      nlinarith [sq_pos_of_ne_zero htv, sq_nonneg (t * y)]
    exact ne_of_gt hpos
  have hDb : (t * x) * (t * x) + (t / 2) * (t / 2) ≠ 0 := by
    have hpos : (0 : Real) < (t * x) * (t * x) + (t / 2) * (t / 2) := by
      nlinarith [sq_pos_of_ne_zero htv, sq_nonneg (t * x)]
    exact ne_of_gt hpos
  rw [bombieriK_ofReal hsxy]
  -- Re-associate first: only then do the kernel pairs stand as contiguous
  -- products that `mul_comm` and `genPair` can grab.
  simp only [mul_assoc]
  -- The second correction product arrives as `K(ty) * K(-tx)`; `genPair`
  -- consumes `K(-tx) * K(ty)`, so commute at the untouched def tokens.
  rw [mul_comm (bombieriK (t * ((Complex.I : Complex) / 2 + (y : Complex))))
               (bombieriK (t * ((Complex.I : Complex) / 2 - (x : Complex))))]
  -- Bridge the four correction arguments into master-split coordinates.
  have hb1 : (t * ((Complex.I : Complex) / 2 - (y : Complex)))
      = (((-(t * y) : Real) : Complex) + (t / 2) * Complex.I) := by
    push_cast
    ring
  have hb2 : (t * ((Complex.I : Complex) / 2 + (x : Complex)))
      = (((t * x : Real) : Complex) + (t / 2) * Complex.I) := by
    push_cast
    ring
  have hb3 : (t * ((Complex.I : Complex) / 2 + (y : Complex)))
      = (((t * y : Real) : Complex) + (t / 2) * Complex.I) := by
    push_cast
    ring
  have hb4 : (t * ((Complex.I : Complex) / 2 - (x : Complex)))
      = (((-(t * x) : Real) : Complex) + (t / 2) * Complex.I) := by
    push_cast
    ring
  have hcastDiv : ((t / 2 : Real) : Complex) = (↑t / (2 : Complex)) :=
    Complex.ofReal_div t 2
  rw [hb1, hb2, hb3, hb4, ← hcastDiv]
  -- Both correction products through the general kernel pair.
  rw [bombieriK_genPair (t * y) (t * x) (t / 2) htv,
      bombieriK_genPair (t * x) (t * y) (t / 2) htv]
  -- The cosine pair and the sine difference become atom polynomials.
  rw [cosXY, cosSum, wCollapse, sinXY, Real.sin_sub]
  -- The two hyperbolic substitutions (see `bombieri7_core`), stated before
  -- the atoms are frozen so that `set` rewrites them along with the goal.
  have hchsq : Real.cosh (t / 2) ^ 2 = Real.sinh (t / 2) ^ 2 + 1 :=
    Real.cosh_sq (t / 2)
  have hshEq : Real.sinh t = 2 * Real.sinh (t / 2) * Real.cosh (t / 2) := by
    have h2 := Real.sinh_two_mul (t / 2)
    have hpow : (2 : Real) * (t / 2) = t := by ring
    rw [hpow] at h2
    exact h2
  -- Freeze the trigonometric atoms (see `bombieri7_core`).
  set sx : Real := Real.sin (t * x) with hsx_def
  set cx : Real := Real.cos (t * x) with hcx_def
  set sy : Real := Real.sin (t * y) with hsy_def
  set cy : Real := Real.cos (t * y) with hcy_def
  set ch : Real := Real.cosh (t / 2) with hch_def
  set sh : Real := Real.sinh (t / 2) with hsh_def
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
    field_simp [ht, hsxy, hshNe, hDa, hDb]
    ring_nf
    rw [hchsq, hshEq]
    ring
  · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf

/-- The symmetry law's punchline: `(1/4 + x^2) K*(x,y;t) =
(1/4 + y^2) K*(y,x;t)` -- both sides equal the common right-hand side of
(7.1), using that the sinc is odd and the cosine pair even under
`x <-> y`. -/
theorem bombieriKstar_symmetric (x y t : Real) (ht : t ≠ 0) (hxy : x ≠ y) :
    (1 / 4 + x ^ 2) * bombieriKstar x y t
      = (1 / 4 + y ^ 2) * bombieriKstar y x t := by
  rw [bombieriKstar_symmetryLaw x y t ht hxy,
      bombieriKstar_symmetryLaw y x t ht (Ne.symm hxy)]
  have hsxy : t * (x - y) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact ht h
    · exact hxy (sub_eq_zero.mp h)
  have hsxy' : t * (y - x) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact ht h
    · exact (Ne.symm hxy) (sub_eq_zero.mp h)
  have hneg : t * (y - x) = -(t * (x - y)) := by ring
  have hplus : t * (y + x) = t * (x + y) := by ring
  have hk : bombieriK (((t * (y - x) : Real) : Complex))
      = bombieriK (((t * (x - y) : Real) : Complex)) := by
    rw [bombieriK_ofReal hsxy', bombieriK_ofReal hsxy, hneg, Real.sin_neg]
    have hr : (-Real.sin (t * (x - y))) / (-(t * (x - y)))
        = Real.sin (t * (x - y)) / (t * (x - y)) := by
      field_simp [hsxy]
    exact congrArg Complex.ofReal hr
  have hc : Real.cos (t * (y - x)) = Real.cos (t * (x - y)) := by
    rw [hneg, Real.cos_neg]
  have hp : Real.cos (t * (y + x)) = Real.cos (t * (x + y)) := by
    rw [hplus]
  rw [hk, hc, hp]
  ring

end C1BombieriSection7Symmetry
end Source
end ConnesWeilRH
