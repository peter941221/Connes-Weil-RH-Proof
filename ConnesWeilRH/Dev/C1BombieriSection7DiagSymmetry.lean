/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Readback

/-!
# Diagonal slice of Bombieri's symmetry law (7.1)

Specializes the symmetry law (7.1) of Bombieri, section 7 (book p.203,
design record `docs/proofs/1043` section 6y) to the diagonal `x = y = r`,
where the two rank-correction terms collapse onto one another.  This is the
first closed-form identity about the corrected kernel `K*` beyond its
definition.

Content:

* `bombieriK_diagPair` -- the kernel pair `K(-u + vi) * K(u + vi)` collapses
  to the explicit real quantity `(sin^2 u + sinh^2 v) / (u^2 + v^2)`; the
  imaginary parts cancel and the real part collapses against the circular
  and hyperbolic Pythagorean identities.
* `bombieriK_genPair` -- the same product with INDEPENDENT real parts
  `K(-a + vi) * K(b + vi)` as an explicit real/imaginary pair; this is the
  off-diagonal building block for the full symmetry law (7.1).
* `bombieriKstar_diagonalFold` -- on the diagonal the corrected kernel folds
  to `1 - (t / sinh t)` times that kernel pair, because the two correction
  coefficients `(1/2 +- ir)` add up to `1` and the two correction products
  coincide.
* `bombieriKstar_diagonalClosedForm` -- the resulting book identity
  `K*(r,r;t) = 1 - (cosh t - cos(2tr)) / (2 t sinh t (1/4 + r^2))`, the
  row-and-column `(x, y) = (r, r)` specialization of the full law (7.1):

```
(1/4 + x^2) K*(x,y;t) = (1/4 + xy) K(t(x-y))
                        - (cosh t cos(t(x-y)) - cos(t(x+y))) / (2 t sinh t)
```

No numerical datum enters any leaf: only exact identities are proven.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7DiagSymmetry

open ConnesWeilRH.Source.C1BombieriSection7Readback

/-- The kernel pair `K(-u + vi) * K(u + vi)` is the real number
`(sin^2 u + sinh^2 v) / (u^2 + v^2)`: expanding both values through the
master real/imaginary split of the sinc kernel, the imaginary parts cancel
and the real part reduces, via `cos^2 = 1 - sin^2` and
`cosh^2 = sinh^2 + 1`, to the displayed sum of squares. -/
theorem bombieriK_diagPair (u v : Real) (hv : v ≠ 0) :
    bombieriK (((-u : Real) : Complex) + (v : Real) * Complex.I)
      * bombieriK ((u : Complex) + (v : Real) * Complex.I)
      = Complex.ofReal
          ((Real.sin u ^ 2 + Real.sinh v ^ 2) / (u * u + v * v)) := by
  have h1 := bombieriK_re_add_mulI (-u) v (Or.inr hv)
  have h2 := bombieriK_re_add_mulI u v (Or.inr hv)
  -- Normalize the sign-borne trigonometric literals in the `(-u)` instance.
  rw [Real.sin_neg, Real.cos_neg] at h1
  -- Align denominators and numerators with the plain-`u` instance.
  have hd : ((-u) * (-u) + v * v) = (u * u + v * v) := by ring
  have hnm : ((-(Real.sin u) * Real.cosh v * (-u)
                + Real.cos u * Real.sinh v * v))
      = (Real.sin u * Real.cosh v * u + Real.cos u * Real.sinh v * v) := by
    ring
  have hnj : ((Real.cos u * Real.sinh v * (-u)
                - (-Real.sin u) * Real.cosh v * v))
      = (-(Real.cos u * Real.sinh v * u - Real.sin u * Real.cosh v * v)) := by
    ring
  rw [hd, hnm, hnj] at h1
  have hsplit :
      ((-(Real.cos u * Real.sinh v * u - Real.sin u * Real.cosh v * v))
          / (u * u + v * v))
        = (-((Real.cos u * Real.sinh v * u
              - Real.sin u * Real.cosh v * v) / (u * u + v * v))) := by
    ring
  rw [hsplit] at h1
  rw [h1, h2]
  -- Nonvanishing of the shared denominator.
  have hD : u * u + v * v ≠ 0 := by
    have hpos : (0 : Real) < u * u + v * v := by
      nlinarith [sq_pos_of_ne_zero hv, sq_nonneg u]
    exact ne_of_gt hpos
  -- Merge the two fraction pairs into a single real quantity.
  have hmerge : ∀ (P J D : Real), D ≠ 0 →
      (Complex.ofReal (P / D) + Complex.ofReal (-(J / D)) * Complex.I)
        * (Complex.ofReal (P / D) + Complex.ofReal (J / D) * Complex.I)
        = Complex.ofReal ((P * P + J * J) / (D * D)) := by
    intro P J D hD0
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
  rw [hmerge (Real.sin u * Real.cosh v * u + Real.cos u * Real.sinh v * v)
    (Real.cos u * Real.sinh v * u - Real.sin u * Real.cosh v * v)
    (u * u + v * v) hD]
  -- Core polynomial step with the two Pythagorean substitutions.
  have hkey : (Real.sin u * Real.cosh v * u + Real.cos u * Real.sinh v * v)
          * (Real.sin u * Real.cosh v * u + Real.cos u * Real.sinh v * v)
      + (Real.cos u * Real.sinh v * u - Real.sin u * Real.cosh v * v)
          * (Real.cos u * Real.sinh v * u - Real.sin u * Real.cosh v * v)
      = (u * u + v * v) * (Real.sin u ^ 2 + Real.sinh v ^ 2) := by
    ring_nf
    rw [Real.cos_sq', Real.cosh_sq]
    ring
  rw [hkey]
  field_simp [hD]

/-- On the diagonal `x = y = r` the corrected kernel folds: the removable
term contributes `1`, the two correction coefficients `(1/2 +- ir)` add up
to `1`, and the two correction products coincide, leaving `1` minus
`(t / sinh t)` times the diagonal kernel pair. -/
theorem bombieriKstar_diagonalFold (r t : Real) :
    bombieriKstar r r t
      = 1 - t / Real.sinh t *
          (bombieriK (t * ((Complex.I : Complex) / 2 - (r : Complex)))
            * bombieriK (t * ((Complex.I : Complex) / 2 + (r : Complex)))) := by
  unfold bombieriKstar
  simp only [sub_self, mul_zero]
  rw [bombieriK_zero]
  ring

/-- The closed diagonal symmetry law (Bombieri section 7, book p.203,
specialization of (7.1) to `x = y = r`):
`K*(r,r;t) = 1 - (cosh t - cos(2 t r)) / (2 t sinh t (1/4 + r^2))`. -/
theorem bombieriKstar_diagonalClosedForm (r t : Real) (ht : t ≠ 0) :
    bombieriKstar r r t
      = 1 - (Real.cosh t - Real.cos (2 * t * r))
          / (2 * t * Real.sinh t * (1 / 4 + r ^ 2)) := by
  rw [bombieriKstar_diagonalFold]
  -- Route both kernel arguments into the master-split coordinates.
  have hb1 : (t * ((Complex.I : Complex) / 2 - (r : Complex)))
      = (((-(t * r) : Real) : Complex) + (t / 2) * Complex.I) := by
    push_cast
    ring
  have hb2 : (t * ((Complex.I : Complex) / 2 + (r : Complex)))
      = (((t * r : Real) : Complex) + (t / 2) * Complex.I) := by
    push_cast
    ring
  have htv : t / 2 ≠ 0 := by
    intro h0
    apply ht
    have h2 := congrArg (fun q : Real => 2 * q) h0
    simpa using h2
  rw [hb1, hb2]
  -- Align the scalar coercion shapes: `diagPair` instantiates with the
  -- cast of the halved scalar, the fold left a complex division.
  have hcastDiv : ((t / 2 : Real) : Complex) = (↑t / (2 : Complex)) :=
    Complex.ofReal_div t 2
  rw [← hcastDiv, bombieriK_diagPair (t * r) (t / 2) htv]
  -- Scalar reformulation of what remains.
  have hpow : (2 : Real) * (t / 2) = t := by ring
  have hch2pos : (0 : Real) < Real.cosh (t / 2) := Real.cosh_pos (t / 2)
  have hch2 : Real.cosh (t / 2) ≠ 0 := ne_of_gt hch2pos
  have hshEq : Real.sinh t = 2 * Real.sinh (t / 2) * Real.cosh (t / 2) := by
    have h2 := Real.sinh_two_mul (t / 2)
    rw [hpow] at h2
    exact h2
  have hcnSub : Real.cos (2 * t * r) = 1 - 2 * Real.sin (t * r) ^ 2 := by
    have hbr : (2 : Real) * t * r = 2 * (t * r) := by ring
    rw [hbr, Real.cos_two_mul_eq_one_sub]
  have hnum : Real.cosh t - Real.cos (2 * t * r)
      = 2 * (Real.sin (t * r) ^ 2 + Real.sinh (t / 2) ^ 2) := by
    have h2 := Real.cosh_two_mul (t / 2)
    rw [hpow] at h2
    rw [h2, Real.cosh_sq, hcnSub]
    ring
  have hpden : (t * r) * (t * r) + (t / 2) * (t / 2) = t * t * (1 / 4 + r ^ 2) := by
    ring
  have hscal : (t / Real.sinh t)
      * ((Real.sin (t * r) ^ 2 + Real.sinh (t / 2) ^ 2)
        / ((t * r) * (t * r) + (t / 2) * (t / 2)))
      = (Real.cosh t - Real.cos (2 * t * r))
        / (2 * t * Real.sinh t * (1 / 4 + r ^ 2)) := by
    rw [hnum, hpden, hshEq]
    field_simp [ht, hch2]
  have hfin : (t / Real.sinh t) * Complex.ofReal
        ((Real.sin (t * r) ^ 2 + Real.sinh (t / 2) ^ 2)
          / ((t * r) * (t * r) + (t / 2) * (t / 2)))
      = Complex.ofReal ((t / Real.sinh t) *
          ((Real.sin (t * r) ^ 2 + Real.sinh (t / 2) ^ 2)
            / ((t * r) * (t * r) + (t / 2) * (t / 2)))) := by
    push_cast
    ring
  rw [hfin, congrArg Complex.ofReal hscal]
  push_cast
  ring

/-- General kernel pair `K(-a + vi) * K(b + vi)` with INDEPENDENT real
parts, still on the common imaginary offset `v`: the master split turns it
into an explicit real/imaginary pair of rational functions.  This is the
building block behind the off-diagonal correction products of the full law
(7.1); the diagonal slice above is the special case `a = b`. -/
theorem bombieriK_genPair (a b v : Real) (hv : v ≠ 0) :
    bombieriK (((-a : Real) : Complex) + (v : Real) * Complex.I)
        * bombieriK ((b : Complex) + (v : Real) * Complex.I)
      = Complex.ofReal
          (((Real.sin a * Real.cosh v * a + Real.cos a * Real.sinh v * v)
              * (Real.sin b * Real.cosh v * b + Real.cos b * Real.sinh v * v)
            + (Real.cos a * Real.sinh v * a - Real.sin a * Real.cosh v * v)
              * (Real.cos b * Real.sinh v * b - Real.sin b * Real.cosh v * v))
            / ((a * a + v * v) * (b * b + v * v)))
        + Complex.ofReal
          (((Real.sin a * Real.cosh v * a + Real.cos a * Real.sinh v * v)
              * (Real.cos b * Real.sinh v * b - Real.sin b * Real.cosh v * v)
            - (Real.cos a * Real.sinh v * a - Real.sin a * Real.cosh v * v)
              * (Real.sin b * Real.cosh v * b + Real.cos b * Real.sinh v * v))
            / ((a * a + v * v) * (b * b + v * v))) * Complex.I := by
  have h1 := bombieriK_re_add_mulI (-a) v (Or.inr hv)
  have h2 := bombieriK_re_add_mulI b v (Or.inr hv)
  rw [Real.sin_neg, Real.cos_neg] at h1
  -- Normalize the `(-a)` instance onto the shared real vocabulary.
  have hd : ((-a) * (-a) + v * v) = (a * a + v * v) := by ring
  have hnm : ((-(Real.sin a) * Real.cosh v * (-a)
                + Real.cos a * Real.sinh v * v))
      = (Real.sin a * Real.cosh v * a + Real.cos a * Real.sinh v * v) := by
    ring
  have hnj : ((Real.cos a * Real.sinh v * (-a)
                - (-Real.sin a) * Real.cosh v * v))
      = (-(Real.cos a * Real.sinh v * a - Real.sin a * Real.cosh v * v)) := by
    ring
  rw [hd, hnm, hnj] at h1
  have hsplit :
      ((-(Real.cos a * Real.sinh v * a - Real.sin a * Real.cosh v * v))
          / (a * a + v * v))
        = (-((Real.cos a * Real.sinh v * a
              - Real.sin a * Real.cosh v * v) / (a * a + v * v))) := by
    ring
  rw [hsplit] at h1
  rw [h1, h2]
  -- Nonvanishing denominators and the merged fraction identity.
  have hDa : a * a + v * v ≠ 0 := by
    have hpos : (0 : Real) < a * a + v * v := by
      nlinarith [sq_pos_of_ne_zero hv, sq_nonneg a]
    exact ne_of_gt hpos
  have hDb : b * b + v * v ≠ 0 := by
    have hpos : (0 : Real) < b * b + v * v := by
      nlinarith [sq_pos_of_ne_zero hv, sq_nonneg b]
    exact ne_of_gt hpos
  have hmerge : ∀ (Pa Qa Pb Qb Da Db : Real), Da ≠ 0 → Db ≠ 0 →
      (Complex.ofReal (Pa / Da) + Complex.ofReal (-(Qa / Da)) * Complex.I)
          * (Complex.ofReal (Pb / Db) + Complex.ofReal (Qb / Db) * Complex.I)
        = Complex.ofReal ((Pa * Pb + Qa * Qb) / (Da * Db))
          + Complex.ofReal ((Pa * Qb - Qa * Pb) / (Da * Db)) * Complex.I := by
    intro Pa Qa Pb Qb Da Db hDa0 hDb0
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
  rw [hmerge (Real.sin a * Real.cosh v * a + Real.cos a * Real.sinh v * v)
    (Real.cos a * Real.sinh v * a - Real.sin a * Real.cosh v * v)
    (Real.sin b * Real.cosh v * b + Real.cos b * Real.sinh v * v)
    (Real.cos b * Real.sinh v * b - Real.sin b * Real.cosh v * v)
    (a * a + v * v) (b * b + v * v) hDa hDb]

end C1BombieriSection7DiagSymmetry
end Source
end ConnesWeilRH
