/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Symmetry

/-!
# The Lemma-10 Gram identity for the corrected kernel

The closed-form display inside the proof of Bombieri's Lemma 10 (book
p.210, design record `docs/proofs/1043` section 6y): for `t ≠ 0` and
`x ≠ y` the corrected kernel satisfies

```
2 t K*(x,y;t) = 2 sin(t(x-y))/(x-y)
   - [e^{(1/2-iy)t} - e^{-(1/2-iy)t}]/(e^t - e^{-t})
     * [e^{(1/2+ix)t} - e^{-(1/2+ix)t}]/(1/2+ix)
   - [e^{(1/2+iy)t} - e^{-(1/2+iy)t}]/(e^t - e^{-t})
     * [e^{(1/2-ix)t} - e^{-(1/2-ix)t}]/(1/2-ix)
```

Every entry is elementary (`sinc`, complex exponentials); no digamma.
The mathematical mechanism: each of the four correction-kernel arguments
is a quarter-turn rotation `t(i/2 -+ y) = I * ((1/2 +- i y) t)`, so
`K (I u) = sinh u / u` (`sin (I u) = sinh u * I` cancels the `I` in the
denominator); the `(1/2 +- i y)` coefficients then cancel the shared
factor of the matching `u`, every `t` disappears, and the definition of
`K*` turns into the display verbatim via `e^w - e^{-w} = 2 sinh w`.

Proof mechanics (mirroring the symmetry-law leaf): right after
`unfold bombieriKstar` a normalization block pulls the `binop%` artifacts
back into single `Complex.ofReal` blocks; the `I / 2` inside each kernel
argument is normalized to `((1/2 : Real) : Complex) * Complex.I` BEFORE
the rotation bridges, so those bridges are division-free and close by
`Complex.ext` projections plus `ring`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection7Lemma10

open ConnesWeilRH.Source.C1BombieriSection7Readback

/-- The kernel value on a quarter-turn argument: `K (I * u) = sinh u / u`
for `u ≠ 0` -- `sin (I u) = sinh u * I` cancels the `I` of the
denominator. -/
theorem bombieriK_I_mul (u : Complex) (hu : u ≠ 0) :
    bombieriK (Complex.I * u) = Complex.sinh u / u := by
  unfold bombieriK
  rw [if_neg (mul_ne_zero Complex.I_ne_zero hu), mul_comm Complex.I u,
    Complex.sin_mul_I]
  field_simp [hu]

/-- The exponential bracket of the Lemma-10 display in reverse: it is
twice the hyperbolic sine (the defining equation of `Complex.sinh`). -/
theorem expBracket (w : Complex) :
    Complex.exp w - Complex.exp (-w) = 2 * Complex.sinh w := by
  have hd : Complex.sinh w = (Complex.exp w - Complex.exp (-w)) / 2 := rfl
  rw [hd]
  ring

/-- The defining equation of `Complex.sinh`, forward. -/
theorem sinhBracket (w : Complex) :
    Complex.sinh w = (Complex.exp w - Complex.exp (-w)) / 2 := rfl

set_option maxHeartbeats 1000000 in -- the closing field_simp clears nine distinct complex denominators
/-- The Lemma-10 Gram identity (book p.210): with `t ≠ 0` and `x ≠ y`,
`2 t K*(x,y;t)` equals the displayed elementary expression in complex
exponentials. -/
theorem bombieriKstar_lemma10 (x y t : Real) (ht : t ≠ 0) (hxy : x ≠ y) :
    ((2 * t : Real) : Complex) * bombieriKstar x y t
      = ((2 * Real.sin (t * (x - y)) / (x - y) : Real) : Complex)
        - (Complex.exp ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I)
              * ((t : Real) : Complex))
            - Complex.exp (-((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I)
              * ((t : Real) : Complex))))
          / (Complex.exp (((t : Real) : Complex))
              - Complex.exp (-(((t : Real) : Complex))))
          * ((Complex.exp ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I)
                * ((t : Real) : Complex))
              - Complex.exp (-((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I)
                * ((t : Real) : Complex))))
            / (((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I))
        - (Complex.exp ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I)
              * ((t : Real) : Complex))
            - Complex.exp (-((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I)
              * ((t : Real) : Complex))))
          / (Complex.exp (((t : Real) : Complex))
              - Complex.exp (-(((t : Real) : Complex))))
          * ((Complex.exp ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I)
                * ((t : Real) : Complex))
              - Complex.exp (-((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I)
                * ((t : Real) : Complex))))
            / (((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I)) := by
  -- Nonvanishing facts.
  have hsxy : t * (x - y) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact ht h
    · exact hxy (sub_eq_zero.mp h)
  have htsC : (((t : Real) : Complex)) ≠ 0 := by
    intro h0
    exact ht (by have h2 := congrArg Complex.re h0; simp at h2; exact h2)
  have hc1 : ((1 / 2 : Real) : Complex) ≠ 0 := by
    intro h0
    exact (by norm_num : (1 / 2 : Real) ≠ 0) (by
      have h2 := congrArg Complex.re h0
      simp at h2)
  have hcoefNe : ∀ c : Real,
      (((1 / 2 : Real) : Complex) + (c : Complex) * Complex.I ≠ 0)
        ∧ (((1 / 2 : Real) : Complex) - (c : Complex) * Complex.I ≠ 0) := by
    intro c
    constructor
    · intro h0
      exact hc1 (by have h2 := congrArg Complex.re h0; simp at h2)
    · intro h0
      exact hc1 (by have h2 := congrArg Complex.re h0; simp at h2)
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
  have hsinhCt : Complex.sinh (((t : Real) : Complex)) ≠ 0 := by
    intro h0
    rw [← Complex.ofReal_sinh] at h0
    exact hshNe (by have h2 := congrArg Complex.re h0; simp at h2; exact h2)
  have hexpT : Complex.exp (((t : Real) : Complex))
        - Complex.exp (-(((t : Real) : Complex))) ≠ 0 := by
    rw [expBracket ((t : Real) : Complex)]
    exact mul_ne_zero (by norm_num) hsinhCt
  -- The four rotated arguments, each nonzero.
  have huA : ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I)
        * ((t : Real) : Complex)) ≠ 0 :=
    mul_ne_zero (hcoefNe y).2 htsC
  have huB : ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I)
        * ((t : Real) : Complex)) ≠ 0 :=
    mul_ne_zero (hcoefNe x).1 htsC
  have huC : ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I)
        * ((t : Real) : Complex)) ≠ 0 :=
    mul_ne_zero (hcoefNe y).1 htsC
  have huD : ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I)
        * ((t : Real) : Complex)) ≠ 0 :=
    mul_ne_zero (hcoefNe x).2 htsC
  -- Normalization haves for the `binop%` artifacts of the definition.
  have hsync : ((t : Complex) * ((x : Complex) - (y : Complex)))
      = (((t * (x - y) : Real) : Complex)) := by
    push_cast
    ring
  have h12 : ((1 : Complex) / (2 : Complex))
      = ((1 / 2 : Real) : Complex) := by
    push_cast
    ring
  have hI2 : (Complex.I / (2 : Complex))
      = ((1 / 2 : Real) : Complex) * Complex.I := by
    rw [div_eq_iff (by norm_num : (2 : Complex) ≠ 0)]
    push_cast
    ring
  have htsh : ((t : Complex) / ((Real.sinh t : Real) : Complex))
      = ((t / Real.sinh t : Real) : Complex) :=
    (Complex.ofReal_div t (Real.sinh t)).symm
  -- Split the doubled cast, absorb the prefactor, and expose the halves.
  have h2t : ((2 * t : Real) : Complex)
      = (2 : Complex) * ((t : Real) : Complex) := by
    push_cast
    ring
  have hpre : ((t / Real.sinh t : Real) : Complex)
      = 2 * ((t : Real) : Complex)
        / (Complex.exp (((t : Real) : Complex))
          - Complex.exp (-(((t : Real) : Complex)))) := by
    rw [expBracket ((t : Real) : Complex)]
    have h1 : ((t / Real.sinh t : Real) : Complex)
        = ((t : Real) : Complex) / ((Real.sinh t : Real) : Complex) := by
      push_cast
      ring
    rw [h1, Complex.ofReal_sinh]
    field_simp [htsC]
  -- The four quarter-turn bridges (division-free after `hI2`).
  have hbC : (((t : Real) : Complex)
          * (((1 / 2 : Real) : Complex) * Complex.I - (y : Complex)))
      = Complex.I * ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I)
          * ((t : Real) : Complex)) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  have hbD : (((t : Real) : Complex)
          * (((1 / 2 : Real) : Complex) * Complex.I + (x : Complex)))
      = Complex.I * ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I)
          * ((t : Real) : Complex)) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  have hbA : (((t : Real) : Complex)
          * (((1 / 2 : Real) : Complex) * Complex.I + (y : Complex)))
      = Complex.I * ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I)
          * ((t : Real) : Complex)) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  have hbB : (((t : Real) : Complex)
          * (((1 / 2 : Real) : Complex) * Complex.I - (x : Complex)))
      = Complex.I * ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I)
          * ((t : Real) : Complex)) := by
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  -- Bookkeeping helpers for the closing pass.
  have hxP : ((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I ≠ 0 :=
    (hcoefNe x).1
  have hxM : ((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I ≠ 0 :=
    (hcoefNe x).2
  unfold bombieriKstar
  rw [h12, htsh, mul_sub, mul_sub, h2t, hsync, bombieriK_ofReal hsxy]
  have hfirst : (2 : Complex) * ((t : Real) : Complex)
        * ((Real.sin (t * (x - y)) / (t * (x - y)) : Real) : Complex)
      = ((2 * Real.sin (t * (x - y)) / (x - y) : Real) : Complex) := by
    push_cast
    field_simp [htsC]
  -- Each correction term equals its Lemma-10 bracket term.  `ring` treats
  -- `x ^ (-1)` as an atom, so the `u`-denominators can never cancel the
  -- coefficient denominator of the display; `field_simp` first clears the
  -- four denominators with the nonvanishing facts, then the residue is a
  -- polynomial identity in the exponentials and the sinc, closed by
  -- `ring`.
  -- Each correction term equals its Lemma-10 bracket term.  `ring` treats
  -- `x ^ (-1)` as an atom, so the `u`-denominators can never cancel the
  -- coefficient denominator of the display; `field_simp` first clears the
  -- four denominators with the nonvanishing facts, then the residue is a
  -- polynomial identity in the exponentials and the sinc, closed by
  -- `ring`.
  have hcorr2 : (2 : Complex) * ((t : Real) : Complex)
        * (2 * ((t : Real) : Complex) / (Complex.exp ((t : Real) : Complex) - Complex.exp (-((t : Real) : Complex)))
          * ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I)
            * (Complex.sinh ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I) * ((t : Real) : Complex)) / ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I) * ((t : Real) : Complex)))
            * (Complex.sinh ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I) * ((t : Real) : Complex)) / ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I) * ((t : Real) : Complex)))))
      = (Complex.exp ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I) * ((t : Real) : Complex)) - Complex.exp (-((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I) * ((t : Real) : Complex)))) / (Complex.exp ((t : Real) : Complex) - Complex.exp (-((t : Real) : Complex)))
        * ((Complex.exp ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I) * ((t : Real) : Complex)) - Complex.exp (-((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I) * ((t : Real) : Complex))))
          / (((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I)) := by
    rw [sinhBracket ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I) * ((t : Real) : Complex)), sinhBracket ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I) * ((t : Real) : Complex))]
    -- Freeze every denominator as an opaque atom BEFORE any normalization:
    -- `field_simp`'s inner `ring_nf` would otherwise distribute the products
    -- inside the inverse arguments (leaving unsimplified `Complex.I ^ 2`),
    -- and the factored nonvanishing facts would no longer match.
    set u1 : Complex := ((((1 / 2 : Real) : Complex) + (y : Complex) * Complex.I) * ((t : Real) : Complex)) with hu1def
    set u2 : Complex := ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I) * ((t : Real) : Complex)) with hu2def
    set eT : Complex := (Complex.exp ((t : Real) : Complex) - Complex.exp (-((t : Real) : Complex))) with heTdef
    set cD : Complex := ((((1 / 2 : Real) : Complex) - (x : Complex) * Complex.I)) with hcDdef
    have hu1 : u1 ≠ 0 := by rw [hu1def]; exact huC
    have hu2 : u2 ≠ 0 := by rw [hu2def]; exact huD
    have heT : eT ≠ 0 := by rw [heTdef]; exact hexpT
    have hcD : cD ≠ 0 := by rw [hcDdef]; exact hxM
    field_simp [hu1, hu2, heT, hcD]
    -- Denominators are gone; unfold the two frozen `u`-atoms (the coefficient
    -- and window factors already match on both sides) and finish polynomially.
    rw [hu1def, hu2def]
    ring
  have hcorr3 : (2 : Complex) * ((t : Real) : Complex)
        * (2 * ((t : Real) : Complex) / (Complex.exp ((t : Real) : Complex) - Complex.exp (-((t : Real) : Complex)))
          * ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I)
            * (Complex.sinh ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I) * ((t : Real) : Complex)) / ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I) * ((t : Real) : Complex)))
            * (Complex.sinh ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I) * ((t : Real) : Complex)) / ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I) * ((t : Real) : Complex)))))
      = (Complex.exp ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I) * ((t : Real) : Complex)) - Complex.exp (-((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I) * ((t : Real) : Complex)))) / (Complex.exp ((t : Real) : Complex) - Complex.exp (-((t : Real) : Complex)))
        * ((Complex.exp ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I) * ((t : Real) : Complex)) - Complex.exp (-((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I) * ((t : Real) : Complex))))
          / (((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I)) := by
    rw [sinhBracket ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I) * ((t : Real) : Complex)), sinhBracket ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I) * ((t : Real) : Complex))]
    -- Freeze every denominator as an opaque atom BEFORE any normalization:
    -- `field_simp`'s inner `ring_nf` would otherwise distribute the products
    -- inside the inverse arguments (leaving unsimplified `Complex.I ^ 2`),
    -- and the factored nonvanishing facts would no longer match.
    set u1 : Complex := ((((1 / 2 : Real) : Complex) - (y : Complex) * Complex.I) * ((t : Real) : Complex)) with hu1def
    set u2 : Complex := ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I) * ((t : Real) : Complex)) with hu2def
    set eT : Complex := (Complex.exp ((t : Real) : Complex) - Complex.exp (-((t : Real) : Complex))) with heTdef
    set cD : Complex := ((((1 / 2 : Real) : Complex) + (x : Complex) * Complex.I)) with hcDdef
    have hu1 : u1 ≠ 0 := by rw [hu1def]; exact huA
    have hu2 : u2 ≠ 0 := by rw [hu2def]; exact huB
    have heT : eT ≠ 0 := by rw [heTdef]; exact hexpT
    have hcD : cD ≠ 0 := by rw [hcDdef]; exact hxP
    field_simp [hu1, hu2, heT, hcD]
    -- Denominators are gone; unfold the two frozen `u`-atoms (the coefficient
    -- and window factors already match on both sides) and finish polynomially.
    rw [hu1def, hu2def]
    ring
  rw [hfirst, hI2, hbC, hbA, hbD, hbB, bombieriK_I_mul _ huC, bombieriK_I_mul _ huD,
    bombieriK_I_mul _ huA, bombieriK_I_mul _ huB, hpre, hcorr2, hcorr3]
  ring

end C1BombieriSection7Lemma10
end Source
end ConnesWeilRH
