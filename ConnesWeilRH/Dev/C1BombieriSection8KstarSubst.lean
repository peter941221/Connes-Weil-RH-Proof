/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Lemma10
import ConnesWeilRH.Dev.C1BombieriSection7DiagSymmetry
import ConnesWeilRH.Dev.C1BombieriSection8ExpMass

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, fifteenth slice: the Lemma-10 substitution pair

Pointwise preparation for the eigen-relation substitution of the
(8.11) readback (Bombieri's Lemma 10, book pp.209-212): the two
entry-level restatements of `2 t K*` that the finite-Γ double sum
consumes.

* Off the diagonal (`x ≠ y`): the Lemma-10 Gram identity with its
  sinc term read back through the window integral —
  `2 sin(t(x−y))/(x−y) = winInt t (y−x)` (the window integral is even
  in the angle) — so `2 t K*(x,y;t)` is `winInt t (y−x)` minus the two
  exponential-bracket correction products, i.e. exactly the split into
  the Q-form channel and the rank-two boundary channels.
* On the diagonal (`x = y = r`): twice `t` times the diagonal closed
  form of (7.1) —
  `2 t K*(r,r;t) = 2 t − (cosh t − cos(2tr)) /
  (sinh t * (1/4 + r^2))` —
  the removable-singularity values that the `winInt` reading cannot
  see.

Both are elementary rearrangements of landed identities; no new
analysis.  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8KstarSubst

open ConnesWeilRH.Source.C1BombieriSection7Readback
open ConnesWeilRH.Source.C1BombieriSection7Lemma10
open ConnesWeilRH.Source.C1BombieriSection7DiagSymmetry
open ConnesWeilRH.Source.C1BombieriSection8ExpMass
open scoped ComplexConjugate

/-- The Lemma-10 Gram identity off the diagonal, with the sinc term read
back through the window integral: for `t ≠ 0`, `x ≠ y`,

```
2 t K*(x,y;t) = winInt t (y−x)
  − [e^{(1/2−iy)t} − e^{−(1/2−iy)t}]/(e^t − e^{−t})
    · [e^{(1/2+ix)t} − e^{−(1/2+ix)t}]/(1/2+ix)
  − [e^{(1/2+iy)t} − e^{−(1/2+iy)t}]/(e^t − e^{−t})
    · [e^{(1/2−ix)t} − e^{−(1/2−ix)t}]/(1/2−ix).
```

The bridge is the real sinc identity
`2 sin(t(x−y))/(x−y) = 2 sin((y−x)t)/(y−x)` (both `sin` and the
denominator flip), i.e. the evenness of the window integral. -/
theorem bombieriKstar_lemma10_winInt (x y t : Real) (ht : t ≠ 0)
    (hxy : x ≠ y) :
    ((2 * t : Real) : Complex) * bombieriKstar x y t
      = winInt t (y - x)
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
  have hne : y - x ≠ 0 := by
    intro h0
    exact hxy (sub_eq_zero.mp h0).symm
  have hreal : (2 * Real.sin (t * (x - y)) / (x - y) : Real)
      = 2 * Real.sin ((y - x) * t) / (y - x) := by
    have hsin : Real.sin (t * (x - y)) = -Real.sin (t * (y - x)) := by
      have h2 : t * (x - y) = -(t * (y - x)) := by ring
      rw [h2, Real.sin_neg]
    have hden : (x - y : Real) = -(y - x) := by ring
    have hcomm : t * (y - x) = (y - x) * t := by ring
    rw [hsin, hden, mul_neg, div_neg, neg_div, neg_neg, hcomm]
  rw [bombieriKstar_lemma10 x y t ht hxy, winInt, if_neg hne, hreal]

/-- Twice `t` times the diagonal closed form of (7.1): for `t ≠ 0`,

```
2 t K*(r,r;t) = 2 t − (cosh t − cos(2tr)) /
  (sinh t * (1/4 + r^2)),
```

the diagonal values that the `winInt` reading cannot see (the window
integral's removable value at `θ = 0` belongs to the mass channel, not
the corrected kernel). -/
theorem bombieriKstar_twoT_diag (r t : Real) (ht : t ≠ 0) :
    ((2 * t : Real) : Complex) * bombieriKstar r r t
      = ((2 * t - (Real.cosh t - Real.cos (2 * t * r))
            / (Real.sinh t * (1 / 4 + r ^ 2)) : Real)
          : Complex) := by
  have hts : Real.sinh t ≠ 0 := by
    intro h0
    have h1 : (Real.exp t - Real.exp (-t)) / 2 = 0 := by
      simpa only [Real.sinh_eq] using h0
    rcases div_eq_zero_iff.mp h1 with h2 | h2
    · have h4 : t = -t := Real.exp_injective (sub_eq_zero.mp h2)
      exact ht (by linarith)
    · norm_num at h2
  have h2t : (2 * t : Real) ≠ 0 := mul_ne_zero (by norm_num) ht
  have hp : (1 / 4 + r ^ 2 : Real) ≠ 0 := ne_of_gt (by positivity)
  have hAB : (2 * t : Real) * (1 - (Real.cosh t - Real.cos (2 * t * r))
        / (2 * t * Real.sinh t * (1 / 4 + r ^ 2)))
      = (2 * t : Real) - (Real.cosh t - Real.cos (2 * t * r))
          / (Real.sinh t * (1 / 4 + r ^ 2)) := by
    field_simp [h2t, hts, hp] <;> ring
  have hfin : ((2 * t : Real) : Complex)
      * (1 - (Real.cosh t - Real.cos (2 * t * r))
          / (2 * t * Real.sinh t * (1 / 4 + r ^ 2)))
      = Complex.ofReal ((2 * t : Real)
          * (1 - (Real.cosh t - Real.cos (2 * t * r))
            / (2 * t * Real.sinh t * (1 / 4 + r ^ 2)))) := by
    push_cast
    ring
  rw [bombieriKstar_diagonalClosedForm r t ht, hfin, hAB]

end C1BombieriSection8KstarSubst
end Source
end ConnesWeilRH
