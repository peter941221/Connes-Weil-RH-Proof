/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8KstarSubst
import ConnesWeilRH.Dev.C1BombieriSection7Symmetry

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain, sixteenth slice: weighted kernel entries

The finite-Gamma assembly of Bombieri's (8.11) needs the matrix entry
after the `(1/4 + x^2)` weight on its first coordinate has been absorbed.
This leaf gives that entry in the two channels used downstream:

```
(1/4 + x^2) 2t K*(x,y;t)
  = (1/4 + xy) winInt(t, y-x)
    - [cosh(t) cos(t(x-y)) - cos(t(x+y))] / sinh(t).
```

The first term is the Q-form channel and the second is the endpoint
correction.  The proof splits only on `x = y`: the off-diagonal branch
uses the landed (7.1) symmetry law and the diagonal branch uses the
removable-value closed form.  Thus repeated ordinates are retained rather
than excluded.  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8KernelWeights

open ConnesWeilRH.Source.C1BombieriSection7Readback
open ConnesWeilRH.Source.C1BombieriSection7Symmetry
open ConnesWeilRH.Source.C1BombieriSection8ExpMass
open ConnesWeilRH.Source.C1BombieriSection8KstarSubst

/-- The finite-window integral coefficient is even in its frequency. -/
theorem winInt_neg (t theta : Real) :
    winInt t (-theta) = winInt t theta := by
  by_cases htheta : theta = 0
  · subst theta
    simp [winInt]
  · have hneg : -theta ≠ 0 := neg_ne_zero.mpr htheta
    simp only [winInt, if_neg hneg, if_neg htheta]
    congr 1
    rw [neg_mul, Real.sin_neg]
    field_simp

/-- The weighted real-sinc entry is the unified window coefficient away from
the diagonal. -/
private theorem twoT_bombieriK_eq_winInt (x y t : Real) (ht : t ≠ 0)
    (hxy : x ≠ y) :
    ((2 * t : Real) : Complex)
        * bombieriK (((t * (x - y) : Real) : Complex))
      = winInt t (y - x) := by
  have harg : t * (x - y) ≠ 0 :=
    mul_ne_zero ht (sub_ne_zero.mpr hxy)
  have hfreq : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  rw [bombieriK_ofReal harg, winInt, if_neg hfreq, ← Complex.ofReal_mul]
  congr 1
  have hflip : (y - x) * t = -(t * (x - y)) := by ring
  rw [hflip, Real.sin_neg]
  field_simp [ht, sub_ne_zero.mpr hxy, hfreq]
  ring

/-- Scaling the `(7.1)` correction by `2t` clears its `2t` denominator. -/
private theorem twoT_correction (x y t : Real) (ht : t ≠ 0) :
    ((2 * t : Real) : Complex)
        * Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
            - Real.cos (t * (x + y))) / (2 * t * Real.sinh t))
      = Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
            - Real.cos (t * (x + y))) / Real.sinh t) := by
  have hsinh : Real.sinh t ≠ 0 := by
    intro hzero
    have hquot : (Real.exp t - Real.exp (-t)) / 2 = 0 := by
      simpa only [Real.sinh_eq] using hzero
    rcases div_eq_zero_iff.mp hquot with hsub | htwo
    · exact ht (by
        have hsame : t = -t := Real.exp_injective (sub_eq_zero.mp hsub)
        linarith)
    · norm_num at htwo
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp [ht, hsinh]

/-- The weighted `K*` entry in the Q-form plus endpoint-correction shape.
The statement is uniform in `x,y`, including the repeated-ordinate diagonal. -/
theorem weighted_twoT_bombieriKstar (x y t : Real) (ht : 0 < t) :
    ((1 / 4 + x ^ 2 : Real) : Complex)
        * (((2 * t : Real) : Complex) * bombieriKstar x y t)
      = Complex.ofReal (1 / 4 + x * y) * winInt t (y - x)
        - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
            - Real.cos (t * (x + y))) / Real.sinh t) := by
  have htnz : t ≠ 0 := ne_of_gt ht
  by_cases hxy : x = y
  · subst y
    have hweight : (1 / 4 + x ^ 2 : Real) ≠ 0 := ne_of_gt (by positivity)
    have hsinh : Real.sinh t ≠ 0 := by
      intro hzero
      have hquot : (Real.exp t - Real.exp (-t)) / 2 = 0 := by
        simpa only [Real.sinh_eq] using hzero
      rcases div_eq_zero_iff.mp hquot with hsub | htwo
      · exact htnz (by
          have hsame : t = -t := Real.exp_injective (sub_eq_zero.mp hsub)
          linarith)
      · norm_num at htwo
    rw [bombieriKstar_twoT_diag x t htnz]
    unfold winInt
    rw [if_pos (sub_self x)]
    have hcos : Real.cos (t * (x + x)) = Real.cos (2 * t * x) := by
      congr 1
      ring
    rw [show t * (x - x) = 0 by ring, Real.cos_zero, hcos]
    have hreal : (1 / 4 + x ^ 2 : Real)
        * (2 * t - (Real.cosh t - Real.cos (2 * t * x))
            / (Real.sinh t * (1 / 4 + x ^ 2)))
        = (1 / 4 + x * x : Real) * (2 * t)
          - (Real.cosh t * 1 - Real.cos (2 * t * x)) / Real.sinh t := by
      field_simp [hweight, hsinh]
    rw [← Complex.ofReal_mul]
    have htwo : (2 : Complex) * (t : Complex) = ((2 * t : Real) : Complex) := by
      push_cast
      ring
    rw [htwo, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
    exact congrArg Complex.ofReal hreal
  · have hkernel := bombieriKstar_symmetryLaw x y t htnz hxy
    have hkernel' : ((1 / 4 + x ^ 2 : Real) : Complex) * bombieriKstar x y t
        = Complex.ofReal (1 / 4 + x * y)
            * bombieriK (((t * (x - y) : Real) : Complex))
          - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
                - Real.cos (t * (x + y))) / (2 * t * Real.sinh t)) := by
      calc
        ((1 / 4 + x ^ 2 : Real) : Complex) * bombieriKstar x y t
            = ((1 / 4 : Complex) + (x : Complex) ^ 2) * bombieriKstar x y t := by
                push_cast
                ring
        _ = ((1 / 4 : Complex) + (x : Complex) * (y : Complex))
              * bombieriK (((t * (x - y) : Real) : Complex))
            - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
                  - Real.cos (t * (x + y))) / (2 * t * Real.sinh t)) := hkernel
        _ = Complex.ofReal (1 / 4 + x * y)
              * bombieriK (((t * (x - y) : Real) : Complex))
            - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
                  - Real.cos (t * (x + y))) / (2 * t * Real.sinh t)) := by
                push_cast
                ring
    calc
      ((1 / 4 + x ^ 2 : Real) : Complex)
          * (((2 * t : Real) : Complex) * bombieriKstar x y t)
          = ((2 * t : Real) : Complex)
              * (((1 / 4 + x ^ 2 : Real) : Complex) * bombieriKstar x y t) := by
            ring
      _ = ((2 * t : Real) : Complex)
            * (Complex.ofReal (1 / 4 + x * y)
                * bombieriK (((t * (x - y) : Real) : Complex))
              - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
                    - Real.cos (t * (x + y)))
                  / (2 * t * Real.sinh t))) := by
            rw [hkernel']
      _ = Complex.ofReal (1 / 4 + x * y)
            * (((2 * t : Real) : Complex)
              * bombieriK (((t * (x - y) : Real) : Complex)))
          - ((2 * t : Real) : Complex)
              * Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
                    - Real.cos (t * (x + y)))
                  / (2 * t * Real.sinh t)) := by
            ring
      _ = Complex.ofReal (1 / 4 + x * y) * winInt t (y - x)
          - Complex.ofReal ((Real.cosh t * Real.cos (t * (x - y))
                - Real.cos (t * (x + y))) / Real.sinh t) := by
            rw [twoT_bombieriK_eq_winInt x y t htnz hxy,
              twoT_correction x y t htnz]

end C1BombieriSection8KernelWeights
end Source
end ConnesWeilRH
