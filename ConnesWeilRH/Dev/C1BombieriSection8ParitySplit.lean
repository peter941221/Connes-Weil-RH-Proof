/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8WirtingerSlice7

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), eighth slice: the even/odd parity split

First brick of the (8.14) assembly: the quadratic form splits over the
even/odd decomposition `Z ± = (Z ± Z∘neg)/2` — exactly the recombination
the book performs between (8.11) and (8.13):

```
Q(Z) = Q(Z⁺) + Q(Z⁻)
```

stated at the `qIntegrand` integral level over the symmetric window
`[-t, t]` (values only — no differentiability enters).  The engine is
the halving identity `∫_{−t}^{t} f = ∫_0^t (f x + f (−x))` plus the
parallelogram law `normSq(a+b) + normSq(a−b) = 2(normSq a + normSq b)`
(with `Complex.normSq_add`/`normSq_sub`, whose `±2·Re(z·conj w)` cross
terms cancel pairwise).  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8ParitySplit

open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice3
open MeasureTheory

/-- Halving identity: the symmetric-window integral is the half-line
integral of the reflected sum of the integrand. -/
theorem integral_symmetry_half (t : Real) (ht : 0 ≤ t) (f : Real → Complex)
    (hfc : Continuous f) :
    ∫ x in -t..t, f x = ∫ x in 0..t, (f x + f (-x)) := by
  have hA : IntervalIntegrable f volume (-t) 0 := Continuous.intervalIntegrable hfc (-t) 0
  have hB : IntervalIntegrable f volume 0 t := Continuous.intervalIntegrable hfc 0 t
  have hB' : IntervalIntegrable (fun x : Real => f (-x)) volume 0 t :=
    Continuous.intervalIntegrable (hfc.comp continuous_neg) 0 t
  rw [intervalIntegral.integral_add hB hB',
    intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := t),
    neg_zero,
    ← intervalIntegral.integral_add_adjacent_intervals hA hB]
  ring

/-- The Q-form integrand is continuous in the pair. -/
private theorem continuous_qIntegrand (f fp : Real → Complex) (hf : Continuous f)
    (hfp : Continuous fp) : Continuous fun x : Real => qIntegrand f fp x := by
  have hstar : Continuous fun x : Real => (starRingEnd ℂ) (f x) := continuous_star.comp hf
  have hstar' : Continuous fun x : Real => (starRingEnd ℂ) (fp x) := continuous_star.comp hfp
  unfold qIntegrand
  exact (continuous_const.mul (hf.mul hstar)).add (hfp.mul hstar')

/-- Norm of a half: `normSq(z/2) = normSq z / 4` (the `2` is an OfNat
node, so `normSq_ofReal` cannot fire; the numeral is evaluated through
the re/im expansion instead). -/
private theorem normSq_half (z : ℂ) :
    Complex.normSq (z / 2) = Complex.normSq z / 4 := by
  have h4 : Complex.normSq (2 : ℂ) = 4 := by
    simp
    norm_num
  rw [Complex.normSq_div, h4]

/-- FLAGSHIP (slice 8): the even/odd parity split of the quadratic form.
`Q(Z) = Q(Z⁺) + Q(Z⁻)` over the symmetric window, with
`Z⁺ = (Z + Z∘neg)/2` and `Z⁻ = (Z − Z∘neg)/2` — the book's
decomposition between (8.11) and (8.13).  Values only: no
differentiability enters. -/
theorem qSplit (t : Real) (ht : 0 ≤ t) (Z Zp : Real → Complex)
    (hZ : Continuous Z) (hZp : Continuous Zp) :
    (∫ x in -t..t, qIntegrand Z Zp x)
      = (∫ x in -t..t, qIntegrand (fun u => (Z u + Z (-u)) / 2)
          (fun u => (Zp u + Zp (-u)) / 2) x)
        + (∫ x in -t..t, qIntegrand (fun u => (Z u - Z (-u)) / 2)
          (fun u => (Zp u - Zp (-u)) / 2) x) := by
  have hZneg : Continuous fun u : Real => Z (-u) := hZ.comp continuous_neg
  have hZpneg : Continuous fun u : Real => Zp (-u) := hZp.comp continuous_neg
  have hE : Continuous fun u : Real => (Z u + Z (-u)) / 2 :=
    (hZ.add hZneg).div_const 2
  have hE' : Continuous fun u : Real => (Zp u + Zp (-u)) / 2 :=
    (hZp.add hZpneg).div_const 2
  have hO : Continuous fun u : Real => (Z u - Z (-u)) / 2 :=
    (hZ.sub hZneg).div_const 2
  have hO' : Continuous fun u : Real => (Zp u - Zp (-u)) / 2 :=
    (hZp.sub hZpneg).div_const 2
  rw [integral_symmetry_half t ht (fun x : Real => qIntegrand Z Zp x)
      (continuous_qIntegrand Z Zp hZ hZp),
    integral_symmetry_half t ht
      (fun x : Real => qIntegrand (fun u => (Z u + Z (-u)) / 2)
        (fun u => (Zp u + Zp (-u)) / 2) x) (continuous_qIntegrand _ _ hE hE'),
    integral_symmetry_half t ht
      (fun x : Real => qIntegrand (fun u => (Z u - Z (-u)) / 2)
        (fun u => (Zp u - Zp (-u)) / 2) x) (continuous_qIntegrand _ _ hO hO')]
  have hiE : IntervalIntegrable (fun x : Real => qIntegrand
        (fun u => (Z u + Z (-u)) / 2) (fun u => (Zp u + Zp (-u)) / 2) x
      + qIntegrand (fun u => (Z u + Z (-u)) / 2)
        (fun u => (Zp u + Zp (-u)) / 2) (-x)) volume 0 t :=
    Continuous.intervalIntegrable
      ((continuous_qIntegrand _ _ hE hE').add
        ((continuous_qIntegrand _ _ hE hE').comp continuous_neg)) 0 t
  have hiO : IntervalIntegrable (fun x : Real => qIntegrand
        (fun u => (Z u - Z (-u)) / 2) (fun u => (Zp u - Zp (-u)) / 2) x
      + qIntegrand (fun u => (Z u - Z (-u)) / 2)
        (fun u => (Zp u - Zp (-u)) / 2) (-x)) volume 0 t :=
    Continuous.intervalIntegrable
      ((continuous_qIntegrand _ _ hO hO').add
        ((continuous_qIntegrand _ _ hO hO').comp continuous_neg)) 0 t
  have hpt : (fun x : Real => qIntegrand Z Zp x + qIntegrand Z Zp (-x))
      = (fun x : Real => qIntegrand (fun u => (Z u + Z (-u)) / 2)
            (fun u => (Zp u + Zp (-u)) / 2) x
          + qIntegrand (fun u => (Z u + Z (-u)) / 2)
            (fun u => (Zp u + Zp (-u)) / 2) (-x)
          + (qIntegrand (fun u => (Z u - Z (-u)) / 2)
            (fun u => (Zp u - Zp (-u)) / 2) x
          + qIntegrand (fun u => (Z u - Z (-u)) / 2)
            (fun u => (Zp u - Zp (-u)) / 2) (-x))) := by
    funext x
    unfold qIntegrand
    simp only []
    rw [neg_neg]
    rw [Complex.mul_conj (Z x), Complex.mul_conj (Z (-x)),
      Complex.mul_conj (Zp x), Complex.mul_conj (Zp (-x)),
      Complex.mul_conj ((Z x + Z (-x)) / 2),
      Complex.mul_conj ((Z (-x) + Z x) / 2),
      Complex.mul_conj ((Z x - Z (-x)) / 2),
      Complex.mul_conj ((Z (-x) - Z x) / 2),
      Complex.mul_conj ((Zp x + Zp (-x)) / 2),
      Complex.mul_conj ((Zp (-x) + Zp x) / 2),
      Complex.mul_conj ((Zp x - Zp (-x)) / 2),
      Complex.mul_conj ((Zp (-x) - Zp x) / 2),
      normSq_half, normSq_half, normSq_half, normSq_half,
      normSq_half, normSq_half, normSq_half, normSq_half,
      Complex.normSq_add, Complex.normSq_add,
      Complex.normSq_sub, Complex.normSq_sub,
      Complex.normSq_add, Complex.normSq_add,
      Complex.normSq_sub, Complex.normSq_sub]
    push_cast
    ring
  rw [hpt, ← intervalIntegral.integral_add hiE hiO]

end C1BombieriSection8ParitySplit
end Source
end ConnesWeilRH
