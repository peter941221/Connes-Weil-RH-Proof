/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8WirtingerSlice5
import ConnesWeilRH.Dev.C1BombieriSection8ParitySplit

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Wirtinger chain (8.13), ninth slice: the full inequality

The (8.14) assembly of Bombieri's Lemma 10 (book pp.209-212): the
parity split `qSplit` of slice 8 plus the even/odd Wirtinger pair of
slices 5 and 7 give, for every C¹ function `Z` with `t > 0`,

```
Q(Z) = ↑( (e^t − e^{−t})/φ₊(t)² · |Z⁺(t)|²
        + (e^t − e^{−t})/φ₋(t)² · |Z⁻(t)|² + S ),   S ≥ 0,
```

where `Z⁺ = (Z + Z∘neg)/2` and `Z⁻ = (Z − Z∘neg)/2` are evaluated at
`t`.  Since the weights are `tanh(t/2)` and `coth(t/2)` (slices 5 and
7), this is the book's (8.13) in the real-channel shape forced by the
orderless `ℂ`:

```
Q(Z) ≥ tanh(t/2)·|Z⁺(t)|² + coth(t/2)·|Z⁻(t)|².
```

The key step is that the split parts carry their TRUE derivatives:
`d/du Z⁺ = (Zp − Zp∘neg)/2` and `d/du Z⁻ = (Zp + Zp∘neg)/2`, which is
exactly the derivative-correct pairing that `qSplit` supplies.  The
chain rule through the reflection is `HasDerivAt.scomp` (the outer
function is ℂ-valued, so plain `comp` does not apply); the inner
derivative of the reflection is `(-1 : ℝ)` in smul form, bridged to
`-(Zp (-u))` by `neg_one_smul`.  DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8WirtingerFull

open ConnesWeilRH.Source.C1BombieriSection8Wirtinger
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice3
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice4
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice5
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice6
open ConnesWeilRH.Source.C1BombieriSection8WirtingerSlice7
open ConnesWeilRH.Source.C1BombieriSection8ParitySplit
open MeasureTheory

/-- The chain rule through the reflection: `d/du Z(-u) = -(Zp (-u))`.
The outer function is ℂ-valued, so the applicable chain rule is
`HasDerivAt.scomp`, whose derivative is the smul `(-1 : ℝ) • Zp (-u)`;
`neg_one_smul` bridges it to the displayed negation. -/
theorem hasDerivAt_neg_reflect {Z Zp : Real → Complex}
    (hZ : ∀ x, HasDerivAt Z (Zp x) x) (u : Real) :
    HasDerivAt (fun y : Real => Z (-y)) (-(Zp (-u))) u := by
  have h : HasDerivAt (fun y : Real => Z (-y)) ((-1 : Real) • Zp (-u)) u :=
    (hZ (-u)).scomp u ((hasDerivAt_id u).neg)
  rw [neg_one_smul] at h
  exact h

/-- The even part `Z⁺ = (Z + Z∘neg)/2` has derivative
`(Zp − Zp∘neg)/2` — its TRUE derivative, the pairing `qSplit` supplies. -/
theorem hasDerivAt_part_even {Z Zp : Real → Complex}
    (hZ : ∀ x, HasDerivAt Z (Zp x) x) (u : Real) :
    HasDerivAt (fun y : Real => (Z y + Z (-y)) / 2) ((Zp u - Zp (-u)) / 2) u := by
  have h : HasDerivAt (fun y : Real => (Z y + Z (-y)) / 2)
      ((Zp u + -(Zp (-u))) / 2) u :=
    ((hZ u).add (hasDerivAt_neg_reflect hZ u)).div_const (2 : Complex)
  exact h.congr_deriv (by ring)

/-- The odd part `Z⁻ = (Z − Z∘neg)/2` has derivative
`(Zp + Zp∘neg)/2` — its TRUE derivative, the pairing `qSplit` supplies. -/
theorem hasDerivAt_part_odd {Z Zp : Real → Complex}
    (hZ : ∀ x, HasDerivAt Z (Zp x) x) (u : Real) :
    HasDerivAt (fun y : Real => (Z y - Z (-y)) / 2) ((Zp u + Zp (-u)) / 2) u := by
  have h : HasDerivAt (fun y : Real => (Z y - Z (-y)) / 2)
      ((Zp u - -(Zp (-u))) / 2) u :=
    ((hZ u).sub (hasDerivAt_neg_reflect hZ u)).div_const (2 : Complex)
  exact h.congr_deriv (by ring)

/-- The even part is even. -/
theorem part_even_even {Z : Real → Complex} (u : Real) :
    (fun y : Real => (Z y + Z (-y)) / 2) (-u)
      = (fun y : Real => (Z y + Z (-y)) / 2) u := by
  simp only []
  rw [neg_neg]
  ring

/-- The odd part is odd. -/
theorem part_odd_odd {Z : Real → Complex} (u : Real) :
    (fun y : Real => (Z y - Z (-y)) / 2) (-u)
      = -((fun y : Real => (Z y - Z (-y)) / 2) u) := by
  simp only []
  rw [neg_neg]
  ring

/-- FLAGSHIP (slice 9): the full Wirtinger-type inequality (8.13).
For every C¹ `Z` with `t > 0`, the quadratic form splits over the
even/odd decomposition and each half is bounded by its boundary value
through the Wirtinger pair:

```
Q(Z) = ↑( (e^t − e^{−t})/φ₊(t)² · |Z⁺(t)|²
        + (e^t − e^{−t})/φ₋(t)² · |Z⁻(t)|² + S ),   S ≥ 0.
```

The weights are `tanh(t/2)` and `coth(t/2)` (see
`wirtingerFull_weights`).  DETECTOR only. -/
theorem wirtingerFull (t : Real) (ht : 0 < t) (Z Zp : Real → Complex)
    (hZ : ∀ x, HasDerivAt Z (Zp x) x) (hZc : Continuous Zp) :
    ∃ S : Real, 0 ≤ S ∧ (∫ x in -t..t, qIntegrand Z Zp x)
      = Complex.ofReal ((Real.exp t - Real.exp (-t))
            / (phiEven t * phiEven t) * Complex.normSq ((Z t + Z (-t)) / 2)
          + (Real.exp t - Real.exp (-t))
            / (phiOdd t * phiOdd t) * Complex.normSq ((Z t - Z (-t)) / 2)
          + S) := by
  have hZcont : Continuous Z :=
    continuous_iff_continuousAt.mpr fun x => (hZ x).continuousAt
  have hDpc : Continuous fun u : Real => (Zp u - Zp (-u)) / 2 :=
    (hZc.sub (hZc.comp continuous_neg)).div_const 2
  have hSpc : Continuous fun u : Real => (Zp u + Zp (-u)) / 2 :=
    (hZc.add (hZc.comp continuous_neg)).div_const 2
  obtain ⟨S1, hS1, hQ1⟩ := wirtingerEven t (le_of_lt ht)
    (fun u => (Z u + Z (-u)) / 2) (fun u => (Zp u - Zp (-u)) / 2)
    (fun u => hasDerivAt_part_even hZ u) hDpc (fun u => part_even_even u)
  obtain ⟨S2, hS2, hQ2⟩ := wirtingerOdd t ht
    (fun u => (Z u - Z (-u)) / 2) (fun u => (Zp u + Zp (-u)) / 2)
    (fun u => hasDerivAt_part_odd hZ u) hSpc (fun u => part_odd_odd u)
  rw [qSplit t (le_of_lt ht) Z Zp hZcont hZc, hQ1, hQ2]
  refine ⟨S1 + S2, add_nonneg hS1 hS2, ?_⟩
  rw [← Complex.ofReal_add]
  ring

/-- The book's (8.13) with the weights identified: `tanh(t/2)` for the
even part and `coth(t/2)` (stated through `cosh`/`sinh` — Mathlib has
no `coth`) for the odd part. -/
theorem wirtingerFull_weights (t : Real) (ht : 0 < t) (Z Zp : Real → Complex)
    (hZ : ∀ x, HasDerivAt Z (Zp x) x) (hZc : Continuous Zp) :
    ∃ S : Real, 0 ≤ S ∧ (∫ x in -t..t, qIntegrand Z Zp x)
      = Complex.ofReal (Real.tanh (t / 2) * Complex.normSq ((Z t + Z (-t)) / 2)
          + (Real.cosh (t / 2) / Real.sinh (t / 2))
            * Complex.normSq ((Z t - Z (-t)) / 2)
          + S) := by
  obtain ⟨S, hS, hQ⟩ := wirtingerFull t ht Z Zp hZ hZc
  refine ⟨S, hS, ?_⟩
  rw [hQ]
  simp only [phiEven, phiOdd, ← pow_two]
  rw [tanhHalf_eq_ratio, coshHalf_div_sinhHalf_eq_ratio t ht]

end C1BombieriSection8WirtingerFull
end Source
end ConnesWeilRH
