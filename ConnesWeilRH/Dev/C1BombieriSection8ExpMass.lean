/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection8ExpSum

import Mathlib.Analysis.Complex.Exponential

/-!
# The Wirtinger chain, eleventh slice: the (8.5) exponential sum

The reduction object of Bombieri's Lemma 10 (book pp.209-212): the
exponential sum

```
Z(u) = Σ_γ e^{−iγu} · z_γ                                     (8.5)
```

with its term-by-term derivative and the term-by-term mass expansion of
the window integral of its squared norm:

```
∫_{−t}^{t} |Z(u)|² du = Σ_i Σ_j (z_i · conj z_j) · winInt t (γ_j − γ_i),
```

where `winInt` unifies the diagonal value `2t` (`γ_j = γ_i`) with the
off-diagonal sinc value `2 sin(t(γ_j − γ_i))/(γ_j − γ_i)` — the exact
integral readback of the Lemma-10 Gram identity's sinc kernel, the
engine of the (8.10) → (8.11) step.

Conventions: `conj` is the `ComplexConjugate`-scope notation for the
bundled `starRingEnd ℂ` hom (so `map_sum`/`map_mul` apply verbatim and
every v4.30 conjugation lemma — `mul_conj`, `conj_I`, `conj_ofReal`,
`exp_conj` — rewrites syntactically); the exponentials stay in the
canonical single-cast form (`cast INSIDE, I OUTSIDE`) so the window
integrals of slice 10 apply verbatim; and the term derivative goes
through the Euler split of slice 10 (`exp_mul_I` + the real `sin`/`cos`
chain rules), so no generic `hasDerivAt_exp` is ever needed.
DETECTOR only.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8ExpMass

open ConnesWeilRH.Source.C1BombieriSection8Wirtinger
open ConnesWeilRH.Source.C1BombieriSection8ExpSum
open scoped ComplexConjugate
open MeasureTheory

variable {n : Nat}

/-- `conj` distributes over products (the bundled `starRingEnd ℂ` hom
is multiplicative). -/
theorem conj_mul_d (a b : Complex) :
    conj (a * b) = conj a * conj b :=
  map_mul (starRingEnd Complex) a b

/-- The conjugated base exponential: `conj (e^{−iγu}) = e^{iγu}` —
`exp_conj`, then `conj_ofReal` and `conj_I` normalize the argument. -/
theorem conj_expTerm (γ u : Real) :
    conj (Complex.exp (Complex.ofReal ((-γ) * u) * Complex.I))
      = Complex.exp (Complex.ofReal (γ * u) * Complex.I) := by
  have hneg : (-γ) * u = -(γ * u) := by ring
  have harg : Complex.ofReal ((-γ) * u) * -Complex.I
      = Complex.ofReal (γ * u) * Complex.I := by
    rw [mul_neg, hneg, Complex.ofReal_neg]
    ring
  rw [← Complex.exp_conj, conj_mul_d, Complex.conj_ofReal, Complex.conj_I, harg]

/-- The conjugated full term: `conj (e^{−iγu} z) = e^{iγu} · conj z`. -/
theorem conj_term_mul (γ : Real) (z : Complex) (u : Real) :
    conj (Complex.exp (Complex.ofReal ((-γ) * u) * Complex.I) * z)
      = Complex.exp (Complex.ofReal (γ * u) * Complex.I) * conj z := by
  rw [conj_mul_d, conj_expTerm]

/-- The two window-exponentials add in single-cast form:
`−iγ_i x + iγ_j x = i(γ_j − γ_i)x`. -/
theorem castSumExpI (γi γj x : Real) :
    Complex.ofReal ((-γi) * x) * Complex.I + Complex.ofReal (γj * x) * Complex.I
      = Complex.ofReal ((γj - γi) * x) * Complex.I := by
  have h1 : (-γi) * x + γj * x = (γj - γi) * x := by ring
  calc Complex.ofReal ((-γi) * x) * Complex.I + Complex.ofReal (γj * x) * Complex.I
      = (Complex.ofReal ((-γi) * x) + Complex.ofReal (γj * x)) * Complex.I :=
        by rw [add_mul]
    _ = Complex.ofReal ((-γi) * x + γj * x) * Complex.I := by
        rw [← Complex.ofReal_add]
    _ = Complex.ofReal ((γj - γi) * x) * Complex.I := by rw [h1]

/-- The per-pair product of the mass expansion:
`e^{−iγ_i x} z_i · conj(e^{−iγ_j x} z_j) = e^{i(γ_j−γ_i)x} · (z_i conj z_j)`,
all in the canonical single-cast form. -/
theorem expPair_mul (γi γj : Real) (zi zj : Complex) (x : Real) :
    (Complex.exp (Complex.ofReal ((-γi) * x) * Complex.I) * zi)
      * conj (Complex.exp (Complex.ofReal ((-γj) * x) * Complex.I) * zj)
      = Complex.exp (Complex.ofReal ((γj - γi) * x) * Complex.I)
          * (zi * conj zj) := by
  rw [conj_term_mul, mul_mul_mul_comm, ← Complex.exp_add, castSumExpI γi γj x]

/-- The (8.5) exponential sum `Z(u) = Σ_γ e^{−iγu} z_γ`, in the canonical
single-cast form that matches the window integrals of slice 10. -/
noncomputable def expSum (γ : Fin n → Real) (z : Fin n → Complex) (u : Real) : Complex :=
  ∑ i, Complex.exp (Complex.ofReal ((-(γ i)) * u) * Complex.I) * z i

/-- The per-pair Gram integrand `y ↦ (z_i conj z_j) e^{i(γ_j−γ_i)y}`,
summed over `j` and named, so the sum-integral exchanges of the
flagship match syntactically (no higher-order rewrite patterns). -/
noncomputable def gramPair (γ : Fin n → Real) (z : Fin n → Complex)
    (i : Fin n) (y : Real) : Complex :=
  ∑ j, (z i * conj (z j)) * Complex.exp (Complex.ofReal ((γ j - γ i) * y) * Complex.I)

/-- The base-exponential derivative
`d/du e^{iθu} = (iθ) · e^{iθu}`, through the Euler split of slice 10
(`exp_mul_I` + the real `sin`/`cos` chain rules) — no generic
`hasDerivAt_exp` is needed, and the derivative is stated as a plain
complex product `(iθ) · e^{iθu}`. -/
theorem hasDerivAt_expTerm (θ u : Real) :
    HasDerivAt (fun y : Real => Complex.exp (Complex.ofReal (θ * y) * Complex.I))
      ((Complex.ofReal θ * Complex.I) * Complex.exp (Complex.ofReal (θ * u) * Complex.I)) u := by
  have hfun : (fun y : Real => Complex.exp (Complex.ofReal (θ * y) * Complex.I))
      = fun y : Real => Complex.ofReal (Real.cos (θ * y))
          + Complex.I * Complex.ofReal (Real.sin (θ * y)) := by
    funext y
    exact exp_i_mul_real θ y
  have hcos : HasDerivAt (fun y : Real => Complex.ofReal (Real.cos (θ * y)))
      (Complex.ofReal (-(θ * Real.sin (θ * u)))) u :=
    hasDerivAt_cast (hasDerivAt_cos_mul_real θ u)
  have hsin : HasDerivAt (fun y : Real => Complex.I * Complex.ofReal (Real.sin (θ * y)))
      (Complex.I * Complex.ofReal (θ * Real.cos (θ * u))) u :=
    (hasDerivAt_cast (hasDerivAt_sin_mul_real θ u)).const_mul Complex.I
  rw [hfun]
  refine (hcos.add hsin).congr_deriv ?_
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hexpand : (Complex.ofReal θ * Complex.I)
      * (Complex.ofReal (Real.cos (θ * u)) + Complex.ofReal (Real.sin (θ * u)) * Complex.I)
    = Complex.ofReal θ * Complex.I * Complex.ofReal (Real.cos (θ * u))
      + Complex.ofReal θ * (Complex.I * Complex.I)
        * Complex.ofReal (Real.sin (θ * u)) := by
    ring
  rw [hexpand, Complex.I_mul_I, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_mul]
  ring

/-- The term-by-term derivative of the (8.5) sum: each exponential
differentiates to `(−iγ_i) · e^{−iγ_i u}`, so the coefficient vector
becomes `w i = (−iγ_i) · z i` — the coordinate change behind the
eigenvalue equation (7.4). -/
theorem hasDerivAt_expSum (γ : Fin n → Real) (z : Fin n → Complex) (u : Real) :
    HasDerivAt (expSum γ z)
      (expSum γ (fun i => (Complex.ofReal (-(γ i)) * Complex.I) * z i) u) u := by
  have h := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_expTerm (-(γ i)) u).mul_const (z i)
  have hfun : (∑ i : Fin n, fun y : Real =>
        Complex.exp (Complex.ofReal ((-(γ i)) * y) * Complex.I) * z i)
      = expSum γ z := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [hfun] at h
  refine h.congr_deriv ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The unified window integral: the diagonal value `2t` (`θ = 0`) and
the off-diagonal sinc value `2 sin(θt)/θ` (`θ ≠ 0`), one case-split
consuming both slice-10 window integrals. -/
noncomputable def winInt (t θ : Real) : Complex :=
  if θ = 0 then (2 * t : ℂ) else Complex.ofReal (2 * Real.sin (θ * t) / θ)

/-- The window integral of the pure exponential equals `winInt t θ` in
both the diagonal and the off-diagonal case. -/
theorem integral_winInt (t θ : Real) (ht : 0 ≤ t) :
    ∫ x in -t..t, Complex.exp (Complex.ofReal (θ * x) * Complex.I) = winInt t θ := by
  by_cases hθ : θ = 0
  · subst hθ
    rw [winInt, if_pos rfl]
    have hz : (fun x : Real => Complex.exp (Complex.ofReal ((0:Real) * x) * Complex.I))
        = fun x : Real =>
          Complex.exp ((Complex.ofReal (0:Real) * Complex.ofReal x) * Complex.I) := by
      funext x
      rw [Complex.ofReal_mul]
    rw [hz, integral_exp_i_window_zero t ht]
  · rw [winInt, if_neg hθ]
    exact integral_exp_i_window t θ ht hθ

/-- FLAGSHIP (slice 11): the term-by-term mass expansion of the (8.5)
exponential sum — the window integral of `|Z|²` (in its `mul_conj`
product form, which keeps the integrand ℂ-valued) over the Gram pairs:

```
∫_{−t}^{t} (Z · conj Z)(u) du = Σ_i Σ_j (z_i · conj z_j) · winInt t (γ_j − γ_i),
```

the diagonal pairs contributing `2t` and the off-diagonal pairs the
sinc value `2 sin(t(γ_j−γ_i))/(γ_j−γ_i)` — the integral readback of the
Lemma-10 Gram identity's kernel, with the finite sum exchanged through
the interval integral (`integral_finsetSum`, no Fubini anywhere).
DETECTOR only. -/
theorem expSum_mass_integral (t : Real) (ht : 0 ≤ t)
    (γ : Fin n → Real) (z : Fin n → Complex) :
    ∫ x in -t..t, (expSum γ z x * conj (expSum γ z x))
      = ∑ i, ∑ j, (z i * conj (z j)) * winInt t (γ j - γ i) := by
  have hpt : ∀ x : Real, expSum γ z x * conj (expSum γ z x)
      = ∑ i, gramPair γ z i x := by
    intro x
    unfold gramPair
    simp only [expSum, map_sum]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [expPair_mul (γ i) (γ j) (z i) (z j) x]
    rw [mul_comm (Complex.exp (Complex.ofReal ((γ j - γ i) * x) * Complex.I))
      (z i * conj (z j))]
  have hpiece : ∀ (i j : Fin n), IntervalIntegrable
      (fun x : Real => (z i * conj (z j))
        * Complex.exp (Complex.ofReal ((γ j - γ i) * x) * Complex.I)) volume (-t) t :=
    fun i j => Continuous.intervalIntegrable
      (continuous_const.mul (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_expTerm (γ j - γ i) x).continuousAt)) (-t) t
  have hint : ∀ i : Fin n, IntervalIntegrable (gramPair γ z i) volume (-t) t := by
    intro i
    unfold gramPair
    have h := IntervalIntegrable.sum (f := fun (j : Fin n) (y : Real) =>
        (z i * conj (z j)) * Complex.exp (Complex.ofReal ((γ j - γ i) * y) * Complex.I))
      Finset.univ (fun j (_ : j ∈ Finset.univ) => hpiece i j)
    have hfun : (∑ j : Fin n, fun y : Real =>
        (z i * conj (z j)) * Complex.exp (Complex.ofReal ((γ j - γ i) * y) * Complex.I))
        = fun y : Real => ∑ j, (z i * conj (z j))
            * Complex.exp (Complex.ofReal ((γ j - γ i) * y) * Complex.I) := by
      funext y
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  have hEq : Set.EqOn (fun x : Real => expSum γ z x * conj (expSum γ z x))
      (fun x : Real => ∑ i, gramPair γ z i x) (Set.uIcc (-t) t) :=
    fun x _ => hpt x
  rw [intervalIntegral.integral_congr hEq,
    intervalIntegral.integral_finsetSum (f := gramPair γ z) (fun i (_ : i ∈ Finset.univ) =>
      hint i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold gramPair
  rw [intervalIntegral.integral_finsetSum
      (f := fun (j : Fin n) (y : Real) =>
        (z i * conj (z j)) * Complex.exp (Complex.ofReal ((γ j - γ i) * y) * Complex.I))
      (fun j (_ : j ∈ Finset.univ) => hpiece i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_const_mul (z i * conj (z j)),
    integral_winInt t (γ j - γ i) ht]

end C1BombieriSection8ExpMass
end Source
end ConnesWeilRH
