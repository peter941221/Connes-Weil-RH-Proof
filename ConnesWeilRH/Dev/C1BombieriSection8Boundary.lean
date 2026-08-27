/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1BombieriSection7Gamma

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Lemma-10 detector skeleton: the even/odd boundary identity

Bombieri proves his Lemma 10 (book p.209: "Moreover if every γ is real all
eigenvalues of H(Γ;t) are non-negative") by the chain (8.5)-(8.15) on
book pp.210-212: the eigenvalue system is rewritten in terms of the
exponential sum `Z(u) = Σ_γ e^{-iγu} z_γ` (8.5), the weighted sum
`λ Σ_γ w_γ conj(w_γ)` is expressed as `¼∫|Z|² + ∫|Z'|²` on `[−t,t]`
minus a two-endpoint boundary correction (8.11), the correction is
recombined over the even and odd parts `Z^±(u) = ½[Z(u) ± Z(−u)]` into

```
(e^t + e^{−t})/(2(e^t − e^{−t})) (|Z(t)|² + |Z(−t)|²)
    − (conj Z(t) Z(−t) + Z(t) conj Z(−t))/(e^t − e^{−t})
  = tanh(t/2) |Z⁺(t)|² + coth(t/2) |Z⁻(t)|²
```

(p.211, bracket verified below), and the Wirtinger-type inequality (8.13)
with equality functions `e^{u/2} ± e^{−u/2}` finally gives (8.14):
`λ Σ w_γ conj(w_γ) = ¼∫|F|² + ∫|F'|² ≥ 0`.

This leaf lands the pure-finite-algebra core of that chain: the even/odd
boundary recombination identity and its nonnegativity for `t > 0`.  The
bracket is `a·conj b + conj a·b` (the REAL-symmetric combination, twice
the real part of `a·conj b`): the book's printed MINUS between the two
bracket summands cannot be literal -- with the printed anti-symmetric
difference the identity fails already at `a = b = 1` (LHS `cosh t/sinh t`,
RHS `tanh(t/2)`), while the symmetric combination closes the identity on
generic complex probes (floats stay out of Lean; the identity is proven
from `Real.exp_neg` and `ring` alone).  This is the second printed-form
erratum recorded in `docs/proofs/1043` section 6y.

Proof mechanics (house rules): every coefficient is written as an explicit
`((... : Real) : Complex)` cast so the elaboration is deterministic;
after `Real.exp_neg` every compound denominator is frozen as an opaque
complex atom via `set` BEFORE `field_simp` (whose inner `ring_nf` would
otherwise distribute inside the inverse arguments), with the nonzero
facts transported through the defining equations.  The remaining steps of
Lemma 10 (the (8.13) integral inequality and the assembly (8.14)) are
analytic and stay open; this leaf is a DETECTOR skeleton, never an
unconditional certificate.  No numerical datum enters any leaf: only
exact identities are proven.
-/

namespace ConnesWeilRH
namespace Source
namespace C1BombieriSection8Boundary

/-- The even/odd boundary recombination (book p.211, between (8.11) and
(8.12)), for the two endpoint values `a = Z(t)`, `b = Z(−t)`: the raw
two-point boundary correction equals the `tanh(t/2)`-weighted square of
the even part plus the `coth(t/2)`-weighted square of the odd part,
written with `x * conj x` so no absolute-value theory is needed. -/
theorem bombieriEvenOddBoundary (a b : Complex) (t : Real) (ht : t ≠ 0) :
    ((Real.exp t + Real.exp (-t) : Real) : Complex)
        / ((2 * (Real.exp t - Real.exp (-t) : Real) : Complex))
        * (a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b)
      - (a * (starRingEnd ℂ) b + (starRingEnd ℂ) a * b)
        / ((Real.exp t - Real.exp (-t) : Real) : Complex)
      = ((Real.exp t - 1 : Real) : Complex)
          / ((Real.exp t + 1 : Real) : Complex)
          * ((a + b) * (starRingEnd ℂ) (a + b) / 4)
        + ((Real.exp t + 1 : Real) : Complex)
          / ((Real.exp t - 1 : Real) : Complex)
          * ((a - b) * (starRingEnd ℂ) (a - b) / 4) := by
  -- `exp (-t)` is `(exp t)⁻¹`; the identity is polynomial in `exp t` only
  -- after that identification.
  rw [Real.exp_neg]
  -- Freeze every compound denominator as an opaque atom BEFORE field_simp.
  set dA : Complex := ((Real.exp t + (Real.exp t)⁻¹ : Real) : Complex) with hdA
  set dB : Complex := ((2 * (Real.exp t - (Real.exp t)⁻¹ : Real)) : Complex) with hdB
  set dC : Complex := ((Real.exp t - (Real.exp t)⁻¹ : Real) : Complex) with hdC
  set dD : Complex := ((Real.exp t + 1 : Real) : Complex) with hdD
  set dE : Complex := ((Real.exp t - 1 : Real) : Complex) with hdE
  -- Nonzero facts, transported through the defining equations.
  have castNe : ∀ r : Real, r ≠ 0 → ((r : Real) : Complex) ≠ 0 := by
    intro r hr h0
    have h2 := congrArg Complex.re h0
    simp at h2
    exact hr h2
  have hX : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have hp : 0 < Real.exp t := Real.exp_pos t
  have hpinv : 0 < (Real.exp t)⁻¹ := inv_pos.mpr hp
  have hE2 : Real.exp t - 1 ≠ 0 := by
    intro h0
    exact ht (Real.exp_injective (by rw [Real.exp_zero]; linarith))
  have hES : Real.exp t - (Real.exp t)⁻¹ ≠ 0 := by
    intro h0
    have h1 : Real.exp t = (Real.exp t)⁻¹ := sub_eq_zero.mp h0
    have h2 : Real.exp t * Real.exp t = 1 := by
      nth_rewrite 1 [h1]
      exact inv_mul_cancel₀ hX
    have h3 : Real.exp t ^ 2 = 1 := by rw [pow_two]; exact h2
    rcases sq_eq_one_iff.mp h3 with h4 | h4
    · exact ht (Real.exp_injective (h4.trans Real.exp_zero.symm))
    · exact absurd h4 (by linarith)
  have nA : dA ≠ 0 := castNe _ (by linarith)
  have nC : dC ≠ 0 := castNe _ hES
  have h6 : 2 * (Real.exp t - (Real.exp t)⁻¹) ≠ 0 := by
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · norm_num at h
    · exact hES h
  -- `set` normalized `dB` to `2 * dC`, so transport through `hdB` directly.
  have nB : dB ≠ 0 := by
    rw [hdB]
    exact mul_ne_zero (by norm_num) nC
  have nD : dD ≠ 0 := castNe _ (by linarith)
  have nE : dE ≠ 0 := castNe _ hE2
  rw [map_add (starRingEnd ℂ) a b, map_sub (starRingEnd ℂ) a b]
  field_simp [nA, nB, nC, nD, nE]
  -- Unfold the frozen atoms back; the residue is polynomial in the single
  -- cast atom once `push_cast` expands the ofReal sums, and the second
  -- `field_simp` clears the remaining inverse powers with the cast-nonzero
  -- fact.
  rw [hdA, hdB, hdC, hdD, hdE]
  push_cast
  field_simp [(Complex.ofReal_ne_zero.mpr hX)]
  ring

/-- The recombined boundary correction is nonnegative: both weights
`(e^t − 1)/(e^t + 1)` and `(e^t + 1)/(e^t − 1)` are strictly positive for
`t > 0`, and the even/odd endpoint terms are squared moduli
(`Complex.normSq`, which is `abs` squared on ℂ). -/
theorem bombieriEvenOddBoundary_nonneg (a b : Complex) (t : Real) (ht : 0 < t) :
    0 ≤ (Real.exp t - 1) / (Real.exp t + 1) * Complex.normSq ((a + b) / 2)
      + (Real.exp t + 1) / (Real.exp t - 1) * Complex.normSq ((a - b) / 2) := by
  have h1 : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hp := Real.exp_pos t
  have hpos1 : 0 < (Real.exp t - 1) / (Real.exp t + 1) :=
    div_pos (by linarith) (by linarith)
  have hpos2 : 0 < (Real.exp t + 1) / (Real.exp t - 1) :=
    div_pos (by linarith) (by linarith)
  exact add_nonneg
    (mul_nonneg (le_of_lt hpos1) (Complex.normSq_nonneg _))
    (mul_nonneg (le_of_lt hpos2) (Complex.normSq_nonneg _))

end C1BombieriSection8Boundary
end Source
end ConnesWeilRH
