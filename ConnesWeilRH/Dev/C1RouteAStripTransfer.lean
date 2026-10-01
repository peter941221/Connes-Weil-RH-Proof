/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1RouteAProducerWired
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Strip transfer law (record 2312)

Record 2303 certified the centered-strip envelope on the corrected
width-a^2 owner as a grid maximum times a continuum-transfer factor
`e^(2 rmax h)`; the transfer half rested on the registered log-derivative
law `|d/dsigma log N| <= 2 rmax` for the strip min-product `N`.  This
module formalizes the analytic core of that transfer in Lean:

* `expWeightedIntegral_le_transfer_of_neighbor` — the primitive
  exponential transfer for a nonnegative continuous weight `g` supported
  in `[-R, R]`: every exponent `sigma` within `h` of a reference exponent
  `sigma_0` satisfies `∫ e^(sigma x) g <= e^(R h) * ∫ e^(sigma_0 x) g`.
  This is the exponential form of the transfer law (it is what the
  linearized log-derivative bound integrates out to, and it needs no
  differentiation under the integral: the pointwise bound
  `e^(sigma x) <= e^(sigma_0 x + R h)` on the support integrates
  directly);
* `stripNorm_le_transfer_of_neighbor` and
  `stripSecondNorm_le_transfer_of_neighbor` — the two strip weights of a
  test function, with the support of `deriv (deriv f)` fed through
  `support_deriv_subset`/`tsupport_deriv_subset`;
* `min_stripProduct_le_transfer_of_neighbor` — the min-product transfer
  `N sigma <= e^(2 R h) * N sigma_0` at a radius `R` dominating the
  supports, assembled from the four per-factor transfers;
* `frozenStripHypothesis_of_certified_grid` — the 2303 grid consumer:
  the grid-existence hypothesis (every centered `sigma` within `h` of a
  node whose min-product is at most the pinned `stripGridMax2303`), the
  support-radius bound, and the record 2312 exponent pin
  `R * h <= stripRadius2303 * stripHalfStep2303` yield the certified
  envelope shape consumed by
  `frozenStripHypothesis_of_certified_envelope` (record 2311).  The
  concrete corner `frozenStripHypothesis_of_certified_grid_rmax`
  instantiates the certified radius and half-step.

The residual inputs are exactly: the grid-existence arithmetic (every
centered `sigma` is within the half-step of one of the 101 certified
sigma-nodes), the grid maximum over the captured owner (artifact, as in
record 2311), and the support-radius bound identifying the captured
owner's support with
`[-stripRadius2303, stripRadius2303]` (owner bridge).  No Lean
formalization of the grid sampling, no owner bridge, no producer GO, no
gate sign change, no RH claim.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open scoped ContDiff

/-- **Exponential transfer of a strip-weighted integral (record 2312).**
For a nonnegative continuous weight `g` supported in `[-R, R]`, any two
exponents within `h` obey

`∫ e^(sigma x) g x <= e^(R h) * ∫ e^(sigma_0 x) g x`.

On the support, `|x| <= R` gives the pointwise bound
`e^(sigma x) <= e^(sigma_0 x + R h)`, which integrates against `g >= 0`;
no differentiation is involved. -/
theorem expWeightedIntegral_le_transfer_of_neighbor {g : ℝ → ℝ}
    (hg : Continuous g) (hgnn : ∀ x, 0 ≤ g x)
    {R h σ σ₀ : ℝ} (hsupp : Function.support g ⊆ Set.Icc (-R) R)
    (hneighbor : |σ - σ₀| ≤ h) :
    (∫ x : ℝ, Real.exp (σ * x) * g x)
      ≤ Real.exp (R * h) * ∫ x : ℝ, Real.exp (σ₀ * x) * g x := by
  have hpt : ∀ x, Real.exp (σ * x) * g x
      ≤ Real.exp (R * h) * (Real.exp (σ₀ * x) * g x) := by
    intro x
    by_cases hx : g x = 0
    · simp [hx]
    · have hxI : x ∈ Set.Icc (-R) R := hsupp hx
      have habsx : |x| ≤ R := abs_le.mpr hxI
      have hh0 : 0 ≤ h := le_trans (abs_nonneg _) hneighbor
      have hmul : (σ - σ₀) * x ≤ R * h := by
        have h1 : (σ - σ₀) * x ≤ |(σ - σ₀) * x| := le_abs_self _
        rw [abs_mul] at h1
        have h2 : |σ - σ₀| * |x| ≤ h * R :=
          mul_le_mul hneighbor habsx (abs_nonneg x) hh0
        exact h1.trans (h2.trans (le_of_eq (mul_comm h R)))
      have hexp : Real.exp (σ * x) ≤ Real.exp (σ₀ * x) * Real.exp (R * h) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      calc Real.exp (σ * x) * g x
          ≤ (Real.exp (σ₀ * x) * Real.exp (R * h)) * g x :=
            mul_le_mul_of_nonneg_right hexp (hgnn x)
        _ = Real.exp (R * h) * (Real.exp (σ₀ * x) * g x) := by ring
  have hint : Integrable (fun x : ℝ => Real.exp (σ₀ * x) * g x) := by
    have hcont : Continuous fun x : ℝ => Real.exp (σ₀ * x) * g x :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hg
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-R) R) isCompact_Icc ?_
    intro x hx
    exact hsupp (mul_ne_zero_iff.mp hx).2
  calc (∫ x : ℝ, Real.exp (σ * x) * g x)
      ≤ ∫ x : ℝ, Real.exp (R * h) * (Real.exp (σ₀ * x) * g x) := by
        apply integral_mono_of_nonneg
        · filter_upwards with x
          exact mul_nonneg (Real.exp_nonneg _) (hgnn x)
        · exact hint.const_mul _
        · filter_upwards with x
          exact hpt x
    _ = Real.exp (R * h) * ∫ x : ℝ, Real.exp (σ₀ * x) * g x :=
        integral_const_mul _ _

/-- **Strip-weight transfer (record 2312).**  The strip `L¹` weight
`stripNorm` transfers exponentially across a support radius `R` for any
continuous function with support in `[-R, R]`. -/
theorem stripNorm_le_transfer_of_neighbor (f : ℝ → ℂ) (hf : Continuous f)
    {R h σ σ₀ : ℝ} (hsupp : Function.support f ⊆ Set.Icc (-R) R)
    (hneighbor : |σ - σ₀| ≤ h) :
    stripNorm σ f ≤ Real.exp (R * h) * stripNorm σ₀ f := by
  have h := expWeightedIntegral_le_transfer_of_neighbor (g := fun x => ‖f x‖)
    hf.norm (fun x => norm_nonneg (f x))
    (fun x hx => hsupp fun h0 => hx (by simp [h0])) hneighbor
  simpa only [stripNorm] using h

/-- **Second-derivative strip-weight transfer (record 2312).**  The same
transfer for `stripSecondNorm`, applied to the literal second derivative
`deriv (deriv f)`; its support is fed in through the derivative support
chain at the consumer. -/
theorem stripSecondNorm_le_transfer_of_neighbor (f : ℝ → ℂ)
    (hf : Continuous (deriv (deriv f)))
    {R h σ σ₀ : ℝ}
    (hsupp : Function.support (deriv (deriv f)) ⊆ Set.Icc (-R) R)
    (hneighbor : |σ - σ₀| ≤ h) :
    stripSecondNorm σ f ≤ Real.exp (R * h) * stripSecondNorm σ₀ f := by
  simpa only [stripSecondNorm, stripNorm] using
    stripNorm_le_transfer_of_neighbor (deriv (deriv f)) hf hsupp hneighbor

/-- **Min-product transfer (record 2312).**  For a pair `b`, `c` whose
supports and second-derivative supports lie in `[-R, R]`, the centered
min-product `N sigma = min (D₂ b * M c, D₂ c * M b) sigma` transfers
exponentially: `N sigma <= e^(2 R h) * N sigma_0` whenever
`|sigma - sigma_0| <= h`.  This is the machine-checked form of the record
2303 log-derivative law `|d/dsigma log N| <= 2 rmax`. -/
theorem min_stripProduct_le_transfer_of_neighbor (b c : ℝ → ℂ)
    (hb : Continuous b) (hc : Continuous c)
    (hb2 : Continuous (deriv (deriv b))) (hc2 : Continuous (deriv (deriv c)))
    {R h σ σ₀ : ℝ}
    (hsuppb : Function.support b ⊆ Set.Icc (-R) R)
    (hsuppc : Function.support c ⊆ Set.Icc (-R) R)
    (hsuppb2 : Function.support (deriv (deriv b)) ⊆ Set.Icc (-R) R)
    (hsuppc2 : Function.support (deriv (deriv c)) ⊆ Set.Icc (-R) R)
    (hneighbor : |σ - σ₀| ≤ h) :
    min (stripSecondNorm σ b * stripNorm σ c)
        (stripSecondNorm σ c * stripNorm σ b)
      ≤ Real.exp (2 * R * h) *
        min (stripSecondNorm σ₀ b * stripNorm σ₀ c)
            (stripSecondNorm σ₀ c * stripNorm σ₀ b) := by
  have hDb := stripSecondNorm_le_transfer_of_neighbor b hb2 hsuppb2 hneighbor
  have hDc := stripSecondNorm_le_transfer_of_neighbor c hc2 hsuppc2 hneighbor
  have hMb := stripNorm_le_transfer_of_neighbor b hb hsuppb hneighbor
  have hMc := stripNorm_le_transfer_of_neighbor c hc hsuppc hneighbor
  have h1 : stripSecondNorm σ b * stripNorm σ c
      ≤ Real.exp (2 * R * h) * (stripSecondNorm σ₀ b * stripNorm σ₀ c) := by
    calc stripSecondNorm σ b * stripNorm σ c
        ≤ (Real.exp (R * h) * stripSecondNorm σ₀ b) *
            (Real.exp (R * h) * stripNorm σ₀ c) :=
          mul_le_mul hDb hMc (stripNorm_nonneg σ c)
            (mul_nonneg (Real.exp_nonneg _) (stripSecondNorm_nonneg σ₀ b))
      _ = Real.exp (2 * R * h) * (stripSecondNorm σ₀ b * stripNorm σ₀ c) := by
          rw [show (Real.exp (R * h) * stripSecondNorm σ₀ b) *
                (Real.exp (R * h) * stripNorm σ₀ c) =
              (Real.exp (R * h) * Real.exp (R * h)) *
                (stripSecondNorm σ₀ b * stripNorm σ₀ c) by ring,
            ← Real.exp_add]
          congr 1
          ring_nf
  have h2 : stripSecondNorm σ c * stripNorm σ b
      ≤ Real.exp (2 * R * h) * (stripSecondNorm σ₀ c * stripNorm σ₀ b) := by
    calc stripSecondNorm σ c * stripNorm σ b
        ≤ (Real.exp (R * h) * stripSecondNorm σ₀ c) *
            (Real.exp (R * h) * stripNorm σ₀ b) :=
          mul_le_mul hDc hMb (stripNorm_nonneg σ b)
            (mul_nonneg (Real.exp_nonneg _) (stripSecondNorm_nonneg σ₀ c))
      _ = Real.exp (2 * R * h) * (stripSecondNorm σ₀ c * stripNorm σ₀ b) := by
          rw [show (Real.exp (R * h) * stripSecondNorm σ₀ c) *
                (Real.exp (R * h) * stripNorm σ₀ b) =
              (Real.exp (R * h) * Real.exp (R * h)) *
                (stripSecondNorm σ₀ c * stripNorm σ₀ b) by ring,
            ← Real.exp_add]
          congr 1
          ring_nf
  calc min (stripSecondNorm σ b * stripNorm σ c)
          (stripSecondNorm σ c * stripNorm σ b)
      ≤ min (Real.exp (2 * R * h) * (stripSecondNorm σ₀ b * stripNorm σ₀ c))
            (Real.exp (2 * R * h) * (stripSecondNorm σ₀ c * stripNorm σ₀ b)) :=
        min_le_min h1 h2
    _ = Real.exp (2 * R * h) *
          min (stripSecondNorm σ₀ b * stripNorm σ₀ c)
              (stripSecondNorm σ₀ c * stripNorm σ₀ b) :=
        (mul_min_of_nonneg _ _ (Real.exp_nonneg (2 * R * h))).symm

/-- **Certified grid consumer (record 2312).**  The record 2303 envelope
assembled from the transfer law: given the grid-existence hypothesis
(every centered `sigma` is within `h` of a certified node whose
min-product is at most the pinned `stripGridMax2303`), the
support-radius bound `tsupport f ⊆ [-R, R]` for both tests, and the
record 2312 exponent pin `R * h <= stripRadius2303 * stripHalfStep2303`,
the certified envelope shape of record 2311 holds, hence
`FrozenStripHypothesis`.  Continuity of the tests and of their literal
second derivatives is read off the Schwartz structure. -/
theorem frozenStripHypothesis_of_certified_grid (b c : CompactLogTest)
    (R h : ℝ)
    (hRh : R * h ≤ stripRadius2303 * stripHalfStep2303)
    (htsupp_b : tsupport (b.test : ℝ → ℂ) ⊆ Set.Icc (-R) R)
    (htsupp_c : tsupport (c.test : ℝ → ℂ) ⊆ Set.Icc (-R) R)
    (hgrid : ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      ∃ σ₀ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
        |σ - σ₀| ≤ h ∧
          min (stripSecondNorm σ₀ (b.test : ℝ → ℂ) *
                stripNorm σ₀ (c.test : ℝ → ℂ))
              (stripSecondNorm σ₀ (c.test : ℝ → ℂ) *
                stripNorm σ₀ (b.test : ℝ → ℂ))
            ≤ stripGridMax2303) :
    FrozenStripHypothesis b c := by
  have hb_cont : Continuous (b.test : ℝ → ℂ) := (b.test.smooth ⊤).continuous
  have hc_cont : Continuous (c.test : ℝ → ℂ) := (c.test.smooth ⊤).continuous
  have hb_smooth2 : ContDiff ℝ (2 : WithTop (WithTop ℕ))
      (b.test : ℝ → ℂ) :=
    (b.test.smooth ⊤).of_le (by decide)
  have hb_smoothFirst : ContDiff ℝ (1 : WithTop (WithTop ℕ))
      (deriv (b.test : ℝ → ℂ)) := ContDiff.deriv' hb_smooth2
  have hb2_cont : Continuous (deriv (deriv (b.test : ℝ → ℂ))) :=
    hb_smoothFirst.continuous_deriv (by decide)
  have hc_smooth2 : ContDiff ℝ (2 : WithTop (WithTop ℕ))
      (c.test : ℝ → ℂ) :=
    (c.test.smooth ⊤).of_le (by decide)
  have hc_smoothFirst : ContDiff ℝ (1 : WithTop (WithTop ℕ))
      (deriv (c.test : ℝ → ℂ)) := ContDiff.deriv' hc_smooth2
  have hc2_cont : Continuous (deriv (deriv (c.test : ℝ → ℂ))) :=
    hc_smoothFirst.continuous_deriv (by decide)
  have hsuppb : Function.support (b.test : ℝ → ℂ) ⊆ Set.Icc (-R) R :=
    (subset_tsupport _).trans htsupp_b
  have hsuppc : Function.support (c.test : ℝ → ℂ) ⊆ Set.Icc (-R) R :=
    (subset_tsupport _).trans htsupp_c
  have hsuppb2 :
      Function.support (deriv (deriv (b.test : ℝ → ℂ))) ⊆ Set.Icc (-R) R :=
    ((support_deriv_subset (f := deriv (b.test : ℝ → ℂ))).trans
      (tsupport_deriv_subset (f := (b.test : ℝ → ℂ)))).trans htsupp_b
  have hsuppc2 :
      Function.support (deriv (deriv (c.test : ℝ → ℂ))) ⊆ Set.Icc (-R) R :=
    ((support_deriv_subset (f := deriv (c.test : ℝ → ℂ))).trans
      (tsupport_deriv_subset (f := (c.test : ℝ → ℂ)))).trans htsupp_c
  have hexp : Real.exp (2 * R * h) ≤ stripTransfer2303 := by
    refine (Real.exp_le_exp.mpr ?_).trans
      real_exp_transfer_le_stripTransfer2303
    linarith [hRh]
  apply frozenStripHypothesis_of_certified_envelope
  intro σ hσ
  obtain ⟨σ₀, _hσ₀, hnear, hval⟩ := hgrid σ hσ
  calc min (stripSecondNorm σ (b.test : ℝ → ℂ) *
            stripNorm σ (c.test : ℝ → ℂ))
          (stripSecondNorm σ (c.test : ℝ → ℂ) *
            stripNorm σ (b.test : ℝ → ℂ))
      ≤ Real.exp (2 * R * h) *
          min (stripSecondNorm σ₀ (b.test : ℝ → ℂ) *
                stripNorm σ₀ (c.test : ℝ → ℂ))
              (stripSecondNorm σ₀ (c.test : ℝ → ℂ) *
                stripNorm σ₀ (b.test : ℝ → ℂ)) :=
        min_stripProduct_le_transfer_of_neighbor (b.test : ℝ → ℂ)
          (c.test : ℝ → ℂ) hb_cont hc_cont hb2_cont hc2_cont
          hsuppb hsuppc hsuppb2 hsuppc2 hnear
    _ ≤ Real.exp (2 * R * h) * stripGridMax2303 :=
        mul_le_mul_of_nonneg_left hval (Real.exp_nonneg _)
    _ ≤ stripTransfer2303 * stripGridMax2303 :=
        mul_le_mul_of_nonneg_right hexp
          (by norm_num [stripGridMax2303])
    _ = stripGridMax2303 * stripTransfer2303 := mul_comm _ _

/-- **Certified grid consumer at the pin (record 2312).**  The concrete
corner at the certified radius and half-step: supports in
`[-stripRadius2303, stripRadius2303]` (any radius the owner bridge can
prove at most the record 2303 render `6.553600000000003` qualifies) and
every centered `sigma` within `stripHalfStep2303` of a node whose
min-product is at most `stripGridMax2303`. -/
theorem frozenStripHypothesis_of_certified_grid_rmax (b c : CompactLogTest)
    (htsupp_b : tsupport (b.test : ℝ → ℂ) ⊆
      Set.Icc (-stripRadius2303) stripRadius2303)
    (htsupp_c : tsupport (c.test : ℝ → ℂ) ⊆
      Set.Icc (-stripRadius2303) stripRadius2303)
    (hgrid : ∀ σ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
      ∃ σ₀ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
        |σ - σ₀| ≤ stripHalfStep2303 ∧
          min (stripSecondNorm σ₀ (b.test : ℝ → ℂ) *
                stripNorm σ₀ (c.test : ℝ → ℂ))
              (stripSecondNorm σ₀ (c.test : ℝ → ℂ) *
                stripNorm σ₀ (b.test : ℝ → ℂ))
            ≤ stripGridMax2303) :
    FrozenStripHypothesis b c :=
  frozenStripHypothesis_of_certified_grid b c stripRadius2303 stripHalfStep2303
    le_rfl htsupp_b htsupp_c hgrid

end Dev
end ConnesWeilRH
