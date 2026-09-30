/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1RouteADirectProductDecay
import ConnesWeilRH.Dev.C1RouteAWeightedZeroMeasure
import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic
import ConnesWeilRH.Dev.C1RouteAMultiplicityBound

/-!
# Producer-side wiring of the direct-product decay brick (record 2268)

Record 2265 landed the producer brick
`laplaceAt_convolution_spectral_bound_of_strip`: a strip hypothesis
`hB : ∀ σ ∈ [-1/2, 1/2], min (D₂ b · M c, D₂ c · M b) σ ≤ B` yields the
per-zero chain-bound `‖Im ρ / 2π‖² ‖L (b ⋆ c) (centeredXiCoordinate ρ)‖ ≤
B / (2π)²`.  Record 2267 certifies the numeric instance
`B = bUpper2243 = 9506275.102584327` on the centered strip.

This module wires the producer brick into the count-free consumer chain of
record 2257 (`C1RouteAItem5Arithmetic.a005_item5_terminal_count_free`) with
the frozen constants:

1. `directProduct_dyadic_shell_bound` — the per-shell dyadic-tail face
   `‖L (b ⋆ c) (centeredXiCoordinate ρ)‖ ≤ bUpper2243 / (2^n)²` for
   `ρ` in height shell `n + 1`, mirroring
   `exists_spectral_laplaceAt_dyadic_tail_bound` with the concrete constant;
2. `directProduct_weightedZeroMeasure_shell_bound` — the shell mass bound by
   `spectralHeightMultiplicity (n + 1) · bUpper2243 / (2^n)²`, the frozen
   re-run of `exists_spectralHeightShell_weightedZeroMeasure_bound`;
3. `directProduct_highShell_tsum_bound` — the high-shell weighted-zero tsum
   bounded by `4 · spectralMultiplicityConstant · bUpper2243`, the frozen
   re-run of `exists_weightedZeroMeasure_highShell_tsum_bound`;
4. `a005_item5_producer_wired` — the end-to-end producer theorem: the strip
   hypothesis and the remaining registered obligations (count-side
   `spectralMultiplicityConstant ≤ multProxy2248`, the L1 margin enclosure,
   the non-tail charge bound, the 2255 gap bound) give the count-free
   terminal inequality with the actual high-shell tsum in the charge
   position.

Record 2274 adds `a005_item5_producer_wired_certified_multiplicity`,
which supplies the multiplicity comparison from a proved analytic bound.
Record 2310 adds `a005_item5_producer_wired_certified_multiplicity_gap_split`,
which consumes the certified hgap split through
`hgap_of_certified_split`: the single opaque gap hypothesis becomes the
registered 2275/2286/2304 decomposition plus the two pinned certified
enclosures (window 2308/2309, tail 2307), with the join arithmetic
machine-checked in `C1RouteAItem5Arithmetic`.
The original conditional theorems remain available for existing callers.
The strip, signed margin, non-tail charge, and gap hypotheses remain open.

No GO, no gate sign change, and no RH claim is made here.
-/

namespace ConnesWeilRH
namespace Dev

open ConnesWeilRH.Source.C1SpectralWeil
open ConnesWeilRH.Source.C1SpectralSummability
open ConnesWeilRH.Source.CC20YoshidaNearZeros
open ConnesWeilRH.Source.CC20YoshidaConvolution.CompactLogTest
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

/-- The centered-strip hypothesis at the frozen constant, as certified
numerically by record 2267. -/
abbrev FrozenStripHypothesis (b c : CompactLogTest) : Prop :=
  ∀ sigma ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2),
    min (stripSecondNorm sigma (b.test : ℝ → ℂ) * stripNorm sigma (c.test : ℝ → ℂ))
        (stripSecondNorm sigma (c.test : ℝ → ℂ) * stripNorm sigma (b.test : ℝ → ℂ))
      ≤ bUpper2243

/-- **Dyadic-tail face at the frozen constant.**  Under the certified strip
hypothesis, the direct-product transform of every source zero in height shell
`n + 1` obeys the dyadic tail bound with constant `bUpper2243`, mirroring
`exists_spectral_laplaceAt_dyadic_tail_bound` with the concrete envelope. -/
theorem directProduct_dyadic_shell_bound
    (b c : CompactLogTest) (hstrip : FrozenStripHypothesis b c) :
    ∀ n (rho : spectralHeightShell (n + 1)),
      norm (laplaceAt (b.convolution c) (centeredXiCoordinate rho)) ≤
        bUpper2243 / ((2 : ℝ) ^ n) ^ 2 := by
  intro n rho
  have hheightLarge : (2 : ℝ) ^ (n + 1) ≤ |rho.1.1.im| :=
    pow_succ_le_of_dyadicShellIndex_eq_succ rho.2
  have hheight : (2 : ℝ) ^ n ≤ |rho.1.1.im| := by
    calc
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n]
      _ ≤ |rho.1.1.im| := hheightLarge
  have hdenom : 0 < 2 * Real.pi := by positivity
  have hscaled :
      (2 : ℝ) ^ n / (2 * Real.pi) ≤
        |rho.1.1.im| / (2 * Real.pi) :=
    div_le_div_of_nonneg_right hheight hdenom.le
  have hscaledNonneg : 0 ≤ (2 : ℝ) ^ n / (2 * Real.pi) := by
    positivity
  have hscaledSq :
      ((2 : ℝ) ^ n / (2 * Real.pi)) ^ 2 ≤
        (|rho.1.1.im| / (2 * Real.pi)) ^ 2 :=
    pow_le_pow_left₀ hscaledNonneg hscaled 2
  have hquad := laplaceAt_convolution_spectral_bound_of_strip b c bUpper2243
    hstrip rho
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hdenom.le] at hquad
  have hsmall :
      ((2 : ℝ) ^ n / (2 * Real.pi)) ^ 2 *
          norm (laplaceAt (b.convolution c) (centeredXiCoordinate rho)) ≤
        bUpper2243 / (2 * Real.pi) ^ 2 :=
    (mul_le_mul_of_nonneg_right hscaledSq (norm_nonneg _)).trans hquad
  have hsmall' :
      (((2 : ℝ) ^ n) ^ 2 *
          norm (laplaceAt (b.convolution c) (centeredXiCoordinate rho))) /
            (2 * Real.pi) ^ 2 ≤ bUpper2243 / (2 * Real.pi) ^ 2 := by
    convert hsmall using 1
    field_simp [Real.pi_ne_zero]
  have hproduct : ((2 : ℝ) ^ n) ^ 2 *
      norm (laplaceAt (b.convolution c) (centeredXiCoordinate rho)) ≤
        bUpper2243 :=
    (div_le_div_iff_of_pos_right (sq_pos_of_pos hdenom)).mp hsmall'
  rw [le_div_iff₀ (sq_pos_of_pos (pow_pos (by norm_num) n))]
  nlinarith

/-- **Frozen shell-mass bound.**  The weighted-zero mass of one exact dyadic
height shell is bounded by the analytic multiplicity mass times the frozen
dyadic constant.  This is the re-run of
`exists_spectralHeightShell_weightedZeroMeasure_bound` with the producer's
concrete per-shell estimate and `F = b ⋆ c`. -/
theorem directProduct_weightedZeroMeasure_shell_bound
    (b c : CompactLogTest) (hstrip : FrozenStripHypothesis b c) (n : Nat) :
    (∑ rho ∈ (spectralHeightShell_finite (n + 1)).toFinset,
        spectralNormTerm (b.convolution c) rho) ≤
      spectralHeightMultiplicity (n + 1) *
        (bUpper2243 / ((2 : ℝ) ^ n) ^ 2) := by
  let shell := spectralHeightShell (n + 1)
  let hfinite : shell.Finite := spectralHeightShell_finite (n + 1)
  letI := hfinite.fintype
  have hmass : spectralHeightMultiplicity (n + 1) =
      ∑ rho ∈ hfinite.toFinset, (xiMultiplicity rho : Real) := by
    simpa only [spectralHeightMultiplicity, shell] using
      (tsum_finite_subtype_eq_sum_toFinset hfinite
        (fun rho => (xiMultiplicity rho : Real)))
  have hpoint : ∀ rho : shell,
      spectralNormTerm (b.convolution c) rho.1 ≤
        (xiMultiplicity rho.1 : Real) *
          (bUpper2243 / ((2 : ℝ) ^ n) ^ 2) := by
    intro rho
    unfold spectralNormTerm
    exact mul_le_mul_of_nonneg_left
      (directProduct_dyadic_shell_bound b c hstrip n rho)
      (Nat.cast_nonneg (xiMultiplicity rho.1))
  rw [hmass]
  calc
    (∑ rho ∈ hfinite.toFinset, spectralNormTerm (b.convolution c) rho) ≤
        ∑ rho ∈ hfinite.toFinset, (xiMultiplicity rho : Real) *
          (bUpper2243 / ((2 : ℝ) ^ n) ^ 2) := by
      exact Finset.sum_le_sum fun rho hrho => hpoint
        ⟨rho, hfinite.mem_toFinset.mp hrho⟩
    _ = (∑ rho ∈ hfinite.toFinset, (xiMultiplicity rho : Real)) *
          (bUpper2243 / ((2 : ℝ) ^ n) ^ 2) := by
      rw [Finset.sum_mul]

/-- **Frozen high-shell tsum bound.**  The exact-owner high-shell weighted-zero
tsum is bounded by `4 · spectralMultiplicityConstant · bUpper2243`: the re-run
of `exists_weightedZeroMeasure_highShell_tsum_bound` at the frozen producer
constant, with the geometric ratio `3/4` assembly unchanged. -/
theorem directProduct_highShell_tsum_bound
    (b c : CompactLogTest) (hstrip : FrozenStripHypothesis b c) :
    (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) ≤
      4 * spectralMultiplicityConstant * bUpper2243 := by
  let r : Real := (3 : Real) / 4
  let K : Real := spectralMultiplicityConstant * bUpper2243
  have hK : 0 ≤ K :=
    mul_nonneg spectralMultiplicityConstant_nonneg (by norm_num [bUpper2243])
  have hr0 : 0 ≤ r := by
    dsimp [r]
    norm_num
  have hr1 : r < 1 := by
    dsimp [r]
    norm_num
  have hgeo : Summable (fun n : Nat => K * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left K
  have hbound : ∀ n : Nat,
      (∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) ≤ K * r ^ n := by
    intro n
    let shell := spectralHeightShell (n + 1)
    let hfinite : shell.Finite := spectralHeightShell_finite (n + 1)
    have hsum :
        (∑' rho : shell, spectralNormTerm (b.convolution c) rho.1) =
          ∑ rho ∈ hfinite.toFinset, spectralNormTerm (b.convolution c) rho := by
      exact tsum_finite_subtype_eq_sum_toFinset hfinite
        (fun rho => spectralNormTerm (b.convolution c) rho)
    rw [hsum]
    dsimp [K, r]
    calc
      (∑ rho ∈ hfinite.toFinset, spectralNormTerm (b.convolution c) rho) ≤
          spectralHeightMultiplicity (n + 1) *
            (bUpper2243 / ((2 : ℝ) ^ n) ^ 2) :=
        directProduct_weightedZeroMeasure_shell_bound b c hstrip n
      _ ≤ (spectralMultiplicityConstant * (3 : ℝ) ^ n) *
            (bUpper2243 / ((2 : ℝ) ^ n) ^ 2) := by
        exact mul_le_mul_of_nonneg_right
          (spectralHeightMultiplicity_geometric_bound n)
          (div_nonneg (by norm_num [bUpper2243]) (sq_nonneg _))
      _ = spectralMultiplicityConstant * bUpper2243 * ((3 : ℝ) / 4) ^ n := by
        rw [div_pow]
        norm_num [pow_two, mul_pow]
        have hfour :
            (2 : ℝ) ^ n * (2 : ℝ) ^ n = 4 ^ n := by
          rw [← mul_pow]
          norm_num
        rw [hfour]
        ring
  have htailSummable : Summable (fun n : Nat =>
      ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) := by
    refine Summable.of_nonneg_of_le
      (fun n => tsum_nonneg (fun rho =>
        spectralNormTerm_nonnegative (b.convolution c) rho.1))
      hbound hgeo
  have htail := htailSummable.tsum_le_tsum hbound hgeo
  calc
    (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) ≤ ∑' n : Nat, K * r ^ n :=
      htail
    _ = K * (∑' n : Nat, r ^ n) := by rw [tsum_mul_left]
    _ = K * (1 / (1 - r)) := by
      rw [tsum_geometric_of_lt_one hr0 hr1]
      simp only [one_div]
    _ = 4 * spectralMultiplicityConstant * bUpper2243 := by
      dsimp [K, r]
      norm_num
      ring

/-- **End-to-end producer theorem.**  With the certified strip hypothesis, the
count-side obligation `spectralMultiplicityConstant ≤ multProxy2248`, the L1
margin enclosure, the non-tail charge bound, and the 2255 gap bound, the
count-free terminal inequality holds with the actual high-shell weighted-zero
tsum placed in the charge position.  This is
`a005_item5_terminal_count_free` fed by the wired producer chain at the frozen
constants `bUpper2243` and `spectralMultiplicityConstant`. -/
theorem a005_item5_producer_wired
    (b c : CompactLogTest) (hstrip : FrozenStripHypothesis b c)
    (hmult : spectralMultiplicityConstant ≤ multProxy2248)
    {qLo gap chargeRest : Real}
    (hmargin : margin2249 ≤ -qLo)
    (hcharge : chargeRest ≤ knownError2109)
    (hgap : gap ≤ gapCharge2255) :
    (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) +
      chargeRest + gap + eps0FullTail2249 < -qLo := by
  have htsum := directProduct_highShell_tsum_bound b c hstrip
  have hcharge' :
      (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) + chargeRest ≤
        4 * spectralMultiplicityConstant * bUpper2243 + knownError2109 := by
    linarith
  exact a005_item5_terminal_count_free
    (mult := spectralMultiplicityConstant) (B := bUpper2243)
    (charge := (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) + chargeRest)
    spectralMultiplicityConstant_nonneg hmult
    (by norm_num [bUpper2243]) le_rfl hmargin hcharge' hgap

/-- The producer inequality with the multiplicity comparison discharged by
record 2274's analytic bound. The strip, signed margin, non-tail charge,
and ideal-to-discrete gap remain explicit hypotheses. -/
theorem a005_item5_producer_wired_certified_multiplicity
    (b c : CompactLogTest) (hstrip : FrozenStripHypothesis b c)
    {qLo gap chargeRest : Real}
    (hmargin : margin2249 ≤ -qLo)
    (hcharge : chargeRest ≤ knownError2109)
    (hgap : gap ≤ gapCharge2255) :
    (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) +
      chargeRest + gap + eps0FullTail2249 < -qLo := by
  exact a005_item5_producer_wired b c hstrip
    Source.C1RouteAMultiplicityBound.spectralMultiplicityConstant_le_multProxy2248
    hmargin hcharge hgap

/-- **Producer with the certified gap split (record 2310).**  The 2255 gap
hypothesis is replaced by the registered 2275/2286/2304 decomposition
`hsplit` plus the two pinned certified enclosures: the window charge
(records 2308/2309, `windowCharge2309`) and the infinite-xi tail charge
(record 2307, `tailCharge2307`).  The join arithmetic is machine-checked
in `C1RouteAItem5Arithmetic.windowCharge2309_add_tailCharge2307_le_gapCharge2255`
and consumed through `hgap_of_certified_split`.  Multiplicity is discharged
by the 2274 analytic bound; the strip, signed margin, and non-tail charge
hypotheses remain explicit. -/
theorem a005_item5_producer_wired_certified_multiplicity_gap_split
    (b c : CompactLogTest) (hstrip : FrozenStripHypothesis b c)
    {qLo gap chargeRest windowCharge tailCharge : Real}
    (hmargin : margin2249 ≤ -qLo)
    (hcharge : chargeRest ≤ knownError2109)
    (hsplit : gap ≤ windowCharge + tailCharge)
    (hwindow : windowCharge ≤ windowCharge2309)
    (htail : tailCharge ≤ tailCharge2307) :
    (∑' n : Nat, ∑' rho : spectralHeightShell (n + 1),
        spectralNormTerm (b.convolution c) rho.1) +
      chargeRest + gap + eps0FullTail2249 < -qLo := by
  exact a005_item5_producer_wired_certified_multiplicity b c hstrip
    hmargin hcharge
    (hgap_of_certified_split hsplit hwindow htail)

end Dev
end ConnesWeilRH
