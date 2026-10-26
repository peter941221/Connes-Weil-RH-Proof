import ConnesWeilRH.Dev.C1RouteBSplitRungEnvelope3115

/-! A two-sided, whole-exterior bound on the actual powered-seed cardinal sum.

Every node remains in the separation denominator and polynomial product.
The seventh derivative supplies decay of order 70 after the tenth power.
The finite-owner degree condition is explicit. No numerical pin is assumed
or proved by this module.
-/

namespace ConnesWeilRH.Source.C1RouteBSplitRungEnvelope3115

open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open C1ExplicitSmoothSeed C1ExplicitFiniteNodeCorrection C1StripTransport2722C
open scoped BigOperators

noncomputable section

def seventhArm3115 (z : ℂ) (T : ℝ) : ℝ :=
  Real.exp (max |z.re| |1 - z.re|) * (2000000000 * (2 : ℝ) ^ 7) /
    (T - |z.im|) ^ 7

theorem poweredSeed_exterior_arm3115 {σ t T : ℝ} (z : ℂ)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (hT : 0 < T)
    (ht : T ≤ |t|) (hz : |z.im| < T) :
    ‖laplaceAt poweredSeed (((σ : ℂ) + (t : ℂ) * Complex.I) - z)‖ ≤
      seventhArm3115 z T ^ 10 / (|t| / T) ^ 70 := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  let q : ℝ := |t| / T
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hq : 1 ≤ q := (le_div_iff₀ hT).mpr (by simpa using ht)
  have hqp : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqt : q * T = |t| := div_mul_cancel₀ _ hT.ne'
  have hd : 0 < T - |z.im| := sub_pos.mpr hz
  have hsep : q * (T - |z.im|) ≤ |t - z.im| := by
    have htri : |t| ≤ |t - z.im| + |z.im| := by
      calc |t| = |(t - z.im) + z.im| := by congr 1; ring
           _ ≤ |t - z.im| + |z.im| := abs_add_le _ _
    have hm := mul_le_mul_of_nonneg_right hq (abs_nonneg z.im)
    nlinarith
  have hdist : 0 < |t - z.im| := lt_of_lt_of_le (mul_pos hqp hd) hsep
  have hv : ((1 / 2 : ℂ) * (s - z)).im ≠ 0 := by
    rw [halved_im_eq, hsim]
    exact div_ne_zero (abs_pos.mp hdist) (by norm_num)
  have hD : derivOrderL1 7 smoothSeed ≤ (2000000000 : ℝ) := by
    simpa [splitD3115] using splitD_bound3115 7 (by simp [splitRungs3115])
  have hseed := norm_laplaceAt_smoothSeed_le_rung hD hv
  rw [halved_re_abs, rung_div_eq, hsre, hsim] at hseed
  have hE : Real.exp |σ - z.re| ≤ Real.exp (max |z.re| |1 - z.re|) :=
    Real.exp_le_exp.mpr (abs_sub_le_max_endpoint z.re hσ)
  have hbound : ‖laplaceAt smoothSeed ((1 / 2 : ℂ) * (s - z))‖ ≤
      Real.exp (max |z.re| |1 - z.re|) * (2000000000 * (2 : ℝ) ^ 7) /
        (q * (T - |z.im|)) ^ 7 := by
    calc _ ≤ Real.exp (max |z.re| |1 - z.re|) *
          ((2000000000 : ℝ) * 2 ^ 7 / |t - z.im| ^ 7) :=
        hseed.trans (mul_le_mul_of_nonneg_right hE (by positivity))
      _ = (Real.exp (max |z.re| |1 - z.re|) * (2000000000 * (2 : ℝ) ^ 7)) /
          |t - z.im| ^ 7 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
        (pow_pos (mul_pos hqp hd) 7)
        (pow_le_pow_left₀ (le_of_lt (mul_pos hqp hd)) hsep 7)
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hbound 10
  change ‖laplaceAt poweredSeed (s - z)‖ ≤ seventhArm3115 z T ^ 10 / q ^ 70
  rw [poweredSeed_laplaceAt, norm_pow]
  refine hpow.trans_eq ?_
  simp only [seventhArm3115, mul_pow, div_pow, ← pow_mul, div_mul_eq_div_div]
  simp only [div_div]
  rw [mul_comm (q ^ (7 * 10))]

def cardinalExteriorBound3115 (nodes : Finset ℂ) (y : ℂ → ℂ)
    (T : ℝ) (p : ℕ) : ℝ :=
  ∑ z ∈ nodes,
    ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
      (∏ w ∈ nodes.erase z, (max |w.re| |1 - w.re| + T + |w.im|)) *
      seventhArm3115 z T ^ 10 * T ^ p

theorem weighted_cardinalSum_le_exterior3115
    (nodes : Finset ℂ) (y : ℂ → ℂ) {σ t T : ℝ} (p : ℕ)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (hT : 0 < T) (ht : T ≤ |t|)
    (hheight : ∀ z ∈ nodes, |z.im| < T) (hdegree : nodes.card + p ≤ 71) :
    |t| ^ p * ‖cardinalSum nodes poweredSeed y
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        cardinalExteriorBound3115 nodes y T p := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  let q : ℝ := |t| / T
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hq : 1 ≤ q := (le_div_iff₀ hT).mpr (by simpa using ht)
  have hqp : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqt : q * T = |t| := div_mul_cancel₀ _ hT.ne'
  have hfactor (w : ℂ) : ‖w - s‖ ≤
      q * (max |w.re| |1 - w.re| + T + |w.im|) := by
    have hre : |w.re - s.re| ≤ max |w.re| |1 - w.re| := by
      rw [hsre, abs_sub_comm]
      exact abs_sub_le_max_endpoint w.re hσ
    have him : |w.im - s.im| ≤ |t| + |w.im| := by
      rw [hsim, abs_sub_comm]
      exact abs_sub _ _
    have hn := (Complex.norm_le_abs_re_add_abs_im (w - s)).trans
      (add_le_add hre him)
    have hm := mul_le_mul_of_nonneg_right hq
      (add_nonneg ((abs_nonneg w.re).trans
        (le_max_left |w.re| |1 - w.re|)) (abs_nonneg w.im))
    nlinarith
  have hterm (z : ℂ) (hz : z ∈ nodes) :
      |t| ^ p * ‖y z / (nodeProduct nodes z z * laplaceAt poweredSeed 0) *
          (nodeProduct nodes z s * laplaceAt poweredSeed (s - z))‖ ≤
        ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
          (∏ w ∈ nodes.erase z, (max |w.re| |1 - w.re| + T + |w.im|)) *
          seventhArm3115 z T ^ 10 * T ^ p := by
    let c := ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖)
    let P := ∏ w ∈ nodes.erase z, (max |w.re| |1 - w.re| + T + |w.im|)
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hP : 0 ≤ P := by
      dsimp only [P]
      apply Finset.prod_nonneg
      intro w _
      have hn := (abs_nonneg w.re).trans (le_max_left |w.re| |1 - w.re|)
      positivity
    have hpoly : ‖nodeProduct nodes z s‖ ≤ q ^ (nodes.erase z).card * P := by
      have h := norm_nodeProduct_le nodes z s
        (fun w => q * (max |w.re| |1 - w.re| + T + |w.im|)) (fun w _ => hfactor w)
      simpa only [Finset.prod_mul_distrib, Finset.prod_const] using h
    have hseed := poweredSeed_exterior_arm3115 z hσ hT ht (hheight z hz)
    have hdeg : (nodes.erase z).card + p ≤ 70 := by
      rw [Finset.card_erase_of_mem hz]
      have hpos := Finset.card_pos.mpr ⟨z, hz⟩
      omega
    have hratio : q ^ ((nodes.erase z).card + p) / q ^ 70 ≤ 1 :=
      (div_le_one (pow_pos hqp 70)).mpr (pow_le_pow_right₀ hq hdeg)
    have hmul := mul_le_mul hpoly hseed (norm_nonneg _)
      (mul_nonneg (pow_nonneg (le_of_lt hqp) _) hP)
    calc
      _ = |t| ^ p * (c *
          (‖nodeProduct nodes z s‖ * ‖laplaceAt poweredSeed (s - z)‖)) := by
        simp only [norm_mul, norm_div]
        rfl
      _ ≤ |t| ^ p * (c * ((q ^ (nodes.erase z).card * P) *
          (seventhArm3115 z T ^ 10 / q ^ 70))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmul hc) (by positivity)
      _ = (c * P * seventhArm3115 z T ^ 10 * T ^ p) *
          (q ^ ((nodes.erase z).card + p) / q ^ 70) := by
        rw [← hqt, mul_pow, pow_add]
        ring
      _ ≤ c * P * seventhArm3115 z T ^ 10 * T ^ p :=
        mul_le_of_le_one_right (by positivity) hratio
  calc |t| ^ p * ‖cardinalSum nodes poweredSeed y s‖ ≤
      |t| ^ p * ∑ z ∈ nodes,
        ‖y z / (nodeProduct nodes z z * laplaceAt poweredSeed 0) *
          (nodeProduct nodes z s * laplaceAt poweredSeed (s - z))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le nodes _) (by positivity)
    _ = ∑ z ∈ nodes, |t| ^ p *
        ‖y z / (nodeProduct nodes z z * laplaceAt poweredSeed 0) *
          (nodeProduct nodes z s * laplaceAt poweredSeed (s - z))‖ := Finset.mul_sum ..
    _ ≤ cardinalExteriorBound3115 nodes y T p := Finset.sum_le_sum hterm

theorem normalized_cardinalSum_le_exterior3115
    (nodes : Finset ℂ) (y : ℂ → ℂ) {σ t T : ℝ} (p : ℕ)
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) (hT : 0 < T) (ht : T ≤ |t|)
    (hheight : ∀ z ∈ nodes, |z.im| < T) (hdegree : nodes.card + p ≤ 71) :
    |t / (2 * Real.pi)| ^ p * ‖cardinalSum nodes poweredSeed y
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        cardinalExteriorBound3115 nodes y T p / (2 * Real.pi) ^ p := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  calc
    _ = (|t| ^ p * ‖cardinalSum nodes poweredSeed y
        ((σ : ℂ) + (t : ℂ) * Complex.I)‖) / (2 * Real.pi) ^ p := by
      rw [abs_div, abs_of_pos hpi, div_pow]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (weighted_cardinalSum_le_exterior3115 nodes y p hσ hT ht hheight hdegree)
      (pow_nonneg (le_of_lt hpi) p)

end
end ConnesWeilRH.Source.C1RouteBSplitRungEnvelope3115
