/-
Record 2725, the powered-seed cardinal envelope bridge.

The 2724 seed-object screen showed the wired cardinal pins quantify
`cardinalSum ... (explicitSeed ...)` while every certified strip
constant on the lane (2720 / 2722B / 2722C) was computed for the model
seed `v |-> L(v/2)^10` = Lean `poweredSeed`.  This module re-seeds the
per-node decay envelope on `poweredSeed`: the cardinal sum of the
powered seed over any finite node set is bounded by the exact envelope
shape the 2720 script computes (per-node crude mass arm `E * l1u`, the
per-rung ladder `E * D_k * 2^k / |t - z.im|^k` folded through
`Finset.inf'`, the halved-argument factors of `poweredSeed_laplaceAt`,
and the endpoint maxima `max |a| |1 - a|` that make the bound uniform
in `sigma in [0, 1]`).

Owner chain: `cardinalSum` (2722C:88) at seed `poweredSeed`, y and node
finsets free; the transform facts are `laplaceAt smoothSeed` l1-mass /
derivative-order-L1 bounds (2722A) and `poweredSeed_laplaceAt`
(`C1ExplicitSmoothSeed.lean:148`).

What this is NOT: no hypothesis of the wired row-B contradiction is
removed here (`wired_hypotheses_removed = 0`).  The numeric values of
`l1u` and the ladder `D k` remain named obligations; the companion tie
record re-anchors the 2720 constants in this emitted shape.  No
producer GO, no RH claim, the map-103 freeze is unchanged.
-/
import ConnesWeilRH.Dev.C1StripTransport2722C
import ConnesWeilRH.Dev.C1StripEnvelopeIbpBridge2722
import ConnesWeilRH.Dev.C1ExplicitSmoothSeedMassBudget

namespace ConnesWeilRH.Source

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1ExplicitFiniteNodeCorrection
open C1LaneRD3Root
open C1StripEnvelopeIbpBridge2722
open C1StripTransport2722C
open C1ExplicitSmoothSeed
open scoped BigOperators

noncomputable section

/-! ## The endpoint bound: sigma-uniformity of the exponential factor -/

/-- On `sigma ∈ [0, 1]`, `|sigma - a|` is at most the larger of the two
endpoint values `|a|` and `|1 - a|`; this is the step that makes the
per-node exponential factor `Real.exp |sigma - z.re|` uniform in
`sigma`. -/
theorem abs_sub_le_max_endpoint (a : ℝ) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) : |σ - a| ≤ max |a| |1 - a| := by
  have h1 : 0 ≤ 1 - σ := by linarith [hσ.2]
  have h2 : 0 ≤ σ := hσ.1
  have h3 : σ - a = (1 - σ) * (-a) + σ * (1 - a) := by ring
  calc |σ - a| = |(1 - σ) * (-a) + σ * (1 - a)| := by rw [h3]
    _ ≤ |(1 - σ) * (-a)| + |σ * (1 - a)| := abs_add_le _ _
    _ = (1 - σ) * |a| + σ * |1 - a| := by
        rw [abs_mul, abs_neg, abs_of_nonneg h1, abs_mul, abs_of_nonneg h2]
    _ ≤ (1 - σ) * max |a| |1 - a| + σ * max |a| |1 - a| :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) h1)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) h2)
    _ = max |a| |1 - a| := by ring

/-! ## The per-factor modulus bound -/

/-- The modulus of a single node factor `w - s` is bounded by
`sqrt (Ds^2 + (s.im - w.im)^2)` as soon as the real parts differ by at
most `Ds`; the mixed square is assembled from `Complex.sq_norm` and the
coordinate square bound. -/
theorem norm_sub_node_le_sqrt (w s : ℂ) {Ds : ℝ}
    (hDs : |w.re - s.re| ≤ Ds) :
    ‖w - s‖ ≤ Real.sqrt (Ds ^ 2 + (s.im - w.im) ^ 2) := by
  have hns : ‖w - s‖ ^ 2 = (w.re - s.re) ^ 2 + (w.im - s.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    ring
  have hsq : (w.re - s.re) ^ 2 ≤ Ds ^ 2 := by
    calc (w.re - s.re) ^ 2 = |w.re - s.re| ^ 2 := by rw [sq_abs]
      _ ≤ Ds ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hDs 2
  calc ‖w - s‖ = Real.sqrt (‖w - s‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (Ds ^ 2 + (s.im - w.im) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [hns]
        have him : (w.im - s.im) ^ 2 = (s.im - w.im) ^ 2 := by ring
        linarith [hsq, him]

/-! ## The node-product bound -/

/-- `nodeProduct nodes z s` (the product of `t - s` over the other
nodes) is bounded by the product of per-node moduli, via the list
product bridge `Finset.prod_map_val`. -/
theorem norm_nodeProduct_le (nodes : Finset ℂ) (z s : ℂ) (M : ℂ → ℝ)
    (hM : ∀ w ∈ nodes.erase z, ‖w - s‖ ≤ M w) :
    ‖nodeProduct nodes z s‖ ≤ ∏ w ∈ nodes.erase z, M w := by
  have hbridge : ((nodes.erase z).toList.map (fun w => ‖w - s‖)).prod =
      ∏ w ∈ nodes.erase z, ‖w - s‖ := by
    rw [← Multiset.prod_coe (List.map (fun w => ‖w - s‖) (nodes.erase z).toList),
      ← Multiset.map_coe (fun w => ‖w - s‖) ((nodes.erase z).toList),
      Finset.coe_toList]
    exact Finset.prod_map_val (nodes.erase z) (fun w => ‖w - s‖)
  unfold nodeProduct
  calc ‖((nodes.erase z).toList.map (fun t => t - s)).prod‖
      ≤ (((nodes.erase z).toList.map (fun t => t - s)).map norm).prod :=
        List.norm_prod_le _
    _ = ((nodes.erase z).toList.map (fun w => ‖w - s‖)).prod := by
        rw [List.map_map]
        rfl
    _ = ∏ w ∈ nodes.erase z, ‖w - s‖ := hbridge
    _ ≤ ∏ w ∈ nodes.erase z, M w :=
        Finset.prod_le_prod (fun w _ => norm_nonneg _) (fun w hw => hM w hw)

/-! ## The two transform arms of the smooth seed -/

/-- Crude arm: the l1-mass bound of the transform, at an upper bound
`l1u >= l1Mass smoothSeed` (the Lean-proven `smoothSeed_l1Mass_le_four`
supplies `l1u = 4`; the exact seed mass `3` is a separate numeric
obligation). -/
theorem norm_laplaceAt_smoothSeed_le_mass {l1u : ℝ}
    (hl1 : l1Mass smoothSeed ≤ l1u) (v : ℂ) :
    ‖laplaceAt smoothSeed v‖ ≤ Real.exp (|v.re| * 2) * l1u := by
  have hsupp : Function.support smoothSeed.test ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro x hx
    have h := smoothSeed_support_subset_Ioo hx
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  calc ‖laplaceAt smoothSeed v‖
      ≤ Real.exp (|v.re| * 2) * l1Mass smoothSeed :=
        norm_laplaceAt_le_exp_mul_l1Mass smoothSeed 2 hsupp v
    _ ≤ Real.exp (|v.re| * 2) * l1u :=
        mul_le_mul_of_nonneg_left hl1 (Real.exp_nonneg _)

/-- Rung arm: the order-`k` transform decay, from the derivative-order-L1
bound `derivOrderL1 k smoothSeed <= Dk` (record 2722A shape) divided by
`|v.im|^k`. -/
theorem norm_laplaceAt_smoothSeed_le_rung {k : ℕ} {Dk : ℝ}
    (hD : derivOrderL1 k smoothSeed ≤ Dk) {v : ℂ} (hv : v.im ≠ 0) :
    ‖laplaceAt smoothSeed v‖ ≤ Real.exp (|v.re| * 2) * (Dk / |v.im| ^ k) := by
  have hsupp : Function.support smoothSeed.test ⊆ Set.Icc (-2 : ℝ) 2 := by
    intro x hx
    have h := smoothSeed_support_subset_Ioo hx
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hcomm := norm_pow_laplaceAt_le_exp_mul_derivOrderL1 k smoothSeed 2
    hsupp v
  have h1 : Real.exp (|v.re| * 2) * derivOrderL1 k smoothSeed ≤
      Real.exp (|v.re| * 2) * Dk :=
    mul_le_mul_of_nonneg_left hD (Real.exp_nonneg _)
  have h2 : |v.im| ^ k ≤ ‖v‖ ^ k :=
    pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm v) k
  have hmain : |v.im| ^ k * ‖laplaceAt smoothSeed v‖ ≤
      Real.exp (|v.re| * 2) * Dk :=
    (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans (hcomm.trans h1)
  have hpos : 0 < |v.im| ^ k := pow_pos (abs_pos.mpr hv) k
  have hdiv : ‖laplaceAt smoothSeed v‖ ≤
      Real.exp (|v.re| * 2) * Dk / |v.im| ^ k := by
    refine (le_div_iff₀ hpos).mpr ?_
    rw [mul_comm ‖laplaceAt smoothSeed v‖ (|v.im| ^ k)]
    exact hmain
  calc ‖laplaceAt smoothSeed v‖
      ≤ Real.exp (|v.re| * 2) * Dk / |v.im| ^ k := hdiv
    _ = Real.exp (|v.re| * 2) * (Dk / |v.im| ^ k) := by ring

/-! ## Coordinates of the halved shift (the `poweredSeed` exponent) -/

/-- Imaginary coordinate of the halved shift `(1/2) * (s - z)`. -/
theorem halved_im_eq (z s : ℂ) :
    ((1 / 2 : ℂ) * (s - z)).im = (s.im - z.im) / 2 := by
  rw [show ((1 / 2 : ℂ)) = Complex.ofReal ((1 / 2 : ℝ)) from by norm_num]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, zero_mul, add_zero]
  ring

/-- Real coordinate magnitude of the halved shift, in the form needed by
the exponential factor: `|Re v| * 2 = |s.re - z.re|`. -/
theorem halved_re_abs (z s : ℂ) :
    |((1 / 2 : ℂ) * (s - z)).re| * 2 = |s.re - z.re| := by
  rw [show ((1 / 2 : ℂ) * (s - z)).re = (s.re - z.re) / 2 from by
    rw [show ((1 / 2 : ℂ)) = Complex.ofReal ((1 / 2 : ℝ)) from by norm_num]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, zero_mul, sub_zero]
    ring]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  ring

/-- The rung denominator books the halving as the exact factor `2^k`:
`Dk / |v.im|^k = Dk * 2^k / |s.im - z.im|^k`; the identity holds
unconditionally, `Dk` and `k` free. -/
theorem rung_div_eq (z s : ℂ) (k : ℕ) (Dk : ℝ) :
    Dk / |((1 / 2 : ℂ) * (s - z)).im| ^ k =
      Dk * (2 : ℝ) ^ k / |s.im - z.im| ^ k := by
  rw [show ((1 / 2 : ℂ) * (s - z)).im = (s.im - z.im) / 2 from by
    rw [show ((1 / 2 : ℂ)) = Complex.ofReal ((1 / 2 : ℝ)) from by norm_num]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, zero_mul, add_zero]
    ring]
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_pow]
  field_simp

/-! ## The per-node powered-seed envelope -/

/-- Per-node supplier: the powered seed's transform at the shifted
argument `s - z` is bounded by the tenth power of the envelope the 2720
script computes.  On the node height (`s.im = z.im`) the rung ladder is
undefined and the crude mass arm governs; off it, the envelope is the
minimum of the crude arm and the ladder `inf'` over `rungs`. -/
theorem norm_laplaceAt_poweredSeed_sub_le_ladder (z s : ℂ)
    {l1u : ℝ} (h1 : l1Mass smoothSeed ≤ l1u)
    {rungs : Finset ℕ} (hne : rungs.Nonempty) {D : ℕ → ℝ}
    (hD : ∀ k ∈ rungs, derivOrderL1 k smoothSeed ≤ D k) :
    ‖laplaceAt poweredSeed (s - z)‖ ≤
      (if s.im = z.im then Real.exp |s.re - z.re| * l1u
        else min (Real.exp |s.re - z.re| * l1u)
          (rungs.inf' hne (fun k => Real.exp |s.re - z.re| *
            (D k * (2 : ℝ) ^ k / |s.im - z.im| ^ k)))) ^ 10 := by
  rw [poweredSeed_laplaceAt, norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  by_cases h : s.im = z.im
  · rw [if_pos h]
    have hA := norm_laplaceAt_smoothSeed_le_mass h1
      ((1 / 2 : ℂ) * (s - z))
    rwa [halved_re_abs z s] at hA
  · have hv : ((1 / 2 : ℂ) * (s - z)).im ≠ 0 := by
      rw [halved_im_eq z s]
      exact div_ne_zero (sub_ne_zero.mpr h) (by norm_num)
    rw [if_neg h]
    refine le_min ?_ ?_
    · have hA := norm_laplaceAt_smoothSeed_le_mass h1
        ((1 / 2 : ℂ) * (s - z))
      rwa [halved_re_abs z s] at hA
    · refine Finset.le_inf' hne (fun k => Real.exp |s.re - z.re| *
        (D k * (2 : ℝ) ^ k / |s.im - z.im| ^ k)) ?_
      intro k hk
      have hB := norm_laplaceAt_smoothSeed_le_rung (hD k hk) hv
      rw [halved_re_abs z s] at hB
      rwa [rung_div_eq z s k (D k)] at hB

/-! ## Endpoint-max monotonicity of the envelope -/

/-- The envelope is nonnegative whenever its crude constant and ladder
values are. -/
theorem ladderEnv_nonneg {l1u : ℝ} (h1n : 0 ≤ l1u) {rungs : Finset ℕ}
    (hne : rungs.Nonempty) {D : ℕ → ℝ} (hDn : ∀ k ∈ rungs, 0 ≤ D k)
    (Eσ : ℝ) (hEσ : 0 ≤ Eσ) (t zim : ℝ) :
    0 ≤ if t = zim then Eσ * l1u
      else min (Eσ * l1u) (rungs.inf' hne (fun k =>
        Eσ * (D k * (2 : ℝ) ^ k / |t - zim| ^ k))) := by
  have harms : ∀ k ∈ rungs, 0 ≤ D k * (2 : ℝ) ^ k / |t - zim| ^ k := by
    intro k hk
    exact div_nonneg (mul_nonneg (hDn k hk) (pow_nonneg (by norm_num) k))
      (pow_nonneg (abs_nonneg _) k)
  by_cases h : t = zim
  · rw [if_pos h]
    exact mul_nonneg hEσ h1n
  · rw [if_neg h]
    refine le_min (mul_nonneg hEσ h1n) ?_
    refine Finset.le_inf' hne (fun k =>
      Eσ * (D k * (2 : ℝ) ^ k / |t - zim| ^ k)) ?_
    intro k hk
    exact mul_nonneg hEσ (harms k hk)

/-- The envelope is monotone in the exponential constant `Eσ` (used to
replace `Real.exp |sigma - z.re|` by its endpoint maximum over
`sigma ∈ [0, 1]`). -/
theorem ladderEnv_le {l1u : ℝ} (h1n : 0 ≤ l1u) {rungs : Finset ℕ}
    (hne : rungs.Nonempty) {D : ℕ → ℝ} (hDn : ∀ k ∈ rungs, 0 ≤ D k)
    (Eσ Emax : ℝ) (hEmax : Eσ ≤ Emax) (t zim : ℝ) :
    (if t = zim then Eσ * l1u
        else min (Eσ * l1u) (rungs.inf' hne (fun k =>
          Eσ * (D k * (2 : ℝ) ^ k / |t - zim| ^ k)))) ≤
      (if t = zim then Emax * l1u
        else min (Emax * l1u) (rungs.inf' hne (fun k =>
          Emax * (D k * (2 : ℝ) ^ k / |t - zim| ^ k)))) := by
  have harms : ∀ k ∈ rungs, 0 ≤ D k * (2 : ℝ) ^ k / |t - zim| ^ k := by
    intro k hk
    exact div_nonneg (mul_nonneg (hDn k hk) (pow_nonneg (by norm_num) k))
      (pow_nonneg (abs_nonneg _) k)
  by_cases h : t = zim
  · rw [if_pos h, if_pos h]
    exact mul_le_mul_of_nonneg_right hEmax h1n
  · rw [if_neg h, if_neg h]
    refine le_min (le_trans (min_le_left _ _)
      (mul_le_mul_of_nonneg_right hEmax h1n)) ?_
    refine le_trans (min_le_right _ _) ?_
    refine Finset.le_inf' hne (fun k =>
      Emax * (D k * (2 : ℝ) ^ k / |t - zim| ^ k)) ?_
    intro k hk
    exact le_trans
      (Finset.inf'_le (fun k => Eσ * (D k * (2 : ℝ) ^ k / |t - zim| ^ k)) hk)
      (mul_le_mul_of_nonneg_right hEmax (harms k hk))

/-! ## The cardinal-sum envelope on the strip -/

/-- Main theorem: the cardinal sum of the powered seed at
`sigma + t * I`, `sigma ∈ [0, 1]`, is bounded by the sum of the per-node
coeffied envelope — the `nodeProduct` modulus bound, the endpoint-max
ladder envelope to the tenth power, and the true seed normalization
`‖laplaceAt poweredSeed 0‖`.  Both the `l1u` and the ladder `D` stay
explicit; no numeric instantiation is performed here. -/
theorem norm_cardinalSum_poweredSeed_le_endpoint_env (nodes : Finset ℂ)
    (y : ℂ → ℂ) {l1u : ℝ} (h1 : l1Mass smoothSeed ≤ l1u)
    (h1n : 0 ≤ l1u) {rungs : Finset ℕ} (hne : rungs.Nonempty)
    {D : ℕ → ℝ} (hD : ∀ k ∈ rungs, derivOrderL1 k smoothSeed ≤ D k)
    (hDn : ∀ k ∈ rungs, 0 ≤ D k) {σ t : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) :
    ‖cardinalSum nodes poweredSeed y ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ∑ z ∈ nodes,
        ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
        (∏ w ∈ nodes.erase z,
          Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) *
        (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * l1u
          else min (Real.exp (max |z.re| |1 - z.re|) * l1u)
            (rungs.inf' hne (fun k =>
              Real.exp (max |z.re| |1 - z.re|) *
                (D k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10 := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by rw [hs, re_ofReal_add_mul_I]
  have hsim : s.im = t := by rw [hs, im_ofReal_add_mul_I]
  have hterm : ∀ z ∈ nodes,
      ‖y z / (nodeProduct nodes z z * laplaceAt poweredSeed 0) *
          (nodeProduct nodes z s * laplaceAt poweredSeed (s - z))‖ ≤
      ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
        (∏ w ∈ nodes.erase z,
          Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) *
        (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * l1u
          else min (Real.exp (max |z.re| |1 - z.re|) * l1u)
            (rungs.inf' hne (fun k =>
              Real.exp (max |z.re| |1 - z.re|) *
                (D k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10 := by
    intro z hz
    have hMQ : ‖nodeProduct nodes z s‖ ≤ ∏ w ∈ nodes.erase z,
        Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2) := by
      refine norm_nodeProduct_le nodes z s (fun w =>
        Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) ?_
      intro w hw
      have hDs : |w.re - s.re| ≤ max |w.re| |1 - w.re| := by
        rw [hsre]
        have h := abs_sub_le_max_endpoint w.re hσ
        rwa [abs_sub_comm] at h
      have hs' := norm_sub_node_le_sqrt w s hDs
      rwa [hsim] at hs'
    have hnode := norm_laplaceAt_poweredSeed_sub_le_ladder z s h1 hne hD
    rw [hsre, hsim] at hnode
    have hnn : 0 ≤ if t = z.im then Real.exp |σ - z.re| * l1u
        else min (Real.exp |σ - z.re| * l1u) (rungs.inf' hne (fun k =>
          Real.exp |σ - z.re| * (D k * (2 : ℝ) ^ k / |t - z.im| ^ k))) :=
      ladderEnv_nonneg h1n hne hDn (Real.exp |σ - z.re|)
        (Real.exp_nonneg _) t z.im
    have hEmax : Real.exp |σ - z.re| ≤ Real.exp (max |z.re| |1 - z.re|) :=
      Real.exp_le_exp.mpr (abs_sub_le_max_endpoint z.re hσ)
    have hle := ladderEnv_le h1n hne hDn (Real.exp |σ - z.re|)
      (Real.exp (max |z.re| |1 - z.re|)) hEmax t z.im
    have hL : ‖laplaceAt poweredSeed (s - z)‖ ≤
        (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * l1u
          else min (Real.exp (max |z.re| |1 - z.re|) * l1u)
            (rungs.inf' hne (fun k =>
              Real.exp (max |z.re| |1 - z.re|) *
                (D k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10 :=
      le_trans hnode (pow_le_pow_left₀ hnn hle 10)
    calc ‖y z / (nodeProduct nodes z z * laplaceAt poweredSeed 0) *
            (nodeProduct nodes z s * laplaceAt poweredSeed (s - z))‖
        = ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
            (‖nodeProduct nodes z s‖ * ‖laplaceAt poweredSeed (s - z)‖) := by
          simp only [norm_mul, norm_div]
      _ ≤ ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
            ((∏ w ∈ nodes.erase z,
              Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) *
            (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * l1u
              else min (Real.exp (max |z.re| |1 - z.re|) * l1u)
                (rungs.inf' hne (fun k =>
                  Real.exp (max |z.re| |1 - z.re|) *
                    (D k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hMQ hL (norm_nonneg _)
              (Finset.prod_nonneg (fun w _ => Real.sqrt_nonneg _)))
            (div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _)
              (norm_nonneg _)))
      _ = ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
            (∏ w ∈ nodes.erase z,
              Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) *
            (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * l1u
              else min (Real.exp (max |z.re| |1 - z.re|) * l1u)
                (rungs.inf' hne (fun k =>
                  Real.exp (max |z.re| |1 - z.re|) *
                    (D k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10 := by
          ring
  calc ‖cardinalSum nodes poweredSeed y s‖
      ≤ ∑ z ∈ nodes,
          ‖y z / (nodeProduct nodes z z * laplaceAt poweredSeed 0) *
            (nodeProduct nodes z s * laplaceAt poweredSeed (s - z))‖ :=
        norm_sum_le nodes _
    _ ≤ ∑ z ∈ nodes,
        ‖y z‖ / (‖nodeProduct nodes z z‖ * ‖laplaceAt poweredSeed 0‖) *
        (∏ w ∈ nodes.erase z,
          Real.sqrt ((max |w.re| |1 - w.re|) ^ 2 + (t - w.im) ^ 2)) *
        (if t = z.im then Real.exp (max |z.re| |1 - z.re|) * l1u
          else min (Real.exp (max |z.re| |1 - z.re|) * l1u)
            (rungs.inf' hne (fun k =>
              Real.exp (max |z.re| |1 - z.re|) *
                (D k * (2 : ℝ) ^ k / |t - z.im| ^ k)))) ^ 10 :=
        Finset.sum_le_sum hterm

end

end ConnesWeilRH.Source
