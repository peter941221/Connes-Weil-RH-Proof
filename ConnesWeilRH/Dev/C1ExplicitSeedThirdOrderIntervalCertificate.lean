import ConnesWeilRH.Dev.C1ExplicitSeedThirdOrderComparison

/-!
# The third-order interval certificate: a rational bracket on the third rung

Record 1975 reduced the uniqueness of the interior zero `x*` of `T'''` on the
left half to ONE explicit comparison: on `0 < s < 1` the sign of the committed
third-order bracket along the logistic curve is the sign of
`u - thirdOrderThreshold s`.  This file closes that comparison by a finite
rational certificate and reads off a certified rational bracket on the third
rung of the seed ladder.

The certificate has four layers.

* **The exp machinery** (`expTaylor`, `expTail`, sections 1--3): the order-20
  Taylor polynomial of `exp` with the Lagrange tail bound on `[0, 1]`, giving
  certified rational two-sided bounds for `e^w` (`exp_bounds_pow`), hence for
  the logistic value `seedU` via `seedExpLo`/`seedExpHi`, `seedULo`/`seedUHi`.
* **The bracket enclosure** (sections 4--7): on a window `[a, b]` with
  `a < b` and a rational sandwich `uL <= u <= uH` along the curve, the
  committed bracket is enclosed by `seedBracketLower a b uL uH` and
  `seedBracketUpper a b uL uH` (`seedBracket_mem_Icc`), via the coefficient
  monotonicity of `thirdOrderLeading`/`thirdOrderMiddle`.
* **The partition and the straddle** (sections 7--11): 37 rational pieces
  `L01--L22` (negative) and `R01--R15` (positive) cover `[0, 11/20]` and
  `[23/40, 1]`; on the straddle `[11/20, 23/40]` the derivative of the bracket
  along the curve is bounded below by the explicit positive constant
  `seedHprimeLower`, so the bracket is strictly monotone there and the crossing
  is unique (`existsUnique_seedBracket_eq_zero`), straddled by the rational
  points `s_d = 5634883/10^7` and `s_c = 1408721/2500000`.
* **The rung** (sections 12--13): the sign transfer to `T'''` and the two
  proper-integral evaluations around the crossing give
  `derivOrderL1 3 smoothSeed` between `787283384/10^7` and `787283385/10^7`,
  i.e. `8 * T'' x*` to within `1e-7`.
-/

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1LaneRD3Root
open ConnesWeilRH.Source.C1ExplicitSmoothSeed
open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection
open Real
open expNegInvGlue

noncomputable section

open scoped Topology

/-! ## 1. Rational exp enclosures at fixed order -/

/-- The order-20 Taylor polynomial of `exp`. -/
noncomputable def expTaylor (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 20, y ^ i / (i.factorial : ℝ)

/-- The order-20 Lagrange tail bound of `exp` on `[0, 1]`. -/
noncomputable def expTail (y : ℝ) : ℝ :=
  y ^ 20 * ((20 : ℝ) + 1) / (((20 : ℕ).factorial : ℝ) * 20)

theorem expTaylor_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ expTaylor y := by
  rw [expTaylor]
  exact Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg hy i) (by positivity)

theorem one_le_expTaylor {y : ℝ} (hy : 0 ≤ y) : 1 ≤ expTaylor y := by
  rw [expTaylor]
  have h0 : (0 : ℝ) ≤ y ^ 0 / ((0 : ℕ).factorial : ℝ) := by norm_num
  have hmem : 0 ∈ Finset.range 20 := Finset.mem_range.mpr (by norm_num)
  have hle := Finset.single_le_sum
    (f := fun i : ℕ => y ^ i / (i.factorial : ℝ))
    (fun i _ => div_nonneg (pow_nonneg hy i) (by positivity)) hmem
  simpa using hle

theorem expTail_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ expTail y := by
  rw [expTail]
  exact div_nonneg (mul_nonneg (pow_nonneg hy 20) (by norm_num)) (by norm_num)

theorem expTail_le_one {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) : expTail y ≤ 1 := by
  rw [expTail]
  have h20 : y ^ 20 ≤ 1 := pow_le_one₀ (n := 20) hy0 hy
  have hden : (0 : ℝ) < (((20 : ℕ).factorial : ℝ)) * 20 := by norm_num
  rw [div_le_one hden]
  have h21 : (21 : ℝ) ≤ (((20 : ℕ).factorial : ℝ)) * 20 := by norm_num
  nlinarith [h20, h21]

theorem sum_le_exp_20 {y : ℝ} (hy : 0 ≤ y) : expTaylor y ≤ Real.exp y := by
  rw [expTaylor]
  exact Real.sum_le_exp_of_nonneg hy 20

theorem exp_le_sum_add {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y ≤ expTaylor y + expTail y := by
  rw [expTaylor, expTail]
  exact Real.exp_bound' hy0 hy1 (by norm_num)

/-- The two leading Taylor terms already give `1 + y`. -/
theorem one_add_le_expTaylor {y : ℝ} (hy : 0 ≤ y) : 1 + y ≤ expTaylor y := by
  rw [expTaylor]
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range 20 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h
    · rw [h]
      exact Finset.mem_range.mpr (by norm_num)
    · rw [h]
      exact Finset.mem_range.mpr (by norm_num)
  have hf : ∀ x ∈ Finset.range 20, x ∉ ({0, 1} : Finset ℕ) →
      0 ≤ y ^ x / (x.factorial : ℝ) := fun x _ _ =>
    div_nonneg (pow_nonneg hy x) (by positivity)
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun x : ℕ => y ^ x / (x.factorial : ℝ)) hsub hf
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at h
  have e0 : y ^ 0 / ((0 : ℕ).factorial : ℝ) = 1 := by norm_num
  have e1 : y ^ 1 / ((1 : ℕ).factorial : ℝ) = y := by norm_num
  rw [e0, e1] at h
  exact h

/-- The Lagrange tail is dominated by the linear term on `[0, 1]`. -/
theorem expTail_le_self {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : expTail y ≤ y := by
  rw [expTail]
  have hden : (0 : ℝ) < (((20 : ℕ).factorial : ℝ)) * 20 := by norm_num
  rw [div_le_iff₀ hden]
  have h19 : y ^ 19 ≤ 1 := pow_le_one₀ (n := 19) hy0 hy1
  have hmul : y * y ^ 19 ≤ y * 1 := mul_le_mul_of_nonneg_left h19 hy0
  have hpow : y ^ 20 = y * y ^ 19 := by ring
  have hc : (21 : ℝ) ≤ (((20 : ℕ).factorial : ℝ)) * 20 := by norm_num
  rw [hpow]
  nlinarith [hmul, hc, hy0]

/-- The certified lower exponential factor is at least one. -/
theorem one_le_expTaylor_sub_expTail {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 ≤ expTaylor y - expTail y := by
  have h1 := one_add_le_expTaylor hy0
  have h2 := expTail_le_self hy0 hy1
  linarith

/-- The two-sided order-20 enclosure of `exp w` through the `m`-th power of the
enclosure of `exp (w / m)`; the hypothesis `w ≤ m` keeps the Taylor argument in
`[0, 1]`. -/
theorem exp_bounds_pow {w : ℝ} (h0 : 0 ≤ w) {m : ℕ} (hm : 1 ≤ m) (hmw : w ≤ m) :
    (expTaylor (w / m) - expTail (w / m)) ^ m ≤ Real.exp w ∧
      Real.exp w ≤ (expTaylor (w / m) + expTail (w / m)) ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 ≤ w / m := div_nonneg h0 (le_of_lt hm0)
  have hy1 : w / m ≤ 1 := by
    rw [div_le_iff₀ hm0]
    simpa using hmw
  have hmul : (m : ℝ) * (w / m) = w := by
    rw [mul_comm]
    exact div_mul_cancel₀ w (ne_of_gt hm0)
  have hlo : expTaylor (w / m) - expTail (w / m) ≤ Real.exp (w / m) := by
    have h1 := sum_le_exp_20 hy0
    have h2 := expTail_nonneg hy0
    linarith
  have hhi : Real.exp (w / m) ≤ expTaylor (w / m) + expTail (w / m) :=
    exp_le_sum_add hy0 hy1
  have hlo0 : 0 ≤ expTaylor (w / m) - expTail (w / m) := by
    have h1 := one_le_expTaylor hy0
    have h2 := expTail_le_one hy0 hy1
    linarith
  constructor
  · calc (expTaylor (w / m) - expTail (w / m)) ^ m
        ≤ (Real.exp (w / m)) ^ m := pow_le_pow_left₀ hlo0 hlo m
      _ = Real.exp ((m : ℝ) * (w / m)) := (Real.exp_nat_mul (w / m) m).symm
      _ = Real.exp w := by rw [hmul]
  · calc Real.exp w = Real.exp ((m : ℝ) * (w / m)) := by rw [hmul]
      _ = (Real.exp (w / m)) ^ m := Real.exp_nat_mul (w / m) m
      _ ≤ (expTaylor (w / m) + expTail (w / m)) ^ m :=
          pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hhi m

/-! ## 2. The logistic variable in the half-width coordinate -/

/-- The half-width coordinate exponential argument `v s = 4 s / (1 - s^2)`. -/
noncomputable def seedV (s : ℝ) : ℝ := 4 * s / (1 - s ^ 2)

/-- The logistic variable `u s = (exp (v s) - 1) / (exp (v s) + 1)`, equal to
`1 - 2 T ((1 - s) / 2)` on the left half. -/
noncomputable def seedU (s : ℝ) : ℝ := (Real.exp (seedV s) - 1) / (Real.exp (seedV s) + 1)

theorem seedV_pos {s : ℝ} (h0 : 0 < s) (h1 : s < 1) : 0 < seedV s := by
  rw [seedV]
  exact div_pos (by linarith) (by nlinarith)

theorem seedV_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : 0 ≤ seedV s := by
  rw [seedV]
  exact div_nonneg (by linarith) (by nlinarith)

theorem seedV_mono {s t : ℝ} (hs0 : 0 < s) (hst : s ≤ t) (ht1 : t < 1) :
    seedV s ≤ seedV t := by
  rw [seedV, seedV]
  have hs1 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  have ht2 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hs1 ht2]
  have hst0 : (0 : ℝ) ≤ t - s := by linarith
  have hst1 : (0 : ℝ) ≤ 1 + s * t := by nlinarith [mul_pos hs0 (lt_of_lt_of_le hs0 hst)]
  nlinarith [mul_nonneg hst0 hst1]

/-- The membership of `seedU s` in the committed reflected logistic form. -/
theorem seedU_eq_reflect (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    seedU s = 1 - 2 * Real.smoothTransition ((1 - s) / 2) := by
  rw [seedU, seedV]
  exact (one_sub_two_mul_smoothTransition_reflect_eq s h0 h1).symm

/-- The ratio `(a - 1) / (a + 1)` is monotone on the positive half-line. -/
theorem ratio_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (a - 1) / (a + 1) ≤ (b - 1) / (b + 1) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem seedU_le_one (s : ℝ) : seedU s ≤ 1 := by
  rw [seedU]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.exp (seedV s) + 1)]
  linarith

theorem seedU_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) : 0 ≤ seedU s := by
  have hv : 0 ≤ seedV s := seedV_nonneg h0 h1
  have hE : 1 ≤ Real.exp (seedV s) := one_le_exp_iff.mpr hv
  rw [seedU]
  exact div_nonneg (sub_nonneg.mpr hE) (by positivity)

/-- `seedU` is increasing on the open half-width interval. -/
theorem seedU_monoOn_Ioo : MonotoneOn seedU (Set.Ioo 0 1) := by
  intro s hs t ht hst
  rw [seedU, seedU]
  exact ratio_mono (Real.exp_pos _) (Real.exp_le_exp.mpr (seedV_mono hs.1 hst ht.2))

/-- The cheap committed lower bound for the logistic variable. -/
theorem seedULower_cheap {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    seedV s / (seedV s + 2) ≤ seedU s := by
  rw [seedU]
  exact self_div_add_two_le_exp_ratio (seedV s) (le_of_lt (seedV_pos h0 h1))

/-! ## 3. Certified two-sided bounds through the order-20 power enclosure -/

noncomputable def seedExpLo (s : ℝ) (m : ℕ) : ℝ :=
  (expTaylor (seedV s / m) - expTail (seedV s / m)) ^ m

noncomputable def seedExpHi (s : ℝ) (m : ℕ) : ℝ :=
  (expTaylor (seedV s / m) + expTail (seedV s / m)) ^ m

noncomputable def seedULo (s : ℝ) (m : ℕ) : ℝ := (seedExpLo s m - 1) / (seedExpHi s m + 1)

noncomputable def seedUHi (s : ℝ) (m : ℕ) : ℝ := (seedExpHi s m - 1) / (seedExpLo s m + 1)

theorem seedULo_zero (m : ℕ) : seedULo 0 m = 0 := by
  rw [seedULo, seedExpLo, seedExpHi, seedV]
  norm_num [expTaylor, expTail, Finset.sum_range_succ]

/-- The certified two-sided enclosure of the logistic variable at a single
point, from the order-20 power bounds on `exp (seedV s)`. -/
theorem seedU_mem_Icc {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) {m : ℕ} (hm : 1 ≤ m)
    (hmw : seedV s ≤ m) : seedU s ∈ Set.Icc (seedULo s m) (seedUHi s m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hv0 : 0 ≤ seedV s := seedV_nonneg h0 h1
  have hy0 : 0 ≤ seedV s / m := div_nonneg hv0 (le_of_lt hm0)
  have hy1 : seedV s / m ≤ 1 := by
    rw [div_le_iff₀ hm0]
    simpa using hmw
  have hb := exp_bounds_pow (w := seedV s) hv0 hm hmw
  have hlo : seedExpLo s m ≤ Real.exp (seedV s) := hb.1
  have hhi : Real.exp (seedV s) ≤ seedExpHi s m := hb.2
  have hlo1 : 1 ≤ seedExpLo s m := by
    rw [seedExpLo]
    exact one_le_pow₀ (one_le_expTaylor_sub_expTail hy0 hy1)
  have hlo0 : 0 < seedExpLo s m := lt_of_lt_of_le one_pos hlo1
  have hsub : 0 ≤ seedExpLo s m - 1 := by linarith
  constructor
  · calc seedULo s m = (seedExpLo s m - 1) / (seedExpHi s m + 1) := rfl
      _ ≤ (seedExpLo s m - 1) / (seedExpLo s m + 1) :=
          div_le_div_of_nonneg_left hsub (by linarith) (by linarith)
      _ ≤ (Real.exp (seedV s) - 1) / (Real.exp (seedV s) + 1) :=
          ratio_mono hlo0 hlo
      _ = seedU s := by rw [seedU]
  · calc seedU s = (Real.exp (seedV s) - 1) / (Real.exp (seedV s) + 1) := by rw [seedU]
      _ ≤ (seedExpHi s m - 1) / (seedExpHi s m + 1) := ratio_mono (Real.exp_pos _) hhi
      _ ≤ (seedExpHi s m - 1) / (seedExpLo s m + 1) :=
          div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
      _ = seedUHi s m := rfl

theorem seedExpLo_ge_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) {m : ℕ} (hm : 1 ≤ m)
    (hmw : seedV s ≤ m) : 1 ≤ seedExpLo s m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 ≤ seedV s / m := div_nonneg (seedV_nonneg h0 h1) (le_of_lt hm0)
  have hy1 : seedV s / m ≤ 1 := by
    rw [div_le_iff₀ hm0]
    simpa using hmw
  rw [seedExpLo]
  exact one_le_pow₀ (one_le_expTaylor_sub_expTail hy0 hy1)

theorem seedExpHi_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ seedExpHi s m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hy0 : 0 ≤ seedV s / m := div_nonneg (seedV_nonneg h0 h1) (le_of_lt hm0)
  rw [seedExpHi]
  exact pow_nonneg (add_nonneg (expTaylor_nonneg hy0) (expTail_nonneg hy0)) m

/-- The certified lower endpoint of the logistic sandwich is nonnegative. -/
theorem seedULo_nonneg {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) {m : ℕ} (hm : 1 ≤ m)
    (hmw : seedV s ≤ m) : 0 ≤ seedULo s m := by
  have h1' := seedExpLo_ge_one h0 h1 hm hmw
  have h2 := seedExpHi_nonneg h0 h1 hm
  rw [seedULo]
  exact div_nonneg (by linarith) (by linarith)

example : seedULo 0 4 = 0 := seedULo_zero 4


example : (seedUHi (1 / 10) 4 : ℝ) < 1 / 5 := by
  rw [seedUHi, seedExpLo, seedExpHi, seedV]
  norm_num [expTaylor, expTail, Finset.sum_range_succ]


/-! ## 4. Coefficient expansions and interval bounds -/

theorem thirdOrderMiddle_eq_expansion (s : ℝ) :
    thirdOrderMiddle s = 36 * s + 12 * s ^ 3 - 36 * s ^ 5 - 12 * s ^ 7 := by
  unfold thirdOrderMiddle
  ring

theorem thirdOrderConstant_eq_expansion (s : ℝ) :
    thirdOrderConstant s = -1 + 8 * s ^ 6 + 3 * s ^ 8 - 42 * s ^ 4 := by
  unfold thirdOrderConstant
  ring

theorem thirdOrderLeading_le_of_le {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) :
    thirdOrderLeading a ≤ thirdOrderLeading b := by
  have hb0 : 0 ≤ b := le_trans ha0 hab
  have h1 : 1 + a ^ 2 ≤ 1 + b ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (add_nonneg hb0 ha0)]
  have h3 : (1 + a ^ 2) ^ 3 ≤ (1 + b ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  unfold thirdOrderLeading
  exact mul_le_mul_of_nonneg_left h3 (by norm_num)

theorem thirdOrderMiddle_mem_Icc {a b s : ℝ} (ha : 0 ≤ a)
    (hs : s ∈ Set.Icc a b) :
    thirdOrderMiddle s ∈ Set.Icc (36 * a + 12 * a ^ 3 - 36 * b ^ 5 - 12 * b ^ 7)
      (36 * b + 12 * b ^ 3 - 36 * a ^ 5 - 12 * a ^ 7) := by
  have hs0 : 0 ≤ s := le_trans ha hs.1
  have hs1 : a ≤ s := hs.1
  have hs2 : s ≤ b := hs.2
  rw [thirdOrderMiddle_eq_expansion]
  constructor
  · have e3 : a ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ ha hs1 3
    have e5 : s ^ 5 ≤ b ^ 5 := pow_le_pow_left₀ hs0 hs2 5
    have e7 : s ^ 7 ≤ b ^ 7 := pow_le_pow_left₀ hs0 hs2 7
    linarith
  · have e3 : s ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ hs0 hs2 3
    have e5 : a ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ ha hs1 5
    have e7 : a ^ 7 ≤ s ^ 7 := pow_le_pow_left₀ ha hs1 7
    linarith

theorem thirdOrderConstant_mem_Icc {a b s : ℝ} (ha : 0 ≤ a)
    (hs : s ∈ Set.Icc a b) :
    thirdOrderConstant s ∈ Set.Icc (-1 + 8 * a ^ 6 + 3 * a ^ 8 - 42 * b ^ 4)
      (-1 + 8 * b ^ 6 + 3 * b ^ 8 - 42 * a ^ 4) := by
  have hs0 : 0 ≤ s := le_trans ha hs.1
  have hs1 : a ≤ s := hs.1
  have hs2 : s ≤ b := hs.2
  rw [thirdOrderConstant_eq_expansion]
  constructor
  · have e4 : s ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ hs0 hs2 4
    have e6 : a ^ 6 ≤ s ^ 6 := pow_le_pow_left₀ ha hs1 6
    have e8 : a ^ 8 ≤ s ^ 8 := pow_le_pow_left₀ ha hs1 8
    linarith
  · have e4 : a ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ ha hs1 4
    have e6 : s ^ 6 ≤ b ^ 6 := pow_le_pow_left₀ hs0 hs2 6
    have e8 : s ^ 8 ≤ b ^ 8 := pow_le_pow_left₀ hs0 hs2 8
    linarith

/-! ## 5. The bracket enclosure master lemma -/

/-- The third-order bracket along the logistic variable. -/
noncomputable def seedBracket (s : ℝ) : ℝ := thirdOrderBracket s (seedU s)

/-- The certified lower enclosure of the bracket on `[a, b]`. -/
noncomputable def seedBracketLower (a b uL uH : ℝ) : ℝ :=
  thirdOrderLeading a * uL ^ 2 -
      (36 * b + 12 * b ^ 3 - 36 * a ^ 5 - 12 * a ^ 7) * uH +
    (-1 + 8 * a ^ 6 + 3 * a ^ 8 - 42 * b ^ 4)

/-- The certified upper enclosure of the bracket on `[a, b]`. -/
noncomputable def seedBracketUpper (a b uL uH : ℝ) : ℝ :=
  thirdOrderLeading b * uH ^ 2 -
      (36 * a + 12 * a ^ 3 - 36 * b ^ 5 - 12 * b ^ 7) * uL +
    (-1 + 8 * b ^ 6 + 3 * b ^ 8 - 42 * a ^ 4)

theorem seedBracket_mem_Icc {a b uL uH s : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hs : s ∈ Set.Icc a b) (huL0 : 0 ≤ uL) (huL : uL ≤ seedU s) (huH : seedU s ≤ uH) :
    seedBracket s ∈ Set.Icc (seedBracketLower a b uL uH) (seedBracketUpper a b uL uH) := by
  have hs0 : 0 ≤ s := le_trans ha hs.1
  have hs1 : s ≤ 1 := le_trans hs.2 hb
  have hmid := thirdOrderMiddle_mem_Icc (b := b) ha hs
  have hcon := thirdOrderConstant_mem_Icc (b := b) ha hs
  have hlead1 : thirdOrderLeading a ≤ thirdOrderLeading s :=
    thirdOrderLeading_le_of_le ha hs.1
  have hlead2 : thirdOrderLeading s ≤ thirdOrderLeading b :=
    thirdOrderLeading_le_of_le hs0 hs.2
  have hu0 : 0 ≤ seedU s := le_trans huL0 huL
  have hu2lo : uL ^ 2 ≤ seedU s ^ 2 := pow_le_pow_left₀ huL0 huL 2
  have hu2hi : seedU s ^ 2 ≤ uH ^ 2 := pow_le_pow_left₀ hu0 huH 2
  have hlead0 : 0 ≤ thirdOrderLeading a := le_of_lt (thirdOrderLeading_pos a)
  have hmid0 : 0 ≤ thirdOrderMiddle s := thirdOrderMiddle_nonneg hs0 hs1
  have hmidhi0 : 0 ≤ 36 * b + 12 * b ^ 3 - 36 * a ^ 5 - 12 * a ^ 7 := le_trans hmid0 hmid.2
  constructor
  · have h1 : thirdOrderLeading a * uL ^ 2 ≤ thirdOrderLeading s * seedU s ^ 2 :=
      mul_le_mul hlead1 hu2lo (sq_nonneg uL) (le_trans hlead0 hlead1)
    have h2 : thirdOrderMiddle s * seedU s ≤
        (36 * b + 12 * b ^ 3 - 36 * a ^ 5 - 12 * a ^ 7) * uH :=
      mul_le_mul hmid.2 huH hu0 hmidhi0
    have h3 : -1 + 8 * a ^ 6 + 3 * a ^ 8 - 42 * b ^ 4 ≤ thirdOrderConstant s := hcon.1
    calc seedBracketLower a b uL uH
        = thirdOrderLeading a * uL ^ 2 -
            (36 * b + 12 * b ^ 3 - 36 * a ^ 5 - 12 * a ^ 7) * uH +
            (-1 + 8 * a ^ 6 + 3 * a ^ 8 - 42 * b ^ 4) := rfl
      _ ≤ thirdOrderLeading s * seedU s ^ 2 - thirdOrderMiddle s * seedU s +
            thirdOrderConstant s := by linarith
      _ = seedBracket s := by
          rw [seedBracket, thirdOrderBracket_eq_quadratic]
  · have h1 : thirdOrderLeading s * seedU s ^ 2 ≤ thirdOrderLeading b * uH ^ 2 :=
      mul_le_mul hlead2 hu2hi (sq_nonneg (seedU s)) (le_of_lt (thirdOrderLeading_pos b))
    have h2 : (36 * a + 12 * a ^ 3 - 36 * b ^ 5 - 12 * b ^ 7) * uL ≤
        thirdOrderMiddle s * seedU s :=
      mul_le_mul hmid.1 huL huL0 hmid0
    have h3 : thirdOrderConstant s ≤ -1 + 8 * b ^ 6 + 3 * b ^ 8 - 42 * a ^ 4 := hcon.2
    calc seedBracket s
        = thirdOrderLeading s * seedU s ^ 2 - thirdOrderMiddle s * seedU s +
            thirdOrderConstant s := by
          rw [seedBracket, thirdOrderBracket_eq_quadratic]
      _ ≤ seedBracketUpper a b uL uH := by
          rw [seedBracketUpper]
          linarith

/-! ## 6. Sandwiches feeding the master lemma -/

theorem seedU_zero : seedU 0 = 0 := by
  rw [seedU, seedV]
  norm_num

/-- The two-sided certified sandwich on a piece `[a, b]` with `a > 0`, through
the point enclosures at the endpoints and monotonicity. -/
theorem seedU_sandwich_exp {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb : b < 1) {m₁ : ℕ}
    (hm₁ : 1 ≤ m₁) (hmw₁ : seedV a ≤ m₁) {m₂ : ℕ} (hm₂ : 1 ≤ m₂) (hmw₂ : seedV b ≤ m₂) :
    ∀ s ∈ Set.Icc a b, seedULo a m₁ ≤ seedU s ∧ seedU s ≤ seedUHi b m₂ := by
  have ha1 : a < 1 := lt_of_le_of_lt hab hb
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 hb
  have hsa : seedU a ≤ seedU s := seedU_monoOn_Ioo ⟨ha0, ha1⟩ ⟨hs0, hs1⟩ hs.1
  have hsb : seedU s ≤ seedU b := seedU_monoOn_Ioo ⟨hs0, hs1⟩ ⟨hb0, hb⟩ hs.2
  have hpa := seedU_mem_Icc (s := a) (le_of_lt ha0) ha1 hm₁ hmw₁
  have hpb := seedU_mem_Icc (s := b) (le_of_lt hb0) hb hm₂ hmw₂
  exact ⟨le_trans hpa.1 hsa, le_trans hsb hpb.2⟩

/-- The sandwich on the first piece `[0, b]`: the lower endpoint contributes
exactly zero. -/
theorem seedU_sandwich_zero {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) {m₂ : ℕ} (hm₂ : 1 ≤ m₂)
    (hmw₂ : seedV b ≤ m₂) :
    ∀ s ∈ Set.Icc 0 b, seedULo 0 m₂ ≤ seedU s ∧ seedU s ≤ seedUHi b m₂ := by
  intro s hs
  have hs1 : s < 1 := lt_of_le_of_lt hs.2 hb1
  have hpb := seedU_mem_Icc (s := b) (le_of_lt hb0) hb1 hm₂ hmw₂
  have hbpos : 0 ≤ seedU b := seedU_nonneg (le_of_lt hb0) hb1
  refine ⟨?_, ?_⟩
  · rw [seedULo_zero]
    exact seedU_nonneg hs.1 hs1
  · rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, seedU_zero]
      exact le_trans hbpos hpb.2
    · have hsb : seedU s ≤ seedU b := seedU_monoOn_Ioo ⟨h, hs1⟩ ⟨hb0, hb1⟩ hs.2
      exact le_trans hsb hpb.2



/-- The certified two-sided sandwich on the last piece `[a, 1)`: the upper
bound is the universal `seedU_le_one`. -/
theorem seedU_sandwich_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {m₁ : ℕ} (hm₁ : 1 ≤ m₁)
    (hmw₁ : seedV a ≤ m₁) :
    ∀ s ∈ Set.Ico a 1, seedULo a m₁ ≤ seedU s ∧ seedU s ≤ 1 := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
  have hs1 : s < 1 := hs.2
  have hsa : seedU a ≤ seedU s := seedU_monoOn_Ioo ⟨ha0, ha1⟩ ⟨hs0, hs1⟩ hs.1
  have hpa := seedU_mem_Icc (s := a) (le_of_lt ha0) ha1 hm₁ hmw₁
  exact ⟨le_trans hpa.1 hsa, seedU_le_one s⟩

/-! ## 7. The certified partition of `(0, 1)`

On each piece of the left chain the bracket is strictly negative; on each piece
of the right chain it is strictly positive.  The partition is `[0, 11 / 20]`
(22 pieces), the monotone straddle `[11 / 20, 23 / 40]`, and `[23 / 40, 1)`
(15 pieces). -/

theorem seedBracket_neg_L01 {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (1 / 10 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_zero (b := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
    (m₂ := 1) (by norm_num) (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (0 : ℝ)) (b := (1 / 10 : ℝ)) (uL := seedULo 0 1)
    (uH := seedUHi (1 / 10 : ℝ) 1) (by norm_num) (by norm_num) hs
    (by rw [seedULo_zero]) hsand.1 hsand.2
  have hp : seedBracketUpper (0 : ℝ) (1 / 10 : ℝ) (seedULo 0 1) (seedUHi (1 / 10 : ℝ) 1) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L02 {s : ℝ} (hs : s ∈ Set.Icc (1 / 10 : ℝ) (3 / 20 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (1 / 10 : ℝ)) (b := (3 / 20 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 1) (by norm_num) (by norm_num [seedV]) (m₂ := 1) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (1 / 10 : ℝ)) (b := (3 / 20 : ℝ))
    (uL := seedULo (1 / 10 : ℝ) 1)
    (uH := seedUHi (3 / 20 : ℝ) 1) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (1 / 10 : ℝ) (3 / 20 : ℝ) (seedULo (1 / 10 : ℝ) 1)
    (seedUHi (3 / 20 : ℝ) 1) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L03 {s : ℝ} (hs : s ∈ Set.Icc (3 / 20 : ℝ) (1 / 5 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (3 / 20 : ℝ)) (b := (1 / 5 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 1) (by norm_num) (by norm_num [seedV]) (m₂ := 1) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (3 / 20 : ℝ)) (b := (1 / 5 : ℝ))
    (uL := seedULo (3 / 20 : ℝ) 1)
    (uH := seedUHi (1 / 5 : ℝ) 1) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (3 / 20 : ℝ) (1 / 5 : ℝ) (seedULo (3 / 20 : ℝ) 1)
    (seedUHi (1 / 5 : ℝ) 1) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L04 {s : ℝ} (hs : s ∈ Set.Icc (1 / 5 : ℝ) (1 / 4 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (1 / 5 : ℝ)) (b := (1 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 1) (by norm_num) (by norm_num [seedV]) (m₂ := 2) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (1 / 5 : ℝ)) (b := (1 / 4 : ℝ)) (uL := seedULo (1 / 5 : ℝ) 1)
    (uH := seedUHi (1 / 4 : ℝ) 2) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (1 / 5 : ℝ) (1 / 4 : ℝ) (seedULo (1 / 5 : ℝ) 1)
    (seedUHi (1 / 4 : ℝ) 2) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L05 {s : ℝ} (hs : s ∈ Set.Icc (1 / 4 : ℝ) (3 / 10 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (1 / 4 : ℝ)) (b := (3 / 10 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 2) (by norm_num) (by norm_num [seedV]) (m₂ := 2) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (1 / 4 : ℝ)) (b := (3 / 10 : ℝ))
    (uL := seedULo (1 / 4 : ℝ) 2)
    (uH := seedUHi (3 / 10 : ℝ) 2) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (1 / 4 : ℝ) (3 / 10 : ℝ) (seedULo (1 / 4 : ℝ) 2)
    (seedUHi (3 / 10 : ℝ) 2) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L06 {s : ℝ} (hs : s ∈ Set.Icc (3 / 10 : ℝ) (7 / 20 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (3 / 10 : ℝ)) (b := (7 / 20 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 2) (by norm_num) (by norm_num [seedV]) (m₂ := 2) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (3 / 10 : ℝ)) (b := (7 / 20 : ℝ))
    (uL := seedULo (3 / 10 : ℝ) 2)
    (uH := seedUHi (7 / 20 : ℝ) 2) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (3 / 10 : ℝ) (7 / 20 : ℝ) (seedULo (3 / 10 : ℝ) 2)
    (seedUHi (7 / 20 : ℝ) 2) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L07 {s : ℝ} (hs : s ∈ Set.Icc (7 / 20 : ℝ) (37 / 100 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (7 / 20 : ℝ)) (b := (37 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 2) (by norm_num) (by norm_num [seedV]) (m₂ := 2) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (7 / 20 : ℝ)) (b := (37 / 100 : ℝ))
    (uL := seedULo (7 / 20 : ℝ) 2)
    (uH := seedUHi (37 / 100 : ℝ) 2) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (7 / 20 : ℝ) (37 / 100 : ℝ) (seedULo (7 / 20 : ℝ) 2)
    (seedUHi (37 / 100 : ℝ) 2) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L08 {s : ℝ} (hs : s ∈ Set.Icc (37 / 100 : ℝ) (39 / 100 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (37 / 100 : ℝ)) (b := (39 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 2) (by norm_num) (by norm_num [seedV]) (m₂ := 2) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (37 / 100 : ℝ)) (b := (39 / 100 : ℝ))
    (uL := seedULo (37 / 100 : ℝ) 2)
    (uH := seedUHi (39 / 100 : ℝ) 2) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (37 / 100 : ℝ) (39 / 100 : ℝ) (seedULo (37 / 100 : ℝ) 2)
    (seedUHi (39 / 100 : ℝ) 2) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L09 {s : ℝ} (hs : s ∈ Set.Icc (39 / 100 : ℝ) (41 / 100 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (39 / 100 : ℝ)) (b := (41 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 2) (by norm_num) (by norm_num [seedV]) (m₂ := 2) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (39 / 100 : ℝ)) (b := (41 / 100 : ℝ))
    (uL := seedULo (39 / 100 : ℝ) 2)
    (uH := seedUHi (41 / 100 : ℝ) 2) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (39 / 100 : ℝ) (41 / 100 : ℝ) (seedULo (39 / 100 : ℝ) 2)
    (seedUHi (41 / 100 : ℝ) 2) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L10 {s : ℝ} (hs : s ∈ Set.Icc (41 / 100 : ℝ) (43 / 100 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (41 / 100 : ℝ)) (b := (43 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 2) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (41 / 100 : ℝ)) (b := (43 / 100 : ℝ))
    (uL := seedULo (41 / 100 : ℝ) 2)
    (uH := seedUHi (43 / 100 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (41 / 100 : ℝ) (43 / 100 : ℝ) (seedULo (41 / 100 : ℝ) 2)
    (seedUHi (43 / 100 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L11 {s : ℝ} (hs : s ∈ Set.Icc (43 / 100 : ℝ) (9 / 20 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (43 / 100 : ℝ)) (b := (9 / 20 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (43 / 100 : ℝ)) (b := (9 / 20 : ℝ))
    (uL := seedULo (43 / 100 : ℝ) 4)
    (uH := seedUHi (9 / 20 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (43 / 100 : ℝ) (9 / 20 : ℝ) (seedULo (43 / 100 : ℝ) 4)
    (seedUHi (9 / 20 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L12 {s : ℝ} (hs : s ∈ Set.Icc (9 / 20 : ℝ) (47 / 100 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (9 / 20 : ℝ)) (b := (47 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (9 / 20 : ℝ)) (b := (47 / 100 : ℝ))
    (uL := seedULo (9 / 20 : ℝ) 4)
    (uH := seedUHi (47 / 100 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (9 / 20 : ℝ) (47 / 100 : ℝ) (seedULo (9 / 20 : ℝ) 4)
    (seedUHi (47 / 100 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L13 {s : ℝ} (hs : s ∈ Set.Icc (47 / 100 : ℝ) (49 / 100 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (47 / 100 : ℝ)) (b := (49 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (47 / 100 : ℝ)) (b := (49 / 100 : ℝ))
    (uL := seedULo (47 / 100 : ℝ) 4)
    (uH := seedUHi (49 / 100 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (47 / 100 : ℝ) (49 / 100 : ℝ) (seedULo (47 / 100 : ℝ) 4)
    (seedUHi (49 / 100 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L14 {s : ℝ} (hs : s ∈ Set.Icc (49 / 100 : ℝ) (1 / 2 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (49 / 100 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (49 / 100 : ℝ)) (b := (1 / 2 : ℝ))
    (uL := seedULo (49 / 100 : ℝ) 4)
    (uH := seedUHi (1 / 2 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (49 / 100 : ℝ) (1 / 2 : ℝ) (seedULo (49 / 100 : ℝ) 4)
    (seedUHi (1 / 2 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L15 {s : ℝ} (hs : s ∈ Set.Icc (1 / 2 : ℝ) (51 / 100 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (1 / 2 : ℝ)) (b := (51 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (1 / 2 : ℝ)) (b := (51 / 100 : ℝ))
    (uL := seedULo (1 / 2 : ℝ) 4)
    (uH := seedUHi (51 / 100 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (1 / 2 : ℝ) (51 / 100 : ℝ) (seedULo (1 / 2 : ℝ) 4)
    (seedUHi (51 / 100 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L16 {s : ℝ} (hs : s ∈ Set.Icc (51 / 100 : ℝ) (13 / 25 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (51 / 100 : ℝ)) (b := (13 / 25 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (51 / 100 : ℝ)) (b := (13 / 25 : ℝ))
    (uL := seedULo (51 / 100 : ℝ) 4)
    (uH := seedUHi (13 / 25 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (51 / 100 : ℝ) (13 / 25 : ℝ) (seedULo (51 / 100 : ℝ) 4)
    (seedUHi (13 / 25 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L17 {s : ℝ} (hs : s ∈ Set.Icc (13 / 25 : ℝ) (53 / 100 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (13 / 25 : ℝ)) (b := (53 / 100 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (13 / 25 : ℝ)) (b := (53 / 100 : ℝ))
    (uL := seedULo (13 / 25 : ℝ) 4)
    (uH := seedUHi (53 / 100 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (13 / 25 : ℝ) (53 / 100 : ℝ) (seedULo (13 / 25 : ℝ) 4)
    (seedUHi (53 / 100 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L18 {s : ℝ} (hs : s ∈ Set.Icc (53 / 100 : ℝ) (107 / 200 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (53 / 100 : ℝ)) (b := (107 / 200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (53 / 100 : ℝ)) (b := (107 / 200 : ℝ))
    (uL := seedULo (53 / 100 : ℝ) 4)
    (uH := seedUHi (107 / 200 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (53 / 100 : ℝ) (107 / 200 : ℝ) (seedULo (53 / 100 : ℝ) 4)
    (seedUHi (107 / 200 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L19 {s : ℝ} (hs : s ∈ Set.Icc (107 / 200 : ℝ) (27 / 50 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (107 / 200 : ℝ)) (b := (27 / 50 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (107 / 200 : ℝ)) (b := (27 / 50 : ℝ))
    (uL := seedULo (107 / 200 : ℝ) 4)
    (uH := seedUHi (27 / 50 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (107 / 200 : ℝ) (27 / 50 : ℝ) (seedULo (107 / 200 : ℝ) 4)
    (seedUHi (27 / 50 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L20 {s : ℝ} (hs : s ∈ Set.Icc (27 / 50 : ℝ) (109 / 200 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (27 / 50 : ℝ)) (b := (109 / 200 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (27 / 50 : ℝ)) (b := (109 / 200 : ℝ))
    (uL := seedULo (27 / 50 : ℝ) 4)
    (uH := seedUHi (109 / 200 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (27 / 50 : ℝ) (109 / 200 : ℝ) (seedULo (27 / 50 : ℝ) 4)
    (seedUHi (109 / 200 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L21 {s : ℝ} (hs : s ∈ Set.Icc (109 / 200 : ℝ) (547 / 1000 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (109 / 200 : ℝ)) (b := (547 / 1000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (109 / 200 : ℝ)) (b := (547 / 1000 : ℝ))
    (uL := seedULo (109 / 200 : ℝ) 4)
    (uH := seedUHi (547 / 1000 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (109 / 200 : ℝ) (547 / 1000 : ℝ) (seedULo (109 / 200 : ℝ) 4)
    (seedUHi (547 / 1000 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_neg_L22 {s : ℝ} (hs : s ∈ Set.Icc (547 / 1000 : ℝ) (11 / 20 : ℝ))
    : seedBracket s < 0 := by
  have hsand := seedU_sandwich_exp (a := (547 / 1000 : ℝ)) (b := (11 / 20 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (547 / 1000 : ℝ)) (b := (11 / 20 : ℝ))
    (uL := seedULo (547 / 1000 : ℝ) 4)
    (uH := seedUHi (11 / 20 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : seedBracketUpper (547 / 1000 : ℝ) (11 / 20 : ℝ) (seedULo (547 / 1000 : ℝ) 4)
    (seedUHi (11 / 20 : ℝ) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_pos_R01 {s : ℝ} (hs : s ∈ Set.Icc (23 / 40 : ℝ) (577 / 1000 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (23 / 40 : ℝ)) (b := (577 / 1000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (23 / 40 : ℝ)) (b := (577 / 1000 : ℝ))
    (uL := seedULo (23 / 40 : ℝ) 4)
    (uH := seedUHi (577 / 1000 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (23 / 40 : ℝ) (577 / 1000 : ℝ) (seedULo (23 / 40 : ℝ) 4)
    (seedUHi (577 / 1000 : ℝ) 4) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R02 {s : ℝ} (hs : s ∈ Set.Icc (577 / 1000 : ℝ) (291 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (577 / 1000 : ℝ)) (b := (291 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (577 / 1000 : ℝ)) (b := (291 / 500 : ℝ))
    (uL := seedULo (577 / 1000 : ℝ) 4)
    (uH := seedUHi (291 / 500 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (577 / 1000 : ℝ) (291 / 500 : ℝ) (seedULo (577 / 1000 : ℝ) 4)
    (seedUHi (291 / 500 : ℝ) 4) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R03 {s : ℝ} (hs : s ∈ Set.Icc (291 / 500 : ℝ) (587 / 1000 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (291 / 500 : ℝ)) (b := (587 / 1000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (291 / 500 : ℝ)) (b := (587 / 1000 : ℝ))
    (uL := seedULo (291 / 500 : ℝ) 4)
    (uH := seedUHi (587 / 1000 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (291 / 500 : ℝ) (587 / 1000 : ℝ) (seedULo (291 / 500 : ℝ) 4)
    (seedUHi (587 / 1000 : ℝ) 4) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R04 {s : ℝ} (hs : s ∈ Set.Icc (587 / 1000 : ℝ) (74 / 125 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (587 / 1000 : ℝ)) (b := (74 / 125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (587 / 1000 : ℝ)) (b := (74 / 125 : ℝ))
    (uL := seedULo (587 / 1000 : ℝ) 4)
    (uH := seedUHi (74 / 125 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (587 / 1000 : ℝ) (74 / 125 : ℝ) (seedULo (587 / 1000 : ℝ) 4)
    (seedUHi (74 / 125 : ℝ) 4) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R05 {s : ℝ} (hs : s ∈ Set.Icc (74 / 125 : ℝ) (301 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (74 / 125 : ℝ)) (b := (301 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (74 / 125 : ℝ)) (b := (301 / 500 : ℝ))
    (uL := seedULo (74 / 125 : ℝ) 4)
    (uH := seedUHi (301 / 500 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (74 / 125 : ℝ) (301 / 500 : ℝ) (seedULo (74 / 125 : ℝ) 4)
    (seedUHi (301 / 500 : ℝ) 4) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R06 {s : ℝ} (hs : s ∈ Set.Icc (301 / 500 : ℝ) (153 / 250 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (301 / 500 : ℝ)) (b := (153 / 250 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 4) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (301 / 500 : ℝ)) (b := (153 / 250 : ℝ))
    (uL := seedULo (301 / 500 : ℝ) 4)
    (uH := seedUHi (153 / 250 : ℝ) 4) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (301 / 500 : ℝ) (153 / 250 : ℝ) (seedULo (301 / 500 : ℝ) 4)
    (seedUHi (153 / 250 : ℝ) 4) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R07 {s : ℝ} (hs : s ∈ Set.Icc (153 / 250 : ℝ) (311 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (153 / 250 : ℝ)) (b := (311 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 4) (by norm_num) (by norm_num [seedV]) (m₂ := 8) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (153 / 250 : ℝ)) (b := (311 / 500 : ℝ))
    (uL := seedULo (153 / 250 : ℝ) 4)
    (uH := seedUHi (311 / 500 : ℝ) 8) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (153 / 250 : ℝ) (311 / 500 : ℝ) (seedULo (153 / 250 : ℝ) 4)
    (seedUHi (311 / 500 : ℝ) 8) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R08 {s : ℝ} (hs : s ∈ Set.Icc (311 / 500 : ℝ) (321 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (311 / 500 : ℝ)) (b := (321 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 8) (by norm_num) (by norm_num [seedV]) (m₂ := 8) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (311 / 500 : ℝ)) (b := (321 / 500 : ℝ))
    (uL := seedULo (311 / 500 : ℝ) 8)
    (uH := seedUHi (321 / 500 : ℝ) 8) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (311 / 500 : ℝ) (321 / 500 : ℝ) (seedULo (311 / 500 : ℝ) 8)
    (seedUHi (321 / 500 : ℝ) 8) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R09 {s : ℝ} (hs : s ∈ Set.Icc (321 / 500 : ℝ) (331 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (321 / 500 : ℝ)) (b := (331 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 8) (by norm_num) (by norm_num [seedV]) (m₂ := 8) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (321 / 500 : ℝ)) (b := (331 / 500 : ℝ))
    (uL := seedULo (321 / 500 : ℝ) 8)
    (uH := seedUHi (331 / 500 : ℝ) 8) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (321 / 500 : ℝ) (331 / 500 : ℝ) (seedULo (321 / 500 : ℝ) 8)
    (seedUHi (331 / 500 : ℝ) 8) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R10 {s : ℝ} (hs : s ∈ Set.Icc (331 / 500 : ℝ) (341 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (331 / 500 : ℝ)) (b := (341 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 8) (by norm_num) (by norm_num [seedV]) (m₂ := 8) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (331 / 500 : ℝ)) (b := (341 / 500 : ℝ))
    (uL := seedULo (331 / 500 : ℝ) 8)
    (uH := seedUHi (341 / 500 : ℝ) 8) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (331 / 500 : ℝ) (341 / 500 : ℝ) (seedULo (331 / 500 : ℝ) 8)
    (seedUHi (341 / 500 : ℝ) 8) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R11 {s : ℝ} (hs : s ∈ Set.Icc (341 / 500 : ℝ) (351 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (341 / 500 : ℝ)) (b := (351 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 8) (by norm_num) (by norm_num [seedV]) (m₂ := 8) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (341 / 500 : ℝ)) (b := (351 / 500 : ℝ))
    (uL := seedULo (341 / 500 : ℝ) 8)
    (uH := seedUHi (351 / 500 : ℝ) 8) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (341 / 500 : ℝ) (351 / 500 : ℝ) (seedULo (341 / 500 : ℝ) 8)
    (seedUHi (351 / 500 : ℝ) 8) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R12 {s : ℝ} (hs : s ∈ Set.Icc (351 / 500 : ℝ) (94 / 125 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (351 / 500 : ℝ)) (b := (94 / 125 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 8) (by norm_num) (by norm_num [seedV]) (m₂ := 8) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (351 / 500 : ℝ)) (b := (94 / 125 : ℝ))
    (uL := seedULo (351 / 500 : ℝ) 8)
    (uH := seedUHi (94 / 125 : ℝ) 8) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (351 / 500 : ℝ) (94 / 125 : ℝ) (seedULo (351 / 500 : ℝ) 8)
    (seedUHi (94 / 125 : ℝ) 8) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R13 {s : ℝ} (hs : s ∈ Set.Icc (94 / 125 : ℝ) (401 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (94 / 125 : ℝ)) (b := (401 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 8) (by norm_num) (by norm_num [seedV]) (m₂ := 16) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (94 / 125 : ℝ)) (b := (401 / 500 : ℝ))
    (uL := seedULo (94 / 125 : ℝ) 8)
    (uH := seedUHi (401 / 500 : ℝ) 16) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (94 / 125 : ℝ) (401 / 500 : ℝ) (seedULo (94 / 125 : ℝ) 8)
    (seedUHi (401 / 500 : ℝ) 16) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R14 {s : ℝ} (hs : s ∈ Set.Icc (401 / 500 : ℝ) (451 / 500 : ℝ))
    : 0 < seedBracket s := by
  have hsand := seedU_sandwich_exp (a := (401 / 500 : ℝ)) (b := (451 / 500 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (m₁ := 16) (by norm_num) (by norm_num [seedV]) (m₂ := 32) (by norm_num)
    (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (401 / 500 : ℝ)) (b := (451 / 500 : ℝ))
    (uL := seedULo (401 / 500 : ℝ) 16)
    (uH := seedUHi (451 / 500 : ℝ) 32) (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (401 / 500 : ℝ) (451 / 500 : ℝ) (seedULo (401 / 500 : ℝ) 16)
    (seedUHi (451 / 500 : ℝ) 32) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem seedBracket_pos_R15 {s : ℝ} (hs : s ∈ Set.Ico (451 / 500 : ℝ) 1) : 0 < seedBracket s := by
  have hsand := seedU_sandwich_one (a := (451 / 500 : ℝ)) (by norm_num) (by norm_num)
    (m₁ := 32) (by norm_num) (by norm_num [seedV]) s hs
  have hm := seedBracket_mem_Icc (a := (451 / 500 : ℝ)) (b := (1 : ℝ))
    (uL := seedULo (451 / 500 : ℝ) 32)
    (uH := 1) (by norm_num) (by norm_num) (Set.Ico_subset_Icc_self hs)
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsand.1 hsand.2
  have hp : 0 < seedBracketLower (451 / 500 : ℝ) (1 : ℝ) (seedULo (451 / 500 : ℝ) 32) (1 : ℝ) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi, seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

/-! ## 8. The derivative of the bracket along the logistic curve -/

noncomputable def seedVSlope (s : ℝ) : ℝ := 4 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2

noncomputable def seedAlphaSlope (s : ℝ) : ℝ := 72 * s * (1 + s ^ 2) ^ 2

noncomputable def seedBetaSlope (s : ℝ) : ℝ := 36 + 36 * s ^ 2 - 180 * s ^ 4 - 84 * s ^ 6

noncomputable def seedGammaSlope (s : ℝ) : ℝ := 48 * s ^ 5 + 24 * s ^ 7 - 168 * s ^ 3

/-- The derivative of `seedV s = 4 s / (1 - s^2)`. -/
theorem hasDerivAt_seedV {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    HasDerivAt seedV (seedVSlope s) s := by
  have hden : (1 : ℝ) - s ^ 2 ≠ 0 := by nlinarith
  have hnum : HasDerivAt (fun t : ℝ => 4 * t) 4 s := by
    simpa using (hasDerivAt_id s).const_mul (4 : ℝ)
  have hd : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_const (x := s) (c := (1 : ℝ))).sub (hasDerivAt_pow 2 s)
  have hdiv := hnum.div hd hden
  have hfun : ((fun t : ℝ => 4 * t) / (fun t : ℝ => 1 - t ^ 2)) = seedV := by
    funext t
    rw [Pi.div_apply, seedV]
  rw [hfun] at hdiv
  convert hdiv using 1
  unfold seedVSlope
  rw [show (4 * (1 - s ^ 2) - 4 * s * -(2 * s)) = 4 * (1 + s ^ 2) by ring]

/-- The derivative of the logistic variable `seedU`. -/
theorem hasDerivAt_seedU {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    HasDerivAt seedU (seedVSlope s / 2 * (1 - seedU s ^ 2)) s := by
  have hv := hasDerivAt_seedV h0 h1
  have hexp := hv.exp
  have hnum := hexp.sub_const 1
  have hden := hexp.add_const 1
  have hden0 : Real.exp (seedV s) + 1 ≠ 0 := by positivity
  have hdiv := hnum.div hden hden0
  have hfun : ((fun t : ℝ => Real.exp (seedV t) - 1) /
      (fun t : ℝ => Real.exp (seedV t) + 1)) = seedU := by
    funext t
    rw [Pi.div_apply, seedU]
  rw [hfun] at hdiv
  convert hdiv using 1
  rw [seedU]
  field_simp
  ring

/-- The derivative of the bracket read along the logistic curve. -/
noncomputable def seedHprime (s : ℝ) : ℝ :=
  seedAlphaSlope s * seedU s ^ 2 - seedBetaSlope s * seedU s + seedGammaSlope s +
    (2 * thirdOrderLeading s * seedU s - thirdOrderMiddle s) * (seedVSlope s / 2) *
      (1 - seedU s ^ 2)

theorem hasDerivAt_seedBracket {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    HasDerivAt seedBracket (seedHprime s) s := by
  have hU := hasDerivAt_seedU h0 h1
  have hA : HasDerivAt thirdOrderLeading (seedAlphaSlope s) s := by
    have hpow : HasDerivAt (fun t : ℝ => (1 + t ^ 2) ^ 3)
        (3 * (1 + s ^ 2) ^ 2 * (2 * s)) s := by
      have hp := (hasDerivAt_pow 2 s).const_add (1 : ℝ)
      have h3 := hp.pow 3
      simpa only [Pi.pow_apply, Nat.reduceSub, pow_one] using h3
    have h12 := hpow.const_mul (12 : ℝ)
    have hfun : (fun t : ℝ => (12 : ℝ) * (1 + t ^ 2) ^ 3) = thirdOrderLeading := by
      funext t
      rw [thirdOrderLeading]
    rw [hfun] at h12
    convert h12 using 1
    unfold seedAlphaSlope
    ring
  have hB : HasDerivAt thirdOrderMiddle (seedBetaSlope s) s := by
    have hfun : thirdOrderMiddle = fun t : ℝ => 36 * t + 12 * t ^ 3 - 36 * t ^ 5 - 12 * t ^ 7 := by
      funext t
      exact thirdOrderMiddle_eq_expansion t
    rw [hfun]
    have hlin : HasDerivAt (fun t : ℝ => 36 * t) 36 s := by
      simpa using (hasDerivAt_id s).const_mul (36 : ℝ)
    have h3a : HasDerivAt (fun t : ℝ => t ^ 3) (3 * s ^ 2) s := by
      simpa only [Nat.reduceSub, pow_one] using hasDerivAt_pow 3 s
    have h5a : HasDerivAt (fun t : ℝ => t ^ 5) (5 * s ^ 4) s := by
      simpa only [Nat.reduceSub, pow_one] using hasDerivAt_pow 5 s
    have h7a : HasDerivAt (fun t : ℝ => t ^ 7) (7 * s ^ 6) s := by
      simpa only [Nat.reduceSub, pow_one] using hasDerivAt_pow 7 s
    have hsum : HasDerivAt (fun t : ℝ => 36 * t + 12 * t ^ 3 - 36 * t ^ 5 - 12 * t ^ 7)
        (36 + 12 * (3 * s ^ 2) - 36 * (5 * s ^ 4) - 12 * (7 * s ^ 6)) s :=
      ((hlin.add (h3a.const_mul 12)).sub (h5a.const_mul 36)).sub (h7a.const_mul 12)
    convert hsum using 1
    unfold seedBetaSlope
    ring
  have hC : HasDerivAt thirdOrderConstant (seedGammaSlope s) s := by
    have hfun : thirdOrderConstant = fun t : ℝ => -1 + 8 * t ^ 6 + 3 * t ^ 8 - 42 * t ^ 4 := by
      funext t
      exact thirdOrderConstant_eq_expansion t
    rw [hfun]
    have hwhole : HasDerivAt (fun t : ℝ => -1 + 8 * t ^ 6 + 3 * t ^ 8 - 42 * t ^ 4)
        (0 + 8 * (6 * s ^ 5) + 3 * (8 * s ^ 7) - 42 * (4 * s ^ 3)) s := by
      have h6a : HasDerivAt (fun t : ℝ => 8 * t ^ 6) (8 * (6 * s ^ 5)) s :=
        (hasDerivAt_pow 6 s).const_mul 8
      have h8a : HasDerivAt (fun t : ℝ => 3 * t ^ 8) (3 * (8 * s ^ 7)) s :=
        (hasDerivAt_pow 8 s).const_mul 3
      have h4a : HasDerivAt (fun t : ℝ => 42 * t ^ 4) (42 * (4 * s ^ 3)) s :=
        (hasDerivAt_pow 4 s).const_mul 42
      have hconst : HasDerivAt (fun _ : ℝ => (-1 : ℝ)) 0 s :=
        hasDerivAt_const (x := s) (-1 : ℝ)
      exact ((hconst.add h6a).add h8a).sub h4a
    convert hwhole using 1
    unfold seedGammaSlope
    ring
  have hprod1 : HasDerivAt (fun t : ℝ => thirdOrderLeading t * seedU t ^ 2)
      (seedAlphaSlope s * seedU s ^ 2 +
        thirdOrderLeading s * (2 * seedU s * (seedVSlope s / 2 * (1 - seedU s ^ 2)))) s := by
    have hp := hA.mul (hU.pow 2)
    simpa only [Pi.pow_apply, Nat.reduceSub, pow_one] using hp
  have hprod2 : HasDerivAt (fun t : ℝ => thirdOrderMiddle t * seedU t)
      (seedBetaSlope s * seedU s + thirdOrderMiddle s * (seedVSlope s / 2 * (1 - seedU s ^ 2))) s :=
    hB.mul hU
  have hsum2 : HasDerivAt
      (fun t : ℝ => thirdOrderLeading t * seedU t ^ 2 - thirdOrderMiddle t * seedU t +
        thirdOrderConstant t)
      (seedAlphaSlope s * seedU s ^ 2 +
          thirdOrderLeading s * (2 * seedU s * (seedVSlope s / 2 * (1 - seedU s ^ 2))) -
        (seedBetaSlope s * seedU s + thirdOrderMiddle s * (seedVSlope s / 2 * (1 - seedU s ^ 2))) +
        seedGammaSlope s) s :=
    (hprod1.sub hprod2).add hC
  have hfun : seedBracket = fun t : ℝ =>
      thirdOrderLeading t * seedU t ^ 2 - thirdOrderMiddle t * seedU t + thirdOrderConstant t := by
    funext t
    rw [seedBracket, thirdOrderBracket_eq_quadratic]
  rw [hfun]
  convert hsum2 using 1
  unfold seedHprime
  ring

/-! ## 9. Coefficient monotonicity on the straddle -/

private theorem mixed_le {s b : ℝ} (h0 : 0 ≤ s) (hsb : s ≤ b) (hb0 : 0 ≤ b) (i j : ℕ) :
    s ^ i * b ^ j ≤ b ^ (i + j) := by
  have h1 : s ^ i ≤ b ^ i := pow_le_pow_left₀ h0 hsb i
  have h := mul_le_mul_of_nonneg_right h1 (pow_nonneg hb0 j)
  rwa [← pow_add] at h

theorem seedAlphaSlope_le {s : ℝ} (hs : s ∈ Set.Icc (11 / 20) (23 / 40)) :
    seedAlphaSlope (11 / 20) ≤ seedAlphaSlope s := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs.1
  have hfac : seedAlphaSlope s - seedAlphaSlope (11 / 20) =
      (s - 11 / 20) * (72 * (1 + 2 * (s ^ 2 + s * (11 / 20) + (11 / 20) ^ 2) +
        (s ^ 4 + s ^ 3 * (11 / 20) + s ^ 2 * (11 / 20) ^ 2 + s * (11 / 20) ^ 3 +
          (11 / 20) ^ 4))) := by
    unfold seedAlphaSlope
    ring
  have hs2 : 0 ≤ s ^ 2 := pow_nonneg hs0 2
  have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
  have hs4 : 0 ≤ s ^ 4 := pow_nonneg hs0 4
  have h1 : 0 ≤ s * (11 / 20) := mul_nonneg hs0 (by norm_num)
  have h2 : 0 ≤ s ^ 3 * (11 / 20) := mul_nonneg hs3 (by norm_num)
  have h3 : 0 ≤ s * (11 / 20) ^ 3 := mul_nonneg hs0 (by norm_num)
  have h4 : 0 ≤ s ^ 2 * (11 / 20) ^ 2 := mul_nonneg hs2 (by norm_num)
  have hsp : 0 ≤ s - 11 / 20 := sub_nonneg.mpr hs.1
  have hinner : 0 ≤ 72 * (1 + 2 * (s ^ 2 + s * (11 / 20) + (11 / 20) ^ 2) +
      (s ^ 4 + s ^ 3 * (11 / 20) + s ^ 2 * (11 / 20) ^ 2 + s * (11 / 20) ^ 3 +
        (11 / 20) ^ 4)) := by
    nlinarith [hs2, hs3, hs4, h1, h2, h3, h4]
  have hQ := mul_nonneg hsp hinner
  linarith [hfac, hQ]

theorem seedBetaSlope_le {s : ℝ} (hs : s ∈ Set.Icc (11 / 20) (23 / 40)) :
    seedBetaSlope s ≤ seedBetaSlope (11 / 20) := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs.1
  have hfac : seedBetaSlope (11 / 20) - seedBetaSlope s =
      (s ^ 2 - (11 / 20) ^ 2) * (180 * (s ^ 2 + (11 / 20) ^ 2) +
        84 * (s ^ 4 + s ^ 2 * (11 / 20) ^ 2 + (11 / 20) ^ 4) - 36) := by
    unfold seedBetaSlope
    ring
  have ha2 : (11 / 20) ^ 2 ≤ s ^ 2 := by nlinarith [hs.1, sq_nonneg (s + 11 / 20)]
  have h1 : 0 ≤ s ^ 2 - (11 / 20) ^ 2 := by linarith
  have hs2 : 0 ≤ s ^ 2 := pow_nonneg hs0 2
  have hs4 : 0 ≤ s ^ 4 := pow_nonneg hs0 4
  have h22 : 0 ≤ s ^ 2 * (11 / 20) ^ 2 := mul_nonneg hs2 (by norm_num)
  have h2 : 0 ≤ 180 * (s ^ 2 + (11 / 20) ^ 2) + 84 * (s ^ 4 + s ^ 2 * (11 / 20) ^ 2 +
      (11 / 20) ^ 4) - 36 := by
    nlinarith [ha2, hs2, hs4, h22]
  have hQ := mul_nonneg h1 h2
  linarith [hfac, hQ]

theorem thirdOrderMiddle_le {s : ℝ} (hs : s ∈ Set.Icc (11 / 20) (23 / 40)) :
    thirdOrderMiddle s ≤ thirdOrderMiddle (23 / 40) := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs.1
  have hb0 : (0 : ℝ) ≤ 23 / 40 := by norm_num
  have hfac : thirdOrderMiddle (23 / 40) - thirdOrderMiddle s = ((23 / 40) - s) *
      (36 + 12 * (s ^ 2 + s * (23 / 40) + (23 / 40) ^ 2)
        - 36 * (s ^ 4 + s ^ 3 * (23 / 40) + s ^ 2 * (23 / 40) ^ 2 + s * (23 / 40) ^ 3 +
            (23 / 40) ^ 4)
        - 12 * (s ^ 6 + s ^ 5 * (23 / 40) + s ^ 4 * (23 / 40) ^ 2 + s ^ 3 * (23 / 40) ^ 3 +
            s ^ 2 * (23 / 40) ^ 4 + s * (23 / 40) ^ 5 + (23 / 40) ^ 6)) := by
    rw [thirdOrderMiddle_eq_expansion, thirdOrderMiddle_eq_expansion]
    ring
  have m1 := mixed_le hs0 hs.2 hb0 2 0
  have m2 := mixed_le hs0 hs.2 hb0 1 1
  have m3 := mixed_le hs0 hs.2 hb0 4 0
  have m4 := mixed_le hs0 hs.2 hb0 3 1
  have m5 := mixed_le hs0 hs.2 hb0 2 2
  have m6 := mixed_le hs0 hs.2 hb0 1 3
  have m7 := mixed_le hs0 hs.2 hb0 6 0
  have m8 := mixed_le hs0 hs.2 hb0 5 1
  have m9 := mixed_le hs0 hs.2 hb0 4 2
  have m10 := mixed_le hs0 hs.2 hb0 3 3
  have m11 := mixed_le hs0 hs.2 hb0 2 4
  have m12 := mixed_le hs0 hs.2 hb0 1 5
  have hQ : 0 ≤ 36 + 12 * (s ^ 2 + s * (23 / 40) + (23 / 40) ^ 2)
      - 36 * (s ^ 4 + s ^ 3 * (23 / 40) + s ^ 2 * (23 / 40) ^ 2 + s * (23 / 40) ^ 3 +
          (23 / 40) ^ 4)
      - 12 * (s ^ 6 + s ^ 5 * (23 / 40) + s ^ 4 * (23 / 40) ^ 2 + s ^ 3 * (23 / 40) ^ 3 +
          s ^ 2 * (23 / 40) ^ 4 + s * (23 / 40) ^ 5 + (23 / 40) ^ 6) := by
    nlinarith [m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12]
  have hQ2 := mul_nonneg (sub_nonneg.mpr hs.2) hQ
  linarith [hfac, hQ2]

theorem seedGammaSlope_le {s : ℝ} (hs : s ∈ Set.Icc (11 / 20) (23 / 40)) :
    seedGammaSlope (23 / 40) ≤ seedGammaSlope s := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs.1
  have hb0 : (0 : ℝ) ≤ 23 / 40 := by norm_num
  have hfac : seedGammaSlope s - seedGammaSlope (23 / 40) = ((23 / 40) - s) *
      (168 * (s ^ 2 + s * (23 / 40) + (23 / 40) ^ 2)
        - 48 * (s ^ 4 + s ^ 3 * (23 / 40) + s ^ 2 * (23 / 40) ^ 2 + s * (23 / 40) ^ 3 +
            (23 / 40) ^ 4)
        - 24 * (s ^ 6 + s ^ 5 * (23 / 40) + s ^ 4 * (23 / 40) ^ 2 + s ^ 3 * (23 / 40) ^ 3 +
            s ^ 2 * (23 / 40) ^ 4 + s * (23 / 40) ^ 5 + (23 / 40) ^ 6)) := by
    unfold seedGammaSlope
    ring
  have g1 : (11 / 20) ^ 2 ≤ s ^ 2 := by nlinarith [hs.1, sq_nonneg (s + 11 / 20)]
  have g2 : (11 / 20) ^ 2 ≤ s * (23 / 40) := by
    have h := mul_le_mul_of_nonneg_left hs.2 (by norm_num : (0 : ℝ) ≤ 11 / 20)
    nlinarith [h, hs.1]
  have g3 : (11 / 20) ^ 2 ≤ (23 / 40) ^ 2 := by norm_num
  have n1 := mixed_le hs0 hs.2 hb0 2 0
  have n2 := mixed_le hs0 hs.2 hb0 1 1
  have n3 := mixed_le hs0 hs.2 hb0 4 0
  have n4 := mixed_le hs0 hs.2 hb0 3 1
  have n5 := mixed_le hs0 hs.2 hb0 2 2
  have n6 := mixed_le hs0 hs.2 hb0 1 3
  have n7 := mixed_le hs0 hs.2 hb0 6 0
  have n8 := mixed_le hs0 hs.2 hb0 5 1
  have n9 := mixed_le hs0 hs.2 hb0 4 2
  have n10 := mixed_le hs0 hs.2 hb0 3 3
  have n11 := mixed_le hs0 hs.2 hb0 2 4
  have n12 := mixed_le hs0 hs.2 hb0 1 5
  have hQ : 0 ≤ 168 * (s ^ 2 + s * (23 / 40) + (23 / 40) ^ 2)
      - 48 * (s ^ 4 + s ^ 3 * (23 / 40) + s ^ 2 * (23 / 40) ^ 2 + s * (23 / 40) ^ 3 +
          (23 / 40) ^ 4)
      - 24 * (s ^ 6 + s ^ 5 * (23 / 40) + s ^ 4 * (23 / 40) ^ 2 + s ^ 3 * (23 / 40) ^ 3 +
          s ^ 2 * (23 / 40) ^ 4 + s * (23 / 40) ^ 5 + (23 / 40) ^ 6) := by
    nlinarith [g1, g2, g3, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12]
  have hQ2 := mul_nonneg (sub_nonneg.mpr hs.2) hQ
  linarith [hfac, hQ2]

theorem seedVSlope_le {s : ℝ} (hs : s ∈ Set.Icc (11 / 20) (23 / 40)) :
    seedVSlope (11 / 20) ≤ seedVSlope s := by
  have hs0 : 0 ≤ s := le_trans (by norm_num) hs.1
  have h0s : 0 < 1 - s ^ 2 := by nlinarith [hs.1, hs.2]
  have h1 : 1 + (11 / 20) ^ 2 ≤ 1 + s ^ 2 := by nlinarith [hs.1, sq_nonneg (s + 11 / 20)]
  have h2 : (1 - s ^ 2) ^ 2 ≤ (1 - (11 / 20) ^ 2) ^ 2 := by
    have ha2 : (11 / 20) ^ 2 ≤ s ^ 2 := by nlinarith [hs.1, sq_nonneg (s + 11 / 20)]
    have hle : 1 - s ^ 2 ≤ 1 - (11 / 20) ^ 2 := by linarith
    exact pow_le_pow_left₀ (le_of_lt h0s) hle 2
  have hd1 : (0 : ℝ) < (1 - (11 / 20) ^ 2) ^ 2 := by norm_num
  have hd2 : 0 < (1 - s ^ 2) ^ 2 := pow_pos h0s 2
  unfold seedVSlope
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [h1, h2, le_of_lt h0s]
/-! ## 10. The chains of pieces -/

theorem seedBracket_neg_of_Icc_zero_s_lo {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (11 / 20 : ℝ)) :
    seedBracket s < 0 := by
  have h0 := hs.1
  rcases le_or_gt s (1 / 10) with h | h
  · exact seedBracket_neg_L01 ⟨h0, h⟩
  rcases le_or_gt s (3 / 20) with h2 | h2
  · exact seedBracket_neg_L02 ⟨le_of_lt h, h2⟩
  rcases le_or_gt s (1 / 5) with h3 | h3
  · exact seedBracket_neg_L03 ⟨le_of_lt h2, h3⟩
  rcases le_or_gt s (1 / 4) with h4 | h4
  · exact seedBracket_neg_L04 ⟨le_of_lt h3, h4⟩
  rcases le_or_gt s (3 / 10) with h5 | h5
  · exact seedBracket_neg_L05 ⟨le_of_lt h4, h5⟩
  rcases le_or_gt s (7 / 20) with h6 | h6
  · exact seedBracket_neg_L06 ⟨le_of_lt h5, h6⟩
  rcases le_or_gt s (37 / 100) with h7 | h7
  · exact seedBracket_neg_L07 ⟨le_of_lt h6, h7⟩
  rcases le_or_gt s (39 / 100) with h8 | h8
  · exact seedBracket_neg_L08 ⟨le_of_lt h7, h8⟩
  rcases le_or_gt s (41 / 100) with h9 | h9
  · exact seedBracket_neg_L09 ⟨le_of_lt h8, h9⟩
  rcases le_or_gt s (43 / 100) with h10 | h10
  · exact seedBracket_neg_L10 ⟨le_of_lt h9, h10⟩
  rcases le_or_gt s (9 / 20) with h11 | h11
  · exact seedBracket_neg_L11 ⟨le_of_lt h10, h11⟩
  rcases le_or_gt s (47 / 100) with h12 | h12
  · exact seedBracket_neg_L12 ⟨le_of_lt h11, h12⟩
  rcases le_or_gt s (49 / 100) with h13 | h13
  · exact seedBracket_neg_L13 ⟨le_of_lt h12, h13⟩
  rcases le_or_gt s (1 / 2) with h14 | h14
  · exact seedBracket_neg_L14 ⟨le_of_lt h13, h14⟩
  rcases le_or_gt s (51 / 100) with h15 | h15
  · exact seedBracket_neg_L15 ⟨le_of_lt h14, h15⟩
  rcases le_or_gt s (13 / 25) with h16 | h16
  · exact seedBracket_neg_L16 ⟨le_of_lt h15, h16⟩
  rcases le_or_gt s (53 / 100) with h17 | h17
  · exact seedBracket_neg_L17 ⟨le_of_lt h16, h17⟩
  rcases le_or_gt s (107 / 200) with h18 | h18
  · exact seedBracket_neg_L18 ⟨le_of_lt h17, h18⟩
  rcases le_or_gt s (27 / 50) with h19 | h19
  · exact seedBracket_neg_L19 ⟨le_of_lt h18, h19⟩
  rcases le_or_gt s (109 / 200) with h20 | h20
  · exact seedBracket_neg_L20 ⟨le_of_lt h19, h20⟩
  rcases le_or_gt s (547 / 1000) with h21 | h21
  · exact seedBracket_neg_L21 ⟨le_of_lt h20, h21⟩
  exact seedBracket_neg_L22 ⟨le_of_lt h21, hs.2⟩

theorem seedBracket_pos_of_Ico_s_hi_one {s : ℝ} (hs : s ∈ Set.Ico (23 / 40 : ℝ) 1) :
    0 < seedBracket s := by
  have h0 := hs.1
  rcases le_or_gt s (577 / 1000) with h | h
  · exact seedBracket_pos_R01 ⟨h0, h⟩
  rcases le_or_gt s (291 / 500) with h2 | h2
  · exact seedBracket_pos_R02 ⟨le_of_lt h, h2⟩
  rcases le_or_gt s (587 / 1000) with h3 | h3
  · exact seedBracket_pos_R03 ⟨le_of_lt h2, h3⟩
  rcases le_or_gt s (74 / 125) with h4 | h4
  · exact seedBracket_pos_R04 ⟨le_of_lt h3, h4⟩
  rcases le_or_gt s (301 / 500) with h5 | h5
  · exact seedBracket_pos_R05 ⟨le_of_lt h4, h5⟩
  rcases le_or_gt s (153 / 250) with h6 | h6
  · exact seedBracket_pos_R06 ⟨le_of_lt h5, h6⟩
  rcases le_or_gt s (311 / 500) with h7 | h7
  · exact seedBracket_pos_R07 ⟨le_of_lt h6, h7⟩
  rcases le_or_gt s (321 / 500) with h8 | h8
  · exact seedBracket_pos_R08 ⟨le_of_lt h7, h8⟩
  rcases le_or_gt s (331 / 500) with h9 | h9
  · exact seedBracket_pos_R09 ⟨le_of_lt h8, h9⟩
  rcases le_or_gt s (341 / 500) with h10 | h10
  · exact seedBracket_pos_R10 ⟨le_of_lt h9, h10⟩
  rcases le_or_gt s (351 / 500) with h11 | h11
  · exact seedBracket_pos_R11 ⟨le_of_lt h10, h11⟩
  rcases le_or_gt s (94 / 125) with h12 | h12
  · exact seedBracket_pos_R12 ⟨le_of_lt h11, h12⟩
  rcases le_or_gt s (401 / 500) with h13 | h13
  · exact seedBracket_pos_R13 ⟨le_of_lt h12, h13⟩
  rcases le_or_gt s (451 / 500) with h14 | h14
  · exact seedBracket_pos_R14 ⟨le_of_lt h13, h14⟩
  exact seedBracket_pos_R15 ⟨le_of_lt h14, hs.2⟩

/-! ## 11. The straddle: positivity of the derivative and the crossing -/

/-- The upper sandwich value stays below one once the exponent modulus is
certified: `(Hi - 1)/(Lo + 1) ≤ 1` is `Hi - Lo ≤ 2`, and the tail mass
`expTail y ≤ 1 / 240` and the Taylor head `expTaylor y ≤ 3` close it. -/
theorem seedUHi_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) (hmw : seedV s ≤ 4) :
    seedUHi s 4 ≤ 1 := by
  have hy0 : 0 ≤ seedV s / 4 := div_nonneg (seedV_nonneg h0 h1) (by norm_num)
  have hy1 : seedV s / 4 ≤ 1 := by linarith
  have hL0 : 0 ≤ seedExpLo s 4 := by
    rw [seedExpLo, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    exact sq_nonneg _
  rw [seedUHi, div_le_iff₀ (by linarith : (0 : ℝ) < seedExpLo s 4 + 1)]
  rw [seedExpHi, seedExpLo]
  have hT3 : expTaylor (seedV s / 4) ≤ 3 := by
    have h : ∑ i ∈ Finset.range 20, (seedV s / 4) ^ i / (i.factorial : ℝ) ≤
        ∑ i ∈ Finset.range 20, (1 : ℝ) / (i.factorial : ℝ) :=
      Finset.sum_le_sum fun i _ =>
        div_le_div_of_nonneg_right (pow_le_one₀ hy0 hy1) (by positivity)
    refine le_trans h ?_
    norm_num [Finset.sum_range_succ]
  have hP240 : expTail (seedV s / 4) ≤ 1 / 240 := by
    have h20 : (seedV s / 4) ^ 20 ≤ 1 := pow_le_one₀ hy0 hy1
    rw [expTail]
    calc (seedV s / 4) ^ 20 * ((20 : ℝ) + 1) / (((20 : ℕ).factorial : ℝ) * 20)
        ≤ 1 * ((20 : ℝ) + 1) / (((20 : ℕ).factorial : ℝ) * 20) := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          nlinarith [h20]
      _ ≤ 1 / 240 := by norm_num
  have hdiff : (expTaylor (seedV s / 4) + expTail (seedV s / 4)) ^ 4 -
      (expTaylor (seedV s / 4) - expTail (seedV s / 4)) ^ 4 ≤ 2 := by
    have hring : (expTaylor (seedV s / 4) + expTail (seedV s / 4)) ^ 4 -
        (expTaylor (seedV s / 4) - expTail (seedV s / 4)) ^ 4 =
        8 * expTaylor (seedV s / 4) * expTail (seedV s / 4) *
          (expTaylor (seedV s / 4) ^ 2 + expTail (seedV s / 4) ^ 2) := by ring
    rw [hring]
    have hT0 : 0 ≤ expTaylor (seedV s / 4) := expTaylor_nonneg hy0
    have hP0 : 0 ≤ expTail (seedV s / 4) := expTail_nonneg hy0
    have hTP : expTaylor (seedV s / 4) * expTail (seedV s / 4) ≤ 3 * (1 / 240) :=
      mul_le_mul hT3 hP240 hP0 (by norm_num)
    have hsum2 : expTaylor (seedV s / 4) ^ 2 + expTail (seedV s / 4) ^ 2 ≤ 10 := by
      nlinarith [hT3, hP240, hT0, hP0]
    have hprod := mul_le_mul hTP hsum2
      (by positivity : (0 : ℝ) ≤ expTaylor (seedV s / 4) ^ 2 + expTail (seedV s / 4) ^ 2)
      (by norm_num : (0 : ℝ) ≤ 3 * (1 / 240))
    linarith [hprod]
  linarith [hdiff]

/-- The lower end of the upper sandwich stays above minus one. -/
theorem seedUHi_ge_neg_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    -1 ≤ seedUHi s 4 := by
  have hH0 : 0 ≤ seedExpHi s 4 := seedExpHi_nonneg h0 h1 (by norm_num)
  have hL0 : 0 ≤ seedExpLo s 4 := by
    rw [seedExpLo, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    exact sq_nonneg _
  rw [seedUHi, le_div_iff₀ (by linarith : (0 : ℝ) < seedExpLo s 4 + 1)]
  linarith

/-- The certified rational lower bound for `h'` on the straddle. -/
noncomputable def seedHprimeLower : ℝ :=
  seedAlphaSlope (11 / 20) * seedULo (11 / 20) 4 ^ 2 -
    seedBetaSlope (11 / 20) * seedUHi (23 / 40) 4 + seedGammaSlope (23 / 40) +
    (2 * thirdOrderLeading (11 / 20) * seedULo (11 / 20) 4 - thirdOrderMiddle (23 / 40)) *
      (seedVSlope (11 / 20) / 2) * (1 - seedUHi (23 / 40) 4 ^ 2)

theorem seedHprimeLower_pos : 0 < seedHprimeLower := by
  norm_num [seedHprimeLower, seedAlphaSlope, seedBetaSlope, seedGammaSlope, seedVSlope,
    seedULo, seedUHi, seedExpLo, seedExpHi, seedV, thirdOrderLeading, thirdOrderMiddle,
    expTaylor, expTail, Finset.sum_range_succ]

theorem seedHprime_ge_lower {s : ℝ} (hs : s ∈ Set.Ioo (11 / 20) (23 / 40)) :
    seedHprimeLower ≤ seedHprime s := by
  have hmem : s ∈ Set.Icc (11 / 20 : ℝ) (23 / 40) := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hsw := seedU_sandwich_exp (a := (11 : ℝ) / 20) (b := 23 / 40) (by norm_num)
    (by norm_num) (by norm_num) (m₁ := 4) (by norm_num) (by norm_num [seedV])
    (m₂ := 4) (by norm_num) (by norm_num [seedV]) s hmem
  have huL0 : 0 ≤ seedULo (11 / 20) 4 :=
    seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV])
  have huH1 : seedUHi (23 / 40) 4 ≤ 1 :=
    seedUHi_le_one (by norm_num) (by norm_num) (by norm_num [seedV])
  have huHm1 : -1 ≤ seedUHi (23 / 40) 4 :=
    seedUHi_ge_neg_one (by norm_num) (by norm_num)
  have huH2le : seedUHi (23 / 40) 4 ^ 2 ≤ 1 := by nlinarith [huH1, huHm1]
  have hu0 : 0 ≤ seedU s := le_trans huL0 hsw.1
  have hu2 : seedULo (11 / 20) 4 ^ 2 ≤ seedU s ^ 2 := pow_le_pow_left₀ huL0 hsw.1 2
  have huH2 : seedU s ^ 2 ≤ seedUHi (23 / 40) 4 ^ 2 := pow_le_pow_left₀ hu0 hsw.2 2
  have hα : seedAlphaSlope (11 / 20) ≤ seedAlphaSlope s := seedAlphaSlope_le hmem
  have hβ : seedBetaSlope s ≤ seedBetaSlope (11 / 20) := seedBetaSlope_le hmem
  have hγ : seedGammaSlope (23 / 40) ≤ seedGammaSlope s := seedGammaSlope_le hmem
  have hB : thirdOrderMiddle s ≤ thirdOrderMiddle (23 / 40) := thirdOrderMiddle_le hmem
  have hA : thirdOrderLeading (11 / 20) ≤ thirdOrderLeading s :=
    thirdOrderLeading_le_of_le (by norm_num) (le_of_lt hs.1)
  have hv : seedVSlope (11 / 20) ≤ seedVSlope s := seedVSlope_le hmem
  have hα0 : 0 ≤ seedAlphaSlope (11 / 20) := by norm_num [seedAlphaSlope]
  have hβ0 : 0 ≤ seedBetaSlope (11 / 20) := by norm_num [seedBetaSlope]
  have hv0 : 0 ≤ seedVSlope (11 / 20) := by norm_num [seedVSlope]
  have hp0 : 0 ≤ 2 * thirdOrderLeading (11 / 20) * seedULo (11 / 20) 4 -
      thirdOrderMiddle (23 / 40) := by
    norm_num [thirdOrderLeading, thirdOrderMiddle, seedULo, seedUHi, seedExpLo, seedExpHi,
      seedV, expTaylor, expTail, Finset.sum_range_succ]
  have hT1 : seedAlphaSlope (11 / 20) * seedULo (11 / 20) 4 ^ 2 ≤
      seedAlphaSlope s * seedU s ^ 2 :=
    mul_le_mul hα hu2 (pow_nonneg huL0 2) (le_trans hα0 hα)
  have hT2 : seedBetaSlope s * seedU s ≤ seedBetaSlope (11 / 20) * seedUHi (23 / 40) 4 :=
    mul_le_mul hβ hsw.2 hu0 hβ0
  have hle1 : 2 * thirdOrderLeading (11 / 20) * seedULo (11 / 20) 4 ≤
      2 * thirdOrderLeading s * seedU s := by
    have hA0 : (0 : ℝ) ≤ thirdOrderLeading (11 / 20) := by norm_num [thirdOrderLeading]
    have h := mul_le_mul hA hsw.1 huL0 (le_trans hA0 hA)
    linarith [h]
  have hF1 : 2 * thirdOrderLeading (11 / 20) * seedULo (11 / 20) 4 -
      thirdOrderMiddle (23 / 40) ≤
      2 * thirdOrderLeading s * seedU s - thirdOrderMiddle s := by linarith [hle1, hB]
  have hF1pos : 0 ≤ 2 * thirdOrderLeading s * seedU s - thirdOrderMiddle s :=
    le_trans hp0 hF1
  have hf2 : seedVSlope (11 / 20) / 2 ≤ seedVSlope s / 2 := by linarith
  have hf20 : 0 ≤ seedVSlope (11 / 20) / 2 := by linarith
  have h12 := mul_le_mul hF1 hf2 hf20 hF1pos
  have h12pos : 0 ≤ (2 * thirdOrderLeading s * seedU s - thirdOrderMiddle s) *
      (seedVSlope s / 2) := mul_nonneg hF1pos (le_trans hf20 hf2)
  have hf3 : 1 - seedUHi (23 / 40) 4 ^ 2 ≤ 1 - seedU s ^ 2 := by linarith [huH2]
  have hf30 : 0 ≤ 1 - seedUHi (23 / 40) 4 ^ 2 := by linarith [huH2le]
  have hT4 := mul_le_mul h12 hf3 hf30 h12pos
  unfold seedHprime seedHprimeLower
  linarith [hT1, hT2, hγ, hT4]

theorem continuousOn_seedBracket :
    ContinuousOn seedBracket (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
  have hv : ContinuousOn seedV (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
    have h : ContinuousOn ((fun t : ℝ => 4 * t) / (fun t : ℝ => 1 - t ^ 2))
        (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
      apply ContinuousOn.div
      · exact continuousOn_const.mul continuousOn_id
      · exact continuousOn_const.sub (continuousOn_id.pow 2)
      · intro x hx
        exact ne_of_gt (by nlinarith [hx.1, hx.2] : (0 : ℝ) < 1 - x ^ 2)
    exact h.congr fun t _ => by rw [Pi.div_apply, seedV]
  have hu : ContinuousOn seedU (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
    have hexp : ContinuousOn (fun t : ℝ => Real.exp (seedV t))
        (Set.Icc (11 / 20 : ℝ) (23 / 40)) := Real.continuous_exp.comp_continuousOn hv
    have h : ContinuousOn
        ((fun t : ℝ => Real.exp (seedV t) - 1) / (fun t : ℝ => Real.exp (seedV t) + 1))
        (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
      apply ContinuousOn.div
      · exact hexp.sub continuousOn_const
      · exact hexp.add continuousOn_const
      · intro x _
        exact ne_of_gt (by positivity : (0 : ℝ) < Real.exp (seedV x) + 1)
    exact h.congr fun t _ => by rw [Pi.div_apply, seedU]
  have hL : ContinuousOn thirdOrderLeading (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
    unfold thirdOrderLeading
    exact continuousOn_const.mul ((continuousOn_const.add (continuousOn_id.pow 2)).pow 3)
  have hM : ContinuousOn thirdOrderMiddle (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
    have hfun : thirdOrderMiddle =
        fun t : ℝ => 36 * t + 12 * t ^ 3 - 36 * t ^ 5 - 12 * t ^ 7 :=
      funext thirdOrderMiddle_eq_expansion
    rw [hfun]
    exact (((continuousOn_id.const_mul 36).add ((continuousOn_id.pow 3).const_mul 12)).sub
      ((continuousOn_id.pow 5).const_mul 36)).sub ((continuousOn_id.pow 7).const_mul 12)
  have hC : ContinuousOn thirdOrderConstant (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
    have hfun : thirdOrderConstant = fun t : ℝ => -1 + 8 * t ^ 6 + 3 * t ^ 8 - 42 * t ^ 4 :=
      funext thirdOrderConstant_eq_expansion
    rw [hfun]
    exact ((continuousOn_const.add ((continuousOn_id.pow 6).const_mul 8)).add
      ((continuousOn_id.pow 8).const_mul 3)).sub ((continuousOn_id.pow 4).const_mul 42)
  have hfun : seedBracket = fun s : ℝ =>
      thirdOrderLeading s * seedU s ^ 2 - thirdOrderMiddle s * seedU s +
        thirdOrderConstant s := by
    funext t
    rw [seedBracket, thirdOrderBracket_eq_quadratic]
  rw [hfun]
  exact ((hL.mul (hu.pow 2)).sub (hM.mul hu)).add hC

theorem seedBracket_strictMonoOn :
    StrictMonoOn seedBracket (Set.Icc (11 / 20 : ℝ) (23 / 40)) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuousOn_seedBracket ?_
  intro x hx
  rw [interior_Icc] at hx
  have hx0 : 0 < x := lt_trans (by norm_num) hx.1
  have hx1 : x < 1 := lt_trans hx.2 (by norm_num)
  have hd : deriv seedBracket x = seedHprime x := (hasDerivAt_seedBracket hx0 hx1).deriv
  rw [hd]
  exact lt_of_lt_of_le seedHprimeLower_pos (seedHprime_ge_lower hx)

theorem seedBracket_at_s_lo_neg : seedBracket (11 / 20) < 0 :=
  seedBracket_neg_L22 ⟨by norm_num, le_rfl⟩

theorem seedBracket_at_s_hi_pos : 0 < seedBracket (23 / 40) :=
  seedBracket_pos_R01 ⟨le_rfl, by norm_num⟩

theorem seedBracket_at_s_d_neg : seedBracket (5634883 / 10 ^ 7) < 0 := by
  have hs : (5634883 / 10 ^ 7 : ℝ) ∈ Set.Icc (5634883 / 10 ^ 7 : ℝ) (5634883 / 10 ^ 7 : ℝ) :=
    ⟨le_rfl, le_rfl⟩
  have hsw := seedU_sandwich_exp (a := (5634883 / 10 ^ 7 : ℝ)) (b := 5634883 / 10 ^ 7)
    (by norm_num) (by norm_num) (by norm_num) (m₁ := 4) (by norm_num) (by norm_num [seedV])
    (m₂ := 4) (by norm_num) (by norm_num [seedV]) _ hs
  have hm := seedBracket_mem_Icc (a := (5634883 / 10 ^ 7 : ℝ)) (b := 5634883 / 10 ^ 7)
    (uL := seedULo (5634883 / 10 ^ 7) 4) (uH := seedUHi (5634883 / 10 ^ 7) 4)
    (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsw.1 hsw.2
  have hp : seedBracketUpper (5634883 / 10 ^ 7) (5634883 / 10 ^ 7)
      (seedULo (5634883 / 10 ^ 7) 4) (seedUHi (5634883 / 10 ^ 7) 4) < 0 := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi,
      seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.2, hp]

theorem seedBracket_at_s_c_pos : 0 < seedBracket (1408721 / 2500000) := by
  have hs : (1408721 / 2500000 : ℝ) ∈
      Set.Icc (1408721 / 2500000 : ℝ) (1408721 / 2500000 : ℝ) := ⟨le_rfl, le_rfl⟩
  have hsw := seedU_sandwich_exp (a := (1408721 / 2500000 : ℝ)) (b := 1408721 / 2500000)
    (by norm_num) (by norm_num) (by norm_num) (m₁ := 4) (by norm_num) (by norm_num [seedV])
    (m₂ := 4) (by norm_num) (by norm_num [seedV]) _ hs
  have hm := seedBracket_mem_Icc (a := (1408721 / 2500000 : ℝ)) (b := 1408721 / 2500000)
    (uL := seedULo (1408721 / 2500000) 4) (uH := seedUHi (1408721 / 2500000) 4)
    (by norm_num) (by norm_num) hs
    (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
    hsw.1 hsw.2
  have hp : 0 < seedBracketLower (1408721 / 2500000) (1408721 / 2500000)
      (seedULo (1408721 / 2500000) 4) (seedUHi (1408721 / 2500000) 4) := by
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi,
      seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  linarith [hm.1, hp]

theorem exists_seedBracket_eq_zero :
    ∃ s ∈ Set.Icc (5634883 / 10 ^ 7) (1408721 / 2500000), seedBracket s = 0 := by
  have hab : (5634883 / 10 ^ 7 : ℝ) ≤ 1408721 / 2500000 := by norm_num
  have hcont : ContinuousOn seedBracket
      (Set.Icc (5634883 / 10 ^ 7 : ℝ) (1408721 / 2500000)) :=
    continuousOn_seedBracket.mono (Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have h0mem : (0 : ℝ) ∈ Set.Icc (seedBracket (5634883 / 10 ^ 7))
      (seedBracket (1408721 / 2500000)) :=
    ⟨le_of_lt seedBracket_at_s_d_neg, le_of_lt seedBracket_at_s_c_pos⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hab hcont h0mem
  exact ⟨s, hs, hfs⟩

theorem existsUnique_seedBracket_eq_zero :
    ∃! s : ℝ, s ∈ Set.Icc (5634883 / 10 ^ 7) (1408721 / 2500000) ∧ seedBracket s = 0 := by
  obtain ⟨s0, hs0, hf0⟩ := exists_seedBracket_eq_zero
  refine ⟨s0, ⟨hs0, hf0⟩, ?_⟩
  intro y hy
  have hy' : y ∈ Set.Icc (11 / 20 : ℝ) (23 / 40) :=
    ⟨le_trans (by norm_num) hy.1.1, le_trans hy.1.2 (by norm_num)⟩
  have hs0' : s0 ∈ Set.Icc (11 / 20 : ℝ) (23 / 40) :=
    ⟨le_trans (by norm_num) hs0.1, le_trans hs0.2 (by norm_num)⟩
  exact ((seedBracket_strictMonoOn.injOn hs0' hy') (by rw [hf0, hy.2])).symm

theorem seedBracket_neg_of_Icc_zero_s_d {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (5634883 / 10 ^ 7)) : seedBracket s < 0 := by
  rcases le_or_gt s (11 / 20) with h | h
  · exact seedBracket_neg_of_Icc_zero_s_lo ⟨hs.1, h⟩
  · have hs' : s ∈ Set.Icc (11 / 20 : ℝ) (23 / 40) :=
      ⟨le_of_lt h, le_trans hs.2 (by norm_num)⟩
    have hs_d : (5634883 / 10 ^ 7 : ℝ) ∈ Set.Icc (11 / 20 : ℝ) (23 / 40) := by norm_num
    have hmono := seedBracket_strictMonoOn.monotoneOn hs' hs_d hs.2
    linarith [hmono, seedBracket_at_s_d_neg]

theorem seedBracket_pos_of_Ico_s_c_one {s : ℝ}
    (hs : s ∈ Set.Ico (1408721 / 2500000) 1) : 0 < seedBracket s := by
  rcases le_or_gt (23 / 40) s with h | h
  · exact seedBracket_pos_of_Ico_s_hi_one ⟨h, hs.2⟩
  · have hs' : s ∈ Set.Icc (11 / 20 : ℝ) (23 / 40) := ⟨by linarith [hs.1], le_of_lt h⟩
    have hs_c : (1408721 / 2500000 : ℝ) ∈ Set.Icc (11 / 20 : ℝ) (23 / 40) := by norm_num
    have hmono := seedBracket_strictMonoOn.monotoneOn hs_c hs' hs.1
    linarith [hmono, seedBracket_at_s_c_pos]

/-! ## 12. The sign transfer to `T'''` -/

theorem iteratedDeriv_three_smoothTransition_eq_seedBracket (s : ℝ) (h0 : 0 < s) (h1 : s < 1) :
    (1 - s ^ 2) ^ 6 * iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) =
      64 * (Real.smoothTransition ((1 - s) / 2) *
        (1 - Real.smoothTransition ((1 - s) / 2))) * seedBracket s := by
  rw [iteratedDeriv_three_smoothTransition_eq_bracket s h0 h1]
  unfold seedBracket
  rw [seedU_eq_reflect s h0 h1]

theorem iteratedDeriv_three_smoothTransition_seedBracket_pos_iff (s : ℝ) (h0 : 0 < s)
    (h1 : s < 1) :
    0 < iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) ↔ 0 < seedBracket s := by
  have hfac := iteratedDeriv_three_smoothTransition_eq_seedBracket s h0 h1
  have hpow : (0 : ℝ) < (1 - s ^ 2) ^ 6 := by
    have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
    positivity
  have hT0 : 0 < Real.smoothTransition ((1 - s) / 2) :=
    Real.smoothTransition.pos_of_pos (by linarith)
  have hT1 : Real.smoothTransition ((1 - s) / 2) < 1 :=
    Real.smoothTransition.lt_one_of_lt_one (by linarith)
  have hprod : (0 : ℝ) < Real.smoothTransition ((1 - s) / 2) *
      (1 - Real.smoothTransition ((1 - s) / 2)) := mul_pos hT0 (by linarith)
  have h64 : (0 : ℝ) < 64 * (Real.smoothTransition ((1 - s) / 2) *
      (1 - Real.smoothTransition ((1 - s) / 2))) := mul_pos (by norm_num) hprod
  rw [← mul_pos_iff_of_pos_left hpow, hfac, mul_pos_iff_of_pos_left h64]

theorem iteratedDeriv_three_smoothTransition_seedBracket_neg_iff (s : ℝ) (h0 : 0 < s)
    (h1 : s < 1) :
    iteratedDeriv 3 Real.smoothTransition ((1 - s) / 2) < 0 ↔ seedBracket s < 0 := by
  have hfac := iteratedDeriv_three_smoothTransition_eq_seedBracket s h0 h1
  have hpow : (0 : ℝ) < (1 - s ^ 2) ^ 6 := by
    have hs2 : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
    positivity
  have hT0 : 0 < Real.smoothTransition ((1 - s) / 2) :=
    Real.smoothTransition.pos_of_pos (by linarith)
  have hT1 : Real.smoothTransition ((1 - s) / 2) < 1 :=
    Real.smoothTransition.lt_one_of_lt_one (by linarith)
  have hprod : (0 : ℝ) < Real.smoothTransition ((1 - s) / 2) *
      (1 - Real.smoothTransition ((1 - s) / 2)) := mul_pos hT0 (by linarith)
  have h64 : (0 : ℝ) < 64 * (Real.smoothTransition ((1 - s) / 2) *
      (1 - Real.smoothTransition ((1 - s) / 2))) := mul_pos (by norm_num) hprod
  rw [← mul_neg_of_pos_left_iff _ _ hpow, hfac, mul_neg_of_pos_left_iff _ _ h64]

theorem iteratedDeriv_three_pos_of_Ioc_zero_x_c {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) (1091279 / 5000000)) :
    0 < iteratedDeriv 3 Real.smoothTransition x := by
  have hs : (1 - 2 * x) ∈ Set.Ico (1408721 / 2500000 : ℝ) 1 := by
    constructor
    · linarith [hx.2]
    · linarith [hx.1]
  have h0 : 0 < 1 - 2 * x := by linarith [hx.2]
  have h1 : 1 - 2 * x < 1 := by linarith [hx.1]
  rw [show x = (1 - (1 - 2 * x)) / 2 by ring]
  exact (iteratedDeriv_three_smoothTransition_seedBracket_pos_iff (1 - 2 * x) h0 h1).mpr
    (seedBracket_pos_of_Ico_s_c_one hs)

theorem iteratedDeriv_three_neg_of_Ico_x_d_half {x : ℝ}
    (hx : x ∈ Set.Ico (4365117 / 20000000) (1 / 2)) :
    iteratedDeriv 3 Real.smoothTransition x < 0 := by
  have hs : (1 - 2 * x) ∈ Set.Icc (0 : ℝ) (5634883 / 10 ^ 7) :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hs0 : 0 < 1 - 2 * x := by linarith [hx.2]
  have h1 : 1 - 2 * x < 1 := by linarith [hx.1]
  rw [show x = (1 - (1 - 2 * x)) / 2 by ring]
  exact (iteratedDeriv_three_smoothTransition_seedBracket_neg_iff (1 - 2 * x) hs0 h1).mpr
    (seedBracket_neg_of_Icc_zero_s_d hs)

theorem iteratedDeriv_three_nonneg_of_Icc_zero_x_c {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (1091279 / 5000000)) :
    0 ≤ iteratedDeriv 3 Real.smoothTransition x := by
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h, iteratedDeriv_three_smoothTransition_zero]
  · exact le_of_lt (iteratedDeriv_three_pos_of_Ioc_zero_x_c ⟨h, hx.2⟩)

theorem iteratedDeriv_three_nonpos_of_Icc_x_d_half {x : ℝ}
    (hx : x ∈ Set.Icc (4365117 / 20000000) (1 / 2)) :
    iteratedDeriv 3 Real.smoothTransition x ≤ 0 := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · rw [h, iteratedDeriv_three_smoothTransition_half]
    norm_num
  · exact le_of_lt (iteratedDeriv_three_neg_of_Ico_x_d_half ⟨hx.1, h⟩)

/-! ## 13. The rung: `derivOrderL1 3 smoothSeed` in a rational bracket -/

/-- The standard-point gain, matching the reflected committed gain. -/
noncomputable def gainStd (s : ℝ) : ℝ := 8 * (1 + s ^ 2) / (1 - s ^ 2) ^ 2

/-- The standard-point gain slope, matching the reflected committed slope. -/
noncomputable def gainSlopeStd (s : ℝ) : ℝ := -(32 * s * (s ^ 2 + 3) / (1 - s ^ 2) ^ 3)

/-- The second-derivative profile in the logistic variable. -/
noncomputable def seedP (s v : ℝ) : ℝ := (1 - v ^ 2) * (v * gainStd s ^ 2 + gainSlopeStd s)

/-- The Lipschitz constant of `seedP s` on `[seedULo s 4, seedUHi s 4]`. -/
noncomputable def ttwoMp (s : ℝ) : ℝ :=
  gainStd s ^ 2 * (1 + 3 * seedUHi s 4 ^ 2) + 2 * seedUHi s 4 * |gainSlopeStd s|

/-- Lower certified bracket for `T'' ((1 - s) / 2)`. -/
noncomputable def ttwoLower (s : ℝ) : ℝ :=
  seedP s (seedULo s 4) / 4 - ttwoMp s * (seedUHi s 4 - seedULo s 4) / 4

/-- Upper certified bracket for `T'' ((1 - s) / 2)`. -/
noncomputable def ttwoUpper (s : ℝ) : ℝ :=
  seedP s (seedULo s 4) / 4 + ttwoMp s * (seedUHi s 4 - seedULo s 4) / 4

/-- Lower bracket of the bracket profile on the two-point gap `[s_d, s_c]`. -/
noncomputable def gapLo : ℝ := seedBracketLower (5634883 / 10 ^ 7) (1408721 / 2500000)
  (seedULo (5634883 / 10 ^ 7) 4) (seedUHi (1408721 / 2500000) 4)

/-- Upper bracket of the bracket profile on the two-point gap `[s_d, s_c]`. -/
noncomputable def gapHi : ℝ := seedBracketUpper (5634883 / 10 ^ 7) (1408721 / 2500000)
  (seedULo (5634883 / 10 ^ 7) 4) (seedUHi (1408721 / 2500000) 4)

/-- The certified bound on `|T'''|` in the gap around the crossing. -/
noncomputable def gapBound : ℝ := 16 * |gapHi| / (1 - (1408721 / 2500000) ^ 2) ^ 6

theorem iteratedDeriv_two_smoothTransition_mem_Icc (s : ℝ) (h0 : 0 < s) (h1 : s < 1)
    (hmw : seedV s ≤ 4) :
    iteratedDeriv 2 Real.smoothTransition ((1 - s) / 2) ∈ Set.Icc (ttwoLower s) (ttwoUpper s) := by
  have hs01 : (0 : ℝ) < (1 - s) / 2 := by linarith
  have hs11 : (1 - s) / 2 < 1 := by linarith
  have hsw : seedULo s 4 ≤ seedU s ∧ seedU s ≤ seedUHi s 4 :=
    seedU_sandwich_exp (a := s) (b := s) h0 le_rfl h1 (m₁ := 4) (by norm_num) hmw
      (m₂ := 4) (by norm_num) hmw s ⟨le_rfl, le_rfl⟩
  have huL0 : 0 ≤ seedULo s 4 := seedULo_nonneg (le_of_lt h0) h1 (by norm_num) hmw
  have huH0 : 0 ≤ seedUHi s 4 := le_trans (le_trans huL0 hsw.1) hsw.2
  have huH1 : seedUHi s 4 ≤ 1 := seedUHi_le_one (le_of_lt h0) h1 hmw
  have huHm1 : -1 ≤ seedUHi s 4 := seedUHi_ge_neg_one (le_of_lt h0) h1
  set u : ℝ := seedU s with hu
  have hu_eq : 1 - 2 * Real.smoothTransition ((1 - s) / 2) = u := by
    rw [hu]
    exact (seedU_eq_reflect s h0 h1).symm
  have hTeq : Real.smoothTransition ((1 - s) / 2) = (1 - u) / 2 := by linarith
  have hT2eq : iteratedDeriv 2 Real.smoothTransition ((1 - s) / 2) = seedP s u / 4 := by
    rw [iteratedDeriv_two_smoothTransition_eq ((1 - s) / 2) hs01 hs11,
      windowGain_reflect_eq s h0 h1, windowGainSlope_reflect_eq s h0 h1]
    rw [← gainStd, ← gainSlopeStd]
    unfold seedP
    rw [hu_eq, hTeq]
    ring
  have hdiff : ∀ v ∈ Set.Icc (seedULo s 4) (seedUHi s 4), DifferentiableAt ℝ (seedP s) v := by
    intro v _
    unfold seedP
    exact ((differentiableAt_const (1 : ℝ)).sub ((hasDerivAt_id v).differentiableAt.pow 2)).mul
      ((((hasDerivAt_id v).differentiableAt.mul_const (gainStd s ^ 2)).add
        (differentiableAt_const (gainSlopeStd s))))
  have hderiv_bound : ∀ v ∈ Set.Icc (seedULo s 4) (seedUHi s 4),
      ‖deriv (seedP s) v‖ ≤ ttwoMp s := by
    intro v hv
    have hvlo : 0 ≤ v := le_trans huL0 hv.1
    have hvhi : v ≤ seedUHi s 4 := hv.2
    have hv2 : v ^ 2 ≤ seedUHi s 4 ^ 2 := pow_le_pow_left₀ hvlo hvhi 2
    have hv1 : v ^ 2 ≤ 1 := by nlinarith [huH1, huHm1, hv2]
    have hG0 : 0 ≤ gainStd s ^ 2 := sq_nonneg _
    have hderiv : deriv (seedP s) v =
        -2 * v * (v * gainStd s ^ 2 + gainSlopeStd s) + (1 - v ^ 2) * gainStd s ^ 2 := by
      have h : HasDerivAt (fun w : ℝ => (1 - w ^ 2) * (w * gainStd s ^ 2 + gainSlopeStd s))
          (-2 * v * (v * gainStd s ^ 2 + gainSlopeStd s) + (1 - v ^ 2) * gainStd s ^ 2) v := by
        have h1 : HasDerivAt (fun w : ℝ => 1 - w ^ 2) (-(2 * v)) v := by
          simpa using (hasDerivAt_const (x := v) (c := (1 : ℝ))).sub (hasDerivAt_pow 2 v)
        have h2 : HasDerivAt (fun w : ℝ => w * gainStd s ^ 2 + gainSlopeStd s)
            (gainStd s ^ 2) v := by
          have h3 : HasDerivAt (fun w : ℝ => w * gainStd s ^ 2) (gainStd s ^ 2) v := by
            simpa using (hasDerivAt_id v).mul_const (gainStd s ^ 2)
          exact h3.add_const (gainSlopeStd s)
        have h4 := h1.mul h2
        convert h4 using 1
        ring
      exact h.deriv
    rw [hderiv, Real.norm_eq_abs]
    have hb1 : |v * gainStd s ^ 2 + gainSlopeStd s| ≤ v * gainStd s ^ 2 + |gainSlopeStd s| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith [neg_abs_le (gainSlopeStd s),
          mul_nonneg (show (0 : ℝ) ≤ 2 * v by linarith) hG0]
      · linarith [le_abs_self (gainSlopeStd s)]
    have hlower :
        -(2 * v * |v * gainStd s ^ 2 + gainSlopeStd s| + (1 - v ^ 2) * gainStd s ^ 2) ≤
          -2 * v * (v * gainStd s ^ 2 + gainSlopeStd s) + (1 - v ^ 2) * gainStd s ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left (le_abs_self (v * gainStd s ^ 2 + gainSlopeStd s))
        (show (0 : ℝ) ≤ 2 * v by linarith)
      have hnn : 0 ≤ (1 - v ^ 2) * gainStd s ^ 2 := mul_nonneg (by linarith [hv1]) hG0
      linarith [h1, hnn]
    have hupper :
        -2 * v * (v * gainStd s ^ 2 + gainSlopeStd s) + (1 - v ^ 2) * gainStd s ^ 2 ≤
          2 * v * |v * gainStd s ^ 2 + gainSlopeStd s| + (1 - v ^ 2) * gainStd s ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_left (neg_le_abs (v * gainStd s ^ 2 + gainSlopeStd s))
        (show (0 : ℝ) ≤ 2 * v by linarith)
      linarith [h1]
    calc |-2 * v * (v * gainStd s ^ 2 + gainSlopeStd s) + (1 - v ^ 2) * gainStd s ^ 2|
        ≤ 2 * v * |v * gainStd s ^ 2 + gainSlopeStd s| + (1 - v ^ 2) * gainStd s ^ 2 :=
          abs_le.mpr ⟨hlower, hupper⟩
      _ ≤ 2 * v * (v * gainStd s ^ 2 + |gainSlopeStd s|) + (1 - v ^ 2) * gainStd s ^ 2 := by
          have h25 := mul_le_mul_of_nonneg_left hb1 (show (0 : ℝ) ≤ 2 * v by linarith)
          linarith [h25]
      _ ≤ ttwoMp s := by
          unfold ttwoMp
          have h1 : gainStd s ^ 2 * (1 + v ^ 2) ≤ gainStd s ^ 2 * (1 + 3 * seedUHi s 4 ^ 2) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hv2, sq_nonneg (seedUHi s 4)]) hG0
          have h2 : 2 * v * |gainSlopeStd s| ≤ 2 * seedUHi s 4 * |gainSlopeStd s| :=
            mul_le_mul_of_nonneg_right (by linarith [hvhi]) (abs_nonneg _)
          nlinarith [h1, h2]
  have hMp0 : 0 ≤ ttwoMp s := by
    unfold ttwoMp
    have h1 : 0 ≤ gainStd s ^ 2 * (1 + 3 * seedUHi s 4 ^ 2) :=
      mul_nonneg (sq_nonneg _) (by nlinarith [huH0])
    have h2 : 0 ≤ 2 * seedUHi s 4 * |gainSlopeStd s| :=
      mul_nonneg (mul_nonneg (by norm_num) huH0) (abs_nonneg _)
    linarith [h1, h2]
  have hmvt := (convex_Icc (seedULo s 4) (seedUHi s 4)).norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv_bound (Set.left_mem_Icc.mpr (le_trans hsw.1 hsw.2)) ⟨hsw.1, hsw.2⟩
  have hnorm : ‖u - seedULo s 4‖ = u - seedULo s 4 :=
    Real.norm_of_nonneg (by linarith [hsw.1])
  have hstep : ‖seedP s u - seedP s (seedULo s 4)‖ ≤
      ttwoMp s * (seedUHi s 4 - seedULo s 4) := by
    calc ‖seedP s u - seedP s (seedULo s 4)‖ ≤ ttwoMp s * ‖u - seedULo s 4‖ := hmvt
      _ = ttwoMp s * (u - seedULo s 4) := by rw [hnorm]
      _ ≤ ttwoMp s * (seedUHi s 4 - seedULo s 4) :=
          mul_le_mul_of_nonneg_left (by linarith [hsw.2]) hMp0
  have habs : |seedP s u - seedP s (seedULo s 4)| ≤
      ttwoMp s * (seedUHi s 4 - seedULo s 4) := by
    rw [← Real.norm_eq_abs]
    exact hstep
  have hb := abs_le.mp habs
  rw [Set.mem_Icc]
  constructor
  · rw [hT2eq, ttwoLower]
    linarith [hb.1]
  · rw [hT2eq, ttwoUpper]
    linarith [hb.2]

theorem iteratedDeriv_three_abs_le_gapBound {y : ℝ}
    (hy : y ∈ Set.Icc (1091279 / 5000000 : ℝ) (4365117 / 20000000)) :
    ‖iteratedDeriv 3 Real.smoothTransition y‖ ≤ gapBound := by
  have hs : (1 - 2 * y) ∈ Set.Icc (5634883 / 10 ^ 7 : ℝ) (1408721 / 2500000) :=
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hsw := seedU_sandwich_exp (a := (5634883 / 10 ^ 7 : ℝ)) (b := 1408721 / 2500000)
    (by norm_num) (by norm_num) (by norm_num) (m₁ := 4) (by norm_num) (by norm_num [seedV])
    (m₂ := 4) (by norm_num) (by norm_num [seedV]) (1 - 2 * y) hs
  have hm : seedBracket (1 - 2 * y) ∈ Set.Icc gapLo gapHi :=
    seedBracket_mem_Icc (a := (5634883 / 10 ^ 7 : ℝ)) (b := 1408721 / 2500000)
      (uL := seedULo (5634883 / 10 ^ 7) 4) (uH := seedUHi (1408721 / 2500000) 4)
      (by norm_num) (by norm_num) hs
      (seedULo_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num [seedV]))
      hsw.1 hsw.2
  have hple : |gapLo| ≤ |gapHi| := by
    rw [gapLo, gapHi]
    norm_num [thirdOrderLeading, seedBracketUpper, seedBracketLower, seedULo, seedUHi,
      seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  have hPabs : |seedBracket (1 - 2 * y)| ≤ |gapHi| :=
    abs_le.mpr ⟨by linarith [hm.1, neg_le_abs gapLo, hple], by linarith [hm.2, le_abs_self gapHi]⟩
  have hs0 : 0 < 1 - 2 * y := by linarith [hy.2]
  have hs1 : 1 - 2 * y < 1 := by linarith [hy.1]
  have hfac := iteratedDeriv_three_smoothTransition_eq_seedBracket (1 - 2 * y) hs0 hs1
  rw [show (1 - (1 - 2 * y)) / 2 = y by ring] at hfac
  have hT0 : 0 < Real.smoothTransition y := Real.smoothTransition.pos_of_pos (by linarith [hy.1])
  have hT1 : Real.smoothTransition y < 1 :=
      Real.smoothTransition.lt_one_of_lt_one (by linarith [hy.2])
  have hprod4 : Real.smoothTransition y * (1 - Real.smoothTransition y) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (Real.smoothTransition y - 1 / 2)]
  have hden : 0 < (1 - (1 - 2 * y) ^ 2) ^ 6 := by
    have h : 0 < 1 - (1 - 2 * y) ^ 2 := by nlinarith [hs0, hs1]
    exact pow_pos h 6
  have step1 : (1 - (1 - 2 * y) ^ 2) ^ 6 * ‖iteratedDeriv 3 Real.smoothTransition y‖ =
      |(1 - (1 - 2 * y) ^ 2) ^ 6 * iteratedDeriv 3 Real.smoothTransition y| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hden]
  have step2 : |(1 - (1 - 2 * y) ^ 2) ^ 6 * iteratedDeriv 3 Real.smoothTransition y| ≤
      16 * |seedBracket (1 - 2 * y)| := by
    rw [hfac, abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 64 by norm_num),
      abs_of_nonneg (mul_nonneg hT0.le (by linarith))]
    have hb0 : 0 ≤ |seedBracket (1 - 2 * y)| := abs_nonneg _
    nlinarith [hprod4, hb0]
  have step3 : 16 * |seedBracket (1 - 2 * y)| ≤ 16 * |gapHi| := by
    have := mul_le_mul_of_nonneg_left hPabs (show (0 : ℝ) ≤ 16 by norm_num)
    linarith [this]
  have step4 : (1 - (1408721 / 2500000) ^ 2) ^ 6 ≤ (1 - (1 - 2 * y) ^ 2) ^ 6 := by
    have hsle : (1 - 2 * y) ≤ 1408721 / 2500000 := by linarith [hy.1]
    have hsge : 0 ≤ 1 - 2 * y := le_of_lt hs0
    have hsq : (1 - 2 * y) ^ 2 ≤ (1408721 / 2500000) ^ 2 := pow_le_pow_left₀ hsge hsle 2
    have h1 : 1 - (1408721 / 2500000) ^ 2 ≤ 1 - (1 - 2 * y) ^ 2 := by linarith
    have h0 : (0 : ℝ) ≤ 1 - (1408721 / 2500000) ^ 2 := by norm_num
    exact pow_le_pow_left₀ h0 h1 6
  have hgb0 : 0 ≤ gapBound := by
    rw [gapBound]
    apply div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
    positivity
  have hsc6 : (0 : ℝ) < (1 - (1408721 / 2500000) ^ 2) ^ 6 := by positivity
  have hgapB : (1 - (1408721 / 2500000) ^ 2) ^ 6 * gapBound = 16 * |gapHi| := by
    rw [gapBound]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ (16 * |gapHi|) (ne_of_gt hsc6)
  have hfinal : (1 - (1 - 2 * y) ^ 2) ^ 6 * ‖iteratedDeriv 3 Real.smoothTransition y‖ ≤
      (1 - (1 - 2 * y) ^ 2) ^ 6 * gapBound := by
    refine le_trans (le_of_eq step1) (le_trans step2 (le_trans step3 ?_))
    calc 16 * |gapHi| = (1 - (1408721 / 2500000) ^ 2) ^ 6 * gapBound := hgapB.symm
      _ ≤ (1 - (1 - 2 * y) ^ 2) ^ 6 * gapBound :=
          mul_le_mul_of_nonneg_right step4 hgb0
  exact le_of_mul_le_mul_left hfinal hden

theorem derivOrderL1_smoothSeed_three_mem_Icc :
    derivOrderL1 3 smoothSeed ∈ Set.Icc (787283384 / 10 ^ 7) (787283385 / 10 ^ 7) := by
  have hcont : Continuous fun y : ℝ => ‖iteratedDeriv 3 Real.smoothTransition y‖ :=
    continuous_norm.comp (contDiff_one_iteratedDeriv_smoothTransition 3).continuous
  have hreflect : ∫ y in (1 / 2 : ℝ)..1, ‖iteratedDeriv 3 Real.smoothTransition y‖ =
      ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (f := fun y : ℝ => ‖iteratedDeriv 3 Real.smoothTransition y‖) (a := (0 : ℝ))
      (b := 1 / 2) (1 : ℝ)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, sub_zero] at hcomp
    rw [← hcomp]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hu
    exact norm_iteratedDeriv_three_one_sub ⟨hu.1, hu.2⟩
  have hoff : ∀ y : ℝ, y ∉ Set.Icc (0 : ℝ) 1 →
      ‖iteratedDeriv 3 Real.smoothTransition y‖ = 0 := by
    intro y hy
    have hzero : iteratedDeriv 3 Real.smoothTransition y = 0 := by
      by_contra hne
      exact hy (support_iteratedDeriv_smoothTransition_subset 3 (by norm_num)
        (Function.mem_support.mpr hne))
    rw [hzero, norm_zero]
  have hfull : ∫ y : ℝ, ‖iteratedDeriv 3 Real.smoothTransition y‖ =
      2 * ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
    calc ∫ y : ℝ, ‖iteratedDeriv 3 Real.smoothTransition y‖
        = ∫ y in Set.Icc (0 : ℝ) 1, ‖iteratedDeriv 3 Real.smoothTransition y‖ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
      _ = ∫ y in (0 : ℝ)..1, ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      _ = (∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖) +
          ∫ y in (1 / 2 : ℝ)..1, ‖iteratedDeriv 3 Real.smoothTransition y‖ :=
          (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
            (hcont.intervalIntegrable 0 (1 / 2))
            (hcont.intervalIntegrable (1 / 2) 1)).symm
      _ = (∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖) +
          ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
          rw [hreflect]
      _ = 2 * ∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖ := by
          ring
  have hsplit : (∫ y in (0 : ℝ)..(1 / 2), ‖iteratedDeriv 3 Real.smoothTransition y‖) =
      (∫ y in (0 : ℝ)..(1091279 / 5000000), ‖iteratedDeriv 3 Real.smoothTransition y‖) +
        (∫ y in (1091279 / 5000000)..(4365117 / 20000000),
          ‖iteratedDeriv 3 Real.smoothTransition y‖) +
        (∫ y in (4365117 / 20000000)..(1 / 2 : ℝ),
          ‖iteratedDeriv 3 Real.smoothTransition y‖) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := fun y : ℝ => ‖iteratedDeriv 3 Real.smoothTransition y‖)
      (hcont.intervalIntegrable (0 : ℝ) (1091279 / 5000000))
      (hcont.intervalIntegrable (1091279 / 5000000) (1 / 2))
    have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := fun y : ℝ => ‖iteratedDeriv 3 Real.smoothTransition y‖)
      (hcont.intervalIntegrable (1091279 / 5000000) (4365117 / 20000000))
      (hcont.intervalIntegrable (4365117 / 20000000) (1 / 2))
    linarith [h1, h2]
  have hxc0 : (0 : ℝ) ≤ 1091279 / 5000000 := by norm_num
  have hxd12 : (4365117 / 20000000 : ℝ) ≤ 1 / 2 := by norm_num
  have hI1 : (∫ y in (0 : ℝ)..(1091279 / 5000000), ‖iteratedDeriv 3 Real.smoothTransition y‖) =
      iteratedDeriv 2 Real.smoothTransition (1091279 / 5000000) := by
    have hcongr : (∫ y in (0 : ℝ)..(1091279 / 5000000),
        ‖iteratedDeriv 3 Real.smoothTransition y‖) =
        ∫ y in (0 : ℝ)..(1091279 / 5000000), iteratedDeriv 3 Real.smoothTransition y := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le hxc0] at hy
      exact Real.norm_of_nonneg (iteratedDeriv_three_nonneg_of_Icc_zero_x_c hy)
    rw [hcongr]
    have hder : (∫ y in (0 : ℝ)..(1091279 / 5000000),
        iteratedDeriv 3 Real.smoothTransition y) =
        ∫ y in (0 : ℝ)..(1091279 / 5000000),
          deriv (iteratedDeriv 2 Real.smoothTransition) y := by
      rw [iteratedDeriv_three_smoothTransition_eq_deriv_deriv]
    rw [hder, intervalIntegral.integral_deriv_of_contDiffOn_Icc
      ((contDiff_one_iteratedDeriv_smoothTransition 2).contDiffOn) hxc0,
      iteratedDeriv_two_smoothTransition_zero]
    ring
  have hI3 : (∫ y in (4365117 / 20000000)..(1 / 2 : ℝ),
      ‖iteratedDeriv 3 Real.smoothTransition y‖) =
      iteratedDeriv 2 Real.smoothTransition (4365117 / 20000000) := by
    have hcongr : (∫ y in (4365117 / 20000000)..(1 / 2 : ℝ),
        ‖iteratedDeriv 3 Real.smoothTransition y‖) =
        ∫ y in (4365117 / 20000000)..(1 / 2 : ℝ),
          -iteratedDeriv 3 Real.smoothTransition y := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [Set.uIcc_of_le hxd12] at hy
      exact Real.norm_of_nonpos (iteratedDeriv_three_nonpos_of_Icc_x_d_half hy)
    rw [hcongr, intervalIntegral.integral_neg]
    have hder : (∫ y in (4365117 / 20000000)..(1 / 2 : ℝ),
        iteratedDeriv 3 Real.smoothTransition y) =
        ∫ y in (4365117 / 20000000)..(1 / 2 : ℝ),
          deriv (iteratedDeriv 2 Real.smoothTransition) y := by
      rw [iteratedDeriv_three_smoothTransition_eq_deriv_deriv]
    rw [hder, intervalIntegral.integral_deriv_of_contDiffOn_Icc
      ((contDiff_one_iteratedDeriv_smoothTransition 2).contDiffOn) hxd12,
      iteratedDeriv_two_smoothTransition_half]
    ring
  have hgap0 : 0 ≤ (∫ y in (1091279 / 5000000)..(4365117 / 20000000),
      ‖iteratedDeriv 3 Real.smoothTransition y‖) := by
    have hle : (1091279 / 5000000 : ℝ) ≤ 4365117 / 20000000 := by norm_num
    have hmono := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const (μ := volume) (c := (0 : ℝ)) (hc := by finiteness))
      (hcont.intervalIntegrable (1091279 / 5000000) (4365117 / 20000000))
      (fun y hy => by
        show (0 : ℝ) ≤ ‖iteratedDeriv 3 Real.smoothTransition y‖
        positivity)
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_zero] at hmono
    exact hmono
  have hgap1 : (∫ y in (1091279 / 5000000)..(4365117 / 20000000),
      ‖iteratedDeriv 3 Real.smoothTransition y‖) ≤
      gapBound * (4365117 / 20000000 - 1091279 / 5000000) := by
    have hle : (1091279 / 5000000 : ℝ) ≤ 4365117 / 20000000 := by norm_num
    have hmono := intervalIntegral.integral_mono_on hle
      (hcont.intervalIntegrable (1091279 / 5000000) (4365117 / 20000000))
      (intervalIntegrable_const (μ := volume))
      (fun y hy => iteratedDeriv_three_abs_le_gapBound hy)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith [hmono]
  have hT2c := iteratedDeriv_two_smoothTransition_mem_Icc (s := 1408721 / 2500000)
    (by norm_num) (by norm_num) (by norm_num [seedV])
  rw [show (1 - 1408721 / 2500000) / 2 = (1091279 / 5000000 : ℝ) by norm_num] at hT2c
  have hT2d := iteratedDeriv_two_smoothTransition_mem_Icc (s := 5634883 / 10 ^ 7)
    (by norm_num) (by norm_num) (by norm_num [seedV])
  rw [show (1 - 5634883 / 10 ^ 7) / 2 = (4365117 / 20000000 : ℝ) by norm_num] at hT2d
  have hbound : derivOrderL1 3 smoothSeed ∈ Set.Icc
      (4 * (ttwoLower (1408721 / 2500000) + ttwoLower (5634883 / 10 ^ 7)))
      (4 * (ttwoUpper (1408721 / 2500000) + ttwoUpper (5634883 / 10 ^ 7) +
        gapBound * (4365117 / 20000000 - 1091279 / 5000000))) := by
    rw [derivOrderL1_smoothSeed_eq 3 (by norm_num), hfull, hsplit, Set.mem_Icc]
    constructor
    · ring_nf
      linarith [hT2c.1, hT2d.1, hI1, hI3, hgap0]
    · ring_nf
      linarith [hT2c.2, hT2d.2, hI1, hI3, hgap1]
  refine ⟨le_trans ?_ hbound.1, le_trans hbound.2 ?_⟩
  · norm_num [ttwoLower, ttwoUpper, ttwoMp, seedP, gainStd, gainSlopeStd, seedULo, seedUHi,
      seedExpLo,
      seedExpHi, seedV, expTaylor, expTail, Finset.sum_range_succ]
  · norm_num [ttwoLower, ttwoUpper, ttwoMp, gapBound, gapLo, gapHi, seedP, gainStd,
      gainSlopeStd, seedULo, seedUHi, seedExpLo, seedExpHi, seedV, expTaylor, expTail,
      thirdOrderLeading, seedBracketUpper, seedBracketLower, Finset.sum_range_succ]
end

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
