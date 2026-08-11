import ConnesWeilRH.Dev.Wall14PlateauExplicitF
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Wall14PlateauFDeriv

The convolution derivative of the explicit plateau bumped square `bumpF`:
`bumpF` is `C^1`, with `bumpF'(x) = (bumpReal ⋆ deriv bumpReal)(x)`, obtained
via `HasCompactSupport.hasDerivAt_convolution_right`.  The near-band analytic
leaf is the sharp pointwise bound `|bumpF'(x)| <= 1` on `[0,1]` (the plateau
total variation is exactly 2, split by the even plateau), which yields
`|A - bumpF(y)| <= y` and finally the `hI` closure.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace Wall14Plateau

open MeasureTheory
open scoped Convolution Topology Set Interval

/-- The real scalar multiplication bilinear map used in the convolution. -/
noncomputable def Lmul : (ℝ →L[ℝ] (ℝ →L[ℝ] ℝ)) := ContinuousLinearMap.mul ℝ ℝ

/-- `bumpReal` is `C^1`. -/
lemma bumpReal_contDiff_one : ContDiff ℝ 1 (fun x : ℝ => bumpReal x) :=
  bumpEx_contDiff.of_le (by norm_num)

/-- `bumpF` equals the convolution square. -/
theorem bumpF_eq_convolution (y : ℝ) :
    bumpF y = (bumpReal ⋆[Lmul, volume] bumpReal) y := by
  rw [bumpF_eq_conv]
  rw [convolution_def]
  rfl

/-- The derivative of `bumpF` (a convolution of `bumpReal` with the derivative). -/
noncomputable def bumpFderiv (x : ℝ) : ℝ :=
  (bumpReal ⋆[Lmul, volume] deriv (fun u : ℝ => bumpReal u)) x

/-- `bumpF` is differentiable with derivative `bumpFderiv`. -/
theorem bumpF_hasDerivAt (x : ℝ) : HasDerivAt bumpF (bumpFderiv x) x := by
  have hbase : HasDerivAt (fun z : ℝ => (bumpReal ⋆[Lmul, volume] bumpReal) z)
      ((bumpReal ⋆[Lmul, volume] deriv (fun u : ℝ => bumpReal u)) x) x := by
    apply HasCompactSupport.hasDerivAt_convolution_right
    · exact bumpReal_continuous.locallyIntegrable
    · exact bumpReal_hasCompactSupport
    · exact bumpReal_contDiff_one
  have hf : bumpF = (fun z : ℝ => (bumpReal ⋆[Lmul, volume] bumpReal) z) := by
    funext z
    rw [bumpF_eq_convolution]
  rw [hf]
  simpa [bumpFderiv] using hbase

/-- `bumpReal` is nonincreasing in `|x|` (equivalently in `x^2`): `|x| <= |y|` implies
`bumpReal y <= bumpReal x`.  This is the derivative-Lipschitz engine: F = f*f is even, and
`|F'| <= 1` follows by dropping the `f(x+u)` term. -/
lemma bumpReal_mono_abs (x y : ℝ) (habs : |x| ≤ |y|) :
    bumpReal y ≤ bumpReal x := by
  unfold bumpReal bumpEx
  have hx2 : (|x| : ℝ) ^ 2 ≤ (|y| : ℝ) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg x) habs 2
  have hsq : x ^ 2 ≤ y ^ 2 := by
    simpa [sq_abs] using hx2
  have h1 : (x ^ 2 - bSq) / (1 - bSq) ≤ (y ^ 2 - bSq) / (1 - bSq) := by
    rw [div_le_div_iff₀ one_sub_bSq_pos one_sub_bSq_pos]
    have hxym : x ^ 2 - bSq <= y ^ 2 - bSq := sub_le_sub_right hsq bSq
    exact mul_le_mul_of_nonneg_right hxym (le_of_lt one_sub_bSq_pos)
  have hm : Real.smoothTransition ((x ^ 2 - bSq) / (1 - bSq)) ≤
      Real.smoothTransition ((y ^ 2 - bSq) / (1 - bSq)) :=
    Real.smoothTransition.monotone h1
  linarith

/-- `bumpReal t <= 1`. -/
lemma bumpReal_le_one (t : ℝ) : bumpReal t ≤ 1 := bumpEx_le_one t


/-- the plateau value `bumpReal (9/10) = 1`. -/
lemma bumpReal_b0_eq_one : bumpReal (9 / 10 : ℝ) = 1 := by
  rw [bumpReal]
  exact bump_eq_one_of_sq_le (9 / 10 : ℝ) (by unfold bSq bplateau; norm_num)

/-- `bumpReal 1 = 0`. -/
lemma bumpReal_one_eq_zero : bumpReal 1 = 0 := by
  rw [bumpReal]
  exact bumpEx_eq_zero_of_one_le_sq 1 (by norm_num)

/-- Derivative of the even bump is odd: `(deriv bumpReal)(-x) = -(deriv bumpReal)(x)`. -/
theorem deriv_bumpReal_neg (x : ℝ) :
    deriv (fun t : ℝ => bumpReal t) (-x) = -deriv (fun t : ℝ => bumpReal t) x := by
  have hda : HasDerivAt (fun t : ℝ => bumpReal (-t))
      (-(deriv (fun u : ℝ => bumpReal u) (-x))) x := by
    simpa using (bumpReal_differentiable (-x)).hasDerivAt.comp x (hasDerivAt_neg x)
  have hfunc : (fun t : ℝ => bumpReal (-t)) = (fun t : ℝ => bumpReal t) := by
    funext t; exact bumpReal_even t
  have hz : deriv (fun t : ℝ => bumpReal t) x = -deriv (fun u : ℝ => bumpReal u) (-x) := by
    have hfall : deriv (fun t : ℝ => bumpReal (-t)) x =
        -deriv (fun u : ℝ => bumpReal u) (-x) := hda.deriv
    simpa [hfunc] using hfall
  linarith



/-! ## The derivative `bd` of the bump and its structural facts. -/

/-- The derivative of the plateau bump: `bd u = (d/du) bumpReal u`. -/
noncomputable def bd (u : ℝ) : ℝ := deriv (fun w : ℝ => bumpReal w) u

/-- `bd` is identically zero on the open plateau `|u| < 9/10`. -/
theorem bd_plateau_zero (u : ℝ) (hu : |u| < (9 / 10 : ℝ)) : bd u = 0 := by
  have h_ev : (fun x : ℝ => bumpReal x) =ᶠ[𝓝 u] (fun _ : ℝ => (1 : ℝ)) := by
    rw [Filter.EventuallyEq]
    have hset : Set.Ioo (-(9 / 10 : ℝ)) (9 / 10 : ℝ) ∈ 𝓝 u := by
      exact isOpen_Ioo.mem_nhds (abs_lt.mp hu)
    filter_upwards [hset] with x hx
    have hxa : |x| < (9/10 : ℝ) := abs_lt.mpr hx
    exact bumpReal_eq_one_of_abs_le x (le_of_lt hxa)
  have hder : HasDerivAt (fun x : ℝ => bumpReal x) (0 : ℝ) u := by
    simpa using ((hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq h_ev)
  unfold bd
  exact hder.deriv

/-- `bd` is zero on the outer region `|u| > 1`. -/
theorem bd_outer_zero (u : ℝ) (hu : (1 : ℝ) < |u|) : bd u = 0 := by
  have h_ev : (fun x : ℝ => bumpReal x) =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
    rw [Filter.EventuallyEq]
    have hset : {x : ℝ | (1 : ℝ) < |x|} ∈ 𝓝 u := by
      exact (isOpen_lt continuous_const continuous_abs).mem_nhds hu
    filter_upwards [hset] with x hx
    exact bumpReal_eq_zero_of_abs_ge x (le_of_lt hx)
  have hder : HasDerivAt (fun x : ℝ => bumpReal x) (0 : ℝ) u := by
    simpa using ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq h_ev)
  unfold bd
  exact hder.deriv

/-- `bd` is odd. -/
theorem bd_neg (u : ℝ) : bd (-u) = -bd u := by
  unfold bd
  exact deriv_bumpReal_neg u

/-- `bd` is continuous (it is the derivative of a `C^1` function). -/
lemma bd_continuous : Continuous bd := by
  have hcf : Continuous (fun x : ℝ => fderiv ℝ (fun w : ℝ => bumpReal w) x) :=
    bumpReal_contDiff_one.continuous_fderiv (by norm_num)
  have hbc : Continuous (fun u : ℝ => ((fderiv ℝ (fun w : ℝ => bumpReal w) u) : ℝ →L[ℝ] ℝ) 1) := by
    fun_prop
  simpa [bd] using hbc

/-- The convolution derivative equals the integral `∫ bumpReal t · bd(x − t)`. -/
theorem bumpFderiv_eq_integral (x : ℝ) :
    bumpFderiv x = ∫ t : ℝ, bumpReal t * bd (x - t) := by
  unfold bumpFderiv
  rw [convolution_def]
  simp [Lmul, bd]

/-- The derivative in the shifted variable: `bumpFderiv x = ∫ bumpReal(x − u)·bd b`. -/
theorem bumpFderiv_custom_sub (x : ℝ) :
    bumpFderiv x = ∫ u : ℝ, bumpReal (x - u) * bd u := by
  rw [bumpFderiv_eq_integral]
  have hH : Continuous (fun w : ℝ => bumpReal (x - w) * bd w) := by
    have h1 : Continuous (fun w : ℝ => x - w) := continuous_const.sub continuous_id
    exact (bumpReal_continuous.comp h1).mul bd_continuous
  simpa using (bumpIntegralReflectFullCont hH x)

/-! ## The `bd`-band reduction of `bumpFderiv` to the two `(9/10,1)`-band survivors.
RH NOT claimed. -/

/-- If `f = 0` on the open interval `(a,b)`, the interval integral is zero. -/
theorem interval_integral_eq_zero_of_Ioo {a b : ℝ} (ha : a < b) {f : ℝ → ℝ}
    (hf : ∀ x, a < x → x < b → f x = 0) :
    (∫ x in a..b, f x) = 0 := by
  rw [intervalIntegral.integral_of_le (le_of_lt ha)]
  have hset : Set.Ioo a b =ᵐ[volume] Set.Ioc a b := by
    simpa using (MeasureTheory.Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := a) (b := b))
  calc
    (∫ x in (Set.Ioc a b : Set ℝ), f x ∂volume)
        = ∫ x in (Set.Ioo a b), f x ∂volume := (setIntegral_congr_set hset).symm
    _ = ∫ x in (Set.Ioo a b), (fun _ : ℝ => (0 : ℝ)) x ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro x hx; exact hf x hx.1 hx.2
    _ = 0 := by simp

/-- The folded parent integrand `bumpReal(x-u) * bd u` and its structural facts. -/
noncomputable def bb (x : ℝ) : ℝ → ℝ := fun u => bumpReal (x - u) * bd u

lemma bb_cont (x : ℝ) : Continuous (bb x) := by
  unfold bb
  have h1 : Continuous (fun w : ℝ => x - w) := continuous_const.sub continuous_id
  exact (bumpReal_continuous.comp h1).mul bd_continuous

lemma bb_int (x) (a b : ℝ) : IntervalIntegrable (bb x) volume a b := (bb_cont x).intervalIntegrable a b

lemma bd_ne_zero_imp_abs_le_one (u : ℝ) (h : bd u ≠ 0) : |u| ≤ (1 : ℝ) := by
  by_contra hc; exact h (bd_outer_zero u (lt_of_not_ge hc))

lemma bb_outer_zero (x : ℝ) (u : ℝ) (hu : (1 : ℝ) < |u|) : bb x u = 0 := by
  unfold bb; simp [bd_outer_zero u hu]

lemma bb_plateau_zero (x : ℝ) (u : ℝ) (hu : |u| < (9 / 10 : ℝ)) : bb x u = 0 := by
  unfold bb; simp [bd_plateau_zero u hu]

lemma bb_support_subset (x : ℝ) : Function.support (bb x) ⊆ Set.Ioc (-2 : ℝ) 2 := by
  intro u hu
  have hb : bb x u ≠ 0 := hu
  unfold bb at hb
  have hbd : bd u ≠ 0 := by intro hz; exact hb (by simp [hz])
  have hub : |u| ≤ (1 : ℝ) := bd_ne_zero_imp_abs_le_one u hbd
  constructor
  · have : -(1 : ℝ) ≤ u := (abs_le.mp hub).1; linarith
  · have : u ≤ (1 : ℝ) := (abs_le.mp hub).2; linarith

lemma bb_integral_reduce (x : ℝ) :
    (∫ u : ℝ, bb x u) = ∫ u in (-2)..(2), bb x u := by
  exact (intervalIntegral.integral_eq_integral_of_support_subset (bb_support_subset x)).symm

lemma bb_outer_left_interval (x : ℝ) : (∫ u in (-2)..(-1), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (-2 : ℝ)) (b := (-1 : ℝ))
  · linarith
  · intro u hu1 hu2
    have hu : |u| = -u := abs_of_neg (by linarith)
    have : (1 : ℝ) < |u| := by rw [hu]; linarith
    exact bb_outer_zero x u this

lemma bb_plateau_mid (x : ℝ) : (∫ u in (-(9/10 : ℝ))..(9/10), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (-(9/10 : ℝ))) (b := (9/10 : ℝ))
  · norm_num
  · intro u hu1 hu2
    exact bb_plateau_zero x u (abs_lt.mpr ⟨hu1, hu2⟩)

lemma bb_outer_right_interval (x : ℝ) : (∫ u in (1)..(2), bb x u) = 0 := by
  apply interval_integral_eq_zero_of_Ioo (a := (1 : ℝ)) (b := (2 : ℝ))
  · linarith
  · intro u hu1 hu2
    have huabs : (1 : ℝ) < |u| := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u)]; linarith
    exact bb_outer_zero x u huabs

theorem bb_chain (x : ℝ) :
    (∫ u in (-2)..2, bb x u)
      = (∫ u in (-2)..(-1), bb x u) + (∫ u in (-1)..(-(9/10 : ℝ)), bb x u)
        + (∫ u in (-(9/10 : ℝ))..(9/10), bb x u) + (∫ u in (9/10)..1, bb x u)
        + (∫ u in (1)..2, bb x u) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (bb_int x (-2) 1) (bb_int x 1 2)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (bb_int x (-2) (9/10)) (bb_int x (9/10) 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (bb_int x (-2) (-(9/10 : ℝ))) (bb_int x (-(9/10 : ℝ)) (9/10))]
  rw [← intervalIntegral.integral_add_adjacent_intervals (bb_int x (-2) (-1)) (bb_int x (-1) (-(9/10 : ℝ)))]

theorem bb_two_band (x : ℝ) :
    (∫ u in (-2)..2, bb x u) = (∫ u in (-1)..(-(9/10 : ℝ)), bb x u) + (∫ u in (9/10)..1, bb x u) := by
  have hchain := bb_chain x
  rw [bb_outer_left_interval x, bb_outer_right_interval x, bb_plateau_mid x] at hchain
  simp at hchain
  exact hchain


/-! ## The |bumpF'|<=1 near-band bound.

`bumpFderiv x` reduces (above) to a single band integral over `u in (9/10,1)` of
the signed bracket `(bumpReal(x-u) - bumpReal(x+u)) * bd u`.  On that band, with
`0<=x<=1`: the bracket is `(bumpReal(x-u)-bumpReal(x+u)) in [0,1]` and the
derivative `bd u <= 0`, so `bumpFderiv x <= 0` and its absolute value is bounded
by `int_{9/10}^1 (-bd) = bumpReal(9/10) - bumpReal(1) = 1`.  RH NOT claimed.
-/

/-- change of variable `u -> -u` on an interval: `int a..b F = int -b..-a F(-u)`. -/
lemma pair_cvt (F : ℝ → ℝ) (a b : ℝ) :
    (∫ u in a..b, F u) = ∫ u in -b..-a, F (-u) := by
  simpa using (intervalIntegral.integral_comp_neg (f := F) (a := -b) (b := -a)).symm

/-- Fold the negative survivor into the positive band via `u -> -u`. -/
lemma bb_neg_piece (x : ℝ) :
    (∫ u in (-1)..(-(9/10 : ℝ)), bb x u)
      = ∫ u in (9/10)..1, bumpReal (x + u) * (-(bd u)) := by
  rw [pair_cvt (bb x) (-1) (-(9/10 : ℝ))]
  simp only [neg_neg]
  congr 1
  funext u
  simp [bb, bd_neg, sub_eq_add_neg]

/-- The `+u`-shifted survivor integrand. -/
noncomputable def bumpPlus (x : ℝ) : ℝ → ℝ := fun u => bumpReal (x + u) * (-(bd u))

lemma bumpPlus_cont (x : ℝ) : Continuous (bumpPlus x) := by
  unfold bumpPlus
  have h1 : Continuous (fun u : ℝ => x + u) := continuous_const.add continuous_id
  exact (bumpReal_continuous.comp h1).mul bd_continuous.neg

lemma bumpPlus_int (x) (a b : ℝ) : IntervalIntegrable (bumpPlus x) volume a b :=
  (bumpPlus_cont x).intervalIntegrable a b

/-- Final pairing: `bumpFderiv x` collapses to ONE band integral with the signed bracket. -/
theorem bumpfFPair (x : ℝ) :
    bumpFderiv x = ∫ u in (9/10)..1, (bumpReal (x - u) - bumpReal (x + u)) * bd u := by
  rw [bumpFderiv_custom_sub]
  change (∫ u : ℝ, bb x u) = ∫ u in (9/10)..1, (bumpReal (x - u) - bumpReal (x + u)) * bd u
  rw [bb_integral_reduce]
  rw [bb_two_band]
  rw [bb_neg_piece]
  change (∫ u in (9/10)..1, (bumpPlus x) u) + ∫ u in (9/10)..1, bb x u
       = ∫ u in (9/10)..1, (bumpReal (x - u) - bumpReal (x + u)) * bd u
  rw [← intervalIntegral.integral_add (bumpPlus_int x (9/10) 1) (bb_int x (9/10) 1)]
  congr 1
  funext u
  simp [bumpPlus, bb]
  ring

/-- `bumpReal` is nonincreasing on `[0,1]`. -/
lemma bumpReal_antitoneOn_Icc01 : AntitoneOn bumpReal (Set.Icc (0 : ℝ) 1) := by
  rintro a ha b hb hab
  exact bumpReal_mono_abs a b (by rw [abs_of_nonneg ha.1, abs_of_nonneg hb.1]; linarith)

/-- `bd u <= 0` on `(9/10, 1)`. -/
theorem bd_nonpos (u : ℝ) (hu : (9/10 : ℝ) < u) (huv : u < 1) : bd u <= 0 := by
  have hmono := bumpReal_antitoneOn_Icc01
  have h0 : derivWithin bumpReal (Set.Icc (0 : ℝ) 1) u <= 0 :=
    hmono.derivWithin_nonpos (x := u)
  have hconv : derivWithin bumpReal (Set.Icc (0 : ℝ) 1) u = deriv bumpReal u := by
    apply derivWithin_of_mem_nhds
    have hu0 : 0 < u := by linarith
    exact Icc_mem_nhds (a := (0 : ℝ)) hu0 huv
  rw [hconv] at h0
  simpa [bd] using h0

/-- FTC: `int_a^b bd u = bumpReal b - bumpReal a`. -/
theorem bd_integral_eq (a b : ℝ) : (∫ u in a..b, bd u) = bumpReal b - bumpReal a := by
  simpa [bd] using
    (intervalIntegral.integral_deriv_eq_sub'
        (f := fun x : ℝ => bumpReal x) (f' := bd)
        (by rfl)
        (by intro x hx; exact bumpReal_differentiable x)
        (by exact bd_continuous.continuousOn))

/-- the signed band integrand. -/
noncomputable def Q (x u : ℝ) : ℝ := (bumpReal (x - u) - bumpReal (x + u)) * bd u

lemma Q_cont (x : ℝ) : Continuous (Q x) := by
  unfold Q
  have h1 : Continuous (fun u : ℝ => x - u) := continuous_const.sub continuous_id
  have h2 : Continuous (fun u : ℝ => x + u) := continuous_const.add continuous_id
  exact ((bumpReal_continuous.comp h1).sub (bumpReal_continuous.comp h2)).mul bd_continuous

/-- bracket magnitude >= 0 for 0<=x and 9/10<=u. -/
lemma bracket_nonneg (x u : ℝ) (hx : 0 <= x) (hu0 : (9 / 10 : ℝ) <= u) :
    0 <= bumpReal (x - u) - bumpReal (x + u) := by
  have hu : 0 <= u := by linarith
  have hxun : 0 <= x + u := by linarith
  have htri : |x - u| <= x + u := by
    calc
      |x - u| = |x + (-u)| := by rw [sub_eq_add_neg]
      _ <= |x| + |(-u)| := abs_add_le x (-u)
      _ = x + u := by rw [abs_of_nonneg hx, abs_neg, abs_of_nonneg hu]
  have habs : |x - u| <= |x + u| := by rwa [abs_of_nonneg hxun]
  have hmono := bumpReal_mono_abs (x - u) (x + u) habs
  linarith

/-- bracket <= 1. -/
lemma bracket_le_one (x u : ℝ) : bumpReal (x - u) - bumpReal (x + u) <= 1 := by
  have h1 : bumpReal (x - u) <= 1 := bumpReal_le_one (x - u)
  have h2 : 0 <= bumpReal (x + u) := bumpReal_nonneg (x + u)
  linarith

/-- the integrand `Q` is nonpositive on `(9/10,1)` when `0<=x`. -/
lemma Q_nonpos (x u : ℝ) (hx : 0 <= x) (hu : u ∈ (Set.Ioo (9 / 10 : ℝ) 1)) :
    Q x u <= 0 := by
  unfold Q
  have hBr : 0 <= bumpReal (x - u) - bumpReal (x + u) := bracket_nonneg x u hx (le_of_lt hu.1)
  have hbd : bd u <= 0 := bd_nonpos u hu.1 hu.2
  exact mul_nonpos_of_nonneg_of_nonpos hBr hbd

/-- pointwise: `-Q x u <= -bd u` on `(9/10,1)`. -/
lemma negQ_le_negBd (x u : ℝ) (hu : u ∈ (Set.Ioo (9 / 10 : ℝ) 1)) :
    - Q x u <= -(bd u) := by
  unfold Q
  rw [← mul_neg]
  have hBle1 : bumpReal (x - u) - bumpReal (x + u) <= 1 := bracket_le_one x u
  have hbdn : (0 : ℝ) <= -(bd u) := neg_nonneg.mpr (bd_nonpos u hu.1 hu.2)
  simpa [one_mul] using (mul_le_mul_of_nonneg_right hBle1 hbdn :
      (bumpReal (x - u) - bumpReal (x + u)) * (-(bd u)) <= 1 * (-(bd u)))

/-- `|bumpFderiv x| <= 1` on `[0,1]` (the sharp plateau total-variation bound). -/
theorem bumpFderiv_abs_le_one (x : ℝ) (hx0 : 0 <= x) (hx1 : x <= 1) :
    |bumpFderiv x| <= 1 := by
  have hQeq : bumpFderiv x = ∫ u in (9 / 10)..1, Q x u := by
    simpa [Q] using bumpfFPair x
  rw [hQeq]
  have hfQ : IntervalIntegrable (fun u : ℝ => Q x u) volume (9 / 10) 1 :=
    (Q_cont x).intervalIntegrable (9 / 10) 1
  have hPair0 : (∫ u in (9 / 10)..1, Q x u) <= (0 : ℝ) := by
    have hg : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (9 / 10) 1 :=
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).intervalIntegrable (9/10) 1
    have hmon := intervalIntegral.integral_mono_on_of_le_Ioo
      (a := (9 / 10 : ℝ)) (b := (1 : ℝ)) (by norm_num)
      hfQ hg (by intro u hu; exact Q_nonpos x u hx0 hu)
    simpa using hmon
  have hnegB : (∫ u in (9 / 10)..1, -(Q x u)) <= ∫ u in (9 / 10)..1, -(bd u) := by
    have hA : IntervalIntegrable (fun u : ℝ => -(Q x u)) volume (9 / 10) 1 :=
      (Q_cont x).neg.intervalIntegrable (9 / 10) 1
    have hB : IntervalIntegrable (fun u : ℝ => -(bd u)) volume (9 / 10) 1 :=
      bd_continuous.neg.intervalIntegrable (9 / 10) 1
    exact intervalIntegral.integral_mono_on_of_le_Ioo
      (a := (9 / 10 : ℝ)) (b := (1 : ℝ)) (by norm_num)
      hA hB (by intro u hu; exact negQ_le_negBd x u hu)
  have hbdint : (∫ u in (9 / 10)..1, -(bd u)) = 1 := by
    calc
      (∫ u in (9 / 10)..1, -(bd u)) = - (∫ u in (9 / 10)..1, bd u) := intervalIntegral.integral_neg
      _ = -(bumpReal 1 - bumpReal (9 / 10 : ℝ)) := by rw [bd_integral_eq (9 / 10) 1]
      _ = 1 := by rw [bumpReal_one_eq_zero, bumpReal_b0_eq_one]; norm_num
  calc
    |∫ u in (9 / 10)..1, Q x u| = - (∫ u in (9 / 10)..1, Q x u) := abs_of_nonpos hPair0
    _ = ∫ u in (9 / 10)..1, -(Q x u) := (intervalIntegral.integral_neg : _).symm
    _ <= ∫ u in (9 / 10)..1, -(bd u) := hnegB
    _ = 1 := hbdint



/-- `bumpF(0) = bumpA` : the conv-square at 0 equals the L2 mass. -/
theorem bumpF_zero_eq_bumpA : bumpF (0 : ℝ) = bumpA := by
  rw [bumpF_eq_conv, bumpA_eq_integral_realSq]
  congr 1
  funext t
  have h : (0 : ℝ) - t = -t := by ring
  rw [h, bumpReal_even t]
  ring
/-- `|bumpA - bumpF y| <= y` on `[0,1]`, via the two-sided mean value theorem from `|bumpF'|<=1`. -/
theorem bumpA_sub_bumpF_le (y : ℝ) (hy0 : 0 <= y) (hyb : y <= 1) :
    |bumpA - bumpF y| <= y := by
  let D : Set ℝ := Set.Icc (0 : ℝ) y
  have hdF : Differentiable ℝ bumpF := fun x => (bumpF_hasDerivAt x).differentiableAt
  have hcF : Continuous bumpF := continuous_iff_continuousAt.mpr fun x => (bumpF_hasDerivAt x).continuousAt
  have hder_in (x : ℝ) (hx : x ∈ interior D) : deriv bumpF x <= 1 := by
    have hx0 : 0 <= x := (interior_subset hx).1
    have hx1 : x <= 1 := (interior_subset hx).2.trans hyb
    have h := (bumpF_hasDerivAt x).deriv
    rw [h]
    exact le_of_abs_le (bumpFderiv_abs_le_one x hx0 hx1)
  have hder_in_neg (x : ℝ) (hx : x ∈ interior D) : deriv (fun i : ℝ => -bumpF i) x <= 1 := by
    have hx0 : 0 <= x := (interior_subset hx).1
    have hx1 : x <= 1 := (interior_subset hx).2.trans hyb
    have hbump : (-1 : ℝ) <= bumpFderiv x := neg_le_of_abs_le (bumpFderiv_abs_le_one x hx0 hx1)
    rw [deriv.fun_neg, (bumpF_hasDerivAt x).deriv]
    linarith
  have hupper : bumpF y - bumpF (0 : ℝ) <= y := by
    have hD : Convex ℝ D := convex_Icc (0 : ℝ) y
    have hcD : ContinuousOn bumpF D := hcF.continuousOn
    have hdD : DifferentiableOn ℝ bumpF (interior D) := hdF.differentiableOn.mono interior_subset
    have h := hD.image_sub_le_mul_sub_of_deriv_le hcD hdD (C := 1) hder_in
      (0 : ℝ) (by dsimp [D]; exact ⟨le_rfl, hy0⟩)
      y (by dsimp [D]; exact ⟨hy0, le_rfl⟩) hy0
    simpa using h
  have hlower : bumpF (0 : ℝ) - bumpF y <= y := by
    have hD : Convex ℝ D := convex_Icc (0 : ℝ) y
    have hcD : ContinuousOn (fun i : ℝ => -bumpF i) D := hcF.neg.continuousOn
    have hdD : DifferentiableOn ℝ (fun i : ℝ => -bumpF i) (interior D) :=
      hdF.neg.differentiableOn.mono interior_subset
    have hr := hD.image_sub_le_mul_sub_of_deriv_le (f := fun i : ℝ => -bumpF i) hcD hdD (C := 1) hder_in_neg
      (0 : ℝ) (by dsimp [D]; exact ⟨le_rfl, hy0⟩)
      y (by dsimp [D]; exact ⟨hy0, le_rfl⟩) hy0
    -- hr : -(bumpF y) - (-(bumpF 0)) <= 1 * (y - 0); hence bumpF 0 - bumpF y <= y.
    nlinarith [hr]
  rw [← bumpF_zero_eq_bumpA]
  rw [abs_le]
  constructor
  · nlinarith [hupper]
  · simpa [sub_eq_add_neg] using hlower


end Wall14Plateau
end Dev
end Source
end ConnesWeilRH