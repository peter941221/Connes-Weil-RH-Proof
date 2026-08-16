import ConnesWeilRH.Dev.C1SpectralSummability
import ConnesWeilRH.Dev.C1XiFiniteHeightRectangle

/-!
# C1XiQuantitativeHeight

A finite set of forbidden real heights admits a point in every unit interval
that stays an explicit positive distance from every forbidden value.  The xi
specialization will apply this elementary packing statement to the finite
height window supplied by the Jensen count.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiQuantitativeHeight

open Set
open CC20YoshidaNearZeros
open CC20ZetaCounting
open C1SpectralWeil
open C1SpectralSummability
open C1XiFiniteHeightRectangle

private def gridDenom (N : Nat) : Real := (N + 2 : Nat)

/-- The explicit exclusion radius used by the finite grid argument. -/
noncomputable def gridGap (N : Nat) : Real := 1 / (4 * gridDenom N)

private noncomputable def gridPoint (B : Real) (N j : Nat) : Real :=
  B + ((j + 1 : Nat) : Real) / gridDenom N

private theorem gridDenom_pos (N : Nat) : 0 < gridDenom N := by
  unfold gridDenom
  positivity

theorem gridGap_pos (N : Nat) : 0 < gridGap N := by
  unfold gridGap
  exact div_pos (by norm_num) (mul_pos (by norm_num) (gridDenom_pos N))

/-- Public formula for the finite-grid separation.  Downstream quantitative
estimates should use this theorem instead of depending on the private grid
implementation. -/
theorem gridGap_eq (N : Nat) :
    gridGap N = 1 / (4 * (((N + 2 : Nat) : Real))) := by
  rfl

private theorem gridPoint_mem_Ioo (B : Real) (N : Nat) (j : Fin (N + 1)) :
    gridPoint B N j.1 ∈ Ioo B (B + 1) := by
  have hden : 0 < gridDenom N := gridDenom_pos N
  have hnum_pos : 0 < ((j.1 + 1 : Nat) : Real) := by positivity
  have hnum_lt_nat : j.1 + 1 < N + 2 := by omega
  have hnum_lt' : ((j.1 + 1 : Nat) : Real) < ((N + 2 : Nat) : Real) := by
    exact_mod_cast hnum_lt_nat
  have hnum_lt : ((j.1 + 1 : Nat) : Real) < gridDenom N := by
    simpa only [gridDenom] using hnum_lt'
  constructor
  · dsimp only [gridPoint]
    linarith [div_pos hnum_pos hden]
  · dsimp only [gridPoint]
    linarith [(div_lt_one hden).mpr hnum_lt]

private theorem gridPoint_diff (B : Real) (N j k : Nat) :
    gridPoint B N j - gridPoint B N k =
      ((j : Real) - (k : Real)) / gridDenom N := by
  simp only [gridPoint]
  push_cast
  ring

private theorem gridPoint_separated (B : Real) (N : Nat)
    (j k : Fin (N + 1)) (hjk : j ≠ k) :
    2 * gridGap N < |gridPoint B N j.1 - gridPoint B N k.1| := by
  have hden : 0 < gridDenom N := gridDenom_pos N
  have hgap : gridGap N = (1 / 4 : Real) * (1 / gridDenom N) := by
    unfold gridGap
    field_simp [hden.ne']
  have habs : 1 ≤ |(j.1 : Real) - (k.1 : Real)| := by
    have hne : j.1 ≠ k.1 := by
      intro h
      apply hjk
      exact Fin.ext h
    rcases lt_or_gt_of_ne hne with hjk_lt | hkj_lt
    · have hstep_nat : j.1 + 1 ≤ k.1 := Nat.succ_le_iff.mpr hjk_lt
      have hstep : (j.1 : Real) + 1 ≤ k.1 := by exact_mod_cast hstep_nat
      rw [abs_of_nonpos (by linarith : (j.1 : Real) - k.1 ≤ 0)]
      linarith
    · have hstep_nat : k.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hkj_lt
      have hstep : (k.1 : Real) + 1 ≤ j.1 := by exact_mod_cast hstep_nat
      rw [abs_of_nonneg (by linarith : 0 ≤ (j.1 : Real) - k.1)]
      linarith
  have hrecip_pos : 0 < 1 / gridDenom N := one_div_pos.mpr hden
  calc
    2 * gridGap N = (1 / 2 : Real) * (1 / gridDenom N) := by
      rw [hgap]
      ring
    _ < 1 * (1 / gridDenom N) := by nlinarith
    _ ≤ |(j.1 : Real) - (k.1 : Real)| * (1 / gridDenom N) := by
      exact mul_le_mul_of_nonneg_right habs hrecip_pos.le
    _ = |((j.1 : Real) - (k.1 : Real)) / gridDenom N| := by
      rw [abs_div, abs_of_pos hden]
      simp only [div_eq_mul_inv, one_mul]
    _ = |gridPoint B N j.1 - gridPoint B N k.1| := by
      rw [gridPoint_diff]

/-- Among `N + 1` equally spaced candidates in a unit interval, one stays at
least `1 / (4 * (N + 2))` from every value in a forbidden set of cardinality
`N`. -/
theorem exists_point_Ioo_away_from_finset (S : Finset Real) (B : Real) :
    ∃ T : Real, T ∈ Ioo B (B + 1) ∧
      ∀ a ∈ S, gridGap S.card ≤ |T - a| := by
  classical
  let N : Nat := S.card
  let candidate : Fin (N + 1) -> Real := fun j => gridPoint B N j.1
  by_contra h_exists
  have hbad (j : Fin (N + 1)) :
      ∃ a ∈ S, |candidate j - a| < gridGap N := by
    by_contra hgood
    push Not at hgood
    apply h_exists
    refine ⟨candidate j, ?_, ?_⟩
    · simpa only [candidate, N] using gridPoint_mem_Ioo B N j
    · intro a ha
      exact hgood a ha
  let f : Fin (N + 1) -> {a : Real // a ∈ S} := fun j =>
    ⟨Classical.choose (hbad j), (Classical.choose_spec (hbad j)).1⟩
  have hf_bad (j : Fin (N + 1)) :
      |candidate j - (f j : Real)| < gridGap N := by
    exact (Classical.choose_spec (hbad j)).2
  have hf_injective : Function.Injective f := by
    intro j k hfk
    by_contra hjk
    have hsep : 2 * gridGap N < |candidate j - candidate k| := by
      dsimp only [candidate]
      apply gridPoint_separated B N j k
      exact hjk
    have hvalue : (f j : Real) = f k := congrArg Subtype.val hfk
    have hleft := hf_bad j
    have hright : |(f j : Real) - candidate k| < gridGap N := by
      rw [hvalue, abs_sub_comm]
      exact hf_bad k
    have htriangle : |candidate j - candidate k| ≤
        |candidate j - (f j : Real)| + |(f j : Real) - candidate k| := by
      exact abs_sub_le _ _ _
    linarith
  have hcard := Fintype.card_le_of_injective f hf_injective
  have hcard' : N + 1 ≤ N := by
    simpa only [Fintype.card_fin, Fintype.card_coe, N] using hcard
  omega

/-- The finite set of nonnegative zero ordinates that can lie within one unit
of a height selected from `(B, B + 1)`. -/
noncomputable def xiHeightForbiddenOrdinates (B : Real) : Finset Real :=
  (finiteHeightZeros (B + 2)).image fun rho => |rho.1.im|

/-- The grid exclusion radius for the xi zeros visible from the unit height
window above `B`. -/
noncomputable def xiHeightSeparation (B : Real) : Real :=
  gridGap (xiHeightForbiddenOrdinates B).card

/-- A tube radius which remains in the finite zero window and inherits the
quantitative horizontal separation. -/
noncomputable def xiHeightTubeRadius (B : Real) : Real :=
  min (xiHeightSeparation B) (1 / 2)

theorem xiHeightTubeRadius_pos (B : Real) : 0 < xiHeightTubeRadius B := by
  unfold xiHeightTubeRadius
  apply lt_min
  · simpa only [xiHeightSeparation] using
      gridGap_pos (xiHeightForbiddenOrdinates B).card
  · norm_num

private theorem abs_height_sub_abs_im_le_dist
    (x T : Real) (hT : 0 ≤ T) (rho : Complex) :
    abs (T - abs rho.im) ≤ dist ((x : Complex) + T * Complex.I) rho := by
  calc
    abs (T - abs rho.im) = abs (abs T - abs rho.im) := by rw [abs_of_nonneg hT]
    _ ≤ abs (T - rho.im) := abs_abs_sub_abs_le_abs_sub _ _
    _ = abs (((x : Complex) + T * Complex.I - rho).im) := by simp
    _ ≤ ‖(x : Complex) + T * Complex.I - rho‖ := Complex.abs_im_le_norm _
    _ = dist ((x : Complex) + T * Complex.I) rho := by rw [dist_eq_norm]

/-- Enlarging the symmetric height window can only add source zeros. -/
theorem finiteHeightZeros_mono {T U : Real} (hTU : T ≤ U) :
    finiteHeightZeros T ⊆ finiteHeightZeros U := by
  intro rho hrho
  rw [mem_finiteHeightZeros_iff T rho] at hrho
  rw [mem_finiteHeightZeros_iff U rho]
  exact le_trans hrho hTU

/-- The analytic-multiplicity mass is monotone with the symmetric height
window. -/
theorem finiteHeightMultiplicity_mono {T U : Real} (hTU : T ≤ U) :
    finiteHeightMultiplicity T ≤ finiteHeightMultiplicity U := by
  unfold finiteHeightMultiplicity
  apply Finset.sum_le_sum_of_subset_of_nonneg (finiteHeightZeros_mono hTU)
  intro rho _ _
  exact Nat.zero_le _

/-- Forgetting repeated ordinates cannot increase their cardinality, and every
source zero contributes at least one analytic multiplicity. -/
theorem xiHeightForbiddenOrdinates_card_le_finiteHeightMultiplicity (B : Real) :
    (xiHeightForbiddenOrdinates B).card ≤ finiteHeightMultiplicity (B + 2) := by
  calc
    (xiHeightForbiddenOrdinates B).card ≤ (finiteHeightZeros (B + 2)).card := by
      unfold xiHeightForbiddenOrdinates
      exact Finset.card_image_le
    _ ≤ finiteHeightMultiplicity (B + 2) := by
      unfold finiteHeightMultiplicity
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro rho hrho
      exact Nat.succ_le_iff.mpr (xiMultiplicity_pos rho)

/-- The existing dyadic Jensen multiplicity estimate bounds the number of
distinct visible xi ordinates needed for the next-unit height selection. -/
theorem xiHeightForbiddenOrdinates_dyadic_card_le (n : Nat) :
    ((xiHeightForbiddenOrdinates ((2 : Real) ^ (n + 2))).card : Real) ≤
      spectralMultiplicityConstant * (3 : Real) ^ (n + 1) := by
  let B : Real := (2 : Real) ^ (n + 2)
  have hB_ge_two : 2 ≤ B := by
    have hpow_one : 1 ≤ (2 : Real) ^ n := one_le_pow₀ (by norm_num)
    dsimp only [B]
    calc
      2 ≤ 4 * (2 : Real) ^ n := by nlinarith
      _ = (2 : Real) ^ (n + 2) := by
        rw [pow_add]
        ring
  have hwindow : B + 2 ≤ (2 : Real) ^ ((n + 1) + 2) := by
    calc
      B + 2 ≤ B + B := by linarith
      _ = (2 : Real) ^ (n + 2) * 2 := by
        dsimp only [B]
        ring
      _ = (2 : Real) ^ ((n + 1) + 2) := by
        have hindex : (n + 1) + 2 = (n + 2) + 1 := by omega
        rw [hindex, pow_succ]
        ring
  have hcard := xiHeightForbiddenOrdinates_card_le_finiteHeightMultiplicity B
  have hmass := finiteHeightMultiplicity_mono hwindow
  change ((xiHeightForbiddenOrdinates B).card : Real) ≤
    spectralMultiplicityConstant * (3 : Real) ^ (n + 1)
  calc
    ((xiHeightForbiddenOrdinates B).card : Real) ≤
        (finiteHeightMultiplicity (B + 2) : Real) := by
          exact_mod_cast hcard
    _ ≤ (finiteHeightMultiplicity ((2 : Real) ^ ((n + 1) + 2)) : Real) := by
          exact_mod_cast hmass
    _ ≤ spectralMultiplicityConstant * (3 : Real) ^ (n + 1) :=
      finiteHeightMultiplicity_dyadic_le (n + 1)

/-- The finite-grid separation has an explicit lower scale on dyadic base
heights. -/
theorem xiHeightSeparation_dyadic_lower_bound (n : Nat) :
    1 / (4 * (spectralMultiplicityConstant * (3 : Real) ^ (n + 1) + 2)) ≤
      xiHeightSeparation ((2 : Real) ^ (n + 2)) := by
  let N : Nat := (xiHeightForbiddenOrdinates ((2 : Real) ^ (n + 2))).card
  let K : Real := spectralMultiplicityConstant * (3 : Real) ^ (n + 1)
  have hN : (N : Real) ≤ K := by
    dsimp only [N, K]
    exact xiHeightForbiddenOrdinates_dyadic_card_le n
  have hdenom_pos : 0 < 4 * ((N : Real) + 2) := by positivity
  have hdenom_le : 4 * ((N : Real) + 2) ≤ 4 * (K + 2) := by
    nlinarith
  change 1 / (4 * (K + 2)) ≤ gridGap N
  unfold gridGap gridDenom
  norm_num only [Nat.cast_add, Nat.cast_ofNat]
  exact one_div_le_one_div_of_le hdenom_pos hdenom_le

/-- An explicit dyadic radius for the two horizontal zero-free tubes. The
minimum retains the fixed finite-window margin used by the geometric proof. -/
noncomputable def dyadicXiHeightTubeRadius (n : Nat) : Real :=
  min (1 / (4 * (spectralMultiplicityConstant * (3 : Real) ^ (n + 1) + 2)))
    (1 / 2)

theorem dyadicXiHeightTubeRadius_pos (n : Nat) :
    0 < dyadicXiHeightTubeRadius n := by
  unfold dyadicXiHeightTubeRadius
  apply lt_min
  · apply one_div_pos.mpr
    apply mul_pos
    · norm_num
    · have hnonneg : 0 ≤ spectralMultiplicityConstant * (3 : Real) ^ (n + 1) :=
        mul_nonneg spectralMultiplicityConstant_nonneg (by positivity)
      linarith
  · norm_num

/-- A nonnegative base height has a successor height in its next unit window
which is separated by an explicit positive distance from every xi zero in the
only finite height window that can meet either horizontal side. -/
theorem exists_quantitative_xiHeightBoundaryAvoidsZeros
    (B : Real) (hB : 0 ≤ B) :
    ∃ T : Real, B < T ∧ T < B + 1 ∧
      xiHeightBoundaryAvoidsZeros T ∧
      ∀ rho ∈ finiteHeightZeros (B + 2),
        xiHeightSeparation B ≤ |T - (|rho.1.im|)| := by
  let S : Finset Real := xiHeightForbiddenOrdinates B
  obtain ⟨T, hT_window, hT_sep⟩ := exists_point_Ioo_away_from_finset S B
  have hT_pos : 0 < T := lt_of_le_of_lt hB hT_window.1
  have hsep (rho : sourceNontrivialZeroSet)
      (hrho : rho ∈ finiteHeightZeros (B + 2)) :
      xiHeightSeparation B ≤ |T - (|rho.1.im|)| := by
    have hord : |rho.1.im| ∈ S := by
      dsimp only [S, xiHeightForbiddenOrdinates]
      exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩
    simpa only [S, xiHeightSeparation] using hT_sep |rho.1.im| hord
  have hboundary : xiHeightBoundaryAvoidsZeros T := by
    constructor
    · intro x hx hzero
      let rho : sourceNontrivialZeroSet :=
        ⟨(x : Complex) - T * Complex.I,
          sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero⟩
      have hT_le : T ≤ B + 2 := by linarith [hT_window.2]
      have hrho : rho ∈ finiteHeightZeros (B + 2) := by
        rw [mem_finiteHeightZeros_iff]
        change |((x : Complex) - T * Complex.I).im| ≤ B + 2
        simpa [abs_of_nonneg hT_pos.le] using hT_le
      have hcontra := hsep rho hrho
      have him : |rho.1.im| = T := by
        simp [rho, abs_of_nonneg hT_pos.le]
      have hzeroGap : xiHeightSeparation B ≤ 0 := by
        simpa [him] using hcontra
      exact (not_le_of_gt (gridGap_pos _)) (by
        simpa only [xiHeightSeparation] using hzeroGap)
    · intro x hx hzero
      let rho : sourceNontrivialZeroSet :=
        ⟨(x : Complex) + T * Complex.I,
          sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero⟩
      have hT_le : T ≤ B + 2 := by linarith [hT_window.2]
      have hrho : rho ∈ finiteHeightZeros (B + 2) := by
        rw [mem_finiteHeightZeros_iff]
        change |((x : Complex) + T * Complex.I).im| ≤ B + 2
        simpa [abs_of_nonneg hT_pos.le] using hT_le
      have hcontra := hsep rho hrho
      have him : |rho.1.im| = T := by
        simp [rho, abs_of_nonneg hT_pos.le]
      have hzeroGap : xiHeightSeparation B ≤ 0 := by
        simpa [him] using hcontra
      exact (not_le_of_gt (gridGap_pos _)) (by
        simpa only [xiHeightSeparation] using hzeroGap)
  exact ⟨T, hT_window.1, hT_window.2, hboundary, hsep⟩

/-- The quantitative selected height has a uniform zero-free complex tube
around its upper horizontal line. The half-unit cap keeps any hypothetical
zero inside the finite `B + 2` window; the grid separation then excludes it. -/
theorem exists_quantitative_xiHeightBoundaryAvoidsZeros_tube
    (B : Real) (hB : 0 ≤ B) :
    ∃ T : Real, B < T ∧ T < B + 1 ∧ xiHeightBoundaryAvoidsZeros T ∧
      ∀ x : Real, ∀ z ∈ Metric.ball ((x : Complex) + T * Complex.I)
        (xiHeightTubeRadius B), completedRiemannXi z ≠ 0 := by
  obtain ⟨T, hB_lt_T, hT_lt, hboundary, hsep⟩ :=
    exists_quantitative_xiHeightBoundaryAvoidsZeros B hB
  have hT_nonneg : 0 ≤ T := le_trans hB hB_lt_T.le
  refine ⟨T, hB_lt_T, hT_lt, hboundary, ?_⟩
  intro x z hz hzero
  let rho : sourceNontrivialZeroSet :=
    ⟨z, sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero⟩
  have hdist : dist ((x : Complex) + T * Complex.I) rho.1 <
      xiHeightTubeRadius B := by
    rw [Metric.mem_ball] at hz
    change dist z ((x : Complex) + T * Complex.I) < xiHeightTubeRadius B at hz
    simpa only [rho, dist_comm] using hz
  have hdist' : dist ((x : Complex) + T * Complex.I) rho.1 <
      min (xiHeightSeparation B) (1 / 2) := by
    simpa only [xiHeightTubeRadius] using hdist
  have hgrid : dist ((x : Complex) + T * Complex.I) rho.1 <
      xiHeightSeparation B :=
    lt_of_lt_of_le hdist' (min_le_left _ _)
  have hhalf : dist ((x : Complex) + T * Complex.I) rho.1 < (1 / 2 : Real) :=
    lt_of_lt_of_le hdist' (min_le_right _ _)
  have hgrid_im : abs (T - abs rho.1.im) < xiHeightSeparation B :=
    lt_of_le_of_lt (abs_height_sub_abs_im_le_dist x T hT_nonneg rho.1) hgrid
  have hhalf_im : abs (T - abs rho.1.im) < (1 / 2 : Real) :=
    lt_of_le_of_lt (abs_height_sub_abs_im_le_dist x T hT_nonneg rho.1) hhalf
  have him_lt : abs rho.1.im < T + 1 / 2 := by
    have hleft : -(1 / 2 : Real) < T - abs rho.1.im := (abs_lt.mp hhalf_im).1
    linarith
  have hrho : rho ∈ finiteHeightZeros (B + 2) := by
    rw [mem_finiteHeightZeros_iff]
    linarith
  exact (not_lt_of_ge (hsep rho hrho)) hgrid_im

/-- The xi functional equation transports the quantitative upper tube to the
lower horizontal line without changing the selected height or radius. -/
theorem exists_quantitative_xiHeightBoundaryAvoidsZeros_tubes
    (B : Real) (hB : 0 ≤ B) :
    ∃ T : Real, B < T ∧ T < B + 1 ∧ xiHeightBoundaryAvoidsZeros T ∧
      (∀ x : Real, ∀ z ∈ Metric.ball ((x : Complex) + T * Complex.I)
        (xiHeightTubeRadius B), completedRiemannXi z ≠ 0) ∧
      ∀ x : Real, ∀ z ∈ Metric.ball ((x : Complex) - T * Complex.I)
        (xiHeightTubeRadius B), completedRiemannXi z ≠ 0 := by
  obtain ⟨T, hB_lt_T, hT_lt, hboundary, hupper⟩ :=
    exists_quantitative_xiHeightBoundaryAvoidsZeros_tube B hB
  refine ⟨T, hB_lt_T, hT_lt, hboundary, hupper, ?_⟩
  intro x z hz hzero
  have hreflect_ball : (1 - z) ∈ Metric.ball
      (((1 - x : Real) : Complex) + T * Complex.I) (xiHeightTubeRadius B) := by
    rw [Metric.mem_ball] at hz ⊢
    calc
      dist (1 - z) (((1 - x : Real) : Complex) + T * Complex.I) =
          dist z ((x : Complex) - T * Complex.I) := by
            rw [dist_eq_norm, dist_eq_norm]
            calc
              ‖(1 - z) - (((1 - x : Real) : Complex) + T * Complex.I)‖ =
                  ‖-(z - ((x : Complex) - T * Complex.I))‖ := by
                    congr 1
                    push_cast
                    ring
              _ = ‖z - ((x : Complex) - T * Complex.I)‖ := norm_neg _
      _ < xiHeightTubeRadius B := hz
  apply hupper (1 - x) (1 - z) hreflect_ball
  rw [completedRiemannXi_one_sub]
  exact hzero

/-- Every dyadic scale has one height in its next unit window with a
same-height, two-sided xi-zero-free tube at an explicit radius. -/
theorem exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes (n : Nat) :
    ∃ T : Real, (2 : Real) ^ (n + 2) < T ∧
      T < (2 : Real) ^ (n + 2) + 1 ∧ xiHeightBoundaryAvoidsZeros T ∧
      (∀ x : Real, ∀ z ∈ Metric.ball ((x : Complex) + T * Complex.I)
        (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0) ∧
      ∀ x : Real, ∀ z ∈ Metric.ball ((x : Complex) - T * Complex.I)
        (dyadicXiHeightTubeRadius n), completedRiemannXi z ≠ 0 := by
  let B : Real := (2 : Real) ^ (n + 2)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  obtain ⟨T, hB_lt_T, hT_lt, hboundary, hupper, hlower⟩ :=
    exists_quantitative_xiHeightBoundaryAvoidsZeros_tubes B hB
  have hrad : dyadicXiHeightTubeRadius n ≤ xiHeightTubeRadius B := by
    change min (1 / (4 * (spectralMultiplicityConstant *
      (3 : Real) ^ (n + 1) + 2))) (1 / 2) ≤
        min (xiHeightSeparation ((2 : Real) ^ (n + 2))) (1 / 2)
    exact min_le_min (xiHeightSeparation_dyadic_lower_bound n) le_rfl
  refine ⟨T, ?_, ?_, hboundary, ?_, ?_⟩
  · simpa only [B] using hB_lt_T
  · simpa only [B] using hT_lt
  · intro x z hz
    apply hupper x z
    rw [Metric.mem_ball] at hz ⊢
    exact lt_of_lt_of_le hz hrad
  · intro x z hz
    apply hlower x z
    rw [Metric.mem_ball] at hz ⊢
    exact lt_of_lt_of_le hz hrad

end C1XiQuantitativeHeight
end Source
end ConnesWeilRH
