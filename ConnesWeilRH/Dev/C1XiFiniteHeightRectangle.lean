import ConnesWeilRH.Dev.C1XiFiniteRectangleSupportReindex

/-!
# C1XiFiniteHeightRectangle - finite-height xi rectangle spectral readout

The standard critical-strip rectangle has horizontal sides at heights `-T`
and `T`.  When those sides contain no xi zero, its strict interior source-zero
family is exactly the existing finite spectral truncation `finiteHeightZeros
T`: source nontrivial zeros are already strictly between real parts zero and
one, while the boundary hypothesis changes `|Im rho| <= T` into a strict
inequality.

No rectangle limit, arithmetic readback, explicit-formula equality, or RH
claim is made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiFiniteHeightRectangle

open Filter
open Set
open CC20YoshidaNearZeros
open CC20ZetaCounting
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiFiniteFactor
open C1XiFiniteRectangleBoundary
open C1XiFiniteRectanglePrincipalPart
open C1XiFiniteRectangleSupportReindex
open C1XiFiniteSupportReindex
open C1XiVerticalFunctional
open scoped BigOperators Interval Topology

/-- The critical-strip rectangle with symmetric height `T`. -/
noncomputable def criticalStripRectangleLower (T : Real) : Complex :=
  (0 : Complex) - T * Complex.I

noncomputable def criticalStripRectangleUpper (T : Real) : Complex :=
  (1 : Complex) + T * Complex.I

@[simp] theorem criticalStripRectangleLower_re (T : Real) :
    (criticalStripRectangleLower T).re = 0 := by
  simp [criticalStripRectangleLower]

@[simp] theorem criticalStripRectangleLower_im (T : Real) :
    (criticalStripRectangleLower T).im = -T := by
  simp [criticalStripRectangleLower]

@[simp] theorem criticalStripRectangleUpper_re (T : Real) :
    (criticalStripRectangleUpper T).re = 1 := by
  simp [criticalStripRectangleUpper]

@[simp] theorem criticalStripRectangleUpper_im (T : Real) :
    (criticalStripRectangleUpper T).im = T := by
  simp [criticalStripRectangleUpper]

/-- The two horizontal height sides avoid xi zeros.  The vertical sides are
already zero-free because source xi zeros have real part strictly between zero
and one. -/
def xiHeightBoundaryAvoidsZeros (T : Real) : Prop :=
  (∀ x ∈ Set.Icc (0 : Real) 1,
    completedRiemannXi ((x : Complex) - T * Complex.I) ≠ 0) ∧
  ∀ x ∈ Set.Icc (0 : Real) 1,
    completedRiemannXi ((x : Complex) + T * Complex.I) ≠ 0

theorem standardRectangle_criticalStripRectangle {T : Real} (hT : 0 < T) :
    standardRectangle (criticalStripRectangleLower T) (criticalStripRectangleUpper T) := by
  constructor
  · simpa only [criticalStripRectangleLower_re, criticalStripRectangleUpper_re] using
      (show (0 : Real) < 1 by norm_num)
  · simpa only [criticalStripRectangleLower_im, criticalStripRectangleUpper_im] using
      (show -T < T by linarith)

/-- The rectangle guard follows from the horizontal guard and the known
zero-free outer boundaries of the source critical strip. -/
theorem xiRectangleBoundaryAvoidsZeros_criticalStripRectangle
    (T : Real) (hheight : xiHeightBoundaryAvoidsZeros T) :
    xiRectangleBoundaryAvoidsZeros
      (criticalStripRectangleLower T) (criticalStripRectangleUpper T) := by
  constructor
  · intro x hx
    have hx' : x ∈ Set.Icc (0 : Real) 1 := by
      simpa only [criticalStripRectangleLower_re, criticalStripRectangleUpper_re,
        uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] using hx
    rw [criticalStripRectangleLower_im]
    have hneg : ((-T : Real) : Complex) = -(T : Complex) := by
      push_cast
      rfl
    rw [hneg]
    have harg :
        (x : Complex) + -(T : Complex) * Complex.I =
          (x : Complex) - (T : Complex) * Complex.I := by
      ring
    rw [harg]
    exact hheight.1 x hx'
  constructor
  · intro x hx
    have hx' : x ∈ Set.Icc (0 : Real) 1 := by
      simpa only [criticalStripRectangleLower_re, criticalStripRectangleUpper_re,
        uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] using hx
    simpa only [criticalStripRectangleUpper_im] using hheight.2 x hx'
  constructor
  · intro y hy hzero
    have hsource := sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero
    have : (1 : Real) < 1 := by
      simpa [criticalStripRectangleUpper] using
        sourceNontrivialZero_re_lt_one hsource
    linarith
  · intro y hy hzero
    have hsource := sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero
    have : (0 : Real) < 0 := by
      simpa [criticalStripRectangleLower] using
        sourceNontrivialZero_zero_lt_re hsource
    linarith

/-- Above every lower bound there is a positive height whose two critical-strip
horizontal boundary segments are xi-zero-free.  The excluded heights are the
finite image of the bounded source-zero window under `rho |-> |Im rho|`. -/
theorem exists_xiHeightBoundaryAvoidsZeros_gt (B : Real) :
    ∃ T > B, xiHeightBoundaryAvoidsZeros T := by
  classical
  let lower : Real := max B 0
  let upper : Real := lower + 1
  let forbidden : Finset Real :=
    (finiteHeightZeros upper).image (fun rho => |rho.1.im|)
  have hB_lower : B ≤ lower := by
    dsimp [lower]
    exact le_max_left _ _
  have hzero_lower : 0 ≤ lower := by
    dsimp [lower]
    exact le_max_right _ _
  have hlower_lt_upper : lower < upper := by
    dsimp [upper]
    linarith
  obtain ⟨T, hT_interval, hT_not_forbidden⟩ :=
    (Set.Ioo_infinite hlower_lt_upper).exists_notMem_finset forbidden
  have hT_gt_B : B < T := lt_of_le_of_lt hB_lower hT_interval.1
  have hT_pos : 0 < T := lt_of_le_of_lt hzero_lower hT_interval.1
  have hT_lt_upper : T < upper := hT_interval.2
  refine ⟨T, hT_gt_B, ?_⟩
  have hT_mem_forbidden_of_zero {z : Complex}
      (hzero : completedRiemannXi z = 0) (habs : |z.im| = T) :
      T ∈ forbidden := by
    let rho : sourceNontrivialZeroSet :=
      ⟨z, sourceNontrivialZero_of_completedRiemannXi_eq_zero hzero⟩
    have hrho : rho ∈ finiteHeightZeros upper := by
      rw [mem_finiteHeightZeros_iff]
      change |z.im| ≤ upper
      rw [habs]
      exact hT_lt_upper.le
    change T ∈ (finiteHeightZeros upper).image (fun rho => |rho.1.im|)
    exact Finset.mem_image.mpr ⟨rho, hrho, by simpa [rho] using habs⟩
  constructor
  · intro x _ hzero
    exact hT_not_forbidden (hT_mem_forbidden_of_zero hzero (by
      simp [abs_of_nonneg hT_pos.le]))
  · intro x _ hzero
    exact hT_not_forbidden (hT_mem_forbidden_of_zero hzero (by
      simp [abs_of_nonneg hT_pos.le]))

/-- A recursively chosen xi-zero-free height sequence with a strict unit gap
between consecutive terms. -/
noncomputable def xiZeroFreeHeights : Nat -> Real
  | 0 => Classical.choose (exists_xiHeightBoundaryAvoidsZeros_gt 0)
  | n + 1 => Classical.choose
      (exists_xiHeightBoundaryAvoidsZeros_gt (xiZeroFreeHeights n + 1))

theorem xiZeroFreeHeights_zero_lt : 0 < xiZeroFreeHeights 0 := by
  change 0 < Classical.choose (exists_xiHeightBoundaryAvoidsZeros_gt 0)
  exact (Classical.choose_spec (exists_xiHeightBoundaryAvoidsZeros_gt 0)).1

theorem xiZeroFreeHeights_succ_gt (n : Nat) :
    xiZeroFreeHeights n + 1 < xiZeroFreeHeights (n + 1) := by
  change xiZeroFreeHeights n + 1 < Classical.choose
    (exists_xiHeightBoundaryAvoidsZeros_gt (xiZeroFreeHeights n + 1))
  exact (Classical.choose_spec
    (exists_xiHeightBoundaryAvoidsZeros_gt (xiZeroFreeHeights n + 1))).1

theorem xiZeroFreeHeights_boundaryAvoidsZeros (n : Nat) :
    xiHeightBoundaryAvoidsZeros (xiZeroFreeHeights n) := by
  cases n with
  | zero =>
      change xiHeightBoundaryAvoidsZeros
        (Classical.choose (exists_xiHeightBoundaryAvoidsZeros_gt 0))
      exact (Classical.choose_spec (exists_xiHeightBoundaryAvoidsZeros_gt 0)).2
  | succ n =>
      change xiHeightBoundaryAvoidsZeros (Classical.choose
        (exists_xiHeightBoundaryAvoidsZeros_gt (xiZeroFreeHeights n + 1)))
      exact (Classical.choose_spec
        (exists_xiHeightBoundaryAvoidsZeros_gt (xiZeroFreeHeights n + 1))).2

/-- The recursively selected zero-free heights dominate their natural index,
so the sequence escapes every bounded height window. -/
theorem nat_lt_xiZeroFreeHeights (n : Nat) :
    (n : Real) < xiZeroFreeHeights n := by
  induction n with
  | zero => simpa using xiZeroFreeHeights_zero_lt
  | succ n hn =>
      calc
        (Nat.succ n : Real) = (n : Real) + 1 := by norm_num
        _ < xiZeroFreeHeights n + 1 := by linarith
        _ < xiZeroFreeHeights (Nat.succ n) := xiZeroFreeHeights_succ_gt n

/-- Every positive critical-strip rectangle lies strictly inside the simple
factorization ball centered at zero with radius `T + 2`. -/
theorem criticalStripRectangle_subset_ball_zero (T : Real) (hT : 0 < T) :
    Complex.Rectangle (criticalStripRectangleLower T) (criticalStripRectangleUpper T) ⊆
      Metric.ball 0 |T + 2| := by
  intro z hz
  have hz_coordinates : z.re ∈ Set.Icc (0 : Real) 1 ∧ z.im ∈ Set.Icc (-T) T := by
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hz
    constructor
    · simpa only [criticalStripRectangleLower_re, criticalStripRectangleUpper_re,
        uIcc_of_le (by norm_num : (0 : Real) ≤ 1)] using hz.1
    · simpa only [criticalStripRectangleLower_im, criticalStripRectangleUpper_im,
        uIcc_of_le (by linarith : -T ≤ T)] using hz.2
  have hre : |z.re| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · linarith [hz_coordinates.1.1]
    · exact hz_coordinates.1.2
  have him : |z.im| ≤ T := abs_le.mpr hz_coordinates.2
  have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have hsum : |z.re| + |z.im| ≤ 1 + T := add_le_add hre him
  rw [Metric.mem_ball, dist_zero_right, abs_of_pos (by linarith : 0 < T + 2)]
  linarith

/-- One owner for a finite-height critical-strip rectangle: its height,
zero-free boundary, finite xi factorization, and containment proof travel
together. -/
structure XiHeightRectangleFactorData where
  height : Real
  height_pos : 0 < height
  cofactor : Complex -> Complex
  cofactor_analytic : AnalyticOnNhd Complex cofactor
    (Metric.closedBall (0 : Complex) |height + 2|)
  cofactor_nonzero : ∀ u : Metric.closedBall (0 : Complex) |height + 2|,
    cofactor u ≠ 0
  factorization : completedRiemannXi =ᶠ[codiscreteWithin
    (Metric.closedBall (0 : Complex) |height + 2|)]
      xiClosedBallFactor (0 : Complex) (height + 2) • cofactor
  rectangle_subset : Complex.Rectangle (criticalStripRectangleLower height)
    (criticalStripRectangleUpper height) ⊆ Metric.ball (0 : Complex) |height + 2|
  boundary_avoids : xiHeightBoundaryAvoidsZeros height

/-- A positive zero-free height has a finite xi factorization owner covering
its complete critical-strip rectangle. -/
theorem exists_xiHeightRectangleFactorData_at
    (T : Real) (hT : 0 < T) (hboundary : xiHeightBoundaryAvoidsZeros T) :
    ∃ D : XiHeightRectangleFactorData, D.height = T := by
  obtain ⟨g, hanalytic, hnonzero, hfactor⟩ :=
    exists_xiClosedBall_factorization (0 : Complex) (T + 2)
  refine ⟨{
    height := T
    height_pos := hT
    cofactor := g
    cofactor_analytic := hanalytic
    cofactor_nonzero := hnonzero
    factorization := hfactor
    rectangle_subset := criticalStripRectangle_subset_ball_zero T hT
    boundary_avoids := hboundary
  }, rfl⟩

/-- Above every lower bound there is one complete finite-height rectangle
owner, not merely separately chosen height and factorization witnesses. -/
theorem exists_xiHeightRectangleFactorData_gt (B : Real) :
    ∃ D : XiHeightRectangleFactorData, B < D.height := by
  obtain ⟨T, hT_gt, hboundary⟩ :=
    exists_xiHeightBoundaryAvoidsZeros_gt (max B 0)
  have hT_pos : 0 < T := by
    linarith [le_max_right B 0]
  obtain ⟨D, hD⟩ := exists_xiHeightRectangleFactorData_at T hT_pos hboundary
  refine ⟨D, ?_⟩
  rw [hD]
  linarith [le_max_left B 0]

/-- A source zero at finite height becomes strictly interior to the standard
critical-strip rectangle as soon as its absolute height is strictly below the
chosen boundary. -/
theorem strictlyInsideRectangle_criticalStrip_of_abs_im_lt
    {T : Real} (rho : sourceNontrivialZeroSet) (hheight : |rho.1.im| < T) :
    strictlyInsideRectangle
      (criticalStripRectangleLower T) (criticalStripRectangleUpper T) rho.1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using sourceNontrivialZero_zero_lt_re rho.2
  · simpa using sourceNontrivialZero_re_lt_one rho.2
  · simpa [criticalStripRectangleLower] using (abs_lt.mp hheight).1
  · simpa [criticalStripRectangleUpper] using (abs_lt.mp hheight).2

/-- A source zero that lies strictly inside the critical-strip rectangle is
in the existing closed symmetric-height truncation. -/
theorem mem_finiteHeightZeros_of_strictlyInsideRectangle_criticalStrip
    (T : Real) (rho : sourceNontrivialZeroSet)
    (hinside : strictlyInsideRectangle
      (criticalStripRectangleLower T) (criticalStripRectangleUpper T) rho.1) :
    rho ∈ finiteHeightZeros T := by
  rw [mem_finiteHeightZeros_iff]
  apply abs_le.mpr
  constructor
  · simpa using hinside.2.2.1.le
  · simpa using hinside.2.2.2.le

/-- On a zero-free horizontal boundary, the closed `finiteHeightZeros T`
truncation has no source zero at either height edge. -/
theorem abs_im_lt_of_mem_finiteHeightZeros_of_xiHeightBoundaryAvoidsZeros
    {T : Real} (hheight : xiHeightBoundaryAvoidsZeros T)
    (rho : sourceNontrivialZeroSet) (hrho : rho ∈ finiteHeightZeros T) :
    |rho.1.im| < T := by
  have hle : |rho.1.im| ≤ T := (mem_finiteHeightZeros_iff T rho).mp hrho
  apply lt_of_le_of_ne hle
  intro heq
  have hor : rho.1.im = T ∨ rho.1.im = -T := eq_or_eq_neg_of_abs_eq heq
  rcases hor with htop | hbottom
  · apply hheight.2 rho.1.re
      ⟨(sourceNontrivialZero_zero_lt_re rho.2).le,
        (sourceNontrivialZero_re_lt_one rho.2).le⟩
    have hpoint : (rho.1.re : Complex) + T * Complex.I = rho.1 := by
      apply Complex.ext <;> simp [htop]
    rw [hpoint]
    exact completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2
  · apply hheight.1 rho.1.re
      ⟨(sourceNontrivialZero_zero_lt_re rho.2).le,
        (sourceNontrivialZero_re_lt_one rho.2).le⟩
    have hpoint : (rho.1.re : Complex) - T * Complex.I = rho.1 := by
      apply Complex.ext <;> simp [hbottom]
    rw [hpoint]
    exact completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2

/-- The factor-owned finite rectangle population is exactly the existing
finite source spectral truncation whenever the rectangle lies in the owner's
open ball and the height sides are xi-zero-free. -/
theorem xiClosedBallSourceZerosInsideRectangle_eq_finiteHeightZeros
    {c : Complex} {R T : Real}
    (hT : 0 < T)
    (hrectangle : Complex.Rectangle (criticalStripRectangleLower T)
      (criticalStripRectangleUpper T) ⊆ Metric.ball c |R|)
    (hheight : xiHeightBoundaryAvoidsZeros T) :
    xiClosedBallSourceZerosInsideRectangle c R
      (criticalStripRectangleLower T) (criticalStripRectangleUpper T) =
      finiteHeightZeros T := by
  apply Finset.ext
  intro rho
  constructor
  · intro hrho
    exact mem_finiteHeightZeros_of_strictlyInsideRectangle_criticalStrip T rho
      ((mem_xiClosedBallSourceZerosInsideRectangle_iff c R
        (criticalStripRectangleLower T) (criticalStripRectangleUpper T) rho).mp hrho).2
  · intro hrho
    apply (mem_xiClosedBallSourceZerosInsideRectangle_iff c R
      (criticalStripRectangleLower T) (criticalStripRectangleUpper T) rho).mpr
    have hinside := strictlyInsideRectangle_criticalStrip_of_abs_im_lt rho
      (abs_im_lt_of_mem_finiteHeightZeros_of_xiHeightBoundaryAvoidsZeros hheight rho hrho)
    refine ⟨?_, hinside⟩
    have hball : rho.1 ∈ Metric.ball c |R| := by
      apply hrectangle
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      constructor
      · rw [uIcc_of_le (standardRectangle_criticalStripRectangle hT).1.le]
        exact ⟨hinside.1.le, hinside.2.1.le⟩
      · rw [uIcc_of_le (standardRectangle_criticalStripRectangle hT).2.le]
        exact ⟨hinside.2.2.1.le, hinside.2.2.2.le⟩
    have hsupport : rho.1 ∈ (xiClosedBallDivisor c R).support :=
      (xiClosedBallDivisor_mem_support_iff c R
        (Metric.ball_subset_closedBall hball)).mpr
        (completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2)
    exact (xiClosedBallDivisor_support_finite c R).mem_toFinset.mpr hsupport

/-- The finite critical-strip rectangle reads exactly the existing spectral
partial sum at height `T`.  This is still a finite contour statement: no
height limit or arithmetic-side comparison is assumed. -/
theorem xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSpectralSum
    (F : CompactLogTest) {c : Complex} {R T : Real} {g : Complex -> Complex}
    (hanalytic : AnalyticOnNhd Complex g (Metric.closedBall c |R|))
    (hnonzero : ∀ q : Metric.closedBall c |R|, g q ≠ 0)
    (hfactor : completedRiemannXi =ᶠ[codiscreteWithin (Metric.closedBall c |R|)]
      xiClosedBallFactor c R • g)
    (hT : 0 < T)
    (hrectangle : Complex.Rectangle (criticalStripRectangleLower T)
      (criticalStripRectangleUpper T) ⊆ Metric.ball c |R|)
    (hheight : xiHeightBoundaryAvoidsZeros T) :
    xiRectangleBoundaryIntegral (xiContourKernel F)
      (criticalStripRectangleLower T) (criticalStripRectangleUpper T) =
      -(2 * (Real.pi : Complex) * Complex.I * finiteSpectralSum F T) := by
  rw [xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSourceSpectralSum_of_factor_support
    F hanalytic hnonzero hfactor hrectangle
    (standardRectangle_criticalStripRectangle hT)
    (xiRectangleBoundaryAvoidsZeros_criticalStripRectangle T hheight)]
  rw [xiClosedBallSourceZerosInsideRectangle_eq_finiteHeightZeros hT hrectangle hheight]
  rfl

/-- The finite critical-strip rectangle readout consumes one complete owner,
so its cofactor, factor support, zero-free boundary, and spectral truncation
cannot be mixed across heights. -/
theorem XiHeightRectangleFactorData.xiRectangleBoundaryIntegral_readout
    (D : XiHeightRectangleFactorData) (F : CompactLogTest) :
    xiRectangleBoundaryIntegral (xiContourKernel F)
      (criticalStripRectangleLower D.height) (criticalStripRectangleUpper D.height) =
      -(2 * (Real.pi : Complex) * Complex.I * finiteSpectralSum F D.height) := by
  exact xiRectangleBoundaryIntegral_xiContourKernel_eq_neg_finiteSpectralSum F
    D.cofactor_analytic D.cofactor_nonzero D.factorization D.height_pos
    D.rectangle_subset D.boundary_avoids

end C1XiFiniteHeightRectangle
end Source
end ConnesWeilRH
