import ConnesWeilRH.Dev.C1HealthyYoshidaInterpolation

/-!
# C1HealthyYoshidaMinimalInterpolation - four-node interpolation on the healthy owner

The healthy Yoshida detector consumes only three finite vanishings and
off-line detection at `rho`.  The old `plus and minus I/2` half-density values
belong to the normalized additive-doubling algebra and are not detector fields on the
healthy compact-log owner.  This module exposes the minimal four-node
interpolation problem in the same narrow support window.

The construction remains linear interpolation only.  It does not assert the
strict local-Weil sign, which is reduced separately to archimedean positivity.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaMinimalInterpolation

open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedYoshidaBridge
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open C1HealthyYoshidaDetector

/-- The four nodes actually consumed by the healthy detector. -/
noncomputable def healthyDetectorNodeSet (rho : Complex) : Finset Complex :=
  {0, 1 / 2, 1, rho}

/-- A convenient normalized target: vanish at the criterion nodes and take
the nonzero value `-1` at the selected source zero. -/
noncomputable def healthyDetectorNodeTarget
    (rho : Complex)
    (z : FiniteMellinNode (healthyDetectorNodeSet rho)) : Complex :=
  if z.1 = rho then -1 else 0

/-- The minimal healthy-owner interpolation data: the three criterion
vanishings and nonzero detection at `rho`. -/
def HealthyMinimalLaplaceRealizes (rho : Complex) (g : CompactLogTest) : Prop :=
  CompactLogTest.laplaceAt g 0 = 0 /\
    CompactLogTest.laplaceAt g (1 / 2) = 0 /\
      CompactLogTest.laplaceAt g 1 = 0 /\
        CompactLogTest.laplaceAt g rho ≠ 0

private theorem source_nontrivial_zero_ne_zero
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ 0 := by
  intro hzero
  have hpos := sourceNontrivialZero_zero_lt_re hrho
  rw [hzero] at hpos
  norm_num at hpos

private theorem source_nontrivial_zero_ne_half
    {rho : Complex}
    (hoff : rho.re ≠ 1 / 2) :
    rho ≠ (1 / 2 : Complex) := by
  intro hhalf
  apply hoff
  calc
    rho.re = (1 / 2 : Complex).re := congrArg Complex.re hhalf
    _ = 1 / 2 := by norm_num

private theorem source_nontrivial_zero_ne_one
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    rho ≠ 1 := by
  intro hone
  have hlt := sourceNontrivialZero_re_lt_one hrho
  rw [hone] at hlt
  norm_num at hlt

private theorem healthyDetectorNodeTarget_at_zero
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    healthyDetectorNodeTarget rho
        (⟨0, by simp [healthyDetectorNodeSet]⟩ :
          FiniteMellinNode (healthyDetectorNodeSet rho)) = 0 := by
  dsimp [healthyDetectorNodeTarget]
  rw [if_neg]
  exact Ne.symm (source_nontrivial_zero_ne_zero hrho)

private theorem healthyDetectorNodeTarget_at_half
    {rho : Complex}
    (hoff : rho.re ≠ 1 / 2) :
    healthyDetectorNodeTarget rho
        (⟨1 / 2, by simp [healthyDetectorNodeSet]⟩ :
          FiniteMellinNode (healthyDetectorNodeSet rho)) = 0 := by
  dsimp [healthyDetectorNodeTarget]
  rw [if_neg]
  exact Ne.symm (source_nontrivial_zero_ne_half hoff)

private theorem healthyDetectorNodeTarget_at_one
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho) :
    healthyDetectorNodeTarget rho
        (⟨1, by simp [healthyDetectorNodeSet]⟩ :
          FiniteMellinNode (healthyDetectorNodeSet rho)) = 0 := by
  dsimp [healthyDetectorNodeTarget]
  rw [if_neg]
  exact Ne.symm (source_nontrivial_zero_ne_one hrho)

private theorem healthyDetectorNodeTarget_at_rho
    (rho : Complex) :
    healthyDetectorNodeTarget rho
        (⟨rho, by simp [healthyDetectorNodeSet]⟩ :
          FiniteMellinNode (healthyDetectorNodeSet rho)) = -1 := by
  simp [healthyDetectorNodeTarget]

/-- The normalized four-node values provide exactly the minimal healthy
detector interpolation data. -/
theorem healthyMinimalLaplaceRealizes_of_node_values
    {rho : Complex} {g : CompactLogTest}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    (hvalues : forall z : FiniteMellinNode (healthyDetectorNodeSet rho),
      CompactLogTest.laplaceAt g z.1 = healthyDetectorNodeTarget rho z) :
    HealthyMinimalLaplaceRealizes rho g := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      CompactLogTest.laplaceAt g 0 =
          healthyDetectorNodeTarget rho
            (⟨0, by simp [healthyDetectorNodeSet]⟩ :
              FiniteMellinNode (healthyDetectorNodeSet rho)) := by
        simpa using hvalues
          (⟨0, by simp [healthyDetectorNodeSet]⟩ :
            FiniteMellinNode (healthyDetectorNodeSet rho))
      _ = 0 := healthyDetectorNodeTarget_at_zero hrho
  · calc
      CompactLogTest.laplaceAt g (1 / 2) =
          healthyDetectorNodeTarget rho
            (⟨1 / 2, by simp [healthyDetectorNodeSet]⟩ :
              FiniteMellinNode (healthyDetectorNodeSet rho)) := by
        simpa using hvalues
          (⟨1 / 2, by simp [healthyDetectorNodeSet]⟩ :
            FiniteMellinNode (healthyDetectorNodeSet rho))
      _ = 0 := healthyDetectorNodeTarget_at_half hoff
  · calc
      CompactLogTest.laplaceAt g 1 =
          healthyDetectorNodeTarget rho
            (⟨1, by simp [healthyDetectorNodeSet]⟩ :
              FiniteMellinNode (healthyDetectorNodeSet rho)) := by
        simpa using hvalues
          (⟨1, by simp [healthyDetectorNodeSet]⟩ :
            FiniteMellinNode (healthyDetectorNodeSet rho))
      _ = 0 := healthyDetectorNodeTarget_at_one hrho
  · intro hzero
    have hvalue := hvalues
      (⟨rho, by simp [healthyDetectorNodeSet]⟩ :
        FiniteMellinNode (healthyDetectorNodeSet rho))
    rw [hzero, healthyDetectorNodeTarget_at_rho] at hvalue
    norm_num at hvalue

/-- The four-node conditions imply the healthy CC20 finite-vanishing
criterion. -/
theorem HealthyMinimalLaplaceRealizes.vanishesOn_cc20Triple
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyMinimalLaplaceRealizes rho g) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g := by
  intro p _hp
  change CompactLogTest.laplaceAt g (criticalVanishingPointValue p) = 0
  cases p
  · simpa [criticalVanishingPointValue] using h.1
  · simpa [criticalVanishingPointValue] using h.2.1
  · simpa [criticalVanishingPointValue] using h.2.2.1

/-- The fourth minimal condition is exactly off-line detection. -/
theorem HealthyMinimalLaplaceRealizes.detects_rho
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyMinimalLaplaceRealizes rho g) :
    CompactLogTest.laplaceAt g rho ≠ 0 :=
  h.2.2.2

/-- The fixed residual window used by the four-node interpolator lies inside
the centered Yoshida endpoint window. -/
private theorem fixedWindow_log_bounds :
    -(Real.log 2 / 2) <
        Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower /\
      Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowUpper <
        Real.log 2 / 2 := by
  have hlowerLog :
      Real.log (1 / 2 : Real) <
        Real.log ((3 / 4 : Real) * (3 / 4 : Real)) := by
    apply Real.log_lt_log
    · norm_num
    · norm_num
  have hlowerLeft : Real.log (1 / 2 : Real) = -Real.log 2 := by
    rw [show (1 / 2 : Real) = (2 : Real)⁻¹ by norm_num, Real.log_inv]
  have hlowerRight :
      Real.log ((3 / 4 : Real) * (3 / 4 : Real)) =
        2 * Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower := by
    rw [Real.log_mul (by norm_num : (3 / 4 : Real) ≠ 0)
      (by norm_num : (3 / 4 : Real) ≠ 0)]
    simp only [CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower]
    ring
  have hlower :
      -(Real.log 2 / 2) <
        Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower := by
    rw [hlowerLeft, hlowerRight] at hlowerLog
    linarith
  have hupperLog :
      Real.log ((5 / 4 : Real) * (5 / 4 : Real)) < Real.log 2 := by
    apply Real.log_lt_log
    · norm_num
    · norm_num
  have hupperLeft :
      Real.log ((5 / 4 : Real) * (5 / 4 : Real)) =
        2 * Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowUpper := by
    rw [Real.log_mul (by norm_num : (5 / 4 : Real) ≠ 0)
      (by norm_num : (5 / 4 : Real) ≠ 0)]
    simp only [CCM25Concrete.SelectedYoshidaBridge.fixedWindowUpper]
    ring
  have hupper :
      Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowUpper <
        Real.log 2 / 2 := by
    rw [hupperLeft] at hupperLog
    linarith
  exact ⟨hlower, hupper⟩

/-- The narrow residual-window interpolation theorem realizes the four
healthy detector nodes on the root-support class consumed by the
Yoshida--Connes--Consani endpoint theorem. -/
theorem exists_healthyMinimalLaplaceRealizes_rootSupport_logTwoHalf
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    exists g : CompactLogTest,
      HealthyMinimalLaplaceRealizes rho g /\
        CompactLogTest.laplaceAt g rho = -1 /\
          Function.support g.test ⊆
            Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) := by
  classical
  have hlower :
      Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower < 0 :=
    Real.log_neg CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower_pos
      CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower_lt_one
  have hupper :
      0 < Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowUpper :=
    Real.log_pos CCM25Concrete.SelectedYoshidaBridge.one_lt_fixedWindowUpper
  rcases CompactLogTest.exists_residualWindow_correction (healthyDetectorNodeSet rho)
      (lower := Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower)
      (upper := Real.log CCM25Concrete.SelectedYoshidaBridge.fixedWindowUpper)
      hlower hupper (healthyDetectorNodeTarget rho) with
    ⟨g, hsupport, hvalues⟩
  have hrealizes :=
    healthyMinimalLaplaceRealizes_of_node_values hrho hoff hvalues
  have hrhoValue := hvalues
    (⟨rho, by simp [healthyDetectorNodeSet]⟩ :
      FiniteMellinNode (healthyDetectorNodeSet rho))
  have hwindow := fixedWindow_log_bounds
  refine ⟨g, hrealizes, ?_, ?_⟩
  · simpa [healthyDetectorNodeTarget] using hrhoValue
  · intro x hx
    rcases hsupport hx with ⟨hlower, hupper⟩
    exact ⟨hwindow.1.le.trans hlower.le, hupper.le.trans hwindow.2.le⟩

/-- The same four-node interpolator has a prime-free Hermitian square.  This
is derived from its stronger root-support certificate, so endpoint consumers
and square-support consumers use the same constructed test. -/
theorem exists_healthyMinimalLaplaceRealizes_primeFreeSquare
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    exists g : CompactLogTest,
      HealthyMinimalLaplaceRealizes rho g /\
        CompactLogTest.laplaceAt g rho = -1 /\
          Function.support g.convolutionSquare.test ⊆
            Set.Ioo (-Real.log 2) (Real.log 2) := by
  rcases exists_healthyMinimalLaplaceRealizes_rootSupport_logTwoHalf hrho hoff with
    ⟨g, hrealizes, hrhoValue, hsupport⟩
  refine ⟨g, hrealizes, hrhoValue, ?_⟩
  have hwindow :=
    CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g hsupport
  have htwo : (2 : Real) * (Real.log 2 / 2) = Real.log 2 := by ring
  rw [htwo] at hwindow
  exact hwindow

/-- The narrow four-node interpolation root supplies all non-sign fields of
healthy detector data once the remaining archimedean positivity is proved. -/
theorem healthyDetectorData_of_HealthyMinimalLaplaceRealizes_of_archimedeanTerm_pos
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyMinimalLaplaceRealizes rho g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (harch : 0 < C1SameOwnerWeil.archimedeanTerm g.convolutionSquare) :
    HealthyYoshidaDetectorData rho g := by
  refine
    { compactSupportSmooth := C1.healthyCC20CompactSupportSmooth g
      vanishesOnF := h.vanishesOn_cc20Triple
      detectsRho := h.detects_rho
      weilSquareSumPositive := ?_ }
  exact
    (weilSquareSumPositive_iff_archimedeanTerm_pos_of_vanishesOn_cc20Triple
      g h.vanishesOn_cc20Triple hsupport).mpr harch

end C1HealthyYoshidaMinimalInterpolation
end Source
end ConnesWeilRH
