import ConnesWeilRH.Dev.C1P2OrbitPhysicalKernelIntegrandBounds

namespace ConnesWeilRH
namespace Source
namespace C1P2OrbitPhysicalKernelCoboundary

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open C1G8R0OrbitGeometry
open C1P2OrbitPhysicalKernelIntegrandBounds
open C1P2OrbitPhysicalProfileReadback
open C1P2SignedBudget
open C1SameOwnerWeil
open CCM25Concrete.CompactLogConvolution

noncomputable section

theorem orbitWeightedKernelIntegrand_continuous
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) :
    Continuous (fun t => orbitWeightedKernelIntegrand geometry x t) := by
  unfold orbitWeightedKernelIntegrand
  fun_prop

theorem differentiableAt_orbitWeightedKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : Real) :
    DifferentiableAt ℝ (fun u => orbitWeightedKernelIntegrand geometry x u) t := by
  let raw := orbitRawFactor geometry
  have harg : DifferentiableAt ℝ
      (fun u : Real => ((x / 2 - u : Real) : Complex)) t := by
    exact (((hasDerivAt_const (x := t) (c := x / 2)).sub
      (hasDerivAt_id t)).ofReal_comp).differentiableAt
  have hexp : DifferentiableAt ℝ
      (fun u : Real => Complex.exp (((x / 2 - u : Real) : Complex))) t := by
    exact (Complex.hasDerivAt_exp _).comp t harg.hasDerivAt |>.differentiableAt
  have hrawLeft : DifferentiableAt ℝ (fun u : Real => raw.test (-u)) t := by
    have hraw : DifferentiableAt ℝ (fun u : Real => raw.test u) (-t) :=
      ((raw.test.smooth ⊤).differentiable (by simp) (-t))
    exact hraw.comp t (hasDerivAt_neg t).differentiableAt
  have hstar : DifferentiableAt ℝ
      (fun u : Real => star (raw.test (-u))) t :=
    Complex.conjCLE.differentiableAt.comp t hrawLeft
  have hrawRight : DifferentiableAt ℝ
      (fun u : Real => raw.test (x - u)) t := by
    have hraw : DifferentiableAt ℝ (fun u : Real => raw.test u) (x - t) :=
      ((raw.test.smooth ⊤).differentiable (by simp) (x - t))
    exact hraw.comp t (((hasDerivAt_const (x := t) (c := x)).sub
      (hasDerivAt_id t)).differentiableAt)
  simpa [orbitWeightedKernelIntegrand, raw] using hexp.mul hstar |>.mul hrawRight

theorem differentiableAt_orbitFinitePhysicalKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) :
    DifferentiableAt ℝ (orbitFinitePhysicalKernelIntegrand geometry) t := by
  unfold orbitFinitePhysicalKernelIntegrand
  apply DifferentiableAt.fun_sum
  intro n hn
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.const_mul
  exact Complex.reCLM.differentiableAt.comp t
    (differentiableAt_orbitWeightedKernelIntegrand geometry (Real.log n) t)

theorem hasDerivAt_conjugate_of_hasDerivAt
    {f : Real → Complex} {f' : Complex} {t : Real}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun u => star (f u)) (star f') t := by
  have hcomp :
      fderiv ℝ (⇑Complex.conjCLE ∘ f) t =
        (Complex.conjCLE : Complex →L[ℝ] Complex) ∘SL fderiv ℝ f t :=
    Complex.conjCLE.comp_fderiv
  have heq :
      fderiv ℝ (⇑Complex.conjCLE ∘ f) t =
        ContinuousLinearMap.toSpanSingleton ℝ (star f') := by
    rw [hcomp]
    apply ContinuousLinearMap.ext
    intro y
    change Complex.conjCLE (fderiv ℝ f t y) = _
    rw [fderiv_eq_smul_deriv, hf.deriv]
    simp [Complex.conjCLE_apply, smul_eq_mul]
  have hfd :=
    (Complex.conjCLE.differentiableAt.comp t hf.differentiableAt).hasFDerivAt
  have hfd' : HasFDerivAt (⇑Complex.conjCLE ∘ f)
      (ContinuousLinearMap.toSpanSingleton ℝ (star f')) t := by
    rw [← heq]
    exact hfd
  apply (hasDerivAt_iff_hasFDerivAt).2
  simpa [Function.comp_def, Complex.conjCLE_apply] using hfd'

def orbitWeightedKernelIntegrandDerivative
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x : Real) (t : Real) : Complex :=
  by
    let raw := orbitRawFactor geometry
    let e := Complex.exp (((x / 2 - t : Real) : Complex))
    let left := star (raw.test (-t))
    let right := raw.test (x - t)
    let dleft := star (deriv (raw.test : Real → Complex) (-t))
    let dright := deriv (raw.test : Real → Complex) (x - t)
    exact -(e * left * right) - e * dleft * right - e * left * dright

theorem hasDerivAt_orbitWeightedKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (x t : Real) :
    HasDerivAt (fun u => orbitWeightedKernelIntegrand geometry x u)
      (orbitWeightedKernelIntegrandDerivative geometry x t) t := by
  let raw := orbitRawFactor geometry
  have harg : HasDerivAt
      (fun u : Real => ((x / 2 - u : Real) : Complex)) (-1) t := by
    simpa using (((hasDerivAt_const (x := t) (c := x / 2)).sub
      (hasDerivAt_id t)).ofReal_comp)
  have hexp := (Complex.hasDerivAt_exp _).comp t harg
  have hrawLeft : HasDerivAt (fun u : Real => raw.test (-u))
      (-deriv (raw.test : Real → Complex) (-t)) t := by
    have htest :=
      ((raw.test.smooth ⊤).differentiable (by simp) (-t)).hasDerivAt
    have hneg : HasDerivAt (fun u : Real => -u) (-1) t :=
      hasDerivAt_neg t
    simpa [smul_eq_mul] using htest.scomp t hneg
  have hstarLeft := hasDerivAt_conjugate_of_hasDerivAt hrawLeft
  have hrawRight : HasDerivAt (fun u : Real => raw.test (x - u))
      (-deriv (raw.test : Real → Complex) (x - t)) t := by
    have htest :=
      ((raw.test.smooth ⊤).differentiable (by simp) (x - t)).hasDerivAt
    have hshift : HasDerivAt (fun u : Real => x - u) (-1) t := by
      simpa using (hasDerivAt_const (x := t) (c := x)).sub (hasDerivAt_id t)
    simpa [smul_eq_mul] using htest.scomp t hshift
  have hprod := hexp.mul hstarLeft |>.mul hrawRight
  unfold orbitWeightedKernelIntegrand orbitWeightedKernelIntegrandDerivative
  dsimp [raw]
  convert hprod using 1 <;> simp [Function.comp_def] <;> ring

def orbitFinitePhysicalKernelIntegrandDerivative
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) : Real :=
  Finset.sum (orbitVisiblePrimeRange geometry) (fun n =>
    ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : Real)) *
      (2 * (orbitWeightedKernelIntegrandDerivative geometry (Real.log n) t).re))

theorem hasDerivAt_orbitFinitePhysicalKernelIntegrand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) :
    HasDerivAt (orbitFinitePhysicalKernelIntegrand geometry)
      (orbitFinitePhysicalKernelIntegrandDerivative geometry t) t := by
  unfold orbitFinitePhysicalKernelIntegrand orbitFinitePhysicalKernelIntegrandDerivative
  apply HasDerivAt.fun_sum
  intro n hn
  have hcomplex := hasDerivAt_orbitWeightedKernelIntegrand geometry (Real.log n) t
  have hreal :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomplex
  apply HasDerivAt.const_mul
  apply HasDerivAt.const_mul
  simpa [Function.comp_def, Complex.reCLM_apply] using hreal

def physicalKernelWindowLeft
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  -((geometry.orbitIndex + 2 : Nat) : Real)

def physicalKernelWindowRight
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  ((geometry.orbitIndex + 2 : Nat) : Real)

/-- The concrete same-owner integration-by-parts primitive.  Its endpoint
vanishing comes from the raw factor's strict support window. -/
def orbitPhysicalKernelCoboundaryQ
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) : Real :=
  t * orbitFinitePhysicalKernelIntegrand geometry t

/-- The residual left after differentiating `t * F(t)`, where `F` is the
actual signed finite physical-prime aggregate. -/
def orbitPhysicalKernelCoboundaryResidual
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) : Real :=
  -t * orbitFinitePhysicalKernelIntegrandDerivative geometry t

theorem hasDerivAt_orbitPhysicalKernelCoboundaryQ
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (t : Real) :
    HasDerivAt (orbitPhysicalKernelCoboundaryQ geometry)
      (orbitFinitePhysicalKernelIntegrand geometry t -
        orbitPhysicalKernelCoboundaryResidual geometry t) t := by
  have hproduct := (hasDerivAt_id t).mul
    (hasDerivAt_orbitFinitePhysicalKernelIntegrand geometry t)
  unfold orbitPhysicalKernelCoboundaryQ orbitPhysicalKernelCoboundaryResidual
  change HasDerivAt (fun u : Real => u * orbitFinitePhysicalKernelIntegrand geometry u)
    (orbitFinitePhysicalKernelIntegrand geometry t -
      -t * orbitFinitePhysicalKernelIntegrandDerivative geometry t) t
  simpa [Pi.mul_apply] using hproduct

theorem orbitPhysicalKernelCoboundaryQ_left_boundary
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitPhysicalKernelCoboundaryQ geometry (physicalKernelWindowLeft geometry) = 0 := by
  unfold orbitPhysicalKernelCoboundaryQ physicalKernelWindowLeft
  rw [orbitFinitePhysicalKernelIntegrand_eq_zero_of_not_mem_raw_support_window]
  · ring
  · simp

theorem orbitPhysicalKernelCoboundaryQ_right_boundary
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitPhysicalKernelCoboundaryQ geometry (physicalKernelWindowRight geometry) = 0 := by
  unfold orbitPhysicalKernelCoboundaryQ physicalKernelWindowRight
  rw [orbitFinitePhysicalKernelIntegrand_eq_zero_of_not_mem_raw_support_window]
  · ring
  · simp

theorem orbitFinitePhysicalKernelIntegrand_continuous
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    Continuous (orbitFinitePhysicalKernelIntegrand geometry) := by
  unfold orbitFinitePhysicalKernelIntegrand
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  apply Continuous.const_mul
  exact Complex.continuous_re.comp
    (orbitWeightedKernelIntegrand_continuous geometry (Real.log n))

/--
An owner-preserving integration-by-parts certificate for the actual finite
physical-kernel aggregate.  The derivative is deliberately typed against the
actual aggregate, not against a primewise surrogate, so all prime cancellation
remains inside `orbitFinitePhysicalKernelIntegrand`.
-/
structure OrbitPhysicalKernelCoboundaryCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) where
  Q : Real → Real
  residual : Real → Real
  Q_intervalIntegrable :
    IntervalIntegrable (deriv Q) volume
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry)
  difference_intervalIntegrable :
    IntervalIntegrable
      (fun t => orbitFinitePhysicalKernelIntegrand geometry t - residual t) volume
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry)
  residual_intervalIntegrable :
    IntervalIntegrable residual volume
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry)
  derivative_identity : ∀ x ∈ Set.uIcc
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry),
      HasDerivAt Q
        (orbitFinitePhysicalKernelIntegrand geometry x - residual x) x
  left_boundary : Q (physicalKernelWindowLeft geometry) = 0
  right_boundary : Q (physicalKernelWindowRight geometry) = 0
  residual_budget :
    archimedeanTerm g.convolutionSquare +
        ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry), residual t ≤ 0

theorem OrbitPhysicalKernelCoboundaryCertificate.derivative_eq_aggregate_sub_residual
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : OrbitPhysicalKernelCoboundaryCertificate geometry)
    {x : Real}
    (hx : x ∈ Set.uIcc
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry)) :
    deriv certificate.Q x =
      orbitFinitePhysicalKernelIntegrand geometry x - certificate.residual x := by
  exact (certificate.derivative_identity x hx).deriv

theorem intervalIntegral_orbitFinitePhysicalKernelIntegrand_eq_residual
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : OrbitPhysicalKernelCoboundaryCertificate geometry) :
    ∫ t in (physicalKernelWindowLeft geometry)..
        (physicalKernelWindowRight geometry),
        orbitFinitePhysicalKernelIntegrand geometry t =
      ∫ t in (physicalKernelWindowLeft geometry)..
        (physicalKernelWindowRight geometry), certificate.residual t := by
  have hderiv := intervalIntegral.integral_eq_sub_of_hasDerivAt
    certificate.derivative_identity certificate.difference_intervalIntegrable
  have hderivQ :
      ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry), deriv certificate.Q t =
        ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          (orbitFinitePhysicalKernelIntegrand geometry t - certificate.residual t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simpa using (certificate.derivative_identity t ht).deriv
  have hzero :
      ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry), deriv certificate.Q t = 0 := by
    rw [hderivQ, hderiv, certificate.right_boundary, certificate.left_boundary, sub_self]
  have hpoint : ∀ t ∈ Set.uIcc
      (physicalKernelWindowLeft geometry) (physicalKernelWindowRight geometry),
      orbitFinitePhysicalKernelIntegrand geometry t =
        deriv certificate.Q t + certificate.residual t := by
    intro t ht
    rw [certificate.derivative_eq_aggregate_sub_residual ht]
    ring
  calc
    ∫ t in (physicalKernelWindowLeft geometry)..
        (physicalKernelWindowRight geometry),
        orbitFinitePhysicalKernelIntegrand geometry t =
        ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry),
          (deriv certificate.Q t + certificate.residual t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t ht
    _ = (∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry), deriv certificate.Q t) +
        ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry), certificate.residual t := by
      rw [intervalIntegral.integral_add certificate.Q_intervalIntegrable
        certificate.residual_intervalIntegrable]
    _ = ∫ t in (physicalKernelWindowLeft geometry)..
          (physicalKernelWindowRight geometry), certificate.residual t := by
      rw [hzero, zero_add]

theorem orbitWindowSemiLocalGate_of_coboundaryCertificate
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    {geometry : OrbitG8Geometry rho g}
    (certificate : OrbitPhysicalKernelCoboundaryCertificate geometry) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g := by
  apply (orbitWindowSemiLocalGate_iff_finitePhysicalKernelIntervalBudget geometry).mpr
  change archimedeanTerm g.convolutionSquare +
      (∫ t in (physicalKernelWindowLeft geometry)..
        (physicalKernelWindowRight geometry),
        orbitFinitePhysicalKernelIntegrand geometry t) ≤ 0
  rw [intervalIntegral_orbitFinitePhysicalKernelIntegrand_eq_residual certificate]
  simpa [physicalKernelWindowLeft, physicalKernelWindowRight] using
    certificate.residual_budget

theorem sourceRH_of_right_orbitGeometry_coboundaryCertificate
    (hproducer : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          ∃ geometry : OrbitG8Geometry rho g,
            Nonempty (OrbitPhysicalKernelCoboundaryCertificate geometry)) :
    RHDefinitionBridge.standard.SourceRH := by
  apply sourceRH_of_right_orbitGeometry_finitePhysicalKernelIntervalBudget
  intro rho hright
  obtain ⟨g, geometry, ⟨certificate⟩⟩ := hproducer rho hright
  refine ⟨g, geometry, ?_⟩
  change archimedeanTerm g.convolutionSquare +
      (∫ t in (physicalKernelWindowLeft geometry)..
        (physicalKernelWindowRight geometry),
        orbitFinitePhysicalKernelIntegrand geometry t) ≤ 0
  rw [intervalIntegral_orbitFinitePhysicalKernelIntegrand_eq_residual certificate]
  simpa [physicalKernelWindowLeft, physicalKernelWindowRight] using
    certificate.residual_budget

end
end C1P2OrbitPhysicalKernelCoboundary
end Source
end ConnesWeilRH
