import ConnesWeilRH.Dev.C1XiRemovablePole
import ConnesWeilRH.Dev.C1XiResidue

/-!
# C1XiGlobalDifference - global entire extension of the H-A1 difference

The local H-A2 theorem supplies an analytic extension at one source-indexed
xi zero.  This file assembles those local extensions into one global function
`xiGlobalWeightedDifference`.  The function agrees with
`logDeriv completedRiemannXi - weightedRegularizedZeroSum` away from the xi
divisor and is analytic at every complex point.

The local extension is selected independently at each zero.  The isolating
ball from the same zero owner is what makes the piecewise definition agree
with that selected extension on a punctured neighborhood.  No growth bound,
Hadamard product, or constant-value conclusion is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiGlobalDifference

open Filter
open C1XiGlobalWeightedZeroSum
open C1XiRemovablePole
open C1XiResidue
open C1SpectralWeil
open CC20YoshidaNearZeros
open CC20ZetaCounting
open scoped Topology

noncomputable section

/-- The raw H-A1 difference on the ordinary zero-free domain. -/
noncomputable def xiLogDerivWeightedDifferenceRaw (s : Complex) : Complex :=
  logDeriv completedRiemannXi s - weightedRegularizedZeroSum s

/-- All data selected from one local H-A2 cancellation certificate. -/
structure XiLocalWeightedDifferenceData
    (rho : sourceNontrivialZeroSet) where
  cofactor : Complex -> Complex
  extension : Complex -> Complex
  radius : Real
  radius_pos : 0 < radius
  cofactor_analytic : AnalyticAt Complex cofactor rho.1
  cofactor_nonzero : cofactor rho.1 ≠ 0
  extension_analytic :
    AnalyticOnNhd Complex extension (Metric.ball rho.1 radius)
  punctured_eq :
    ∀ᶠ s in 𝓝[≠] rho.1,
      xiLogDerivWeightedDifferenceRaw s = extension s
  ball_formula : ∀ s ∈ Metric.ball rho.1 radius,
    extension s =
      logDeriv cofactor s - (xiMultiplicity rho : Complex) / rho.1 -
        weightedRegularizedZeroSumWithout rho s

theorem xiLocalWeightedDifferenceData_nonempty
    (rho : sourceNontrivialZeroSet) :
    Nonempty (XiLocalWeightedDifferenceData rho) := by
  obtain ⟨h, H, r, hr, hanalytic, hnonzero, hH, hpunct, hformula⟩ :=
    exists_local_xiLogDeriv_weightedDifference rho
  exact ⟨
    { cofactor := h
      extension := H
      radius := r
      radius_pos := hr
      cofactor_analytic := hanalytic
      cofactor_nonzero := hnonzero
      extension_analytic := hH
      punctured_eq := by
        simpa only [xiLogDerivWeightedDifferenceRaw] using hpunct
      ball_formula := hformula }⟩

/-- A fixed local H-A2 certificate for each source-indexed zero.  The use of
choice is only a selection of already-proved local data; it is not a new
mathematical assumption. -/
noncomputable def xiLocalWeightedDifferenceData
    (rho : sourceNontrivialZeroSet) : XiLocalWeightedDifferenceData rho :=
  Classical.choice (xiLocalWeightedDifferenceData_nonempty rho)

/-- The global piecewise extension: use the selected local analytic extension
at xi zeros and the raw logarithmic-derivative difference elsewhere. -/
noncomputable def xiGlobalWeightedDifference (s : Complex) : Complex :=
  dite (completedRiemannXi s = 0)
    (fun hzero =>
      (xiLocalWeightedDifferenceData
        ⟨s, (completedRiemannXi_eq_zero_iff_sourceNontrivialZero s).mp hzero⟩).extension s)
    (fun _ => xiLogDerivWeightedDifferenceRaw s)

theorem xiGlobalWeightedDifference_eq_raw
    {s : Complex} (hs : completedRiemannXi s ≠ 0) :
    xiGlobalWeightedDifference s = xiLogDerivWeightedDifferenceRaw s := by
  simp only [xiGlobalWeightedDifference, dif_neg hs]

theorem xiGlobalWeightedDifference_eq_local_extension
    (rho : sourceNontrivialZeroSet) :
    xiGlobalWeightedDifference rho.1 =
      (xiLocalWeightedDifferenceData rho).extension rho.1 := by
  have hzero : completedRiemannXi rho.1 = 0 :=
    completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2
  rw [xiGlobalWeightedDifference, dif_pos hzero]

theorem xiLogDerivWeightedDifferenceRaw_analyticAt_of_ne_zero
    {s : Complex} (hs : completedRiemannXi s ≠ 0) :
    AnalyticAt Complex xiLogDerivWeightedDifferenceRaw s := by
  have hne : ∀ᶠ z in 𝓝 s, completedRiemannXi z ≠ 0 :=
    (((differentiable_completedRiemannXi.continuous).continuousAt).ne_iff_eventually_ne
      continuousAt_const).mp hs
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [hne] with z hz
  have hlog : DifferentiableAt Complex (logDeriv completedRiemannXi) z :=
    differentiableAt_logDeriv_of_analyticAt_of_ne_zero
      (differentiable_completedRiemannXi.analyticAt z) hz
  obtain ⟨D, hD⟩ := weightedRegularizedZeroSum_hasDerivAt z hz
  exact hlog.sub hD.differentiableAt

theorem xiGlobalWeightedDifference_eq_raw_eventually
    {s : Complex} (hs : completedRiemannXi s ≠ 0) :
    ∀ᶠ z in 𝓝 s,
      xiGlobalWeightedDifference z = xiLogDerivWeightedDifferenceRaw z := by
  have hne : ∀ᶠ z in 𝓝 s, completedRiemannXi z ≠ 0 :=
    (((differentiable_completedRiemannXi.continuous).continuousAt).ne_iff_eventually_ne
      continuousAt_const).mp hs
  filter_upwards [hne] with z hz
  exact xiGlobalWeightedDifference_eq_raw hz

theorem xiGlobalWeightedDifference_analyticAt (s : Complex) :
    AnalyticAt Complex xiGlobalWeightedDifference s := by
  by_cases hs : completedRiemannXi s ≠ 0
  · have hEq : (fun z : Complex => xiGlobalWeightedDifference z) =ᶠ[𝓝 s]
        (fun z : Complex => xiLogDerivWeightedDifferenceRaw z) :=
      xiGlobalWeightedDifference_eq_raw_eventually hs
    exact (xiLogDerivWeightedDifferenceRaw_analyticAt_of_ne_zero hs).congr hEq.symm
  · have hs_zero : completedRiemannXi s = 0 := by
      exact Classical.not_not.mp hs
    let rho : sourceNontrivialZeroSet :=
      ⟨s, (completedRiemannXi_eq_zero_iff_sourceNontrivialZero s).mp hs_zero⟩
    let D : XiLocalWeightedDifferenceData rho :=
      xiLocalWeightedDifferenceData rho
    obtain ⟨riso, hriso, hiso⟩ := exists_sourceZero_isolating_ball rho
    have hpunct : (fun z : Complex => xiGlobalWeightedDifference z) =ᶠ[𝓝[≠] s]
        (fun z : Complex => D.extension z) := by
      change ∀ᶠ z in 𝓝[≠] s,
        xiGlobalWeightedDifference z = D.extension z
      rw [eventually_nhdsWithin_iff]
      have hball_rho : ∀ᶠ z in 𝓝 rho.1, z ∈ Metric.ball rho.1 riso :=
        Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hriso)
      have hball : ∀ᶠ z in 𝓝 s, z ∈ Metric.ball rho.1 riso := by
        simpa [rho] using hball_rho
      have hraw := D.punctured_eq
      rw [eventually_nhdsWithin_iff] at hraw
      filter_upwards [hball, hraw] with z hzball hzraw hzne
      have hxi : completedRiemannXi z ≠ 0 := by
        intro hzero
        have hz_eq : z = rho.1 := (hiso z hzball).mp hzero
        exact hzne (by simpa [rho] using hz_eq)
      rw [xiGlobalWeightedDifference_eq_raw hxi]
      exact hzraw hzne
    have hcenter : xiGlobalWeightedDifference s = D.extension s := by
      have hlocal := xiGlobalWeightedDifference_eq_local_extension rho
      simpa [rho, D] using hlocal
    have hfull : (fun z : Complex => xiGlobalWeightedDifference z) =ᶠ[𝓝 s]
        (fun z : Complex => D.extension z) :=
      eventuallyEq_nhds_of_eventuallyEq_nhdsNE hpunct hcenter
    have hD : AnalyticAt Complex D.extension s := by
      have hs_rho : s = rho.1 := by rfl
      rw [hs_rho]
      exact D.extension_analytic rho.1 (Metric.mem_ball_self D.radius_pos)
    exact hD.congr hfull.symm

theorem xiGlobalWeightedDifference_analyticOnNhd :
    AnalyticOnNhd Complex xiGlobalWeightedDifference Set.univ := by
  intro s hs
  exact xiGlobalWeightedDifference_analyticAt s

end
end C1XiGlobalDifference
end Source
end ConnesWeilRH
