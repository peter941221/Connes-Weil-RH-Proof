/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20FiniteRankOperatorReadback

/-!
# The CC20 finite-rank profile difference

This leaf identifies the numerical object in CC20 equation (115) with the
operator gap in equation (121).  The profile is the concrete difference
between the endpoint displacement profile and the finite Fourier profile;
its ROOT-window kernel lifts exactly to `K_I - T`.

No numerical enclosure is asserted here.  A later certificate must prove the
`L¹` mass of this named profile difference.

Reference: equations (115), (119)--(121) of
<https://arxiv.org/html/2006.13771>.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20FiniteRankDifference

open MeasureTheory
open CC20Concrete
open C1CC20DisplacementKernel C1CC20FiniteRankApproximation
  C1CC20FiniteRankOperatorReadback C1CC20KernelLpLift
  C1CC20RawKernelMass C1CC20RootWindowOperator

/-- The profile whose `L¹` mass is the exact input consumed by paper
equation (121): the endpoint profile `χ` minus the finite profile `τ`. -/
noncomputable def cc20FiniteRankDifferenceProfile {ι : Type*} [Fintype ι]
    (endpointData : CC20EndpointSpectralData) (finiteData : CC20FiniteRankData ι) :
    ℝ → ℂ :=
  endpointDisplacementProfile endpointData - cc20FiniteRankProfile finiteData

/-- The ROOT-window kernel of the profile difference. -/
noncomputable def cc20FiniteRankDifferenceKernel {ι : Type*} [Fintype ι]
    (endpointData : CC20EndpointSpectralData) (finiteData : CC20FiniteRankData ι) :
    ℝ × ℝ → ℂ :=
  endpointKernelOnSquare endpointData cc20RootHalfWidth -
    cc20FiniteRankKernel finiteData

/-- The concrete kernel difference is the windowed displacement kernel of
the named profile difference. -/
theorem cc20FiniteRankDifferenceKernel_eq_windowedDisplacementKernel
    {ι : Type*} [Fintype ι]
    (endpointData : CC20EndpointSpectralData) (finiteData : CC20FiniteRankData ι) :
    cc20FiniteRankDifferenceKernel endpointData finiteData =
      windowedDisplacementKernel
        (cc20FiniteRankDifferenceProfile endpointData finiteData)
        cc20RootHalfWidth := by
  rw [cc20FiniteRankDifferenceKernel,
    endpointKernelOnSquare_eq_windowedDisplacementKernel,
    cc20FiniteRankKernel_eq_windowedDisplacementKernel]
  funext p
  by_cases hp : p ∈ cc20WindowPair cc20RootHalfWidth
  · simp [windowedDisplacementKernel, displacementKernel,
      cc20FiniteRankDifferenceProfile, hp, sub_eq_add_neg]
  · simp [windowedDisplacementKernel,
      cc20FiniteRankDifferenceProfile, hp]

/-- An `L²` endpoint-kernel owner automatically supplies the same owner for
the finite-rank difference kernel. -/
theorem memLp_cc20FiniteRankDifferenceKernel
    {ι : Type*} [Fintype ι]
    (endpointData : CC20EndpointSpectralData) (finiteData : CC20FiniteRankData ι)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume) :
    MemLp (cc20FiniteRankDifferenceKernel endpointData finiteData) 2 volume := by
  unfold cc20FiniteRankDifferenceKernel
  exact hendpoint.sub (memLp_cc20FiniteRankKernel finiteData)

/-- The bounded operator induced by the profile-difference kernel is exactly
the operator gap `K_I - T`. -/
theorem applyKernelLp_cc20FiniteRankDifferenceKernel_eq_operatorGap
    {ι : Type*} [Fintype ι]
    (endpointData : CC20EndpointSpectralData) (finiteData : CC20FiniteRankData ι)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume) :
    applyKernelLp (cc20FiniteRankDifferenceKernel endpointData finiteData)
      (memLp_cc20FiniteRankDifferenceKernel endpointData finiteData hendpoint) =
        applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
          hendpoint - cc20FiniteRankOperator finiteData := by
  unfold cc20FiniteRankDifferenceKernel
  rw [applyKernelLp_kernel_sub hendpoint (memLp_cc20FiniteRankKernel finiteData),
    applyKernelLp_cc20FiniteRankKernel_eq_operator]

end C1CC20FiniteRankDifference
end Source
end ConnesWeilRH
