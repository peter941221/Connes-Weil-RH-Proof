/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20FiniteRankApproximation
import ConnesWeilRH.Dev.C1CC20KernelLpLift

/-!
# The CC20 finite-rank profile as a bounded operator

Equation (119) defines a finite-rank operator through Fourier projections,
whereas equation (120) uses one displacement profile.  This leaf proves that
these are the same bounded `L²` operator on the ROOT window.  Consequently a
future certified `L¹` bound for the difference of the endpoint profile and
the finite-rank profile has one unambiguous operator consumer.

Reference: equations (118)--(121) of
<https://arxiv.org/html/2006.13771>.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20FiniteRankOperatorReadback

open MeasureTheory
open C1CC20DisplacementKernel C1CC20FiniteRankApproximation C1CC20KernelLpLift
  C1CC20RawKernelMass C1CC20RootWindowOperator

/-- The two-variable kernel of one finite-rank summand in equation (119). -/
noncomputable def cc20FiniteRankTermKernel {ι : Type*}
    (data : CC20FiniteRankData ι) (i : ι) : ℝ × ℝ → ℂ :=
  cc20FourierProjectionKernel (data.frequency i) +
    (-((data.coefficient i : ℝ) : ℂ)) •
      cc20FourierProjectionKernel (data.perturbedFrequency i)

theorem memLp_cc20FiniteRankTermKernel {ι : Type*}
    (data : CC20FiniteRankData ι) (i : ι) :
    MemLp (cc20FiniteRankTermKernel data i) 2 volume := by
  unfold cc20FiniteRankTermKernel
  exact (memLp_cc20FourierProjectionKernel (data.frequency i)).add
    ((memLp_cc20FourierProjectionKernel (data.perturbedFrequency i)).const_smul
      (-((data.coefficient i : ℝ) : ℂ)))

/-- The raw kernel of one finite-rank summand is the windowed displacement
kernel of its equation-(120) profile term. -/
theorem cc20FiniteRankTermKernel_eq_windowedDisplacementKernel
    {ι : Type*} (data : CC20FiniteRankData ι) (i : ι) :
    cc20FiniteRankTermKernel data i =
      windowedDisplacementKernel (cc20FiniteRankProfileTerm data i)
        cc20RootHalfWidth := by
  funext p
  rw [cc20FiniteRankTermKernel,
    cc20FourierProjectionKernel_eq_windowedDisplacementKernel,
    cc20FourierProjectionKernel_eq_windowedDisplacementKernel]
  by_cases hp : p ∈ cc20WindowPair cc20RootHalfWidth
  · simp [windowedDisplacementKernel, displacementKernel,
      cc20FiniteRankProfileTerm, hp, sub_eq_add_neg]
  · simp [windowedDisplacementKernel,
      cc20FiniteRankProfileTerm, hp]

/-- The lifted kernel of one finite-rank profile term is its equation-(119)
bounded-operator summand. -/
theorem applyKernelLp_cc20FiniteRankTermKernel_eq_operatorTerm
    {ι : Type*} (data : CC20FiniteRankData ι) (i : ι) :
    applyKernelLp (cc20FiniteRankTermKernel data i)
      (memLp_cc20FiniteRankTermKernel data i) =
        cc20FiniteRankOperatorTerm data i := by
  let k := cc20FourierProjectionKernel (data.frequency i)
  let l := cc20FourierProjectionKernel (data.perturbedFrequency i)
  let c : ℂ := ((data.coefficient i : ℝ) : ℂ)
  have hk : MemLp k 2 volume :=
    memLp_cc20FourierProjectionKernel (data.frequency i)
  have hl : MemLp l 2 volume :=
    memLp_cc20FourierProjectionKernel (data.perturbedFrequency i)
  calc
    applyKernelLp (cc20FiniteRankTermKernel data i)
        (memLp_cc20FiniteRankTermKernel data i) =
      applyKernelLp k hk + applyKernelLp ((-c) • l) (hl.const_smul (-c)) := by
        simpa only [cc20FiniteRankTermKernel, k, l, c] using
          (applyKernelLp_kernel_add hk (hl.const_smul (-c)))
    _ = applyKernelLp k hk + (-c) • applyKernelLp l hl := by
      rw [applyKernelLp_kernel_smul]
    _ = cc20FiniteRankOperatorTerm data i := by
      rw [applyKernelLp_cc20FourierProjectionKernel_eq_projection,
        applyKernelLp_cc20FourierProjectionKernel_eq_projection]
      dsimp [c]
      change cc20FourierProjection (data.frequency i) +
          (-((data.coefficient i : ℝ) : ℂ)) •
            cc20FourierProjection (data.perturbedFrequency i) =
        cc20FourierProjection (data.frequency i) -
          ((data.coefficient i : ℝ) : ℂ) •
            cc20FourierProjection (data.perturbedFrequency i)
      rw [neg_smul]
      rw [sub_eq_add_neg]

/-- The kernel obtained by summing every equation-(119) term. -/
noncomputable def cc20FiniteRankKernel {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι) : ℝ × ℝ → ℂ :=
  ((data.lambda : ℝ) : ℂ) •
    ∑ i, cc20FiniteRankTermKernel data i

theorem memLp_cc20FiniteRankKernel {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι) :
    MemLp (cc20FiniteRankKernel data) 2 volume := by
  unfold cc20FiniteRankKernel
  apply MemLp.const_smul
  exact memLp_finsetSum' Finset.univ fun i _ =>
    memLp_cc20FiniteRankTermKernel data i

/-- The full finite-rank kernel is the ROOT-window displacement kernel of the
equation-(120) profile. -/
theorem cc20FiniteRankKernel_eq_windowedDisplacementKernel
    {ι : Type*} [Fintype ι] (data : CC20FiniteRankData ι) :
    cc20FiniteRankKernel data =
      windowedDisplacementKernel (cc20FiniteRankProfile data)
        cc20RootHalfWidth := by
  classical
  have hterms :
      (∑ i, cc20FiniteRankTermKernel data i) =
        ∑ i, windowedDisplacementKernel
          (cc20FiniteRankProfileTerm data i) cc20RootHalfWidth := by
    apply Finset.sum_congr rfl
    intro i _
    exact cc20FiniteRankTermKernel_eq_windowedDisplacementKernel data i
  rw [cc20FiniteRankKernel, cc20FiniteRankProfile, hterms]
  funext p
  by_cases hp : p ∈ cc20WindowPair cc20RootHalfWidth <;>
    simp [windowedDisplacementKernel, displacementKernel, hp]

/-- Equation (119) and equation (120) define one and the same bounded ROOT
window operator. -/
theorem applyKernelLp_cc20FiniteRankKernel_eq_operator
    {ι : Type*} [Fintype ι] (data : CC20FiniteRankData ι) :
    applyKernelLp (cc20FiniteRankKernel data)
      (memLp_cc20FiniteRankKernel data) =
        cc20FiniteRankOperator data := by
  classical
  let hterms : ∀ i, MemLp (cc20FiniteRankTermKernel data i) 2 volume :=
    fun i => memLp_cc20FiniteRankTermKernel data i
  calc
    applyKernelLp (cc20FiniteRankKernel data)
        (memLp_cc20FiniteRankKernel data) =
      ((data.lambda : ℝ) : ℂ) •
        applyKernelLp (∑ i, cc20FiniteRankTermKernel data i)
          (memLp_finsetSum' Finset.univ fun i _ => hterms i) := by
        simpa only [cc20FiniteRankKernel, hterms] using
          (applyKernelLp_kernel_smul
            (memLp_finsetSum' Finset.univ fun i _ => hterms i)
            ((data.lambda : ℝ) : ℂ))
    _ = ((data.lambda : ℝ) : ℂ) •
        ∑ i, applyKernelLp (cc20FiniteRankTermKernel data i) (hterms i) := by
      rw [← applyKernelLp_kernel_finsetSum]
    _ = cc20FiniteRankOperator data := by
      simp only [applyKernelLp_cc20FiniteRankTermKernel_eq_operatorTerm,
        cc20FiniteRankOperator]

end C1CC20FiniteRankOperatorReadback
end Source
end ConnesWeilRH
