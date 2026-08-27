/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20RawKernelMass

/-!
# The CC20 root window `[−log 2 / 2, log 2 / 2]` and its operator bound

This leaf instantiates the explicit certified window-mass flagship of
`C1CC20RawKernelMass` at the paper's OWN working interval
`I = [−(log 2)/2, (log 2)/2]` — the additive-log-coordinate form of the
published support hypothesis `[2^(−1/2), 2^(1/2)]` (arXiv:2006.13771,
Lemma `second` builds `nf_I` on `L²(I)` here).  Since `2 * a = log 2` at
this radius, the closed-form operator mass reads `Bc ^ 2 * (log 2) ^ 2`.

Scope: `L²` boundedness ONLY, behind the standing continuity premise of the
displacement profile.  The paper's concrete prolate data (eigenvalues
`lambda`, modes `xi_n^an`, and the equation-(100) slope identity) and every
spectral/sign estimate remain explicit caller obligations; no RH claim is
made here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20RootWindowOperator

open CC20Concrete
open MeasureTheory
open C1CC20RawKernelMass

/-- Half-width of the published CC20/Yoshida root window, `log 2 / 2`. -/
noncomputable def cc20RootHalfWidth : ℝ := Real.log 2 / 2

theorem cc20RootHalfWidth_pos : 0 < cc20RootHalfWidth :=
  div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)

/-- The root window is the symmetric window at the root half-width. -/
theorem cc20RootWindow_eq_cc20Window :
    Set.Icc (-cc20RootHalfWidth) (cc20RootHalfWidth)
      = cc20Window cc20RootHalfWidth := rfl

/-- At the root radius the doubled half-width is exactly `log 2`. -/
theorem two_mul_cc20RootHalfWidth_sq_eq_logTwo_sq :
    ((2 : ℝ) * cc20RootHalfWidth) ^ 2 = (Real.log 2) ^ 2 := by
  unfold cc20RootHalfWidth
  ring

/-- Square-root-window area collapses to `(log 2)^2`: with `a = log 2 / 2`,
the doubled radius is `2 * a = log 2`. -/
theorem volume_cc20RootSquarePair :
    volume (cc20WindowPair cc20RootHalfWidth)
      = ENNReal.ofReal ((Real.log 2) ^ 2) := by
  rw [volume_cc20WindowPair_of_nonneg cc20RootHalfWidth_pos.le,
    two_mul_cc20RootHalfWidth_sq_eq_logTwo_sq]

/-- Flagship specialization to the paper's window: mere continuity of the
displacement profile yields an explicit operator bound on `L²(I)`,

    ∫⁻ x, ‖A f(x)‖ₑ² ≤ Bc² · (log 2)² · ∫⁻ ‖f‖ₑ²,

with `Bc ≥ 0` packaged by compactness.  This is the boundedness half of the
paper's `kf_I` on `I`; its spectral content is NOT addressed here. -/
theorem applyKernel_l2_sq_le_explicit_rootWindow
    (data : CC20EndpointSpectralData)
    (hcont : Continuous data.endpointWindowKernel)
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal 2)) :
    ∃ Bc : ℝ, 0 ≤ Bc ∧
      (∫⁻ x, ‖C1CC20LpOperator.applyKernel
          (endpointKernelOnSquare data cc20RootHalfWidth) f x‖ₑ ^ (2 : ℝ)) ≤
        ENNReal.ofReal (Bc ^ 2 * ((Real.log 2) ^ 2)) *
          (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ)) := by
  obtain ⟨Bc, hBc0, hB⟩ :=
    applyKernel_l2_sq_le_explicit data cc20RootHalfWidth
      cc20RootHalfWidth_pos.le hcont hf
  refine ⟨Bc, hBc0, ?_⟩
  rw [two_mul_cc20RootHalfWidth_sq_eq_logTwo_sq] at hB
  exact hB

end C1CC20RootWindowOperator
end Source
end ConnesWeilRH
