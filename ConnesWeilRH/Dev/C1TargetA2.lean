/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1A2WindowSplit

/-!
# C1TargetA2 - the TARGET-A2 counting frame (record 1365 s2; L2c definitions-side)

Build preregistration: docs/proofs/1365_targetA2_counting_frame_design.md
(all statements LOCKED there before any build log - law-42 discipline;
the `A` binder is uninterpreted BY ADJUDICATION s1: its energy
realization is the registered L2a/L2c science, and the gap shadow was
rejected there with reasons).

This leaf carries NO analysis. It gives the enemy (1360 s4 TARGET-A2)
a Lean name, proves the definitional monotonicities of the window
counts, machine-verifies that under SourceRH every near-line off-line
window count is ZERO, and reduces the residual content of the A2-shape
under RH to the strict positivity margin A > 0 at non-void windows.
That margin is exactly the 1353 s5 SPREAD limb, so this is a map
result, not a shortcut. The F7 void-window guard `1 <= windowTotalCount`
is applied pre-digit per 1365 s3.

RH is not claimed anywhere; the stop word is the gate certificate
(charter 1358 s4).
-/

namespace ConnesWeilRH
namespace Source
namespace C1TargetA2

open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralOnlineSplit
open C1A2WindowSplit

noncomputable section

/-! ### Counts (1365 s2, ENNReal via Set.encard - no per-window finiteness needed) -/

/-- Total source zeros in one ordinate window. -/
noncomputable def windowTotalCount (W : Real) (k : Int) : ENNReal :=
  Set.encard (windowSet W k)

/-- On-line source zeros in one ordinate window. -/
noncomputable def windowOnLineCount (W : Real) (k : Int) : ENNReal :=
  Set.encard (windowSet W k ∩ onLineZeroSet)

/-- Off-line zeros within eps of the critical line in one ordinate window:
the left-hand side of the TARGET-A2 inequality. -/
noncomputable def windowNearLineOffCount (W eps : Real) (k : Int) : ENNReal :=
  Set.encard (windowSet W k ∩ offLineZeroSet ∩
    {rho : sourceNontrivialZeroSet | |rho.1.re - 1 / 2| < eps})

/-- The window's height threshold: its lower ordinate edge. -/
def windowHeight (W : Real) (k : Int) : Real :=
  (k : Real) * W

/-! ### The contest threshold function f*(A) = A / (A + 2) -/

/-- The TARGET-A2 threshold function (1360 s4): admissible near-line
off-line density as a function of the on-line spread ratio. -/
def fstar (A : Real) : Real :=
  A / (A + 2)

theorem fstar_nonneg {A : Real} (hA : 0 ≤ A) : 0 ≤ fstar A := by
  unfold fstar
  exact div_nonneg hA (by linarith)

theorem fstar_zero : fstar 0 = 0 := by
  norm_num [fstar]

theorem fstar_lt_one {A : Real} (hA : 0 ≤ A) : fstar A < 1 := by
  unfold fstar
  exact (div_lt_one (by linarith)).mpr (by linarith)

theorem fstar_mono {A B : Real} (hA : 0 ≤ A) (hAB : A ≤ B) :
    fstar A ≤ fstar B := by
  unfold fstar
  have h1 : (0 : Real) < A + 2 := by linarith
  have h2 : (0 : Real) < B + 2 := by linarith
  have hcr : A * (B + 2) ≤ B * (A + 2) := by nlinarith
  calc A / (A + 2) = (A * (B + 2)) / ((A + 2) * (B + 2)) := by field_simp
    _ ≤ (B * (A + 2)) / ((A + 2) * (B + 2)) := by gcongr
    _ = B / (B + 2) := by field_simp

/-! ### Definitional monotonicities -/

theorem windowOnLineCount_le_total (W : Real) (k : Int) :
    windowOnLineCount W k ≤ windowTotalCount W k := by
  unfold windowOnLineCount windowTotalCount
  exact_mod_cast Set.encard_le_encard (Set.inter_subset_left)

theorem windowNearLineOffCount_le_total (W eps : Real) (k : Int) :
    windowNearLineOffCount W eps k ≤ windowTotalCount W k := by
  unfold windowNearLineOffCount windowTotalCount
  exact_mod_cast Set.encard_le_encard
    (Set.inter_subset_left.trans Set.inter_subset_left)

theorem nearLineOffCount_eps_mono (W : Real) {eps1 eps2 : Real}
    (h : eps1 ≤ eps2) (k : Int) :
    windowNearLineOffCount W eps1 k ≤ windowNearLineOffCount W eps2 k := by
  unfold windowNearLineOffCount
  have hsub :
      (windowSet W k ∩ offLineZeroSet ∩
          {rho : sourceNontrivialZeroSet | |rho.1.re - 1 / 2| < eps1}) ⊆
      (windowSet W k ∩ offLineZeroSet ∩
          {rho : sourceNontrivialZeroSet | |rho.1.re - 1 / 2| < eps2}) := by
    intro rho hrho
    obtain ⟨h12, hnear⟩ := hrho
    obtain ⟨hwin, hoff⟩ := h12
    exact ⟨⟨hwin, hoff⟩, lt_of_lt_of_le hnear h⟩
  exact_mod_cast Set.encard_le_encard hsub

/-! ### The enemy, named (1365 s2) -/

/-- TARGET-A2 in counting-frame form: above height T1, every NON-VOID
window carries strictly fewer near-line off-line zeros than f*(A)
times its total count. `A` is the (here uninterpreted, by 1365 s1)
spread-ratio functional of the window. -/
def targetA2Schema (W : Real) (T1 eps : Real) (A : Int → Real) : Prop :=
  ∀ k : Int, windowHeight W k ≥ T1 →
    (1 : ENNReal) ≤ windowTotalCount W k →
    windowNearLineOffCount W eps k <
      ENNReal.ofReal (fstar (A k)) * windowTotalCount W k

/-! ### The two machine-checked facts about the schema -/

/-- Under SourceRH every near-line off-line window count is ZERO: the
left-hand side of the enemy vanishes. -/
theorem sourceRH_windowNearLineOffCount_zero
    (hRH : RHDefinitionBridge.standard.SourceRH) (W eps : Real) (k : Int) :
    windowNearLineOffCount W eps k = 0 := by
  unfold windowNearLineOffCount
  have hempty :
      (windowSet W k ∩ offLineZeroSet ∩
          {rho : sourceNontrivialZeroSet | |rho.1.re - 1 / 2| < eps}) = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp fun ⟨rho, hrho⟩ => by
      obtain ⟨⟨_hwin, hoff⟩, _hnear⟩ := hrho
      have hline : rho.1.re = 1 / 2 :=
        RHDefinitionBridge.standard.sourceCriticalLine_to_mathlib rho.1
          (hRH rho.1 rho.2)
      exact hoff (by simpa [onLineZeroSet] using hline)
  exact_mod_cast Set.encard_eq_zero.mpr hempty

/-- The residual content: under SourceRH, targetA2Schema follows from
the strict positivity margin 0 < fstar (A k) at non-void windows
above T1 - the 1353 s5 SPREAD limb, named. No analysis is used;
this is the reduction itself. -/
theorem sourceRH_targetA2_margin_reduction
    (hRH : RHDefinitionBridge.standard.SourceRH) (W T1 eps : Real)
    (A : Int → Real)
    (hmargin : ∀ k : Int, windowHeight W k ≥ T1 →
      (1 : ENNReal) ≤ windowTotalCount W k → 0 < fstar (A k)) :
    targetA2Schema W T1 eps A := by
  intro k hT1 hN
  rw [sourceRH_windowNearLineOffCount_zero hRH W eps k]
  have hpos : 0 < ENNReal.ofReal (fstar (A k)) :=
    ENNReal.ofReal_pos.mpr (hmargin k hT1 hN)
  refine lt_of_lt_of_le hpos ?_
  have hN' : (1 : ENNReal) ≤ windowTotalCount W k := hN
  calc ENNReal.ofReal (fstar (A k)) =
        ENNReal.ofReal (fstar (A k)) * 1 := (mul_one _).symm
    _ ≤ ENNReal.ofReal (fstar (A k)) * windowTotalCount W k :=
        mul_le_mul_of_nonneg_left hN' (le_of_lt hpos)

end
end C1TargetA2
end Source
end ConnesWeilRH
