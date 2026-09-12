/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1TargetA2
import ConnesWeilRH.Dev.C1WeilCriterionEquivalence
import ConnesWeilRH.Dev.C1SpectralOnlineNonneg

/-!
# C1H2Corridor - the H2 corridor formalized (record 1367 s2; the wall's signature)

Build preregistration: docs/proofs/1367_h2_corridor_formalization_design.md
(all statements LOCKED there before any build log - law-42 discipline).

What this leaf is: the machine-checked map "per-window balance is the
ONE missing bridge" between the 1366 counting frame (TARGET-A2) and
the d767a1d gate. Every link of the 1350 s3 skeleton that is formal is
proved formal here; the unformal content survives exactly as the type
of the single explicit hypothesis `hBridge` (and no bridge is claimed
to exist - per record 1353 the PURE-COUNTING form `sourceRH_of_countBridge`
is not derivable; the live form is the spread-carrying
`sourceRH_of_A2Bridge`).

The positive control `sourceRH_windowMassBalance` shows the balance
Prop is true at the RH endpoint, so the bridge hypothesis is not
inconsistent with its conclusion.

RH is not claimed anywhere; the stop word is the gate certificate
(charter 1358 s4).
-/

namespace ConnesWeilRH
namespace Source
namespace C1H2Corridor

open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1SpectralWeil
open C1SpectralOnlineSplit
open C1SpectralOnlineNonneg
open C1A2WindowSplit
open C1TargetA2
open C1HealthyYoshidaSpectralNegativity

noncomputable section

/-! ### The two named Props (1367 s2, locked) -/

/-- Per-window balance: every ordinate window's on-line mass plus
off-line residual is nonnegative. This is the target-side content of
leg L3 (1350 s3): the window-wise nonnegativity that, summed, IS the
gate. -/
def windowMassBalance (g : CompactLogTest) (W : Real) : Prop :=
  ∀ k : Int, 0 ≤ windowOnLineMass g W k + windowOffLineMass g W k

/-- The H1/H2 counting hypothesis (1350 s2-s3) in the 1366 vocabulary:
no non-void window above `T1` carries a near-line off-line majority,
measured against the threshold `f*(1) = 1/3`. By definition this is
`targetA2Schema` at the constant spread level `A = 1`. -/
def noNearLineMajority (W eps T1 : Real) : Prop :=
  targetA2Schema W T1 eps (fun _ => 1)

theorem fstar_one : fstar 1 = 1 / 3 := by
  norm_num [fstar]

/-! ### Monotonicities of the counting hypothesis (locked) -/

theorem noMajority_eps_mono (W : Real) {eps1 eps2 : Real}
    (h : eps1 ≤ eps2) (T1 : Real)
    (hc : noNearLineMajority W eps2 T1) :
    noNearLineMajority W eps1 T1 := by
  intro k hT1 hN
  exact lt_of_le_of_lt (nearLineOffCount_eps_mono W h k) (hc k hT1 hN)

theorem noMajority_height_mono {Ta Tb : Real} (h : Ta ≤ Tb) (W eps : Real)
    (hc : noNearLineMajority W eps Ta) :
    noNearLineMajority W eps Tb :=
  fun k hTb => hc k (le_trans h hTb)

/-! ### The corridor: balance -> gate -> SourceRH (locked; pure
    composition over committed bricks, zero analysis) -/

theorem qw_nonneg_of_windowMassBalance (g : CompactLogTest) (W : Real)
    (h : windowMassBalance g W) : 0 ≤ C1SameOwnerWeil.qw g := by
  rw [qw_window_assembly g W]
  exact tsum_nonneg h

/-- THE machine-checked map statement: any bridge from the counting
hypotheses to `windowMassBalance`, uniform on the triple-vanishing
class, discharges the gate and hence SourceRH (d767a1d `.mp`). The C6
charter's formal target is exactly the type of `hBridge`. -/
theorem sourceRH_of_windowMassBalanceBridge (W : Real)
    (hBridge : ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g →
        windowMassBalance g W) :
    RHDefinitionBridge.standard.SourceRH :=
  C1WeilCriterionEquivalence.weilCriterion_iff_sourceRH.mp fun g hg =>
    qw_nonneg_of_windowMassBalance g W (hBridge g hg)

/-- The pure-counting instance (H2 as drafted in 1350 s3).
RAIL (1353): no such bridge is derivable from counts alone - clustered
on-line configurations defeat count assembly by 70-146x. Registered as
the dead-end form of the corridor, kept to make the rail checkable. -/
theorem sourceRH_of_countBridge (W eps T1 : Real)
    (hBridge : ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g →
        noNearLineMajority W eps T1 → windowMassBalance g W)
    (hCount : noNearLineMajority W eps T1) :
    RHDefinitionBridge.standard.SourceRH :=
  sourceRH_of_windowMassBalanceBridge W fun g hg => hBridge g hg hCount

/-- The TARGET-A2 instance (1360 s5 "A2 discharges via B4+B2/B3", now
with B2/B3 isolated inside `hBridge`): the spread-carrying form - the
live lane. `A` uninterpreted per 1365 s1. -/
theorem sourceRH_of_A2Bridge (W eps T1 : Real) (A : Int → Real)
    (hBridge : ∀ g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g →
        targetA2Schema W T1 eps A → windowMassBalance g W)
    (hA2 : targetA2Schema W T1 eps A) :
    RHDefinitionBridge.standard.SourceRH :=
  sourceRH_of_windowMassBalanceBridge W fun g hg => hBridge g hg hA2

/-! ### Positive control (locked): the balance Prop is true at the RH
    endpoint, so the bridge's conclusion is satisfiable - no bridge
    statement here is vacuously aiming at False. -/

theorem sourceRH_windowMassBalance
    (hRH : RHDefinitionBridge.standard.SourceRH)
    (g : CompactLogTest) (W : Real) : windowMassBalance g W := by
  intro k
  have hline : ∀ rho : sourceNontrivialZeroSet, rho.1.re = 1 / 2 := fun rho =>
    RHDefinitionBridge.standard.sourceCriticalLine_to_mathlib rho.1
      (hRH rho.1 rho.2)
  have h_off : windowOffLineMass g W k = 0 := by
    unfold windowOffLineMass
    have hterm : ∀ rho : {r : sourceNontrivialZeroSet // r ∈ windowSet W k},
        (offLineSpectralTerm g rho).re = 0 := fun rho => by
      have hn : (rho : sourceNontrivialZeroSet) ∉ offLineZeroSet := by
        intro hmem
        simp only [offLineZeroSet, Set.mem_compl_iff, onLineZeroSet,
          Set.mem_setOf_eq] at hmem
        exact hmem (hline rho)
      show ((offLineZeroSet.indicator (spectralTerm g.convolutionSquare)) rho).re = 0
      classical
      rw [Set.indicator_apply, if_neg hn, Complex.zero_re]
    rw [tsum_congr hterm, tsum_zero]
  have h_on : 0 ≤ windowOnLineMass g W k := by
    unfold windowOnLineMass
    refine tsum_nonneg (fun rho : {r : sourceNontrivialZeroSet // r ∈ windowSet W k} => ?_)
    have hmem : (rho : sourceNontrivialZeroSet) ∈ onLineZeroSet := by
      rw [onLineZeroSet]; exact hline rho
    show 0 ≤ (onLineZeroSet.indicator (spectralTerm g.convolutionSquare) rho).re
    rw [Set.indicator_of_mem hmem]
    exact spectralTerm_convolutionSquare_nonneg_of_onLine g rho (hline rho)
  rw [h_off, add_zero]
  exact h_on

end
end C1H2Corridor
end Source
end ConnesWeilRH
