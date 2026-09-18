/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.SoninWindowWitness
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

/-!
# Window witnesses transport to the one-sided carrier

Record 1623 filed a mismatch between the committed carrier and the CCM Sonin
space: the committed carrier

  `V_arch(lambda) = Radial(lambda) INTER FourierSupport(lambda)`

asks only for *half-line* vanishing (`t < log lambda`), while the paper's
two-sided Sonin space asks for vanishing on the complement of a bounded
window.  This file makes the direction of the mismatch formal:

* every *window* witness — a nonzero `u` vanishing outside `(-T, T)`, with its
  Hardy--Titchmarsh transform `H u` vanishing outside the same window — is a
  carrier witness at *every* scale `lambda <= exp (-T)`
  (`carrier_nontrivial_of_window_witness`);

so the one-sided obligation is *weaker* than any bounded-window existence
result, and a solution of the two-sided problem transports into the tree
without further analysis.  Composed with the scale monotonicity of record 1626
(`archimedeanSoninCarrier_nontrivial_of_le`) the transport spreads the witness
downward in `lambda`.

The transport is purely a support statement: the proof uses only the lower
edge of the window, because the carrier discards the upper edge.  It is
therefore *not* a step toward solving the carrier base — no window witness is
constructed here, `archimedeanSoninCarrier_nontrivial` stays the open analytic
obligation (law F33), and RH is not claimed.
-/

namespace ConnesWeilRH
namespace Dev
namespace SoninWindowTransport

open MeasureTheory
open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Dev.SoninWindowWitness
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse

/-- A window witness of half-width `T`: a nonzero vector that vanishes outside
the bounded window `(-T, T)`, together with its Hardy--Titchmarsh transform.
This is the two-sided shape of the CCM Sonin problem, before the tree's
one-sided relaxation. -/
def IsWindowWitness (T : ℝ) (u : cc20GlobalLogCrossingL2) : Prop :=
  u ≠ 0 ∧
    (∀ᵐ t ∂volume, t ∉ Set.Ioo (-T) T → u t = 0) ∧
    (∀ᵐ t ∂volume, t ∉ Set.Ioo (-T) T →
      (ccm24ArchimedeanHardyTitchmarsh u) t = 0)

/-- Below the window's lower edge, a window witness is radially supported at
every scale with `log lambda <= -T`. -/
theorem mem_radialSupport_of_window {T : ℝ} {lambda : CCM24SoninScale}
    (hle : Real.log lambda.1 ≤ -T) {u : cc20GlobalLogCrossingL2}
    (hu : ∀ᵐ t ∂volume, t ∉ Set.Ioo (-T) T → u t = 0) :
    u ∈ ccm24LogRadialSupportClosedSubspace lambda := by
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff]
  filter_upwards [hu] with t ht hlt
  exact ht (fun hmem => by linarith [hmem.1, hlt, hle])

/-- Below the window's lower edge, the Hardy--Titchmarsh transform of a window
witness is radially supported at every scale with `log lambda <= -T`. -/
theorem mem_fourierSupport_of_window {T : ℝ} {lambda : CCM24SoninScale}
    (hle : Real.log lambda.1 ≤ -T) {u : cc20GlobalLogCrossingL2}
    (hu : ∀ᵐ t ∂volume, t ∉ Set.Ioo (-T) T →
      (ccm24ArchimedeanHardyTitchmarsh u) t = 0) :
    u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda := by
  rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff]
  exact mem_radialSupport_of_window hle hu

/-- Transport: a window witness of any half-width `T > 0` is a witness of the
one-sided carrier at every scale `lambda <= exp (-T)`. -/
theorem carrier_nontrivial_of_window_witness {T : ℝ} {lambda : CCM24SoninScale}
    (hle : Real.log lambda.1 ≤ -T) {u : cc20GlobalLogCrossingL2}
    (h : IsWindowWitness T u) :
    archimedeanSoninCarrier_nontrivial lambda := by
  obtain ⟨hne, hu, hHu⟩ := h
  refine ⟨⟨u, Submodule.mem_inf.mpr
    ⟨mem_radialSupport_of_window hle hu,
      mem_fourierSupport_of_window hle hHu⟩⟩, ?_⟩
  exact fun hzero => hne (congrArg Subtype.val hzero)

end SoninWindowTransport
end Dev
end ConnesWeilRH
