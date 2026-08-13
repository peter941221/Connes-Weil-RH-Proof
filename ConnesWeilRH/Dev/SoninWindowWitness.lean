import ConnesWeilRH.Dev.OuterTwoNonzeroObligation
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh
import ConnesWeilRH.Source.CC20Concrete.CCM24PaleyWienerSpectral
import ConnesWeilRH.Source.CC20Concrete.CCM24LogRadialSupport
import ConnesWeilRH.Source.CC20Concrete.CCM24FiniteEulerSoninTransport

/-!
# Sonin window witness module (Dev)

Route: docs/proofs/999 and docs/proofs/998.  This module pins, by name and by
exact type, the analytic witness target used by the conditional coframe
calculation in docs/998. `Dev/OuterTwoNonzeroObligation.lean` defines the target
Prop; it does not prove the coframe strip identity or the target itself.

The documentation (docs/999) records that producing a nonzero element of the
archimedean Sonin carrier `sourceSoninCarrier lambda` with nonzero mass on the
window `(log lambda, log lambda + log 2)` is genuinely new analysis (the
Paley--Wiener / Titchmarsh detection theorem for the archimedean Sonin space),
not present in this repository nor in mathlib v4.30.0.

Each open goal below is stated with its exact type as a `noncomputable def ... :
Prop`. A `Prop` definition fixes a type but proves nothing. The actual theorems
needed are: a Sonin window witness, the `{2}` strip identity in `Lp`, and the
bridge from nonzero restriction to `twoOuterNonzeroObligation`.
-/

namespace ConnesWeilRH
namespace Dev
namespace SoninWindowWitness

open MeasureTheory
open scoped InnerProduct

open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalLeakage
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCoframeResponse
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Dev.OuterTwoNonzero

/-- Goal 1 (docs/999 §3.1): the archimedean Sonin carrier is nontrivial.
This is the load-bearing analytic existence: every later step reduces to it. -/
noncomputable def archimedeanSoninCarrier_nontrivial
    (lambda : CCM24SoninScale) : Prop :=
  ∃ u : sourceSoninCarrier lambda, u ≠ 0

/-- Goal 1 (docs/999 §3.2): membership in `V_arch` is definitionally the pair
of radial-support and Fourier-support conditions.  This is definitional; the
difficulty lives in manufacturing an element, not in the membership type. -/
noncomputable def archimedeanSonin_membership_pred
    (lambda : CCM24SoninScale) (u : cc20GlobalLogCrossingL2) : Prop :=
  u ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
  u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda

/-- Goal 3: the open Sonin window `(log lambda, log lambda + log 2)` for the
radial band mapping `t ↦ t + log 2` (docs/998 §1). -/
noncomputable def windowT (lambda : CCM24SoninScale) : Set ℝ :=
  Set.Ioo (Real.log lambda) (Real.log lambda + Real.log 2)

/-- The open Sonin window is nonempty at every scale (it has positive length). -/
theorem windowT_nonempty (lambda : CCM24SoninScale) :
    (windowT lambda).Nonempty := by
  unfold windowT
  have hlog2 : (0 : ℝ) < Real.log 2 := by
    exact Real.log_pos (by norm_num)
  exact Set.nonempty_Ioo.mpr (by linarith)

/-!
Goal 3 (docs/999 §3.3): nonzero `L2` mass on the window.

This is the statement that a nontrivial element of the archimedean Sonin
carrier has nonzero restriction to the window.  The restriction map is used
instead of point evaluation because `Lp` elements are equal only almost
everywhere.  It is the immediate analytic input for the outer-coframe bridge
in the family `{2}`.
-/
noncomputable def soninWindowRestriction (lambda : CCM24SoninScale) :
    cc20GlobalLogCrossingL2 →L[ℂ] Lp ℂ 2 (volume.restrict (windowT lambda)) :=
  LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (windowT lambda)

noncomputable def archimedeanSonin_window_mass
    (lambda : CCM24SoninScale) : Prop :=
  ∃ u : sourceSoninCarrier lambda,
    u ≠ 0 ∧ soninWindowRestriction lambda (u : cc20GlobalLogCrossingL2) ≠ 0

/-!
Fourier-side PSP core: a nonzero kernel vector for the scattering Toeplitz
operator.  The multiplier is the repository phase
`Gamma_R(1/2 - I * 2*pi*xi) / Gamma_R(1/2 + I * 2*pi*xi)`.  This declaration
records the valid `L2`/Hardy target; it does not assert that the kernel is
nontrivial or that the Fourier transport to `sourceSoninCarrier` is complete.
-/
noncomputable def archimedeanScatteringToeplitzKernel_nontrivial : Prop :=
  ∃ psi : ccm24HardyPositiveSubspace,
    psi ≠ 0 ∧
      ccm24PositiveFrequencyProjection
        (ccm24ArchimedeanScatteringMultiplier (psi : cc20GlobalLogCrossingL2)) = 0

/-- A scattering Toeplitz-kernel vector has a negative-Hardy image. -/
theorem scattering_toeplitz_kernel_image_mem_negative
    (psi : ccm24HardyPositiveSubspace)
    (hpsi : ccm24PositiveFrequencyProjection
      (ccm24ArchimedeanScatteringMultiplier (psi : cc20GlobalLogCrossingL2)) = 0) :
    ccm24ArchimedeanScatteringMultiplier (psi : cc20GlobalLogCrossingL2) ∈
      ccm24HardyNegativeSubspace := by
  rw [mem_ccm24HardyNegativeSubspace_iff]
  exact hpsi

/-!
### Reduction: a radial +-1-eigenvector of HTm already lies in V_arch.

V_arch = Radial(lambda) INTER Fourier(lambda), with
Fourier(lambda) = HT^[-1](Radial(lambda)).  A (nonzero) vector that lies in
the radial subspace and is fixed (or antifixed) by the involutive
Hardy--Titchmarsh isometry HTm forces HTm u = u (resp. -u) back into the
radial subspace, making the Fourier-support half automatic.

Hence producing a nonzero radial eigenvector of HTm is sufficient for
archimedeanSoninCarrier_nontrivial.  This reduction lemma is the exact
meeting point of the Fourier-support half; the remaining work is to exhibit the
concrete radial eigenvector.
-/
theorem archimedeanSonin_membership_pred_of_radial_and_involutive
    (lambda : CCM24SoninScale) {u : cc20GlobalLogCrossingL2}
    (huRadial : u ∈ ccm24LogRadialSupportClosedSubspace lambda)
    (hinv : ccm24ArchimedeanHardyTitchmarsh u = u ∨
            ccm24ArchimedeanHardyTitchmarsh u = -u) :
    archimedeanSonin_membership_pred lambda u := by
  constructor
  · exact huRadial
  · rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff]
    rcases hinv with hself | hanti
    · rw [hself]
      exact huRadial
    · rw [hanti]
      exact Submodule.neg_mem
        (ccm24LogRadialSupportClosedSubspace lambda).toSubmodule huRadial

/-!
### The {2}-family outer gate (exact typed condition).

Conditionally on the unformalized strip identity in docs/998, a window witness
suggests the chain `w = finiteEulerGram u0`, followed by a nonzero image under
`sourceOuterCoframeLeakage`. This typed Prop records the intended intermediate
operator witness. It is not derived from `archimedeanSonin_window_mass` here.
-/
noncomputable def twoOuterNonzero_gate_on_archwitness
    (lambda : CCM24SoninScale) : Prop :=
  ∃ u0 : sourceSoninCarrier lambda,
    u0 ≠ 0 ∧
      sourceOuterCoframeLeakage lambda twoFamily
        (finiteEulerGram lambda twoFamily u0) ≠ 0

end SoninWindowWitness
end Dev
end ConnesWeilRH
