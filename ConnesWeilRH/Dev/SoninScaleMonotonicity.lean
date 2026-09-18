/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.SoninWindowWitness
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

/-!
# Scale monotonicity of the archimedean Sonin carrier

The committed carrier at scale `lambda` is

  `V_arch(lambda) = Radial(lambda) INTER FourierSupport(lambda)`,

where `Radial(lambda) = {u : u = 0 a.e. on t < log lambda}` and
`FourierSupport(lambda) = {u : H u = 0 a.e. on t < log lambda}`.  Since the
vanishing region `Iio (log lambda)` grows with `lambda`, all three subspaces
are antitone in the scale:

  `lambda <= lambda'  ==>  V_arch(lambda') <= V_arch(lambda)`.

Consequences recorded here:

* carrier nonemptiness propagates downward in the scale
  (`archimedeanSoninCarrier_nontrivial_of_le`): a witness at a larger scale
  also witnesses every smaller one, so the set of admissible scales is a
  downward-closed interval and the base obligation is a sharp-threshold
  statement in `lambda`, not an isolated existence at one scale;
* triviality at a scale forces triviality at every larger scale
  (`archimedeanSoninCarrier_nontrivial_of_not_of_le`), which is the exact
  form of the `m = 1` sanity check of record 1624 (there `H = R` and the
  carrier is `{0}` precisely for `log lambda > 0`, so triviality at `1`
  forces triviality at every larger scale).

No existence statement is proved: `archimedeanSoninCarrier_nontrivial` stays
the open analytic obligation (law F33) and RH is not claimed.
-/

namespace ConnesWeilRH
namespace Dev
namespace SoninScaleMonotonicity

open MeasureTheory
open ConnesWeilRH.Source.CC20Concrete
open ConnesWeilRH.Dev.SoninWindowWitness
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramResponse

/-- The radial support subspaces are antitone in the scale: the vanishing
region `t < log lambda` grows with `lambda`. -/
theorem ccm24LogRadialSupportClosedSubspace_mono
    {lambda lambda' : CCM24SoninScale} (h : lambda.1 ≤ lambda'.1) :
    ccm24LogRadialSupportClosedSubspace lambda' ≤
      ccm24LogRadialSupportClosedSubspace lambda := by
  intro u hu
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff] at hu ⊢
  filter_upwards [hu] with t ht
  intro hlt
  exact ht (lt_of_lt_of_le hlt (Real.log_le_log lambda.2 h))

/-- The Fourier-support subspaces are antitone in the scale. -/
theorem ccm24ArchimedeanFourierSupportClosedSubspace_mono
    {lambda lambda' : CCM24SoninScale} (h : lambda.1 ≤ lambda'.1) :
    ccm24ArchimedeanFourierSupportClosedSubspace lambda' ≤
      ccm24ArchimedeanFourierSupportClosedSubspace lambda := by
  intro u hu
  exact ccm24LogRadialSupportClosedSubspace_mono h hu

/-- The archimedean Sonin carrier is antitone in the scale. -/
theorem ccm24ArchimedeanSoninClosedSubspace_mono
    {lambda lambda' : CCM24SoninScale} (h : lambda.1 ≤ lambda'.1) :
    ccm24ArchimedeanSoninClosedSubspace lambda' ≤
      ccm24ArchimedeanSoninClosedSubspace lambda :=
  inf_le_inf (ccm24LogRadialSupportClosedSubspace_mono h)
    (ccm24ArchimedeanFourierSupportClosedSubspace_mono h)

/-- Carrier nonemptiness propagates downward in the scale: a witness at the
larger scale `lambda'` also witnesses the larger carrier at `lambda`. -/
theorem archimedeanSoninCarrier_nontrivial_of_le
    {lambda lambda' : CCM24SoninScale} (h : lambda.1 ≤ lambda'.1) :
    archimedeanSoninCarrier_nontrivial lambda' →
      archimedeanSoninCarrier_nontrivial lambda := by
  rintro ⟨u, hu⟩
  have hu_ne : (u : cc20GlobalLogCrossingL2) ≠ 0 :=
    fun h0 => hu (Subtype.ext h0)
  exact ⟨⟨(u : cc20GlobalLogCrossingL2),
    ccm24ArchimedeanSoninClosedSubspace_mono h u.2⟩,
    fun hzero => hu_ne (congrArg Subtype.val hzero)⟩

/-- Triviality at a scale forces triviality at every larger scale. -/
theorem archimedeanSoninCarrier_nontrivial_of_not_of_le
    {lambda lambda' : CCM24SoninScale} (h : lambda.1 ≤ lambda'.1) :
    ¬ archimedeanSoninCarrier_nontrivial lambda →
      ¬ archimedeanSoninCarrier_nontrivial lambda' :=
  fun h' h0 => h' (archimedeanSoninCarrier_nontrivial_of_le h h0)

end SoninScaleMonotonicity
end Dev
end ConnesWeilRH
