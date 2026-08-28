/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20Eq115Table
import ConnesWeilRH.Dev.C1CC20FiniteRankProfileSymmetry
import ConnesWeilRH.Dev.C1CC20FiniteRankHalfGapCertificate

/-!
# Concrete symmetry and certificate assembly for the extracted table

The extracted equation-(115) table `cc20Eq115Data` realizes the paper's
`alpha_{-n} = -alpha_n`, `d(-n) = d(n)` conventions structurally over the
paired index `Fin m x Bool`, so the evenness producer of
`C1CC20FiniteRankProfileSymmetry` applies verbatim.  This leaf packages that
pairing, proves the finite profile even and ROOT-window continuous, and
assembles the Fact-1 half-gap certificate for the concrete table.

After this assembly the ONLY remaining unknowns of the concrete certificate
are the two analytic sides supplied by the caller:

* the ROOT-window continuity of the endpoint profile `chi` (an explicit
  `CC20EndpointSpectralData` instance with an analytic enclosure does not
  exist yet), and
* the strict mass inequality `2 * integral_[0, log 2] |chi - tau| <= epsilon1`
  (the paper states only an asymptotic decimal).

Reference: equations (114)--(115), (120)--(121) of
<https://arxiv.org/html/2006.13771>; table provenance in
`C1CC20Eq115Table`.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20Eq115Symmetry

open MeasureTheory
open CC20Concrete
open C1CC20DisplacementKernel C1CC20FiniteRankApproximation
  C1CC20FiniteRankDifference C1CC20FiniteRankHalfGapCertificate
  C1CC20FiniteRankProfileSymmetry C1CC20OperatorGap

open C1CC20Eq115Table

/-- The paired `plus/minus` negation data of the extracted table: the `Bool`
slot carries the sign, so frequencies flip and coefficients are preserved
under `cc20Eq115NegIndex`. -/
def cc20Eq115NegationData (lam : Real) :
    CC20FiniteRankProfileNegationData (cc20Eq115Data lam) where
  negIndex := cc20Eq115NegIndex
  frequency_at_negIndex := by
    rintro ⟨n, s⟩
    cases s <;> simp [cc20Eq115Data, cc20Eq115NegIndex]
  perturbedFrequency_at_negIndex := by
    rintro ⟨n, s⟩
    cases s <;> simp [cc20Eq115Data, cc20Eq115NegIndex]
  coefficient_at_negIndex := by
    rintro ⟨n, s⟩
    simp [cc20Eq115Data, cc20Eq115NegIndex]

/-- The extracted finite profile is even, for every value of the free scale
`lam`.  This discharges `finite_profile_even` of the Fact-1 half-gap
certificate concretely, from published data alone. -/
theorem cc20Eq115Profile_even (lam : Real) (v : Real) :
    cc20FiniteRankProfile (cc20Eq115Data lam) (-v) =
      cc20FiniteRankProfile (cc20Eq115Data lam) v :=
  cc20FiniteRankProfile_even_of_negationData _ (cc20Eq115NegationData lam) v

/-- The equation-(115) difference profile of the extracted table is even. -/
theorem cc20Eq115DifferenceProfile_even (lam : Real)
    (endpointData : CC20EndpointSpectralData) (v : Real) :
    cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) (-v) =
      cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v :=
  cc20FiniteRankDifferenceProfile_even_of_finiteProfile_even endpointData _
    (cc20Eq115Profile_even lam) v

/-- One Fourier-projection profile is continuous on the ROOT displacement
window: the closed-window indicator is invisible from inside the window. -/
theorem continuousOn_cc20FourierProjectionProfile (alpha : Real) :
    ContinuousOn (cc20FourierProjectionProfile alpha) cc20RootDisplacementWindow := by
  have hg : ContinuousOn
      (fun v : Real => ((cc20RootLength⁻¹ : Real) : ℂ) * cc20FourierPhase (-alpha) v)
      cc20RootDisplacementWindow :=
    continuous_const.continuousOn.mul (continuous_cc20FourierPhase (-alpha)).continuousOn
  exact hg.congr fun v hv => by
    simp only [cc20FourierProjectionProfile, Set.indicator_of_mem hv]

/-- The extracted finite profile is continuous on the ROOT displacement
window: a finite sum of window-indicator Fourier phases. -/
theorem continuousOn_cc20Eq115Profile (lam : Real) :
    ContinuousOn (cc20FiniteRankProfile (cc20Eq115Data lam)) cc20RootDisplacementWindow := by
  have hterm : ∀ i : Fin 1732 × Bool,
      ContinuousOn (cc20FiniteRankProfileTerm (cc20Eq115Data lam) i)
        cc20RootDisplacementWindow := by
    intro i
    have hfun2 : (cc20FiniteRankProfileTerm (cc20Eq115Data lam) i) =
        fun v : Real =>
          cc20FourierProjectionProfile ((cc20Eq115Data lam).frequency i) v -
            (((cc20Eq115Data lam).coefficient i : Real) : ℂ) •
              cc20FourierProjectionProfile
                ((cc20Eq115Data lam).perturbedFrequency i) v := by
      funext v
      simp only [cc20FiniteRankProfileTerm, Pi.sub_apply, Pi.smul_apply]
    rw [hfun2]
    exact (continuousOn_cc20FourierProjectionProfile
        ((cc20Eq115Data lam).frequency i)).sub
      ((continuousOn_cc20FourierProjectionProfile
        ((cc20Eq115Data lam).perturbedFrequency i)).const_smul
        (((cc20Eq115Data lam).coefficient i : Real) : ℂ))
  have hsum : ContinuousOn
      (fun v : Real =>
        ∑ i : Fin 1732 × Bool, cc20FiniteRankProfileTerm (cc20Eq115Data lam) i v)
      cc20RootDisplacementWindow :=
    continuousOn_finsetSum Finset.univ fun i _ => hterm i
  have hfun :
      (∑ i : Fin 1732 × Bool, cc20FiniteRankProfileTerm (cc20Eq115Data lam) i) =
        fun v : Real =>
          ∑ i : Fin 1732 × Bool, cc20FiniteRankProfileTerm (cc20Eq115Data lam) i v := by
    funext v
    exact Finset.sum_apply v Finset.univ
      (fun i => cc20FiniteRankProfileTerm (cc20Eq115Data lam) i)
  unfold cc20FiniteRankProfile
  rw [hfun]
  exact hsum.const_smul ((cc20Eq115Data lam).lambda : ℂ)

/-- The Fact-1 half-gap certificate of the EXTRACTED table.  Every structural
field is discharged here from published data; the caller supplies only the
two analytic sides: the ROOT-window continuity of `chi` and the strict mass
inequality `2 * integral_[0, log 2] |chi - tau| <= epsilon1`. -/
theorem cc20Eq115_halfGapCertificate
    (lam : Real) (endpointData : CC20EndpointSpectralData)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (hmass :
      2 * ∫ v in (0 : ℝ)..cc20RootLength,
          ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤
        gapData.epsilon1) :
    CC20FiniteRankHalfGapCertificate endpointData (cc20Eq115Data lam) gapData where
  difference_profile_continuousOn_root := by
    unfold cc20FiniteRankDifferenceProfile
    exact hchi.sub (continuousOn_cc20Eq115Profile lam)
  finite_profile_even := cc20Eq115Profile_even lam
  two_half_norm_mass_le_epsilon1 := hmass

end C1CC20Eq115Symmetry
end Source
end ConnesWeilRH
