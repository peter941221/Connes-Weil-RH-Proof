import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20YoshidaMellin
import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Dev.SchwartzAmbientOwnerProbe
import ConnesWeilRH.Source.CC20Concrete.CCM24LogRadialSupport
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh

/-!
# E_lambda family monotonicity: the radial/log-Fourier/Sonin subspaces grow with lambda

Task 3 of the wide-3.  The generic-lambda `hfactor` Summable gap (845) has no
transport/conjugation bridge; 846 diagnosed the remaining live road as a
"lambda-monotone projector-family spectral bound".  This probe writes the FIRST
step of that road: prove that the whole `E_lambda` grid of closed subspaces —

    radialSupport  E_lambda   := ker(restrict t<log lambda)
    Fourier Q_lambda          := comap(HT, radialSupport lambda)
    Sonin  R0_lambda          := radialSupport ⊓ FourierSupport

— is *monotone non-decreasing in lambda* (lambda_1 ≤ lambda_2 ⇒ subspace ≤).
That is the submodule-family side (projective family ordering) of the gap.  It
does not close RH and does not give the Summable either; it is the honest first
sentence of the generic-lambda analysis (the family grows like radial support).

RH is NOT claimed.  Pure supporting fact; zero `sorry`, `#print axioms` stays
clean like the other probes.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace ELambdaMonotone

open MeasureTheory Set

/-- The radial-support closed subspace cramnotes with `lambda`: the forbidden
radial region is `{t | t < log λ}`, which GROWS with λ (bigger log), so a
bigger λ imposes vanishing on a bigger region and yields a SMALLER subspace.
Thus `λ_a ≤ λ_b ⇒ LogRadial λ_b ⊆ LogRadial λ_a` (antitγ in λ).  This is the
root of the `E_λ` family ordering; `comap`/`⊓` propagate it to the
Fourier/Sonin subspaces below. -/
lemma logRadialSubspace_antitone
    {lambda_b : CCM24SoninScale}
    (lambda_a : CCM24SoninScale)
    (hle : lambda_a.1 ≤ lambda_b.1) :
    ccm24LogRadialSupportClosedSubspace lambda_b ≤
      ccm24LogRadialSupportClosedSubspace lambda_a := by
  intro u hu
  rw [mem_ccm24LogRadialSupportClosedSubspace_iff] at hu ⊢
  -- the forbidden radial region {t | t < log λ} GROWS with λ, so a *larger*
  -- ν (bigger log) imposes vanishing on a strictly larger region, hence gives
  -- a *smaller* subspace; `{t | t < log λ_a} ⊆ {t | t < log λ_b}`, so vanishing
  -- on the larger (λ_b) region is stronger.
  have hlog_a_le : Real.log lambda_a.1 ≤ Real.log lambda_b.1 :=
    Real.log_le_log lambda_a.property hle
  filter_upwards [hu] with t htVanish
  intro hta
  exact htVanish (lt_of_lt_of_le hta hlog_a_le)

/-- Fourier-support subspace: `comap` preserves the antitone radial ordering,
so `λ_a ≤ λ_b ⇒ Fourier λ_b ⊆ Fourier λ_a`. -/
lemma fourierSubspace_antitone
    {lambda_b : CCM24SoninScale}
    (lambda_a : CCM24SoninScale)
    (hle : lambda_a.1 ≤ lambda_b.1) :
    ccm24ArchimedeanFourierSupportClosedSubspace lambda_b ≤
      ccm24ArchimedeanFourierSupportClosedSubspace lambda_a := by
  intro u hu
  rw [mem_ccm24ArchimedeanFourierSupportClosedSubspace_iff] at hu ⊢
  exact (logRadialSubspace_antitone lambda_a hle) hu

/-- Sonin: intersection of two antitone families is antitone. -/
lemma soninSubspace_antitone
    {lambda_b : CCM24SoninScale}
    (lambda_a : CCM24SoninScale)
    (hle : lambda_a.1 ≤ lambda_b.1) :
    ccm24ArchimedeanSoninClosedSubspace lambda_b ≤
      ccm24ArchimedeanSoninClosedSubspace lambda_a := by
  intro u hu
  have huradial_b : u ∈ ccm24LogRadialSupportClosedSubspace lambda_b :=
    (Submodule.mem_inf.mp hu).1
  have hufourier_b : u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda_b :=
    (Submodule.mem_inf.mp hu).2
  have huradial_a : u ∈ ccm24LogRadialSupportClosedSubspace lambda_a :=
    (logRadialSubspace_antitone lambda_a hle) huradial_b
  have hufourier_a : u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda_a :=
    (fourierSubspace_antitone lambda_a hle) hufourier_b
  exact Submodule.mem_inf.mpr ⟨huradial_a, hufourier_a⟩

end ELambdaMonotone
end CC20Concrete
end Source
end ConnesWeilRH