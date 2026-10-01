import ConnesWeilRH.Dev.C1RouteAEndpointStrip

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def externalFamilyValue2344
    (coefficient : ℂ) (modulation radius position : ℝ) : ℂ :=
  if |position| < radius then
    coefficient * Complex.exp
      ((-30 / (1 - (position / radius) ^ 2) : ℝ) +
        (modulation * position : ℝ) * Complex.I)
  else 0

noncomputable def externalPhysical2344
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) : ℝ → ℂ :=
  fun position => ∑ index : Fin 30,
    externalFamilyValue2344 (coefficients index) (modulations index)
      (storedWidth index ^ 2) position

theorem externalFamilyValue2344_eq_familyTerm
    (coefficient : ℂ) (modulation radius position : ℝ) :
    externalFamilyValue2344 coefficient modulation radius position =
      coefficient * (widthBump radius position : ℂ) *
        Complex.exp ((modulation * position : ℝ) * Complex.I) := by
  by_cases hinside : |position| < radius
  · simp only [externalFamilyValue2344, widthBump, if_pos hinside,
      Complex.exp_add, Complex.ofReal_exp]
    ring
  · simp [externalFamilyValue2344, widthBump, hinside]

theorem externalPhysical2344_eq_correctedPhysical
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    externalPhysical2344 coefficients modulations =
      correctedPhysical coefficients modulations := by
  funext position
  unfold externalPhysical2344 correctedPhysical physicalFamilySum
  apply Finset.sum_congr rfl
  intro index _
  exact externalFamilyValue2344_eq_familyTerm _ _ _ _

theorem externalPhysical2344_secondDerivative_eq
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    deriv (deriv (externalPhysical2344 coefficients modulations)) =
      deriv (deriv (correctedPhysical coefficients modulations)) := by
  rw [externalPhysical2344_eq_correctedPhysical]

theorem externalPhysical2344_stripNorm_eq
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) (sigma : ℝ) :
    stripNorm sigma (externalPhysical2344 coefficients modulations) =
      stripNorm sigma (correctedPhysical coefficients modulations) := by
  rw [externalPhysical2344_eq_correctedPhysical]

theorem externalPhysical2344_stripSecondNorm_eq
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) (sigma : ℝ) :
    stripSecondNorm sigma (externalPhysical2344 coefficients modulations) =
      stripSecondNorm sigma (correctedPhysical coefficients modulations) := by
  rw [externalPhysical2344_eq_correctedPhysical]

theorem frozenStripHypothesis_of_external_endpoint_bounds
    (baseCoefficients correctionCoefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ)
    (hbase : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripNorm endpoint (externalPhysical2344 baseCoefficients modulations) ≤ baseNormUpper2343)
    (hbaseSecond : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripSecondNorm endpoint (externalPhysical2344 baseCoefficients modulations) ≤
        baseSecondUpper2343)
    (hcorrection : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripNorm endpoint (externalPhysical2344 correctionCoefficients modulations) ≤
        correctionNormUpper2343)
    (hcorrectionSecond : ∀ endpoint ∈ ({-(1 / 2), 1 / 2} : Set ℝ),
      stripSecondNorm endpoint (externalPhysical2344 correctionCoefficients modulations) ≤
        correctionSecondUpper2343) :
    FrozenStripHypothesis (correctedPhysicalCompactLogTest baseCoefficients modulations)
      (correctedPhysicalCompactLogTest correctionCoefficients modulations) := by
  apply frozenStripHypothesis_of_owner_endpoint_bounds
    baseCoefficients correctionCoefficients modulations
  · simpa only [externalPhysical2344_stripNorm_eq] using hbase
  · simpa only [externalPhysical2344_stripSecondNorm_eq] using hbaseSecond
  · simpa only [externalPhysical2344_stripNorm_eq] using hcorrection
  · simpa only [externalPhysical2344_stripSecondNorm_eq] using hcorrectionSecond

end ConnesWeilRH.Dev
