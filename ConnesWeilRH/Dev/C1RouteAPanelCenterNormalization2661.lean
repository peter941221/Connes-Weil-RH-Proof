import ConnesWeilRH.Dev.C1RouteAAnalyticMomentNormalization2618

/-!
# Panel center normalization for the normalized moment integrand (record 2661)

Generic bridge between the actual normalized entry integrand
(`normalizedMomentIntegrand2618`) and the per-panel certificate spelling of
records 2655-2660: on a panel of half-width `halfWidth` centered at `center`,
the normalized integrand factors as the center value times the panel-local
phase exponential

  F(center + position)
    = F(center) * exp(phase(position) - phase(0)),

where the center factor and the phase are spelled to definitionally match the
generated record-2656 panel phase and the record-2660 amplitude / rotation.
The coefficient hypothesis `hcoef` is the exact-rational tie between the
captured entry parameters and the panel table (instantiated per entry).

Scope: the algebraic factorization on one panel; no integral bounds, no
off-diagonal claim, no entry containment.
-/

namespace ConnesWeilRH.Dev

open MeasureTheory
open scoped Interval

/-- Panel-local phase, spelled to definitionally match
`complexPanelPhase2656P095` after instantiation. -/
noncomputable def panelPhase2661 (beta psi center : ℝ) (position : ℝ) : ℂ :=
  ((beta : ℂ) + (psi : ℂ) * Complex.I) * (position : ℂ)
    + Complex.ofReal ((-30 : ℝ) / (1 - (center + position) ^ 2))

/-- Center factor `exp(beta*center - 30/(1-center^2)) * exp(I*psi*center)`,
spelled to definitionally match `ampCenterComplex2660 * rotTrue2660P095`
after the rational pins. -/
noncomputable def panelCenterFactor2661 (beta psi center : ℝ) : ℂ :=
  Complex.ofReal (Real.exp (beta * center - 30 / (1 - center ^ 2)))
    * Complex.exp (Complex.I * ((psi * center : ℝ) : ℂ))

theorem normalizedMomentIntegrand_eq_centerFactor2661
    (modulation radius : ℝ) (node : ℂ) (beta psi center halfWidth position : ℝ)
    (hcoef : (node + (modulation : ℂ) * Complex.I) * (radius : ℂ)
      = (beta : ℂ) + (psi : ℂ) * Complex.I)
    (hguardWidth : |center| + halfWidth < 1)
    (hposition : position ∈ Set.Icc (-halfWidth) halfWidth) :
    normalizedMomentIntegrand2618 modulation radius node (center + position)
      = panelCenterFactor2661 beta psi center
        * Complex.exp (panelPhase2661 beta psi center position
            - panelPhase2661 beta psi center 0) := by
  have hguard : |center + position| < 1 := by
    have h1 : |center + position| ≤ |center| + |position| := abs_add_le _ _
    have h2 : |position| ≤ halfWidth := abs_le.mpr hposition
    linarith
  have hexp : Complex.ofReal ((-30 : ℝ) / (1 - (center + position) ^ 2))
        + ((beta : ℂ) + (psi : ℂ) * Complex.I) * ((center + position : ℝ) : ℂ)
      = (Complex.ofReal (beta * center - 30 / (1 - center ^ 2))
          + Complex.I * ((psi * center : ℝ) : ℂ))
        + (panelPhase2661 beta psi center position
            - panelPhase2661 beta psi center 0) := by
    unfold panelPhase2661
    push_cast
    ring
  unfold normalizedMomentIntegrand2618 panelCenterFactor2661
  rw [if_pos hguard, hcoef, hexp]
  rw [Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp]

theorem panelCenterNormalization2661
    (modulation radius : ℝ) (node : ℂ) (beta psi center halfWidth : ℝ)
    (hcoef : (node + (modulation : ℂ) * Complex.I) * (radius : ℂ)
      = (beta : ℂ) + (psi : ℂ) * Complex.I)
    (hwidth : 0 ≤ halfWidth) (hguardWidth : |center| + halfWidth < 1) :
    (∫ position in (-halfWidth)..halfWidth,
        normalizedMomentIntegrand2618 modulation radius node (center + position))
      = panelCenterFactor2661 beta psi center
        * ∫ position in (-halfWidth)..halfWidth,
            Complex.exp (panelPhase2661 beta psi center position
              - panelPhase2661 beta psi center 0) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro position hposition
  have hle : -halfWidth ≤ halfWidth := by linarith
  rw [Set.uIcc_of_le hle] at hposition
  exact normalizedMomentIntegrand_eq_centerFactor2661 modulation radius node beta psi
    center halfWidth position hcoef hguardWidth hposition

#print axioms normalizedMomentIntegrand_eq_centerFactor2661
#print axioms panelCenterNormalization2661

end ConnesWeilRH.Dev
