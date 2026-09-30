/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1RouteAOwnerSupport
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The corrected owner as a compact log test (record 2315)

Record 2314 proved the support radius of the corrected width-a^2 owner
`correctedPhysical`; the record 2313 strip consumer takes its inputs as
`CompactLogTest`s (`test : SchwartzMap ℝ ℂ` plus `HasCompactSupport`).
This module closes that structural gap: the owner is packaged as a
`CompactLogTest`, for arbitrary coefficient and modulation vectors.

The bridge between the two shapes is the flat-junction identity

    widthBump radius x = expNegInvGlue ((1 - (x / radius)^2) / 30)
      (0 < radius),

where `expNegInvGlue t = exp (-t⁻¹)` for `t > 0` and `0` for `t ≤ 0`:
the bump's `if |x| < radius` guard matches `t > 0` exactly, and
`-30 / w = -((w / 30)⁻¹)`.  Smoothness is then inherited from Mathlib's
`expNegInvGlue.contDiff` (its junction is flat enough to be `C^∞`),
composed with the smooth rational map, and the family sum is smooth by
`ContDiff.sum`; compact support is the record 2314 `tsupport` bound
through `IsCompact.of_isClosed_subset` and `isClosed_tsupport`.

Main declarations:

* `widthBump_eq_expNegInvGlue`, `widthBump_contDiff` — the identity and
  bump smoothness;
* `familyTerm_contDiff`, `physicalFamilySum_contDiff`,
  `physicalFamilySum_hasCompactSupport` — smoothness and compact
  support of the general family sum;
* `storedWidth_pos` — every stored width is positive (the radii of the
  corrected owner are their squares);
* `correctedPhysical_contDiff`,
  `correctedPhysical_hasCompactSupport` — the owner instances;
* `correctedPhysicalCompactLogTest` — the packaged `CompactLogTest`,
  with `correctedPhysicalCompactLogTest_toFun` (the underlying function
  is the owner), `correctedPhysicalCompactLogTest_tsupport_subset` (the
  support bound in exactly the hypothesis shape of the record 2313 node
  consumer), and `correctedPhysicalCompactLogTest_compactSupport`.

Residual owner-bridge obligation: the 101 node values at
`stripGridMax2303` (over the captured coefficient and modulation
vectors, artifact-grade).  No producer GO, no gate sign change, no RH
claim.
-/

namespace ConnesWeilRH
namespace Dev

open scoped BigOperators
open scoped ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

/-- **The bump is the flat-junction glue (record 2315).**  For positive
radius the width bump equals Mathlib's `expNegInvGlue` at the scaled
quadratic deficit: the `if |x| < radius` guard matches `t > 0`, and
`-30 / w = -((w / 30)⁻¹)`. -/
theorem widthBump_eq_expNegInvGlue (radius : ℝ) (hr : 0 < radius) :
    ∀ x : ℝ,
      widthBump radius x = expNegInvGlue ((1 - (x / radius) ^ 2) / 30) := by
  intro x
  by_cases hlt : |x| < radius
  · have h1 : |x / radius| < 1 := by
      rw [abs_div, abs_of_pos hr, div_lt_one hr]
      exact hlt
    have h2 : (x / radius) ^ 2 < 1 := by
      nlinarith [sq_abs (x / radius), abs_nonneg (x / radius)]
    have hu : 0 < 1 - (x / radius) ^ 2 := by linarith
    rw [widthBump, if_pos hlt]
    unfold expNegInvGlue
    rw [if_neg (not_le.mpr (div_pos hu (by norm_num : (0 : ℝ) < 30)))]
    congr 1
    rw [inv_div, neg_div]
  · have h1 : 1 ≤ |x / radius| := by
      rw [abs_div, abs_of_pos hr, one_le_div hr]
      exact not_lt.mp hlt
    have h2 : 1 ≤ (x / radius) ^ 2 := by
      rw [← sq_abs (x / radius)]
      exact one_le_pow₀ h1
    have hu : 1 - (x / radius) ^ 2 ≤ 0 := by linarith
    rw [widthBump, if_neg hlt]
    exact (expNegInvGlue.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg hu (by norm_num : (0 : ℝ) ≤ 30))).symm

/-- **The bump is smooth (record 2315).** -/
theorem widthBump_contDiff (radius : ℝ) (hr : 0 < radius) :
    ContDiff ℝ ∞ (fun x : ℝ => widthBump radius x) := by
  have h : ContDiff ℝ ∞
      (fun x : ℝ => expNegInvGlue ((1 - (x / radius) ^ 2) / 30)) :=
    expNegInvGlue.contDiff.comp (by fun_prop)
  simpa [funext (widthBump_eq_expNegInvGlue radius hr)] using h

/-- **Family terms are smooth (record 2315).**  Coefficient and
modulation are arbitrary; only the radius positivity enters. -/
theorem familyTerm_contDiff (coefficient : ℂ) (modulation radius : ℝ)
    (hr : 0 < radius) :
    ContDiff ℝ ∞ (fun x : ℝ =>
      coefficient * (widthBump radius x : ℂ) *
        Complex.exp ((modulation * x : ℝ) * Complex.I)) := by
  have hw : ContDiff ℝ ∞ (fun x : ℝ => (widthBump radius x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (widthBump_contDiff radius hr)
  have hphase : ContDiff ℝ ∞ (fun x : ℝ =>
      (modulation * x : ℝ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul contDiff_id)).mul contDiff_const
  exact (contDiff_const.mul hw).mul (Complex.contDiff_exp.comp hphase)

/-- **The family sum is smooth (record 2315).** -/
theorem physicalFamilySum_contDiff (coefficients : Fin 30 → ℂ)
    (modulations radii : Fin 30 → ℝ) (hradii : ∀ index, 0 < radii index) :
    ContDiff ℝ ∞ (physicalFamilySum coefficients modulations radii) := by
  change ContDiff ℝ ∞ (fun x : ℝ => ∑ index : Fin 30,
      coefficients index * (widthBump (radii index) x : ℂ) *
        Complex.exp ((modulations index * x : ℝ) * Complex.I))
  exact ContDiff.sum (fun index _ => familyTerm_contDiff
    (coefficients index) (modulations index) (radii index) (hradii index))

/-- **The family sum has compact support (record 2315).** -/
theorem physicalFamilySum_hasCompactSupport (coefficients : Fin 30 → ℂ)
    (modulations radii : Fin 30 → ℝ) {R : ℝ}
    (hR : ∀ index, radii index ≤ R) :
    HasCompactSupport (physicalFamilySum coefficients modulations radii) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (physicalFamilySum_tsupport_subset coefficients modulations radii hR)

/-- **Stored widths are positive (record 2315).** -/
theorem storedWidth_pos (index : Fin 30) : 0 < storedWidth index := by
  fin_cases index <;> norm_num [storedWidth]

/-- **The corrected owner is smooth (record 2315).** -/
theorem correctedPhysical_contDiff (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) :
    ContDiff ℝ ∞ (correctedPhysical coefficients modulations) := by
  change ContDiff ℝ ∞ (physicalFamilySum coefficients modulations
    (fun index => storedWidth index ^ 2))
  exact physicalFamilySum_contDiff coefficients modulations
    (fun index => storedWidth index ^ 2)
    (fun index => pow_pos (storedWidth_pos index) 2)

/-- **The corrected owner has compact support (record 2315).** -/
theorem correctedPhysical_hasCompactSupport (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) :
    HasCompactSupport (correctedPhysical coefficients modulations) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (correctedPhysical_tsupport_subset_pin coefficients modulations)

/-- **The corrected owner as a compact log test (record 2315).**  The
packaged test's underlying function is the owner family sum, and its
support is the record 2314 pin interval; the coefficient and modulation
vectors stay free. -/
noncomputable def correctedPhysicalCompactLogTest
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    CompactLogTest :=
  { test := HasCompactSupport.toSchwartzMap
      (correctedPhysical_hasCompactSupport coefficients modulations)
      (correctedPhysical_contDiff coefficients modulations)
    compactSupport := by
      simpa using correctedPhysical_hasCompactSupport coefficients modulations }

/-- **The packaged test is the owner (record 2315).** -/
theorem correctedPhysicalCompactLogTest_toFun (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) :
    ((correctedPhysicalCompactLogTest coefficients modulations).test :
        ℝ → ℂ) = correctedPhysical coefficients modulations := by
  funext x
  exact HasCompactSupport.toSchwartzMap_toFun
    (correctedPhysical_hasCompactSupport coefficients modulations)
    (correctedPhysical_contDiff coefficients modulations) x

/-- **The packaged owner's support bound (record 2315).**  Exactly the
`htsupp` hypothesis shape of the record 2313 node consumer. -/
theorem correctedPhysicalCompactLogTest_tsupport_subset
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    tsupport ((correctedPhysicalCompactLogTest coefficients modulations).test :
        ℝ → ℂ) ⊆
      Set.Icc (-stripRadius2303) stripRadius2303 := by
  rw [correctedPhysicalCompactLogTest_toFun]
  exact correctedPhysical_tsupport_subset_pin coefficients modulations

/-- **The packaged owner's compact support (record 2315).** -/
theorem correctedPhysicalCompactLogTest_compactSupport
    (coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :
    HasCompactSupport ((correctedPhysicalCompactLogTest coefficients
      modulations).test : ℝ → ℂ) :=
  (correctedPhysicalCompactLogTest coefficients modulations).compactSupport

end Dev
end ConnesWeilRH
