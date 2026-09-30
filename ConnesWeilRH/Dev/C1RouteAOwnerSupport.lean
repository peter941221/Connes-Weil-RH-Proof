/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic

/-!
# Owner support radius at the strip pin (record 2314)

Record 2303 certified the centered-strip envelope on the corrected
width-a^2 owner, and record 2276 built that owner's family sum in Lean:
`correctedPhysical` is the finite sum over the 30 stored families of
`coefficient * widthBump (a_j^2) x * exp (i * theta_j * x)`, where the
bump `widthBump r x = exp (-30 / (1 - (x/r)^2))` on `|x| < r` and `0`
outside.  Records 2312/2313 consume a support-radius bound
`tsupport f subset [-stripRadius2303, stripRadius2303]` as the first
half of the owner bridge.

This module supplies that half for the corrected owner, for arbitrary
coefficient and modulation vectors:

* `widthBump_eq_zero_of_not_lt` /
  `ofReal_widthBump_eq_zero_of_not_lt` / `widthBump_support_subset` —
  the bump profile vanishes outside `|x| < radius`;
* `familyTerm_support_subset` — a single family term is supported in
  `[-radius, radius]` (coefficient and modulation are irrelevant);
* `physicalFamilySum_support_subset` /
  `physicalFamilySum_tsupport_subset` — the family sum is supported in
  `[-R, R]` once every family radius is at most `R`;
* `storedWidth_nonneg`, `storedWidth_le_four`, `storedWidth_sq_le_four`
  — family 4 is the unique largest stored width, so every squared width
  is at most `a_4^2`;
* `storedWidth_four_sq_le_pin` — `a_4^2 <= stripRadius2303` in exact
  rational arithmetic: the pin `6.5536001` dominates the exact radius
  `a_4^2 = 2076918743413931858457251756481 / 316912650057057350374175801344`
  whose float64 render is exactly the committed `owner.rmax`
  `6.553600000000003`, with slack `9.999999745341483e-08`;
* `correctedPhysical_tsupport_subset_four` and
  `correctedPhysical_tsupport_subset_pin` — the corrected owner family
  sum has `tsupport subset [-a_4^2, a_4^2] subset
  [-stripRadius2303, stripRadius2303]`.

The remaining owner-bridge obligations are the `CompactLogTest`
packaging of the owner (smooth bump, compact support as structure data)
and the 101 node values (the grid maximum over the captured owner,
artifact-grade).  No producer GO, no gate sign change, no RH claim.
-/

namespace ConnesWeilRH
namespace Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

/-- **Bump vanishes outside the radius (record 2314).** -/
theorem widthBump_eq_zero_of_not_lt (radius position : ℝ)
    (h : ¬ |position| < radius) : widthBump radius position = 0 := by
  rw [widthBump, if_neg h]

/-- **Complex bump vanishes outside the radius (record 2314).** -/
theorem ofReal_widthBump_eq_zero_of_not_lt (radius position : ℝ)
    (h : ¬ |position| < radius) : (widthBump radius position : ℂ) = 0 := by
  rw [widthBump_eq_zero_of_not_lt radius position h, Complex.ofReal_zero]

/-- **Bump support (record 2314).**  The width bump is supported in
`[-radius, radius]`. -/
theorem widthBump_support_subset (radius : ℝ) :
    Function.support (fun x : ℝ => (widthBump radius x : ℂ)) ⊆
      Set.Icc (-radius) radius := by
  intro x hx
  have hlt : |x| < radius := by
    by_contra h
    exact hx (ofReal_widthBump_eq_zero_of_not_lt radius x h)
  exact ⟨le_of_lt (abs_lt.mp hlt).1, le_of_lt (abs_lt.mp hlt).2⟩

/-- **Family-term support (record 2314).**  A single family term
`c * bump(r, x) * exp(i theta x)` is supported in `[-r, r]`; the
coefficient and the modulation do not matter for support. -/
theorem familyTerm_support_subset (coefficient : ℂ) (modulation radius : ℝ) :
    Function.support (fun x : ℝ =>
      coefficient * (widthBump radius x : ℂ) *
        Complex.exp ((modulation * x : ℝ) * Complex.I)) ⊆
      Set.Icc (-radius) radius := by
  intro x hx
  exact widthBump_support_subset radius (by
    intro hb
    exact hx (by simp [hb]))

/-- **Family-sum support (record 2314).**  Once every family radius is at
most `R`, the finite family sum is supported in `[-R, R]`. -/
theorem physicalFamilySum_support_subset (coefficients : Fin 30 → ℂ)
    (modulations radii : Fin 30 → ℝ) {R : ℝ}
    (hR : ∀ index, radii index ≤ R) :
    Function.support (physicalFamilySum coefficients modulations radii) ⊆
      Set.Icc (-R) R := by
  intro x hx
  by_contra hxR
  refine hx ?_
  rw [physicalFamilySum]
  apply Finset.sum_eq_zero
  intro index _
  have hout := ofReal_widthBump_eq_zero_of_not_lt (radii index) x (by
    intro hlt
    exact hxR (Set.Icc_subset_Icc (neg_le_neg (hR index)) (hR index)
      ⟨le_of_lt (abs_lt.mp hlt).1, le_of_lt (abs_lt.mp hlt).2⟩))
  simp [hout]

/-- **Family-sum tsupport (record 2314).**  Same bound for the closed
support. -/
theorem physicalFamilySum_tsupport_subset (coefficients : Fin 30 → ℂ)
    (modulations radii : Fin 30 → ℝ) {R : ℝ}
    (hR : ∀ index, radii index ≤ R) :
    tsupport (physicalFamilySum coefficients modulations radii) ⊆
      Set.Icc (-R) R :=
  isClosed_Icc.closure_subset_iff.mpr
    (physicalFamilySum_support_subset coefficients modulations radii hR)

/-- **Stored widths are nonnegative (record 2314).** -/
theorem storedWidth_nonneg (index : Fin 30) : 0 ≤ storedWidth index := by
  fin_cases index <;> norm_num [storedWidth]

/-- **Family 4 is the largest stored width (record 2314).** -/
theorem storedWidth_le_four (index : Fin 30) :
    storedWidth index ≤ storedWidth 4 := by
  change storedWidth index ≤ (1441151880758559 / 562949953421312 : ℝ)
  fin_cases index <;> norm_num [storedWidth]

/-- **Squared stored widths are at most `a_4^2` (record 2314).** -/
theorem storedWidth_sq_le_four (index : Fin 30) :
    storedWidth index ^ 2 ≤ storedWidth 4 ^ 2 :=
  pow_le_pow_left₀ (storedWidth_nonneg index) (storedWidth_le_four index) 2

/-- **The exact owner radius is below the strip pin (record 2314).**
`a_4^2 <= stripRadius2303` in exact rational arithmetic; the pin
dominates the exact radius `2076918743413931858457251756481 /
316912650057057350374175801344` whose float64 render is the committed
`owner.rmax` `6.553600000000003`. -/
theorem storedWidth_four_sq_le_pin :
    storedWidth 4 ^ 2 ≤ stripRadius2303 := by
  change (1441151880758559 / 562949953421312 : ℝ) ^ 2 ≤ (6.5536001 : ℝ)
  norm_num

/-- **Corrected owner support at the exact family radius (record 2314).**
The corrected family sum has `tsupport subset [-a_4^2, a_4^2]` for
arbitrary coefficients and modulations. -/
theorem correctedPhysical_tsupport_subset_four (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) :
    tsupport (correctedPhysical coefficients modulations) ⊆
      Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2) := by
  change tsupport
    (physicalFamilySum coefficients modulations
      (fun index => storedWidth index ^ 2)) ⊆
      Set.Icc (-(storedWidth 4 ^ 2)) (storedWidth 4 ^ 2)
  exact physicalFamilySum_tsupport_subset coefficients modulations
    (fun index => storedWidth index ^ 2)
    (fun index => storedWidth_sq_le_four index)

/-- **Corrected owner support at the strip pin (record 2314).**  The
support-radius half of the owner bridge: the corrected owner family sum
has `tsupport subset [-stripRadius2303, stripRadius2303]` for arbitrary
coefficients and modulations, exactly the hypothesis shape consumed by
the record 2313 grid consumer. -/
theorem correctedPhysical_tsupport_subset_pin (coefficients : Fin 30 → ℂ)
    (modulations : Fin 30 → ℝ) :
    tsupport (correctedPhysical coefficients modulations) ⊆
      Set.Icc (-stripRadius2303) stripRadius2303 :=
  (correctedPhysical_tsupport_subset_four coefficients modulations).trans
    (Set.Icc_subset_Icc (neg_le_neg storedWidth_four_sq_le_pin)
      storedWidth_four_sq_le_pin)

end Dev
end ConnesWeilRH
