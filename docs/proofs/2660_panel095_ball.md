Record 2660: P095 certified panel ball (ball replacement over 2659)
Date: 2026-10-10

Result

Positive.  `ConnesWeilRH/Dev/C1RouteAPanelBall2660P095.lean` proves the
first ball-replacement theorem of the entry (0, 3) containment chain: the
true panel value, formed with the TRUE amplitude, TRUE rotation, and TRUE
center-normalized exponential integral, lies in the L1 ball around the
exact rational assembly center with radius

    panelAssemblyCharge2659P095 + panelResidualCharge2660P095,

that is

    |amp(c) * rot(c) * integral(exp(phase - phase 0)) - assembly_center|_1
      <= panelAssemblyCharge2659P095 + panelResidualCharge2660P095.

The build is green with zero errors, zero `sorry`, and every declaration
auditing to exactly `[propext, Classical.choice, Quot.sound]`.

Correction carried by this record

The record-2658 phase radius is a PER-COORDINATE radius
(`phaseExp_cos_error2646` and `phaseExp_sin_error2646` each bound one
coordinate), so the L1 rotation error is at most `2 * phaseRadius2658P095`,
not one radius per phase slot.  The record-2659 charge was corrected in
place (both phase slots now carry the factor 2); the corrected float value
is 3.0108388912202296e-87, about 1.68x the original reading.  The fix is a
soundness fix, not a tightening; it is numerically negligible at this
scale.

The residual charge

`panelResidualCharge2660P095` prices the record-2656 analytic residual
(the integral of exp(phase - phase 0) minus the polynomial integral) with
NO factor-2 loss:

  (amp_center + amp_radius) * (2 * exp(2 * (11733889/277722225))
      * complexPanelResidualUpper2648P095 / (9999/10000)^2
      * 2 * h^2),

using `complexL1_le_two_norm2660` on the product `rt * eps_i` with
`|rt| = 1` (the rotation is unitary), which gives `|rt * eps_i|_1 <=
2 * |eps_i|` exactly - the naive two-norm bound on the full product would
have paid a factor 4 * exp * E.

Proof architecture

Generic L1 lemmas on ℂ (add triangle, product submultiplicativity,
two-norm comparison, real-times-complex exact form, embedPair
identification), then the master theorem in three pieces:

  1. piece 1: `ea * rt * eps_i` bounded via
     `complexL1_real_mul2660` + `complexL1_le_two_norm2660` +
     `|rt| = 1` (Complex.norm_exp) + the amplitude upper pin;
  2. piece 2: `(ea * rt - av * ePV) * e_i` bounded via
     complexL1 submultiplicativity, the amplitude pin on
     `(ampCenterComplex2660 - ampValue)` in L1 (radius
     `ampRadius2657P095`), and the rotation-ball pin
     `|rot - ePV|_1 <= 2 * phaseRadius2658P095`;
  3. assembly: split `panelIntegralTrue = eps_i + embedPair(integral)`
     by additivity of the interval integral, decompose, and close by
     nlinarith over the four certified product factors.

Coercion-hygiene note

The real amplitude is embedded into ℂ through a NAMED constant
`ampCenterComplex2660 := Complex.ofReal (Real.exp (ampArg2657P095))`
with rfl lemmas `ampCenterComplex_im2660` / `ampCenterComplex_re2660`.
The first three build attempts failed intermittently on the inlined
spelling `(Real.exp (ampArg2657P095 : ℝ) : ℂ)`: its elaboration is
context-dependent (under some unification contexts the cast normalizes
through the complex exponential, making `.im = 0` simply false as
written).  Naming the constant and proving its `.re`/`.im` behavior once
removed the fragility class; builds then passed first try.

Evidence

- Lean module: `ConnesWeilRH/Dev/C1RouteAPanelBall2660P095.lean`
  (build log `build-logs/2660_ball_build4.log`: 0 `error:`, 0
  `uses sorry`, `Build completed successfully (3737 jobs)`, 8/8 axiom
  lines exactly the standard trio, olean present).
- Corrected pricing: `results/2659_panel095_assembly_pricing.json`
  (charge_float 3.0108388912202296e-87) and
  `scripts/price_panel_assembly_2659.py` (correction comment).

Scope

This panel (P095) and this assembly shape only.  The identity
`integral F = F(c) * integral exp(phase - phase 0)` for the actual entry
integrand, the 190-panel partition sum, and containment in
`analyticMomentInterval2597_row_03` are the next obligations.  No producer
GO and no RH claim is made here.
