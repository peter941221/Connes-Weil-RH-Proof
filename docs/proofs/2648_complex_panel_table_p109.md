Record 2648: complex panel table for the (0,3) pilot panel 109 GREEN (2624 GO-route brick 3)
Date: 2026-10-10

Result

Positive: `ConnesWeilRH/Dev/C1RouteAComplexPanelTable2648P109.lean`
built green (0 error, 0 `uses sorry`, 0 module warning,
`✔ Built (42s)` over the 3729-job graph) and lands the first complex
panel table of the record-2624 GO route: the exact rational data layer
of the worst panel of the pilot entry (0, 3).

Panel and data

    panel 109 (worst panel of the 2624 degree-55 ladder), center 29/200,
    half width 1/200, degree 55, entry (0, 3)
    beta = node_re * width^2, psi = (node_im + modulation) * width^2
      (exact hex-float-derived rationals from the 2275 owner capture,
      |psi| = 422.5447585... column-3 family)
    complex numerator N(t) = (beta + i*psi) * D(t) - 60 * (center + t)

Emitted tables: deficit (3 pairs), numerator (5 pairs), polynomial
(57 pairs — degree-55 coefficients plus one trailing zero slot),
primitive (57 pairs), residual (61 slots — 55 zero, five structural,
one trailing zero), residualUpper, integral. Every table is
regression-checked in the generator against
`offdiagonal_residual_pricing_2624.build_complex_panel` (modulus
bound and integral byte-equal) and the degree-55 `worst_panel == 109`
payload check. residualUpper ~ 5.58e-53, integral ~ (4.06e-3, -8.70e-5).

Theorems (all `decide +kernel`, all against the record-2647 generic
layer): primitive derivative replay, D P' - N P residual replay with
`take 55 = replicate 55 (0, 0)` and `drop 60 = [(0, 0)]` zero-slot
checks, |re| + |im| residual-upper replay and nonnegativity, and the
two integral components. No analytic containment is emitted here;
that is the next brick.

The trailing-zero-slot law

The generator initially emitted the polynomial without the trailing
zero slot and the primitive replay failed with "Reduction got stuck"
at the FIRST pair addition — a misleading display: the house
derivative helpers (`polynomialDerivative2621`,
`complexPolyDerivative2647`) are length-preserving, so
`derivative primitive = polynomial` is length-exact only when the
polynomial carries the same trailing zero slot the primitive carries
at its head (the committed 2621 tables end with `((0 : ℚ) / 1)]`).
With the pad, the residual gains one trailing zero slot and the
replay becomes `.drop (degree+5) = [(0, 0)]`. residualUpper and the
integral are unchanged by the padding. New laws: AGENTS 2cj.

Build evidence

Five builds: (1) missing list commas — 10 "Function expected" errors
and sorry-poisoned lists; (2) /tmp log lost to `set -e` aborting
before the cp; (3) only the primitive replay failing, stuck at slot 0;
(4) green with 8 heartbeat-linter warnings; (5) green, 0 warnings —
`set_option maxHeartbeats 2000000 in` + explanatory comment before
each replay theorem. Probes confirmed `decide +kernel` handles tiny
pair lists, the exact stuck shape, huge fractions, and 57-slot small
data — isolating the failure to the length mismatch, not the tactic.

Scope

Data layer only: one panel, one column, no panel containment, no
analytic consumption, no off-diagonal claim. Producer GO, SourceRH,
RH remain open.

Next obligations

1. Complex primitive/FTC helper + analytic pilot-panel containment
   consuming `complexExpPolynomialResidualStability2647` with the
   phase engine of record 2646 (the 2649 shape), then the 190-panel
   partition + monotone edge bound.
2. The (0,3) entry containment against the committed 2597 rectangle;
   widen row 0 to the 27 non-cancelling columns.
3. Producer GO, SourceRH, RH stay out of scope.
