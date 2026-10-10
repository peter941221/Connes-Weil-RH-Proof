Record 2649: analytic containment certificate for pilot panel 109 GREEN (2624 GO-route brick 4)
Date: 2026-10-10

Result

Positive: `ConnesWeilRH/Dev/C1RouteAComplexPanelAnalytic2649P109.lean`
built green (0 error, 0 `uses sorry`, 0 module warning,
`✔ Built (38s)` over the 3730-job graph) and lands the first analytic
containment certificate of the record-2624 GO route: for the worst
panel of the pilot entry (0, 3),

    ||integral exp(phase)|| <= pairMagnitude(integral2648)
        + exp(1/5) * (residualUpper / (391/400)^2) * 2 * (1/200)^2
      = 4.142072531705658e-3 + 3.568235612869019e-57.

The analytic error term is 54 orders of magnitude below the table
integral it corrects: the 2646 phase engine contains the oscillation
exactly to the precision the 2648 tables carry.

Panel and data

    panel 109 (worst of the 2624 degree-55 ladder), center 29/200,
    half width 1/200, entry (0, 3)
    phase(t) = betaC * t + ofReal(-30 / D(t)),  D(t) = 1 - (c+t)^2
    betaC = beta + i*psi (exact hex-float-derived rationals from 2648)
    quotient identity:  D^2 * (P' - phase' * P) = residual
    numerator  N(t) = betaC * D(t)^2 - 60 * (c + t)  (quartic, 5 pairs)

Theorem chain (all consuming the committed 2646/2647/2648 layers)

1. Deficit lower bound 391/400 on the panel (nlinarith, no new data).
2. Deficit and numerator table replays at an arbitrary position — the
   numerator eval is the first complex-power table replay: `pow_two`
   must fire before `Complex.mul_re`, since simp cannot push `.re`
   through a complex power.
3. Real and complex phase derivatives, rebuilt layer by layer with
   `simpa using` on plain lambdas (the 2647 house pattern); the raw
   `HasDerivAt.div` output carries Pi-form atoms that ring cannot
   equate with their beta forms.
4. Residual stability: `||P' - phase'*P|| <= RU/(391/400)^2`, proved by
   term-level algebra against the replay (`sub_mul, mul_right_comm,
   hrel, ← hom, ring`); linear_combination's module normalform does
   not reconcile the atom spellings between the replay and the goal.
5. Re-variation: `|Re(phase(t) - phase(0))| <= 1/10` — beta term
   <= 1/25, deficit term <= 1/20 via the exact sign identity
   `(-30)/d + 30/a = 30*(d - a)/(a*d)` and `|d - a| <= 59/40000`.
6. Pointwise bound, integral error, polynomial FTC bridge to the
   2648 integral table, and the final triangle certificate.

The certificate bound is stated in the cast form
`((RU / ((391:ℚ)/400)^2 : ℚ) : ℝ)` so it feeds the coming (0,3)
entry containment against the committed 2597 rectangle unchanged.

Build evidence

Nine builds: (5) 15 errors — the cast-elaboration and Pi-form diseases
of earlier records; (6) 4 errors after the pow_two/simpa/restructure
round — exposed a real sign bug in the deficit-variation identity
(`30*(a-d)/(a*d)` vs the true `30*(d-a)/(a*d)`, caught by field_simp
producing a provably false subgoal); (7) 2 errors — pow_le_pow_left₀
needs the literal form and the integral split needs the integrand's
elaboration level pinned; (8) 1 error — the `: ℝ → ℂ` ascription on
the split integrand made the elaborator read the integrand as a
function-space element (`NormedAddCommGroup (ℝ → ℂ)` fails); (9)
green with the integrand as a pointwise-sum body lambda, which exact
reconciles with the Pi-form of `intervalIntegral.integral_add`
definitionally. Laws: AGENTS 2ck.

Scope

One panel, one column, analytic containment only: no panel
partition, no off-diagonal entry claim, no producer claim. Producer
GO, SourceRH, RH remain open.

Next obligations

1. 190-panel partition over the remaining panels of column 3
   (monotone edge bound at the two half-width edge panels).
2. The (0,3) entry containment against the committed 2597 rectangle;
   widen row 0 to the 27 non-cancelling columns.
3. cell2700 pilot discharge (lane-A audit unknown #1, margin 1.14e-10).
