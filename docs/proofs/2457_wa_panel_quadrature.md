# 2457 - W-A panel quadrature bound landed in Lean (one-sided trapezoid)

Date: 2026-10-02.

Verdict in one line: obligation W-A of record 2455 is discharged - the
one-sided panel quadrature bound is a Lean theorem on the standard
three axioms, and the discovery that Mathlib already carries the
trapezoidal error theorem (TrapezoidalRule, 2025) reduced the module to
a single-sided corollary plus the strip-shaped instance.

## Statements

`panelQuadrature_le_2457` (`ConnesWeilRH/Dev/C1RouteAPanelQuadrature
2457.lean`): for g : R -> R, a <= b, g C^2 on the closed panel with
|iteratedDerivWithin 2 g (uIcc a b) x| <= zeta, and N > 0,

  integral x in a..b, g x
    <= trapezoidal_integral g N a b + (b - a)^3 * zeta / (12 * N^2).

`stripPanelQuadrature_expNorm_le_2457`: the same for the strip integrand
shape exp(sigma x) * |F x| - the exact form the 2342 panel factor
m_(k+2) + 2|sigma| m_(k+1) + sigma^2 m_k (times exp(|sigma| R)) feeds
once W-C attaches the m_j sup bounds.

Build: 2678 jobs green on the ext4 mirror; both declarations audited on
[propext, Classical.choice, Quot.sound].  The proof of the core theorem
is the Mathlib bound in absolute value, one outward rewrite of
|b - a| <= b - a, and the lower half of the absolute-value split by
linarith - the one-sided direction is free.

## Why the node values stay hypotheses

The theorem is deliberately owner-free: trapezoidal_integral contains
the node evaluations g(a + (k+1)(b-a)/N) symbolically.  Attaching the
actual owner's node values (the 2454-style containment at each node of
the ~98k-120k grid) and the zeta bound is W-C; the support glue
(full-line stripNorm = panel interval integral for supported
integrands) is the remaining W-A extension, both recorded as open.

## Discovery note

The whole module rests on Mathlib.MeasureTheory.Integral.
IntervalIntegral.TrapezoidalRule (new-location layout; the old
Mathlib.MeasureTheory.IntervalIntegral path does not exist in v4.30).
The 2455 plan had W-C sized for a hand-built panel theorem; with the
Mathlib theorem in hand the panel side is one import away, and the
grid-glue plus attachment become the only real cost centers.

Scope: generic analysis, no owner data, no strip norm discharged, no
producer GO, no RH claim.

Evidence:

- `ConnesWeilRH/Dev/C1RouteAPanelQuadrature2457.lean`
- `ConnesWeilRH/Dev/C1RouteAPanelQuadrature2457Audit.lean`
- `build-logs/2457_panel_quadrature.log`
