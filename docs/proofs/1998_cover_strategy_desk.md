# Record 1998 — COVER strategy desk: the (delta, gamma, scale) knot, verified margins, and five attack directions

Date: 2026-09-26.

Status: desk record. No Lean brick, no rig run registered here (one
post-hoc diagnostic on already-committed JSONs, labeled), no theorem
proved, no RH claim. This consolidates the verified facts about the
COVER layer (uniformity over all hypothetical off-line zeros) and prices
the attack directions. It corrects two claims made in strategy
discussion before this desk.

## 1. Why COVER is the frontier

The formal implication from a same-owner per-rho certificate to Mathlib RH is complete (record 1956). The producer inputs are not complete: what remains are the three analytic facts. The empirical layers of SIGN (D < 0) are green at every measured ordinate gamma_1..gamma_8 (records 1981/1983/1994/1996), but this is not a theorem and does not cover unmeasured ordinates. The open layer is uniformity in rho =
(1/2 + delta, gamma): infinitely many cells, so the certificate must
eventually be one analytic theorem, not per-cell readings.

## 2. Verified facts (sources cited; all numeric claims re-checked
## against committed JSONs and records this date)

**(F-a) The difficulty is ONE three-dimensional knot, not two walls.**
The strategy discussion before this desk framed two walls: a
delta -> 0 wall (near-line) and a gamma -> infinity wall (height). Both
are wrong as absolute walls:

- The record-1981 registered table shows delta = 0.05 FAIL (D =
  +1.006e+06) — but that table is scale 1.00 ONLY. The same committed
  JSON (`results/1981_offline_owner.json`) contains delta = 0.05 at
  scale 0.90 reading C = +4.18, B01 = +5.00e+04, D = -3.678e+08: a
  certified-sign opposite-gates host at delta = 0.05. The record's own
  informational-knobs paragraph already says D < 0 at both scale-0.90
  rows.
- Record 1918's vertex face covers delta = 0.05 at its owner family
  with thin certified margins (disc > 0 on 18/18, margin_rel
  8.66e-04 .. 1.16e-01, worst certified case disc/|ddisc_cert| = 30.4).
- The height side: hosts at every measured ordinate (1996), with
  ordinate-dependent single-scale windows (0.92 at gamma_7, 0.88 at
  gamma_8).

So every measured (delta, gamma) family has a host SOMEWHERE in the
scale grid; the window moves jointly in (delta, gamma, scale). COVER =
"the window never closes" in this 3-space.

**(F-b) Measured margins grow with height; the sampled book is D-dominated.**
|D| at certified hosts: -1.07e+06 (gamma_1, 1981) -> -1.34e+12
(gamma_5 committed, 1994) -> -2.04e+20 (gamma_7, 1996): roughly 14
orders then 8 more. C at hosts: +1.42 (gamma_1) vs +13 .. +664
(gamma_5..gamma_8). Cross-term dominance |B01|/|D| <= 6.7e-02 over all
60 committed cells, and ~ 4e-10 at gamma_7/gamma_8. The difficulty is
the moving window, not the sign strength.

**(F-c) Post-hoc diagnostic (labeled): no tested moment reweighting of the existing book can create uniformity.** Computing the lambda-average of
the gate over [0,1], F = D - B/2 + C/3 (= integral of the parabola
D - lambda*B + lambda^2*C), on all 60 committed cells (1981/1994/1996
JSONs): F has the sign of D in every cell, because |B| and |C| are
dominated by |D| (F-b). Corollary: any "trace/moment-level" escape must
change the BOOK (a different Gram object, e.g. zero-side structure or
the 1919/1920 kernel), not the weights on this one.

**(F-d) The cost law stands (memory-verified, laws 1680 no-slack /
F67 shape).** The current route audit says that COVER must consume an RH-equivalent uniform input somewhere; inventing mathematics here means choosing the softest
currency to pay it, not avoiding it.

## 3. The five attack directions, priced and corrected

```
+---+----------------------+----------+--------------------------------------+
| # | direction            | status   | change made by this desk             |
|   |                      | after    |                                      |
|   |                      | desk     |                                      |
+---+----------------------+----------+--------------------------------------+
| A | window-track         | STRENGTH | F-a/F-b: hosts exist everywhere      |
|   | theorem (envelope    | -ENED    | measured, margins grow; only the     |
|   | calculus on (sc,gam) |          | window moves. Decisive experiment:  |
|   | extending the 1990   |          | the width law (section 4).          |
|   | A-machine)           |          |                                      |
+---+----------------------+----------+--------------------------------------+
| B | trace/moment-level   | FIRST    | F-c kills the reweighting version.  |
|   | certificate          | EXPERI-  | Survives only as a zero-side        |
|   |                      | MENT     | Gram-object reframing (1919/1920    |
|   |                      | DEAD     | kernel moments); unpriced.          |
+---+----------------------+----------+--------------------------------------+
| D | Speiser split        | DOWN-    | F-a: near-line is not currently a   |
|   | (near-line winding + | GRADED   | wall (delta=0.05 hosts). Fallback   |
|   | far-band four-point) |          | if the delta-floor scan finds       |
|   |                      |          | closure below 0.05.                |
+---+----------------------+----------+--------------------------------------+
| E | total positivity /   | UNCHANGED| Classical (Karlin); cheap kernel    |
|   | variation-diminishing|          | check pending; prime cos-kernels    |
|   |                      |          | likely break PF — verify, do not   |
|   |                      |          | assume.                             |
+---+----------------------+----------+--------------------------------------+
| C | family-covering      | UNCHANGED| Research-grade; names the           |
|   | certificate with     |          | obstruction (badly-approximable     |
|   | explicit Diophantine |          | gamma for the phase vectors         |
|   | structure            |          | gamma*log p) — where the F-d cost   |
|   |                      |          | is paid in its hardest currency.    |
+---+----------------------+----------+--------------------------------------+
```

## 4. Decision rules fixed NOW for the next (pre-registered) runs

These rules are binding for the future preregistration files; they are
fixed here before any run.

Width-law scan (direction A): sc grid 0.80..1.00 step 0.01 at delta =
0.10 for gamma_1..gamma_8; window width = contiguous run of certified
C > 0 cells.

```text
WINDOW_STABLE    every gamma has width >= 0.03 (3 grid steps)
WINDOW_PINCHING  width at gamma_7/gamma_8 < 0.02 while gamma_1 >= 0.05
KNOT_COMPLEX     anything else (multiple narrow bands, drift)
A is desk-able only under WINDOW_STABLE; PINCHING redirects to C/E.
```

delta-floor scan: floor(gamma) = smallest delta in {0.02, 0.05, 0.10,
0.15, 0.20, 0.30} with a certified host at that gamma (scale swept,
not sampled).

```text
FLOOR_UNIFORM    floor <= 0.05 for every measured gamma
FLOOR_RISING     floor grows with gamma  -> Speiser split (D) promoted
```

## 5. Scope and honesty

- Nothing here is a theorem; F-a..F-d are verified empirical facts
  about committed data plus two classical citations (1918 margins;
  Karlin total positivity as background for E).
- No change to any Route A or Route B obligation; no change to the
  F2 gate (record 1997 order stands).
- RH is not claimed.

See also: 1917 (trichotomy), 1918 (vertex face), 1981 (registered
point + informational scales), 1994/1996 (height audits), 1997 (F2
bridge desk), 1919/1920 (kernel variance lead, via record 1995's
citations). The numerical cross-check used the committed JSON artifacts
`results/1981_offline_owner.json`, `results/1994_opposite_gates_height.json`,
and `results/1996_gamma78_full_sweep.json`; it is a reproducibility check,
not an additional proof artifact.
