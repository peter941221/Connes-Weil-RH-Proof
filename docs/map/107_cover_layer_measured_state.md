# 107 — COVER layer: measured state of the (delta, gamma, scale) problem

Date: 2026-09-27.

Status: routing record. Subordinate to
[003](003_b1_b5_minimal_exit_route_selection.md) and
[004](004_endpoint_literature_interface_audit.md); it applies the decision
rules fixed in [1998](../proofs/1998_cover_strategy_desk.md) and pre-registered
in [2012](../proofs/2012_cover_window_floor_scans_preregistration.md) to the
measurements reported in [2016](../proofs/2016_cover_window_law_outcome.md)
and [2017](../proofs/2017_cover_delta_floor_outcome.md).  It proves nothing,
moves no gate, and does not touch the binding producer obligation.  RH is not
claimed.

## 1. What the layer is

COVER is the uniformity clause every route needs and no route's Lean source
currently states:

```text
hypothetical off-line zero rho = (1/2 + delta) + i*gamma
  -> a healthy selected CompactLog detector g for that rho
  -> qw(g) < 0
  -> prove qw(g) >= 0 for the same owner
  -> contradiction -> SourceRH -> Mathlib RiemannHypothesis
```

The producer lanes (map 104, 103/105/106) live in the second-to-last line.
COVER lives in the first: for every hypothetical `rho`, a witness must exist,
with the health screen `C > 0` (record 1931) and the binding sign `D < 0`
(records 1981/2014a) carried along.  The witness set is parameterized by three
coordinates - `delta` (distance from the line), `gamma` (ordinate), `scale`
(the family width multiplier) - so "is there a witness" is a question about
that three-dimensional set, not about a single detector.

## 2. Measured state

Both halves of the record-2012 pre-registration have now run on the committed
family.  The measurements are in `docs/proofs/`; this map records only what
they rule.

```text
coordinate      question                          reading        verdict
delta (2017)    smallest delta with a host        0.02 at all    FLOOR_UNIFORM
                at each height, scale swept       eight heights
scale (2016)    width of the C > 0 band per      4..1 grid      KNOT_COMPLEX
                height at delta = 0.10            steps; 4-7
                                                  bands/height
layer (2016)    gamma_5 through both layers      bands differ   control fires
                                                  cell by cell
```

Three readings carry the routing weight:

- the health predicate in `scale` is a comb, not an interval (4-7 disjoint
  `C > 0` runs per height, all in the single-copy committed family);
- the binding sign `D < 0` is scale-dependent below `gamma_6` (43 of 190 cells
  have `D >= 0`, all at `gamma_1..gamma_5`), so the host set is a comb
  intersected with a region;
- the `gamma_5` layer control disagrees between the committed and EXT layers,
  so no cross-height width law is licensed by this data.

Versus the coordinates that turned out benign: the host's *scale window* at a
fixed height is stable over the whole delta grid, and `n_primes` is a function
of (layer, height, scale) alone, so moving the witness toward the line costs
nothing in the visible-prime book.  The cost of the near-line direction is not
information, it is resolution.

## 3. Routing rulings

Only the registered precedence rules were applied, and they give:

```text
direction A   window-track theorem                 EXCLUDED by measurement
              (WINDOW_STABLE not met; the predicate is neither an interval in
              scale nor layer-stable at the one height where layers vary)
direction D   Speiser split (near-line winding)    STAYS DOWN-GRADED
              (FLOOR_UNIFORM; the near-line side is not a wall above the
              smallest registered delta)
directions    family-covering / Diophantine (C)     NOT SELECTED
C and E       total positivity / variation (E)      NOT SELECTED
              (both were the WINDOW_PINCHING branch, which did not trigger:
              PINCHING needs gamma_7 and gamma_8 at <= 2 steps AND gamma_1 at
              >= 5 steps; the data has gamma_7 at 1 and gamma_8 at 2 - the
              narrow end holds - but gamma_1 at 4, one step short of the
              anchor bar, so the branch fails on its wide-anchor clause)
```

## 4. The live obligation

COVER's analytic currency is now an open question again, and that state is the
ruling: the witness cannot be produced by a *scale window* argument (A) and
cannot be produced by a *near-line obstruction* argument (D).  What survives
both measurements is the structure the data actually shows - a per-height,
scale-specific, delta-stable witness with a frozen visible-prime book - which
is exactly the shape direction C is priced for (a family-covering certificate
with explicit Diophantine control of the phase vectors `gamma*log p`).

This does not reorder the mainline.  COVER is downstream of the producer: the
binding obligation remains `D < 0` on the selected healthy owner (map 104,
records 1981/2014/2014a), the F2 gate of record 1997 stands, and no COVER
mechanism may be promoted while the producer's own margin is open.

## 5. Registered follow-up measurements

Two are registered, and both are measurements rather than mechanisms:

```text
M1  the band-edge re-read at dxi = 0.002 (registered in 2016 section 5):
    the comb is a dxi = 0.004 reading of C, the cancelled coordinate whose
    offset is the mass-level offset amplified by |2 + f|, and f reaches
    1.6e+06 at gamma_2 against 8.6e+04 where record 2014 measured the
    amplification - so the comb's fine structure, and at gamma_2 the sign of C
    itself, must be re-read at half resolution before any decision rests on it
M2  a finer delta grid (0.005, 0.01, 0.02) on the heights whose hosts sit
    inside the five-point grid (registered in 2017 section 5): FLOOR_UNIFORM is
    a statement about delta >= 0.02 and cannot distinguish "no wall" from "a
    wall below 0.02"; M2 is the only registered way to move the near-line
    quantifier
```

A third, deliberately not registered: the far-delta side.  Two heights lose
their five-point host at `delta = 0.30`, and section 2a of the registration
forbids reading a negative from a five-point grid, so this is an observation
about an unmeasured question - the delta-interval question - not a finding.

## 6. Boundaries

The rulings rest on registered decision rules applied to measurements on one
family, one layer per height plus one control, one resolution, eight heights
and `delta >= 0.02`.  They are not theorems about the operator, they do not
cover unmeasured heights or deltas, they cannot be promoted to the map as
numerical facts (map policy), and they change no Lean statement.  Any future
campaign that wants direction A or D back must produce either a new control
that repairs the layer disagreement or a measurement that moves the floor
below the registered grid - not a new reading of the same data.