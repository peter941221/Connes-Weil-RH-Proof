# 2313 — GRID-SAMPLING-FORMALIZED: the record 2303 sigma-grid covering arithmetic is machine-checked, and the 101-node consumer narrows the strip lane to owner-bridge inputs

Record 2312 left the grid-existence arithmetic of the record 2303
centered-strip envelope as the named hypothesis `hgrid`: every centered
`sigma` within `stripHalfStep2303` of a certified node.  This record
discharges that arithmetic in Lean.

    gridSample2303:
      sigma in [-1/2, 1/2]
      ------------------------------------------------------------
      exists j : Z,  -50 <= j <= 50,  |sigma - j/100| <= stripHalfStep2303

    frozenStripHypothesis_of_certified_nodes:
      node values only at the 101 nodes j/100   (shape of grid_rows)
      + support bounds at stripRadius2303
      ------------------------------------------------------------
      FrozenStripHypothesis

Verdict: **GRID-SAMPLING-FORMALIZED** — the covering arithmetic is a
Lean theorem (standard axioms only, no hypothesis), the node geometry
and covering radius are cross-checked against the committed 2303
artifact in exact rational arithmetic, and the record 2312 files are
proved byte-frozen by cross-record hash continuity.  The residual
strip-lane inputs are now exactly the 101 node values (the grid maximum
over the captured owner) and the support-radius bound — both
owner-bridge obligations.  No owner bridge, no producer GO, no RH
claim.

## The theorem chain (namespace `ConnesWeilRH.Dev`)

+-------------------------------------+----------------------------------+
| declaration                         | content                          |
+-------------------------------------+----------------------------------+
| gridSample2303                      | nearest-node arithmetic: every   |
|                                     | centered sigma is within the     |
|                                     | half-step of a node j/100,       |
|                                     | j in {-50, ..., 50}              |
| frozenStripHypothesis_of_           | 101-node consumer: node values   |
|   certified_nodes                   | at the grid nodes + support      |
|                                     | bounds -> FrozenStripHypothesis  |
+-------------------------------------+----------------------------------+

Continuity structure, support chain, and the envelope conversion are
inherited from records 2312/2311 unchanged; the new module
`ConnesWeilRH/Dev/C1RouteAGridSampling.lean` imports
`C1RouteAStripTransfer` and does not touch it or the arithmetic module.

## The sampling argument

`j = floor (sigma * 100 + 1/2)` is the round-to-nearest index.  The
index bounds are `Int.le_floor` (from `sigma >= -1/2`:
`-50 <= sigma*100 + 1/2`) and `Int.floor_le_iff` (from
`sigma <= 1/2`: `sigma*100 + 1/2 < 51`).  The distance bound is the
floor sandwich `Int.floor_le` and `Int.lt_floor_add_one`:

    floor y <= y < floor y + 1   at   y = sigma*100 + 1/2
    =>  -1/2 <= sigma*100 - floor y < 1/2
    =>  |sigma - floor y / 100| = |sigma*100 - floor y| / 100
       <= 1/200 = stripHalfStep2303        (abs_div + norm_num)

No enumeration, no case analysis on the 101 nodes: the Lean theorem is
the continuum statement, and the 101-node grid enters only through the
consumer's hypothesis set.

## Pins and the exact covering certificate

The pin check `scripts/routea_grid_sampling_lean_pin_2313.py` reads the
Lean sources, extracts the statement geometry, and verifies in
`Fraction` arithmetic against `results/2303_corrected_strip_envelope.json`:

+-------------------------+------------------------------+------------+
| quantity                | reference                    | value      |
+-------------------------+------------------------------+------------+
| Lean node range         | artifact grid_rows           | -50 .. 50  |
| Lean denominator        | grid spacing 1/100           | 100        |
| stripHalfStep2303       | grid.half_step render 0.005  | 0.005      |
| design half-step        | 1/(2*(101-1))                | 1/200      |
| covering radius         | sup over [-1/2, 1/2] of      | 1/200      |
|                         | distance to nearest node     |            |
+-------------------------+------------------------------+------------+

The covering radius is certified exactly: with design nodes `j/100` the
distance-to-nearest-node function is piecewise linear with breakpoints
at the nodes and their midpoints, so its sup over the window is
attained on the window endpoints, the node points (distance 0) and the
midpoints (distance exactly `1/200`); the script evaluates all of them
in exact rationals and obtains `1/200`, equal to the Lean bound target.
The artifact compatibility is exact: all 101 committed `sigma` renders
round-trip to the design decimal `j/100` (max deviation 0.0), the
`j`-labels are contiguous `-50..50`, and the committed `grid.half_step`
render equals `1/200`.

## Cross-record hash continuity

The 2313 record narrows the 2312 "no grid sampling" non-claim without
editing the 2312 files, and the pin check makes that mechanical: the
live md5 hashes of `C1RouteAItem5Arithmetic.lean`
(`b3fb88c3dd1e2e289454193dfc000376`) and `C1RouteAStripTransfer.lean`
(`9bcd576a9ade09702b07235ed1c9f6c2`) equal the hashes recorded in the
2312 pin artifact's provenance.  Any future edit to those files breaks
the 2313 check until the drift is explained.

## Controls

Controls run in the same pass and all pass:

+-----------------------------+--------------------------------------+
| control                     | observed                             |
+-----------------------------+--------------------------------------+
| synthetic parse             | fabricated 60/60/120 geometry parsed |
|                             | back exactly                         |
| shifted grid rejected       | nodes shifted +6e-3 exceed the       |
|                             | radius at the window endpoint        |
| short grid rejected         | 100 nodes leave sigma = 1/2 at       |
|                             | distance 1/100                       |
| tight bound rejected        | bound 1/1000 below the exact sup     |
|                             | 1/200                                |
+-----------------------------+--------------------------------------+

One control premise was falsified by measurement during development: a
uniform node shift of 1e-3 does NOT break the covering bound (midpoint
distances are shift-invariant; only the window endpoints see the shift,
and 1e-3 < 1/200).  The rejection control therefore uses a 6e-3 shift,
above the radius.  The lesson is registered: a negative control must
falsify the bound, not merely perturb the object.

## Lean acceptance (record 2313)

+--------------------------------+--------------------------------------+
| artifact                       | reading                              |
+--------------------------------+--------------------------------------+
| C1RouteAGridSampling.lean      | new module, 2 declarations           |
| C1RouteAGridSamplingProbe.lean | +2 #print axioms                     |
+--------------------------------+--------------------------------------+

Targeted build log `build_2313_step1.log`: `Build completed successfully
(3573 jobs)`, zero `error:` lines, zero `sorryAx`, zero warnings from
the two new files.  Root aggregate log `build_2313_root.log` (library
plus the new probe explicit): `Build completed successfully (4245
jobs)`, 0 errors, the replayed probe output carries the standard axiom
trio `[propext, Classical.choice, Quot.sound]` for both declarations.
The plan-count figures are reported verbatim; both root runs (2312 and
2313) report 4245, so no per-module census delta is claimed from them.

## What this changes for the route

- The 2312 grid consumer's hypothesis splits into a sampled half and a
  value half; the sampled half is now a theorem.  The new consumer
  `frozenStripHypothesis_of_certified_nodes` takes node values only at
  the exact 101 nodes of the committed `grid_rows`, which is the shape
  the owner bridge must produce.
- The strip lane now reads: 101 node values (owner) + support radius
  (owner) -> `FrozenStripHypothesis` -> producer.  The first strip-lane
  obligation named by record 2311 has its arithmetic half closed.
- The record 2312 module, its probe, and its pin artifact are unchanged;
  the 2312 checker still passes against the frozen files.

## Non-claims

- The node-value hypothesis (`hnode`) is not proved: the grid maximum
  over the captured owner is still an artifact-grade input, and the
  owner bridge (captured owner vs selected Lean test functions, support
  radius, node values) is not done.
- The 2303 reduction (pavement, zero-count gate, coefficient inflation,
  node evaluation) remains artifact-grade.
- No producer GO, no gate sign change, no RH claim.

## Provenance

- Lean: `ConnesWeilRH/Dev/C1RouteAGridSampling.lean` (new, md5
  `3581e51273315f70394add69cfbd7647`) and its probe (md5
  `44a6688c2728e1fb858013e1f55c25c7`).
- Check: `scripts/routea_grid_sampling_lean_pin_2313.py` ->
  `results/2313_grid_sampling_lean_pin.json` (verdict
  PINNED-GRID-SAMPLING-VERIFIED, failures empty).
- Upstream artifacts: `results/2303_corrected_strip_envelope.json`
  (grid), `results/2312_strip_transfer_lean_pin.json` (hash continuity).

Next registered obligation: the owner bridge — identify the captured
owner with the selected Lean test functions, prove the support-radius
bound at `stripRadius2303`, and supply the 101 node values at
`stripGridMax2303`; then the signed margin and the non-tail charge; the
selected-owner signed inequality remains the summit.