Record 2652: complete boundary-integral discharge — the 2551-2559 conditional family cleared GREEN
Date: 2026-10-10

Result

Positive: `ConnesWeilRH/Dev/C1RouteABoundaryDischarge2652.lean` built
green (`ℹ [4017/4017] Built ... (3.0s)` + `Build completed
successfully (4017 jobs)`; 0 error, 0 `uses sorry`, 0 module warning;
all four unconditional forms depend only on
`[propext, Classical.choice, Quot.sound]`).

Before this record, a full inventory sweep found that the committed
2553-2559 batch era already carried the SAME coefficient-ball
conditional across the whole signed-segment family — ten cell-spans
across both signs — and the 2649 lane-A audit had undercounted this
inventory (it scanned four payloads; the 2557/2558/2559 readbacks
were already committed).  This record discharges every composition
top of that family, in the two standard forms:

    target                              covers                      discharged upper
    bothSignsSegmentIntegralBound2558   2700/2701, both signs       5159/10^12 (sum)
    centralBothSignsIntegralBound2559   5119/5120, both signs       35314967257/500000000000
    batchC02702Minus...Bound2558        cell 2702 minus             59/25000000000
    batchC02702Plus...Bound2558         cell 2702 plus              27/250000000000

Each target gets a region form (hypothesis weakened to membership in
the record-2338 base boxes, via `baseCoefficient_error_of_box2540`)
and an unconditional form (exact-rational center tuple instantiated,
zero premises).  Together with records 2650 (cell2700 edge form) and
2651 (cell5440), TWELVE unconditional boundary certificates now
exist, and NO committed boundary-integral certificate in the
2551-2559 family retains the ball premise in discharged form.

Mechanism

Identical to 2650/2651 — the ball is implied by the certified box
region, so the discharge is a two-line composition at every level of
the composition tree.  The new observation is ECONOMIC: discharging
the composition TOPS (the both-signs segments) covers six cell-spans
per theorem, including cell 2701 plus which has no per-cell
certificate of its own.  Discharge effort should always target the
top of the certificate DAG.

Audit correction

`results/2652_lane_a_pricing_audit_v2.json` supersedes the 2649
inventory counts: the committed conditional family was 10 per-cell
certificates + 6 segments (not 3 entries), the minus-sign boundary
chain already existed (the old unknown #2 premise was wrong), and
the residual unknowns are re-ranked: #1 exact-owner transfer
composition, #2 grid scale-out of the (now fully proven) batch
pipeline, #3 full-grid import composition.  Method law: audits must
glob the payload range, not hand-pick (AGENTS 2cm).

Build evidence and the transient-failure note

The first build attempt failed with `unknown free variable HSub` at
`C1RouteABatchC05120PlusMidpoint2559.lean:1695` — a 3264-line
generated module compiled for the first time since the 2650 mirror
repair.  Diagnosis: a direct lean invocation of the identical module
(standard LEAN_PATH, fresh olean output) compiled with ZERO errors,
and the unchanged lake build then passed green.  Classified as a
transient parallel-elaboration glitch; no source was patched.  Laws:
AGENTS 2cm (retry-then-direct-lean protocol before touching any
generated file).

Scope

The discharged certificates cover their cells and spans at the
center owner (unconditional) and over the record-2338 region
(conditional form).  No full-grid claim, no Weil-positivity
conclusion (the bounds are integrals of norms), exact-owner transfer
remains open.  Producer GO, SourceRH, RH remain open.

Next obligations

1. Exact-owner transfer composition (unknown #1): assemble the
   2452/2453-54/2455-59 per-seam imports into a live-tuple box-
   membership assertion; the region forms are its waiting consumer.
2. Grid scale-out (unknown #2): batch the 2547-2551/2553-2559
   generators over further cells — the pipeline, discharge pattern,
   and audit loop are now proven end-to-end at twelve certificates.
3. Parallel 2649 lane: 190-panel partition over column 3, then the
   (0,3) entry containment against the committed 2597 rectangle.
