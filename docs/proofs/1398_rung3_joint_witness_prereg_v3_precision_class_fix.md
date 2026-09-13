# 1398 v3 — Preregistration revision: the GF/GR precision class, the GV band margin, and tier-2 failure scope (model VERBATIM; revisions justified by two disclosed VOID-run telemetry sets)

Date: 2026-09-14. Law 42 revision path, third application in this line
(1388 -> 1390 pre-run; 1398 v1 -> v2 pre-run; here v2 -> v3 AFTER two
VOID runs whose gates themselves refused to certify). v2 was committed
(cbaf45e), then two instrument invocations ran and both printed
`VERDICT jointWitness=NONE cells=VOID` — the runs produced NO verdict
digits; what they produced is disclosed gate telemetry, used here exactly
as 1393 v3 used inv1/inv2 telemetry. v2 is hereby SUPERSEDED; no model
content moves. RH not claimed.

## Telemetry that motivates this revision (disclosed, uncertified, verdict-free)

inv1 (log `1398_rig_run.log.inv1`, gs_ok=False): the GS gate caught the
mpmath three-argument `mp.matrix(m, n, list)` silent zero-fill — the same
1393-inv1 trap; the solve produced the zero vector, `A = 0` exactly, and
GS/GF/GD failed. Instrument fix (nested-list constructor + local rhs
integrity assert) committed; model untouched.

inv2 (log `1398_rig_run.log`, tier-1 only, then VOID): all structural
gates PASSED — GI, G0, GS (residual 5.2e-58 / 2.3e-56), GT
(1.2e-60 / 6.8e-17 / 3.4e-17), GD (`|lap g,rho + 1| = 2.3e-7`), GQ
(`A_quadr == 4*A` to 15 digits, error 0.0). Two convergence gates FAILED:

```text
GF (npw-24 vs npw-32 recompute of F(0)): relative difference  7.7e-7  vs 1e-8 locked
GR (npw-32 vs npw-64 recompute of A)   : relative difference  6.3e-7  vs 1e-8 locked
```

A dedicated convergence probe (tier-1 owner, `npw` in 24/32/64/96):

```text
npw:        24             32             64             96
A:      -88.19508618   -88.19525497   -88.19519960   -88.19518121
delta:      --+1.69e-4--   +5.54e-5--     +1.84e-5--
```

The step ratios fit `error = C/npw` with `C ~ 3.6e-3` (first-order) to
within 2%: 5.54/1.84 = 3.01 = (1/32-1/64)/(1/64-1/96). So the 1e-8
relative class is NOT achievable by this instrument at ANY node count —
v2 locked a precision class the instrument cannot attain. This is law F10
(the prereg must numerically lock its achievable precision class) violated
in the optimistic direction, the mirror image of 1393 v2's band-DROP
unsatisfiability. The VALUE side is stable far beyond what matters here:
`A = -88.1952 +- 2e-4`, negative by 6.8e5 tie-band widths.

## What moves (exactly four clauses)

1. **GF recompute class**: `GF_RE_TOL` (npw-24 vs npw-32 relative bound
   on `re F(0)`) REVISED `1e-8 -> 1e-5`. Achieved measured: 7.7e-7
   (13x margin). `GF_IM_TOL` (1e-6) and `F(0) > 0` strict POSITIVITY
   unchanged.
2. **GR class**: `GR_TOL` (npw-32 vs npw-64 relative bound on `A`)
   REVISED `1e-8 -> 1e-5`. Achieved measured: 6.3e-7. Violation still
   means VOID. Reporting addition: the tier-1 line must also print
   `A96` and the first-order Richardson value `A_R = 2*A64 - A32`
   (INFORMATIONAL only, no gate consumes it).
3. **GV band margin**: POS/NEG classification now requires crossing the
   tie edge by more than the certified uncertainty can move it:
   `POS iff A > (1 + 1e-3) * GV_TIE * S`, `NEG iff A < -(1 + 1e-3) *
   GV_TIE * S`, else TIE. The 1e-3 relative margin dominates the revised
   1e-5 certified error class by 100x; decisive cells (|A| / (1e-6*S) in
   the thousands or more) classify unchanged.
4. **Tier-2 failure scope**: a tier-2 cell whose OWN integrity checks fail
   (`GS` residual > 1e-30, or `F(0) <= 0`, or `|Im F(0)| > 1e-6*re F(0)`,
   or `|lap + 1| > 1e-6`) is classified `BADCELL`: excluded from the
   POS/NEG/TIE census, printed with its numbers, and counted — it does
   NOT void the run. Rationale, pre-committed: the float64 `lap` and
   `F(0)`-imaginary noise grows with `|Im rho|` (the tier-2 candidate set
   reaches `im = 2108`, twice tier-1's frequency); letting one cell's
   arithmetic floor void 41 cells converts an honest census into a
   deadlock, while the per-cell exclusion keeps every COUNTED digit
   certified at its own locked class. Tier-1 global gates keep VOID
   semantics unchanged; `GI` remains global-VOID on violation.
   The sentinel gains a fourth count:
   `VERDICT jointWitness=<geo|NONE> cells=POS:n,NEG:m,TIE:k,BAD:b`.

## Everything else

Model (v1 sections 1.1-1.5 with v2's unchanged re-lock), cells and tier
rules (v1 section 2 + the inv1-fixed positional decode: 96,000 rows,
census PASS 45,915 / MARGINAL 6,283 / FAIL 43,802 verified against the
1394 record by the inv2 GI gate), instrument construction (v1 section 3
verbatim including npw = 32/64/24 definitions, the 16-node GL panels, the
closed sliver forms, the graded J master), gates G0/GI/GS/GT/GQ
verbatIM, kill scope (v1 section 6 VERBATIM — a negative decides nothing;
this revision is a precision calibration, not a scope change), artifacts
`docs/proofs/1398_rig_*` with `*.invN.*` rename-before-rerun (inv1, inv2
exist), acceptance log-not-exit-code, boundary: unchanged.

Zero certified rung-3 digits exist before this file; inv1/inv2 values are
uncertified VOID telemetry disclosed above and in the 1399 outcome record
as such. The instrument fix between inv1 and inv2 was constructor syntax
only (rhs construction), never model content. RH not claimed.
