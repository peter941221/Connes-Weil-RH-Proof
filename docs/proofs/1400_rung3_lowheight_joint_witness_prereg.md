# 1400 — Preregistration: RUNG-3 LOW-HEIGHT joint-witness rig — first evaluation of A(g) at the actual zeta-zero heights on the instrument-visible head of the (J1) PASS band

Date: 2026-09-13 (committed before any rung-3 digit of this wave).
Follows [1399](1399_rung3_joint_witness_outcome_all_negative.md) section 8
item 1 (the data-named live direction: 1659 of the 1700 PASS-band
candidate geometries were never evaluated, and the 41 that were, all sat
at the artificial height im = 1054 where the shape levers are provably
dead). Model, instrument, gates, kill scope: [1398 v3
chain](1398_rung3_joint_witness_prereg_v3_precision_class_fix.md),
re-locked VERBATIM below and physically shared through module import —
`scripts/run_1400_rig.py` imports `scripts/run_1398_rig.py` and changes
ONLY the selection rule, tiering, conditioning audit, artifact names and
the run's log identity. RH not claimed.

## 0. What this rig decides (identical one-sided scope to 1398)

DECIDES (MODEL evidence, one-sided): does any evaluated low-height owner
geometry carry BOTH (J1) PASS (1394/1393 artifact band) AND A(g) > 0
outside the GV tie window? A POS cell is joint-witness evidence for
simultaneous rung-2/rung-3 realizability on ONE owner at a height that is
an actual zeta zero. DECIDES NOTHING when negative (sup-lower-bound law,
1087 s2 verbatim in 1397 s3); a FAIL is NOT a falsifier of route alpha.
CANNOT decide: sign on all owners, rung 4/5, RH either direction.

## 1. Selection (A-BLIND, deterministic, computed from the committed artifact only)

Candidates: geometries with >= 1 PASS row in
`docs/proofs/1393_component5_rig_cells.tsv.gz` (positional decode and GI
recompute gate of 1398 v1/v2/v3 section 2, VERBATIM including the inv1
rhs-construction fix), RESTRICTED to heights `im in {14.134725,
21.022040, 25.010858}` (the three lowest grid heights; 14.134725 is the
first zeta zero ordinate; im = 1054 is EXCLUDED — measured in 1399).

INSTRUMENT-VISIBILITY FILTER (pre-run, rung-2 quantities only; this is
the law F12 audit as a per-cell precondition): a candidate geometry is
TESTED only if, writing `alpha_X = lambda_min G(R_X; nodes)` and
`delta_X = min(R_X/2, eps_X*alpha_X/(4(1+eps_X)TB_X^2))` exactly as in
1398 v1 sections 1.2 (the Lift.lean formulas):

```text
alpha_f >= 1e-11  AND  alpha_u >= 1e-11
AND delta_f >= 100 * 2.3e-16 * Rf   AND  delta_u >= 100 * 2.3e-16 * Ru
```

Geometries failing the filter are EXCLUDED and DISCLOSED with their
alphas and deltas in `docs/proofs/1400_rig_visibility.tsv` — they are
counted as UNTESTED, never as negatives. Rationale: below this floor the
taper sliver is below float64 radius resolution (the 1399 dead-lever
finding) and the coefficient dynamic range predicts noise approaching the
locked gate class (the 1398 tier-1 measurement: relative noise
7.7e-7 at alpha 5.9e-12; the filter floor 1.87e-11 extrapolates to
<= 2.4e-7, a 40x margin under the 1e-5 class — the class is retained
UNCHANGED, not relaxed again).

TIERING: within each height stratum, geometries ordered by (-max PASS-row
ratio, then lexicographic (rr, Rf, Ru, eps, epsp)); tier-1 = head of
stratum im = 14.134725; tier-2 = the next 19 of that stratum, then the
first 10 of im = 21.022040, then the first 10 of im = 25.010858;
41 cells total, same full-battery structure as 1398 (tier-1 full, tier-2
light, v3 BADCELL scope for tier-2 integrity failures).

SELECTION ASSERTION (F11: the selection code must reproduce this
audit-derived head or VOID): the pre-run scan of section 5 fixes the
expected tier-1 geometry to
`(Rf, Ru, eps, epsp, rr, im) = (0.1732, 0.08, 0.01, 0.01, 0.99, 14.134725)`
and the expected visible-stratum sizes to 180 / 320 / 320.

## 2. Model = 1398 v3, byte-identical through import

Sections 1.1-1.5 of 1398 v1 (register: nodes s = (0, 1/2, 1, rho),
p_u = (1,1,1,1), p_f = (0,0,0,-1); per-factor G/alpha/TB/Delta/delta/
rIn/rOut/T-with-J-slivers/coeff; taper tau(x) = S((rOut-|x-m|)/(rOut-rIn))
with the Mathlib smoothTransition transcription; degeneracy reductions;
F = g~ * g; A(g) with the v2 GV scale) — ALL VERBATIM, and not
re-typed: the rig imports the same functions that produced 1399's
certified run. Gate classes: G0 exact pinning; GI 1e-9 recompute; GS
1e-30; GT (1e-40 / 1e-10 / 1e-12); GF F(0) > 0 strict + 1e-6 im +
1e-5 npw-24 recompute; GD 1e-6; GR 1e-5; GQ 1e-9; GV tie window
(1+1e-3)*1e-6*S with the v2 formula S = |(log4pi+gamma) reF0| +
|2 reF0| * 0.5*(ln tanh(Rg) - ln tanh(y0/2)), y0 = 1e-3.

## 3. Outputs and acceptance

Log `docs/proofs/1400_rig_run.log` (rename-before-rerun `*.invN.*`);
sentinels `DONE gates=...` and `VERDICT jointWitness=<geo|NONE>
cells=POS:n,NEG:m,TIE:k,BAD:b` (v3 format); artifacts
`docs/proofs/1400_rig_results.json`, `docs/proofs/1400_rig_cells.tsv.gz`,
`docs/proofs/1400_rig_visibility.tsv`; sha256 prints; validity-violation
semantics unchanged (GI/GS/GT/GF/GD/GR/GQ tier-1 FAIL => cells=VOID);
log-not-exit-code.

## 4. Kill scope (VERBATIM from 1398 v1 section 6 via v3 re-lock)

A negative here kills NOTHING (41 more cells out of 820 visible at these
strata and an infinite continuum outside the grid; sup-lower-bound law).
A positive is MODEL evidence only (no harch/hJ1 discharge, no rung 4/5,
no RH). The exclusions (filter-failing geometries) are disclosed and
untested — they are neither negatives nor witnesses.

## 5. Pre-run conditioning audit (rung-2 numbers, computed 2026-09-13; NOT rung-3 digits)

Heads and floors per stratum (alpha_f, alpha_u, delta_f, delta_u at the
max-ratio visible head; visibility counts 180/320/320 of 360/420/420
low-height PASS geometries):

```text
im=14.134725  head (0.1732,0.08,0.01,0.01,0.99):  af=5.5e-8  au=2.3e-10
                                                df=6.1e-13 du=1.45e-14
im=21.022040  head (0.1732,0.05,0.01,0.01,0.99):  af=1.4e-7  au=1.9e-11
                                                df=1.9e-13 du=1.3e-15
im=25.010858  head (0.1732,0.05,0.01,0.01,0.99):  af=2.0e-7  au=2.7e-11
                                                df=7.8e-14 du=1.5e-15
```

Predicted float64 relative noise <= 2.4e-7 (1398-measured 7.7e-7 scaled
linearly in 1/alpha_min); locked classes at 1e-5 — satisfiable by
construction with >= 40x margin (law F12 satisfied: every gate in this
prereg is achievable by this instrument on every geometry it will run).
G0 admissibility: max Rf+Ru in the candidate pool = 0.1732+0.12 = 0.2932
<= log2/2 = 0.34657 (1397 section 1 prime-sum-empty condition holds a
fortiori).

## 6. Protocol and boundary

Law 42: this file is committed BEFORE any A(g) digit of this wave;
revisions cost a new prereg version. The section-5 numbers are Gram-layer
(rung-2) quantities of the same class already committed in the 1393/1394
records and re-checked by the GI gate — no owner value, no convolution,
no sign was computed for this prereg. Acceptance via the sentinel lines.
Environment: WSL2 Ubuntu-24.04, /usr/bin/python3.12, numpy 2.5.3,
mpmath 1.4.1, runner `scripts/run_resource_aware_task.sh --class normal`.
RH not claimed.
