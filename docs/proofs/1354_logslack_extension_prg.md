# Record 1354 (PREREG, FINALIZED) - log-slack rung-II: full-dump re-run, gamma(m) vs the 1/3 target

```text
+---------------------------------------------------------------------+
| PREREGISTRATION - committed BEFORE any 1354 digit (law 42).         |
| Owner ruling 2026-09-12: "开干" -> option A of the draft decision   |
| card funded (rung-II only; rung-I m=768 stays DEFERRED behind this |
| landing). Bands below are LOCKED HERE; no digit may move them.     |
| Estimation class (no FIRE/NO-FIRE). MODEL grade; certifies         |
| nothing; RH NOT claimed. History: drafted 1354_DRAFT, branch-     |
| specified by 1349 s3/s4 (CRITICAL-PINNING).                        |
+---------------------------------------------------------------------+
```

## 1. Question and object

1349 established that at 5 tiers the (alpha, kappa) decomposition is
UNIDENTIFIED, but the floor-vs-MEAN trajectory gamma(m) =
ln(mean/lambda_min)/ln m is measurable and is the actual target of
the uniform-constant program (1348 appendix s2.2). Committed tiers
24/48/96 give gamma_3pt = 0.3355 (already 0.002 ABOVE 1/3 - inside
any knife band). Object here: RE-RUN the deterministic 1348 rungs
m=192/384 (same module chain 1344->1342, same NQ rule 2^18/2^19,
same G9-certified fast path) with the ONLY changes: (a) the FULL
eig_spectrum is dumped (the rig field named by 1348 appendix s4),
giving mean/HS2/participation at the deep tiers; (b) the re-run
doubles as a CROSS-RUN REPRODUCTION gate: lambda_min must match the
committed 1348 digits bit-exactly (constants parsed at runtime from
1348_a1b_results.json - constants are DATA).

## 2. Fidelity architecture

- Anchor block carried verbatim from 1348: G1a (1225 committed
  control, rel < 1e-6), G8c (inv12 ladder 800/1600 cap 6400, band
  UNCHANGED), both aborting, ONCE per process.
- G9-quick per grid (2^18, 2^19): 3 random span vectors (seed
  1354001), verbatim vs fast path, PASS = max rel < 1e-12.
- R gate (reproduction, aborting): lambda_min(192), lambda_min(384)
  vs committed 1348 digits, rel < 5e-13 EACH. A FAIL here is not a
  physics readout - it is a CROSS-RUN NONDETERMINISM DISCOVERY and
  forces ABORTED-UNINFORMATIVE plus a new rig record; no gamma digit
  may be trusted through it.
- Per-rung gates carried with 1348 bands: G3a (rank==3, sv_ratio <
  1e-10, cond > 1e-12), G3b < 1e-9, G5 < 1e-9 on seeds 1342001-02-03,
  G7 (support + square proxy + prime-residue < 1e-9).
- Sign/escalation: any lambda_min <= -1e-8 (impossible if R passes;
  kept for clause symmetry) -> report digit, ESCALATION-NO-BAND.

## 3. Decision statistics and LOCKED bands

Primary statistic: gamma_5pt = log-log LSQ slope of (mean/lambda_min)
over tiers {24,48,96,192,384} (low-tier means parsed at runtime from
1344_a1_results.json eig_spectrum; deep-tier means from THIS run's
dump; lambda digits from this run, R-gated).

```text
  gamma_5pt < 1/3 - 0.02 = 0.313333  =>  TARGET-SURVIVES
        the bare uniform-constant form lambda_min >= c_eps m^(-1/3-eps)
        mean stays admissible on this family.
  0.313333 <= gamma_5pt <= 0.353333  =>  ON-TARGET-KNIFE
        separation grows exactly like the 1/3 power: the log-budget
        reading of 1349 s3 is confirmed; the uniform-constant target
        survives ONLY per-epsilon, never as a bare constant.
  gamma_5pt > 1/3 + 0.02 = 0.353333  =>  TARGET-FALSE
        a bare m^(-1/3-eps) uniform-constant program is FALSE on this
        family at measured depth; the honest aim re-specs at the
        measured exponent: lambda_min >= c_eps m^(-gamma_5pt-eps) mean.
```

Secondary (reported, NO band attached): per-tier gamma(m) at
{192,384}; participation ratio d/(tr2/HS2) extended from 3 to 5
tiers (1348 appendix FLAT check at depth); tr(m) and mean(m)
exponents on 5 tiers; lambda2/lambda1 confirmation vs 1348;
eig_full saved for future reanalysis without re-runs.

If R gate fails at either rung: ABORTED-UNINFORMATIVE, band NOT
issued, digits disclosed in the rig record (law-42 3rd-instance
precedent: disclosure before amendment).

## 4. Budget

Calibration from 1348: 192 rung 19.0 min, 384 rung 127.3 min,
anchors ~4 min => expected total ~2.6 h. CLOCK-ONLY hard stop 4 h
checked at rung entry (never reads a digit); exceeded -> rungs
landed so far reported, label DEPTH-LIMITED (band issued only from
the gamma_5pt actually computable over landed tiers >= 3 rungs
needed beyond the 3 committed low tiers... explicit: if 384 does
not land, NO band is issued; gamma_192 reported as secondary
observation only).

## 5. Artifacts and acceptance

Script docs/proofs/1354_rung2_logslack_probe.py (imports 1344_a1
module -> 1342; zero copied arithmetic); runner
1354_rung2_official_runner.sh (batch 1549; pins numpy==2.5.3 /
mpmath==1.4.1; log 1549_1354_rung2_official.log local+mirror,
gitignored; JSON docs/proofs/1354_rung2_results.json committed).
Acceptance by LOG CONTENT: sentinel "DONE 1354-RUNG2". SMOKE mode
(P_SMOKE=1: rungs {6,8} @2^15, reduced ladder, R gate
skipped-by-design, machinery evidence only).

## 6. Rungs-I deferral and non-claims

m=768 @2^20 (8-13 h, the only current instrument that can break the
(alpha,kappa) identifiability) is explicitly NOT funded by this
prereg; it stays a named follow-up selectable after rung-II lands.
Rails restated: ONE bump family at the gate observable; MODEL
grade; no theorem; no transfer to 2608.13637's compression (1344
s3b); 1353's placement finding is the TIME axis and does not
interact with this SPACE-axis ladder. RH NOT claimed.
