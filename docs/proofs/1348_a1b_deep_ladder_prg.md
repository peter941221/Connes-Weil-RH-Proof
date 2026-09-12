# Record 1348 (PREREG) - A1b deep ladder: settle the criticality of alpha at the gate observable

```text
+---------------------------------------------------------------------+
| PREREGISTRATION - committed BEFORE any 1348 digit (law 42).          |
| Owner funding ruling 2026-09-12: "打吧".                             |
| Estimation class (no FIRE/NO-FIRE bands). Model-level; certifies     |
| nothing; RH NOT claimed. A1 (1344/1347) is SPENT and stays spent -  |
| this is a NEW probe reading a DEEPER rung of the same deterministic  |
| object, with the committed A1 digits as anchor points (parsed at     |
| runtime from 1344_a1_results.json - constants are DATA).             |
+---------------------------------------------------------------------+
```

## 1. Question and object

Object: exactly the 1344-A1 / 1342 machinery (bump family Rp=R/(1+1.6/m),
w_b=0.8*spacing, 3m vanishing constraints, SVD nullspace, polarization
Gram, G9-certified sparse fast prime path). New ladder rungs: m in {192,
384}; NQ rule (10*DX <= w_b) computed from the imported module constants:
m=192 -> NQ=2^18 (margin ~1.30x), m=384 -> NQ=2^19 (~1.31x).

Why: A1 measured alpha_3pt = 0.98836 with pairwise slopes RISING
(0.98359 -> 0.99312) toward the branch boundary 1, verdict explicitly
tier-limited (1347 s2 honesty rail 1). The next mainline step (the
uniform-constant route prereg, L4 Fork B family) cannot be written
honestly without knowing whether alpha sits strictly below 1 (polynomial
slack), pins at 1 (harmonic/knife-edge), or crosses (capacity-deep).
This probe buys exactly that bit. Fusion context: the answer is the
capacity-vs-slack discriminator for the arXiv:2608.13637 method-ceiling
question (1344 s3b rails stay in force: species-level map, non-transfer).

## 2. Fidelity architecture (carried + new gates)

- Anchor block carried verbatim from A1: G1a (broken-rule provenance,
  committed 1225 control), G1b (independent-path arch dev < 1e-9), G8c
  (inv12 self-calibrating ladder, official (800,1600,3200) cap 6400,
  band UNCHANGED) - all aborting, ONCE per process.
- G9-quick at EVERY new grid (2^17, 2^18, 2^19): 3 random span vectors,
  verbatim vs fast path, PASS = max rel < 1e-12. A1's full-Gram G9 was
  0.0/0.0; these spot-check the per-grid sparse rebuild.
- NEW G10 (cross-run ladder reproduction): re-run m=96 on the fast path
  at NQ=2^17; lambda_min must match the committed A1 digit
  (parsed from 1344_a1_results.json) with rel < 5e-13. G10 FAIL =>
  ABORTED-UNINFORMATIVE before any 192/384 digit is trusted.
- Per-rung gates carried with A1 bands: G3a (rank==3 exactly, sv_ratio
  < 1e-10, cond > 1e-12), G3b nullspace residual < 1e-9, G5 polarization
  identity on the three committed seeds (1342001-02-03) < 1e-9, G7
  (support in window + square_radius_proxy < log 2 by 1e-12; prime-term
  residue < 1e-9).

## 3. Branch rule (LOCKED HERE, before digits)

Primary statistic: the DEEPEST consecutive log-log slope
  s* = ln(lam(192)/lam(384)) / ln 2   if the 384 rung lands,
  s* = ln(lam(96)/lam(192))  / ln 2   if 384 was budget-killed (s1) or
                                    an escalation intervened;
sign stability (all four/five lambda_min > 0) is a precondition; any
lambda_min <= -1e-8 arms the escalation clause of 1344 s3a (report the
digit, flag ESCALATION-CANDIDATE, NO branch verdict - adjudication moves
to a NEW prereg; the s3a verbatim-recheck note applies with the
amendment that the fast path is now G9-bit-identity-certified and G10
reproduces bit-exactly across runs, so a deep sign flip is read as an
OBJECT fact of the ladder, not path noise).

  s* < 0.99   =>  SUBCRITICAL-CONFIRMED.   alpha strictly below 1 with
                room: the compression carries polynomial positivity
                slack on the gate observable; the uniform-constant
                route prereg is the justified next step.
  0.99 <= s* < 1.00  =>  CRITICAL-PINNING. alpha pins to 1 from below:
                knife-edge (harmonic/log) regime; any limit-exchange
                proof must budget a log per epsilon; the uniform-
                constant prereg is replaced by a fork-B-with-log-slack
                prereg.
  s* >= 1.00  =>  BOUNDARY-CROSSED. deep ladder decays at least m^-1:
                capacity-dead at the gate observable (mirror of 1335/
                1339); fusion reading flips to the WALL side of the
                2608.13637 ceiling question.
  If 384 missing: label the reading DEPTH-LIMITED (4-point ladder);
  same bands on s*; 1348b (m=384 alone, fresh prereg) becomes the named
  resolving measurement.
Secondary statistics reported without any branch attached: full pairwise
slope list (drift direction), 5-point LSQ alpha and c, lambda_2/lambda_1
ratios, doubling-style grid notes, per-rung gate numbers.

## 4. Budget and the wall-time-only kill (no digit peeking)

Machine budget: the run executes 192 first, then 384. After the 192 rung
completes, if ELAPSED WALL TIME > 2.5 h the 384 rung is SKIPPED
(INCOMPLETE-DEPTH disclosure, s* := the 96->192 slope per s3). This kill
reads the CLOCK ONLY - never a lambda digit - so it cannot bias branch
selection. A1 calibration: full official ladder in 1153.7 s (1/12 of its
own estimate); expected here: 192 rung ~30-60 min, 384 rung ~1-4 h at
2^19 fast-path rates; total target <= 6 h wall, hard stop 8 h (script-
internal deadline check at rung boundaries, clock-only).

## 5. Artifacts and acceptance

Script docs/proofs/1348_a1b_deep_ladder_probe.py (imports the 1344_a1
module - which imports 1342 verbatim; no copied arithmetic beyond the
G9-certified fast path); runner docs/proofs/1348_a1b_official_runner.sh
(batch 1548; fidelity pins numpy==2.5.3 / mpmath==1.4.1; log
docs/proofs/1548_1348_a1b_official.log - mirror + local, gitignored per
convention; JSON docs/proofs/1348_a1b_results.json committed).
Acceptance by LOG CONTENT: sentinel "DONE 1348-A1B"; SMOKE mode
(P_SMOKE=1: m in {6,8} @2^15, reduced SMOKE-ONLY G8 ladder (400,800),
G10 skipped-by-design, machinery evidence only).

## 6. Non-claims

No gate verdict; no RH claim; MODEL grade. The slope statistics describe
ONE bump ladder at the gate observable; they do not test other test
families and do not transfer as theorems to 2608.13637's compression
(1344 s3b rails, restated). If SUBCRITICAL: nothing is proved toward the
gate - it licenses writing the NEXT prereg, nothing more.
