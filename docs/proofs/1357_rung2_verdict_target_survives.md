# Record 1357 (VERDICT) - 1354 rung-II: gamma_5pt = 0.288332, TARGET-SURVIVES

```text
+---------------------------------------------------------------------+
| Batch 1549 accepted by sentinel "DONE 1354-RUNG2  (OFFICIAL,        |
| 8371.3s, MODEL, certifies nothing, RH NOT claimed)" in log          |
| 1549_1354_rung2_official.log (log-not-exit-code).                   |
| Prereg: 1354_logslack_extension_prg.md, bands + R gate +            |
| 4h clock-only stop locked at finalize (3965f87) BEFORE any digit    |
| (law-42). Data: 1354_rung2_results.json (committed). MODEL grade;   |
| certifies nothing about zeta; RH NOT claimed.                       |
+---------------------------------------------------------------------+
```

## 1. The locked adjudication

Band edges were pre-locked at 1/3 -+ 0.02 on the 5-tier least-squares
gamma_5pt = slope of ln(mean/lambda_min) against ln m over tiers
24/48/96/192/384:

| quantity | value | band |
|---|---|---|
| gamma_5pt | **0.28833155275942074** | < 0.313333 |
| issued band | **TARGET-SURVIVES** | prereg s3 first limb |

Consequence (locked wording): the uniform-constant capacity target of
the 1348 appendix, lambda_min >= c * m^(-1/3 - eps) * mean, is NOT
falsified at measured tiers; the "capacity-dead" branch of the 1344
map did not fire. Margin to the knife edge: 0.025 (1.25x the band
half-width).

## 2. Fidelity rollup (all committed-source-checked)

| gate | reading | status |
|---|---|---|
| G1a provenance | control +1.895767602e-02 vs committed 0.01895768, rel 2.10e-07 | PASS |
| G8 control | geom +1.302073921e-01 vs spect(800) +1.302071817e-01, drift 0.00e+00 (ladder 800/1600/3200) | PASS |
| G9q 2^18 / 2^19 | worst rel 0.00e+00 (sparse fast prime path, bit-exact vs dense) | PASS |
| R m=192 | +3.928222862e-04 vs committed 1348, rel 0.0 | PASS bit-exact |
| R m=384 | +1.968753895e-04 vs committed 1348, rel 0.0 | PASS bit-exact |
| per-rung | G3a sv_ratio 0.0 / cond ~1.9e-03 / rank 3/3, G3b res < 6e-18, G5 < 5.5e-15, G7 (prime res < 3.5e-17) | all T |
| clock | wall 8371.3 s vs 4 h stop measured from rung entry | 23 min inside |
| escalation | false | - |

R-gate note: 1549 re-ran the SAME (seed, parameters) as 1548 from a
fresh process and reproduced both deep-tier lambda_min at rel 0.0.
Cross-run determinism of the full float path is now witnessed twice
(1349 G10 + this); no nondeterminism branch entered.

## 3. The trajectory, honestly

per-tier gamma(m) = ln(mean/lambda_min)/ln m:

```text
  m        24       48       96      192      384
  gamma  0.2134   0.2402   0.2505   0.2519   0.2487
  part.  1.0295   1.0290   1.0253   1.0209   1.0170
```

Three observations (none adjudicated; all MODEL):

1. **Plateau + non-monotonicity.** The per-tier ratio peaked at 192
   and DECLINED at 384 (0.2519 -> 0.2487). The last local slope
   (between the two deepest tiers) is ~0.23. The floor-vs-mean decay
   has been BELOW the 1/3 target since tier ~96 and is drifting
   AWAY from it on deep tiers. The 1348 appendix three-tier number
   gamma_3pt = 0.3355 sat just inside the knife edge; five tiers
   pulled it to 0.2883 - the deep tiers flatten the fit. A sixth
   point (rung-I m=768) is now forecast to move gamma_5pt by <~0.01:
   the gamma question is DECIDED with margin at current tiers.
2. **Cross-consistency with the 1349 alpha reading.** mean decays
   mean(192)/mean(384) = 1.708 ~ m^-0.77; with s* = 0.99659 (the
   lambda_min-vs-m exponent) this predicts gamma ~ 0.9966 - 0.77 ~
   0.23, matching the observed plateau 0.249-0.252 to first order.
   The two axes (pairwise alpha pinning; floor-vs-mean gamma) are
   readings of the SAME digits and are mutually consistent - no
   hidden tension inside the capacity story.
3. **Participation drift.** 1.0295 -> 1.0170: still ~1 (the floor is
   still essentially one direction at the bottom edge), now mildly
   MORE concentrated on deep tiers. Extends the 1349 self-similarity
   reading; no qualitative change claimed.

What this does NOT touch: the 1349 PRE-LOCKED consequence lives on
the ALPHA axis (s* ~ 0.9966 in [0.99,1.00), critical-pinning,
log-per-epsilon budgeting for limit-exchange proofs). TARGET-SURVIVES
here says the FLOOR-vs-MEAN limb is comfortable; it does not retire
the log-slack budget, and it says nothing about (alpha, kappa)
identifiability (the 1349 secondary finding stands).

## 4. Portfolio consequence (probe ledger)

Probes 1342 (B0a) / 1344-A1 / 1348-A1B / 1354-RUNG2: all SPENT, all
accepted, collectively painting the capacity picture as: pairwise
alpha pins below 1 with geometric drift contraction; floor-vs-mean
gamma ~0.25 plateau well inside the m^-1/3 target; floor a band of
one-ish directions. The capacity branch of 1344 s3 (A1 ladder) is
CLOSED at MODEL level with no live contradiction. Remaining funded
artifacts this session: brick B1+B4 green (1356 s4/s6), A3 screens
1352+1355, and the N1/H1/H2 specs with the 1353 two-limb correction.

## 5. Owner card (unchanged menu, new evidence weights)

| option | cost | what it would add after 1357 |
|---|---|---|
| A. rung-I m=768 @ NQ 2^20 | 8-13 h | gamma: ~nothing (decided, margin 0.025, forecast shift <0.01); the remaining value is the (alpha,kappa) identifiability axis only |
| B. B2/B3 windowwise brick | C6/NLLE-v2 science | the actual gap (1353): not a run, a research program; needs its own charter |
| C. 1355 deeper pass (Yakaboylu) | generic refereeing | tells how close a third-party B-species attempt gets to the wall |
| D. #9 thermometer | constant-parse | turns f* into f*(A); cheapest named next artifact, still unfunded |
| E. stop / harvest only | 0 | H1/H2 specs + green brick + closed capacity map are already deliverables |

My read, stated as recommendation not fact: **A is downgraded** by
this verdict (its headline question just resolved with margin);
**D** is now the highest value-per-hour remaining inside the house
machinery; B/C/E are direction calls, not compute calls.

RH NOT claimed anywhere; every number above is MODEL-grade numerics
on the projected Gram, and the only machine-checked theorems in the
tower remain B0b (d767a1d) and the 1356 brick (B1+B4).
