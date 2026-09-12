# Record 1349 (VERDICT) - A1b deep ladder: CRITICAL-PINNING; and the (alpha,kappa) unresolvability

```text
+---------------------------------------------------------------------+
| VERDICT record for batch 1548 (docs/proofs/1548_1348_a1b_official.  |
| log, mirror + local; log gitignored per repo convention). ACCEPTED  |
| by LOG CONTENT: sentinel "DONE 1348-A1B (OFFICIAL, 8779.7s, MODEL,  |
| certifies nothing, RH NOT claimed)" - exit code not trusted (law).  |
| Branch = pre-locked 1348_prg s3 reading of the script's own         |
| READOUT line. Numbering: 1349 was reserved for this by the 1353     |
| renumber (1353 s8). MODEL grade; certifies nothing; RH NOT claimed. |
+---------------------------------------------------------------------+
```

## 1. Digits (verbatim from 1348_a1b_results.json, committed with this record)

```text
 m    NQ       lambda_min      lambda_2      rank/resid/G5/prime-res    gates    rung-time
 192  2^18     +3.928222862e-04  +4.891119e-04  3/3  5.71e-18  5.2e-15  1.3e-16  all T   19.0 min
 384  2^19     +1.968753895e-04  +2.452425e-04  3/3  3.79e-18  5.4e-15  3.4e-17  all T   127.3 min
 a1 anchors (parsed at runtime, constants=DATA):
  24  +3.0832438870712037e-03   48  +1.559255371407266e-03   96  +7.833531534466537e-04
 pairwise slopes: 0.9835918  0.9931225  0.9957861  0.9965940
 s* (192->384) = 0.9965940036101494   drift (last-prev) = +0.0008079308108801531
 5-pt LSQ (power law): alpha 0.9927097, c 0.0725561
 BRANCH (prereg s3): CRITICAL-PINNING   STATUS: COMPLETE (CRITICAL-PINNING)
 budget_kill_384: False   escalation: unarmed (all four rungs positive)
```

## 2. Fidelity rollup

G1a PASS (rel 2.10e-07, carried), G8c PASS (gap 2.10e-07, drift 0.0,
ladder 800/1600), G9-quick at ALL THREE new grids (2^17/2^18/2^19)
worst rel 0.00e+00 (bit-exact), **G10 cross-run m=96 rel 0.00e+00**
- the deep ladder is anchored bit-exactly onto the committed A1
digit. Per-rung gates G3a/G3b/G5/G7 all TRUE. The whole acceptance
architecture purchased before launch did its job: no escalation, no
budget kill, no abort.

## 3. What CRITICAL-PINNING says (band reading, locked pre-digit)

The deepest slope sits in [0.99, 1.00): alpha pins to 1 FROM BELOW.
The ladder is knife-edge, not slack: per the pre-locked consequence,
**any limit-exchange proof at this observable must budget a log per
epsilon, and the uniform-constant prereg is replaced by a
fork-B-with-log-slack prereg.** The drift sequence
(+0.00953, +0.00266, +0.00081) contracts geometrically (ratios
0.28/0.30); the geometric tail extrapolates the slope-limit to
~0.9969 - on measured tiers this observable PINS, it does not cross.

## 4. Secondary statistics (free reanalysis of committed JSON; NO branch attached)

(a) MODEL-IDENTIFICATION FAILURE, not a number: pure power law fits
alpha = 0.99271; adding ONE log-correction parameter
(ln lam = c - a*ln m - k*ln ln m) re-fits the SAME five digits as
a = 1.01970 +/- 0.00488, k = -0.11989 +/- 0.02160. The (alpha, kappa)
decomposition is UNRESOLVED at this depth - what the ladder pins is
the APPROACH of the slope to 1, not the slack's functional form.
(b) Bottom-band self-similarity: lam2/lam1 = 1.24512 (192) ->
1.24567 (384); lam6/lam1 = 2.04885 -> 2.05224 (both shift <= 0.16%
under doubling). The floor is not one special direction - the whole
low band scales together. Consistent with the 1348-appendix FLAT
spectrum reading, extended to the new tiers at the bottom edge.

## 5. Fusion-axis reading (1344 s3b rails restated, MODEL, non-transfer)

On the slack-vs-wall axis for the arXiv:2608.13637 ceiling question,
CRITICAL-PINNING is the knife-edge: neither "polynomial slack proves
capacity fine" nor "alpha >= 1 mirror-of-1339 wall" is licensed. What
IS licensed: the honest next target is NOT the bare uniform constant
lambda_min >= c_eps m^(-1/3-eps) mean (s4a says a pure power-law
target is not identifiable here) but a floor-vs-mean inequality with
EXPLICIT log slack, or nothing.

## 6. Portfolio consequences

- A1b CLOSED + SPENT (probes: 1342, 1344-A1, 1348-A1B).
- Next space-axis prereg DRAFTED per branch: 1354 (log-slack
  extension), FUNDED-BY-OWNER-ONLY; execution not started.
- A3 queue moves UP per 1353 s9.3 (arXiv:2408.15135, paper-only
  species screen) - separate lane, cheap.
- N1: unchanged PENDING, colder since 1353.
- 1351 brick decision (B1+B4 green core, C6-free, 1353-confirmed)
  remains the other open owner-ruling item.

## 7. Artifacts

docs/proofs/1348_a1b_deep_ladder_probe.py / ..._runner.sh (828c445),
1348_a1b_results.json (committed with this record), local+mirror log
1548_1348_a1b_official.log (gitignored), this record, 1354 draft.

## 8. Next steps

1. Owner ruling on 1354 (recommended first rung: m=384 re-run with
   full spectrum dump, ~2.2 h, doubles as G10 re-anchor).
2. Owner ruling on 1351 brick build funding (B1+B4).
3. Optional paper-only: A3 species screen of 2408.15135.
