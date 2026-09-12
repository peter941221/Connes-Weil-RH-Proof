# Record 1354 (DRAFT - NOT YET PREREGISTERED) - log-slack extension of the A1 ladder

```text
+---------------------------------------------------------------------+
| DRAFT. Bands below are PROPOSED, not locked: law 42 engages only    |
| at funding (this file is committed WITHOUT any execution intent;    |
| the locked prereg is a FINALIZE+commit step at owner "打").         |
| No digits exist for anything measured here beyond the committed     |
| 24/48/96/192/384 ladder (1347/1349). MODEL; certifies nothing;     |
| RH NOT claimed.                                                     |
+---------------------------------------------------------------------+
```

## 1. Why this probe exists (branch-specified by 1349 s3/s4)

1349 measured CRITICAL-PINNING and one hard negative: the
(alpha, kappa) decomposition is UNIDENTIFIED at 5 tiers - power-law
alpha 0.9927 and log-corrected a=1.0197/k=-0.12 fit the same digits.
The knife-edge question therefore cannot be pushed by re-fitting
existing data; it needs either (I) one more LAMBDA tier (m=768) to
break the identifiability, or (II) the MEAN of the Gram at the deep
tiers (full spectrum dump - the rig named by 1348 appendix s4),
which tests a DIFFERENT inequality: the floor-vs-mean trajectory
gamma(m) = ln(mean/lam_min)/ln m against the uniform-constant target.
(I) is the 8-12 h rung; (II) is a 2.2 h re-run. They are not
redundant: (II) measures tr/d, which NO spectrum-free fit can.

## 2. Recommended first funding: rung-II (cheap, tests the real target)

Object: rerun m=384 at NQ=2^19 on the G9-certified fast path,
identical seeds, with the ONLY changes:
  - dump FULL eig_spectrum (field `eig_full`, the 1348 s4 rig note);
  - compute gamma(384) = ln(mean_384 / lam_min_384) / ln 384 and
    (same dump path at m=192, ~19 min) gamma(192).
Anchors: G1a/G8c carried; G9q per grid; **G10 doubles here** -
lam_min must match 1348's +1.968753894733601e-04 bit-exactly
(rel < 5e-13) since object and seeds are identical; mismatch =
ABORTED-UNINFORMATIVE (a cross-run nondeterminism discovery, which
would itself be the story).
Proposed decision statistic (band LOCKED AT FUNDING, not here):
  gamma trajectory: mean/lam_min ratios 1.97/2.53/3.14 at tiers
  {24,48,96} (1348 appendix s2 table) => gamma_3pt exponent 0.3355;
  extended by gamma(192), gamma(384) from the new dumps. Band proposal:
    gamma_exponent(new pair) < 1/3 - 0.02  => uniform-constant target m^(-1/3-eps) SURVIVES
    within [1/3-0.02, 1/3+0.02]           => ON-TARGET knife edge (log-budget exactly the slack)
    > 1/3 + 0.02                          => bare uniform-constant FALSE on this family;
                                             floor-vs-mean needs a super-1/3 exponent
Wall time: ~2.5 h total. Budget kill: clock-only 3.5 h hard stop.

## 3. Deferred: rung-I (m=768) and the (alpha,kappa) identifiability

If rung-II lands ON-TARGET or FALSE, the log-correction question
gets one sharper instrument: 6th lambda tier m=768 @ NQ=2^20.
Calibration from 1349: rung cost scaled ~6.7x per doubling
(19 -> 127 min); m=768 projected 8-13 h - a full-day run, own
prereg, only proposed AFTER rung-II's outcome (measurement order
keeps the cheap discriminator first; owner may also fund I directly).
Fit to be locked there: the 3-param joint model on 6 tiers with
proposed bands kappa in [-0.05,0.05] PURE-CRITICAL / outside =
log-slack sign; crossing guard s(384->768) >= 1.00 overrides.

## 4. What this probe CANNOT say (rails, restated)

Same rails as 1348/1349: ONE bump family at the gate observable; no
theorem; no transfer to 2608.13637's compression; 1353's placement
finding (time axis) does not interact with this space-axis ladder.
If uniform-constant reads FALSE: the 1348 appendix s2.2 target
formula dies, and the honest space-axis target becomes
lambda_min >= c_eps m^(-gamma_inf-eps) mean with gamma_5pt measured -
a WEAKER target that a future floor proof must aim at, still a
prerequisite inventory item, not a proof.

## 5. Owner decision card

```text
 option A (recommended): fund rung-II now (~2.5 h)  -> 1354 finalize+commit (bands locked) -> official batch 1549
 option B: fund rung-II + rung-I (~11-16 h total)   -> two preregs, II first
 option C: park; the 1351 brick ruling + A3 screen (2408.15135) proceed as the cheap lanes
 option D: decline all; mainline idles at 1349
```
