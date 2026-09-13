# 1403 v2 — PREREG REVISION: the GI-beta clause-1 class 1e-30 is unsatisfiable against the model's own taper band; re-locked at 1e-15

Date: 2026-09-14. Law 42: 1403 v1 (committed at ae6a12f) is NEVER
edited; this file is the revision instrument. Scope of change: exactly
ONE clause — GI-beta's mp tolerance. Everything else in v1 (model,
cohort, tiering, all other gate classes, sentinels, artifacts, kill
scope, the section-5 conditioning audit) stands re-locked VERBATIM.
Outcome record remains 1404. RH not claimed.

## 1. What happened (inv1, disclosed verbatim)

Invocation 1 ran 30.3 s and went VOID on its own new gate:

```text
[   0.0s] tier-1 (0.99, 14.134725)
[  30.3s] tier-1 A=-1.7343109912e+01 S=1.145e+02 F0=1.190947e+01-6.503791e-19j gdmax=7.39e-14 gi=(2.0e-18,7.4e-14) gates={'G0': 'PASS', 'GI': 'FAIL', 'GS': 'PASS', 'GT': 'PASS', 'GF': 'PASS', 'GD': 'PASS', 'GR': 'PASS', 'GQ': 'PASS'}
[  30.3s] tier-1 extras: A64=-1.734311e+01 A96=-1.734311e+01 A_R=-1.734311e+01 A2v=-6.937244e+01 A_eps0.1=-1.7343109912e+01 A_alpha2=-1.734311e+01 gt=(1.2e-60,6.8e-17,3.4e-17) delta=1.183e-19
VERDICT betaAnchorWitness=NONE cells=VOID
DONE gates=G0:PASS,GI:FAIL,GS:PASS,GT:PASS,GF:PASS,GD:PASS,GR:PASS,GQ:PASS
sha256 docs/proofs/1403_rig_results.json = 748a50d0afddbf0a47c0d137b22e138e84a1792e12f65ed577afaa89f75be515
sha256 docs/proofs/1403_rig_cells.tsv.gz = 2d36e43237d4b62a2c07de984a3aa6a468d4ac7195914bd7038ee0ec3c2da19c
```

## 2. Root cause (the instrument is healthy; the new gate was mine)

Every pre-existing gate passed at once, with margin: GS at the v1-audited
1e-57 scale, GT 1.2e-60/6.8e-17/3.4e-17, GF |Im|~6.5e-19, GD 7.4e-14
(8 orders under class), GR/GQ consistent to 7 digits. The failing
clause-1 value 2.0e-18 is EXACTLY the size the v1 section-5 audit
numbers predict for its own defect: the section-1 pairing derivation
(and hence the intended 1e-30) is a SHARP-window identity, but the
locked model SOLVES the tapered T with band width delta > 0. The
reassembled sharp-kernel pairing of the tapered solution therefore
deviates by the band term:

```text
|L_j - p_j| <= ||c||_1 * delta * (2R + O(delta))
v1 audit worst point (im=14.134725, rr=0.9): delta 1.188e-19,
|c|max 9.673e3 (7 nodes, so ||c||_1 <= 6.8e4), 2R = 0.693
=> bound 6.8e4 * 1.188e-19 * 0.693 = 5.6e-15 > 1e-30 (FAIL PREDICTED)
measured at tier-1: 2.0e-18  (inside the bound; the bound is loose by
~3 orders through cancellation, as expected for a Hermitian sum)
```

This is law F12's fourth documented recurrence — and the sharpest
form yet: the conditioning audit table was written CAREFULLY (it
locked every OLD gate's class from rung-2 numbers) but the ONE newly
invented gate was never itself passed through the audit, although the
two numbers that predict its failure (delta and |c|max) sit in the
table's own columns.

## 3. Re-locked clause (the ONLY change; v1 section 3 GI row is
superseded by this text)

GI-beta, tier-1 only, two clauses:

* clause 1: `max_j |L_j^{mp} - p_j| <= 1e-15`, where L^{mp} is
  reassembled from the solved coefficients via the SHARP conjugated
  kernel exactly as in v1 section 3. Justification: the band-term
  bound of section 2 is <= 5.6e-15 at every cohort point from the v1
  audit table itself (delta <= 1.19e-19, |c|max <= 9.7e3), and the
  measured deviation scales as delta * ||c|| * R, so 1e-15 keeps >= 3
  orders of margin; the errors this gate EXISTS to catch (node-order
  drift between nodes7 and TARGETS, rho index-3 placement, target
  sign/permutation) all enter at O(1) scale — the detection margin is
  now 15 orders, and the gate remains a real convention detector
  (law F11 preserved). Clause-1 PASS must be reported with its
  measured value so 1404 can re-check the delta * ||c|| * R law at
  every battery cell.
* clause 2: UNCHANGED (`|laplace_g(h, s_j) - L_j^{mp}| <= 1e-6`).

Everything else in v1, unchanged. The rig change implementing this is
the constant `GI_MP_TOL = 1e-15` in scripts/run_1403_rig.py (committed
with this file).

## 4. inv1 disposition (law 7j)

inv1 log/results/cells are renamed `*.inv1.*` in the mirror before the
rerun and are NOT copied to the repo; their sentinel text is preserved
verbatim in section 1 above (that is the record). The inv1 numbers
already visible in section 1 (tier-1 A = -1.7343109912e+01 and the
eps=0.1 variant agreeing to ALL printed digits) are MODEL telemetry
of a VOID invocation: reported here for honesty, EXCLUDED from the
1404 census — no cell band is claimed until a VALID invocation.

## 5. Next steps

1. Commit v2 + the one-constant rig change; sync both; rerun
   invocation 2.
2. If VALID: 1404 with the 25-cell census, the F14-beta eps variant,
   the clause-1 band-law verification across cells, and the 1402
   consolidation. If a new failure: new prereg or rig-bug fix per the
   1398 v1->v2->v3 precedent (bug-in-rig vs defect-in-lock triage
   before touching any class).
