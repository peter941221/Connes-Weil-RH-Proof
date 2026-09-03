# 1104 - mirror-decay decision scan (pre-registration)

Date: 2026-09-03.

Status: PRE-REGISTRATION, committed BEFORE the run. This record is the
INTERNAL decision-grade execution of prompt-006 round-3 task P-1 (the
windowed-mirror decay law) plus the A1 saturation probe. The external
AIs are running a hypothesis-grade copy of the same scan this same day;
this run secures the decision numbers on our own machine first, so
their returns can be adjudicated on arrival. Evidence level NUMERICAL
(diagnostic float64); no certified bound is claimed; no map change is
keyed to any branch below; the windowed-mirror fact stays UNPROMOTED
(record promotion remains user-gated). RH is not claimed.

## 1. The quantities

All cells reuse the committed record-1100b machinery verbatim
(`OrbitGateProbe`, basis_family = legendre, envelope_power = 1,
include_primes = True, include_first_cell = True), imported in-process
(law 26: no reimplementation). V = triple-vanishing nullspace,
orthonormal basis. Per cell (radius a, basis size K, grid n):

```text
A(a)        = top spec(arch|_V)
B(a)        = -min spec(prime|_V)
eps(a)      = B/A - 1            (the mirror mismatch rate)
top_total   = top spec((arch + prime)|_V)
top_counter = top spec((arch - prime)|_V)
```

## 2. The cell table

Main ray: K = 8, grid 4001, a in {0.5, 0.75, 1, 1.5, 2, 3, 4, 5, 6}.
K-stability cells: (a=2, K=16, grid 32001) and (a=4, K=24, grid 32001)
- identical to audit rows 4-5 of 006-mult-audit-raw.log.

## 3. Gates and verdict mapping (literal, law 42)

- REPRO (abort gate, law 26/30/37): the four cells (2,8,4001),
  (4,8,4001), (2,16,32001), (4,24,32001) must reproduce the audit-log
  values of top_arch, min_prime, top_counter to 1e-9 absolute (same
  machine, same environment: in-environment imports are bit-close by
  law 37 precedent). Any miss >= 1e-6 => ABORT, diagnose drift, NO
  verdict issued.
- G1 zero-pinning persistence: |top_total| <= 1e-3 at every cell with
  a >= 1.5. Radii below 1.5 may break pinning (a=1 already showed
  eps = +214% and top_total = -1.8e-4); that is data, not failure.
- G2 mirror decay: eps(a) strictly decreasing over a in {2, 3, 4, 5, 6}
  AND eps(6) inside the pre-registered band [1e-7, 1e-4]. The band
  covers both extrapolations live today: steep power law (p ~ 6.4 from
  the two known points gives eps(6) ~ 2e-6) and exponential (kappa ~
  2.2/doubling gives ~1e-8). Outside the band => ANOMALY branch:
  report raw values, no decay-law conclusion.
- G3 saturation (A1 falsification probe): branch on top_arch(a=6):
  - top_arch(6) < 5.0 => slow-convergence hypothesis SURVIVES (the
    round-3 A1 feed stays standing);
  - top_arch(6) >= 5.0 => FAST saturation, A1 feed is falsified,
    round-4 owes a correction;
  - additionally record whether top_arch(a) is monotone increasing on
    the ray; a plateau strictly below 5.372183 is a THIRD outcome
    (constraint-suppressed saturation: V kills u=0 via the s=1/2
    moment, so the multiplier peak may be unreachable in V) - report
    as candidate finding, not verdict.
- G4 counterfactual sign: top_counter > +0.3 at every radius on the
  ray (the smallest measured value today is +0.37 at a=1).

## 4. What this record cannot do

The scan is diagnostic float64 on finite windows: it prices the mirror
decay and the saturation curve, nothing about the continuum gate. The
windowed-mirror identity itself remains a diagnostic observation until
a pre-registration promotes it (user gate). No certified interval
appears here; the 1101 certifier is untouched.

## 5. Execution

Probe: `1104_mirror_decay_scan_probe.py`, run WSL-side through the
repo `.venv-probe` interpreter, log written Linux-side to
`docs/proofs/1104_mirror_decay_scan.log`. Acceptance = log content
(REPRO gate line + G1..G4 lines + literal VERDICT line), not exit code.

## 6. Post-run addendum (2026-09-03, after the run - NOT a rescoping)

Registered VERDICT: **FAIL** (G1 PASS, G2 PASS, G4 FAIL; G3 =
SLOW-CONVERGENCE-SURVIVES). G4 was falsified exactly at the two
sub-threshold radii a = 0.5 (counter = -0.54, n_visible = 1) and
a = 0.75 (counter = +0.001, n_visible = 3) - the regime G1 itself
exempted as pre-threshold. Law 42 forbids post-hoc rescoping, so the
FAIL stands as recorded; this addendum only RESTRICTS the claim going
forward: G4 holds for a >= 1.5 with min = +1.1045 (at a = 1.5), and
the counterfactual sign regime starts no later than a = 1 (+0.37).
Registration flaw banked as AGENTS 7c law (46): every gate must
inherit the regime scope of the phenomenon it tests.

REPRO gate addendum: worst miss 4.821e-7 against the 1e-9 tolerance -
root-caused to the six-decimal PRINT precision of the audit-log anchors
(5e-7 rounding floor); abort threshold 1e-6 held, the in-environment
rerun is deterministic, so REPRO passes at the registered abort level.

Decision numbers (K=8, grid 4001): eps(a) = +4.99e-3 / +3.96e-4 /
+5.78e-5 / +6.03e-6 / +1.02e-7 at a = 2/3/4/5/6 (strictly monotone;
eps(6) below BOTH registered extrapolations => decay faster than
exponential, ~10^{-a/1.4}); top_total <= 1.3e-6 for a >= 1.5;
top_arch(a=6) = +2.5939 (monotone, ~0.40 per unit a, far below the
5.372183 peak - A1 slow convergence stands); top_counter grows
+0.37 -> +5.19. K-stability cells bit-reproduce the audit.
