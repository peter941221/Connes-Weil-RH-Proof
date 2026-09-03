# 1106 - in-house F-pack completion (pre-registration)

Date: 2026-09-03.

Status: PRE-REGISTRATION, committed BEFORE the run. External AI-1
delivered round-3 experiments F.4 (constraint ablation), F.5 (weight
coupling), F.6 (pure-compression asymptotic) as NUMBERS ONLY - the five
runner sources were not pasted (delivery gap, ledger 2.6). The task
specifications are complete, and the shared reference implementation
(bundle `f0.py`, anchor-verified in record 1105) supports all three
natively (`drop_moments`, `scale`, empty prime override). Per the
no-more-external directive (2026-09-03), this record rebuilds and runs
the three experiments IN-HOUSE. Criteria below are the pre-registrations
already on the books (ledger 2.6 rows 6/7/8; external round-3 F.4-F.6).
Evidence level NUMERICAL (diagnostic float64); RH not claimed; no map
change keyed to any branch.

## 1. Cells and criteria (literal, law 42)

All cells: bundle `f0`, grid 4001, legendre, envelope_power=1.

- F.4 ablation, a=2, K=8: baseline (codim 3) + six subsets of
  {0, 1/2, 1} dropped. Registered prediction (external round-2, row 6):
  (i) the single-drop s=1/2 jump is the LARGEST single jump;
  (ii) dropping BOTH s=0 and s=1 (keeping 1/2) leaves the gate pinned,
  |top_total| <= 1e-3; (iii) dropping everything is O(1)-large.
  External reference values: +0.0045 / +2.96 / ~0 / +0.098 / +9.22.
- F.5 weight coupling, a in {2, 4}, K=8: delta in
  {-0.1, -0.01, -0.001, 0, +0.001, +0.01, +0.1}, scale = 1 + delta on
  the prime matrix. Registered prediction (row 7): slope/-A OUTSIDE the
  naive band [0.8, 1.2] (external measured 0.66/0.73); the crossing
  delta* sits at noise scale (|delta*| <= 1e-3), i.e. the pinning does
  NOT sit on the weight boundary with an O(1) margin.
- F.6 pure compression, a in {1, 2, 4, 6, 10}, K=8, NO prime term
  (shifts=[], weights=[]): top_arch on V (constraints kept) and on the
  full basis (drop_moments=(0, 0.5, 1)). Registered expectation
  (row 8): both monotone increasing toward the multiplier peak
  5.372183; at a=10, V-value near +3.79 and full-space value near
  +5.06 (tolerance 1e-2 against the external table - same shared f0);
  the V-vs-full gap is the price of the three constraints and shrinks
  only slowly (their 1/a law).

## 2. Verdict mapping

- F.4 PASS iff (i) and (ii) hold (iii is reported, not gated - their
  +9.22 is grid/basis dependent at codim 0).
- F.5 PASS iff both ratios lie outside [0.8, 1.2] AND |delta*| <= 1e-3
  at both radii.
- F.6 PASS iff monotone growth at both columns and the a=10 pair lands
  within 1e-2 of the external reference (the shared implementation
  makes this a digit-level replication test, not a fit).
- ABORT: f0 anchor drift > 2e-3 (the bundle must stay pinned to the
  committed F.1 anchors).

## 3. What this record buys

(i) "the multiplier set shrinks to ONE (the s=1/2 constraint)" becomes
an internal decision-grade fact iff F.4 passes - this halves-plus the
E0 certificate object count and is input to the SOS re-registration
(next record); (ii) F.5 fixes the slope mechanism numerically (top
state = Z-zero direction, per P-6); (iii) F.6 anchors the
pure-compression asymptotic on our machine so the saturation curve
needs no external feed. Execution: `1106_fpack_completion_probe.py`,
WSL-side through `.venv-probe`, log local (gitignored).
