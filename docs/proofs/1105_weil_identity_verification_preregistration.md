# 1105 - Weil-identity matrix verification (pre-registration)

Date: 2026-09-03.

Status: PRE-REGISTRATION, committed BEFORE the run. External AI-1
(prompt 006, round 3) returned a decision experiment P-6 claiming the
EXACT operator identity on the window space V:

```text
M := A + P = kappa * Z,   kappa ~ -1,
Z_ij = 2 * sum_{gamma_j > 0} Re( v_i(gamma_j) * conj(v_j(gamma_j)) ),
v_i(gamma) = integral f_i(t) exp(i gamma t) dt   (Simpson),
```

with Z the nontrivial-zero Gram operator (60 zeros + density tail),
reported residuals 1.7e-6 / 6.9e-7 / 6.3e-6 relative to ||A|| at
(2,8) / (4,8) / (2,16), plus the P-2 randomized-control verdict
(15/15 broken, arithmetic coherence). External numbers are
HYPOTHESIS-grade until re-run here (prompt/README rule 3). This record
is that re-run. RH is not claimed; evidence level NUMERICAL
(diagnostic float64); no map change keyed to any branch.

## 1. Verbatim discipline (law 26 family)

The three code artifacts are EXTRACTED VERBATIM from the round-3
transcript (awk fence extraction, zero manual transcription):

```text
docs/proofs/1105_weil_identity_bundle/f0.py        (= our F.0 skeleton,
                                                      as shipped to them)
docs/proofs/1105_weil_identity_bundle/p6_weil.py   (their P-6 runner)
docs/proofs/1105_weil_identity_bundle/f3_random.py (their P-2 runner)
```

Only the assertion layer (`gate.py`) is ours. Their p6_weil.py is run
both as-is (log capture) and through gate.py which recomputes the
decision numbers via their own `zero_gram` construction.

## 2. Gates and verdict mapping (literal, law 42)

- G-A identity residuals: ||M - kappa Z|| / ||A|| <= 1e-4 at ALL three
  cells (2,8), (4,8), (2,16) - their own registered criterion; and
  kappa in [-1.001, -0.999] at (2,8) and (2,16). Expected values
  1.7e-6 / 6.9e-7 / 6.3e-6 (one decade of slack is PASS, not a
  re-derivation).
- G-B pin-depth mechanism: at (2,8), |top(M) - (-lambda_min(Z))| <=
  1e-6; at (4,8) and (2,16) BOTH |top(M)| and |lambda_min(Z)| <= 1e-5
  (noise regime - sign unresolvable by design, their claim is exactly
  that the true value sits below the quadrature floor).
- G-C P-2 replication: a=4, K=8, seeds 1-5, three variants (perm /
  uniform / random-weights): all 15 top(arch+prime_ctrl) agree with
  their reported values to +-5e-3 AND all 15 >= +0.95 (their
  pre-registered break threshold). Reported reference values:
  perm {+1.546, +1.099, +1.568, +1.447, +1.260};
  unif {+1.751, +3.254, +0.953, +0.982, +8.273};
  rndw {+1.767, +1.860, +1.519, +1.505, +2.092}.
- G-D mechanism column: at (2,8) the leakage ratio eps*A/(2 m1) in
  [0.8, 2.0] (they report 1.20), m1 = |FT of A-top eigenvector at
  gamma_1|^2.
- ABORT: any import/setup failure, or f0 anchor drift > 2e-3 against
  our committed F.1 anchors (the bundle's f0.py must first reproduce
  tops(2.0,8)/tops(4.0,8) exactly as shipped).

## 3. What a PASS buys (and what it does not)

PASS upgrades the identity to an INTERNAL numerical fact
(decision-grade float64) and authorizes re-registering E0 as an
SOS-identity certificate (their Q-F1.3 proposal) - but only after a
separate pre-registration; this record books no program change by
itself. FAIL (residual O(1)) kills the Weil-identity reading and the
mirror stays an open diagnostic. Neither branch touches the committed
gate, map, or 1101 certifier. The Z-tail discretization (60 zeros +
trapezoid density tail to u=400) is THEIR construction, re-run as-is;
if residuals pass only WITH the tail and fail without it, both numbers
are logged (tail-dependence is part of the verdict line).

## 4. Execution

Bundle dir `docs/proofs/1105_weil_identity_bundle/`, run WSL-side
through the repo `.venv-probe` interpreter (mpmath for `zetazero`);
log written Linux-side to `1105_weil_identity_bundle/run.log`.
Acceptance = log content (G-A..G-D lines + literal VERDICT line),
not exit code.
