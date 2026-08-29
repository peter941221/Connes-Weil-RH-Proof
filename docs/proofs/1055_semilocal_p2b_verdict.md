# 1055 - Semilocal P2b verdict: the prolate gate dies at the precision wall

Date: 2026-08-29. Follows 1053 and 1054.

Status:

```text
DEAD: the semilocal prolate asymptotic family (1053 section 1, third block)
      is closed as a feasible next-theorem target.

REASON: P2b is unprovable at the current state of the literature (no
        self-adjoint realization, no cancellation mechanism, generic
        obstruction exact), AND unfalsifiable by its promised numerical
        go/no-go test (the observable has no fixed-precision decodable
        content at any lambda where the asymptotic question is nontrivial).
        The pre-registered first gate therefore does not exist.

RH is not claimed. The landed 1050 RH-equivalence of the coverage root is
untouched; only this candidate construction is eliminated.
```

## 1. What Was to Be Decided

Proof 1054 section 5 made P2b the mandatory first coefficient-complete test
for the surviving 1053 candidate: for the actual Gamma/Meixner semilocal
prolate family,

```text
P2b.  lim_(lambda -> infinity) Readback_1cross(
        1/2 E_lambda''(0) - 1/2 delta_(cos(2 L s)) E_lambda(0) ) = 0.
```

`docs/proofs/1055_semilocal_p2b_probe.py` pins the model to primary sources
(CCM24 arXiv:2310.18423, Theorem 3.1 / section 3.4: Jacobi coefficients
`a_n = sqrt((n+1/2)(n+1))`, diagonal `0`; formal `W = -D^2 + 2 pi lambda^2
(4N+1) - 1/4`, equation (5); Euler factor `w_a = |1 - a e^{i L s}|^{-2}`) and
implements the energy `E = || Pi_- J_a Pi_+ ||_HS^2` with the deformed cyclic
pair realized as the Lanczos tridiagonal of the exact `J0` started at
`psi = sqrt(w(J0)) e_0`. The direct channel is the FIRST variation along
`exp(2 t cos(2 L s)) dm`, per 1054 (1.2)-(1.3) and (3.3).

The measurement produced three separable claims.

## 2. Claim A: No Generic Algebraic Cancellation (exact, reproduced)

The harness reproduces the 1054 three-point counterexample end to end:

```text
A  control: pipeline Delta=-0.354698 closed-form=-0.354698 -> PASS
```

That is, `Delta = E_x(2/3) * (-8/27) + E_xx(2/3) * (16/81) < 0` with the
closed-form values `E_x = 16(13/3)/(59/3)^{3/2}`,
`E_xx = -3104/(3 (59/3)^{5/2})`. A correct first harmonic plus Euler-log
analyticity does not produce the `p^2` coefficient; the iterated
first-harmonic second response survives in any honest finite model. This was
1054's own exact result; the reproduction confirms the probe's conventions
(no sign or channel mixups) before anything numerical is read.

No mechanism for a special cancellation exists either: the generalized Toda
route is blocked for this family, because Ong--Remling requires a bounded
Jacobi operator (https://arxiv.org/abs/1801.03053) while the archimedean
coefficients grow like `n`, and the 2026 unbounded paper assumes `O(|n|^alpha)`
with `alpha < 1` and the standard flow
(https://arxiv.org/abs/2604.05434); see 1054 section 4.

## 3. Claim B: The Numerical Gate Is Infeasible at Fixed Precision

This is the decisive new finding, and it kills the opposite hope: that a
computation could fail the family empirically.

Mechanism. Any float64 evaluation of `E_lambda''(0)` needs the deformed
Jacobi coefficients to the prolate band depth `K ~ 4 pi lambda^2` (the
coordinates whose `W = -J^2 + 8 pi lambda^2 N + ...` diagonal crosses zero).
Recovering coefficients of the cyclic pair `(J0, psi)` from a floating
approximation of `psi` amplifies the deep-coordinate noise `eps` by the
Krylov product

```text
prod_(j<K) a_j = sqrt(Gamma(K+1/2) Gamma(K+1))  ~  K! / K^(1/4).
```

At double precision the coefficient floor `eps * K! / K^(1/4)` passes the
signal scale `~ K` at depth `K* ~ 15-20` -- while the band `4 pi lambda^2`
exceeds 15 already at `lambda ~ 1.1` and grows without bound. The `lambda ->
infinity` limit that P2b quantifies over is precisely the regime in which the
observable is not a computable function of any fixed-precision input.

Measurement 1: the amplifier, step by step. Reconstructing the BASE cyclic
vector through the exact eigenbasis of `J0` at `M = 200` perturbs it by
`1.1e-15`. The `r`-component of the Lanczos recurrence in coordinates `> k+1`
is identically zero in exact arithmetic; its norm grows multiplicatively
(`x30` per step at this size):

```text
    k:      0       1       2       3       4       5       6       7       8
  tail: 2.8e-15 8.4e-14 1.3e-12 1.4e-11 1.1e-10 7.1e-10 3.6e-09 1.6e-08 5.9e-08
```

At larger `M` the same 1e-15-level start error destroys the recurrence by
depth 5-6: `a_5 = 1070`, `a_6 = 3252` at `M = 1952` -- values impossible for
a Jacobi matrix of that truncation (`||J|| <= 2 sqrt(2*1952) ~ 88`). Full
reorthogonalization (done twice) cannot prevent it: this is the forward
instability of the moment problem itself, not a scheme defect.

Measurement 2: the base energy of the same measure, two representations.
`g = 1` means the exact vector `e_0` and its spectral reconstruction denote
the SAME cyclic pair, so the base energy must be one number. It is not:

```text
  lam    band   E0_exact    dE0/E0
  0.50      4   5.66e+01    0.80
  0.70      7   1.15e+02    0.86
  0.90     11   1.81e+02    0.39
  1.10     16   2.48e+02    0.94
  6.00    453   7.45e+03    0.43
 12.00   1810   6.85e+04    2.68
```

The very quantity the finite differences differentiate is already 40-270%
amplifier output at every tested `lambda` -- including `lambda = 0.5`, where
the band is four coordinates deep. There is no "safe low-lambda" region.

Consequence for earlier readings. The interim table produced by the first
version of this probe (`ratio |Delta|/|d_dot| ~ 1e3-1e8`, "no decay in
lambda") is WITHDRAWN as physical evidence: its inputs are past the wall.
The ratios remain in `p2b_probe_results.json` labelled by the measured
`dE0` blowup, exactly so that nobody re-reads them as a measurement of the
iterated channel. Raising precision is not an escape: the depth budget grows
only logarithmically in the digit count (extra digits `D` buy `K* ~ 2D /
log10 K*`), so 100 extra digits reach depth ~ 40 (`lambda ~ 1.8`) and 1000
digits depth ~ 400 (`lambda ~ 5.6`) -- logarithmic sludge against an
infinite target. A `lambda -> infinity` cancellation can therefore only ever
be decided by analysis, which is Claim C's missing part.

## 4. Claim C: There Is No Functional to Cancel

P2b as written quantifies over `E_lambda` after "the same trace smoothing
and one-crossing readback used in P2" (1054 section 5). That object does not
exist in the literature:

```text
CCM24 (2310.18423):    formal expression (5), cyclic pairs, Sonin stability.
                       No self-adjoint W_(lambda,S) realization, no
                       cross-spectral HS trace theorem; "candidate" language
                       with delicate domain.
CC19 (1910.14368):     semilocal positivity is Conjecture 4.1; the simple
                       positive-projection attempt is shown to fail.
q-series 2024          moments and Jacobi coefficients for S = {infinity, p}
(2403.01247):          only; proves no P2b-type spectral-projection trace
                       statement.
```

1054 section 5 says explicitly that the kill test becomes meaningful only
after P0/P1 are supplied. They are not, and this record adds that they cannot
be approximated by a numerically observable gate either (Claim B). The probe's
truncated Lanczos matrices were the best available honest finite realization;
their observable is provably not float-stable.

## 5. Verdict

```text
P2b: neither provable (no realization, no mechanism, exact generic
     obstruction) nor refutable by the pre-registered test (no fixed-
     precision evaluation of the gate exists at meaningful scale).
     The gate does not exist.

Semilocal prolate asymptotic family: CLOSED as a next-theorem target.
     Under 1053 section 6 the route may not receive a conditional Lean
     producer; under this record it may not receive a numerical screening
     step either, because the first coefficient-complete checkpoint of
     1053 section 3 / 1054 section 5 is unstateable without P0/P1 and
     unobservable with them, until a theorem replaces the measurement.
```

The verdict is a DEAD for the program as designed ("the only remaining
go-shaped construction"), not a theorem that `Delta_lambda != 0`: the
mathematical statement `P2b` concerns an object nobody has defined, and the
definition is exactly the RH-level open analysis 1053 section 5 lists as
missing.

Revival conditions (all three, in this order):

1. a proved self-adjoint realization `W_(lambda,S)` with usable spectral
   projections (P0), and Hilbert--Schmidt / trace legality of
   `Pi_- C_S(g) Pi_+` on the explicit-formula test (P1);
2. an analytic (not computational) proof or disproof of the 1054 (1.3)
   one-crossing limit -- e.g. a Ward/Toda-type identity for the prolate
   grading, or an exact asymptotic coefficient theorem for the
   Gamma-weight-times-Euler-factor orthogonal polynomials;
3. only then any P2/P3 or Lean-owner work.

Until a publication or our own work supplies (1), no further probe, table,
or owner may reference this family.

## 6. Consequences for the Mainline

```text
1053 section 1 decision tree:
   fixed-S projection-square owner ......... DEAD (1051/1052)
   translation/Poisson multiplier .......... DEAD (111/116/131/207)
   semilocal prolate asymptotic family ..... DEAD at P2b gate (this record)
```

With the last surviving global-shape candidate eliminated, the C1 same-owner
route has NO open RH-facing construction beyond the already-landed
detector-selected framework of 1050 section 4. The active program is
therefore exactly the GATE 1 residue plus the four paper-scale CC20-local
payloads already tracked in the README:

```text
alpha-blocked beta residue ... OPEN (interval-ODE brick)
alpha (Fact-1 L1 enclosure) .. OPEN
gamma (paper-scale branch) ... OPEN at paper scale; Bessel branch landed
delta (finite-section cert) .. OPEN
gapData ...................... CLOSED (accepted)
coverage root ................ RH-equivalent (1050); NOT a density lemma
```

Any future global step must now come from a NEW construction with its own
coefficients-complete first checkpoint; the prolate asymptotics slot is
filled by this death.

## 7. Proven vs Evidence-Level

```text
PROVEN (exact arithmetic, reproduced):
  - the 1054 counterexample value Delta = -0.354698 < 0 (generic algebra
    insufficiency for a positive cross-spectral HS energy).

MEASURED (this record, numpy 2.4 / scipy 1.17, full data committed as
`docs/proofs/p2b_probe_results.json`):
  - coefficient-tail amplification ~ x30 per Lanczos step from a 1e-15
    start perturbation;
  - base-energy representation discrepancy dE0/E0 = 0.39-2.68 at every
    tested lambda;
  - prolate gaps 225/508/904/2035 at lambda = 6/9/12/18 (exact-start,
    trustworthy: zero-deep-noise cyclic vector).

JUDGED (conditional on the above + 1053/1054's own rules):
  - closure of the semilocal prolate family as a feasible target.
    This is a programmatic verdict (no definable, decidable first gate),
    not a disproof of the P2b identity, which remains unspeakable until
    P0/P1 exist.
```

## 8. Reproduction

```text
python docs/proofs/1055_semilocal_p2b_probe.py        # ~6 min
# outputs: stdout report, docs/proofs/p2b_probe_results.json (committed)
# expected: "A  control: ... PASS"; exact-e0 reproduction 0.00e+00;
# the B2 dE0 table; every B3 row labelled by its measured dE0 blowup.
```

Harness structure: `control_3point` (Claim A), `tail_growth_demo` and
`precision_wall` (Claim B), `p2b_fd_table` (labelled artefact data only),
`base_physics` (exact-start reference energies). Known numeric landmines
recorded in AGENTS.md section 7c/7d: Stieltjes/QR coefficient recovery is
catastrophically ill-conditioned for these exponential weights; the direct
Euler channel is the FIRST variation along `exp(2 t cos(2 L s))`, not a second
derivative; Lanczos here needs full reorthogonalization twice and is still
depth-limited by `eps * K!`.

## 9. Sources

```text
CCM24 semilocal cyclic pairs:        https://arxiv.org/abs/2310.18423
CC20 archimedean positivity:         https://arxiv.org/abs/2006.13771
CC19 semilocal conjecture:           https://arxiv.org/abs/1910.14368
2024 q-series Jacobi construction:   https://arxiv.org/abs/2403.01247
Ong-Remling bounded Toda:            https://arxiv.org/abs/1801.03053
2026 unbounded Toda:                 https://arxiv.org/abs/2604.05434
Repo: docs/proofs/1053, 1054, and 1055 probe + results json.
```
