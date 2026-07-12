# Plan 020: Nyman--Mobius Dyadic Energy Certificate

Date: 2026-07-11

Status: rejected as an executable RH route. The finite identities remain valid,
but the central M4 inequality has not reduced to a lower arithmetic producer.
Every tested structural decomposition retains the inverse finite Gram matrix,
and the only source-grade asymptotic for the relevant Mobius approximation is
conditional on RH plus a zero-derivative moment bound. This does not disprove
M4 as a mathematical statement; it rejects Plan 020 as a guaranteed route.

## 1. Scope And Explicit Non-Goals

This experiment leaves the Connes trace route and works in the discrete
Nyman--Beurling--Baez-Duarte Hilbert space

```text
H = {a : sum_(n>=1) |a_n|^2/(n(n+1)) < infinity}.
```

Let

```text
gamma(n)   = 1,
gamma_k(n) = {n/k},
V_N        = span(gamma_2,...,gamma_N),
d_N        = distance(gamma,V_N).
```

The source theorem gives `RH <=> d_N -> 0`.

The experiment does not assume RH, a zero-free half-plane, a bound for
`1/zeta`, cancellation of the Mertens function, or convergence of the
unregularized Mobius approximation. It does not create Lean route APIs before
the arithmetic lower bound passes.

Primary sources:

```text
Bhaskar Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space
reformulation of the Riemann hypothesis, Proc. Indian Acad. Sci. 116 (2006),
137--146, Theorem 1 and Remark 8.
https://www.ias.ac.in/article/fulltext/pmsc/116/02/0137-0146

Luis Baez-Duarte, A strengthening of the Nyman-Beurling criterion for the
Riemann hypothesis, 2, arXiv:math/0205003.
https://arxiv.org/abs/math/0205003
```

## 2. Route Obligation

```text
route obligation:
  prove d_N -> 0 through a uniform finite dyadic energy decrement

old weak path:
  numerical observation that the best least-squares distance decreases

new mathematical owner:
  exact weighted sequence Hilbert space, its finite Gram matrices, the
  orthogonal residual r_N, and one explicit Mobius block vector

consumer to rewire:
  a future source-RH bridge, then _root_.RiemannHypothesis

forbidden circular inputs:
  RH, zero locations, Littlewood bounds, Mertens cancellation, Lindelof,
  convergence of sum mu(k) gamma_k, or any lower bound stated using d_N
  without an independent finite arithmetic proof

smallest verification target:
  an exact finite formula and uniform lower bound for the Mobius block capture

focused axiom audit:
  inactive until Gate M4 supplies a theorem-grade lower bound
```

## 3. Exact Finite Mechanism

Let `P_N` be orthogonal projection onto `V_N` and

```text
r_N = gamma - P_N gamma.
```

For the dyadic block `B_N={N+1,...,2N}`, define

```text
b_N = sum_(k in B_N) mu(k)/k * gamma_k,
w_N = (I-P_N)b_N.
```

If `w_N != 0`, projection onto the single new direction gives the exact
certificate

```text
d_(2N)^2
  <= d_N^2 - |<r_N,w_N>|^2 / ||w_N||^2.                 (M3.1)
```

Therefore the finite arithmetic inequality

```text
|<r_N,w_N>|^2 / ||w_N||^2
  >= (c/log N) d_N^2                                   (M4.1)
```

for one absolute `c>0` and every sufficiently large dyadic `N` implies

```text
d_(2N)^2 <= (1-c/log N)d_N^2.
```

Since `sum_j 1/log(2^j)` diverges, the product of these factors is zero. Thus
`d_(2^j)->0`; monotonicity then gives `d_N->0`, and the discrete criterion
gives RH.

This logic bridge is unconditional and finite at every scale. The unknown is
only (M4.1).

## 4. Why The Main Gate Is Not Already A Proof In Disguise

The conclusion `d_N->0` is RH-equivalent, so every sufficient uniform
decrement theorem is necessarily strong enough to imply RH. That fact alone
does not make (M4.1) circular. The admissibility test is its input language:

```text
admissible producer:
  finite sums of residues n mod k, mu(k), positive weights 1/(n(n+1)),
  exact Gram/Schur identities, and unconditional divisor-sum estimates

rejected producer:
  estimates for 1/zeta in Re(s)>1/2, M(x)=O(x^(1/2+epsilon)), Weil
  positivity, or the assertion that the Mobius approximants converge in H
```

Baez-Duarte's source explicitly constructs natural Mobius approximants only
under RH, using Littlewood-type control. That proof cannot be reused for M4.
The new content must be a direct finite block inequality.

## 5. Rejection-First Gates

### M0. Exact criterion and object match

Pass only if the implemented sequence, weight, target, and basis agree with
the published discrete criterion. Status: passed.

Evidence: Bagchi, Theorem 1, and the unitary identification in the proof after
Theorem 7. The experiment implements the same entries and weights in
`scratch_nyman_block.py:5-21`.

### M1. Numerical artifact guard

Replace tail-truncated sums by exact inner-product formulas or interval bounds.
Track Gram and Schur condition numbers. Reject if the normalized capture
collapses under precision, cutoff, or scale changes.

Status: passed for the tested scales, not as a uniform theorem. The exact finite
periodic formula is recorded in
`docs/proofs/020_nyman_mobius_m4_first_verdict.md`. Cutoffs
`250000, 500000, 1000000, 2000000` change the
`N=128` normalized `mu/k` capture only from approximately `0.6166` to `0.6164`.
At cutoff `500000`, the old Gram condition number at `N=128` is about
`3.82e4`; the block Schur condition number is about `3.87e3`. Exact or interval
inner products remain mandatory.

### M2. Exact one-direction decrement

Prove (M3.1) from orthogonal projection and Schur complementation, including
the `w_N=0` branch. Status: mathematically passed; Lean formalization is
inactive until M4 survives.

### M3. Dyadic product closure

Prove that (M4.1) implies `d_N->0`, with all threshold and monotonicity
quantifiers explicit. Status: mathematically passed; this is elementary once
M4 holds.

### M4. Uniform Mobius block capture

This is the first decisive mathematical gate. Prove (M4.1) without a spectral
or RH-equivalent input. Split it into two estimates:

```text
correlation lower bound:
  |<r_N,w_N>| >= A_N * d_N

energy upper bound:
  ||w_N||^2 <= B_N

required margin:
  A_N^2/B_N >= c/log N.
```

The first attack must expand both quantities into finite residue/divisor sums
and test whether the Mobius identity `sum_(d|m) mu(d)=1_(m=1)` creates a
diagonal main term. Reject this certificate if cancellation leaves an error of
the same order with no unconditional sign or if proving the correlation bound
requires Mertens cancellation at square-root strength.

The first structural audit rejected direct use of Vasyunin's explicit infinite
biorthogonal family: the finite dual is `P_N f_n`, whose coordinates are again
the rows of `G_N^-1`. Do not treat infinite biorthogonality as a finite inverse
formula. The remaining concrete entrypoint is the tail identity

```text
w_N = (I-P_N)(b_N-N*S_N*gamma_N),
S_N = sum_(N<k<=2N) mu(k)/k^2,
```

whose unprojected vector vanishes in the first `N-1` coordinates. It turns the
denominator into short weighted Mobius sums but has not controlled the
correlation. See `docs/proofs/020_nyman_mobius_m4_first_verdict.md`.

### M5. Exact source-to-Mathlib bridge

Only after M4 passes, formalize the discrete criterion or connect it to an
existing source theorem, then prove the no-argument implication to
`_root_.RiemannHypothesis`. Audit both the complete theorem type and axioms.

## 6. Current Experiment

The implementation computes the target projection, the full block optimum,
and several explicit directions. For the proposed `mu(k)/k` direction, the
reported quantity is

```text
log(N) * certificate_capture / d_N^2.
```

WSL2, cutoff `2000000`, omitted scalar weight mass `5e-7`:

```text
+------+----------------+----------------------+----------------------+
| N    | d_N^2          | best block * log(N)  | mu/k cert * log(N)   |
+------+----------------+----------------------+----------------------+
| 16   | 1.793668e-2    | 0.5966               | 0.4263               |
| 32   | 1.407740e-2    | 0.6609               | 0.5779               |
| 64   | 1.139282e-2    | 0.6287               | 0.5544               |
| 128  | 9.670621e-3    | 0.7166               | 0.6164               |
+------+----------------+----------------------+----------------------+
```

The next rejection run reached `N=512`. The normalized certificate was
approximately `0.4140` at `N=256` and recovered to `0.5802` at `N=512`; no
monotone collapse was observed. See
`docs/proofs/020_nyman_mobius_m4_first_verdict.md` for the exact Gram formula,
the decomposed correlation, and the natural-Mobius divergence guard.

Interpretation: the explicit certificate survives four nontrivial dyadic
scales and captures most of the best block improvement. This is evidence that
M4 is a coherent target, not evidence that its infimum is positive.

## 7. Decision Criteria

```text
accepted feasibility:
  M0-M3 pass and M4 is reduced to named unconditional finite estimates with a
  strict positive margin

accepted RH route:
  M4 and M5 pass with no RH-equivalent analytic input

partial:
  exact finite formulas and scale-stable numerics exist, but no uniform lower
  bound is proved

rejected:
  the normalized certificate tends to zero, exact arithmetic destroys the
  observed margin, or M4 requires square-root Mertens/Littlewood control
```

Current verdict: rejected as a research route, with M4 itself unresolved. It
crossed more preliminary gates than Plans 017--019, but every proposed lower
producer for M4 failed while the exact inverse-Gram inequality remained. Since
M4 by itself implies RH, leaving that whole inequality as the named bottom is
not a route reduction.

The first M4 structural round rejects two shortcuts but not the whole plan.
Vasyunin's infinite biorthogonal system does not give the finite inverse, and
the published Cholesky positivity conjecture does not control the mixed-sign
target coordinates. Existing power-saving Mobius--Vasyunin estimates give
upper cancellation bounds, while M4's numerator needs a uniform non-cancellation
lower bound after finite projection. The remaining named bottom is therefore:

```text
inverse-Gram Mobius non-cancellation:
  abs(a_N^T (t_block-C_N^T G_N^-1 t_N))^2
    >= (c/log N) * d_N^2
         * a_N^T(B_N-C_N^T G_N^-1 C_N)a_N.
```

Do not continue by proving only a short-sum upper bound for the denominator;
that cannot close M4 without an independent signed numerator theorem.

The next sign audit rejects a pointwise route. For the sequential
Gram--Schmidt coordinate `E_n=<gamma,e_n>`, the proposed sign
`sign(E_n)=sign(-mu(n))` already fails at the squarefree index `n=31` and at 23
more squarefree indices through `256`. Therefore M4 cannot be proved by making
every Mobius-weighted correlation nonnegative.

Power weights `mu(k)/k^alpha` for a broad range `-1<=alpha<=2` all preserve the
same numerical scale through `N=512`, showing that the Mobius signs rather than
fine exponent tuning drive the experiment. The source-motivated BCF log taper
is weaker and is conditional in its published asymptotic theorem. The sole
remaining numerator target is a block-average dominance theorem that allows
individual bad signs.

The good/bad mass audit further rules out a fixed-fraction dominance proof. For
`alpha=1`, `bad_N/good_N` rises from about `0.051` at `N=32` to `0.509` at
`N=512`. The normalized certificate survives only because the projected Schur
energy also shrinks. Replace the phrase "block-average dominance" by the exact
coupled target: net correlation squared relative to projected energy and
`d_N^2`. Do not bound the two sides independently with coarse estimates.

The final large-scale rejection run used the matrix-free CUDA mode in
`scratch_nyman_block.py`. It solves only the two old-space normal equations
needed for the selected direction. With cutoff `250000`, both relative normal
residuals were below `1e-11`:

```text
+------+---------------------------+
| N    | mu/k certificate * log(N) |
+------+---------------------------+
| 512  | 0.5802                    |
| 1024 | 0.2948                    |
| 2048 | 0.5869                    |
| 4096 | 0.2664                    |
+------+---------------------------+
```

At `N=1024`, changing the cutoff from `100000` to `250000` changed the value
from `0.2965` to `0.2948`. At `N=4096`, it changed from `0.2834` to `0.2664`.
The experiment therefore finds strong dyadic oscillation and descending low
subscales, not a stable visible positive margin. It is not a rigorous
counterexample: the projected energy is smaller than the crude omitted-weight
bound, so finite cutoff cannot certify that the infimum is zero.

Final rejection mechanism:

```text
finite identities and numerics
  -> inverse-Gram Mobius non-cancellation remains intact
  -> no independent sign, diagonal main term, or lower arithmetic theorem
  -> known matching Mobius asymptotic assumes RH plus a zeta-derivative moment
  -> M4 is the unresolved RH-producing statement, not a lowered dependency
```

Do not reopen Plan 020 through larger floating-point runs, Vasyunin duality,
pointwise signs, fixed-fraction good/bad estimates, power-weight tuning, or the
BCF taper. A future route may reuse the exact finite formulas only after a new
unconditional theorem supplies a genuinely lower coupled inverse-Gram bound.
