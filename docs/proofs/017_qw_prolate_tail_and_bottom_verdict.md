# 017 QW--Prolate Tail And Full-Bottom Verdict

Date: 2026-07-11

Result: partial. The exact Poisson tail remains a legitimate research
mechanism, but it does not yet define a `QW_lambda` Rayleigh estimate or select
the full ground state. The present gap is a quadratic-form domain and graph-norm
theorem, followed by a genuinely uniform low-cluster comparison.

## 1. What Is Now Separated

Three assertions must not be conflated:

```text
(A) xi_lambda is the simple even full ground state of A_lambda;
(B) its eigenvalue mu_lambda is nonnegative;
(C) QW is nonnegative on every compactly supported Weil test.
```

`(A)` alone does not imply `(B)` or RH. The source explicitly warns that the
lowest spectral value need not be nonnegative:

```text
Zeta Spectral Triples
https://arxiv.org/abs/2511.22755
mc2arXiv.tex:658-668
```

If `(A)` and `(B)` hold along a cofinal sequence `lambda_j -> infinity`, then
every test supported in one of those windows has nonnegative `QW` value. Support
exhaustion then gives `(C)`, which is the RH-level Weil positivity theorem.
Thus the sign in `(B)`, not ground-state ownership by itself, is the direct
positivity barrier.

## 2. The Restricted Form Is Not A Tail Norm

The exact source formula is

```text
QW_lambda(f,f)
  = integral |f_hat(t)|^2 * theta'(t)/pi dt
      + pole-evaluation term
      - sum_(1<n<=lambda^2) Lambda(n) <f,T(n)f>.
```

Source:

```text
https://arxiv.org/abs/2511.22755
mc2arXiv.tex:530-540
```

The archimedean part is an unbounded Fourier multiplier with asymptotic symbol
`(1/2) log |t|`; the pole and finite-prime parts are bounded perturbations.
Source: `mc2arXiv.tex:612-627`.

Consequently the exact leakage identity

```text
||r_lambda||_2^2
  = chi_0^2 |p_0(0)|^2 (1-chi_2^2)
      + chi_2^2 |p_4(0)|^2 (1-chi_0^2)
```

does not by itself bound `QW_lambda(k_lambda,k_lambda)`. An `L2`-small vector
can carry uncontrolled mass at large Fourier frequency for an unbounded closed
form. The required norm is a `QW` form norm, comparable on the archimedean side
to

```text
integral |f_hat(t)|^2 * (1 + log_+ |t|) dt.
```

## 3. The Formal Tail Identity And Its Missing Hypothesis

Let

```text
g_lambda := E(h_lambda),
p_lambda := 1_[lambda^-1,lambda] * g_lambda,
q_lambda := g_lambda - p_lambda.
```

Since `h_lambda` is supported in `[-lambda,lambda]`, the upper tail of
`g_lambda` vanishes. The first R1 calculation gives the lower tail of
`q_lambda` exactly in terms of `r_lambda` and `h_lambda(0)`.

There is a useful formal lemma. If all three vectors lie in one Hermitian
quadratic-form domain and

```text
QW(g_lambda,v) = 0 for every v in that domain,
```

then sesquilinearity gives

```text
QW(p_lambda,p_lambda) = QW(q_lambda,q_lambda).
```

This would turn the exact Poisson tail into an exact producer for the proxy's
restricted Rayleigh value.

The source does not currently justify applying that lemma to `h_lambda`.
The published radical statement uses the codimension-two Schwartz space

```text
S_0 = {f even Schwartz | f(0)=0 and integral f=0}.
```

See:

```text
Spectral Triples and Zeta-Cycles
https://arxiv.org/abs/2106.01715
Spectraltriples.tex:181-189,696-708
```

Our exact source-normalized proxy satisfies `integral h_lambda = 0` but

```text
h_lambda(0)
  = p_0(0) p_4(0) (chi_0-chi_2) != 0
```

at finite `lambda`. It is therefore outside the stated `S_0` theorem. Its
nonzero value at zero is exactly the Poisson correction already found; it may
still admit a larger-domain radical identity, but that extension must be
proved from the Mellin/explicit formula with convergence at both endpoints.
It cannot be imported by name from the source.

The endpoint discontinuity of a compactly supported prolate mode is not by
itself fatal. The source states that compactly supported piecewise-smooth tests
have Fourier decay `O(1/|t|)` and belong to `Dom(QW_lambda)`.
See `mc2arXiv.tex:658-666`. The missing point is the common global form domain
for `g_lambda`, its lower tail, and the cross terms, not merely local
piecewise smoothness of `p_lambda`.

## 4. Complement Coercivity: What The Source Gives

The source decomposition yields qualitative high-frequency coercivity:

```text
A_lambda
  = archimedean log-Fourier multiplier
      + bounded pole and finite-prime perturbations.
```

This proves compact resolvent and a discrete lower-bounded spectrum, but the
paper supplies no uniform bound in `lambda` that places the entire complement
of the approximately `2*lambda^2` prolate cluster above the selected state.
The proof is for each fixed `lambda`; its cutoff depends on the norm of the
bounded perturbation. See `mc2arXiv.tex:612-657`.

The older prolate paper gives approximately `2*lambda^2` near-intersection
modes and only numerical/graphical comparison with the smallest QW
eigenvectors:

```text
https://arxiv.org/abs/2106.01715
Spectraltriples.tex:181-193,741-760
```

Therefore qualitative high-frequency coercivity does not close R1B. The
uncontrolled region is the growing low and intermediate spectrum, precisely
where a Riesz-projection, Feshbach, or effective-matrix estimate is needed.

## 5. Current Decision

```text
Poisson-tail mechanism:        survives, conditional on a new domain theorem
L2 leakage -> QW estimate:     rejected as a sufficient implication
full-bottom ownership:         open
lowest-eigenvalue sign:        open and RH-sensitive
017 route:                     not rejected, not feasible yet
```

The next smallest mathematical target is the following extended-radical and
tail-form theorem for the same `h_lambda`:

```text
g_lambda, p_lambda, q_lambda belong to one closed QW form domain;
QW(g_lambda,v)=0 for every compact form-core test v;
QW_lambda(p_lambda,p_lambda)=QW(q_lambda,q_lambda);
|QW(q_lambda,q_lambda)| <= C_lambda * TailDefect(lambda),
```

with an explicit `C_lambda`. R1 advances only if this loss is smaller than a
proved relative gap in a full growing-cluster model. A two-mode calculation
without the higher cluster and complement cannot pass the gate.
