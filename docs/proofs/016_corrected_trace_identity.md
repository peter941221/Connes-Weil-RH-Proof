# 016 Corrected Trace Identity

Date: 2026-07-10

Status: Contract M0 complete at the trace-class interface. Contract M2 must
construct the operators and discharge the stated trace-class and cyclicity
hypotheses before Lean can consume this identity.

## 1. Result

Let `lambda_qw > 1`. Let `g` have multiplicative support in
`[lambda_qw^(-1), lambda_qw]`, and put

```text
F_g = g^* * g.
```

Let `S` contain the archimedean place and every prime that occurs in the
prime-power terms with `1 < n <= lambda_qw^2`. Let `Lambda_op > 0` denote the
cutoff used in the support and Fourier-support projections. Under the analytic
hypotheses in Section 7, the corrected identity is

```text
PositiveTrace_(S,Lambda_op)(g)
  = QW_lambda_qw(g,g)
      - Pole_lambda_qw(g)
      + D_(S,Lambda_op)(F_g).                         (M0)
```

Here

```text
Pole_lambda_qw(g)
  = 2 Re(hat(g)(i/2) * conjugate(hat(g)(-i/2))).
```

For the route's vanishing conditions at `+/- i/2`, this specializes to

```text
PositiveTrace_(S,Lambda_op)(g)
  = QW_lambda_qw(g,g) + D_(S,Lambda_op)(F_g).         (M0-vanishing)
```

The signs of both `QW_lambda_qw` and `D_(S,Lambda_op)` are positive on the
right side. The old equality without `D` is false.

## 2. Parameter Separation

Two source parameters have different jobs:

```text
lambda_qw:
  support window for g
  prime-power bound n <= lambda_qw^2 in CCM25 QW_lambda

Lambda_op:
  cutoff in P_Lambda_op and P_hat_Lambda_op
  parameter of the positive compressed operator and D_(S,Lambda_op)
```

CCM25 equations (3.19)-(3.20) use `lambda_qw`. Connes 1999 Theorem 4 uses
`Lambda_op` in the cutoff projections and then sends it to infinity. Neither
source proves `Lambda_op = lambda_qw`. The corrected owner must store both.
The M3 route may set `Lambda_op = 1`, matching the CC20 archimedean model,
without fixing `lambda_qw`.

## 3. Source Conventions

Primary sources:

```text
Connes and Consani, Weil positivity and Trace formula, the archimedean place
https://arxiv.org/abs/2006.13771
Definition 2.1, Proposition 2.2, Corollary 2.3, Theorem 3.6
formulas (41), (43), (51), (56), (58)

Connes, Consani, and Moscovici, Zeta Spectral Triples
https://arxiv.org/abs/2511.22755
equations (3.7)-(3.11), (3.19)-(3.20)

Connes, Consani, and Moscovici, Zeta zeros and prolate wave operators
https://arxiv.org/abs/2310.18423
Propositions 4.1-4.2, equations (46)-(47)

Connes, Trace formula in noncommutative geometry and the zeros of the
Riemann zeta function
https://arxiv.org/abs/math/9811068
Section VII, Theorem 4
```

CCM25 defines

```text
QW(f,g) = Psi(f^* * g),

Psi(F)
  = W_(0,2)(F) - W_R(F) - sum_p W_p(F),

W_R = -W_infinity.
```

Therefore

```text
QW(f,g)
  = W_(0,2)(F_g) + W_infinity(F_g) - sum_p W_p(F_g).
```

The restricted form is

```text
QW_lambda_qw(g,g)
  = W_infinity(F_g)
      + Pole_lambda_qw(g)
      - sum_(1<n<=lambda_qw^2)
          vonMangoldt(n) * n^(-1/2)
            * (F_g(n) + F_g(n^(-1))).                (1)
```

This fixes the pole and finite-prime signs before any operator algebra enters.

## 4. Semilocal Phase Sign

Use the scattering phase orientation

```text
u_S(t)
  = product_(v in S)
      L_v(1/2+it) / L_v(1/2-it).
```

At the archimedean place,

```text
u_infinity(t) = exp(2 i theta(t)),
d/dt arg(u_infinity(t)) = 2 theta'(t).
```

At a finite prime,

```text
u_p(t)
  = L_p(1/2+it) / L_p(1/2-it),

d/dt arg(u_p(t))
  = -2 (log p) sum_(m>=1) p^(-m/2) cos(m t log p).
```

The CC20 quantized-trace normalization sends the phase derivative to the local
distribution. Hence the uncompressed semilocal functional is

```text
W_S(F)
  = W_infinity(F) - sum_(p in S, p finite) W_p(F).    (2)
```

For the support of `F_g`, the prime-power terms outside
`1 < n <= lambda_qw^2` vanish. If `S` contains the visible primes, equations
(1) and (2) give

```text
W_S(F_g)
  = QW_lambda_qw(g,g) - Pole_lambda_qw(g).            (3)
```

The product phase introduces no cross term. For two commuting phase
multipliers `a` and `b`,

```text
(a*b)^* [H,a*b]
  = b^* a^* [H,a] b + b^* [H,b].
```

After multiplying by the test operator, cyclicity removes the outer `b` and
`b^*`. Iteration gives the sum of the local phase derivatives in (2).

## 5. Projection Algebra

Let

```text
P       = P_Lambda_op,
H       = 2P - 1,
P_hat   = u_S^* (1-P) u_S,
T_S     = u_S^* [H,u_S].
```

Unitarity of `u_S` gives

```text
u_S^* H u_S = 1 - 2 P_hat.
```

Thus

```text
P T_S P
  = P(u_S^* H u_S - H)P
  = -2 P P_hat P,

P P_hat P = -(1/2) P T_S P.                         (4)
```

Define the source remainder from the same phase and projection:

```text
D_(S,Lambda_op)(F)
  = (1/2) Tr(theta_S(F) * (T_S - P T_S P)).          (5)
```

Equation (5) is an operator-defined distribution. It is not a free scalar or a
stored route conclusion.

The uncompressed local functional has the CC20 normalization

```text
W_S(F) = -(1/2) Tr(theta_S(F) * T_S).                (6)
```

From (4)-(6),

```text
Tr(theta_S(F) * P P_hat P)
  = W_S(F) + D_(S,Lambda_op)(F).                     (7)
```

For `S={infinity}` and `Lambda_op=1`, equation (7) is CC20 Corollary 2.3:

```text
L(F) = W_infinity(F) + D(F).
```

This specialization checks the sign of `D`.

## 6. Positive Trace

Set

```text
A_(S,Lambda_op,g) = P_hat P theta_S(g).
```

Since the multiplicative convolution algebra is commutative,
`theta_S(g)^* theta_S(g)` and `theta_S(F_g)` represent the same square. Legal
trace cyclicity gives

```text
Tr(A^* A)
  = Tr(theta_S(F_g) * P P_hat P).                    (8)
```

Combining (3), (7), and (8) proves (M0).

## 7. Analytic Interface Owned By M2

The algebraic proof consumes these analytic facts:

```text
A_(S,Lambda_op,g) is Hilbert-Schmidt
A^* A is trace-class
theta_S(F_g) T_S is trace-class after source smoothing
theta_S(F_g) P T_S P is trace-class
each cyclic trace move uses a trace-class/bounded pair
the ordinary complex trace in (8) equals a real nonnegative scalar
```

Contract M2 must prove them for the same owner. M0 fixes the statement and
signs; it does not replace M2.

## 8. Rank And Pole Accounting

The pole pairing already belongs to `QW_lambda_qw` and appears exactly once in
(M0), with subtraction on the right side.

No separate rank term occurs in (M0). The term

```text
2 h(1) log' Lambda_op
```

belongs to the asymptotic trace of `P_hat_Lambda_op P_Lambda_op U(h)` in
Connes 1999 Theorem 4. That operator is not the positive square in (8). A route
may introduce a separate rank term only after proving an equality between
those two trace problems.

## 9. Route Consequences

The corrected downstream owner must expose

```text
lambda_qw
Lambda_op
S and visible-prime coverage
g and F_g
P, P_hat, u_S, and T_S
PositiveTrace = Tr(A^* A)
Pole_lambda_qw
D_(S,Lambda_op)
M0 identity
```

It must not expose

```text
supportSquareTrace = QW_lambda_qw
D_(S,Lambda_op) = 0
Lambda_op = lambda_qw without a theorem
a second pole or rank ledger copied into QW_lambda_qw
```

Contract M3 now owns the sign control of `D_(S,1) o Q`. Contract M5 must place
the conditioned detector in the nonpositive subspace for that same remainder.
