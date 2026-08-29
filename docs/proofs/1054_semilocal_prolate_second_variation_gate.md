# 1054 - Semilocal prolate second-variation gate

Date: 2026-08-29. Follows proof 1053.

Status:

```text
PROVED: P2a is necessary but is not a decisive Euler-coefficient test.

PROVED: the Poisson/logarithmic measure path has an independent quadratic
        response at p^2. It does not reduce algebraically to the linear
        cos(2 L s) response, even for a finite cyclic pair with an exactly
        prolate-normalized self-adjoint operator and a genuine positive
        cross-spectral Hilbert-Schmidt energy.

OPEN: whether the specific Gamma/Meixner-Pollaczek semilocal prolate model has
      a special large-lambda cancellation of that quadratic one-crossing term.
```

This is not a no-go for every asymptotic prolate construction. It rules out one
shortcut: a correct first variation at `m = 1` plus analyticity of the Euler
logarithm does not imply the required coefficient at `m = 2`.

## 1. Why P2a Cannot Decide P2

For one prime, write

```text
a = p^(-1/2),       L = log p,
w_a(s) = |1 - a exp(i L s)|^(-2).
```

The exact logarithmic expansion is

```text
log w_a(s)
  = 2 a cos(L s) + a^2 cos(2 L s) + O(a^3).             (1.1)
```

Let `E_lambda(a)` be any proposed cross-spectral energy after all its
self-adjointness and trace-ideal hypotheses have actually been proved. The
coefficient of `a^2` is

```text
1/2 E_lambda''(0).
```

The Euler logarithm supplies only the direct second-harmonic contribution

```text
1/2 delta_(cos(2 L s)) E_lambda(0),                     (1.2)
```

where `delta_f` means the first variation under the separate weight
`exp(2 t f(s))`. Their difference contains the iterated first-harmonic
response

```text
1/2 [ E_lambda''(0) - delta_(cos(2 L s)) E_lambda(0) ]. (1.3)
```

No general projection identity, QR identity, or positivity identity makes
(1.3) vanish. It must be proved to have zero one-crossing readback, or the
`p^2` coefficient is changed. This is the same logical location at which the
metric-Sonin owner failed, but it is not inherited automatically by a new
prolate owner.

```text
P2a: first harmonic is correct
             |
             v
P2b: quadratic first-harmonic response has no one-crossing U^(2) term
             |
             v
P2: all higher mixed responses assemble to the Euler logarithm
```

## 2. Exact Finite Cyclic-Pair Counterexample

The following finite model is deliberately elementary. Its purpose is to test
whether (1.3) could vanish by general operator algebra alone. It cannot.

Take the three-point spectral space

```text
X = {-1, 0, 1},             L = pi/2,
dmu_a(s) proportional to w_a(s) dmu_0(s),
w_a(s) = |1 - a exp(i L s)|^(-2),
```

with equal base weights. The ratio of the central weight to either endpoint
weight is

```text
h(a) = (1 + a^2)/(1 - a)^2,
x(a) = E_a[s^2] = 2/(h(a) + 2)
     = 2 (1-a)^2/(3 - 4a + 3a^2).                       (2.1)
```

Thus

```text
x(0) = 2/3,       x'(0) = -4/9,       x''(0) = -32/27.  (2.2)
```

In the degree-ordered orthonormal-polynomial basis, multiplication by `s` is

```text
            [ 0       sqrt(x)           0       ]
D_a =       [ sqrt(x)    0        sqrt(1-x)    ].       (2.3)
            [ 0       sqrt(1-x)          0       ]

N = diag(0, 1, 2).
```

Choose `lambda^2 = 1/(4 pi)`. Then the formal CCM24 normalization is exactly

```text
W_a = -D_a^2 + 2 N + 1/4 I.                             (2.4)
```

At `a = 0`, its odd block is `5/4`, while its even block is

```text
[ 1/4 - x          -sqrt(x (1-x)) ]
[ -sqrt(x (1-x))    13/4 + x      ].                    (2.5)
```

The determinant of (2.5) is `13/16 - 4x`, hence it has one negative and one
positive eigenvalue at `x = 2/3`. Let `Pi_-` and `Pi_+` be the corresponding
spectral projections and take the honest self-adjoint multiplier `C = D_a`.
Parity reduces the positive cross-spectral energy to one matrix coefficient:

```text
E(a) = || Pi_- D_a Pi_+ ||_HS^2
     = 1/2 + (8 x(a) - 3)/(2 sqrt(9 + 16 x(a))).         (2.6)
```

This is a finite-dimensional Hilbert-Schmidt norm, so no trace convention,
regularization, or threshold ambiguity is involved.

## 3. The Nonlinear Term Is Strictly Nonzero

For the direct second harmonic use the separate path

```text
dmu_t proportional to exp(2 t cos(2 L s)) dmu_0.
```

Here `cos(2 L s) = cos(pi s)`, so its central/end-point ratio is `exp(4t)` and

```text
d/dt [ 2/(exp(4t) + 2) ] at t=0 = -8/9.                 (3.1)
```

Writing the right side of (2.6) as `E(x)`, direct differentiation at
`x = 2/3` gives

```text
E_x  at x = 2/3 = 16 (13/3)/(59/3)^(3/2) > 0,
E_xx at x = 2/3 = -3104/(3 (59/3)^(5/2)) < 0.           (3.2)
```

Therefore the actual Poisson-path second response minus the pure
second-harmonic response is

```text
E''(0) - d/dt E_(cos(2 L s))(t)|_(t=0)
  = E_x (-8/27) + E_xx (16/81)
  < 0.                                                    (3.3)
```

Equation (3.3) is an exact strict inequality. The term `E_xx (x'(0))^2` is
the iterated first-harmonic response. It remains after the direct
`cos(2 L s)` contribution has been removed.

Consequently, a proof of P2 cannot say that the logarithmic series (1.1)
alone supplies the Euler coefficients. It must calculate or cancel (1.3) in
the actual infinite-dimensional model.

## 4. QR/Toda Interpretation

For a finite cyclic pair with `dmu_t = exp(2 t f) dmu`, let `e_n(t)` be the
orthonormal-polynomial basis transported to the fixed Hilbert space. If

```text
F_mn = <e_m, f(D) e_n>,
K_mn = sign(m-n) F_mn,
```

then `K` is skew-adjoint and Gram--Schmidt differentiation gives

```text
dJ/dt = [J, K],
dN/dt = [K, N].                                         (4.1)
```

For the prolate form `W = -J^2 + c N + d I`, the non-gauge variation is
`c [K,N]`. At second order, differentiating (4.1) necessarily produces both
the direct `cos(2 L D)` generator and an iterated `[K_L,[K_L,N]]` channel.
The finite example above shows that a positive cross energy can see that
iterated channel.

This is consistent with the general QR/Toda mechanism, but the available
generalized Toda theorem is not an escape hatch here: Ong--Remling assumes a
bounded Jacobi operator, while the archimedean coefficients are asymptotic to
`n`; see https://arxiv.org/abs/1801.03053 and CCM24 section 3.4. The 2026
unbounded Toda paper still assumes coefficient growth `O(|n|^alpha)` with
`alpha < 1` for its quoted existence result and treats the standard Toda
flow, not this cosine generalized flow; see https://arxiv.org/abs/2604.05434.

## 5. Required P2b Theorem

For the actual Gamma/Meixner-Pollaczek semilocal family, define the operator
and smoothing first. CCM24 supplies a formal `W_(lambda,S)` and the cyclic
measure, but not the cross-spectral functional or its trace identity:

```text
https://arxiv.org/html/2310.18423
```

Only after P0/P1 are supplied is the following a meaningful kill test:

```text
P2b. After the same trace smoothing and one-crossing readback used in P2,

  lim_(lambda -> infinity)
    Readback_1cross(
      1/2 E_lambda''(0)
      - 1/2 delta_(cos(2 L s)) E_lambda(0)
    ) = 0.
```

If P2b fails for one compact admissible test with visible `p^2`, the proposed
asymptotic cross-spectral owner is rejected. If it holds, it is the first
evidence that the positivity object has a special Ward/Toda cancellation not
present in generic cyclic pairs. Only then is it rational to attempt the full
summation over `m` and finite `S`.

The 2024 q-series paper constructs moments and Jacobi coefficients for
`S = {infinity,p}`, but proves no P2b-type spectral-projection trace theorem:

```text
https://arxiv.org/abs/2403.01247
```

## 6. Verdict

```text
P2a correct: necessary only.
P2b cancellation: the first coefficient-complete go/no-go gate.
Generic QR/Toda algebra: insufficient; exact finite counterexample above.
Actual semilocal prolate P2b: open.
New conditional Lean owner: forbidden until P0, P1, and P2b are analytic.
```
