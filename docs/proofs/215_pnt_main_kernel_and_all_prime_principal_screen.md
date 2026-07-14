# Proof 215: PNT main-kernel sign and all-prime principal screen

Date: 2026-07-13

Status: the continuous PNT main-kernel theorem is accepted and unconditional.
The all-prime principal screen is superseded as route evidence by Proof 217:
it places the Q-image derivative multiplier on the same raw vector as the
prime translation instead of using the genuine pair `g=L xi`.  The tables
remain reproducible diagnostics for that raw model, but their positive values
do not identify the CC20 same-object bottom.  RH remains unproved.

## 1. From prime translations to the PNT main kernel

For an interval `I=(-a,a)` of length

```text
T=2a=log(c),
```

the exact finite-prime translation operator is

```text
K_c
 = sum_(q=p^m<c) Lambda(q)/sqrt(q)
     (T_(log q)+T_(-log q)).                            (P.1)
```

The project proves the same-object quadratic read-off for (P.1) in
`SelectedPrimeTranslationQuadratic.lean:72-139`.

Replace the von-Mangoldt Stieltjes measure `d psi(x)` by its unconditional PNT
main measure `dx`.  With `b=log x`,

```text
dx/sqrt(x)=exp(b/2)db.
```

Thus the continuous main operator is

```text
(K_0 f)(x)
 = integral_(-a)^a exp(|x-y|/2) f(y)dy.                 (P.2)
```

The upper limit `b<T` covers every pair `(x,y)` in the interval, so there is
no cutoff error in (P.2).

## 2. Exact Green-kernel identity

Let

```text
u=K_0 f,
D=partial_x^2-1/4.
```

The derivative jump of `exp(|x-y|/2)` at `x=y` is one.  Therefore

```text
D u=f,                                                  (P.3)

u'(a)=u(a)/2,
u'(-a)=-u(-a)/2.                                       (P.4)
```

Put

```text
C(x)=cosh(x/2).
```

Since `D C=0`, Green's identity and (P.4) give

```text
<C,f>
 = (exp(-a/2)/2)[u(a)+u(-a)].                          (P.5)
```

Hence pole neutrality `<C,f>=0` is exactly the endpoint condition

```text
u(-a)=-u(a).                                           (P.6)
```

This identifies why the `cosh` row, rather than the mean-zero row, removes the
PNT main mode.

## 3. Main-kernel sign on the pole-neutral space

Write `v=u(a)`.  Equations (P.4) and (P.6) give

```text
<f,K_0f>
 = <D u,u>
 = |v|^2-integral_(-a)^a(|u'|^2+(1/4)|u|^2)dx.         (P.7)
```

Among functions with endpoint values `u(-a)=-v`, `u(a)=v`, the energy in
(P.7) is minimized by

```text
u_0(x)=v sinh(x/2)/sinh(a/2).
```

The Dirichlet principle gives

```text
integral_(-a)^a(|u'|^2+(1/4)|u|^2)dx
 >= coth(a/2)|v|^2.                                   (P.8)
```

Combining (P.7)-(P.8),

```text
<C,f>=0
  -> <f,K_0f>
       <= [1-coth(a/2)]|u(a)|^2
       <= 0.                                           (P.9)
```

This is an exact continuum theorem.  In particular, `K_0` has at most one
positive direction, and the codimension-one `C` row removes it.  No zeta zero,
RH assumption, or numerical input occurs in (P.2)-(P.9).

## 4. The remaining discrete error

Write

```text
K_c=K_0+E_c.                                           (P.10)
```

For the autocorrelation

```text
F_g(b)=<g,T_b g>,
```

partial summation expresses the scalar form of `E_c` through

```text
psi(x)-x
```

and the derivative of

```text
x^(-1/2)F_g(log x).                                    (P.11)
```

The certified CC20 bound from proof 214 supplies the common Sobolev budget

```text
(1/50)(||g'||^2+(1/4)||g||^2).                         (P.12)
```

The desired next producer is therefore a form estimate for (P.11), on the
same compact-support and pole-neutral domain, strong enough to prove

```text
<g,E_c g>
 <= 2||g||^2+(1/50)||g'||^2                            (P.13)
```

after using the favorable sign (P.9).

A naive absolute-value insertion of the classical PNT error is not enough:
its weighted integral can still grow with `c`.  The proof of (P.13) must retain
the autocorrelation cancellation or use a multiplicative large-sieve/positive
quadrature argument.  Replacing it by an RH-strength square-root PNT error is
forbidden.

## 5. All-prime principal-form screen

The probe discretizes

```text
A_principal(c)
 = (1/50)(-partial_x^2+1/4)+2 Id-K_c                 (P.14)
```

on `(-log(c)/2,log(c)/2)` with zero extension.  It aggregates all exact prime
powers into one Toeplitz matrix and imposes the three source rows

```text
1,
cosh(x/2),
sinh(x/2).
```

At grid size 500:

```text
+----------+----------------------------+
| cutoff   | constrained minimum        |
+----------+----------------------------+
| 16       | 2.78520050                 |
| 64       | 2.75676404                 |
| 256      | 2.74756595                 |
| 1024     | 2.74328902                 |
| 10000    | 2.73956111                 |
+----------+----------------------------+
```

The aggregated assembly agrees with the direct term-by-term matrix at
`c=10000`, size 500, to `3e-14`.  Grid refinement gives

```text
+---------+------+----------------------+
| cutoff  | size | constrained minimum  |
+---------+------+----------------------+
| 256     | 250  | 2.74760119           |
| 256     | 500  | 2.74756595           |
| 256     | 750  | 2.74757203           |
| 256     | 1000 | 2.74756622           |
| 10000   | 250  | 2.73774497           |
| 10000   | 500  | 2.73956111           |
| 10000   | 750  | 2.73911519           |
| 10000   | 1000 | 2.73990308           |
+---------+------+----------------------+
```

The aggregated size-600 extension remains stable:

```text
+----------+----------------------------+
| cutoff   | constrained minimum        |
+----------+----------------------------+
| 10^5     | 2.73629421                 |
| 10^6     | 2.73810597                 |
| 10^7     | 2.73803001                 |
+----------+----------------------------+
```

These are rejection screens, not lower bounds for the continuum operator.

## 6. Constraint mechanism

At `c=10000`, size 500, the constraint split is

```text
+----------------------+------------------+
| constraints          | minimum          |
+----------------------+------------------+
| none                 | -102.06094229    |
| mean only            |  -18.95606811    |
| sinh only            | -102.06094229    |
| cosh only            |    2.73952207    |
| cosh and sinh        |    2.73952207    |
| all three            |    2.73956111    |
+----------------------+------------------+
```

The unconstrained matrix has exactly one negative eigenvalue in the tested
section; the next eigenvalue is `2.73952334`.  This matches the exact main-kernel
theorem (P.9): the negative Perron mode is even and the `cosh` row removes it.
The mean-zero row is not the principal sign mechanism.

## 7. Reproduction

The default screen requires SciPy:

```text
python3 -B docs/proofs/215_all_prime_principal_form_probe.py \
  --cutoff 16 64 256 1024 10000 --size 500
```

Larger cutoffs can be screened with, for example,

```text
python3 -B docs/proofs/215_all_prime_principal_form_probe.py \
  --cutoff 100000 1000000 10000000 --size 600
```

## 8. Corrected route judgment

```text
continuous PNT main kernel:               exact in the raw model
main-kernel sign on cosh-perp:            proved unconditionally
strict CC20 multiplier lower bound:       proved by Proof 214
raw all-prime principal screen:           positive through 10^7
same-object Q-root representation:        absent from this screen
corrected 1/50 coarse form:               strongly negative; Proof 217
named compact CC20 remainder:             not reinserted
Lean owner:                               none
RH:                                       unproved
```

Do not pursue (P.13) as the route theorem.  The corrected target is (Q.8) of
Proof 217, with the full `ell_CC20` multiplier acting on `g=L xi` and the
ordinary compact remainder acting on `xi`.
