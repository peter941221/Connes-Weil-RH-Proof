# Proof 377: Cayley compact-root Sobolev budget

Date: 2026-07-18

Status: quantitative transfer from a compact smooth logarithmic convolution
root to Proof 376's Cayley coefficient functional.  The resulting estimate is
polynomial in the support radius and a fixed Sobolev norm.

Together with Proofs 375--376, this proves the open endpoint estimate `(MR.6)`.
Proof 378 assembles the detector row and audits the still-open same-object
root-split pairing.

## 1. Result

Let `g` be supported in `[-B,B]`, let

```text
c(s)=Fourier(g)(s),                                  (CS.1)
```

and transfer the real line to the circle by the Cayley boundary coordinate

```text
s=cot(theta/2),
c_C(e^(i theta))=c(s).                               (CS.2)
```

If `(c_n)` are the circle Fourier coefficients of `c_C`, then

```text
sum_(n !=0)sqrt(abs(n))abs(c_n)
 <=C(1+B)^2 norm(g)_(H^3(R)).                        (CS.3)
```

The exponents are not optimized.  Their purpose is a fixed polynomial ledger,
not a sharp Cayley embedding theorem.

## 2. Fourier coefficient reduction

By Cauchy--Schwarz,

```text
sum_(n !=0)sqrt(abs(n))abs(c_n)

 <=[
    sum_n(1+n^2)^2 abs(c_n)^2
   ]^(1/2)
   [
    sum_(n !=0)abs(n)/(1+n^2)^2
   ]^(1/2).                                         (CS.4)
```

The second factor is one finite universal constant.  By circle Plancherel, the
first factor is equivalent to `norm(c_C)_(H^2(T))`.

## 3. Cayley derivatives

Put

```text
a(s)=(1+s^2)/2.
```

Since `d/dtheta=-a(s)d/ds`, one has

```text
partial_theta c_C=-a c',                            (CS.5)

partial_theta^2 c_C
 =s(1+s^2)c'/2+(1+s^2)^2 c''/4.                    (CS.6)
```

Also

```text
dtheta=2 ds/(1+s^2).                                (CS.7)
```

Equations `(CS.5)--(CS.7)` give

```text
norm(c_C)_(H^2(T))
 <=C[
   norm(c)_2
  +norm((1+s^2)^(1/2)c')_2
  +norm(s(1+s^2)^(1/2)c')_2
  +norm((1+s^2)^(3/2)c'')_2].                       (CS.8)
```

The apparent Cayley singularity is paid for by the rapid decay of the Fourier
transform of a compact smooth root.

## 4. Return to the root

For `j,k>=0`, ordinary Fourier calculus gives

```text
s^k partial_s^j c(s)
 =Fourier[(-i partial_x)^k((-ix)^j g(x))](s),        (CS.9)
```

up to the fixed transform convention.  Plancherel and Leibniz therefore imply

```text
norm(s^k partial_s^j c)_2
 <=C_(j,k)(1+B)^j norm(g)_(H^k),                    (CS.10)
```

for the values `j<=2`, `k<=3` occurring in `(CS.8)`.  Substitution proves
`(CS.3)`.

No Euler parameter enters `(CS.3)`.

## 5. Endpoint commutator

Proof 376 and `(CS.3)` give, for every endpoint Sonin projection `R_j`,

```text
norm([C_g,R_j])_2
 <=C(1+B)^2 norm(g)_(H^3).                           (CS.11)
```

The outer half-line projection satisfies the same estimate, either by the
standard half-line kernel formula or by treating `H^2` as the trivial nearly
invariant space.  Since `P_j=E-R_j`,

```text
sup_j norm([C_g,P_j])_2^2
 <=C(1+B)^4 norm(g)_(H^3)^2.                         (CS.12)
```

Equation `(CS.12)` is Proof 373 `(MR.6)` with `d=4` and `r=3`.

## 6. Direct half-line check

In the real logarithmic coordinate, the two corners of `[C_g,E]` have kernels
on opposite sides of the boundary.  Tonelli gives, up to Fourier normalization,

```text
norm([C_g,E])_2^2
 =integral_R abs(x) abs(g(x))^2 dx
 <=B norm(g)_2^2.                                    (CS.13)
```

This agrees with the Cayley estimate and shows why compact root support, rather
than the raw whole-line root, is the correct finite-mass object.

## 7. Reproducible certificate

The companion probe uses compact cardinal B-spline roots with the exact
Fourier multiplier

```text
c_B(s)=sinc(Bs/m)^m.                                 (CS.14)
```

It samples the Cayley pullback, checks the coefficient Cauchy--Schwarz bound,
and inserts the multiplier against a transported nearly invariant projection
to verify Proof 376's `S_2` estimate.

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/377_cayley_compact_root_sobolev_probe.py
```

The numerical root is a certificate for the coordinate and constants.  The
continuous proof is `(CS.4)--(CS.10)`.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Cayley coefficient functional                 | polynomial root bound    |
| endpoint Sonin commutator                     | uniform in prefix        |
| quotient endpoint `(MR.6)`                    | closed `(CS.12)`         |
| explicit Euler Gram inverse                   | absent                    |
| near detector-row assembly                    | Proof 378                |
| same-object root-split pairing                | open                     |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
