# Proof 369: corrected normalized-covariance bottom

Date: 2026-07-18

Status: exact positive-operator form of the boundary-corrected quotient
crossing from Proof 368.  The old transported crossing is governed by the
shorted quotient metric, while the compression correction contributes two
mandatory mixed covariance terms and one correction square.  Their complete
sum is the new Douglas owner.

This replaces Proof 364 `(NP.8)` as the active near Gate 3U theorem.  It
closes the carrier and covariance audit but not the required uniform
domination by the compact-root common envelope.  Gate 3U, the finite-`S`
sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| quotient moving projection                    | exact Gram correction    |
| transported old-crossing covariance           | shorted metric           |
| compression-correction covariance              | exact                    |
| two mixed covariance terms                     | mandatory               |
| complete corrected Douglas owner               | exact                    |
| common-envelope uniform domination             | open, active near bottom|
| finite certificate                             | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Quotient metric

Retain Proof 368's notation on `E H`:

```text
P_K=U_0 U_0*,
R=E-P_K,
A=A_j,
G=A* A,
H=U_0* G U_0.                                     (NC.1)
```

The normalized moving frame and projection are

```text
V=A U_0 H^(-1/2),
P_A=V V*=A U_0 H^(-1)U_0* A*.                     (NC.2)
```

Define the quotient shorted metric on `Ran(R)` by

```text
S_A
 =R(G-G U_0 H^(-1)U_0*G)R
 =R A*(E-P_A)A R.                                  (NC.3)
```

If `A` is invertible on `E H`, block inversion also gives

```text
S_A=(R G^(-1)R)^(-1) |_Ran(R).                    (NC.4)
```

Equations `(NC.3)--(NC.4)` identify the old crossing's metric exactly.  They
do not assert a uniform lower bound for `H` or `S_A`.

## 3. Boundary-corrected numerator

Put

```text
F=-[W_E,R]U_0,
C=[W_E,A]U_0.                                      (NC.5)
```

Then `F=R W_E U_0` has range in `Ran(R)`, and Proof 368 gives

```text
Y U_0=A F+C,
Y=-A[W_E,R]+[W_E,A].                               (NC.6)
```

The actual moving quotient crossing is

```text
D=(E-P_A)(A F+C)H^(-1/2).                         (NC.7)
```

## 4. Complete covariance

Taking the adjoint product in the displayed order gives

```text
D*D
 =H^(-1/2)(
    F* A*(E-P_A)A F
   +F* A*(E-P_A)C
   +C*(E-P_A)A F
   +C*(E-P_A)C
  )H^(-1/2).                                      (NC.8)
```

The first term uses the shorted metric:

```text
F* A*(E-P_A)A F=F* S_A F.                         (NC.9)
```

Equivalently, without splitting the signed physical bracket,

```text
D*D
 =H^(-1/2)U_0*Y*(E-P_A)Y U_0 H^(-1/2).           (NC.10)
```

Equation `(NC.10)` is the preferred owner.  Equation `(NC.8)` exposes why
the correction cannot be appended only as a positive error square: its two
mixed terms can have either sign and are part of the same-object
cancellation.

## 5. Uniform pre-Gram budget

After Markov normalization, `norm(A)<=1`.  Proof 367 and the fixed source
commutator give

```text
norm(Y)_2
 <=norm([W_E,R])_2+2 norm([W,E])_2.                (NC.11)
```

This proves a uniform Hilbert--Schmidt budget before `H^(-1/2)`.  It is not a
Gate estimate: multiplying `(NC.11)` by `norm(H^(-1/2))` would restore the
complete Euler condition number.

## 6. Correct Douglas theorem

Let `A_L` be the common compact-root near envelope on the same fixed source
coordinate.  By Proof 360, the required factorization of the literal
corrected row is equivalent to

```text
H_j^(-1/2) U_0* Y_j* (E-P_j)Y_j U_0 H_j^(-1/2)

 <=C^2(1+L+B_root)^(2d) A_L* A_L,                  (NC.12)
```

where

```text
Y_j=-A_j[W_E,R]+[W_E,A_j],
[W_E,A_j]=E[W,E]V_jE+EV_j[W,E]E.                  (NC.13)
```

The mandatory kernel test is

```text
ker(A_L) subset
 ker((E-P_j)Y_jU_0H_j^(-1/2)).                    (NC.14)
```

Equations `(NC.12)--(NC.14)` replace Proof 364 `(NP.8)--(NP.10)`.  They
retain the quotient boundary correction, both mixed covariance terms, the
complete Gram normalization, and the physical outer/second/prolate signs.

## 7. What remains analytic

The remaining theorem is no longer an abstract prefix-conditioning question.
It is a real-line boundary observability statement:

```text
compact root invisible in the common near envelope
  -> complete corrected quotient response vanishes;

visible boundary energy
  -> corrected normalized response is polynomially bounded,
     uniformly in the finite Euler prefix.          (NC.15)
```

The only available structure strong enough to prove `(NC.15)` is the actual
one-sided renewal kernel together with the Burnol shorted metric.  A generic
contraction, ambient commutation, or an estimate of either diagonal term in
`(NC.8)` cannot prove it.

## 8. Reproducible certificate

The companion finite probe checks

```text
the shorted identities `(NC.3)--(NC.4)`;
the corrected moving crossing `(NC.7)`;
the unsplit covariance `(NC.10)`;
the four-term expansion `(NC.8)`;
nonzero mixed covariance omitted by diagonal-only bounds. (NC.16)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/369_corrected_normalized_covariance_bottom_probe.py
```

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 358/364 carrier audit                    | repaired                 |
| shorted old-crossing metric                    | exact `(NC.3)`           |
| correction and mixed covariances               | exact `(NC.8)`           |
| corrected Douglas owner                       | exact `(NC.12)`          |
| real-line observability `(NC.12)`              | open, active near bottom|
| Proof 359 harmonic consumer                    | ready after `(NC.12)`   |
| Proof 336 far lane                             | retained                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
