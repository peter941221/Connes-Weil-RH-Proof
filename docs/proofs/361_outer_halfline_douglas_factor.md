# Proof 361: outer half-line Douglas factor

Date: 2026-07-18

Status: exact common-window factorization and Douglas domination for the
compact-root outer half-line detector crossing.  Compact root support forces
the intermediate convolution variable into one fixed interval before any
Hilbert--Schmidt norm is taken.

This closes Proof 360's domination criterion for the outer source branch.  It
does not close the scattering-conjugate second support, the prolate branch, or
the complete moving quotient.  Gate 3U, the finite-`S` sign, Burnol's identity,
and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| compact-root outer crossing                   | exact window factor       |
| intermediate window                           | [-B,B]                   |
| right factor                                  | Hilbert--Schmidt          |
| left factor norm                              | <= convolution norm       |
| Douglas covariance domination                 | exact                     |
| scattering-conjugate branch                   | unaudited, next batch    |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
## 2. Setup

Let

```text
H=L2(R),
E=1_[0,infinity),
E_-=I-E.                                            (OH.1)
```

Let `g in L1(R) intersection L2(R)` satisfy

```text
supp(g) subset [-B,B],  B>=0,                       (OH.2)
```

and let `C_g` be whole-line convolution by `g`.  Define the positive detector

```text
W_g=C_g* C_g.                                       (OH.3)
```

The outer detector crossing is

```text
D_out=E_- W_g E.                                    (OH.4)
```

## 3. Intermediate-window localization

The integral kernel of `(OH.4)` is, for `x<0<=y`,

```text
K(x,y)=integral_R conjugate(g(z-x))g(z-y)dz.         (OH.5)
```

If the integrand in `(OH.5)` is nonzero, compact support gives

```text
z in [x-B,x+B],
z in [y-B,y+B].                                     (OH.6)
```

Since `x<0<=y`, equations `(OH.6)` imply

```text
-B<=z<=B.                                           (OH.7)
```

Let `E_B=1_[-B,B]`.  Inserting this projection into the intermediate
convolution variable changes no kernel value:

```text
D_out=E_- C_g* E_B C_g E.                           (OH.8)
```

Equation `(OH.8)` is an operator identity on the continuous `L2` carrier.  It
is not a trace-cycle identity.

## 4. Explicit Douglas factor

Set

```text
A_out=E_B C_g E,
B_out=E_- C_g* E_B.                                 (OH.9)
```

Then

```text
D_out=B_out A_out,                                  (OH.10)
norm(B_out)<=norm(C_g).                             (OH.11)
```

Proof 360 now gives the positive operator domination

```text
D_out*D_out
 <=norm(C_g)^2 A_out*A_out.                         (OH.12)
```

In particular, `ker(A_out) subset ker(D_out)` is proved by the actual support
geometry, not postulated.

## 5. Hilbert--Schmidt budget

The right factor has kernel

```text
1_[-B,B](z) g(z-y) 1_[0,infinity)(y).               (OH.13)
```

Tonelli gives

```text
norm(A_out)_2^2
 <=integral_(z in [-B,B]) integral_R abs(g(z-y))^2 dy dz
 =2B norm(g)_2^2.                                   (OH.14)
```

Thus

```text
norm(D_out)_2^2
 <=2B norm(C_g)^2 norm(g)_2^2.                      (OH.15)
```

The estimate is polynomial in root support and independent of every finite
Euler set.

## 6. Relation to Proof 357

Proof 357 constructs a common envelope for a family of completed translated
boundary crossings.  Equation `(OH.8)` is its fixed-boundary atomic source:
the window is inserted between the two convolution roots, after the outer
crossing has forced the intermediate variable to be finite.

The forbidden alternative remains

```text
C_g E is Hilbert--Schmidt.                           (OH.16)
```

It is false by Proof 259.  Only `E_B C_g E` in `(OH.9)` is
Hilbert--Schmidt.

## 7. Exact remaining branches

The full fixed quotient commutator from Proof 358 also contains

```text
second-support/scattering terms involving [W_g,Q_f],
the fixed Burnol boundary term [W_g,Q_b],
the prolate commutator [W_g,K_prol].                 (OH.17)
```

Equation `(OH.12)` cannot simply be conjugated by an arbitrary unitary and
still use the same compact window: the conjugated root may lose finite
propagation.  The next batch audits the actual CC20 scattering relation before
claiming a second window factor.

## 8. Reproducible certificate

The companion zero-fill Toeplitz probe checks

```text
the exact matrix analogue of `(OH.8)`;
the factorization `(OH.10)`;
the Douglas inequality `(OH.12)`;
the discrete Hilbert--Schmidt budget `(OH.14)`.       (OH.18)
```

Run only in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/361_outer_halfline_douglas_factor_probe.py
```

The continuous proof is the support implication `(OH.6)--(OH.8)` plus
Tonelli.  The finite probe is an implementation certificate.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| outer branch kernel visibility                | closed `(OH.8)`          |
| outer Douglas domination                      | closed `(OH.12)`         |
| outer HS support cost                         | closed `(OH.14)`         |
| second support / Burnol / prolate              | still separate          |
| full quotient domination                      | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
