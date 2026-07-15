# Proof 258: Covariant prolate cancellation

Date: 2026-07-15

Status: exact rejection of separate estimates for Proof 257's transported
base-prolate and second-boundary branches, followed by an exact covariant
diagnostic.  Even after scalar normalization makes the metric at least the
identity and the transport preserves the second support subspace, the two
endpoint branches can have arbitrarily large equal norms and cancel exactly.

Kato parallel transport carries the current second-support leakage from the
base prolate owner without this unstable split.  Proof 259 shows that the
leakage records only the `Q`-corner and cannot own the complete route trace.
The Kato and Duhamel identities below remain exact diagnostics; the proposed
leakage seminorm is retired as the active bottom.  No Lean owner or route
rewire is authorized, and RH remains unproved.

## 1. Result first

```text
+---------------------------------------------+------------------------------+
| object                                      | verdict                      |
+---------------------------------------------+------------------------------+
| T Q B and [Q,T]B endpoint identity          | exact                        |
| separate endpoint branch estimates          | rejected by exact C^2 model  |
| orthogonal band Kato generator              | exact                        |
| Kato unitary transport of B_0 to B_t        | exact                        |
| covariant leakage C_t=Q U_t B_0             | exact Q-corner diagnostic    |
| base prolate owner as initial condition     | retained                     |
| raw T_t amplification of base prolate tail  | removed from active owner    |
| compact-root Duhamel estimate               | retired as route bottom      |
| RH                                          | unproved                     |
+---------------------------------------------+------------------------------+
```

The route correction is

```text
Q U_t
 =(Q-R_t)[T_tQ B+[Q,T_t]B]Sigma_t^(-1/2)
                 |
                 X  never estimate the two terms separately
                 |
                 v
C_t=Q mathcalU_t B
                 |
                 +-- initial value Q B = base prolate owner
                 +-- complete Kato boundary flow
                 |
                 v
Q-corner diagnostic; not the complete route trace.                (U.1)
```

## 2. Exact cancellation counterexample

Work on `C^2`.  Let

```text
Q=|e_1><e_1|,
b_kappa=(kappa e_1+e_2)/sqrt(1+kappa^2),
B_kappa=|b_kappa><b_kappa|,

T_kappa=[1  -kappa]
        [0     1  ].                                  (U.2)
```

`Ran(Q)` is invariant under `T_kappa`.  Multiply `T_kappa` by the reciprocal
of its smallest singular value.  This scalar changes no transported range and
ensures

```text
T_kappa* T_kappa>=I.                                  (U.3)
```

The scalar also cancels from every normalized frame below.  Directly,

```text
T_kappa b_kappa=e_2/sqrt(1+kappa^2).                  (U.4)
```

Hence the normalized transported band vector is `u_kappa=e_2`, and

```text
Q u_kappa=0.                                          (U.5)
```

Now split the left side using Proof 257's endpoint identity.  After the same
Gram normalization,

```text
T_kappa Q b_kappa Sigma_kappa^(-1/2)
 =+kappa e_1,

[Q,T_kappa]b_kappa Sigma_kappa^(-1/2)
 =-kappa e_1.                                         (U.6)
```

Thus

```text
norm(base branch)=kappa,
norm(boundary branch)=kappa,
norm(complete leakage)=0.                             (U.7)
```

The ratio between a separate majorant and the real object is unbounded.  This
counterexample satisfies the exact structural assumptions which the old
estimate intended to use:

```text
Q-invariant invertible transport;
normalized metric at least the identity;
orthogonal transported band;
contractive complete leakage.                        (U.8)
```

Therefore the high-prolate/second-boundary split from Proof 257 is an exact
source decomposition but not an admissible triangle inequality.  The proposed
standalone high-mode estimate in Proof 257 must be used only inside an
organization which preserves the sum.

## 3. Kato transport of the band

Let `P_t=B_t` be the differentiable orthogonal band projection from Proof 257.
Differentiate `P_t^2=P_t` to obtain

```text
P_t P_t' P_t=0.                                       (U.9)
```

Define the skew-adjoint Kato generator

```text
A_t=[P_t',P_t]=P_t'P_t-P_tP_t'.                      (U.10)
```

Using `(U.9)`,

```text
A_t*=-A_t,
[A_t,P_t]=P_t'.                                      (U.11)
```

Let the unitary `mathcalU_t` solve

```text
mathcalU_t'=A_t mathcalU_t,
mathcalU_0=I.                                         (U.12)
```

Equations `(U.11)--(U.12)` give

```text
P_t=mathcalU_t P_0 mathcalU_t*.                       (U.13)
```

This transport depends only on the orthogonal band path.  It contains no
choice of primal frame and no condition number of `T_t`.

## 4. Covariant leakage owner

Fix the base band `B=P_0` and define

```text
C_t=Q mathcalU_t B.                                   (U.14)
```

Its endpoint relation to the actual leakage is

```text
Q P_t=C_t mathcalU_t*,

C_t C_t*=Q P_t Q,                                    (U.15)

C_t* C_t
 =B mathcalU_t* Q mathcalU_t B.                       (U.16)
```

Thus `C_t` has exactly the singular values of the current operator `Q P_t`.
At the base point,

```text
C_0=Q B,                                              (U.17)
```

whose singular values are CC20's rapidly decaying `|lambda(n)|` from Proof
257.

Differentiating `(U.14)` gives the condition-number-free flow

```text
C_t'=Q A_t mathcalU_t B
    =Q[P_t',P_t]mathcalU_tB.                          (U.18)
```

Integration yields the exact Duhamel formula

```text
C_t
 =Q B+integral_0^t Q[P_s',P_s]mathcalU_sB ds.         (U.19)
```

The base prolate operator now appears only as the initial condition.  It is
never multiplied by a raw endpoint norm of `T_t`.

## 5. Insert the complete source flow

Proof 257 gives

```text
P_t'=B_t'=Y_t+Y_t*,

Y_t
 =(I-E_t)X_tB_t-R_tX_t*Q B_t.                        (U.20)
```

Substitute `(U.20)` into `(U.18)--(U.19)`.  Every evolution term is built from
the complete orthogonal band derivative.  The scalar part of `X_t` has already
cancelled in `(U.20)`, so it cannot reappear in the Kato generator.

This changes the quantitative problem from

```text
norm(T_t Q B)+norm([Q,T_t]B)                          (rejected)
```

to

```text
base prolate initial condition
  +integral of complete band crossings.               (U.21)
```

The initial condition may use CC20's explicit factorial tail without paying
the complete Euler condition number.  The evolution must remain recombined;
expanding `P_t'` into prime channels before root smoothing can still recreate
the insufficient `p^(-m/2)` sum.

## 6. Former root-smoothed target

Let `W=C_g* C_g` be the route detector associated with a compact smooth root.
The former proposal used the covariant leakage seminorm

```text
N_g(C)=norm(C_g C)_HS.                                (U.22)
```

and asked for

```text
N_g(C_t)
 <=N_g(QB)
   +integral_0^t
      norm(C_g Q[P_s',P_s]mathcalU_sB)_HS ds

 <=C (1+B)^d norm(g)_(H^s),                           (U.23)
```

uniformly in the visible finite set.  Proof 259 rejects `(U.23)` as a sufficient
route theorem.  It controls only `Q mathcalU_tB`, does not determine
`Tr(W(B_t-B_0))`, and supplies no second Hilbert--Schmidt factor.  It may remain
an auxiliary Q-corner estimate.

The death conditions remain:

```text
raw norm(T_t) or norm(X_t) appears:
  reject;

prime channels are bounded separately at p^(-m/2):
  reject;

complete source-owned Y_t factorization is polynomial in support:
  route survives.                                     (U.24)
```

## 7. Reproducible certificate

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/258_covariant_prolate_flow_probe.py
```

The exact branch guard reports:

```text
+----------+-------------+-----------------+----------+
| kappa    | base branch | boundary branch | complete |
+----------+-------------+-----------------+----------+
| 2        | 2           | 2               | 0        |
| 10       | 10          | 10              | 1.77e-15 |
| 100      | 100         | 100             | 0        |
| 10000    | 10000       | 10000           | 0        |
+----------+-------------+-----------------+----------+
```

The maximum branch identity error relative to the separated scale is
`8.65e-19`.

An independent nonzero Q-preserving nested flow reports:

```text
+--------------------------------------+-----------+
| check                                | error     |
+--------------------------------------+-----------+
| P_t P_t' P_t                         | 4.09e-16  |
| A_t*=-A_t                            | 0         |
| [A_t,P_t]=P_t'                       | 1.27e-15  |
| finite-difference P_t'               | 2.70e-9   |
| Kato unitarity                       | 8.55e-16  |
| mathcalU_t B mathcalU_t*=B_t         | 3.86e-16  |
| C_t C_t*=Q B_t Q                     | 3.65e-16  |
| fixed compression C_t*C_t            | 2.12e-16  |
+--------------------------------------+-----------+
```

The finite difference dominates the maximum.  The Kato and leakage identities
are at roundoff scale.

## 8. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| endpoint TQB+[Q,T]B identity                   | exact                    |
| separate endpoint branch estimates            | rejected exactly          |
| raw transported-prolate tail estimate          | retired                  |
| Kato band transport                            | exact                    |
| covariant leakage C_t                          | exact diagnostic         |
| CC20 prolate tail as C_0                       | retained                 |
| complete-flow Duhamel source                   | exact                    |
| root-smoothed covariant estimate (U.23)        | retired as route bottom  |
| full fixed-S Y_t trace-class legality          | closed by Proof 261      |
| two-HS factor norms as uniform estimator       | rejected by Proof 260    |
| signed uniform finite-S remainder bound        | open, Gate 3U            |
| negative-owner integrated smallness            | open                     |
| same-object finite-S trace identity            | open                     |
| Burnol all-zero identity                       | open                     |
| Lean owner or route rewire                     | none                     |
| RH                                             | unproved                 |
+------------------------------------------------+--------------------------+
```

Proof 258 prevents Proof 257's source decomposition from becoming another
catastrophic triangle inequality.  Proof 259 retains that guard and the exact
Kato algebra, but rejects `C_t` as the complete route-trace owner.  The active
object is the full lower crossing `Y_t`, with all three source branches
recombined.  Proof 260 permits a source-specific two-Hilbert--Schmidt
factorization as a fixed-`S` legality certificate, but rejects its positive
factor norms as the uniform estimator.  The quantitative owner is the signed
complete trace.  Proof 261 supplies the ordinary fixed-`S` trace legality.
