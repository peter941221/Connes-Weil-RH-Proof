# Proof 356: commuting-detector crossing transport

Date: 2026-07-18

Status: exact one-step transport formula for the surviving old-projection
detector crossing from Proof 355.  If the detector commutes with the invertible
Euler factor, the new crossing is produced only by the old crossing.  The
formula is scale invariant, but its individual Hilbert--Schmidt norm can be
amplified by the full one-step condition number; an exact two-dimensional
Euler-resolvent guard attains that amplification.

This rules out iterating one-step crossing norms.  It does not rule out a
single direct-sum/Bessel estimate for the complete sequential row.  Gate 3U,
the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| commuting detector crossing pullback          | exact                     |
| dependence on detector diagonal blocks         | cancels exactly          |
| scalar normalization of Euler factor           | cancels exactly          |
| one-step crossing amplification                | can reach condition no.  |
| condition-number-free iteration                | false                    |
| complete row Bessel estimate                   | open                     |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Frame setup

Let `V_0:H_0->H` be an isometry and put

```text
P_0=V_0 V_0*.                                       (CT.1)
```

Let `A:H->H` be bounded and invertible.  The Gram-normalized frame for the
transported range is

```text
G_0=V_0* A* A V_0,
V_1=A V_0 G_0^(-1/2),
P_1=V_1 V_1*.                                       (CT.2)
```

Let `W=W*` be bounded and assume

```text
[W,A]=0.                                            (CT.3)
```

The old and new detector crossings, written with isometric source
coordinates, are

```text
K_0=(I-P_0)W V_0,
K_1=(I-P_1)W V_1.                                   (CT.4)
```

## 3. Exact crossing transport

Using `(CT.2)--(CT.3)`,

```text
K_1
 =(I-P_1)W A V_0 G_0^(-1/2)
 =(I-P_1)A W V_0 G_0^(-1/2).                        (CT.5)
```

Split

```text
W V_0=P_0 W V_0+(I-P_0)W V_0.                      (CT.6)
```

The first term in `(CT.6)` is `V_0(V_0*WV_0)`.  Its image under `A` lies in
`Ran(A V_0)=Ran(P_1)` and is killed by `I-P_1`.  Therefore

```text
K_1
 =(I-P_1)A(I-P_0) K_0 G_0^(-1/2).                  (CT.7)
```

Equation `(CT.7)` proves that every apparent contribution of the diagonal
blocks `P_0WP_0` and `(I-P_0)W(I-P_0)` in a graph-coordinate expansion
cancels exactly when `[W,A]=0`.

## 4. Scale invariance

Replacing `A` by `cA`, `c!=0`, does not change `P_1`.  In `(CT.7)`,

```text
(I-P_1)(cA)(I-P_0)        contributes c,
[V_0*(cA)*(cA)V_0]^(-1/2) contributes 1/abs(c).      (CT.8)
```

The phase cancels because `V_1` is an isometric frame coordinate.  Thus the
crossing transport depends only on the projective action of `A`, exactly as
the Gram-corrected range projection does.

This cancellation does not imply a condition-number-free norm bound.

## 5. The sharp two-dimensional guard

Take

```text
H=C^2,
W=diag(0,1),
U=diag(-1,1),
A=(I-aU)^(-1),  0<a<1.                              (CT.9)
```

Then `[W,U]=[W,A]=0` and

```text
A=diag(1/(1+a),1/(1-a)),
kappa=(1+a)/(1-a).                                  (CT.10)
```

Let `P_theta` project onto `(cos(theta),sin(theta))`.  Its detector crossing
has the single singular value

```text
k(theta)=abs(sin(theta)cos(theta)).                 (CT.11)
```

Transport by `A` sends the slope `t=tan(theta)` to `kappa t`, so

```text
k(theta_new)/k(theta)
 =kappa(1+t^2)/(1+kappa^2 t^2).                     (CT.12)
```

Consequently

```text
lim_(theta->0) k(theta_new)/k(theta)=kappa.          (CT.13)
```

For the Euler coefficient `a=p^(-1/2)`, the sharp one-step amplification is

```text
kappa_p=(1+p^(-1/2))/(1-p^(-1/2)).                 (CT.14)
```

The `p=2` factor is about `5.828427`; for large `p`,
`kappa_p=1+2p^(-1/2)+O(p^(-1))`.  Multiplying these factors over primes is
precisely the forbidden half-power condition growth.

## 6. Consequence for Proof 355

The naive recursion

```text
norm(K_j)_2<=kappa_(p_j) norm(K_(j-1))_2            (CT.15)
```

is mathematically valid as a coarse estimate and analytically useless.  Its
product loses the prime-square gain before compact support can act.

The correct next theorem must apply `(CT.7)` to all steps at once and show
that the normalized maps

```text
K_0
 -> ((p_j-1)^(-1/2) K_(j-1) A_root)_j              (CT.16)
```

form a bounded observation row after the complete Julia/Gram
orthogonalization.  No product of the individual norms in `(CT.7)` may appear.

## 7. Reproducible certificate

The companion probe checks `(CT.2)--(CT.7)` for random commuting normal
Euler/detector data.  It separately evaluates `(CT.12)` at decreasing angles
and verifies convergence to `(CT.14)` for several primes.

Run only in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/356_commuting_detector_crossing_transport_probe.py
```

The unified WSL2 run reports maximum random-matrix identity error
`9.561142661822e-15`.  At angle `10^(-6)`, the `p=2` crossing-amplification
ratio is within `1.921680592432e-10` of the sharp condition number; the error
decreases for larger primes.

The random check certifies finite algebra.  The two-dimensional cohort is an
exact obstruction to a universal one-step contraction claim.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| new crossing depends only on old crossing     | exact `(CT.7)`            |
| diagonal detector terms                        | cancel by commutation     |
| scalar Euler normalization                     | irrelevant               |
| individual crossing contraction                | false `(CT.13)`          |
| direct-sum observation row `(CT.16)`           | open, active bottom      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
