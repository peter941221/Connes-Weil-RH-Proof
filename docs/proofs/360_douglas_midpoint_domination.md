# Proof 360: Douglas midpoint domination criterion

Date: 2026-07-18

Status: exact reformulation of Proof 359's remaining bounded-factor producer
as one positive operator inequality on the common near-envelope domain.  The
factor `B_j` need not be guessed first: Douglas factorization makes its
existence and optimal norm equivalent to quadratic-form domination.

This sharpens the active theorem but does not prove the required domination
for the CCM24 quotient midpoint.  Gate 3U, the finite-`S` sign, Burnol's
identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 359 common-factor statement             | exact active owner       |
| bounded factor existence                       | Douglas equivalent       |
| optimal factor norm                            | least domination constant|
| common-envelope kernel condition               | explicit                |
| trace/HS norm alone                             | insufficient            |
| route quadratic-form domination                | open                    |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
## 2. Common-domain Douglas theorem

Let

```text
A:X->Y,
D:X->Z.                                              (DG.1)
```

For `C>=0`, the following are equivalent:

```text
1. D=B A for some bounded B:Y->Z with norm(B)<=C;

2. D*D<=C^2 A*A;

3. norm(Dx)<=C norm(Ax) for every x in X.           (DG.2)
```

The implication `1 -> 2` is immediate.  For `3 -> 1`, define

```text
B_0(Ax)=Dx                                           (DG.3)
```

on `Ran(A)`.  The inequality makes `(DG.3)` well defined and bounded by `C`;
extend it continuously to `closure(Ran(A))` and set it to zero on the
orthogonal complement.  This is the common-domain form of Douglas's theorem,
equivalently obtained by applying the standard theorem to `D*` and `A*`.

The optimal factor norm is

```text
inf {C : D*D<=C^2 A*A}.                             (DG.4)
```

## 3. Apply it to Proof 359

Let

```text
A_L=A_(g,J_(L,B_root))                              (DG.5)
```

be Proof 357's boundary-localized common Hilbert--Schmidt envelope.  Let
`D_j` be the literal completed midpoint detector row after the Proof 358
physical commutator, prefix Gram normalization, and near restriction have
been kept whole.

Proof 359's remaining producer

```text
D_j=B_j A_L,
sup_j norm(B_j)<=C(1+L+B_root)^d                    (DG.6)
```

is equivalent to the family of operator inequalities

```text
D_j*D_j
 <=C^2(1+L+B_root)^(2d) A_L*A_L.                   (DG.7)
```

Equivalently, for every common source vector `x`,

```text
norm(D_j x)^2
 <=C^2(1+L+B_root)^(2d) norm(A_L x)^2.              (DG.8)
```

No Schatten norm, trace cycle, or prime sum occurs in `(DG.7)--(DG.8)`.
Those are applied only after the domination is proved.

## 4. Concrete envelope covariance

For `A_L=R_J C_g`,

```text
A_L*A_L=C_g* E_J C_g,                               (DG.9)
```

where `E_J` is the finite-window projection.  Thus the active near theorem is
the explicit covariance domination

```text
D_j*D_j
 <=C^2(1+L+B_root)^(2d) C_g*E_J C_g.               (DG.10)
```

Equation `(DG.10)` is a positive-kernel statement on one fixed source
carrier.  It is compatible with Proof 357's exact Hilbert--Schmidt square

```text
Tr(C_g*E_J C_g)=abs(J) norm(g)_2^2.                 (DG.11)
```

Once `(DG.10)` holds, Proof 359 takes the trace and prime weights without
further operator geometry.

## 5. Mandatory kernel test

Every domination `(DG.7)` implies

```text
ker(A_L) subset ker(D_j).                            (DG.12)
```

This is not cosmetic.  A small trace norm or Hilbert--Schmidt norm of `D_j`
does not imply `(DG.12)`.  In `C^2`, take

```text
A=diag(1,0),
D=diag(0,epsilon),  epsilon>0.                       (DG.13)
```

Then `norm(D)_2=epsilon` can be arbitrarily small, but no finite `C` satisfies
`D*D<=C^2 A*A` and no factorization `D=BA` exists.

For the route, `(DG.12)` says that the completed midpoint response must depend
only on root data visible inside the common boundary envelope.  Proving this
support statement is the first half of `(DG.10)`.

## 6. Why this is a better active theorem

The factor form `(DG.6)` hides two separate obligations:

```text
support/range:
  no response on ker(A_L);

size:
  bounded response relative to norm(A_L x).         (DG.14)
```

The quadratic form `(DG.8)` exposes both at once and can be attacked directly
from the real-line kernels.  It also prevents a tautological definition
`B_j=D_j A_L^dagger` unless the pseudoinverse is uniformly bounded on the
actual range.

The next source calculation should prove `(DG.10)` first for one completed
outer half-line commutator, then audit its scattering conjugate, and finally
return to the full signed quotient bracket.

## 7. Primary source

The factorization theorem used above is Theorem 1 of:

```text
R. G. Douglas,
On Majorization, Factorization, and Range Inclusion of Operators on
Hilbert Space,
Proceedings of the American Mathematical Society 17 (1966), 413--415.
https://home.agh.edu.pl/~rudol/Operat/DouglasFactorizationLemma.pdf
```

The paper states the equivalence of range inclusion, operator majorization,
and bounded factorization.  The route uses it only after all operators share
the concrete common envelope domain.

## 8. Reproducible certificate

The companion finite probe checks

```text
D=BA -> D*D<=norm(B)^2 A*A;
reconstruction of the reduced Douglas factor by a pseudoinverse;
equality of its norm with the generalized Rayleigh quotient;
the kernel-leak guard `(DG.13)`.                     (DG.15)
```

Run only in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/360_douglas_midpoint_domination_probe.py
```

The pseudoinverse is used only to verify finite matrices.  It is not proposed
as the infinite-dimensional Gate producer.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| HC.10 factorization                            | Douglas-equivalent       |
| common-envelope covariance                    | explicit `(DG.9)`        |
| kernel visibility requirement                 | explicit `(DG.12)`       |
| outer half-line domination                    | next calculation         |
| full quotient domination `(DG.10)`            | open, sole near bottom   |
| Proof 336 far lane                             | closed                   |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
