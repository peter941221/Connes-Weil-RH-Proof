# Proof 278: Burnol boundary Gram covariance

Date: 2026-07-15

Status: exact complementary-subspace reduction and finite-dimensional
certificate.  Burnol's finite-window projection formula turns the complete
Sonin Toeplitz covariance into one centered Gram defect on two copies of the
source interval.  The same scalar is the mixed logarithmic derivative of a
Jacobi complementary determinant.  The outer, second-support, and prolate
commutator branches recombine before the boundary reduction.  A zero-prolate
ownership guard rejects the stronger claim that every surviving covariance
term carries a truncated-Fourier factor.

This is the correct entry point for a source-relative continuous
Wiener--Hopf/BOGC factorization.  It does not prove the required continuous
trace domain, the `exp(-z/2)` Toeplitz covariance estimate, the passage of the
complete prime telescope through the boundary Gram, Gate 3U, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Burnol complement projection                  | exact                        |
| Sonin covariance as boundary Gram defect      | exact                        |
| covariance as mixed log-determinant jet       | exact                        |
| relative E/R ambient determinant cancellation | exact                        |
| plus/minus finite-window Gram diagonalization | exact                        |
| prolate spectrum from the truncated Fourier   | exact                        |
| outer/second/prolate commutator recombination | exact                        |
| prolate-only extra-factor mechanism           | rejected by exact guard      |
| even/two-boundary survivor at F_0=0            | nonzero in both test cohorts |
| continuous root-sandwiched trace domain       | open                         |
| source-relative continuous BOGC               | open                         |
| complete prime telescope through boundary     | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The ownership change is

```text
Sonin Toeplitz covariance on the whole carrier
  -> one finite-window Gram covariance
  -> one complementary Jacobi determinant
  -> prospective continuous Hankel product
  -X-> no branchwise trace-norm estimate.                    (AO.1)
```

## 2. Burnol's finite-window complement

Let `H` be the even whole-line source Hilbert space, let `P_0` be restriction
to the source interval `[-1,1]`, and put

```text
H_0=P_0 H,
F_0=P_0 Fourier P_0|H_0.                               (AO.2)
```

On `H_0 direct-sum H_0`, define

```text
A(u,v)=u+Fourier(v),

G=A* A
 =[[I,F_0],
   [F_0,I]].                                          (AO.3)
```

The truncated Fourier transform has norm strictly below one.  Hence `G` is
positive and invertible.  Burnol's Theorem 4 gives the orthogonal projection
onto the complement of the Sonin space.  In the notation above it is

```text
C:=I-R=A G^(-1) A*.                                   (AO.4)
```

Indeed `A G^(-1) A*` is self-adjoint, idempotent, and has range

```text
Ran(P_0)+Ran(Fourier P_0),                             (AO.5)
```

whose orthogonal complement is the space of functions whose source value and
Fourier transform both vanish on `[-1,1]`.

Primary source:

```text
Jean-Francois Burnol,
Sur les "Espaces de Sonine" associes par de Branges a la
transformation de Fourier,
Theorem 4, arXiv:math/0208121v1.
https://arxiv.org/abs/math/0208121
```

Burnol prints `(AO.4)` in its two plus/minus resolvent components.  Equation
`(AO.3)` is the same formula before diagonalizing the `2 x 2` Gram.

## 3. The boundary covariance identity

Let `W,H_z` be commuting self-adjoint multipliers.  Under Proof 261's
root-sandwiched trace-legality contract, the complete Sonin Toeplitz
semicommutator is

```text
S_R(W,H_z)
 :=Tr_H(R W(I-R)H_z R).                               (AO.6)
```

Insert `(AO.4)` and use rectangular trace cyclicity only on the completed
trace-class product:

```text
S_R(W,H_z)
 =Tr_H(R W A G^(-1) A* H_z R)

 =Tr_(H_0 direct-sum H_0)
    (G^(-1) A* H_z R W A).                            (AO.7)
```

Now substitute `R=I-A G^(-1)A*` inside the same scalar.  This proves

```text
S_R(W,H_z)
 =Tr_(H_0 direct-sum H_0)
   G^(-1)[
     A* H_z W A
     -A* H_z A G^(-1) A* W A
   ].                                                 (AO.8)
```

Equation `(AO.8)` is the new lowest exact owner.  Its two terms must remain
centered as displayed.  The first is the static boundary compression; the
second is the compressed boundary product found in Proof 277.  Their
difference, not either term, is the Sonin covariance.

The identity also recovers the two earlier forms:

```text
S_R(W,H_z)
 =Tr(T_(W H_z)^R-T_W^R T_(H_z)^R)

 =1/2 Tr([W,R]*[H_z,R]).                              (AO.9)
```

This does not apply a Hilbert--Schmidt norm to either commutator.  Proof 260's
zero-trace/positive-nuclear-mass guard therefore remains respected.

## 4. Complementary Jacobi determinant

First work in finite dimension.  Let `Q_R` be an isometry onto `Ran(R)` and
put

```text
Q_C=A G^(-1/2).                                       (AO.10)
```

For every invertible ambient operator `M`, Jacobi's complementary-minor
identity gives

```text
det_(Ran R)(Q_R* M Q_R)
 =det_H(M)
  det_(H_0 direct-sum H_0)(G^(-1)A* M^(-1)A).         (AO.11)
```

Take

```text
M_(s,t)=exp(sW+tH_z).                                 (AO.12)
```

Since `W` and `H_z` commute, the ambient determinant in `(AO.11)` has zero
mixed logarithmic derivative.  Differentiating the other two terms at the
origin gives

```text
partial_s partial_t log det_(Ran R)(Q_R* M_(s,t)Q_R)|_(0,0)

 =Tr(T_(W H_z)^R-T_W^R T_(H_z)^R)

 =partial_s partial_t
   log det(G^(-1)A* M_(s,t)^(-1)A)|_(0,0).            (AO.13)
```

Direct differentiation of the last line is exactly `(AO.8)`.  Thus the
boundary covariance is not merely analogous to a determinant jet: it is the
mixed first jet of the complementary Jacobi determinant.

There is a stronger nested form.  Since `R<=E`, apply `(AO.11)` to `E` and
`R` before taking their ratio.  Let `J_0:H_0 -> H` be source-window zero
extension.  The two ambient determinants cancel exactly:

```text
det_(Ran E)(Q_E* M Q_E)
--------------------------------
det_(Ran R)(Q_R* M Q_R)

     det_(H_0)(J_0* M^(-1)J_0)
 = -------------------------------------.          (AO.13a)
   det_(H_0 direct-sum H_0)
     (G^(-1)A* M^(-1)A)
```

At `M_(s,t)=exp(sW+tH_z)`, the mixed logarithmic derivative is

```text
partial_s partial_t log(left side of AO.13a)|_(0,0)
 =S_E(W,H_z)-S_R(W,H_z)

 =1/2[D_E(W,H_z)-D_R(W,H_z)].                       (AO.13b)
```

The same derivative on the right side gives the difference of the one-copy
outer boundary covariance and the two-copy Burnol boundary covariance.
Equation `(AO.13a)` is the exact finite-dimensional cancellation which a
continuous relative theorem must preserve.  It is stronger than separately
writing two complementary formulas because no ambient determinant remains.

In infinite dimension `det_H(M)` is not route-legal.  Proof 267 avoids it by
forming the relative quotient between the `E` and `R` determinant lines.
Equation `(AO.13)` identifies the Burnol finite-window coordinate on which a
continuous relative BOGC theorem must act.  It does not reinstate an ambient
determinant.

## 5. Plus/minus channels and the two-channel obstruction

The unitary block Hadamard transform diagonalizes `(AO.3)`:

```text
G
 ->diag(I+F_0,I-F_0).                                (AO.14)
```

The odd resolvent combination is

```text
(I+F_0)^(-1)-(I-F_0)^(-1)
 =-2F_0(I-F_0^2)^(-1).                               (AO.15)
```

If `lambda_n` are the signed truncated-Fourier eigenvalues, the nonzero
eigenvalues of the CC20 prolate correction are `lambda_n^2`.  The companion
certificate verifies this equality independently from `(AO.15)`.

Equation `(AO.15)` exposes a truncated-Fourier factor only in the odd
resolvent difference.  It does not imply that the complete centered bracket
`(AO.8)` lies in that channel.  In particular, the cancellation of all
identity-channel terms is false under the abstract Burnol projection algebra.

The certificate enforces this ownership boundary with a second exact model.
Its Fourier surrogate exchanges the source window with a disjoint copy, so

```text
F_0=0,
K_prol=E E_hat E-R=0.                                (AO.15a)
```

Nevertheless, generic commuting self-adjoint `W,H` give

```text
default:   |S_R(W,H)|=1.895109,
           |S_E(W,H)-S_R(W,H)|=0.5740917;

alternate: |S_R(W,H)|=2.079365,
           |S_E(W,H)-S_R(W,H)|=0.5070580.            (AO.15b)
```

Both values survive while the truncated-Fourier and prolate norms are exactly
zero in the model.  Thus a valid successor must retain two contributions:

```text
even/two-boundary channel
  + odd/prolate channel.                             (AO.15c)
```

Only the second channel visibly contains `(AO.15)`.  The missing half-power,
if available, must be proved for the complete relative determinant after both
channels recombine.  It cannot be charged solely to CC20's
super-exponentially decaying prolate spectrum.  Proof 278 therefore does not
infer the moving covariance tail from the static CC20 `epsilon` series.

## 6. Physical-branch recombination

Let

```text
E=I-P_0,
E_hat=Fourier E Fourier,
K_prol=E E_hat E-R.                                   (AO.16)
```

Then the source identity is

```text
R=E E_hat E-K_prol.                                   (AO.17)
```

For every bounded `H_z`, the Leibniz rule gives the complete commutator

```text
[R,H_z]
 =E E_hat[E,H_z]
  +E[E_hat,H_z]E
  +[E,H_z]E_hat E
  -[K_prol,H_z].                                      (AO.18)
```

The four displayed terms are the two outer orientations, the second-support
branch, and the prolate branch.  The certificate verifies that `(AO.18)`
recombines before insertion into `(AO.9)` and that its signed Dirichlet scalar
equals `(AO.8)`.  No norm of an individual branch is used.

## 7. BOGC boundary

Bufetov proves a continuous Hankel-product BOGC formula for the sine-process
under a half-Sobolev symbol contract:

```text
Alexander I. Bufetov,
The Expectation of a Multiplicative Functional under the Sine-Process,
arXiv:2412.20902v1.
https://arxiv.org/abs/2412.20902
```

Petrov proves a Jacobi/BOGC identity for oblique Hardy-space splittings:

```text
Leonid Petrov,
A Borodin-Okounkov-Geronimo-Case identity for tilted Toeplitz minors,
arXiv:2605.24976v1.
https://arxiv.org/abs/2605.24976
```

These results determine the architecture, not the theorem needed here.
Petrov assumes an ambient BOGC operator `I-K` with `K` trace class.  The
route's almost-periodic Euler multiplier does not satisfy that assumption.
Bufetov treats the ordinary sine projection, not the relative `E/R` Burnol
boundary.

The next legal target is therefore a source-specific theorem of the form

```text
relative Jacobi quotient from Proof 267
  =Fredholm determinant of a completed Burnol-boundary Hankel product,
                                                                  (AO.19)
```

where the right side is trace class only after the `E/R` subtraction and the
compact root have been inserted.  Differentiating `(AO.19)` must reproduce
`(AO.18)` exactly.  If it drops any one of the four terms, it is not the route
owner.

## 8. Reproduction

Run in WSL2:

```text
python3 -B docs/proofs/278_burnol_boundary_gram_covariance_probe.py

python3 -B docs/proofs/278_burnol_boundary_gram_covariance_probe.py \
  --size 34 --support-rank 8 --seed 2278
```

The default certificate reports

```text
maximum exact algebra error             3.27e-15,
Jacobi complementary determinant error  3.22e-15,
relative E/R determinant error           9.83e-17,
boundary covariance error               8.62e-16,
mixed log-determinant derivative error  5.72e-8,
relative mixed-derivative error          1.05e-8,
three-branch commutator error            3.95e-16.
```

Its zero-prolate guard reports

```text
truncated Fourier norm                   0,
prolate correction norm                  0,
Sonin covariance magnitude               1.895109,
relative E/R covariance magnitude        0.5740917.
```

The mixed derivative is evaluated by a centered finite difference; all other
reported identities are direct matrix equalities.  The random transform is a
self-adjoint unitary surrogate for the even Fourier transform.  It preserves
the pair-of-projections and Gram algebra but does not estimate a continuous
Fourier kernel.

## 9. Route judgment

Proof 278 closes the exact algebraic Gate G0 for the base Sonin covariance:
there is one named finite-window Gram owner, one complementary determinant,
and one recombined physical commutator.  It does not close the analytic or
uniform gates.

The active sequence is

```text
prove the root-sandwiched continuous version of (AO.8)
  -> separate but retain the even/two-boundary and odd/prolate channels
  -> derive the source-relative Hankel determinant (AO.19)
  -> differentiate and recover every term of (AO.18)
  -> keep the complete normalized Euler product inside that determinant
  -> telescope prime defects before the first absolute value
  -> prove the polynomial-support Gate 3U bound.                  (AO.20)
```

The decisive rejection guards are:

```text
if (AO.19) needs an ambient I+S1 Euler operator, reject it;

if its derivative does not reproduce (AO.18), reject it;

if it claims that F_0 or K_prol divides the complete covariance, reject it;

if the boundary Gram prevents the complete prime telescope, retain (AO.8)
but fall back to Proof 277 (AN.13) plus Proof 273's signed renewal.          (AO.21)
```

Gate 3U, the same-object finite-S arithmetic identity, negative-owner
integration, Burnol's all-zero identity, and RH remain open.  No Lean owner or
route consumer is changed.
