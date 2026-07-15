# Proof 265: Causal boundary numerator and signed renewal gate

Date: 2026-07-15

Status: exact one-sided causal representation of Proof 264's ordered Gram
response.  After centering the Gram numerator, every detector occurrence lies
in the outer-half-line crossing or the Sonin crossing before the common killed
covariance is inverted.  Normalizing the Euler inverse to a contraction gives
a fixed-`S` signed renewal series.

The renewal series is not a uniform estimate.  Its termwise trace-norm sum
contains the inverse lower bound and is forbidden.  Gate 3U now asks for a
compact-support stopped-renewal or determinant argument for the complete signed
series.  No finite-`S` sign, same-object arithmetic identity, Burnol identity,
Lean owner, route rewire, or RH proof is claimed.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| fixed-S endpoint trace legality                | closed by Proof 261          |
| ordered causal Gram response                   | exact by Proof 264           |
| centered Gram numerator                        | exact                        |
| outer-minus-Sonin boundary factorization       | exact                        |
| compact-root support before covariance inverse | explicit                     |
| normalized killed covariance                   | positive contraction         |
| fixed-S signed renewal expansion               | exact, trace-norm convergent |
| termwise absolute renewal estimate             | rejected                     |
| uniform stopped-renewal estimate               | open, active Gate 3U         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Put

```text
A=T_S^(-1),
K=E A B,
Gamma=K* K=B A* E A B,
W=W_(eta,xi)=C_xi* C_eta.                            (AB.1)
```

Proof 264 gives

```text
Q_S(eta,xi)
 =Tr_B(K* W K Gamma^(-1)-W_B),

W_B=B W B.                                            (AB.2)
```

Define the centered numerator

```text
N_W=K* W K-W_B Gamma.                                 (AB.3)
```

Then the exact active owner is

```text
Q_S(eta,xi)=Tr_B(N_W Gamma^(-1)).                     (AB.4)
```

The order in `(AB.3)` is essential.  Replacing `W_B Gamma` by `Gamma W_B`
separates off the similarity trace anomaly rejected by Proof 264.

## 2. Exact boundary factorization of the numerator

Use the source projections

```text
R<=E,
B=E-R,
C=I-E.                                                (AB.5)
```

The root product `W` commutes with `A` and `A*`.  Expand `(AB.3)`:

```text
N_W
 =B A* E W E A B-B W B A* E A B.                    (AB.6)
```

Add and subtract `B A* W E A B`.  The first difference is

```text
B A*(E W E-W E)A B
 =-B A* C W E A B.                                    (AB.7)
```

For the second difference, commute `W` through `A*`:

```text
B A* W E A B-B W B A* E A B
 =B W(I-B)A* E A B.                                   (AB.8)
```

Proof 256's causal orientation gives

```text
C A* E=0.                                             (AB.9)
```

Since `I-B=C+R`, only the Sonin block remains in `(AB.8)`.  Therefore

```text
N_W
 =-B A* C W E A B
   +B W R A* E A B.                                  (AB.10)
```

Both detector factors are completed source crossings:

```text
C W E=C[W,E]E,
B W R=B[W,R]R.                                        (AB.11)
```

Substitution gives the commutator form

```text
N_W
 =-B A* C[W,E]E A B
   +B[W,R]R A* E A B.                                (AB.12)
```

Equation `(AB.12)` is the main move.  The paired outer-minus-Sonin detector
geometry is exposed before `Gamma^(-1)`.  No coframe, Sonin graph, Kato path,
Euler generator, or separately conditioned inverse remains.

The first branch is not an error term.  In the specialization `R=0,B=E`, the
entire response reduces to that branch, and Proof 222 identifies its trace with

```text
-log(p) sum_(m>=1)p^(-m/2)
  [F(m log(p))+F(-m log(p))].                         (AB.12a)
```

This is the genuine finite-prime boundary series.  The purpose of the second
branch and the complete renewal is to control its same-object Sonin
counterpart, not to discard `(AB.12a)` as a trace anomaly.

For roots supported in `[-B_root,B_root]`, the convolution kernel inside both
source commutators has displacement support in

```text
[-2B_root,2B_root].                                   (AB.13)
```

The raw Sonin commutator is nonlocal.  Insert the decomposition

```text
R=E E_hat E-K_prol                                   (AB.14)
```

in the second crossing before using `(AB.13)`.  It replaces that commutator by
three outer/scattering-conjugate half-line commutators with the same
displacement ledger plus a prolate trace-class commutator.  Those branches must
remain paired with the first crossing through the common factors in
`(AB.12)`.

## 3. Fixed-S trace legality

For compact smooth cross roots, Proof 261 gives

```text
C_eta(B_S-B)C_xi* in S1.                              (AB.15)
```

It also proves

```text
[C_eta,E], [C_eta,R], [C_eta,B] in S1,
```

and the companion statements for `C_xi*`.  All remaining factors in
`(AB.12)` are bounded for fixed finite `S`.  Thus `(AB.4)` is the same ordinary
relative trace licensed by Proofs 261--264.  The formula does not define the
bare traces of either summand in `(AB.2)`.

## 4. Normalize the causal inverse

Use Proof 253's scalar gauge and replace `A` by

```text
Atilde_S
 =product_(p in S)
    (1-p^(-1/2))(I-p^(-1/2)U_(log p))^(-1).           (AB.16)
```

This positive scalar change does not change `(AB.2)`: both `K*WK` and `Gamma`
receive the same scalar square.  The normalized inverse is a contraction and
has the probability representation

```text
Atilde_S
 =E[U_(X_S)],

X_S=sum_(p in S) N_p log(p),
P(N_p=n)=(1-p^(-1/2))p^(-n/2).                        (AB.17)
```

Hence

```text
0<Gamma<=B.                                           (AB.18)
```

The strict lower bound in `(AB.18)` is only a fixed-`S` statement.  It follows
because the causal Toeplitz block `E Atilde_S E` has the bounded inverse
`E Atilde_S^(-1)E` and `K` is its restriction to `Ran(B)`.  The lower bound is
not uniform in `S`.

## 5. The signed renewal identity

Put

```text
Delta=B-Gamma.                                         (AB.19)
```

For fixed finite `S`, equations `(AB.18)--(AB.19)` give

```text
0<=Delta<B,
norm(Delta)<1,

Gamma^(-1)=sum_(k>=0) Delta^k                          (AB.20)
```

in operator norm on `Ran(B)`.  Since `N_W` is trace class under the smoothed
fixed-`S` contract, multiplication gives the trace-norm convergent identity

```text
Q_S(eta,xi)
 =sum_(k>=0) Tr_B(N_W Delta^k).                        (AB.21)
```

This is the exact signed renewal owner requested by Proof 263.  The first
factor in every term is the completed boundary difference `(AB.12)`.

The defect itself has the positive decomposition

```text
Delta
 =B(I-A* A)B+B A* C A B.                              (AB.22)
```

The first term is the normalized ambient metric defect.  The second is the
killed outer-boundary covariance.  Both must stay inside the common renewal;
expanding them into separate prime words before compact support repeats the
mixed-prime failure from Proof 251.

## 6. Why the obvious bound is forbidden

Taking absolute values in `(AB.21)` gives only

```text
sum_(k>=0) norm(N_W Delta^k)_1
 <=norm(N_W)_1/(1-norm(Delta)).                       (AB.23)
```

The denominator in `(AB.23)` is the smallest eigenvalue of the killed
covariance in disguise.  It can contain the complete Euler condition number.
Thus `(AB.23)` is exactly the conditioned-inverse estimate eliminated by
Proofs 255--256.

The allowed order is

```text
boundary difference N_W
  -> compact displacement support
  -> complete signed renewal
  -> one absolute value.                              (AB.24)
```

The forbidden order is

```text
split outer/Sonin or prime channels
  -> take trace norms
  -> sum geometric inverse mass.                      (AB.25)
```

## 7. The remaining stopped-renewal theorem

The corrected Gate 3U contract is

```text
abs sum_(k>=0) Tr_B(N_(S,eta,xi) Delta_S^k)

 <=C(1+B_root)^d
      norm(eta)_(H^r) norm(xi)_(H^r),                 (AB.26)
```

with `C,d,r` independent of finite `S`.

A successful proof must use `(AB.17)` as a monotone path law and `(AB.13)` as
a stopping rule before any positive majorant.  The desired square-function
gain has the elementary summability target

```text
sum_(p<=exp(2B_root)) p^(-1)
 <=1+2B_root.                                          (AB.27)
```

Proof 251 shows why `(AB.27)` cannot be obtained by truncating the complete
product at degree two: fixed-separation mixed-prime curvature remains at the
half-power scale.  The entire renewal in `(AB.21)` must produce the connected
cancellation.

The first falsification test must retain the actual source pair and all three
branches from Proof 257:

```text
outer boundary
  + second-support boundary
  + prolate leakage.                                  (AB.27a)
```

Omitting `K_prol` is not a legal preliminary model.  Proof 258 gives an exact
`Q`-preserving guard in which the separated second-boundary and prolate-like
terms have norms `kappa` and `kappa` while their sum is zero, for arbitrary
`kappa`.  The same obstruction applies after multiplication by the common
renewal factor.  A falsification test may simplify the Euler law or the compact
root, but it must preserve `(AB.27a)` as one numerator before every absolute
value.

## 8. Determinant literature boundary

The ordered response has the formal relative determinant from Proof 264.  Two
source results explain why determinant language does not close `(AB.26)` by
itself:

```text
Elgart--Fraas, On Kitaev's determinant formula
https://arxiv.org/abs/2110.00599

  multiplicative commutators can have arbitrary nonzero determinant;
  determinant one follows under trace-class products of both deviations and
  their adjoint counterparts;

Migler, Functional calculus and joint torsion of pairs of almost commuting
operators
https://arxiv.org/abs/1409.6289

  Hardy Toeplitz joint torsion is computed from tame symbols and
  Helton--Howe--Pincus boundary integrals under its Fredholm/Schatten premises.
```

The route has trace-class compact-root commutators, not the deviation-product
premises of the Kitaev theorem.  Migler's formula treats one Hardy Toeplitz
compression, not the ordered Sonin-band covariance `Gamma` in `(AB.1)`.
Applying
either result separately to the outer and Sonin terms would violate
`(AB.24)`.  A new relative determinant theorem for the complete owner may still
be useful, but its domain and its outer-minus-Sonin factorization must be
proved.

## 9. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/265_causal_boundary_renewal_probe.py
```

The default normal finite model reports

```text
boundary numerator error       7.33e-16
commutator numerator error     7.46e-16
direct endpoint error          2.09e-16
renewal final operator error   4.41e-16.               (AB.28)
```

Its covariance lower bound is `0.6681371` and
`norm(Delta)=0.3318629`.  The signed renewal response converges as follows:

```text
+-------+-------------+-------------+
| power | response    | operator err|
+-------+-------------+-------------+
|     0 | 0.0862381   | 1.63e-2     |
|     1 | 0.103903    | 4.47e-3     |
|     2 | 0.107810    | 1.32e-3     |
|     4 | 0.108970    | 1.28e-4     |
|     8 | 0.109056    | 1.41e-6     |
|    16 | 0.109057    | 1.96e-10    |
|    32 | 0.109057    | 4.41e-16    |
+-------+-------------+-------------+
```

Finite matrices certify the ordering, boundary numerator, and renewal algebra.
Their geometric convergence rate is not evidence for an `S`-uniform lower
bound; the source proof must use signed stopping instead.

## 10. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Gate 3L fixed-S trace legality                 | closed by Proof 261          |
| causal Gram endpoint                           | exact by Proof 264           |
| completed boundary numerator                  | exact                        |
| fixed-S signed renewal                        | exact                        |
| termwise trace-norm renewal                   | rejected                     |
| determinant shortcut from existing literature | no matching contract         |
| uniform stopped-renewal bound (AB.26)         | open, Gate 3U                |
| negative-owner integrated smallness            | open                         |
| same-object finite-S trace identity            | open                         |
| Burnol all-zero identity                       | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 265 supplies the exact one-sided causal representation left open by
Proof 263.  It also identifies the remaining danger precisely: the complete
signed renewal must be bounded using physical compact support, while its
killed-covariance inverse is never estimated as a positive geometric series.
