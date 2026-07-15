# Proof 264: Causal Gram response and polar trace-anomaly guard

Date: 2026-07-15

Status: exact fixed-`S` reformulation of the Gate 3U endpoint response.  The
shorted covariance from Proof 255 is the Gram operator of one killed causal
Euler inverse.  Consequently the paired inverse-metric coframe and Sonin graph
in Proof 262 collapse, inside the legally smoothed relative trace, to one
asymmetric causal Gram response.

The tempting further replacement by the orthogonal polar isometry is not an
automatic infinite-dimensional trace identity.  An exact unilateral-shift
guard gives a positive invertible similarity whose trace-class difference has
nonzero trace.  Finite sections hide that mass by placing the opposite trace at
their artificial far boundary.  Therefore the active owner must retain the
Gram ordering, or prove a new source-specific anomaly cancellation theorem.

This proof does not establish the uniform polynomial-support bound, the
finite-`S` sign, the same-object arithmetic identity, Burnol's identity, or RH.
No Lean owner or route consumer is changed.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| fixed-S root-sandwiched trace legality         | closed by Proof 261          |
| covariance shorted over the preserved halfline| exact                        |
| shorted covariance = killed causal Gram        | exact                        |
| Sonin graph from covariance blocks             | exact                        |
| nested Schur inverse = inverse band covariance | exact                        |
| endpoint causal Gram response                  | exact                        |
| pure orthogonal-polar trace replacement        | false without extra theorem  |
| finite-section polar cycling                    | boundary-polluted guard      |
| relative Gram determinant                      | exact formal derivative      |
| determinant-domain theorem                     | open                         |
| uniform causal Gram bound                      | open, active Gate 3U         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The new fixed-`S` owner is

```text
Q_S(eta,xi)
 =Tr_B(K_S* W_(eta,xi) K_S (K_S* K_S)^(-1)
       -B W_(eta,xi) B),                                  (AA.1)

K_S=E T_S^(-1)B,
W_(eta,xi)=C_xi* C_eta.                                   (AA.2)
```

Equation `(AA.1)` is one relative trace.  Neither displayed summand is asserted
to be trace class by itself.  The order of `(K_S* K_S)^(-1)` in `(AA.1)` is
part of the theorem and must not be symmetrized by an unlicensed trace cycle.

## 2. Inputs already owned by the route

Use the source nested pair

```text
R<=E,
B=E-R,
C=I-E.                                                   (AA.3)
```

Let `T=T_S` be one normalized complete finite-`S` Euler transport and put

```text
H=T* T,
M=H^(-1),
A=T^(-1).                                                (AA.4)
```

The whole-line Euler convolution is normal.  The source orientation proved in
Proof 256 says that `Ran(C)` is invariant under both `A` and `A^(-1)=T`.
Normality allows the inverse metric to use the causal ordering

```text
M=A A*=A* A.                                             (AA.5)
```

Proof 255 supplies the Sonin graph, Schur operator, and inverse-metric coframe:

```text
L=(R H R)^(-1)R H B,
Z=B-RL,
Sigma=Z* H Z,

mathcalD=H Z Sigma^(-1).                                (AA.6)
```

Proof 256 supplies the one-sided coframe collapse

```text
mathcalD=T E A B.                                        (AA.7)
```

For compact roots, Proof 261 makes the endpoint difference trace class and
licenses the ordinary cyclicity used by Proofs 262--263.  No bare translated
projection trace is introduced here.

## 3. Shorted covariance is one causal Gram operator

Short `M` over the preserved complement `C`:

```text
S
 =E M E-E M C(C M C)^(-1)C M E.                        (AA.8)
```

Relative to `C direct-sum E`, invariance gives the triangular factor

```text
    [A_C  X]
A = [      ],                                            (AA.9)
    [ 0   A_E]
```

where `A_C` is invertible.  Using `M=A* A`, its blocks are

```text
C M C=A_C* A_C,
C M E=A_C* X,
E M E=X* X+A_E* A_E.                                   (AA.10)
```

The crossing square cancels exactly in `(AA.8)`:

```text
S=A_E* A_E=E A* E A E.                                 (AA.11)
```

Write `(AA.11)` in the decomposition `E=R direct-sum B` and define

```text
K=E A B.                                                 (AA.12)
```

Then

```text
S_BB=B S B=K* K,
S_RB=R A* E A B.                                        (AA.13)
```

This is a covariance identity, not a norm estimate.  In particular, no inverse
of `K* K` has been bounded.

## 4. The graph and Schur inverse are covariance identities

The block inverse formula for the decomposition `C direct-sum E` gives

```text
E H E=S^(-1).                                           (AA.14)
```

Writing `S` in `R/B` blocks and using the `R,B` block of
`S^(-1)S=I` gives

```text
L=-S_RB S_BB^(-1).                                      (AA.15)
```

The Schur complement of the `R/R` block of `S^(-1)` is the inverse of the
opposite covariance block:

```text
Sigma=S_BB^(-1)=(K* K)^(-1).                            (AA.16)
```

The coframe has the companion identities

```text
mathcalD* M mathcalD=S_BB,

Z=M mathcalD S_BB^(-1).                                (AA.17)
```

Equations `(AA.15)--(AA.17)` show that `L`, `Sigma`, `Z`, and `mathcalD` are
two coordinate descriptions of the same shorted covariance.  Estimating any
one of their inverses separately would discard this identity.

## 5. Exact collapse of the endpoint scalar

Proof 255's legally smoothed intrinsic endpoint owner is

```text
Q_S(eta,xi)
 =Tr_B(mathcalD*
   (W_(eta,xi) Z-Z B W_(eta,xi) B)).                    (AA.18)
```

Put `Gamma=K* K`.  Equations `(AA.7)`, `(AA.16)`, and `(AA.17)` give

```text
mathcalD=T K,
Z=T^(-*) K Gamma^(-1).                                 (AA.19)
```

The second identity uses normality:

```text
M T=T^(-*).                                             (AA.20)
```

Every legal root product `W_(eta,xi)` commutes with `T`, `T*`, and their
inverses.  Therefore

```text
mathcalD* W Z
 =K* T* W T^(-*) K Gamma^(-1)
 =K* W K Gamma^(-1).                                   (AA.21)
```

Also `mathcalD*Z=B`.  Substitution into `(AA.18)` proves `(AA.1)`.

This removes the explicit coframe `mathcalD`, graph `L`, source frame `Z`,
compressed `R H R` inverse, and outer Euler transport from the scalar owner.
All finite-`S` dependence is now inside one killed causal factor `K` and its
Gram normalization.

## 6. Why the pure polar replacement is not licensed

Let

```text
V=K(K* K)^(-1/2).                                      (AA.22)
```

Then `V*V=B`, but `(AA.1)` contains

```text
K* W K(K* K)^(-1)
 =(K* K)^(1/2)(V* W V)(K* K)^(-1/2).                  (AA.23)
```

In finite dimensions the trace of `(AA.23)` equals `Tr(V*WV)`.  In the source
space neither term is individually trace class.  A similarity difference can
be trace class and still have nonzero trace, so finite-dimensional cycling is
not a theorem here.

The guard is elementary.  On `ell2(N)`, let `S_+` be the unilateral shift and

```text
X=(S_++S_+*)/2,
Y=(S_+-S_+*)/(2i),
W_0=Y+2I>=I.                                            (AA.24)
```

For the first coordinate projection `P_0`,

```text
[S_+*,S_+]=P_0,
[X,Y]=P_0/(2i).                                         (AA.25)
```

Let `C_t=exp(tX)`, a positive bounded invertible operator.  Duhamel's formula
gives

```text
C_t W_0 C_t^(-1)-W_0
 =integral_0^t C_s[X,Y]C_s^(-1) ds in S1.              (AA.26)
```

Ordinary trace cyclicity applies to the rank-one integrand, so

```text
Tr(C_t W_0 C_t^(-1)-W_0)
 =t Tr([X,Y])
 =t/(2i)
 =-i t/2 !=0.                                          (AA.27)
```

Thus positivity of the similarity and positivity of the detector do not erase
the anomaly.  A source-specific theorem may still prove that the anomaly in
`(AA.23)` vanishes or is uniformly controlled, but abstract polar algebra does
not.

Finite unilateral-shift sections necessarily have total trace zero.  The
certificate shows what happens: the left boundary carries `-it/2`, the
artificial right boundary carries `+it/2`, and the middle is zero.  This is the
same finite-boundary mechanism which made the zero-fill models in Proof 256
unsuitable as global trace evidence.

The route's anomaly is not expected to vanish.  Set `R=0` and `B=E` in
`(AA.1)`.  Then `K=E A E` is the invertible causal Toeplitz block and the
ordered Gram response is exactly the outer-half-line endpoint response from
Proof 222.  For one prime, with

```text
a=p^(-1/2),
L=log(p),
```

Proof 222 computes

```text
Tr(C_F(E_a-E))
 =-L sum_(m>=1)a^m[F(mL)+F(-mL)].                    (AA.27a)
```

Thus the source similarity anomaly contains the genuine finite-prime boundary
channel.  A theorem setting it to zero would erase the arithmetic term.  Gate
3U must keep `(AA.27a)` paired with the Sonin response; it may not try to prove
the outer polar anomaly vanishes separately.

## 7. Relative determinant form

The ordering in `(AA.1)` has a natural determinant interpretation.  On
`Ran(B)`, put formally

```text
Gamma_0=K* K,
Gamma_s=K* exp(sW) K,
B_s=B exp(sW) B,

mathcalR_s=Gamma_s Gamma_0^(-1) B_s^(-1).             (AA.28)
```

Then `mathcalR_0=B` and

```text
partial_s mathcalR_s at s=0
 =K* W K(K* K)^(-1)-B W B.                            (AA.29)
```

If a successor proves

```text
mathcalR_s-B in S1
```

with trace-norm differentiability near zero, the Fredholm determinant gives

```text
Q_S(eta,xi)
 =partial_s log det(mathcalR_s) at s=0.                (AA.30)
```

Equation `(AA.30)` is not asserted here: its determinant-domain premise is the
new analytic work.  Unlike the determinant shortcut rejected in Proof 262,
`(AA.28)` contains one causal Gram operator rather than two separately
conditioned `E/R` Schur complements.  It is therefore worth a focused audit,
but invoking strong Szego theory without proving `(AA.28)` is still forbidden.

## 8. The corrected Gate 3U target

After the scalar normalization of Proof 253, the causal inverse is the Markov
average

```text
A_S
 =E[U_(sum_p N_p log(p))],

P(N_p=n)=(1-p^(-1/2))p^(-n/2).                        (AA.31)
```

For roots supported in `[-B_root,B_root]`, the active theorem is now

```text
abs Tr_B(K_S* W_(eta,xi) K_S (K_S* K_S)^(-1)
         -B W_(eta,xi) B)

 <=C(1+B_root)^d
      norm(eta)_(H^r) norm(xi)_(H^r),                 (AA.32)
```

uniformly in finite `S`.

The factor `K_S* K_S` must remain paired with the numerator.  Bounding its
inverse, replacing the relative trace by a positive trace norm, or cycling to
the polar isometry before proving anomaly cancellation recreates a rejected
condition-number argument.

The next sufficient mechanism is a stopped innovation or relative-determinant
identity which uses compact displacement support before taking an absolute
value.  A successful square-function estimate should expose squared Euler
weights:

```text
sum_(p<=exp(2B_root)) p^(-1)
 <=sum_(n<=exp(2B_root)) n^(-1)
 <=1+2B_root.                                           (AA.33)
```

Equation `(AA.33)` explains the desired polynomial support cost.  It is not a
proof that `(AA.32)` has such a square-function representation.

## 9. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/264_causal_gram_response_probe.py
```

The three algebra layers report maximum error

```text
2.61e-15.
```

They separately verify:

```text
generic Schur/shorted-covariance identities;
exact triangular causal factorization;
the direct, intrinsic, and causal-Gram endpoint responses
  on a finite normal reducing model.                            (AA.34)
```

At `t=0.7`, unilateral-shift sizes `32,64,96,128` report

```text
+------+-----------+-----------+-----------+-----------+
| size | left Im   | middle Im | right Im  | total     |
+------+-----------+-----------+-----------+-----------+
|   32 | -0.35000  | 0         | +0.35000  | 2.29e-14  |
|   64 | -0.35000  | 0         | +0.35000  | 1.78e-14  |
|   96 | -0.35000  | 0         | +0.35000  | 3.80e-14  |
|  128 | -0.35000  | 0         | +0.35000  | 8.64e-14  |
+------+-----------+-----------+-----------+-----------+
```

The infinite left-boundary value from `(AA.27)` is exactly `-0.35i`.  These
finite sections certify the compensation mechanism; they do not prove an
infinite trace by numerical convergence.

## 10. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Gate 3L fixed-S trace legality                 | closed by Proof 261          |
| endpoint two-commutator owner                  | replaced algebraically       |
| causal shorted covariance                      | exact                        |
| coframe/graph causal Gram collapse             | exact                        |
| pure polar response                            | rejected without anomaly gate|
| finite-section total-trace cycling             | misleading by exact guard    |
| relative causal Gram determinant               | narrowed, domain open        |
| uniform polynomial support bound (AA.32)       | open, Gate 3U                |
| negative-owner integrated smallness            | open                         |
| same-object finite-S trace identity            | open                         |
| Burnol all-zero identity                       | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 264 removes the explicit paired coframe and Sonin graph from the endpoint
scalar, but it also blocks an invalid simplification.  The active object is one
ordered relative Gram response for the killed one-sided Euler inverse.  Gate
3U now asks for a compact-support estimate of that object, or a source-realized
counterexample, before any polar cycling or determinant theorem is used.
