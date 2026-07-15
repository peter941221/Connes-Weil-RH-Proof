# Proof 255: Nested shorting cancellation and dual-frame gate

Date: 2026-07-15

Status: exact replacement of the separate shorting-defect target by one
canonical polar owner and then by a stronger primal/dual-frame identity.  The
oblique phase and its positive shorting defect can both grow like the square of
the complete Euler condition while their difference remains the orthogonal
band projection.  Estimating either positive term separately is therefore
route-useless.

The polar isometry removes that numerical cancellation.  More importantly, a
contractive dual frame built from the inverse Markov metric cancels the outer
Euler transport exactly against the expanding primal frame for every legal
convolution detector.  The remaining object is one intrinsic boundary
intertwining pairing between two shorted frames.  Finite Sonin sections keep
this intrinsic object at order tens while the rejected phase terms reach
`10^11`.

This is not a continuous uniform bound, a finite-S sign, or an RH proof.  No
Lean owner or route rewire is authorized.

## 1. Result first

Proof 254 left the shorting defect

```text
B M C(C M C)^(-1) C M B                              (P.1)
```

as the lowest named obstruction.  Proof 255 shows that `(P.1)` must not be
treated as a separate positive target:

```text
+------------------------------------------+-------------------------------------+
| object                                   | verdict                             |
+------------------------------------------+-------------------------------------+
| oblique phase square                     | exact, can grow catastrophically    |
| positive shorting defect square          | exact, same catastrophic size       |
| phase minus defect                       | orthogonal band projection          |
| separate positive domination             | rejected as too lossy               |
| canonical polar isometry                 | exact, norm one                     |
| Sylvester response equation              | exact, no inverse-square-root loss  |
| inverse-metric dual frame                | exact contraction                   |
| primal/dual outer-transport cancellation | exact for convolution W             |
| intrinsic dual-frame boundary pairing    | open continuous theorem             |
+------------------------------------------+-------------------------------------+
```

The route move is

```text
shorting defect by itself
  -> phase and defect recombined
  -> canonical polar isometry
  -> primal/dual shorted frames
  -> intrinsic boundary intertwining pairing.                        (P.2)
```

Only the last line of `(P.2)` remains an analytic target.

## 2. Source-owned geometry

The source facts used to choose the nested pair are:

```text
CCM24, Zeta Zeros and Prolate Wave Operators
https://arxiv.org/html/2310.18423v2

  Definition 4.5:
    the local Sonin space imposes simultaneous support gaps on a function
    and its Fourier transform;

  Theorem 2:
    theta_S gives a Hilbert-space isomorphism from the archimedean Sonin
    space to the semilocal Sonin space;

  original TeX lines 946--981:
    the finite Euler factor is the actual Mellin multiplier;

  original TeX lines 983--1029:
    transport of the Sonin space;

  original TeX lines 1031--1073:
    one common vector space with the S-dependent Hilbert norm.
```

The same paper's equation `(6)` displays the semilocal spectral measure as the
square of the complete product of local factors.  It does not state a uniform
shorted-boundary estimate or the dual-frame identity below.

Proof 224 audited the support orientations.  One Hardy half-line is crossed by
the Euler transport, while the other support orientation is preserved.  Thus
the real source geometry can be written as one nested pair

```text
R <= E,
B=E-R,
C=I-E,                                                   (P.3)
```

where `R` is the Sonin intersection and `E` is the crossed half-line.  This is
not an invented replacement for the source Sonin space.

The boundary decomposition which a continuous proof must retain is owned by
CC20:

```text
CC20, Weil Positivity and Trace Formula, the Archimedean Place
https://arxiv.org/abs/2006.13771

  original TeX lines 542--548:    scattering conjugacy
  original TeX lines 960--984:    rapid prolate decay
  original TeX lines 1072--1103:  P P_hat P=R+K_prol
  original TeX lines 2087--2120:  legal smoothed boundary commutators.
```

All formulas from `(P.4)` onward are project derivations, not claims copied
from those papers.

## 3. The nested Schur frame

Let `T` be one normalized complete finite-S transport and put

```text
H=T* T,
M=H^(-1).                                               (P.4)
```

The scalar normalization of Proof 253 gives

```text
H>=I,
0<M<=I.                                                 (P.5)
```

All inverses below are inverses on the displayed compressed ranges.  Define

```text
A_R=R H R,
X=R H B,

Sigma=B H B-X* A_R^(-1) X,
Z=B-R A_R^(-1) X,
G=T Z.                                                  (P.6)
```

The column `Z b` is the unique vector `r+b` in `Ran(E)` whose image under `T`
is orthogonal to `T Ran(R)`.  Direct multiplication gives

```text
G* T R=0,
G*G=Sigma.                                              (P.7)
```

Therefore the orthogonal transported band projection is

```text
B_T=G Sigma^(-1) G*.                                   (P.8)
```

The normalization `(P.5)` also gives a useful lower bound without a condition
number.  For every `b in Ran(B)`,

```text
<b,Sigma b>
 =min_(r in Ran(R)) <r+b,H(r+b)>
 >=min_r ||r+b||^2
 =||b||^2.
```

Hence

```text
Sigma>=B.                                               (P.9)
```

## 4. Why the positive defect target fails

Let

```text
Q_E=T E T^(-1)                                         (P.10)
```

be the oblique projection onto `T Ran(E)`.  The corresponding oblique band
projection is

```text
A_obl=G B T^(-1)
     =(I-R_T)Q_E.                                      (P.11)
```

It is idempotent, has range `Ran(B_T)`, and acts as the identity on that range:

```text
A_obl^2=A_obl,
B_T A_obl=A_obl,
A_obl B_T=B_T.                                         (P.12)
```

Proof 254's nested shorting formula is

```text
Sigma^(-1)
 =B M B-B M C(C M C)^(-1) C M B.                      (P.13)
```

Since

```text
A_obl A_obl*=G(B M B)G*,                               (P.14)
```

equations `(P.8)` and `(P.13)` give

```text
A_obl A_obl*-B_T
 =G[B M C(C M C)^(-1) C M B]G*
 =(A_obl-B_T)(A_obl-B_T)*.                             (P.15)
```

Thus the old proposed organization

```text
orthogonal band
  =positive oblique phase square
   -positive shorting defect square                    (P.16)
```

is mathematically correct.  It is also unusably ill-conditioned.  There is no
permission to replace the difference in `(P.16)` by domination of either
positive term.

## 5. Canonical polar recombination

Let

```text
Omega=Sigma^(1/2),
V=G Sigma^(-1/2).                                      (P.17)
```

Then `G=V Omega` is the polar decomposition of the nested Schur frame, and

```text
V*V=B,
VV*=B_T.                                               (P.18)
```

For a self-adjoint smoothed detector `W`, write `W_B=B W B`.  Whenever the
traces are legal,

```text
Tr(W(B_T-B))
 =Tr_B(V* W V-W_B)
 =Tr_B(V*(W V-V W_B)).                                 (P.19)
```

The right side of `(P.19)` has no subtraction of two large positive squares.

There is also a condition-number-free response equation.  Put

```text
X_W=V* W V-W_B,
K_W=W G-G W_B.                                         (P.20)
```

Using `G=V Omega` twice gives the exact Sylvester identity

```text
Omega X_W+X_W Omega=V* K_W+K_W* V.                    (P.21)
```

Since `Omega>=B`,

```text
X_W
 =integral_0^infinity
    exp(-s Omega)(V* K_W+K_W* V)exp(-s Omega) ds,

||X_W||_1<=||K_W||_1.                                  (P.22)
```

More generally the right side is divided by the lower spectral bound of
`Omega`.  This proves that the inverse square root in `(P.17)` is not itself a
condition-number obstruction.

Equation `(P.22)` is not the final estimate.  In the real finite Sonin
sections, `||K_W||_1` inherits the expanding outer transport and grows from
about `42` to `5.2e7`.  The polar rewrite is stable, but a raw norm of `K_W`
still throws away the source cancellation.

## 6. Contractive dual frame and exact transport deletion

The inverse metric supplies a second Schur frame.  Define

```text
D=B-C(C M C)^(-1) C M B,
F=T^(-*) D.                                             (P.23)
```

The definition immediately gives

```text
C M D=0,
D*Z=B.                                                  (P.24)
```

The first identity says that `M D` lies in `Ran(E)`, so
`F=T(MD)` lies in `T Ran(E)`.  Since `D` lies in `Ran(B+C)`, `F` is orthogonal
to `T Ran(R)`.  Thus `F` lies in the same transported band as `G`.

Using `(P.24)`,

```text
G*F=Z* T* T^(-*)D=Z*D=B.                               (P.25)
```

The unique dual frame inside `Ran(G)` is therefore

```text
F=G Sigma^(-1),
D=H Z Sigma^(-1).                                      (P.26)
```

Consequently

```text
G*F=F*G=B,
G F*=F G*=B_T,
F*F=Sigma^(-1)<=B,
||F||<=1.                                               (P.27)
```

This is the canonical biorthogonal pair:

```text
              expanding primal frame G=T Z
                         ||
                         ||  G*F=F*G=B
                         ||
             contractive dual frame F=T^(-*)D.         (P.28)
```

Now use the fact specific to the route: the detector `W=C_g* C_g` and the
finite Euler transport `T` are convolution multipliers on the same logarithmic
carrier, so

```text
W T=T W.                                                (P.29)
```

Combining `(P.24)`, `(P.27)`, and `(P.29)` deletes the outer Euler transport
exactly:

```text
Tr(W(B_T-B))
 =Tr_B(F* W G-W_B)
 =Tr_B(D* T^(-1) W T Z-W_B)
 =Tr_B(D* W Z-W_B)
 =Tr_B(D*(W Z-Z W_B)).                                 (P.30)
```

Equation `(P.30)` is stronger than the polar estimate.  It does not bound an
Euler product, differentiate a phase, or subtract the two terms of `(P.16)`.
The complete outer transport has disappeared algebraically.

The remaining dependence on `S` is intrinsic and named:

```text
Z=B-R(R H R)^(-1)R H B,
D=B-C(C M C)^(-1)C M B.                               (P.31)
```

The two conditioned frames in `(P.31)` must remain paired.  Abstract norm
bounds on `(C M C)^(-1)` can recreate the rejected condition number.

## 7. Boundary form of the new bottom

Put

```text
L=(R H R)^(-1)R H B,
W_R=R W R.                                              (P.32)
```

Since `Z=B-RL`, the intrinsic defect in `(P.30)` has the exact expansion

```text
W Z-Z W_B
 =(I-B)W B
  -(I-R)W R L
  -R(W_R L-L W_B).                                     (P.33)
```

The last graph intertwinement satisfies

```text
(R H R)(W_R L-L W_B)
 =[R H R,W_R]L+W_R(R H B)-(R H B)W_B.                 (P.34)
```

Because `W` commutes with `H`, every nonzero term in `(P.33)--(P.34)` contains
a crossing of `W` through `R`, `B`, or their complements.  This is the right
place to insert

```text
B=P(I-P_hat)P+K_prol                                    (P.35)
```

and CC20's three half-line/scattering branches.  The prolate term in `(P.35)`
must remain in the same expression.

The continuous successor is now the following dual-frame boundary theorem.
For a root `g` supported in `[-B_root,B_root]`, prove

```text
abs Tr_B(D_(S,t)*
  (W_g Z_(S,t)-Z_(S,t) B W_g B))

 <=C (1+B_root)^d ||g||_(H^r)^2,                       (P.36)
```

with `C,d,r` independent of the finite place set and `0<=t<=1`.

The proof order is forced:

```text
1. construct Z and D on the same source nested pair;
2. prove the smoothed trace legality of (P.30);
3. insert (P.33)--(P.35) without separating D from Z;
4. complete every half-line/scattering crossing;
5. apply compact root support before expanding the Markov law;
6. sum probability mass rather than primewise absolute coefficients;
7. integrate the synchronized t-flow only after the uniform bound.       (P.37)
```

A polynomial bound in `(P.36)` is sufficient for Proof 249: its root support
grows only linearly while the resonant contraction decays geometrically.  A
conditioned-return coefficient growing exponentially in `B_root` rejects that
detector-specific route.

## 8. Exact three-dimensional guard

The need for recombination is already exact in `C^3`.  Let

```text
T=diag(1,kappa,1),
R=span(e1),
E=span(e1,(e2+e3)/sqrt(2)),
W=|e2><e2|.                                             (P.38)
```

On the `e2,e3` block,

```text
A_obl
 =[ 1/2          kappa/2 ]
  [ 1/(2 kappa)  1/2     ].                            (P.39)
```

The exact detector values are

```text
phase  =(1+kappa^2)/4,
actual =kappa^2/(kappa^2+1),
defect =(kappa^2-1)^2/[4(kappa^2+1)],

actual-base
 =(kappa^2-1)/[2(kappa^2+1)].                          (P.40)
```

Thus phase and defect grow like `kappa^2/4`, while their difference tends to
one and the endpoint response tends to `1/2`.

This model also retains Proof 254's Markov hypothesis.  In the physical
Hadamard basis the inverse metric is

```text
[(1+kappa^(-2))/2] I
 +[(1-kappa^(-2))/2] swap.                              (P.41)
```

Both coefficients are nonnegative and sum to one.  Repeating a legal local
factor realizes arbitrary `kappa` without taking a local Euler parameter to
one.

The closed certificate gives:

```text
+-------+--------------+--------------+--------------+----------+
| kappa | ||A_obl||    | phase        | defect       | endpoint |
+-------+--------------+--------------+--------------+----------+
|     2 | 1.2500e0     | 1.2500e0     | 4.5000e-1    | 0.300000 |
|    10 | 5.0500e0     | 2.5250e1     | 2.42599e1    | 0.490099 |
|   100 | 5.0005e1     | 2.50025e3    | 2.49925e3    | 0.499900 |
|  1000 | 5.000005e2   | 2.5000025e5  | 2.4999925e5  | 0.499999 |
+-------+--------------+--------------+--------------+----------+
```

The canonical isometry norm is exactly one on every row.  The maximum closed
formula error is `7.28e-16`.

## 9. Same-geometry finite-section certificate

The companion script uses the actual finite Sonin intersection from Proof 251,
the complete finite-S multiplier from Proof 252, and Proof 253's compact root
detector.

Default WSL2 command:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/255_nested_shorting_cancellation_probe.py
```

The hard gates report:

```text
maximum generic algebra error        2.97e-14
maximum three-dimensional error      7.28e-16
maximum strict Sonin error           3.94e-11
certificate                          PASS
```

The default same-geometry table is:

```text
+--------+----------+------------+-------------+-------------+----------+-----------+
| cutoff | log cond | ||A_obl||  | phase       | defect      | actual   | ||K0||_1  |
+--------+----------+------------+-------------+-------------+----------+-----------+
|      2 |   1.7627 | 1.4361e0   | 8.9056e1    | 1.2324e1    | 76.7320  | 11.9412   |
|     29 |   6.7958 | 8.2037e1   | 4.4319e2    | 3.6629e2    | 76.8994  | 17.8373   |
|     97 |   9.0034 | 5.6074e2   | 2.5455e4    | 2.5378e4    | 77.0092  | 18.4122   |
|    997 |  17.1382 | 1.1279e7   | 1.3262e11   | 1.3262e11   | 76.8466  | 22.3315   |
+--------+----------+------------+-------------+-------------+----------+-----------+
```

Here

```text
K0=W Z-Z W_B.                                           (P.42)
```

The `997` row is diagnostic because subtraction of the two `10^11` phase
terms loses about `4.4e-3` in floating point.  The canonical, dual-frame, and
intrinsic values agree without that subtraction.  The strict algebra gates use
cutoffs through `97`.

Three larger configurations physically contain the `p<=997` translation and
the root interval.  They give:

```text
+------+-------+----------+------------+-----------+--------+-----------+
| size | step  | half box | Sonin rank | ||K0||_1  | ||D||  | endpoint  |
+------+-------+----------+------------+-----------+--------+-----------+
|  208 | 0.080 |     8.32 |          8 |   19.6993 | 3.1774 | -1.42745  |
|  288 | 0.060 |     8.64 |         16 |   22.5086 | 3.4760 | -1.34980  |
|  320 | 0.050 |     8.00 |         24 |   24.3946 | 4.5197 | -1.15843  |
+------+-------+----------+------------+-----------+--------+-----------+
```

Across these rows the rejected phase is between `5.6e10` and `8.0e10`.
The intrinsic defect remains between about `20` and `24`.  This is strong
evidence that `(P.30)` removed a false condition-number amplification.  The
endpoint is not converged, the selected Sonin rank changes, and no finite
section proves `(P.36)`.

## 10. Literature boundary

Two standard operator-theory routes were checked with `research-stack`:

```text
Labuschagne--Xu, A Helson-Szego theorem for subdiagonal subalgebras
https://arxiv.org/abs/1301.6863

  characterizes weighted Hardy/Toeplitz boundedness through the angle
  between past and future;

Peller, Besov Spaces in Operator Theory
https://arxiv.org/abs/2402.09853

  surveys Schatten Hankel criteria, Besov regularity, and operator
  perturbation estimates.
```

Those sources support the relevance of Hardy angles, Hankel commutators, and
trace ideals.  They do not provide an `S`-uniform estimate for the complete
Euler-dependent shorted pair `(D,Z)`.  A generic weighted Hardy estimate also
normally retains a constant depending on the weight angle.  Using such a
constant before `(P.30)` would reproduce the rejected Euler condition number.

The dual-frame cancellation is therefore kept as a project-derived identity,
not attributed to those papers.

## 11. Route judgment

```text
+------------------------------------------------+--------------------------+
| layer                                          | judgment                 |
+------------------------------------------------+--------------------------+
| nested Schur frame G                           | exact                    |
| oblique band identity                          | exact                    |
| shorting square factorization                  | exact                    |
| phase/defect separate positive estimates       | rejected                 |
| canonical polar isometry V                     | exact                    |
| Sylvester response reduction                   | exact                    |
| raw expanding K_W trace-norm route             | rejected as too lossy    |
| inverse-metric dual frame F                     | exact contraction       |
| primal/dual outer-transport deletion            | exact for convolution W |
| intrinsic defect D*(WZ-ZW_B)                   | reduced by Proof 262     |
| endpoint two-source-commutator pairing         | active Gate 3U owner     |
| finite Sonin stability                         | survivor diagnostic      |
| continuous polynomial support bound (P.36)     | open                     |
| negative-owner integrated smallness            | open                     |
| same-object finite-S trace identity            | open                     |
| Burnol all-zero identity                       | open                     |
| Lean owner or route rewire                     | none                     |
| RH                                             | unproved                 |
+------------------------------------------------+--------------------------+
```

Proof 255 does not close Gate 3.  It changes what Gate 3 is: the route no
longer asks for a standalone shorting-defect estimate.  It asks for one
completed CC20 boundary estimate on the exact dual-frame pairing `(P.30)`.
Proof 262 uses `D*R=0` and `D*B=B` to reduce that pairing further to

```text
Tr_B(D*(C[W,E]B-[W,R]R L)).
```

The active estimate must use the compact support of both source commutators
before expanding the paired coframe and graph.
