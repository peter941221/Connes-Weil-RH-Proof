# Proof 354: canonical-midpoint off-diagonal innovation

Date: 2026-07-18

Status: exact two-projection reformulation of Proof 353's graph-detector
identity.  Relative to the canonical midpoint of two consecutive orthogonal
range projections, their difference is purely off diagonal.  The three-term
old-coordinate detector innovation is therefore replaced by one midpoint
commutator corner, without deleting its quadratic contribution.

This is an algebraic and trace-legality advance.  The source-specific uniform
weighted Hilbert--Schmidt estimate for the midpoint detector corners remains
open.  Gate 3U, the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| canonical midpoint of consecutive projections | exact                     |
| projection difference in midpoint coordinates | purely off diagonal       |
| Proof 353 three-term innovation                | one commutator corner     |
| graph-sine singular values                     | preserved exactly         |
| midpoint commutator from endpoint commutators  | explicit Schatten bound   |
| finite-matrix certificate                      | passes                    |
| two-projection ring algebra                    | Lean, axiom-clean         |
| uniform source midpoint row                    | open                      |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

The new coordinate choice is

```text
old range P_0 ---- canonical midpoint Q ---- new range P_1
       \                  |                  /
        \                 |                 /
         +------ equal operator angle -----+

relative to Q:

P_1-P_0 = [[0,R*],[R,0]].                         (MI.1)
```

Thus the quadratic diagonal terms from Proof 353 have not vanished.  The
midpoint rotation has resummed them into the single off-diagonal corner `R`.

## 2. Two-projection algebra

Let `P_0,P_1` be orthogonal projections on a Hilbert space and put

```text
A=P_1-P_0,
B=P_1+P_0-I.                                       (MI.2)
```

Direct expansion using `P_i^2=P_i=P_i*` gives

```text
AB+BA=0,
A^2+B^2=I.                                         (MI.3)
```

Assume

```text
norm(A)<1.                                         (MI.4)
```

Then `B^2=I-A^2` is strictly positive.  Define the midpoint symmetry and
midpoint projection by

```text
J=B(B^2)^(-1/2),
Q=(I+J)/2.                                         (MI.5)
```

Because `B` anticommutes with `A` while `B^2` commutes with `A`,

```text
J*=J,
J^2=I,
JA=-AJ.                                            (MI.6)
```

Hence `Q` is an orthogonal projection and

```text
Q A Q=0,
(I-Q)A(I-Q)=0.                                     (MI.7)
```

With

```text
R=(I-Q)A Q,                                        (MI.8)
```

equation `(MI.7)` gives the exact off-diagonal decomposition

```text
A=R+R*.                                            (MI.9)
```

No trace, compactness, finite-dimensional approximation, or choice of graph
coordinates occurs in `(MI.2)--(MI.9)`.

The canonical cosine--sine geometry behind this midpoint is the classical
two-subspaces decomposition:

```text
P. R. Halmos, Two subspaces,
Transactions of the American Mathematical Society 144 (1969), 381--389.
https://doi.org/10.1090/S0002-9947-1969-0251519-5
```

The route does not import a theorem from that paper: `(MI.2)--(MI.9)` is the
complete direct algebra needed here.  The citation records the standard
geometric context and does not supply the open Schatten estimate.

## 3. One detector innovation

Let `W=W*` be a bounded detector and set

```text
D_W=(I-Q)WQ.                                       (MI.10)
```

Whenever the two rectangular products are trace legal, `(MI.9)` gives

```text
Tr[W(P_1-P_0)]
 =2 Re Tr[D_W* R].                                 (MI.11)
```

This is the midpoint replacement for Proof 353 `(GI.8)--(GI.9)`:

```text
old P_0 coordinates:
  H_W=2W_10 C+W_11S-SW_00;

canonical midpoint coordinates:
  D_W=(I-Q)WQ.                                     (MI.12)
```

The term `W_11S-SW_00` has not been dropped.  It is exactly the coordinate
correction required to turn the old off-diagonal block into the midpoint
corner `(MI.10)`.  Expanding `D_W` back in the old coordinates recovers the
complete Proof 353 response.

## 4. The range row is unchanged

Suppose `P_1` is the graph projection from Proof 350, with normalized graph
cosine and sine `C,S`.  The canonical midpoint is the geodesic midpoint of
`P_0` and `P_1`.  The nonzero singular values of

```text
R=(I-Q)(P_1-P_0)Q                                  (MI.13)
```

are exactly the singular values of the old graph sine `S`.  Equivalently,
`R*R` and `S*S` are unitarily equivalent on their supports.  Therefore Proof
351's constant-one Julia range ledger transfers without loss:

```text
sum_j (p_j-1) norm(R_j Psi_(j-1) A_root)_2^2
 <=norm(A_root)_2^2.                                (MI.14)
```

Equation `(MI.14)` is a change of orthogonal coordinates, not a new estimate.

## 5. Fixed-step Schatten legality

The midpoint corner is controlled by endpoint commutators.  From `(MI.10)`,

```text
D_W=(I-Q)[W,Q]Q,
norm(D_W)_2<=norm([W,Q])_2.                         (MI.15)
```

For every Julia prime step with `p>=3`, Proof 350 gives

```text
norm(A)^2<=1/(p-1)<=1/2.                            (MI.16)
```

The power series of `f(x)=(1-x)^(-1/2)` on `[0,1/2]`, together with
`B^2=I-A^2`, gives

```text
norm([W,f(A^2)])_2<=2 norm([W,A])_2.                (MI.17)
```

Using `J=Bf(A^2)`, `norm(f(A^2))<=sqrt(2)`, and

```text
[W,A]=[W,P_1]-[W,P_0],
[W,B]=[W,P_1]+[W,P_0],                              (MI.18)
```

one obtains the explicit ideal bound

```text
norm([W,Q])_2
 <=(1/2)(sqrt(2)+2)
   [norm([W,P_0])_2+norm([W,P_1])_2].               (MI.19)
```

The same argument works in `S_1`.  The prime `p=2` is one fixed exceptional
step and may be handled with its actual strict angle gap; it cannot create an
`S`-dependent accumulation.

Equation `(MI.19)` closes a structural gap left in Proof 353: once the two
root-completed endpoint commutators are in the relevant Schatten ideal, the
midpoint detector corner is in that ideal as well.  It does not make their
norms uniform in `S`.

## 6. Lean owner

The carrier-independent ring algebra is formalized in

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSMidpointProjection.lean
```

Lean proves

```text
projectionDifference_anticommutes_projectionBisector,
projectionDifference_sq_add_projectionBisector_sq,
projectionDifference_eq_midpointDifferenceCorners.  (MI.19a)
```

The audit file is

```text
ConnesWeilRH/Dev/CCM24FiniteSMidpointProjectionAudit.lean
```

The owning build, audit, and narrow aggregate import pass in WSL2:

```text
+------------------------------------------+-------------------------------+
| check                                    | result                        |
+------------------------------------------+-------------------------------+
| midpoint owning module                   | PASS, 575 jobs                |
| focused axiom audit                      | PASS                          |
| CCM25Concrete aggregate                  | PASS, 3659 jobs               |
| audited theorem axiom set                | propext                       |
+------------------------------------------+-------------------------------+
```

The functional-calculus construction `(MI.5)`, Schatten estimate `(MI.19)`,
and uniform source row `(MI.20)` are not stored as Lean premises.

## 7. Why the uniform estimate is still open

The desired near bound now has the cleaner form

```text
sum_(log(p_j)<=L) norm(D_(W,j))_2^2/(p_j-1)
 <=C_root L(1+L).                                   (MI.20)
```

The owner is the literal midpoint of consecutive Gram-corrected quotient
ranges from Proof 343.  A proof of `(MI.20)` must still show that these
midpoint corners are contractive images of the complete physical combination

```text
outer crossing
  -Sonin crossing
  +K_prol
  +half-density residue cancellation
  +canonical and boundary-anomaly terms.            (MI.21)
```

It is not legal to insert `(MI.19)` into the sum and estimate the endpoint
commutators one by one.  That would recreate Proof 260's total-variation
bound and Proof 348's coherent prime-cluster obstruction.

The correct next producer is a source identity

```text
D_(W,j)=C_j mathcalB_j A_j                          (MI.22)
```

in which `mathcalB_j` is the already recombined physical boundary bracket,
the outer factors are contractions after Julia normalization, and all compact
root support is applied before one absolute value.  Equations `(MI.11)` and
`(MI.14)` then leave only one direct-sum Cauchy--Schwarz step.

## 8. Reproducible certificate

The companion script constructs commuting Euler translations and a
self-adjoint detector in a common spectral representation.  For every prime
step it verifies

```text
AB+BA=0 and A^2+B^2=I;
the midpoint symmetry and projection identities;
the zero diagonal blocks `(MI.7)`;
the detector pairing `(MI.11)`;
equality of midpoint-range and graph-sine singular values;
the sequential endpoint telescope.                 (MI.23)
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/354_midpoint_off_diagonal_innovation_probe.py
```

This is a finite algebra certificate.  It is not evidence for `(MI.20)`.

## 9. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| old three-term graph innovation               | exactly resummed          |
| midpoint detector owner                       | one commutator corner     |
| Julia range Bessel row                        | preserved                 |
| two-projection algebra                        | Lean, `[propext]`         |
| fixed-step Schatten transfer                  | explicit `(MI.19)`        |
| uniform source row `(MI.20)`                   | open, active near bottom  |
| Proof 336 far lane                             | already closed            |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
