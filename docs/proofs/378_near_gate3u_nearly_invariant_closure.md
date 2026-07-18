# Proof 378: near Gate 3U nearly-invariant completion audit

Date: 2026-07-18

Status: closes the uniform endpoint root-commutator estimate `(MR.6)` and the
reciprocal-weight midpoint detector row.  A completion audit then exposes one
remaining same-object requirement: the raw midpoint range corner has not been
factored through the common boundary-localized Hilbert--Schmidt root required
by Proof 351's Julia Bessel row.

Consequently Gate 3U remains open.  Proof 336 still owns the far displacement
tail, but it cannot be joined to the near lane until the root-split pairing is
constructed.  The nearly-invariant analysis has no full Lean formalization.

## 1. Result

Proofs 375--377 prove, for every actual Euler-prefix quotient projection
`P_j=E-R_j`,

```text
sup_j norm([C_g,P_j])_2^2
 <=C_0(1+B_root)^4 norm(g)_(H^3)^2.                 (NG.1)
```

Proofs 354, 359, 371, and 373 therefore give the reciprocal-weight detector
row

```text
sum_(log(p_j)<=L)
 norm((I-M_j)W M_j)_2^2/(p_j-1)

 <=C_1(1+L)(1+B_root)^d norm(g)_(H^3)^4,            (NG.2)
```

where `W=C_g* C_g` and `M_j` is the canonical midpoint of
`P_(j-1),P_j`.  The constants are independent of the visible finite set.

Equations `(NG.1)--(NG.2)` do not yet prove a bound for the route response.
The missing contract is

```text
Tr[W(P_j-P_(j-1))]
 =2 Re <D_j^root,R_j^root>_(S_2),                  (NG.3)

R_j^root
 =Julia range sine applied to one common
  boundary-localized Hilbert--Schmidt root input,   (NG.4)

norm(D_j^root)_2
 <=C norm([C_g,M_j])_2.                            (NG.5)
```

The same objects must occur in all three lines.

## 2. Exact midpoint algebra

Let

```text
Delta_j=P_j-P_(j-1),
D_j=(I-M_j)W M_j,
A_j=(I-M_j)Delta_j M_j.                            (NG.6)
```

Proof 354 gives

```text
M_j Delta_j M_j=0,
(I-M_j)Delta_j(I-M_j)=0.                           (NG.7)
```

In finite dimensions, or whenever both rectangular cycles are trace class,
this yields

```text
Tr(W Delta_j)=2 Re Tr(D_j* A_j).                   (NG.8)
```

Summing `(NG.8)` is the literal endpoint telescope.  It does not drop a
canonical term or boundary anomaly.  However, scalar trace legality does not
turn `A_j` into a Hilbert--Schmidt operator and does not instantiate the
common-input Julia row.

## 3. Closed detector row

Proof 371 gives

```text
norm(D_j)_2^2
 <=2 norm(C_g)^2 norm([C_g,M_j])_2^2.               (NG.9)
```

For `p_j>=3`, Proof 354 transfers the root commutator to the endpoints:

```text
norm([C_g,M_j])_2^2
 <=2 c_mid^2[
   norm([C_g,P_(j-1)])_2^2
  +norm([C_g,P_j])_2^2],                           (NG.10)

c_mid=(sqrt(2)+2)/2.                               (NG.11)
```

Insert `(NG.1)` and Proof 359's harmonic estimate

```text
sum_(log(p)<=L)1/(p-1)<=1+L.                       (NG.12)
```

This proves `(NG.2)`.  The single `p=2` midpoint has one fixed strict-angle
constant and contributes one fixed term.  No Euler Gram inverse or primewise
physical-branch norm enters this row.

## 4. Julia range row

Proof 351 proves a constant-one Bessel estimate only after one source-owned
Hilbert--Schmidt input has been supplied:

```text
sum_j(p_j-1) norm(R_j^root)_2^2
 <=norm(A_root)_2^2.                               (NG.13)
```

Here every `R_j^root` is the corresponding Julia range sine applied to the
same `A_root`.  The raw midpoint corner `A_j` in `(NG.6)` is only known to be
bounded.  Replacing `R_j^root` by `A_j`, or silently omitting `A_root`, is not
an application of `(NG.13)`.

This distinction is structural:

```text
fixed-S trace legality
        |
        +-- defines the completed scalar response
        |
        `-- does not create a common S_2 input

common boundary root
        |
        `-- makes the Julia range row an S_2 Bessel estimate.   (NG.14)
```

## 5. Active same-object theorem

Proof 357 constructs candidate common boundary-root inputs for the physical
half-line branches.  Proofs 365--369 show that the actual quotient crossing
also contains the two compression-boundary corrections and two mandatory
mixed covariance terms.

The next producer must factor the completed corrected bracket, not its
branches separately:

```text
outer crossing
  -Sonin/scattering crossing
  +prolate correction
  +two quotient-boundary corrections
  +residue and anomaly terms
        |
        v
one common boundary-localized root input
        |
        +-- detector output D_j^root satisfying `(NG.5)`
        `-- Julia range output R_j^root satisfying `(NG.13)`.   (NG.15)
```

Once `(NG.3)--(NG.5)` are proved, one Cauchy--Schwarz inequality gives the
near scalar estimate:

```text
abs Q_S^near(g,g)
 <=2[
   sum_j norm(D_j^root)_2^2/(p_j-1)
  ]^(1/2)
  [
   sum_j(p_j-1)norm(R_j^root)_2^2
  ]^(1/2).                                          (NG.16)
```

Until then, `(NG.16)` is a consumer contract rather than a proved route
identity.

## 6. Near/far split

The root cross-correlation is supported in `[-2B_root,2B_root]`.  The intended
displacement cutoff remains

```text
L=8B_root+4.                                        (NG.17)
```

Proof 336 controls the complementary complete displacement tail after the
half-density residue has been removed.  That far theorem remains available.
The open root split `(NG.3)--(NG.5)` prevents adding it to a proved near
response bound, so no Gate 3U conclusion follows yet.

## 7. Bilinear response

Proof 263 proves that the legal response is Hermitian and that a diagonal
bound polarizes to the bilinear bound without enlarging the support window.
This becomes usable after the diagonal same-object identity `(NG.3)` is
proved.  Polarization cannot supply the missing Hilbert--Schmidt input.

## 8. Obstruction audit

```text
Proof 260 total variation:
  avoided on the detector row, but the Julia range row still needs the common
  root split before its orthogonality can be used;

Proof 340 owner mismatch:
  avoided because `(NG.1)` uses near invariance, not a claimed semilocal
  Hermite--Biehler generator;

Proof 348 coherent prime cluster:
  absent from the uniform endpoint commutator, but cancellation on the range
  side is available only through Proof 351's exact common-input row;

Proof 349 mean-type obstruction:
  avoided because transported ranges are declared nearly invariant, not
  scalar model spaces;

Proofs 365--369 quotient correction:
  still mandatory inside the root-split bracket.                    (NG.18)
```

## 9. Reproducible certificate

The companion probe constructs analytic Euler-prefix nearly invariant ranges
in a finite Laurent Hardy model.  It checks

```text
the uniform endpoint root-commutator budget;
the canonical midpoint off-diagonal identity;
the positive-detector root reduction;
the reciprocal-weight harmonic detector row;
the finite endpoint response telescope.                    (NG.19)
```

Run only in the unified five-batch verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/378_near_gate3u_nearly_invariant_closure_probe.py
```

The certificate does not construct `(NG.3)--(NG.5)` and cannot establish
infinite-dimensional trace compatibility.

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| endpoint theorem `(MR.6)`                     | closed mathematically    |
| reciprocal-weight midpoint detector row       | closed mathematically    |
| common boundary-root input                    | Proof 357 candidates     |
| corrected quotient bracket                    | Proofs 365--369          |
| root-split same-object `S_2` pairing           | open, active producer   |
| far displacement tail                        | Proof 336                |
| Gate 3U uniform analytic bound                | open                     |
| finite-S sign / Burnol / RH                    | open / open / open       |
+------------------------------------------------+---------------------------+
```
