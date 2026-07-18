# Proof 385: outer-boundary two-sided root insertion

Date: 2026-07-18

Status: exact two-Hilbert--Schmidt factorization of the compact-root positive
detector crossing at the outer half-line.  Keeping the finite intermediate
window makes both root legs Hilbert--Schmidt and turns the midpoint trace into
a legal rectangular `S_2` pairing with one inserted range-side root.

This proves the atomic outer branch of Proof 382 `(JR.9)`.  It does not yet
include the reflected second support, prolate term, quotient corrections, or
moving prefix/Gram coordinates.  Gate 3U, the finite-`S` sign, Burnol's
identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| outer positive detector crossing             | exact two-root product  |
| left root leg                                 | Hilbert--Schmidt        |
| right root leg                                | Hilbert--Schmidt        |
| intermediate window                          | fixed `[-B,B]`          |
| rectangular trace cycle                       | legal                    |
| translated common near window                 | Proof 357               |
| other physical branches                       | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Outer crossing

Work on `H=L2(R)` and put

```text
E_+=1_[0,infinity),
E_-=I-E_+.                                          (OI.1)
```

Let `g in L1(R) intersection L2(R)` satisfy

```text
supp(g) subset [-B,B],                              (OI.2)
```

and write

```text
C=C_g,
W=C* C.                                             (OI.3)
```

The forward positive detector crossing is

```text
D_out=E_- W E_+.                                    (OI.4)
```

Its kernel has the completed two-root form

```text
k(x,y)
 =1_(x<0)1_(y>=0)
   integral_R conjugate(g(z-x))g(z-y) dz.           (OI.5)
```

If the integrand is nonzero, compact support and `x<0<=y` force

```text
-B<=z<=B.                                           (OI.6)
```

Let `E_B=1_[-B,B]`.  Equation `(OI.6)` gives the operator identity

```text
D_out
 =E_- C* E_B C E_+
 =L_out A_out,                                      (OI.7)

L_out=E_- C* E_B,
A_out=E_B C E_+.                                    (OI.8)
```

This is an identity before a trace or norm.

## 3. Both root legs are Hilbert--Schmidt

The right leg has kernel

```text
1_[-B,B](z) g(z-y)1_(y>=0),                         (OI.9)
```

and the left leg has kernel

```text
1_(x<0) conjugate(g(z-x))1_[-B,B](z).               (OI.10)
```

Tonelli gives the uniform bounds

```text
norm(A_out)_2^2<=2B norm(g)_2^2,
norm(L_out)_2^2<=2B norm(g)_2^2.                    (OI.11)
```

Thus `(OI.7)` is trace class and

```text
norm(D_out)_1
 <=norm(L_out)_2 norm(A_out)_2
 <=2B norm(g)_2^2.                                  (OI.12)
```

The earlier Proof 361 used only boundedness of `L_out`.  Proof 385 retains its
stronger Hilbert--Schmidt property because that is what inserts the second
root into the Julia range row.

## 4. Exact rectangular insertion

Let

```text
R:Ran(E_+)->Ran(E_-)                                (OI.13)
```

be any bounded range corner for which the displayed physical response is the
one under consideration.  Since `L_out` and `R A_out*` are
Hilbert--Schmidt,

```text
Tr_(Ran(E_+))(D_out* R)

 =Tr_(Ran(E_+))(A_out* L_out* R)

 =Tr_(L2([-B,B]))(L_out* R A_out*)

 =<L_out,R A_out*>_(S_2).                          (OI.14)
```

Equation `(OI.14)` is the outer atomic form of Proof 382 `(JR.9)`:

```text
detector root =L_out,
inserted range root=R A_out*.                       (OI.15)
```

The cycle in `(OI.14)` is legal because it exchanges products of two
rectangular Hilbert--Schmidt maps.  It is not inferred from finite sections.

The repository's `BasisHilbertSchmidtPairData` and
`ContinuousKernelHilbertSchmidt` modules already own this rectangular
trace-product pattern for the concrete continuous kernels.

## 5. Reverse orientation

The reverse crossing has the identical structure

```text
D_out_rev=E_+ W E_-
 =L_out_rev A_out_rev,                              (OI.16)

L_out_rev=E_+ C* E_B,
A_out_rev=E_B C E_-.                               (OI.17)
```

Both legs again satisfy `(OI.11)`.  Bundle the two right legs as

```text
A_outer x=(A_out x,A_out_rev x).                   (OI.18)
```

Then

```text
norm(A_outer)_2^2<=4B norm(g)_2^2.                 (OI.19)
```

The two signs and orientations stay in the left readout; the direct sum is a
fixed two-copy owner, not one copy per prime.

## 6. Near translated family

For a translated crossing of displacement at most `L`, Proof 357 enlarges
`[-B,B]` to one interval `J_(L,B)`.  Both factors in `(OI.7)` are restrictions
or translations of the two common finite-window roots.  Their square cost is
at most

```text
(L+2B) norm(g)_2^2                                  (OI.20)
```

per orientation.  The factorization is applied to the completed crossing
before a prime sum or absolute value.

## 7. Reproducible certificate

The companion zero-fill Toeplitz probe checks

```text
the finite-window identity `(OI.7)`;
both Hilbert--Schmidt bounds `(OI.11)`;
the trace-class bound `(OI.12)`;
the rectangular insertion `(OI.14)`;
the reverse orientation `(OI.16)--(OI.19)`.         (OI.21)
```

Run only after Proofs 385--389 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/385_outer_boundary_two_sided_root_insertion_probe.py
```

The continuous proof is the support implication `(OI.6)`, Tonelli, and the
ordinary two-Hilbert--Schmidt trace cycle.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| outer two-sided root owner                    | closed `(OI.7)`          |
| outer trace-preserving insertion              | closed `(OI.14)`         |
| translated common-window version              | Proof 357               |
| second support / prolate insertion             | next batch              |
| complete corrected bracket                    | open                    |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
