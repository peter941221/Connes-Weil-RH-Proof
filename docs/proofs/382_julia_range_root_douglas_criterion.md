# Proof 382: Julia range-root Douglas criterion

Date: 2026-07-18

Status: exact two-stage criterion for inserting Proof 380's two-copy
range-root corner into Proof 351's Julia Bessel row.  First, a source identity
must insert one common root without changing the physical trace.  Second, the
inserted range column must satisfy one Douglas domination by the actual Julia
range column, not merely a Hilbert--Schmidt norm bound.

This removes ambiguity from the missing common-root statement.  It does not
prove the source domination for the corrected CCM24 quotient bracket.  Gate
3U, the finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Proof 380 range-root pair                     | exact input              |
| Proof 351 weighted Julia column               | contraction             |
| trace-preserving common-root insertion        | explicit, open         |
| inserted-column compatibility                 | Douglas equivalent      |
| mandatory kernel inclusion                    | explicit                |
| total Hilbert--Schmidt norm alone             | insufficient            |
| CCM24 source domination                       | open                    |
| finite certificate                            | supplied                |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```

## 2. Actual Julia range column

Retain Proof 351's notation.  Let

```text
w_j=p_j-1,
T_j=S_j J_(j-1) Psi_(j-1):K_0->K_j_perp.          (JR.1)
```

Proof 351 `(JB.16)` says that the column

```text
mathcalT x=(sqrt(w_j) T_j x)_j                    (JR.2)
```

is a contraction:

```text
mathcalT* mathcalT<=I_(K_0).                      (JR.3)
```

For one source-owned Hilbert--Schmidt input

```text
A_root:H_aux->K_0,                                (JR.4)
```

define

```text
mathcalS_A=mathcalT A_root.                       (JR.5)
```

Then

```text
norm(mathcalS_A)_2^2
 =sum_j w_j norm(T_j A_root)_2^2
 <=norm(A_root)_2^2.                              (JR.6)
```

This is the literal range owner.  Replacing `mathcalS_A` by an arbitrary
column with the same norm loses the Julia defect coordinates.

## 3. Pull back the physical range-root row

Proof 380 gives, in each canonical midpoint coordinate, the two-copy root
corner

```text
Y_(root,j)
 =(C_(11,j)R_j,R_j C_(00,j)*).                    (JR.7)
```

Use the canonical half-angle unitaries from Proof 355 and the fixed-source
unitaries `J_(j-1)` from Proof 351 to pull the domain of every component back
to `K_0`.  This gives bounded operators

```text
Ytilde_(root,j):K_0->Y_j.                          (JR.8)
```

All coordinate changes in `(JR.8)` are unitary.  They do not change a trace
or repair a missing source factor.

The first open source identity must construct Hilbert--Schmidt operators
`Bhat_(root,j):H_aux->Y_j` such that

```text
Tr[W(P_j-P_(j-1))]
 =2 Re <Bhat_(root,j),
          Ytilde_(root,j) A_root>_(S_2).           (JR.9)
```

Equation `(JR.9)` is not implied by coordinate pullback.  It includes the
trace-class cycle which inserts `A_root` on both sides of Proof 380's pairing.
The same `A_root` must work for every `j`.

After `(JR.9)` is proved, define the inserted weighted physical column

```text
mathcalY_root x
 =(sqrt(w_j) Ytilde_(root,j)A_root x)_j.           (JR.10)
```

The second requirement is

```text
mathcalY_root=Z mathcalS_A.                        (JR.11)
```

for one bounded operator `Z` on the direct-sum range.  The route needs

```text
norm(Z)<=C(1+L+B_root)^d.                          (JR.12)
```

The signs and the two root orientations remain inside `(JR.9)--(JR.11)`; no
branch is normed before the same-object column is formed.

## 4. Douglas equivalence

Apply the common-domain Douglas theorem to the two operators in `(JR.11)`.
For any `C>=0`, the following are equivalent:

```text
1. mathcalY_root=Z mathcalS_A with norm(Z)<=C;

2. mathcalY_root*mathcalY_root
     <=C^2 mathcalS_A*mathcalS_A;

3. norm(mathcalY_root x)
     <=C norm(mathcalS_A x) for every x.           (JR.13)
```

In particular, `(JR.13)` contains the mandatory visibility condition

```text
ker(mathcalS_A) subset ker(mathcalY_root).          (JR.14)
```

Equation `(JR.14)` is stronger than

```text
norm(mathcalY_root)_2<=C norm(A_root)_2.            (JR.15)
```

A small column may still leak on `ker(mathcalS_A)` and have no factorization
through the Julia row.

## 5. Final scalar consumer

Let `mathcalB_root` be Proof 380's direct-sum detector-root column, weighted
reciprocally:

```text
norm(mathcalB_root)_2^2
 =sum_j norm(Bhat_(root,j))_2^2/w_j.               (JR.16)
```

The source insertion in `(JR.9)` must preserve Proof 378's polynomial bound
when replacing the raw endpoint corners by `Bhat_(root,j)`.  If it does, and
`(JR.11)--(JR.12)` hold, then the same-object response is

```text
Q_S^near(g,g)
 =2 Re <mathcalB_root,mathcalY_root>_(S_2)

 =2 Re <mathcalB_root,Z mathcalS_A>_(S_2).         (JR.17)
```

One Cauchy--Schwarz inequality gives

```text
abs Q_S^near(g,g)
 <=2 norm(mathcalB_root)_2 norm(Z) norm(A_root)_2. (JR.18)
```

This is now a legal `S_2` pairing because both columns in `(JR.17)` are
Hilbert--Schmidt.  No raw midpoint range corner remains.

## 6. Active source theorem

The near Gate 3U bottom consists of the insertion identity `(JR.9)`, the
preserved detector bound, and the positive inequality

```text
mathcalY_root*mathcalY_root

 <=C^2(1+L+B_root)^(2d)
   mathcalS_A*mathcalS_A,                          (JR.19)
```

where

```text
A_root is one physical boundary-localized root bundle;
mathcalS_A is Proof 351's actual Julia column;
mathcalY_root is Proof 380's actual two-copy range-root column;
all Proof 365--369 quotient corrections are retained.          (JR.20)
```

The weaker inequality with `A_root*A_root` on the right does not establish
alignment with the Julia range sine.  Equations `(JR.9)` and `(JR.19)` are the
required same-object strengthening of Proof 369 `(NC.12)`.

## 7. Reproducible certificate

The companion probe builds a finite contraction cascade, its exact Julia
defect column, one common Hilbert--Schmidt input, and a contractive physical
readout `Z`.  It checks `(JR.3)--(JR.6)`, `(JR.11)--(JR.13)`, and the final
weighted Cauchy--Schwarz inequality.

It also adds an arbitrarily small rank-one leakage on
`ker(mathcalS_A)`.  The leakage has a small Hilbert--Schmidt norm but violates
`(JR.14)`, so no Douglas factor exists.

Run only after Proofs 380--384 are complete:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/382_julia_range_root_douglas_criterion_probe.py
```

The finite certificate checks the Douglas stage after an aligned insertion
has been supplied.  It does not construct the CCM24 identity `(JR.9)` or prove
the source inequality `(JR.19)`.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| Julia common-input range column               | exact `(JR.5)`           |
| trace-preserving insertion `(JR.9)`            | open                    |
| inserted-column Douglas criterion             | exact `(JR.13)`          |
| kernel visibility                             | mandatory `(JR.14)`      |
| CCM24 domination `(JR.19)`                    | open, active producer   |
| Proof 336 far lane                             | retained                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
