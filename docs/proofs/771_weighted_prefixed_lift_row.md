# Proof 771: weighted prefixed lift row

Date: 2026-08-03

Status: exact strong sufficient reduction of Proof 770's completed two-root
factorization to one weighted trace-class (`S_1`) source row.  It produces the
common Hilbert--Schmidt (`S_2`) factors and their optimal reciprocal detector
budget automatically.  It does not construct the physical lifts for CCM24.
Proof 772 records the weaker signed trace target that is preferred for Gate
3U.  The finite-`S` sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+-----------------------------------------------------+-----------------------------+
| layer                                               | judgment                    |
+-----------------------------------------------------+-----------------------------+
| recombined physical corner `L_j`                    | exact, Proof 770            |
| bounded prefix lift `Ltilde_j=Psi_(j-1) X_j`       | source requirement          |
| weighted row `X_S`                                  | exact packaging             |
| trace-class row polar factorization                 | exact                       |
| common `S_2` input and reciprocal detector row      | exact                       |
| constant-one Julia range consumer                   | Proofs 351 and 354          |
| support-polynomial trace-norm lift estimate          | strong sufficient theorem  |
| Gate 3U / finite-S sign / Burnol / RH               | open / open / open / open   |
+-----------------------------------------------------+-----------------------------+
```

The reduction has one purpose: replace many separate Douglas readouts by one
source-side trace-norm statement without splitting the two root orientations
that Proof 770 has already recombined.

```text
completed physical corners `L_j`
        |
        | pull their range to the fixed midpoint source
        v
prefix lifts `Ltilde_j=Psi_(j-1) X_j`
        |
        | put every `X_j` in one reciprocal-weighted row
        v
`X_S in S_1`
        |
        | polar square-root factorization
        v
one common `A_S` and the exact detector row `B_j`.
```

## 2. Fixed notation and the real source condition

For a finite chronological prime family, write

```text
w_j=p_j-1 > 0,
E_j=(I-P_j)H,
L_j=P_j C* C (I-P_j):E_j -> P_j H.
```

Here `L_j` is the *recombined* completed detector corner from Proof 770:

```text
L_j=C_(10,j)* C_(11,j)+C_(00,j)* C_(01,j).
```

It is essential that this equality is applied before the next line.  Let
`U_j^mid:K_0 -> P_j H` be the midpoint input-coordinate unitary and put

```text
Ltilde_j=(U_j^mid)* L_j:E_j -> K_0.                (PL.1)
```

The new source input is a bounded physical lift

```text
Ltilde_j=Psi_(j-1) X_j,
X_j:E_j -> K_0.                                    (PL.2)
```

Equation `(PL.2)` is an operator equation on the actual physical carrier.  It
is not a definition by a Moore--Penrose inverse (Moore--Penrose inverse): the
Julia prefix can have nonclosed range, and a formal inverse can then be
unbounded.  It is also stronger than the necessary visibility condition

```text
ker(Psi_(j-1)*) subset ker(Ltilde_j*).             (PL.3)
```

Condition `(PL.3)` only gives inclusion in the *closed* prefix range.  A
bounded lift in `(PL.2)` requires the actual Douglas domination

```text
Ltilde_j Ltilde_j*
 <=c_j^2 Psi_(j-1) Psi_(j-1)*                     (PL.4)
```

for some finite `c_j`.  The sought Gate input is stronger again: the lifts
must be chosen jointly so that their weighted row is trace class.

## 3. The weighted physical lift row

Let

```text
E_S=direct_sum_j E_j,
iota_j:E_j -> E_S
```

be the coordinate inclusions.  From any chosen lifts in `(PL.2)`, define

the one row operator

```text
X_S:E_S -> K_0,
X_S(x_j)_j=sum_j w_j^(-1/2) X_j x_j,
X_S iota_j=w_j^(-1/2) X_j.                         (PL.5)
```

One strong sufficient source theorem is the existence of the lifts in `(PL.2)`
such that

```text
X_S in S_1,
norm(X_S)_1
 <=C (1+B_root)^d norm(g)_(H^r)^2,                (PL.6)
```

with constants independent of the visible finite set.  The source theorem
must construct `(PL.2)` *after* the outer, reflected second-support, prolate,
and quotient-boundary terms have been recombined inside `L_j`.

This is not the total-variation condition

```text
sum_j w_j^(-1/2) norm(X_j)_1 < infinity.
```

That stronger condition implies `(PL.6)` by the triangle inequality, but it
destroys the common-source geometry.  The trace norm of the horizontal row in
`(PL.5)` is the correct joint cost.

## 4. Polar factorization supplies both rows

Assume the first part of `(PL.6)`.  Write the polar decomposition

```text
X_S=V |X_S|,
D_S=|X_S|^(1/2):E_S -> E_S,
A_S=V |X_S|^(1/2):E_S -> K_0.                     (PL.7)
```

Then

```text
X_S=A_S D_S,
norm(A_S)_2^2=norm(D_S)_2^2=norm(X_S)_1.          (PL.8)
```

For every coordinate define

```text
B_j*=sqrt(w_j) D_S iota_j:E_j -> E_S,
B_j=sqrt(w_j) iota_j* D_S*:E_S -> E_j.            (PL.9)
```

Since `(PL.5)` says `X_j=sqrt(w_j) X_S iota_j`, equations
`(PL.2)`, `(PL.7)`, and `(PL.9)` give the exact Proof 770 factorization

```text
L_j=U_j^mid Psi_(j-1) A_S B_j*.                    (PL.10)
```

The common input `A_S` is the same for every `j` in the finite family.  It may
depend on the family through `X_S`; that is harmless to the Julia Bessel
consumer, whose only requirement is commonality across the row.  A later
factorization through Proof 383's pre-existing, family-independent root bundle
would be a stronger source construction, not a prerequisite for this
reduction.

Orthogonality of the direct-sum coordinates gives the exact reciprocal budget

```text
sum_j norm(B_j)_2^2/w_j
 =sum_j norm(D_S iota_j)_2^2
 =norm(D_S)_2^2
 =norm(X_S)_1.                                    (PL.11)
```

Thus the trace norm is not merely an upper bound.  It is the balanced
Hilbert--Schmidt cost of the factorization.  Conversely, if a completed
factorization `(PL.10)` is already available and its reciprocal detector row
is Hilbert--Schmidt, then `(PL.5)` factors as

```text
X_S=A_root B_row*,
B_row x=(w_j^(-1/2) B_j x)_j,
```

so `X_S` is trace class and

```text
norm(X_S)_1
 <=norm(A_root)_2
   (sum_j norm(B_j)_2^2/w_j)^(1/2).                (PL.12)
```

The polar construction in `(PL.7)` achieves equality after balancing the two
Hilbert--Schmidt legs.  Therefore `(PL.6)` is a sharp reformulation of the
joint ideal part of Proof 770's source requirement, not an extra loss.

## 5. The Julia consumer becomes immediate

Set

```text
T_j=R_j U_j^mid Psi_(j-1):K_0 -> E_j.
```

Proof 354's midpoint coordinate identification and Proof 351's Julia Bessel
row give, for every Hilbert--Schmidt input `A`,

```text
sum_j w_j norm(T_j A)_2^2 <=norm(A)_2^2.           (PL.13)
```

The repository evidence is the named-basis Hilbert--Schmidt amplification in
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSJuliaBessel.lean`
(`summable_juliaRangeEnergy_comp`) and the norm-one weighted range-sine
Douglas theorem in
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSActualJuliaRangeSineDouglas.lean`
(`exists_weightedRangeSineFactor_of_rangeSine_weighted_le`).

By the legal two-`S_2` cycle in Proof 770, `(PL.10)` yields

```text
Q_S_near
 =2 Re sum_j <B_j,T_j A_S>_(S_2).                 (PL.14)
```

Use Cauchy--Schwarz (Cauchy--Schwarz inequality) only once, on the two whole
weighted rows:

```text
abs(Q_S_near)
 <=2 [sum_j norm(B_j)_2^2/w_j]^(1/2)
      [sum_j w_j norm(T_j A_S)_2^2]^(1/2)
 <=2 norm(X_S)_1.                                 (PL.15)
```

Combining `(PL.6)` and `(PL.15)` is a support-polynomial sufficient form:

```text
abs(Q_S_near)
 <=2 C (1+B_root)^d norm(g)_(H^r)^2.              (PL.16)
```

No second range-side Douglas theorem is needed: it is already the
constant-one Julia row in `(PL.13)`.  No root orientation or physical branch
has been separated before the one absolute value in `(PL.15)`.

Proof 260's trace-norm obstruction means that `(PL.6)` must not be promoted
to the preferred Gate 3U target merely because `(PL.15)` is valid.  A compact
root can make the signed scalar small while its completed crossing has large
nuclear norm.  Proof 772 keeps the same lifted row but bounds its signed Julia
trace directly, before the first absolute value.

## 6. Non-negotiable guards

```text
+-------------------------------------------------------------+-----------------------------------+
| forbidden shortcut                                          | reason                            |
+-------------------------------------------------------------+-----------------------------------+
| factor `L_plus` and `L_minus` before `(PL.2)`              | loses Proof 770's cancellation    |
| define `X_j` using `Psi_(j-1)^+`                            | may be unbounded                  |
| use only `(PL.3)`                                           | closed-range visibility is weaker |
| bound each `X_j` separately and sum absolute norms          | imposes total variation           |
| pull an off-model vector through `g_0`                      | Proof 770 domain violation        |
+-------------------------------------------------------------+-----------------------------------+
```

The rank-deficient test in the companion certificate uses

```text
Psi=diag(1,0),
L=[[0,0],[1,0]].
```

For `v=e_1`, `Psi* v=0` but `L* v=e_0`.  Hence `(PL.3)` fails and no bounded
lift `L=Psi X` exists.  A small norm of `L` would not repair this range error.

## 7. Verification and scope

The finite certificate constructs several rectangular lifts, forms `(PL.5)`,
uses a singular-value decomposition to implement `(PL.7)`, and verifies

```text
the row factorization `(PL.10)`;
the exact norm identity `(PL.11)`;
the contraction-model analogue of `(PL.13)`;
the one-step weighted Cauchy--Schwarz bound `(PL.15)`;
the rank-deficient visibility obstruction.
```

Run it in the Linux-side verification environment:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/771_weighted_prefixed_lift_row_probe.py
```

The certificate checks finite-dimensional polar algebra only.  It does not
prove that CCM24's completed physical corners admit `(PL.2)`, prove the
support-polynomial bound `(PL.6)`, identify the full finite-S route target
with `Q_S_near`, prove the finite-S sign, prove Burnol's identity, or prove
`_root_.RiemannHypothesis`.

## 8. Route judgment

```text
+-----------------------------------------------------+-----------------------------+
| statement                                           | judgment                    |
+-----------------------------------------------------+-----------------------------+
| polar row factorization `(PL.7)--(PL.11)`          | exact                       |
| Julia consumption `(PL.13)--(PL.15)`               | exact                       |
| physical bounded lifts `(PL.2)`                     | open source construction    |
| trace-class row bound `(PL.6)`                      | strong sufficient route     |
| Gate 3U / finite-S sign / Burnol / RH               | open / open / open / open   |
+-----------------------------------------------------+-----------------------------+
```
