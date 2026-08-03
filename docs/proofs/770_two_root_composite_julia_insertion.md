# Proof 770: Two-root composite Julia insertion

Date: 2026-08-03

Status: an exact reorganization of the two-copy root pairing.  It removes the
separate Douglas domination `(JR.19)` from the conditional route: once a
source-specific common factorization of two completed root composites is
proved, the range side is exactly the already-controlled Julia row.  The
required common factorization is not known for CCM24, so Gate 3U, the
finite-S sign, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------------+------------------------+
| layer                                                | judgment               |
+------------------------------------------------------+------------------------+
| two-copy root pairing, Proof 380                    | exact input            |
| two-root composite cyclic placement                 | exact                  |
| range leg after placement                            | raw midpoint sine R_j  |
| Julia Bessel row for that range leg                 | Proofs 351 and 354     |
| separate Douglas condition `(JR.19)`                | redundant conditionally|
| common completed composite factorization             | open source theorem    |
| global multiplier extension of g_0                  | not supplied           |
| Gate 3U / finite-S sign / Burnol / RH                | open / open / open / open|
+------------------------------------------------------+------------------------+
```

The new order is:

```text
positive root W=C* C
        |
        v
recombine both midpoint root orientations into L_j
        |
        | one common Hilbert--Schmidt right factor
        v
raw midpoint sine R_j applied to one common source input
        |
        v
Proof 351 Julia Bessel row.
```

The point is structural.  The old formulation put a diagonal root block on
the range side, namely `C_11 R_j` or `R_j C_00*`.  Those blocks made the
Douglas inequality look like a new analytic estimate.  A legal trace cycle
instead puts both root copies into a completed physical composite.  The range
side then contains only `R_j`.

## 2. Exact two-root placement

Let `P` be the canonical midpoint projection for one consecutive pair, let
`Q=I-P`, and write

```text
Delta = P_1-P_0 = R+R*,
R     = Q Delta P.
```

For a bounded, not necessarily self-adjoint root `C`, write its midpoint
blocks as in Proof 380:

```text
C_00=P C P,    C_01=P C Q,
C_10=Q C P,    C_11=Q C Q,
W=C* C.
```

Whenever the displayed rectangular products are trace legal, Proof 380 gives

```text
Tr(W Delta)
 =2 Re [Tr(C_10* C_11 R)+Tr(C_01 R C_00*)].          (TC.1)
```

Cycle only the second term in `(TC.1)` and define the two algebraic root
components

```text
L_plus  = C_10* C_11 : QH -> PH,
L_minus = C_00* C_01 : QH -> PH.                    (TC.2)
```

They must be recombined before any factorization.  Direct block multiplication
gives the exact completed midpoint corner

```text
L = L_plus+L_minus
  =P C* (Q+P) C Q
  =P C* C Q
  =(Q W P)*.                                        (TC.3)
```

Then the same scalar is

```text
Tr(W Delta)=2 Re Tr(L R).                            (TC.3a)
```

This is not an estimate and does not discard a root orientation.  The first
component carries `C*` followed by `C`; the second carries the opposite
midpoint placement of the same two root copies.  Their sum is the one actual
detector corner.  Estimating the two summands independently would violate the
same-object cancellation guard.

## 3. The sufficient common-factor theorem

Let `K_root` be an auxiliary Hilbert space.  For each step, let
`U_j^mid : K_0 -> P_j H` be the exact midpoint input-coordinate unitary from
Proof 354, and retain Proof 351's chronological Julia prefix `Psi_(j-1)`.
Suppose the one completed physical composite in `(TC.3)` has the fixed-source
factorization

```text
L_j=U_j^mid Psi_(j-1) A_root B_j*,                   (TC.4)

A_root : K_root -> K_0,
B_j    : K_root -> (I-P_j)H,

A_root,B_j are Hilbert--Schmidt.
```

Equation `(TC.4)` is deliberately stronger than merely knowing that a
product in `(TC.3a)` is trace class.  It is the completed two-root
factorization that provides two genuinely Hilbert--Schmidt legs before the
final trace cycle.

Substitution into `(TC.3)` gives the exact pairing

```text
Tr(W Delta)
 =2 Re <B_j,R_j U_j^mid Psi_(j-1) A_root>_(S_2).     (TC.5)
```

The cycle is legal for the concrete reason

```text
Tr(L R)
 =Tr(U_j^mid Psi_(j-1) A_root B_j* R_j)
 =Tr(B_j* R_j U_j^mid Psi_(j-1) A_root)
 =<B_j,R_j U_j^mid Psi_(j-1) A_root>_(S_2).          (TC.6)
```

Both end factors in `(TC.6)` are Hilbert--Schmidt.  This is the missing
trace-preserving insertion in a form that does not require cancelling a
compact operator or using a dense-range inverse.

### The exact Douglas lifting test

Pull the moving midpoint output back to the fixed source and set

```text
Ltilde_j=(U_j^mid)* L_j : (I-P_j)H -> K_0.          (TC.6a)
```

The factorization `(TC.4)` is exactly the Hilbert--Schmidt lifting

```text
Ltilde_j=Psi_(j-1) A_root D_j,
B_j=D_j*,                                           (TC.6b)
```

where `D_j` is Hilbert--Schmidt.  Ordinary Douglas gives only the bounded
part of this statement:

```text
Ltilde_j Ltilde_j*
 <=c_j^2 Psi_(j-1) A_root A_root* Psi_(j-1)*
  <=> Ltilde_j=Psi_(j-1) A_root D_j
      with norm(D_j)<=c_j.                           (TC.6c)
```

It does not imply that `D_j` is Hilbert--Schmidt.  The Gate input is the
strictly stronger weighted ideal condition

```text
sum_j norm(D_j)_2^2/(p_j-1) <=P_root(B_root).        (TC.6d)
```

Even before the ideal estimate, `(TC.6b)` has the mandatory visibility test

```text
ker(A_root* Psi_(j-1)*) subset ker(Ltilde_j*).       (TC.6e)
```

It is not enough that `Ltilde_j` has a small Schatten norm.  Any response
outside the closed visibility subspace
`closure(Ran(Psi_(j-1) A_root))` is invisible to the Julia row and cannot be
recovered by a bounded or Hilbert--Schmidt readout.

Thus a uniform `S_2` norm of the raw detector corner, a bounded Douglas
factor, or a dense range of `A_root` cannot replace `(TC.6d)`.  This is the
same compact-range obstruction recorded in Proofs 381 and 762, now stated on
the correctly recombined two-root corner.

The factors in `(TC.4)` must be constructed after the complete physical
outer/reflected-second-support/prolate bracket and the quotient-boundary
corrections are recombined.  Applying `(TC.4)` separately to `L_plus` and
`L_minus`, or to bare `C_10`, `C_11`, `C_00`, or `C_01`, would recreate the
total-variation split forbidden by Proofs 260 and 368.

## 4. The Julia range side becomes automatic

For the actual `j`-th Euler step, apply the fixed half-angle unitaries from
Proof 355 to identify `R_j` with the range sine in Proof 354.  Pulling that
domain back to the fixed source gives exactly the row used by Proof 351:

```text
R_j U_j^mid Psi_(j-1) A_root
  = unitary output change of
    S_j J_(j-1) Psi_(j-1) A_root.                    (TC.7)
```

For one `A_root` independent of `j`, Proof 354 `(MI.14)` gives the
constant-one range ledger

```text
sum_j (p_j-1) norm(R_j U_j^mid Psi_(j-1) A_root)_2^2
 <=norm(A_root)_2^2.                                 (TC.8)
```

Thus, after `(TC.4)` has been established on the actual source carrier, the
range column in `(TC.5)` is already the actual Julia column up to a coordinate
unitary.  Its Douglas readout has norm one.  In the notation of Proof 382,
the conditional conclusion is

```text
mathcalY_root = U_coord mathcalS_(A_root),
norm(U_coord)=1.                                     (TC.9)
```

So `(JR.19)` is not a second analytic producer after this placement.  The
single unresolved producer is the common completed factorization `(TC.4)`,
with `A_root` independent of `j`.

If, in addition, the detector factors satisfy

```text
sum_j norm(B_j)_2^2/(p_j-1)
 <=P_root(B_root),                                   (TC.10)
```

then one direct-sum Cauchy--Schwarz step yields

```text
abs Q_S_near
 <=2 sqrt(P_root(B_root)) norm(A_root)_2.            (TC.11)
```

This is the desired Proof 351 consumer.  It has not been applied to CCM24
because neither `(TC.4)` nor `(TC.10)` is currently a source theorem.

## 5. Weighted Toeplitz-domain guard

Proof 769 identifies the actual fixed source coordinate as

```text
M_0=g_0 K_Theta,
M_S=g_0 ker T_(conj(Theta) q_S^(-1)).                (TC.12)
```

The supplied Burnol/CCM24 datum is the isometric multiplier

```text
U_g : K_Theta -> M_0,
U_g f=g_0 f.                                         (TC.13)
```

It is not a theorem that multiplication by `g_0` is a bounded operator on
all of `H2`.  Therefore the tempting identity

```text
C M_(g_0 q_S) P_Theta
 -M_(g_0 q_S)P_Theta(P_Theta C P_Theta)
=M_(g_0 q_S)(I-P_Theta)C P_Theta                    (TC.14)
```

cannot be used from `(TC.13)`: its right side applies `g_0` to the off-model
vector `(I-P_Theta)C P_Theta f`, which need not lie in `K_Theta`.

This is a domain issue, not a missing scalar estimate.  A bounded extension
of `U_g` is not determined by its value on `K_Theta`.  On `H=C^2`, take

```text
K=span(e_0),
U_g(e_0)=e_0,
P=e_0 e_0*,
C=e_1 e_0*.
```

Both bounded extensions

```text
E_0=P,
E_1=I
```

agree with `U_g` on `K`, while

```text
E_0 (I-P) C P=0,
E_1 (I-P) C P=(I-P) C P !=0.                        (TC.15)
```

Hence no off-model commutator formula follows from the isometric multiplier
alone.  A valid CCM24 proof of `(TC.4)` must construct its factors on the
actual physical carrier first, then use the weighted Toeplitz coordinate only
to pull the already-defined source maps back to `K_Theta`.

## 6. What the next source theorem must say

The source theorem is now narrower than Proof 382's old pair of obligations:

```text
completed physical two-root detector corner
        |
        | exact physical factorization, one fixed source input
        v
L_j=U_j^mid Psi_(j-1) A_root B_j*
        |
        | Proof 354 coordinate equivalence
        v
R_j U_j^mid Psi_(j-1) A_root = actual Julia range row.
```

It must preserve all of the following before the first absolute value:

```text
the weighted Gram correction from Proof 769;
the complete finite Euler prefix;
both root orientations in (TC.2);
the outer, reflected second-support, and prolate cancellation;
the two quotient-compression corrections from Proof 368;
the half-density residue and the fixed far-tail split.
```

The seven-copy bundle of Proof 383 remains a candidate for the fixed source
factor `A_root`.  Proof 770 does not prove that it factors the literal
recombined corner in `(TC.4)`.  It shows why that factorization, rather than a
second Douglas estimate on a diagonal-root range column, is the precise
remaining near source statement.

## 7. Evidence and verification

The algebra in `(TC.1)--(TC.9)` uses only the midpoint identities from
Proofs 354 and 380 and ordinary trace cycles through two Hilbert--Schmidt
factors.  The finite certificate factorizes the recombined matrix `L` by its
polar singular-value decomposition through one fixed finite contraction that
models `Psi_(j-1)`, checks `(TC.3a)` and `(TC.5)`, and checks the extension
ambiguity `(TC.15)`.  A separate rank-deficient prefix check exhibits the
visibility failure `(TC.6e)`.  The certificate cannot prove the actual
infinite-dimensional range inclusion required by `(TC.6c)`:

```text
python3 -B docs/proofs/770_two_root_composite_julia_insertion_probe.py
```

The underlying fixed-source range and weight facts remain:

```text
Burnol, Theorem 8:
https://arxiv.org/pdf/math/0208121

Camara--Carteiro--Ross, multiplier/Toeplitz-kernel scope:
https://arxiv.org/abs/2307.05453

Liang--Partington, Theorems 1.1--1.2:
https://arxiv.org/abs/2506.18646
```

Burnol identifies the Sonin/de Branges carrier.  Camara--Carteiro--Ross study
multiplier equivalence of Toeplitz kernels.  Liang--Partington records the
standard `h K_Theta` isometric multiplier and its weighted compressed operator
formula; it does not turn that multiplier into a bounded full-Hardy operator.
None of the three sources supplies the physical composite factorization
`(TC.4)`, the weighted completed trace, or the support-polynomial Gate estimate.

## 8. Route judgment

```text
two-root cyclic placement `(TC.3)`:                 exact;
conditional common-factor pairing `(TC.5)`:         exact;
Julia range ledger after `(TC.4)`:                   exact, constant one;
separate Douglas producer `(JR.19)`:                 no longer needed then;
actual CCM24 composite factorization `(TC.4)`:       open;
weighted g_0 off-model extension:                    not supplied;
support-polynomial Gate 3U / finite-S sign / RH:     open.
```
