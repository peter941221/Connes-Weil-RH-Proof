# Proof 261: Fixed-S trace-class gate

Date: 2026-07-15

Status: closes Gate 3L at the mathematical route-evidence level.  For every
fixed finite set of visible primes `S`, every `t in [0,1]`, and every pair of
compact smooth roots, the complete root-sandwiched synchronized band derivative
is trace class.  The same holds for its time integral and hence for the
root-sandwiched endpoint correction.

The proof keeps the complete metric inverse intact.  A trace-class root
commutator passes through the compressed inverse by the exact inverse-
commutator identity.  The transported crossing then pulls back to the base
half-line or Sonin crossing.  CC20 reduces the Sonin crossing to three
half-line crossings plus its trace-class prolate remainder.  The complete
finite-`S` Euler generator has an absolutely summable trace-norm ledger because
its `m`th coefficient is `t^(m-1)p^(-m/2)` and a crossing of length
`m log(p)` costs at most a linear factor in that length.

This result supplies ordinary trace legality only.  Its constants depend on
`S`, and the proof takes absolute values of the prime-power and Sonin branches.
It cannot prove Gate 3U.  The uniform signed estimate, the arithmetic
same-object finite-`S` trace identity, the negative-owner integration, the
Burnol identity, and RH remain open.  No Lean owner or route rewire is
authorized.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| CC20 root/half-line commutator                 | trace class, source theorem  |
| root commutator through compressed inverse     | exact                        |
| transported crossing pullback                  | exact                        |
| base half-line crossing                        | finite-interval S2 x S2      |
| base Sonin crossing                            | 3 half-lines + prolate S1    |
| fixed-S prime-power S1 sum                     | absolutely convergent        |
| instantaneous complete root-sandwiched flow    | S1                           |
| integrated fixed-S endpoint correction         | S1                           |
| ordinary trace / cyclicity                     | legal                        |
| Gate 3L                                        | closed mathematically        |
| Gate 3U                                        | open                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The proof has one direction of travel:

```text
CC20 [root,P] in S1
        |
        v
compressed metric inverse remains root-smooth
        |
        v
current crossing = bounded dressings of base crossing
        |
        v
finite crossing interval gives S2 x S2
        |
        v
fixed-S geometric Euler sum belongs to S1.             (X.1)
```

## 2. Source inputs

Work in the common logarithmic Hilbert space used by Proofs 253 and 257.  Let
`P` denote the crossed half-line projection.  A compact smooth source root
becomes a Schwartz multiplier in the Mellin coordinate and a convolution
operator `G=C_g` in the logarithmic coordinate.

CC20 proves

```text
[G,P] in S1.                                           (X.2)
```

The exact source is Connes--Consani,
*Weil positivity and Trace formula, the archimedean place*:

```text
https://arxiv.org/abs/2006.13771

weil-compo.tex:2087--2120
  Lemma quantsmooth proves that [H,f] is an infinitesimal
  of infinite order for every Schwartz multiplier f.
```

CC20 also gives the scattering and prolate identities

```text
P_hat=mathcalS* (I-P) mathcalS,
P P_hat P=R+K_prol,                                  (X.3)
```

where `mathcalS` is a convolution/scattering unitary and `K_prol` is positive
trace class.  The source locations are `weil-compo.tex:542--548` and
`1072--1076`; the rapid eigenvalue estimate appears at `982--984`.

Every root convolution commutes with `mathcalS` and with each logarithmic
translation `U_b`.  Equations `(X.2)--(X.3)` imply

```text
[G,P_hat] in S1,
[G,R] in S1,
[G,E] in S1,
[G,B] in S1,                                         (X.4)
```

for `E=P` and `B=E-R`.

CCM24 supplies the finite Euler multiplier

```text
T_(S,1)=product_(p in S)(I-p^(-1/2)U_(log p)).        (X.5)
```

See Connes--Consani--Moscovici,
*Zeta zeros and prolate wave operators*,
<https://arxiv.org/abs/2310.18423>, equation `tensorsonin1` and the Sonin
stability argument at source lines `946--1029`.  The synchronized path used by
Proofs 252--257 is

```text
T_t=product_(p in S)(I-t p^(-1/2)U_(log p)),
0<=t<=1.                                             (X.6)
```

All factors in `(X.6)` commute and are normal.  Every `T_t` is invertible for
finite `S`.

Peller's criterion gives an independent ideal check.  Sections 5.2--5.3 of
<https://arxiv.org/abs/2402.09853> state that a Hardy commutator belongs to
`S_p` exactly when its symbol belongs to `B_p^(1/p)`.  A Schwartz root lies in
`B_1^1`, so the `p=1` case agrees with `(X.2)`.  The proof below uses CC20's
stronger infinite-order statement.

## 3. The root-smooth inverse algebra

Fix one bounded root convolution `G`.  Define

```text
mathcalA_G^1
 ={D in B(H):[G,D] in S1}.                            (X.7)
```

This class is an algebra because

```text
[G,D_1D_2]=[G,D_1]D_2+D_1[G,D_2].                   (X.8)
```

It is inverse closed.  If `D` has a bounded inverse, then

```text
[G,D^(-1)]=-D^(-1)[G,D]D^(-1) in S1.                (X.9)
```

No Neumann expansion or condition-number estimate enters `(X.9)`.

For `J in {E,R}`, put

```text
H_t=T_t* T_t,
A_(J,t)=J H_t J+(I-J),
D_(J,t)=A_(J,t)^(-1).                                (X.10)
```

The extension by `I-J` turns the compressed metric into an invertible operator
on the ambient Hilbert space.  Since `G` commutes with `H_t`, equation `(X.4)`
gives

```text
[G,A_(J,t)]
 =[G,J]H_tJ+JH_t[G,J]-[G,J] in S1.                  (X.11)
```

Equations `(X.9)--(X.11)` prove

```text
[G,D_(J,t)] in S1.                                  (X.12)
```

The orthogonal metric projection onto `T_t Ran(J)` is

```text
J_t=T_t J D_(J,t) J T_t*.                            (X.13)
```

The root commutes with `T_t` and `T_t*`, so

```text
[G,J_t]
 =T_t[G,J D_(J,t)J]T_t* in S1.                      (X.14)
```

Therefore

```text
[G,E_t] in S1,
[G,R_t] in S1,
[G,B_t] in S1,
B_t=E_t-R_t.                                         (X.15)
```

Equation `(X.14)` closes the metric-dressing issue for trace legality.  Proofs
230--234 expanded compressed inverses to control compactness uniformly across
profiles.  Gate 3L only needs fixed-`S` ideal membership, and `(X.9)` supplies
it without a word expansion.

## 4. Pull the moving crossing back to the source

The right logarithmic derivative is

```text
X_t=T_t'T_t^(-1).                                    (X.16)
```

It commutes with `T_t` and every root convolution.  For `J in {E,R}`, define

```text
Z_(J,t)=(I-J_t)X_tJ_t.                               (X.17)
```

Substitute `(X.13)` into `(X.17)`.  The range identity

```text
(I-J_t)T_tJ=0                                        (X.18)
```

deletes the `J X_t J` block and yields

```text
Z_(J,t)
 =(I-J_t)T_t
   [(I-J)X_tJ]
   D_(J,t)J T_t*.                                    (X.19)
```

Thus the current metric crossing is a boundedly dressed copy of the base
crossing.  The metric inverse remains unexpanded.

Proof 257 gives the complete lower band flow

```text
Y_t
 =(I-E_t)X_tB_t-R_tX_t*Q B_t.                       (X.20)
```

The source orientation satisfies `R_tX_t*=R_tX_t*Q`.  Hence the second term in
`(X.20)` equals `R_tX_t*B_t`.  Nestedness gives `B_t<=E_t` and
`R_tB_t=0`, so

```text
Y_t=[Z_(E,t)-Z_(R,t)*]B_t.                           (X.21)
```

Equation `(X.21)` retains the complete outer-minus-Sonin flow.  Gate 3L may
estimate its two terms separately because it asks for ideal membership, not a
uniform scalar bound.

## 5. Base half-line and Sonin crossings

The complete fixed-`S` generator has the norm-convergent expansion

```text
X_t
 =-sum_(p in S)sum_(m>=1)
    t^(m-1)p^(-m/2)U_(m log p).                      (X.22)
```

For `J=E=P`, every mode in `(I-P)X_tP` is a completed half-line crossing.
For `b!=0`, the commutator `[U_b,P]` factors through one interval `I_b` of
length `|b|`:

```text
[U_b,P]=L_b R_b,
L_b:L2(I_b)->H,
R_b:H->L2(I_b).                                      (X.23)
```

For a root convolution `G=C_g`,

```text
norm(G L_b)_2^2=|b| norm(g)_2^2,
norm(R_b G*)_2^2=|b| norm(g)_2^2.                   (X.24)
```

The Sonin crossing has the same source intervals.  From `(X.3)`,

```text
R=P P_hat P-K_prol.                                  (X.25)
```

For every translation `U_b`,

```text
[U_b,R]
 =[U_b,P]P_hat P
   +P[U_b,P_hat]P
   +P P_hat[U_b,P]
   -[U_b,K_prol],                                    (X.26)

[U_b,P_hat]
 =-mathcalS*[U_b,P]mathcalS.                         (X.27)
```

Also

```text
(I-R)U_bR=(I-R)[U_b,R]R.                             (X.28)
```

Equations `(X.26)--(X.28)` express one Sonin crossing as three boundedly
dressed half-line crossings plus a trace-class prolate term.  They preserve the
same translation length `|b|`.

## 6. Dressed crossing lemma

Let `A_0,A_1` be bounded operators satisfying

```text
[G_eta,A_0] in S1,
[A_1,G_xi*] in S1.                                  (X.29)
```

For a crossing factorization `(X.23)`, write

```text
G_eta A_0 [U_b,P] A_1 G_xi*

 =(G_eta A_0 L_b)(R_b A_1 G_xi*).                   (X.30)
```

The first factor is Hilbert--Schmidt because

```text
G_eta A_0L_b
 =A_0G_eta L_b+[G_eta,A_0]L_b.                       (X.31)
```

The first term in `(X.31)` is Hilbert--Schmidt by `(X.24)`; the second is trace
class and hence Hilbert--Schmidt.  The right factor obeys the companion identity

```text
R_bA_1G_xi*
 =R_bG_xi*A_1+R_b[A_1,G_xi*]                         (X.32)
```

and is Hilbert--Schmidt for the same reason.  Therefore `(X.30)` belongs to
`S1`.

The factor norms satisfy a coarse bound

```text
norm(G_eta A_0L_b)_2
 <=c_0(1+sqrt(|b|)),

norm(R_b A_1G_xi*)_2
 <=c_1(1+sqrt(|b|)).                                 (X.33)
```

Consequently

```text
norm(G_eta A_0[U_b,P]A_1G_xi*)_1
 <=C(1+|b|).                                         (X.34)
```

All dressings in `(X.19)--(X.21)` satisfy `(X.29)` by `(X.4)`,
`(X.12)`, `(X.14)`, and `(X.15)`.  Equations `(X.26)--(X.28)` handle the
Sonin branch.  Terms containing `K_prol` already belong to `S1` and remain
there after bounded dressing.

## 7. Fixed-S trace-norm summability

Insert `b=m log(p)` into `(X.34)`.  For `0<=t<=1`,

```text
sum_(m>=1)
 t^(m-1)p^(-m/2)(1+m log(p))

 <=p^(-1/2)/(1-p^(-1/2))
   +log(p)p^(-1/2)/(1-p^(-1/2))^2
 <infinity.                                          (X.35)
```

The set `S` is finite, so the sum over `p in S` is finite.  The prolate
remainder uses the easier geometric sum without the `m log(p)` factor.

For each fixed finite `S`, the factors in `(X.19)` have bounded operator norms
and bounded root-commutator trace norms, uniformly for `t in [0,1]`.  Indeed,

```text
s_min(T_t)>=product_(p in S)(1-p^(-1/2))>0.          (X.36)
```

Equations `(X.9)--(X.15)` then give uniform fixed-`S` bounds for every metric
dressing.  Combining `(X.21)`, `(X.34)`, and `(X.35)` proves

```text
C_eta Y_t C_xi* in S1,
C_eta Y_t* C_xi* in S1,

C_eta B_t' C_xi*
 =C_eta(Y_t+Y_t*)C_xi* in S1.                        (X.37)
```

The majorant in `(X.35)` also proves continuity in the trace norm and gives

```text
sup_(0<=t<=1) norm(C_eta B_t'C_xi*)_1<infinity       (X.38)
```

for fixed `S`.

The constant in `(X.38)` depends on `S`.  In particular, the metric dressing
can carry the full finite-`S` condition number.  Gate 3L permits that
dependence; Gate 3U does not.

## 8. Endpoint trace and corrected Dirichlet pairing

Trace-norm continuity makes the synchronized flow Bochner integrable in `S1`:

```text
C_eta(B_1-B_0)C_xi*
 =integral_0^1 C_eta B_t'C_xi* dt
 in S1.                                               (X.39)
```

The ordinary trace is continuous on `S1`, so

```text
Tr(C_eta(B_1-B_0)C_xi*)
 =integral_0^1 Tr(C_eta B_t'C_xi*) dt.                (X.40)
```

This also legalizes Proof 253's scalar Dirichlet identity.  For the diagonal
detector `W=C_g* C_g`, equation `(X.14)` gives

```text
[W,J_t] in S1,
J in {E,R}.                                          (X.41)
```

The Euler generator `h_t=Re(X_t)` is bounded for fixed `S`, so `[M_(h_t),J_t]`
is bounded.  Define the extended trace pairing

```text
mathfrakD_(J_t)(W,h_t)
 :=Tr([W,J_t]* [M_(h_t),J_t]).                        (X.42)
```

The first factor in `(X.42)` is trace class and the second is bounded.  If both
commutators happen to be Hilbert--Schmidt, `(X.42)` agrees with their
Hilbert--Schmidt inner product.  Gate 3L needs only the trace-class/bounded
pairing.

Ordinary cyclicity and the projection derivative give

```text
Tr(C_g B_t'C_g*)
 =mathfrakD_(E_t)(W,h_t)
   -mathfrakD_(R_t)(W,h_t).                           (X.43)
```

Equation `(X.43)` is the legal version of Proof 253's `D_E-D_R` formula.  It
does not bound the difference uniformly in `S`.

## 9. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/261_fixed_s_trace_class_gate_probe.py
```

The matrix certificate verifies

```text
+--------------------------------------+-----------+
| check                                | error     |
+--------------------------------------+-----------+
| root/transport commutator            | 0         |
| transported projection identities    | 2.34e-16  |
| crossing pullback                    | 6.03e-16  |
| inverse commutator                   | 1.12e-15  |
| transported root commutator          | 1.11e-15  |
| complete lower flow                  | 3.01e-16  |
| band derivative                      | 2.78e-16  |
| extended Dirichlet trace             | 1.81e-14  |
+--------------------------------------+-----------+
```

For `S={2,3,5,7,11}` and `t=0.63`, the closed prime-power majorant is
`10.59827533`.  Eighty modes recover it with maximum error `4.44e-16`.  The
maximum checked error across both layers is `1.81e-14`.

Finite matrices do not prove trace-class membership.  They check the exact
metric, inverse, pullback, and nested-flow algebra.  The continuous ideal proof
uses CC20 `(X.2)--(X.4)`, the interval factors `(X.23)--(X.24)`, and the
summation `(X.35)`.

## 10. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| root-smooth inverse algebra                    | exact                        |
| current-to-base crossing pullback              | exact                        |
| complete outer-minus-Sonin flow                | exact                        |
| CC20 half-line root commutator                 | source-backed S1             |
| CC20 Sonin/prolate reduction                   | source-backed                |
| dressed finite crossing                        | S2 x S2, hence S1            |
| fixed-S prime-power trace-norm series          | absolutely convergent        |
| instantaneous root-sandwiched B_t'             | S1                           |
| integrated root-sandwiched B_1-B_0             | S1                           |
| ordinary trace / time integration              | legal                        |
| extended D_E-D_R trace pairing                 | legal and exact              |
| Gate 3L                                        | closed mathematically        |
| Gate 3U                                        | open                         |
| arithmetic same-object finite-S identity       | open                         |
| negative-owner integrated smallness            | open                         |
| Burnol all-zero identity                       | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 261 removes ordinary trace legality from the active analytic bottom.  The
remaining estimate must use `(X.43)` as one signed difference and keep its
constant independent of `S`.  The trace-norm proof above is unsuitable for
that task because `(X.35)` and the metric dressing both take absolute values and
retain finite-`S` growth.

Successor note: Proof 262 integrates `(X.43)` exactly and replaces the
time-dependent form by the endpoint identity

```text
Tr_B(mathcalD_S*
  (C_0[W,E]B-[W,R]R L_S)).
```

This is the active Gate 3U owner.  It keeps the outer and Sonin detector
crossings paired and exposes their compact-root support before any Markov
expansion.
