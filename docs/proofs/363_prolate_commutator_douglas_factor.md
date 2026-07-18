# Proof 363: prolate commutator Douglas factor

Date: 2026-07-18

Status: exact fixed Hilbert--Schmidt factorization of a bounded-detector
commutator with a positive trace-class prolate operator.  Both commutator
orientations are carried by a two-copy square-root owner whose cost is
independent of the finite Euler set.

Together with Proofs 361--362, every fixed-source branch in the CC20
outer/second-support/prolate ledger now has a polynomial or fixed
Hilbert--Schmidt owner.  Uniform control after the complete Euler prefix and
Gram normalization remains open.  Gate 3U, the finite-`S` sign, Burnol's
identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| positive prolate square root                  | Hilbert--Schmidt          |
| prolate commutator factorization               | exact, two-copy          |
| common-factor square budget                    | trace(K)*(1+norm(W)^2)   |
| dependence on finite Euler set                 | none                      |
| signed fixed-source branch bundle              | finite direct sum        |
| prefix/Gram uniformity                         | open                      |
| finite certificate                            | supplied                 |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
## 2. Positive trace-class setup

Let `K>=0` be trace class on a Hilbert space `H`, and let `W` be bounded.  Put

```text
S=K^(1/2).                                          (PC.1)
```

Then `S` is Hilbert--Schmidt and

```text
norm(S)_2^2=Tr(K).                                  (PC.2)
```

No finite-rank truncation or eigenbasis choice is needed for the operator
identities below.

## 3. Exact two-copy factorization

Define

```text
A_K:H->H direct-sum H,
A_K x=(Sx,SWx),                                     (PC.3)

B_K:H direct-sum H->H,
B_K(y,z)=WSy-Sz.                                    (PC.4)
```

Then

```text
B_K A_K x
 =W K x-K W x
 =[W,K]x.                                           (PC.5)
```

For the opposite convention `[K,W]`, replace `B_K` by `-B_K`; the common
right factor is unchanged.

The two-copy Hilbert--Schmidt budget is

```text
norm(A_K)_2^2
 =norm(S)_2^2+norm(SW)_2^2
 <=Tr(K)(1+norm(W)^2).                              (PC.6)
```

The left factor satisfies

```text
norm(B_K)
 <=norm(S)sqrt(1+norm(W)^2)
 =sqrt(norm(K))sqrt(1+norm(W)^2).                   (PC.7)
```

Hence Douglas domination gives

```text
[W,K]*[W,K]
 <=norm(K)(1+norm(W)^2) A_K*A_K.                   (PC.8)
```

## 4. Apply it to the source prolate operator

For the fixed CC20 source scale, take

```text
K=K_prol,
W=W_g=C_g* C_g.                                     (PC.9)
```

The existing strict-angle/prolate trace results make `K_prol` positive trace
class.  Therefore `(PC.3)--(PC.8)` give a fixed common owner for

```text
[W_g,K_prol]                                        (PC.10)
```

with no Euler prefix, prime count, prime spacing, or support-displacement
condition in its Hilbert--Schmidt cost.  Root Sobolev norms enter only through
the bounded convolution norm `norm(W_g)`.

## 5. Fixed-source signed bundle

Proofs 361 and 362 give compact-window factors for both orientations of the
outer and reflected second-support crossings.  Let their right factors be

```text
A_out^+, A_out^-, A_ref^+, A_ref^-.                 (PC.11)
```

Bundle them with `(PC.3)`:

```text
A_fixed x=
 (A_out^+ x,A_out^- x,
  A_ref^+ x,A_ref^- x,
  A_K x).                                           (PC.12)
```

Every complete fixed-source three-branch commutator is then

```text
mathcalB_W=B_fixed A_fixed,                          (PC.13)
```

where `B_fixed` carries the literal signs, support compressions, and bounded
unitary/scattering dressings.  The signs are inserted before the final norm.

The common square budget has the form

```text
norm(A_fixed)_2^2
 <=C_boundary B_root norm(g)_2^2
   +Tr(K_prol)(1+norm(W_g)^2).                      (PC.14)
```

All constants in `(PC.14)` are independent of the visible finite Euler set.

## 6. What is and is not closed

Equation `(PC.13)` closes the fixed-source common-factor construction.  It
does not prove that transporting `(PC.13)` through the complete prefix and
its compressed Gram inverse preserves a uniform Douglas constant.

The remaining map is the Proof 358 dressing

```text
(I-P_<j)A_<j(I-P_K) B_fixed
  [followed by the prefix Gram normalization].       (PC.15)
```

Proof 356 forbids bounding `(PC.15)` by a product of raw prefix condition
numbers.  The fifth batch must keep the normalized frame whole and identify
the exact coisometric or shorted-metric quantity that controls `(PC.15)`.

## 7. Reproducible certificate

The companion probe chooses a positive matrix `K`, a self-adjoint detector
`W`, and checks

```text
the factorization `(PC.5)`;
the two-copy HS budget `(PC.6)`;
the left-factor bound `(PC.7)`;
the Douglas covariance inequality `(PC.8)`;
a signed direct-sum recombination with synthetic boundary factors. (PC.16)
```

Run only in the unified verification phase:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/363_prolate_commutator_douglas_factor_probe.py
```

The finite direct sum checks the algebraic bundling pattern.  The actual
outer/reflected factors are owned by Proofs 361--362.

## 8. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| prolate fixed HS owner                        | closed `(PC.3)`           |
| fixed source three-branch bundle              | closed `(PC.13)`          |
| S-uniform fixed-source square budget           | closed `(PC.14)`          |
| normalized prefix dressing                    | open, next/sole bottom   |
| Gate 3U / finite-S sign / Burnol / RH           | open / open / open / open|
+------------------------------------------------+---------------------------+
```
