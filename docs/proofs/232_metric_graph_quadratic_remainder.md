# Proof 232: metric graph quadratic remainder

Date: 2026-07-14

Status: exact reduction of the nonlinear metric correction.  The orthogonal
graph projection has one linear boundary-crossing tangent.  Every term beyond
that tangent contains at least two copies of the source commutator
`[b,u]` or its adjoint.  After sandwiching by one genuine compact smooth
`Q`-root, the two-crossing terms have a Hilbert--Schmidt root kernel by CC20's
smoothed-commutator factorization.  Thus the nonlinear graph and Schur
corrections cannot be the remaining essential channel.  The only unresolved
compactness term is an explicitly named, boundedly dressed, single-crossing
linear channel.  Its identification with Proof 229's complete Euler profile
is not proved here.  The integrated sign and RH remain open.  No Lean owner
is authorized.

## 1. Same-object Schur data

Use Proof 231's notation.  Let `r<=e` be orthogonal projections, put

```text
b=e-r,
T=I-alpha u,
h=T* T,
0<=alpha<1,
m=(1-alpha)^2.                                        (Q.1)
```

On `Ran(r) direct-sum Ran(b)`, define

```text
A=r h r,
C=r h b,
D=b h b,
S=D-C* A^(-1) C,
Z=b-r A^(-1) C.                                       (Q.2)
```

All four positive corner operators have inverse norm at most `m^(-1)`.
Put

```text
V=T b,
W=T r A^(-1) C.                                       (Q.3)
```

The bare metric image of `b` and the nested metric complement are

```text
q_alpha=V D^(-1) V*,
b_alpha=(V-W) S^(-1) (V-W)*.                          (Q.4)
```

These are the orthogonal projections onto `T Ran(b)` and the orthogonal
complement of `T Ran(r)` inside `T Ran(e)`, respectively.  Formula `(Q.4)` is
Proof 224's Schur owner; no new projection or carrier is introduced.

## 2. Exact tangent of one graph projection

Decompose the ambient Hilbert space as

```text
Ran(b) direct-sum Ran(I-b).                            (Q.5)
```

The `b` component of `V` is invertible because

```text
M=b T b,
norm(M^(-1))<=1/(1-alpha).                             (Q.6)
```

Set

```text
J=(I-b)T b,
L=J M^(-1):Ran(b)->Ran(I-b).                          (Q.7)
```

Then `T Ran(b)` is the graph of `L`.  If

```text
R_L=(I+L* L)^(-1),                                    (Q.8)
```

the graph projection is exactly

```text
q_alpha = [ R_L          R_L L*   ]
          [ L R_L        L R_L L* ].                  (Q.9)
```

The projection onto the base is `b=diag(I,0)`.  Subtract its linear tangent

```text
T_L=[ 0  L* ]
    [ L   0 ].                                        (Q.10)
```

Using `R_L-I=-R_L L*L`, one obtains the exact remainder

```text
q_alpha-b-T_L
 = [ -R_L L*L         -R_L L*L L* ]
   [ -L R_L L*L        L R_L L*   ].                  (Q.11)
```

Every block in `(Q.11)` contains at least two factors from `{L,L*}`.  This is
an exact algebraic statement, not a small-`alpha` expansion.

## 3. Exact tangent of the nested Schur correction

Expand the second formula in `(Q.4)` and subtract `q_alpha`:

```text
b_alpha-q_alpha
 =V(S^(-1)-D^(-1))V*
  -W S^(-1)V*-V S^(-1)W*
  +W S^(-1)W*.                                       (Q.12)
```

The resolvent identity is

```text
S^(-1)-D^(-1)
 =S^(-1) C* A^(-1) C D^(-1).                         (Q.13)
```

Therefore the only part of `(Q.12)` that is linear in the off-diagonal
metric block `C` is

```text
T_C=-W D^(-1)V*-V D^(-1)W*.                          (Q.14)
```

Subtracting `(Q.14)` from `(Q.12)` gives

```text
R_C=
  V(S^(-1)-D^(-1))V*
 -W(S^(-1)-D^(-1))V*
 -V(S^(-1)-D^(-1))W*
 +W S^(-1)W*.                                        (Q.15)
```

The first and fourth terms in `(Q.15)` contain two copies of `C` or `C*`.
The middle terms contain three.  Hence the complete metric correction has the
exact decomposition

```text
b_alpha-b = Lambda_alpha + R_alpha,

Lambda_alpha=T_L+T_C,
R_alpha=(q_alpha-b-T_L)+R_C,                          (Q.16)
```

where every summand of `R_alpha` contains at least two boundary crossings.

## 4. Both tangents have the same source commutator

Let

```text
delta=norm([b,u]).                                    (Q.17)
```

The graph crossing in `(Q.7)` is exactly

```text
J=alpha (I-b)[b,u]b.                                  (Q.18)
```

Since `r b=0`, the Schur crossing is exactly

```text
C=alpha r([b,u]+[b,u*])b.                             (Q.19)
```

Thus both `L` and `W` contain one copy of the same source failure.  The other
factors in `Lambda_alpha` are the bounded metric factors

```text
T, M^(-1), A^(-1), D^(-1).                            (Q.20)
```

In particular,

```text
norm(L)<=alpha delta/(1-alpha),
norm(C)<=2alpha delta,
norm(W)<=2alpha(1+alpha)delta/m.                       (Q.21)
```

Equations `(Q.11)` and `(Q.15)` consequently imply a genuine quadratic
estimate

```text
norm(R_alpha)<=K_alpha delta^2,                        (Q.22)
```

for an explicit rational function `K_alpha`, finite on every closed interval
`0<=alpha<=a<1`.  One coarse bound follows by combining

```text
norm(q_alpha-b-T_L)
 <=2 norm(L)^2(1+norm(L)),

norm(S^(-1)-D^(-1))
 <=4 alpha^2 delta^2/m^3                              (Q.23)
```

with `(Q.15)`.  The route uses the factor count, not the size of this coarse
constant.

## 5. Why the quadratic remainder is root Hilbert--Schmidt

For a compact smooth root `g`, CC20 proves that a smoothed Hardy-boundary
commutator is trace class, and its one-crossing version is
Hilbert--Schmidt.  The exact source locations used here are:

```text
CC20, https://arxiv.org/abs/2006.13771
  original TeX lines 542--548: scattering conjugacy of the cutoffs
  original TeX lines 960--984: rapid prolate singular-value decay
  original TeX lines 1072--1103: Sonin plus trace-class prolate correction
  original TeX lines 2087--2120: smoothed commutator theorem
```

Proof 226 already transports this statement to the same Sonin projection and
shows that the compressed metric inverses have trace-class commutators with
the root smoothing multiplier.  Hence a word with two source crossings can
be factored, after the genuine `Q`-root is inserted, as

```text
root smoothing
  -> one Hilbert--Schmidt boundary block
  -> bounded metric word
  -> one Hilbert--Schmidt boundary block
  -> root smoothing.                                  (Q.24)
```

The product in `(Q.24)` is trace class.  Polarizing in two roots
`eta,xi` and applying Hilbert--Schmidt Cauchy--Schwarz gives an `L2(I x I)`
kernel for the induced root form.  The prolate correction is already trace
class and remains in the same class after bounded metric multiplication.

All blocks in `R_alpha` have the factorization `(Q.24)` by
`(Q.11)`, `(Q.15)`, `(Q.18)`, and `(Q.19)`.  The Neumann ratios for the corner
inverses are uniformly below `2sqrt(2)/3` by Proof 226, so the polynomial word
weights introduced by the fixed second-order `Q` operation remain summable.
Therefore:

```text
the post-Q finite-root-window operator induced by R_alpha
is Hilbert--Schmidt, hence compact.                    (Q.25)
```

This is stronger than ambient ideal containment: it uses the two explicit
crossings before taking the root trace.

## 6. The one remaining compactness term

The nonlinear metric correction is closed by `(Q.25)`.  The remaining term
is exactly

```text
Lambda_alpha
 =L+L*
  -W D^(-1)V*-V D^(-1)W*.                            (Q.26)
```

It has one and only one source crossing in each summand.  Ambient boundedness
does not prove its post-`Q` compactness.  The next theorem must show that the
internal Toeplitz resolvents `M^(-1),A^(-1),D^(-1)` preserve Proof 229's
cellwise ledger:

```text
HS-summable interiors
  plus operator-norm-summable logarithmic chirps.      (Q.27)
```

This is now a linear profile-module problem.  No quadratic graph amplitude,
Schur inverse correction, or oblique-defect square remains in that gate.

## 7. Reproduction

Run in WSL:

```text
python3 -B docs/proofs/232_metric_graph_quadratic_remainder.py
python3 -B docs/proofs/232_metric_graph_quadratic_remainder.py --prime 3
```

The deterministic certificate independently checks:

```text
the Schur projection against the directly moved nested complement;
the graph projection formula;
the source-commutator factorizations (Q.18)--(Q.19);
the exact tangent/remainder decomposition (Q.16);
quadratic shrinkage of R_alpha against norm([b,u]).
```

Finite matrices do not certify the infinite-dimensional root ideal.  They
check the algebra and the predicted order.  The root-Hilbert--Schmidt result
is the factorization `(Q.24)` using the named CC20 smoothing theorem.

## 8. Route judgment

```text
metric graph linear tangent:                   exact
nested Schur linear tangent:                   exact
all nonlinear metric terms:                    at least two crossings
nonlinear post-Q root operator:                Hilbert--Schmidt / compact
remaining metric compactness channel:          Lambda_alpha only
linear Toeplitz-profile stability:             open
integrated three-row sign:                     open
Lean owner or route rewire:                    none
RH:                                             unproved
```

The next proof must attack `(Q.26)` as one linear source-crossing profile and
must not reopen the quadratic metric amplitude.
