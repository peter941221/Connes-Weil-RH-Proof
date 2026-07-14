# Proof 222: metric-projection boundary telescoping repair

Date: 2026-07-14

Status: exact local principal-coefficient correction and reproducible
finite-section certificate.  The half-line endpoint metric projection does
not have the factor-two `p^2` mismatch claimed in Proof 042.  Its interrupted
boundary word removes one of the two length-`log(p)` cells, and the full
relative half-line projection has coefficient `p^(-m/2) log(p)` at every
prime power.  This invalidates the stated local no-go and reopens the global
metric-projection coefficient gate; it does not construct the global fixed-S
post-Q remainder, prove its sign, or prove RH.

## 1. Source-owned multiplier

For `S={infinity,p}`, CCM24 constructs the bounded Sonin isomorphism
`theta_S`.  In the multiplicative Fourier coordinate its finite-place factor
is

```text
T_a=I-a U_(-L),
a=p^(-1/2),
L=log(p),
(U_b f)(x)=f(x+b).                                      (B.1)
```

This is the formula

```text
F_mu w_S(theta_S(f))(s)
 =(1-p^(-1/2-is)) F_mu w_infinity(f)(s)
```

in CCM24 v2, `mainc2m24fine.tex:946-981`.  The same source proves that
`theta_S` is a bounded isomorphism from the archimedean Sonin space onto the
semilocal Sonin space at lines `983-1029`.  Consequently, if `R` is the
archimedean Sonin projection, the orthogonal semilocal projection is the
metric projection onto `T_a Ran(R)`.

Proof 042 tested the local half-line principal part of this projection and
claimed that its `m=2` coefficient is twice the Weil coefficient.  The error
is already visible and repairable in that same half-line quotient.

Primary source:

```text
Alain Connes, Caterina Consani, and Henri Moscovici,
Zeta Zeros and Prolate Wave Operators: Semilocal Adelic Operators, v2,
https://arxiv.org/abs/2310.18423
```

## 2. Translation-fiber model

Use the project translation convention

```text
(U_L f)(x)=f(x+L).
```

The source factor in `(B.1)` uses `U_(-L)`.  On the half-line boundary that it
crosses, index cells in the decreasing log direction and relabel `n` by `-n`.
Then the same source translation becomes the backward bilateral shift below.
Using the opposite boundary swaps `F(mL)` with `F(-mL)`; their paired sum is
unchanged.

Decompose the line into cells of length `L`:

```text
L2(R)=L2([0,L)) tensor ell2(Z),
U_L=I tensor S,
S e_n=e_(n-1).                                         (B.2)
```

Let `P` be the projection onto the nonnegative cells `n>=0`, and put

```text
T_a=I-aS,
P_a=orthogonal projection onto T_a Ran(P),
0<a<1.                                                  (B.3)
```

The continuous `L2([0,L))` factor will supply exactly one factor `L` in the
trace.  All boundary algebra takes place in `ell2(Z)`.

## 3. Exact graph projection

For `z=sum_(j>=0) z_j e_j` in `Ran(P)`, solve

```text
z=P T_a x,
x in Ran(P).                                            (B.4)
```

The recursion is

```text
x_j=z_j+a x_(j+1),
x_0=sum_(j>=0) a^j z_j.                                (B.5)
```

The negative component of `T_a x` is therefore

```text
(I-P)T_a x
 =-a x_0 e_(-1)
 =-sum_(j>=0) a^(j+1) z_j e_(-1).                      (B.6)
```

Thus `T_a Ran(P)` is the graph of the rank-one operator

```text
D_a=-|e_(-1)><v_a|,
v_a=sum_(j>=0) a^(j+1)e_j,
||v_a||^2=a^2/(1-a^2).                                 (B.7)
```

The standard graph-projection formula now gives, relative to
`Ran(P) direct-sum Ran(I-P)`,

```text
P(P_a-P)P
  =-(1-a^2)|v_a><v_a|,

(I-P)P_aP
  =-(1-a^2)|e_(-1)><v_a|,

P P_a(I-P)
  =-(1-a^2)|v_a><e_(-1)|,

(I-P)P_a(I-P)
  =a^2|e_(-1)><e_(-1)|.                               (B.8)
```

The raw scalar terms cancel on the central diagonal.  More importantly, the
off-diagonal graph row and the positive-cell rank-one block telescope on every
nonzero translation diagonal.

## 4. All-order Laurent coefficients

Let `Delta_a=P_a-P`, use matrix entries

```text
(Delta_a)_(j,i)=<e_j,Delta_a e_i>,
```

and define the sum along translation degree `k` by

```text
q_k(a)=sum_(i-j=k) (Delta_a)_(j,i).                    (B.9)
```

For `k>0`, the positive-positive block in `(B.8)` contributes

```text
-(1-a^2) sum_(j>=0) a^(j+1)a^(j+k+1)=-a^(k+2),        (B.10)
```

while the graph row contributes

```text
-(1-a^2)a^k.                                           (B.11)
```

Their sum is exactly `-a^k`.  The adjoint block gives the same result for
negative `k`.  At `k=0`, the positive block contributes `-a^2` and the
negative diagonal contributes `+a^2`.  Hence

```text
q_0(a)=0,
q_k(a)=-a^|k|,  k!=0.                                  (B.12)
```

Let `C_F` be a legally smoothed convolution operator with kernel value
`F(x-y)`.  Its product with `Delta_a` has trace

```text
Tr(C_F Delta_a)
 =-L sum_(m>=1) a^m [F(mL)+F(-mL)].                   (B.13)
```

The factor `L`, rather than `mL`, comes from the one fundamental boundary cell
`[0,L)`.  The geometric series is absolutely summable.  For a compact smooth
convolution square, the same smoothing/factorization used by CC20 makes the
trace legal.

Substituting `a=p^(-1/2)` and `L=log(p)` turns `(B.13)` into

```text
-sum_(m>=1) p^(-m/2) log(p)
   [F(m log(p))+F(-m log(p))],                         (B.14)
```

which is exactly the signed finite-prime Weil series at `p`.

## 5. The `p^2` cancellation missed by Proof 042

Proof 042 uses the algebra

```text
(I-P) U_L P U_L P
 =(I-P)U_L^2P-(I-P)U_L(I-P)U_LP.                      (B.15)
```

It assigns the first word a boundary length `2L`, which is correct.  It then
calls the second word a two-boundary compact remainder.  That classification
is false: after the first translation enters `Ran(I-P)`, the second
translation remains in `Ran(I-P)`.  There is only one `P` to `I-P` crossing.

The two supports are explicit:

```text
(I-P)U_L^2P:
  [0,2L) -> [-2L,0),       boundary length 2L;

(I-P)U_L(I-P)U_LP:
  [0,L)  -> [-2L,-L),      boundary length L.          (B.16)
```

Subtracting them leaves

```text
[L,2L) -> [-L,0),         boundary length L.           (B.17)
```

Therefore the complete second-order term is

```text
-a^2 L [F(2L)+F(-2L)],                                (B.18)
```

not the factor-two value `-2a^2L[...]`.  Formula `(B.12)` proves the same
telescoping at every order.

The reusable rule is stricter than counting projection letters:

```text
an internal P or (I-P) is only a compression;
it counts as another boundary crossing only if the adjacent translation
actually changes the side of the boundary.                              (B.19)
```

This is the same failure mode already identified independently in Proof 206
for an inverse compressed metric.

## 6. What is and is not reopened

Equation `(B.14)` removes the stated mathematical reason for rejecting the
endpoint metric projection in Proofs 034, 036, 038, and 042.  Their source
metric, orthogonal-projection formula, and local finite-prime sign remain
valid; the factor-two verdict does not.

It does not repair the separate common-domain objection in Proof 040.  The
actual global theorem must still prove, on one named convolution-root Hilbert
space, that:

```text
CCM24 metric Sonin projection
  = archimedean positive owner
      - complete finite-prime series
      + one explicit fixed-S post-Q remainder;          (B.20)

the remainder is self-adjoint on the common Q form domain;
the remainder has the sign required by the route vanishing subspace.
```

CC20's source identity

```text
P P_hat P
 = R_Sonin + sum_n lambda_n^2 |zeta_n><zeta_n|
```

at `weil-compo.tex:1072-1076` is the natural next bridge: it separates the
Sonin projection from a trace-class angle correction.  It has not yet been
combined with `(B.8)` into the global fixed-S post-Q owner.

Primary source:

```text
Alain Connes and Caterina Consani,
Weil Positivity and Trace Formula, the Archimedean Place,
https://arxiv.org/abs/2006.13771
```

## 7. Reproduction

The companion script constructs finite metric projections directly from
`T_a=I-aS`, without inserting the expected coefficients.  It checks
idempotence, the diagonal sums `(B.12)`, the trace `(B.13)`, and the `2-1=1`
boundary count in `(B.16)--(B.17)`.

The default `p=2` run gives

```text
p2 boundary counts:       2, 1, 1
radius-64 p2 ratio:       1.000000000000
maximum coefficient error: 1.715e-14
convolution trace error:    2.687e-14
```

Independent runs at `p=3` and `p=101` also give `p2 ratio = 1` to displayed
precision and finish with `certificate=PASS`.

```text
python3 -B docs/proofs/222_metric_projection_boundary_telescoping_repair.py
```

## 8. Route judgment

```text
CCM24 one-prime multiplier T_a:             source-exact
orthogonal metric projection:               source-owned geometry
central scalar cancellation:                exact
p^2 half-line boundary coefficient:         repaired from 2L to L
all half-line p^m boundary coefficients:     a^m L exactly
Proof 042 factor-two rejection:              invalid
global metric-projection coefficient gate:  reopened, not yet passed
global fixed-S post-Q identity:              still open
same-domain remainder sign:                  still open
Lean owner or route rewire:                  none yet
RH:                                          unproved
```
