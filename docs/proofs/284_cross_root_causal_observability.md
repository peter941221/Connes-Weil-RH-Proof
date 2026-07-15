# Proof 284: Cross-root causal observability pairing

Date: 2026-07-15

Status: exact fixed-`S` extension of Proof 270's renewal column to the
non-Hermitian cross detector from Proof 283.  The prolate left reward must use
the detector adjoint.  With that correction, the moving cross-root cocycle,
the endpoint response, and the causal renewal-column pairing are three exact
coordinates of one scalar.

This proof does not estimate that scalar uniformly in `S`.  The stopped
cross-root disintegration, Gate 3U, the finite-`S` sign, the arithmetic
same-object trace identity, Burnol's identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| moving cross-root transgression                | exact, Proof 283             |
| cross-root centered numerator                  | exact                        |
| prolate left reward A R W* Q B                 | mandatory                    |
| old Hermitian-only reward A R W Q B            | rejected                     |
| complete three-branch factor N_W=L_W* K        | exact                        |
| right renewal column                           | isometry                     |
| endpoint/causal column pairing                 | exact for fixed S            |
| compact-support stopped scalar estimate        | open                         |
| Gate 3U and RH                                 | open / unproved              |
+------------------------------------------------+------------------------------+
```

The completed identity is

```text
2 integral_0^1 movingBandJet_(eta,xi,alpha) dalpha

 =Q_S(eta,xi)

 =Tr_B(C_(L,W_(eta,xi))* C_K).                    (AU.1)
```

Equation `(AU.1)` is an identity of a factorized compact-root response.  It is
not a definition of the forbidden raw point trace
`Tr(U_z(B_(S,1)-B))`.

## 2. Cross detector and causal owner

Let `eta,xi` be compact roots in the same source window and put

```text
W=W_(eta,xi)=C_xi* C_eta,

F_(eta,xi)=xi^star*eta.                            (AU.2)
```

In general,

```text
W* =W_(xi,eta) !=W.                                (AU.3)
```

Use Proofs 264--270 at the endpoint with

```text
C=I-E,
B=E-R,
A=T_S^(-1),
K=E A B,
Gamma=K* K,
Delta=B-Gamma,
D=Delta^(1/2).                                     (AU.4)
```

The ordered centered numerator on `Ran(B)` is

```text
N_W=K* W K-B W B Gamma.                            (AU.5)
```

Proof 266's algebra is linear in `W`; it does not require `W=W*`.  Its three
physical branches are

```text
O_W=-B A* C[W,E]E A B,

S_W=B(I-Q)[W,Q]R A*E A B,

P_W=B Q W R A*E A B,

N_W=O_W+S_W+P_W.                                   (AU.6)
```

The outer, second-support, and prolate terms in `(AU.6)` must remain one
signed numerator.

## 3. The adjoint correction

Proof 270 explicitly assumed a Hermitian detector.  For the cross detector,
define the left rewards by

```text
L_O(W)=-[W,E]* C A B,

L_S(W)=A R[W,Q]*(I-Q)B,

L_P(W)=A R W* Q B,

L_W=L_O(W)+L_S(W)+L_P(W).                          (AU.7)
```

Here every displayed `*` is an operator adjoint.  Taking adjoints before
multiplying by `K` gives

```text
L_O(W)* K=O_W,

L_S(W)* K=S_W,

L_P(W)* K=P_W.                                    (AU.8)
```

For the last line,

```text
(A R W* Q B)* E A B
 =B Q W R A*E A B.                                (AU.9)
```

Therefore

```text
N_W=L_W* K.                                       (AU.10)
```

The former Hermitian-only expression

```text
L_P^old(W)=A R W Q B                              (AU.11)
```

produces `B Q W* R A*E A B`, not the route-owned `P_W`.  It agrees with
`(AU.7)` only when `W=W*`.  This is a structural adjoint error, not a numerical
tolerance issue.

Notice that `L_W` is conjugate-linear in `W`, while `L_W* K` and the final
scalar are linear in `W`.  This is exactly the variance needed by Proof 283's
sesquilinear endpoint response.

## 4. Renewal-column pairing

Define the right survivor column and the corrected left reward column by

```text
C_K x=(K D^k x)_(k>=0),

C_(L,W) x=(L_W D^k x)_(k>=0).                     (AU.12)
```

Since `Gamma=B-D^2` and `D` commutes with `Gamma`, Proof 270's telescope is
unchanged:

```text
C_K* C_K
 =sum_(k>=0)D^k Gamma D^k
 =B.                                               (AU.13)
```

Thus the right column is an isometry on `Ran(B)`.  For every renewal level,
fixed-`S` trace legality from Proof 261 and `(AU.10)` give

```text
Tr_B(N_W Delta^k)
 =Tr_B((L_W D^k)*(K D^k)).                         (AU.14)
```

Summing in the original ordered renewal gives

```text
Tr_B(N_W Gamma^(-1))
 =Tr_B(C_(L,W)* C_K).                              (AU.15)
```

In the source problem, the right side of `(AU.15)` denotes the same extended
paired trace limit as Proof 270.  It does not assert that either column is
individually Hilbert--Schmidt or that `C_(L,W)*C_K` may be bounded by the
product of two positive column norms.

## 5. Moving, endpoint, and causal coordinates

Proof 283 gives

```text
Q_S(eta,xi)

 =2 integral_0^1 [
    Tr(B_alpha W C_alpha H_alpha B_alpha)
   -Tr(R_alpha W B_alpha H_alpha R_alpha)
   ] dalpha.                                       (AU.16)
```

Proofs 264--270 give the endpoint causal coordinate

```text
Q_S(eta,xi)=Tr_B(N_W Gamma^(-1)).                  (AU.17)
```

Combining `(AU.15)--(AU.17)` proves `(AU.1)`:

```text
+--------------------------+
| moving synchronized flow |
+------------+-------------+
             |
             v
+------------+-------------+     +--------------------------+
| compact-root endpoint Q  | --> | signed causal columns    |
+--------------------------+     +--------------------------+

same scalar; no branch norm and no raw point trace.          (AU.18)
```

The adjoint symmetry is automatic:

```text
Q_S(xi,eta)=conj(Q_S(eta,xi)),                      (AU.19)
```

because `W_(xi,eta)=W_(eta,xi)*` and the endpoint projection difference is
self-adjoint.  The corrected column formula preserves this symmetry.

## 6. Compact support enters before scalar disintegration

The endpoint multiplier in `(AU.2)` is convolution by `F_(eta,xi)`, and

```text
supp(eta),supp(xi) subset [-B_root,B_root]

  => supp(F_(eta,xi)) subset [-2B_root,2B_root].     (AU.20)
```

The legal order for the successor is

```text
corrected complete left reward L_O+L_S+L_P
  -> pair with the right survivor at each renewal level
  -> write the completed paired kernel in source coordinates
  -> insert F_(eta,xi) and clip relative displacement
  -> disintegrate only the first unmatched causal displacement
  -> one absolute value after the complete signed scalar.      (AU.21)
```

The following orders are forbidden:

```text
norm(C_(L,W)) before pairing;

norm(L_O)+norm(L_S)+norm(L_P);

pointwise Tr(U_z(B_S-B));

prime-path expansion before the support clip;

replacing W* by W in the prolate left reward.                  (AU.22)
```

## 7. Finite certificate

The companion certificate builds a genuinely complex cross detector and
checks `(AU.6)--(AU.19)` independently.  The default cohort
(`multiplicity=8`, `seed=284`) reports

```text
correct left-factor error            2.13e-16,
right-column isometry error          7.08e-16,
column-pairing error                 2.36e-16,
adjoint-symmetry error               4.24e-17,
polarization error                   5.05e-17,
wrong old prolate-factor error       1.01e-2.
```

The alternate cohort (`multiplicity=10`, `seed=2284`) reports

```text
correct left-factor error            1.58e-16,
right-column isometry error          1.24e-15,
column-pairing error                 1.09e-16,
adjoint-symmetry error               8.20e-17,
polarization error                   5.62e-17,
wrong old prolate-factor error       6.18e-3.
```

Both responses have nonzero real and imaginary parts.  The old formula fails
by many orders of magnitude above the exact-algebra errors in both cohorts.
These are finite-dimensional algebra certificates, not a continuous uniform
estimate.

## 8. Active analytic target

Proof 284 closes the cross-root ownership gap but not the hard estimate.  The
next theorem must construct a scalar disintegration of the already paired
quantity

```text
sum_(k>=0)Tr_B((L_W D^k)*(K D^k)),                  (AU.23)
```

in which each term is expressed through the compact cross-correlation before
causal histories are separated.  A suitable owner has the schematic form

```text
Tr_B((L_W D^k)*(K D^k))
 =integral_(|z|<=2B_root) F_(eta,xi)(z)
    d nu_(S,k)(z),                                  (AU.24)
```

where `(AU.24)` is defined from the completed three-branch paired kernel, not
from a raw translated projection trace.  The required proof must then pair
equal histories, expose only the first missing displacement, and obtain a
bound for the complete signed sum uniformly in `S`.

Proof 284 does not assert the existence or bounded variation of the schematic
measure in `(AU.24)`.  Those are part of the next analytic theorem.  In
particular, total variation would recreate Proof 260's rejected nuclear-norm
estimate.

## 9. Reproduction

Run from the repository root:

```text
python3 -B docs/proofs/284_cross_root_causal_observability_probe.py

python3 -B docs/proofs/284_cross_root_causal_observability_probe.py \
  --multiplicity 10 --seed 2284
```

Both runs report

```text
cross_root_three_branch_factorization=EXACT,
corrected_prolate_left_reward=USES_W_ADJOINT,
hermitian_only_prolate_reward=REJECTED,
right_survivor_column=ISOMETRY,
cross_root_causal_column_pairing=EXACT,
complex_polarization=EXACT,
stopped_cross_root_scalar_bound=OPEN,
gate_3u=OPEN,
RH=UNPROVED.
```

## 10. Route judgment

Proof 284 repairs a real object mismatch.  Proof 283's cross detector is not
Hermitian, so Proof 270 could not be imported verbatim.  With the `W*`
correction, the route now has one exact chain from the synchronized moving
flow to the factorized endpoint and then to the inverse-free causal columns.

The next attack is

```text
cross-root causal column pairing (AU.23)
  -> completed source-kernel formula before any norm
  -> compact support clip at |z|<=2B_root
  -> first-missing-displacement causal disintegration
  -> signed stopped estimate uniform in S
  -> Gate 3U.                                             (AU.25)
```

The scalar disintegration, uniform bound, finite-`S` sign, arithmetic
same-object trace identity, negative-owner integration, Burnol's all-zero
identity, and RH remain open.  No Lean owner or route consumer is changed.

## 11. Successor audit

Proof 285 cycles the corrected paired scalar only after the three physical
branches have recombined.  On the convolution commutant it obtains

```text
Q_S(eta,xi)=Lambda_(eta,xi)(Z_S),

Z_S
 =R A*K Gamma^(-1)iota_B*
  -K Gamma^(-1)iota_B*A*C.
```

This moves the compact cross-correlation outside the common renewal, so its
support clips the completed two-boundary kernel before `Gamma^(-1)` is
expanded.  The displayed identity is a factorized trace-functional identity,
not an operator equality `Z_S=B_S-B`; a noncommuting detector rejects that
stronger statement.  See
`docs/proofs/285_support_first_boundary_renewal.md`.
