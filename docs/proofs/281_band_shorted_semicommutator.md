# Proof 281: Band-shorted semicommutator

Date: 2026-07-15

Status: exact fixed-`S` ordinary Fredholm determinant on the common source band
`B=E-R`.  Proof 280's relative `E/R` Toeplitz cocycle descends, after Schur
shorting over `R`, to one detector-first semicommutator on `B`.  Its defect is
trace class because the detector becomes block diagonal modulo `S1`.  Its
mixed derivative is the signed difference of two completed physical band
crossings.

This closes the ordinary band-determinant domain for the two-parameter
semicommutator combination.  It does not close the uniform relative band
estimate, prime stopping, Gate 3U, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| nested Schur shorting onto B                  | exact                        |
| detector block diagonal modulo S1             | exact                        |
| band semicommutator differs from I by S1       | exact                        |
| band determinant equals relative E/R cocycle  | exact determinant-line owner |
| mixed derivative is two band crossings         | exact                        |
| block-diagonal detector gives identity         | exact guard                  |
| zero-prolate two-boundary survivor             | retained                     |
| uniform relative band estimate                 | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The owner is now on one Hilbert space:

```text
det(K_E)/det(K_R)
  -> one determinant-line Schur coordinate
  -> one ordinary Fredholm determinant on Ran(B)
  -> two signed physical band crossings.                    (AR.1)
```

## 2. Nested shorting

Use the orthogonal decomposition

```text
I=C direct-sum R direct-sum B,
E=R direct-sum B,
B=E-R,
C=I-E.                                                   (AR.2)
```

For an operator `X` whose `R` compression is invertible, define its shorting
from `E` to `B` by

```text
S_B(X)
 =B X B-B X R(R X R)^(-1)R X B.                       (AR.3)
```

For positive invertible `X`, `S_B(X)` is positive and invertible on `Ran(B)`.
In finite dimension, block determinant factorization gives

```text
det_E(E X E)/det_R(R X R)=det_B(S_B(X)).              (AR.4)
```

Proof 267 interprets `(AR.4)` as a determinant-line Schur coordinate when the
individual infinite determinants do not exist.

## 3. The band semicommutator

Retain Proof 280's detector-first multipliers

```text
U_s=exp(sW),
V_t=exp(tH).                                           (AR.5)
```

Define on `Ran(B)`

```text
L_B(s,t)
 =S_B(U_sV_t) S_B(V_t)^(-1) S_B(U_s)^(-1).            (AR.6)
```

Finite block determinant algebra applied to `(AR.4)` gives

```text
det_B(L_B(s,t))
 =det(K_E(s,t))/det(K_R(s,t)),                         (AR.7)
```

where `K_E,K_R` are Proof 280's genuine Toeplitz semicommutator cocycles.
Equation `(AR.7)` is not a ratio of separately estimated determinants; it is
one determinant-line coordinate on the quotient `E/R=B`.

## 4. Why the band defect is trace class

Let `pi` be the quotient map into the Banach algebra

```text
B(H)/S1.                                               (AR.8)
```

Proof 261 and Duhamel give

```text
[U_s,E] in S1,
[U_s,R] in S1.                                        (AR.9)
```

Since `B=E-R`, `(AR.9)` makes `pi(U_s)` commute with `pi(C)`, `pi(R)`, and
`pi(B)`.  Thus the detector is block diagonal in the quotient.  Write its
`R/B` blocks there as

```text
pi(E U_s E)=diag(u_R,u_B).                            (AR.10)
```

For an arbitrary invertible block operator

```text
pi(E V_t E)=[[a,b],[c,d]],                            (AR.11)
```

direct Schur algebra gives

```text
S_B(U_sV_t)
 =u_B[d-c a^(-1)b]
 =S_B(U_s)S_B(V_t)                                    (AR.12)
```

inside the quotient.  The possible outer path through `C` also vanishes
modulo `S1` because

```text
E U_s C=-E[U_s,E]C in S1.                             (AR.13)
```

Equations `(AR.12)--(AR.13)` prove

```text
S_B(U_sV_t)-S_B(U_s)S_B(V_t) in S1.                  (AR.14)
```

Multiplication by the two bounded shorted inverses yields

```text
L_B(s,t)-B in S1                                      (AR.15)
```

trace-norm continuously near the origin.  Therefore

```text
ell_B(s,t)=det_B(L_B(s,t))                            (AR.16)
```

is an ordinary Fredholm determinant.  This is stronger than Proof 267's raw
one-parameter shorted coordinate: its multiplicative second difference has
removed the non-`S1` common part.

The proof uses no ideal premise on `[V_t,E]` or `[V_t,R]`.

## 5. Determinant-line equality

In finite dimension, `(AR.7)` follows immediately by applying `(AR.4)` to
`U_sV_t`, `U_s`, and `V_t`.  In the fixed-`S` source, Proof 280 makes the left
side of `(AR.7)` a genuine relative determinant line, while `(AR.15)` makes the
right side an ordinary Fredholm determinant.

Block Gaussian elimination identifies the two coordinates.  The upper and
lower triangular graph changes have identity diagonal; in the complete
multiplicative second difference their determinant contributions cancel.
Hence

```text
ell_B(s,t)=c_(E/R)(s,t).                              (AR.17)
```

No individual `det_E(E X E)`, `det_R(R X R)`, or `det_B(S_B(X))` is asserted
for `X in {U_s,V_t,U_sV_t}`.  Only the two cocycles in `(AR.17)` are ordinary
Fredholm determinants.

## 6. Mixed derivative as physical band crossings

Proof 280 gives

```text
partial_(s,t)log ell_B|_(0,0)=S_E(W,H)-S_R(W,H).      (AR.18)
```

Expand `E=R+B` and `I-R=C+B`.  The common `R-C` crossing cancels before any
norm:

```text
S_E
 =Tr(B W C H B)+Tr(R W C H R),

S_R
 =Tr(R W C H R)+Tr(R W B H R).                       (AR.19)
```

Therefore

```text
partial_(s,t)log ell_B|_(0,0)
 =Tr(B W C H B)-Tr(R W B H R).                       (AR.20)
```

This is the new lowest scalar owner.  Both terms are completed crossings
generated by the compact-root detector:

```text
B W C=-B[W,E]C,
R W B=-R[W,R]B.                                      (AR.21)
```

Proof 261 makes them trace class against the bounded return legs from `H`.
Equation `(AR.20)` must remain one signed difference.  Estimating its two
terms separately recreates the rejected outer/Sonin triangle inequality.

## 7. Ownership guards

### 7.1 Block-diagonal detector

If the detector commutes exactly with `E` and `R`, it is block diagonal on
`C direct-sum R direct-sum B`.  Then `(AR.12)` holds before quotienting and

```text
L_B(s,t)=B                                             (AR.22)
```

for every admissible second multiplier.  The certificate uses

```text
U=1.13 C+0.91 R+1.27 B.                              (AR.23)
```

The outer, Sonin, and band cocycles are the identity to `2.00e-15`.  Thus the
entire response is sourced by detector boundary crossings; there is no hidden
bulk determinant.

### 7.2 Zero-prolate survivor

Proof 279's deterministic model still has

```text
F_0=K_prol=0.                                         (AR.24)
```

Nevertheless,

```text
Tr(B W C H B)-Tr(R W B H R)=-1/4,                    (AR.25)
```

and the nonzero band cocycle log has magnitude `0.004395863`.  The centered
finite-difference derivative reads `(AR.25)` with error `2.05e-8`.  The band
owner therefore preserves the genuine even/two-boundary channel.

## 8. Analytic consequence

Proof 281 closes two domain questions:

```text
fixed-S relative Toeplitz cocycle domain: closed by Proof 280;
fixed-S ordinary band cocycle domain:     closed by Proof 281.    (AR.26)
```

For the synchronized route, `(AR.20)` is applied at each flow time
`alpha in [0,1]` with

```text
E=E_(S,alpha),
R=R_(S,alpha),
B=B_(S,alpha),
C=I-E,
H=M_(h_(S,alpha)).                                    (AR.27)
```

Here `h_(S,alpha)=Re(T_S'(alpha)T_S(alpha)^(-1))` is the complete
time-dependent Euler generator multiplier from Proof 253.  It is not the
endpoint metric `H_S=T_S*T_S` from Proof 262.

Proof 277's normalization is

```text
D_J(W,H)=2S_J(W,H).                                   (AR.28)
```

Therefore Proofs 253 and 261 give the exact endpoint identity

```text
Tr(W(B_(S,1)-B_(S,0)))

 =2 integral_0^1 [
    Tr(B_(S,alpha) W C_(S,alpha)
       M_(h_(S,alpha)) B_(S,alpha))

   -Tr(R_(S,alpha) W B_(S,alpha)
       M_(h_(S,alpha)) R_(S,alpha))
   ] dalpha.                                          (AR.29)
```

The uniform theorem is the integrated same-object estimate

```text
|right side of (AR.29)|
 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),                    (AR.30)
```

with constants independent of the visible finite set.  A pointwise-in-`alpha`
bound for either crossing is neither proved nor required; cancellation may
also occur along the synchronized time integral.

The next proof should not return to boundary Gram determinants.  It should:

```text
1. insert the real-line kernels for the two detector crossings in (AR.21);

2. identify the common translated path segment in their
   `M_(h_(S,alpha))` return legs;

3. cancel paths which miss both physical boundaries;

4. apply the 2B_root displacement clip;

5. expose the causal prime law only on the stopped residual;

6. take one absolute value after the scalar difference.          (AR.32)
```

The remaining forbidden moves are:

```text
separate trace norms of the two terms in (AR.20);
an inverse condition-number bound for a shorted factor;
absolute prime-word expansion of `h_(S,alpha)`;
periodic replacement of either physical boundary;
use of fixed-S S1 legality as a uniform estimate.                 (AR.33)
```

## 9. Reproduction

Run in WSL2:

```text
python3 -B docs/proofs/281_band_shorted_semicommutator_probe.py

python3 -B docs/proofs/281_band_shorted_semicommutator_probe.py \
  --size 34 --support-rank 8 --seed 2281
```

The default cohort reports

```text
determinant-coordinate error             7.69e-15,
physical band-crossing error             1.18e-16,
mixed-derivative error                   1.96e-8,
block-diagonal guard error               1.35e-15.
```

The alternate cohort reports determinant-coordinate error `1.98e-15`,
boundary-coordinate error `1.67e-14`, physical crossing error `3.38e-16`, and
mixed-derivative error `2.65e-8`.  All shorted positive matrices retain
strictly positive minimum eigenvalues in both cohorts.

## 10. Route judgment

Proof 281 turns the relative determinant-line owner into one ordinary band
Fredholm determinant and removes the common `R-C` crossing before estimation.
The remaining difficulty is no longer a determinant domain or an inverse
Gram.  Proof 282 identifies the route owner as the time integral of this signed
difference along the moving synchronized carrier, with second leg
`M_(h_(S,alpha))` and the exact factor `2`.

The active bottom is

```text
time-integrated moving-band crossing difference (AR.29)
  -> real-line common-path cancellation
  -> compact displacement stopping
  -> causal residual with complete prime history
  -> uniform polynomial-support scalar bound
  -> Gate 3U.                                             (AR.34)
```

The uniform bound, stopped prime theorem, finite-S sign, arithmetic same-object
trace identity, negative-owner integration, Burnol's all-zero identity, and RH
remain open.  No Lean owner or route consumer is changed.

Successor note: Proof 282 applies the band cocycle at every synchronized flow
time, restores `D_J=2S_J`, and proves that twice the time integral of the
moving band jet is the exact endpoint response.  The endpoint metric
substitution and a required pointwise crossing bound are rejected.
