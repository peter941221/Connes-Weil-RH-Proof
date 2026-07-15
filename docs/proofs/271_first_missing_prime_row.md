# Proof 271: First-missing renewal row and exact prime filtration

Date: 2026-07-15

Status: exact refinement of Proof 270.  Every nonzero renewal term now exposes
one physical missing channel before estimation.  The missing channel splits as
the random Euler innovation plus outer-boundary escape.  The random part has an
exact Doob decomposition into orthogonal prime differences.

The survivor row is a coisometry onto `Ran(K)`.  The Gate 3U scalar is its
signed pairing with one complete three-branch reward row.  Proof 273 rejects a
positive `H1` norm estimate on the reward row.  The remaining theorem must
disintegrate the paired scalar trace after the deterministic renewal
contractions have acted.

Gate 3U, the finite-S sign, the arithmetic trace identity, and RH remain open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Delta=I_rand*I_rand+I_C*I_C                   | exact                        |
| first-missing maps J_k                         | exact                        |
| sum J_k*J_k=Gamma^(-1)                         | exact                        |
| right survivor row                             | coisometry on Ran(K)        |
| row pairing equals Gate 3U renewal             | exact for fixed S           |
| prime Doob difference formula                  | exact                        |
| prime difference orthogonality                 | exact                        |
| positive predictable H1 estimate               | rejected by Proof 273      |
| positive square-energy concentration           | exact in Proof 272           |
| signed scalar local coefficient                | p^(-m/2), exact              |
| complete signed extra half-power               | open, Proof 274 (AK.12)      |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The current owner is

```text
complete L_W
  -> renewal contraction
  -> first missing event
       +-- prime innovation
       +-- outer escape
  -> survivor coisometry
  -> signed extended trace.                              (AH.1)
```

## 2. Actual missing channels

Retain the notation from Proof 270:

```text
K=E A B,
Gamma=K*K,
Delta=B-Gamma,
D=Delta^(1/2).                                         (AH.2)
```

Proof 266 gives the normalized probability dilation

```text
A=J*V,
I-A*A=V*(I-P_0)V.                                     (AH.3)
```

Define

```text
I_rand=(I-P_0)V B,
I_C=C A B.                                             (AH.4)
```

Since `E=I-C`, direct multiplication yields

```text
I_rand*I_rand
 =B-B A*A B,

I_C*I_C
 =B A*C A B,

I_rand*I_rand+I_C*I_C
 =B-B A*E A B
 =Delta.                                               (AH.5)
```

Let

```text
mathcalM=column(I_rand,I_C).                            (AH.6)
```

Then

```text
mathcalM*mathcalM=Delta=D^2.                           (AH.7)
```

Equation `(AH.7)` preserves the source meaning of the renewal defect.  The
canonical square root `D` records its size; `mathcalM` records why the path
failed to survive.

## 3. Expose the first missing event

Define maps with a common input `Ran(B)`:

```text
J_0=B,

J_(k+1)=mathcalM D^k,  k>=0.                           (AH.8)
```

Their Grams are

```text
J_0*J_0=B,

J_(k+1)*J_(k+1)
 =D^k Delta D^k
 =Delta^(k+1).                                         (AH.9)
```

Therefore

```text
sum_(k>=0)J_k*J_k
 =B+sum_(k>=1)Delta^k
 =Gamma^(-1).                                          (AH.10)
```

The equality uses the fixed-`S` strict contraction from Proof 266.  Equation
`(AH.10)` expands the renewal inverse through an actual missing event rather
than a scalar inverse norm.

## 4. Survivor and reward rows

Proof 270 constructs the complete reward

```text
L_W
 =-[W,E]* C A B
   +A R[W,Q]*(I-Q)B
   +A R W Q B,                                        (AH.11)

N_W=L_W*K.                                             (AH.12)
```

Build two rows on the direct sum of the `J_k` output spaces:

```text
mathcalR_K=(K J_k*)_(k>=0),

mathcalR_L=(L_W J_k*)_(k>=0).                          (AH.13)
```

Equation `(AH.10)` gives

```text
mathcalR_K mathcalR_K*
 =K Gamma^(-1)K*.                                     (AH.14)
```

The right side is the orthogonal projection onto `Ran(K)`.  Hence

```text
norm(mathcalR_K)=1.                                    (AH.15)
```

For every `k`, fixed-`S` trace legality permits

```text
Tr((L_WJ_k*)*(KJ_k*))
 =Tr(J_k L_W*K J_k*).
```

Summing and using `(AH.10)` gives

```text
Tr_B(N_W Gamma^(-1))
 =Tr(mathcalR_L*mathcalR_K).                           (AH.16)
```

This row form exposes `mathcalM` in every term after `k=0`.  The `k=0` term is
the single complete physical reward.  Proof 269 gives its local chirp scale,
but that scale has the divergent first-mode ledger `sum_p 1/p`.  The same
source formula must also expose compact-support stopping before summing over
primes.

## 5. Exact prime Doob differences

Order the primes as `p_1,...,p_n`.  Let

```text
V_j(omega_j)=U_(N_(p_j)(omega_j) log(p_j)),

A_j=E[V_j],

V_S=product_j V_j,
A_S=product_j A_j.                                    (AH.17)
```

Let `P_j` average the variables with indices greater than `j`.  Put

```text
V_<j=product_(i<j)V_i,
A_>j=product_(i>j)A_i.                                (AH.18)
```

Conditional expectation gives

```text
P_j V_S=V_<j V_j A_>j,

P_(j-1)V_S=V_<j A_j A_>j.                             (AH.19)
```

Subtracting proves

```text
(P_j-P_(j-1))V_S
 =V_<j(V_j-A_j)A_>j.                                  (AH.20)
```

The factors in `(AH.20)` have distinct roles:

```text
V_<j        common unitary translation history;

V_j-A_j    centered local geometric innovation;

A_>j       contractive future average.                 (AH.21)
```

The martingale projections have orthogonal ranges, so

```text
I_rand*I_rand
 =sum_j I_(rand,j)*I_(rand,j),                         (AH.22)

I_(rand,j)=(P_j-P_(j-1))V_S B.                        (AH.23)
```

The companion certificate verifies `(AH.20)` on truncated geometric laws and
checks

```text
sum_j E[|d_j|^2]
 =E[|V_S-E[V_S]|^2]
 =1-|A_S|^2.                                          (AH.24)
```

The maximum probability-layer error is `3.33e-16`.

## 6. The exact source row after prime refinement

Insert `(AH.22)` into the random output part of `(AH.13)`.  For `k>=0`, the
prime components of the left reward row have the form

```text
L_W D^k I_(rand,j)*.                                   (AH.25)
```

Using `(AH.20)`, their local geometric structure is

```text
L_W D^k B A_>j*
  (V_j*-A_j*)V_<j*.                                   (AH.26)
```

The outer missing components are

```text
L_W D^k I_C*.                                          (AH.27)
```

Equations `(AH.25)--(AH.27)` give the concrete input for the next estimate.
They preserve the complete `L_W`; no outer, second-support, or prolate norm has
been taken.

## 7. Remaining predictable-crossing theorem

Proof 268 cancels the common history `V_<j` before compact support clips the
relative displacement.  Proof 269 bounds the coefficient-weighted local chirp
by `p^(-m/2)`, so its square has scale `p^(-m)`.  Proof 271 identifies the
intervening operator:

```text
D^k B A_>j*.                                           (AH.28)
```

It is a contraction for fixed `S`, but an arbitrary contraction can cancel an
oscillatory phase.  A proof may not delete `(AH.28)` or replace it by its norm
before deriving the real-line kernel.  The required theorem must show that the
complete source combination in

```text
L_W D^k B A_>j*(V_j*-A_j*)V_<j*                       (AH.29)
```

acts as an admissible predictable martingale transform for the compact-root
chirp square function.  It must also show that the residual relative
displacement has a concentration bound at window length `4B_root`.  Proof 272
proves that the ordered future Euler cloud in `A_>j` has enough
anti-concentration for the positive square-energy sum, but an arbitrary contraction
in `(AH.28)` can destroy that conclusion.

Proof 272 proposed the positive bound

```text
norm_H1_root(
  (L_W D^k I_(rand,j)*)_(k,j)
  directSum
  (L_W D^k I_C*)_k)

 <=C(1+B_root)^d norm(g)_(H^r)^2,                     (AH.30)
```

with constants independent of `S`.  The survivor row has norm one by
`(AH.15)`, so an `H^1`--`BMO` pairing would then prove Gate 3U.

Proof 273 withdraws `(AH.30)`.  A completed compact-root crossing can have zero
scalar trace and positive trace norm.  Its one-column `H1` norm is the trace
norm, so compact-support stopping cannot produce a concentration factor in
the positive left-row norm.

The exact surviving object is the signed left/right expansion in Proof 273
equation `(AJ.11)`.  Gate 3U requires the paired scalar disintegration
`(AJ.14)--(AJ.15)`, with `D^k` and the three physical branches retained until
after the scalar trace.

Proof 274 audits the coefficient after this withdrawal.  The signed scalar
owns `p^(-m/2)` locally; the `p^(-m)` envelope in `(AJ.15)` is an open
extra-half-power theorem rather than an output of Proof 272.

## 8. Reproduction

Run in WSL2 from the Windows source snapshot:

```text
python3 -B docs/proofs/271_first_missing_prime_row_probe.py

python3 -B docs/proofs/271_first_missing_prime_row_probe.py \
  --multiplicity 10 --seed 272 --maximum-mode 6
```

The default source certificate reports:

```text
missing channel Gram error        1.04e-15
renewal J Gram error              4.70e-16
right row projection error        5.37e-16
right row idempotence error       4.93e-16
row pairing trace error           2.07e-15
```

The prime filtration certificate reports zero variance-decomposition error and
orthogonal cross-inner-product error below `6.17e-17`.

## 9. Route judgment

Proof 271 finishes the algebraic prime-filtration channelization requested by
Proofs 269 and 270.  Every renewal term now has a named first missing channel,
and every random missing channel has a named centered prime difference.

The active Gate 3U bottom is Proof 274 `(AK.12)`: construct the signed scalar
disintegration of `(AH.29)` paired with its survivor row on the real CC20
carrier and prove the complete extra half-power.  Gate 3U,
the arithmetic same-object finite-S identity, negative-owner integration,
Burnol's identity, and RH remain open.  No Lean owner or route rewire is
authorized.
