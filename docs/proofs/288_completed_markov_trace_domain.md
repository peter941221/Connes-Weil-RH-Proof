# Proof 288: Completed Markov displacement trace domain

Date: 2026-07-15

Status: closes the fixed-`S` trace domain left open by Proof 287.  The complete
renewal reward is a signed sum of two detector-commutator trace-class
operators.  Its displacement coefficient is therefore an ordinary bounded
continuous function.  The complete relative-mode sum is one trace-class
operator defect involving the local relative Markov operator.

The trace norm depends on `S` and on the renewal owner.  This proof supplies
legality only; it does not prove the uniform Markov-defect estimate, Gate 3U,
the finite-`S` sign, the arithmetic same-object identity, Burnol's identity,
or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| complete ambient renewal reward               | two detector commutators    |
| fixed-S reward ideal                          | S1                           |
| displacement coefficient kappa(z)             | ordinary trace, continuous  |
| relative geometric Markov operator            | A_p A_p*                    |
| full local mode sum                            | one operator defect         |
| exact local defect norm                        | 4a_p/(1+a_p)^2              |
| fixed scalar mode                             | killed                       |
| fixed-S trace norm                            | finite, S-dependent         |
| trace norm as Gate 3U estimate                | forbidden                    |
| complete Sonin Markov-defect bound            | open                         |
| Gate 3U and RH                                 | open / unproved              |
+------------------------------------------------+------------------------------+
```

The new legal chain is

```text
root commutators [W,E],[W,R] in S1
  -> complete reward X_(S,k)(W) in S1
  -> kappa_(S,k)(z)=Tr(U_z X_(S,k)(W)) is legal
  -> local Markov defect is one S1 trace
  -> signed uniform estimate still required.             (AY.1)
```

## 2. Ambient form of the reward

Let `iota_B:H_B->H` be the band inclusion and retain

```text
B=iota_B iota_B*,
K=E A iota_B,
Delta=I_(H_B)-K*K.                                   (AY.2)
```

Proof 286 defines, for `k>=1`,

```text
H_(S,k)(W)
 =iota_B* W R A*K Delta^(k-1)
  -iota_B*A*C W K Delta^(k-1).                       (AY.3)
```

Put the reward back on the ambient carrier:

```text
X_(S,k)(W)
 :=iota_B H_(S,k)(W)iota_B*.                         (AY.4)
```

Direct substitution gives

```text
X_(S,k)(W)
 =B W R A*K Delta^(k-1)iota_B*
  -B A*C W K Delta^(k-1)iota_B*.                     (AY.5)
```

This is the object whose future translates occur in Proof 287.  It is not the
raw endpoint projection difference `B_S-B`.

## 3. Two detector commutators

Use the nested projection identities

```text
BR=0,
CK=0,
RK=R E A iota_B,
EK=K.                                                (AY.6)
```

The two detector factors in `(AY.5)` become

```text
B W R=B[W,R]R,

C W K=C[W,E]K.                                       (AY.7)
```

Therefore

```text
X_(S,k)(W)
 =B[W,R]R A*K Delta^(k-1)iota_B*
  -B A*C[W,E]K Delta^(k-1)iota_B*.                   (AY.8)
```

Equation `(AY.8)` is a signed equality, not a branchwise estimate.

For compact roots `eta,xi`,

```text
W=C_xi* C_eta.                                       (AY.9)
```

Proof 261 gives the diagonal root-commutator statements, and Proof 283's
polarization gives the cross-root form:

```text
[W,E] in S1,
[W,R] in S1.                                        (AY.10)
```

Every other factor in `(AY.8)` is bounded for fixed finite `S`.  Since `S1`
is a two-sided operator ideal,

```text
X_(S,k)(W) in S1.                                    (AY.11)
```

No prime-power absolute sum or Hilbert--Schmidt factor norm is needed for this
particular fixed-`S` reward.

## 4. The displacement coefficient is legal

Let `U_z` be the strongly continuous logarithmic translation group.  Define

```text
kappa_(S,k)(z;eta,xi)
 :=Tr(U_z X_(S,k)(W)).                               (AY.12)
```

Equation `(AY.11)` makes `(AY.12)` an ordinary trace.  It obeys

```text
|kappa_(S,k)(z;eta,xi)|
 <=norm(X_(S,k)(W))_1.                              (AY.13)
```

Moreover,

```text
z ->U_z X_(S,k)(W)
```

is trace-norm continuous.  To see this, approximate `X_(S,k)(W)` in `S1` by
finite-rank operators.  Strong continuity of `U_z`, uniform boundedness of the
unitaries, and the finite-rank approximation prove

```text
norm((U_z-U_z0)X_(S,k)(W))_1 ->0.                   (AY.14)
```

Thus

```text
kappa_(S,k)(.;eta,xi) in C_b(R).                    (AY.15)
```

This closes precisely the coefficient domain left open in Proof 287.  It does
not legalize the unrelated raw point response
`Tr(U_z(B_S-B))` prohibited by Proof 263.

## 5. The relative Markov operator

For one prime put

```text
a=a_p=p^(-1/2),
L=log(p),

nu_p(m)=(1-a)a^m,
A_p=sum_(m>=0)nu_p(m)U_(mL)
    =(1-a)(I-aU_L)^(-1).                             (AY.16)
```

The series converges in operator norm.  Let

```text
d_p(r)=(1-a)/(1+a)a^|r|,  r in Z.                   (AY.17)
```

The two independent geometric legs give

```text
G_p
 :=sum_(r in Z)d_p(r)U_(rL)
 =A_p A_p*.                                         (AY.18)
```

The series in `(AY.18)` also converges in operator norm.  Hence `G_p` is a
positive contraction and fixes the scalar translation mode.

Proof 287's Markov operator on displacement coefficients is exactly the
operator action

```text
(P_p kappa_(S,k))(z)
 =Tr(U_z G_p X_(S,k)(W)).                            (AY.19)
```

Therefore the complete local Markov defect is the single ordinary trace

```text
kappa_(S,k)(z)-(P_p kappa_(S,k))(z)

 =Tr(U_z(I-G_p)X_(S,k)(W)).                          (AY.20)
```

Equation `(AY.20)` is the legal continuous replacement for the formal
relative-mode series.

## 6. Agreement with the completed second difference

For `T_r=U_(rL)-I`, trace cyclicity on the `S1` reward gives

```text
1/2 sum_(r in Z)d_p(r)
 Tr(T_r U_z X_(S,k)(W)T_r*)

 =Tr(U_z(I-G_p)X_(S,k)(W)).                          (AY.21)
```

Absolute convergence is automatic for fixed `S` because

```text
sum_r d_p(r)=1,
norm(T_r U_z X T_r*)_1<=4norm(X)_1.                  (AY.22)
```

Thus the following three coordinates are now simultaneously legal and equal:

```text
coefficient Markov defect;
completed relative-mode second-difference sum;
single operator defect I-A_pA_p*.                    (AY.23)
```

## 7. Exact size of the local defect

On the spectral circle, `A_p` has multiplier

```text
b_p(theta)=(1-a)/(1-a exp(i theta)).                 (AY.24)
```

Therefore

```text
I-G_p=I-A_pA_p*
```

has multiplier `1-|b_p(theta)|^2`, and

```text
norm(I-G_p)
 =1-(1-a)^2/(1+a)^2
 =4a/(1+a)^2.                                        (AY.25)
```

This is `O(p^(-1/2))`, exactly the one route-owned half-power.  It is not the
missing second half-power.

The fixed-mode value is zero because `b_p(0)=1`.  That cancellation belongs to
the whole operator defect `(AY.20)`, not to its individual translation modes.

## 8. Why the trace norm cannot close Gate 3U

The immediate estimate

```text
|Tr(U_z(I-G_p)X_(S,k)(W))|
 <=norm(I-G_p) norm(X_(S,k)(W))_1                   (AY.26)
```

is valid for fixed `S` and unsuitable for Gate 3U.  Proof 261 already warns
that its trace-norm constants depend on `S`; Proofs 260 and 273 show that
positive nuclear mass cannot express compact-support cancellation.

The finite certificate makes the dimensional failure explicit.  Eight
orthogonal copies keep every local operator norm fixed while

```text
norm(I_8 tensor X)_1=8norm(X)_1.                     (AY.27)
```

The default/alternate branchwise trace-norm costs are `1.489` and `1.276`
times the complete reward norm.  These values are finite diagnostics, not
continuous lower bounds.  They reinforce that `(AY.8)` must remain signed.

## 9. Finite certificate

The default cohort reports

```text
reward/commutator factorization error     7.09e-17,
maximum Markov algebra error              7.30e-16,
point defect error                        2.27e-18,
completed second-difference error         2.64e-18,
exact geometric defect norm error         0.
```

The alternate cohort reports

```text
reward/commutator factorization error     2.62e-17,
maximum Markov algebra error              7.28e-16,
point defect error                        1.23e-18,
completed second-difference error         1.78e-18,
exact geometric defect norm error         0.             (AY.28)
```

For `p=3`, the exact local defect norm is `0.928203...`; this is consistent
with `(AY.25)` and illustrates why small primes must remain in the complete
signed owner.

The finite certificate checks algebra.  The continuous `S1` theorem is
`(AY.7)--(AY.11)` using Proof 261's source-backed commutator ideal membership.

## 10. Evidence and reproduction

Source evidence:

```text
Proof 261 fixed-S trace-class gate and CC20 root commutators:
docs/proofs/261_fixed_s_trace_class_gate.md

Connes--Consani, root/half-line commutator:
https://arxiv.org/abs/2006.13771
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/288_completed_markov_trace_domain_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/288_completed_markov_trace_domain_probe.py \
  --multiplicity 12 --seed 2288 --renewal-power 2 \
  --maximum-mode 12 --spectral-size 48
```

Both runs report

```text
completed_reward_commutator_factorization=EXACT,
fixed_s_displacement_coefficient=TRACE_CLASS_CONTINUOUS,
relative_markov_operator=A_p_A_pSTAR,
completed_mode_sum=ONE_OPERATOR_DEFECT,
local_defect_norm=4a_p_over_1_plus_a_p_squared,
trace_norm_used_for_uniform_gate=FALSE,
complete_sonin_markov_defect_bound=OPEN,
gate_3u=OPEN,
RH=UNPROVED.
```

## 11. Route judgment

Proof 288 closes the fixed-`S` continuous coefficient domain and nothing
stronger.  The complete local Markov defect now has one legal ordinary-trace
owner:

```text
Tr(U_z(I-A_pA_p*)X_(S,k)(W)).                        (AY.29)
```

The next attack is

```text
legal owner (AY.29)
  -> retain the signed commutator difference (AY.8)
  -> source kernel readback of I-A_pA_p*
  -> outer three-window concentration
  -> complete Sonin Toeplitz-covariance tail
  -> second half-power without norm(X)_1
  -> Gate 3U.                                             (AY.30)
```

The uniform Markov-defect bound, base/outer remainder, Gate 3U, finite-`S`
sign, arithmetic same-object trace identity, negative-owner integration,
Burnol's all-zero identity, and RH remain open.  No Lean owner or route
consumer is changed.

Successor correction: Proof 289 uses the fact that `X_(S,k)(W)` is common to
every Doob prime channel.  The local operators from `(AY.20)` retain their
predictable-future products and telescope exactly:

```text
sum_p G_fut(p)(I-G_p)=I-G_S.
```

Consequently the route need not obtain another half-power from each local
defect.  It must estimate one complete global defect together with the base,
outer-missing, and renewal terms; see Proof 289 `(AZ.20)--(AZ.26)`.
