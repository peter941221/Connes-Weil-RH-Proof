# Proof 401: one-step Gram trace owner

Date: 2026-07-18

Status: exact one-step physical owner for each summand in Proof 400.  Every
normalized local cocycle is the compact-root trace of one consecutive
projection increment.  Its only Gram inverse is a one-prime covariance with
an absolute condition bound, independent of the previous prefix and of `S`.

This removes cumulative Euler conditioning from the scalar Gate.  It does not
sum the local increments uniformly, prove Gate 3U, the finite-`S` sign,
Burnol's identity, or RH.

## 1. One physical step

Let

```text
T_j=I-a_jU_j,             a_j=p_j^(-1/2),
A_j=T_j/(1+a_j),
M_j=(1-a_j)T_j^(-1),
rho_j=(1-a_j)/(1+a_j).                         (LG.1)
```

Let `J_(j-1)` and `J_j` be the canonical orthonormal frames of the
consecutive source ranges.  Proofs 390 and 395 give

```text
A_jJ_j=J_(j-1)G_j,
M_jJ_(j-1)=J_jR_j,
G_jR_j=R_jG_j=rho_jI.                            (LG.2)
```

For `alpha_j=J_j*WJ_j`, define

```text
f_j=G_jalpha_jR_j-rho_jalpha_(j-1).              (LG.3)
```

Proof 398 makes `(LG.3)` trace class for the complete corrected root owner.

## 2. Consecutive projection readback

Put `P_j=J_jJ_j*`.  Since `R_j=rho_jG_j^(-1)`, the local normalized response
is

```text
rho_j^(-1)f_j
 =G_jalpha_jG_j^(-1)-alpha_(j-1).                (LG.4)
```

The same rectangular trace cycle used in Proofs 343 and 398 gives

```text
rho_j^(-1)Tr[f_j]
 =Tr[W(P_j-P_(j-1))].                            (LG.5)
```

Neither bare trace on the right of `(LG.5)` is asserted.  The root-completed
difference is trace class, and `(LG.5)` is its relative trace.

Substitution into Proof 400 yields the literal projection telescope

```text
Q_S(W)
 =sum_j Tr[W(P_j-P_(j-1))]
 =Tr[W(P_n-P_0)].                                (LG.6)
```

The value in `(LG.6)` is not zero: infinite-dimensional relative trace is
formed only after compact-root completion, and the ordered trace anomaly is
preserved.

## 3. Local covariance has an absolute lower bound

The probability-normalized inverse satisfies

```text
rho_j I<=abs(M_j)<=I.                             (LG.7)
```

Indeed, on the unit circle,

```text
(1-a_j)/abs(1-a_j z) in [rho_j,1].               (LG.8)
```

The one-step source covariance is

```text
H_j=J_(j-1)*M_j*M_jJ_(j-1)=R_j*R_j.             (LG.9)
```

Therefore

```text
rho_j^2 I<=H_j<=I,
norm(H_j^(-1))<=rho_j^(-2).                      (LG.10)
```

Since every prime satisfies `p_j>=2`,

```text
rho_j^(-2)
 <=[(1+2^(-1/2))/(1-2^(-1/2))]^2
 =(3+2sqrt(2))^2<34.                             (LG.11)
```

This constant is absolute.  The exponentially conditioned complete
covariance from Proofs 343 and 393 no longer appears in any local summand.

## 4. Remaining theorem

The active Gate scalar is now

```text
sup_(finite S)
 abs sum_(j=1)^n Tr[W_root(P_j-P_(j-1))]

 <=C(1+L+B_root)^d norm(g)_(H^r)^2.              (LG.12)
```

The sum must remain signed.  The absolute one-step inverse bound `(LG.11)`
licenses local algebra; it does not license a sum of local trace norms.

## 5. Reproducible certificate

The companion probe checks `(LG.2)--(LG.6)` for a commuting detector and
translation family.  It also checks every local covariance against
`[rho_j^2,1]` and compares the uniformly bounded one-step inverses with the
rapidly growing complete forward inverse.

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/401_one_step_gram_trace_owner_probe.py
```

## 6. Route judgment

```text
+-----------------------------------------------+---------------------------+
| layer                                         | judgment                  |
+-----------------------------------------------+---------------------------+
| normalized local trace                        | projection increment     |
| one-step covariance inverse                   | absolute bound `<34`     |
| complete-prefix inverse                       | absent from scalar owner |
| signed projection-increment sum `(LG.12)`      | open, active Gate bottom|
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / open|
+-----------------------------------------------+---------------------------+
```
