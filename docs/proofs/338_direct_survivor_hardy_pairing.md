# Proof 338: direct survivor Hardy pairing

Date: 2026-07-17

Status: exact Hardy-space owner for Proof 270's signed renewal scalar.  The
common inverse, finite horizon, and reciprocal survival gap are absent from
the formula.  The result also rejects an incorrect `p^(-1)` reading of Proof
289's complete-prime defect.

This does not prove the source Hardy functional bound, Gate 3U, the finite-S
sign, Burnol's identity, or RH.

## 1. Result

```text
+-----------------------------------------------+-------------------------+
| layer                                         | judgment                |
+-----------------------------------------------+-------------------------+
| direct state D=sqrt(Delta)                    | exact                   |
| survivor observability column                 | isometry                |
| Abel Hardy pairing                            | exact                   |
| renewal horizon / survival gap                | absent                  |
| infinite trace cycle                          | not used                |
| de Branges--Rovnyak domination                | constant one            |
| local coefficient of I-G_p                    | p^(-1/2), not p^(-1)   |
| complete source Hardy functional              | open                    |
| Gate 3U / RH                                  | open / unproved         |
+-----------------------------------------------+-------------------------+
```

## 2. Direct contraction model

On the source band retain Proof 270's objects

```text
Gamma=K* K,
Delta=I-Gamma,
D=Delta^(1/2).                                      (BV.1)
```

Then

```text
K*K=I-D^2.                                          (BV.2)
```

Define

```text
O_D x=(K D^k x)_(k>=0).                              (BV.3)
```

For every `n`,

```text
sum_(k=0)^n D^k K*K D^k+D^(2n+2)=I.                 (BV.4)
```

Since `norm(D)<1` for fixed finite `S`, `(BV.4)` gives

```text
O_D* O_D=I.                                          (BV.5)
```

No lower bound for `Gamma` appears.

## 3. Direct de Branges--Rovnyak kernel

In analytic notation,

```text
(O_D x)(z)=K(I-zD)^(-1)x.                            (BV.6)
```

The range kernel is

```text
K_D(z,w)
 =K(I-zD)^(-1)(I-conj(w)D)^(-1)K*.                 (BV.7)
```

The isometric pair `[D;K]` can be completed to a unitary colligation.  Its
Schur transfer function `S_D` therefore satisfies

```text
K_D(z,w)
 =[I-S_D(z)S_D(w)*]/[1-z conj(w)]
 <=I/[1-z conj(w)].                                  (BV.8)
```

The inequality is positivity of kernels.  Its constant is exactly one and
does not contain `min spectrum(Gamma)`.

Primary source for the colligation/RKHS implication:

```text
J. A. Ball and V. Bolotnikov,
de Branges--Rovnyak spaces: basics and theory,
Theorem 2.1(1),(4), arXiv:1405.2980.
https://arxiv.org/abs/1405.2980
```

## 4. Exact Abel scalar pairing

Let `L_W` be Proof 270's one complete physical reward.  In Proof 293's
orientation it is the observable outer-minus-Sonin generator

```text
L_W=g_W
 =-E W C A iota_B-E A R[W,R]iota_B.                 (BV.9)
```

The equality uses the already proved recombination of Proof 270's outer,
second-support, and prolate terms.  The two summands in `(BV.9)` remain one
signed operator.

Define analytic operator functions

```text
F_L(z)=L_W(I-zD)^(-1),
F_K(z)=K(I-zD)^(-1).                                 (BV.10)
```

For `0<r<1`, expand both resolvents in operator norm.  Orthogonality of the
circle monomials gives

```text
int_T Tr(F_L(r zeta)* F_K(r zeta)) d zeta

 =sum_(j,k>=0)r^(j+k)
   int_T zeta^(k-j)
     Tr((L_WD^j)*(KD^k)) d zeta

 =sum_(k>=0)r^(2k)
     Tr((L_WD^k)*(KD^k)).                            (BV.11)
```

Proof 261 supplies fixed-`S` trace legality after the prescribed compact-root
smoothing.  Taking `r` upward to one in the same extended-trace convention as
Proof 270 yields

```text
lim_(r->1) int_T Tr(F_L(r zeta)*F_K(r zeta))d zeta
 =Tr(C_L* C_K)
 =Tr_B(N_W Gamma^(-1)).                              (BV.12)
```

No infinite trace is cyclically reordered in `(BV.11)--(BV.12)`.

## 5. Exact analytic intertwinement defect

Write `W_E=EWE` and `W_B=iota_B*W iota_B`.  From

```text
L_W=W_EK-KW_B                                       (BV.13)
```

and `R_D(z)=(I-zD)^(-1)`, one gets

```text
F_L(z)
 =W_E F_K(z)-F_K(z)W_B
   +z K R_D(z)[D,W_B]R_D(z).                         (BV.14)
```

Indeed

```text
[R_D(z),W_B]=z R_D(z)[D,W_B]R_D(z).                 (BV.15)
```

The last term is mandatory.  Deleting it would silently commute the band
detector through the renewal state and would erase Proof 264's trace anomaly.
The commutator `[D,W_B]` is the operator divided difference of the already
completed owner

```text
[Delta,W_B]=K*L_W-L_W* K.                            (BV.16)
```

Thus `(BV.14)` is the correct Hardy/Hankel interface for Proofs 306--310's
continuous divided-difference machinery.

## 6. Prime-exponent guard

Proof 289's exact local factorization is

```text
I-G_p
 =a_p R_p(I-U_p)(I-U_p*)R_p*,
a_p=p^(-1/2).                                        (BV.17)
```

Consequently the complete telescope

```text
sum_p G_fut(p)(I-G_p)=I-G_S                         (BV.18)
```

is bounded as one positive contraction, but its local source coefficient has
not changed from `p^(-1/2)` to `p^(-1)`.  A quadratic ledger can arise only
after a further source-specific signed pairing.  It is not a consequence of
`(BV.17)--(BV.18)`.

There is a second guard.  Proof 289 proves

```text
M_rand* M_rand+M_C* M_C=Delta.                       (BV.19)
```

Using `(BV.19)` before compact support merges the global prime defect and the
outer escape back into the original conditioned renewal.  The direct Hardy
model is therefore a uniform transfer mechanism, not permission to forget
the two physical missing channels.

## 7. Exact remaining theorem

The missing source estimate can now be stated without a horizon or a spectral
gap:

```text
sup_(finite S,0<r<1)
 abs int_T Tr(F_L(r zeta)*F_K(r zeta))d zeta

 <=C(1+B_root)^d
   norm(eta)_(H^q) norm(xi)_(H^q),                  (BV.20)
```

where `L_W` is kept in the complete form `(BV.9)`, `R` is kept as

```text
R=E E_hat E-K_prol,
```

and compact correlation support is applied before the absolute value.

The de Branges--Rovnyak bound `(BV.8)` handles the survivor column.  It does
not bound the trace multiplicity of the left functional; Proof 270's
direct-sum guard still rules out that generic inference.  The next producer
must prove `(BV.20)` from the real-line source kernel.

## 8. Verification evidence

The updated Proof 337 probe checks both contraction models.  Its direct model
reports

```text
survivor observability isometry error  8.94e-16,
Hardy kernel bound violation           0.
```

Run without a Lean build:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/337_debranges_rovnyak_observability_probe.py
```

This is a finite algebra certificate only.  It does not test `(BV.20)`.

## 9. Route judgment

```text
direct renewal Hardy owner:                 closed;
survival-gap and horizon dependence:        eliminated;
automatic p^(-1) ledger:                    rejected;
source outer-minus-Sonin Hardy functional:  open;
Gate 3U:                                    open;
finite-S sign / Burnol identity / RH:        open.       (BV.21)
```
