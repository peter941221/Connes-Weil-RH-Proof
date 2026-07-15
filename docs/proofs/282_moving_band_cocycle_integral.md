# Proof 282: Moving-band cocycle integral

Date: 2026-07-15

Status: exact transport of Proof 281's fixed-time band Fredholm cocycle through
the actual synchronized finite-`S` flow.  At each flow time, the second
operator is the real logarithmic-generator multiplier from Proof 253, not the
endpoint metric.  The mixed cocycle jet is one half of the extended Dirichlet
pairing.  Twice its time integral is exactly the endpoint band response.

This repairs the final owner mismatch left after Proof 281.  It does not prove
the uniform integrated estimate, compact-path stopping, Gate 3U, or RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| moving E/R/B/C carrier                        | exact Proof 253 owner        |
| generator is M_(h_(S,alpha))                  | exact                        |
| fixed-time band Fredholm cocycle              | exact by Proof 281          |
| D_J=2 S_J normalization                       | exact                        |
| common R-C crossing cancellation              | exact at every flow time    |
| time integral recovers endpoint               | exact                        |
| endpoint metric substitution                  | rejected                     |
| pointwise crossing bound                      | not required                 |
| uniform integrated estimate                   | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The corrected ownership chain is

```text
Proof 253 synchronized flow
  -> at each alpha, Proof 281 band cocycle
  -> mixed jet S_E-S_R
  -> multiply by 2 to recover D_E-D_R
  -> integrate in alpha
  -> exact endpoint response.                              (AS.1)
```

## 2. Two independent parameters

There are two different kinds of parameters and they must not share notation:

```text
alpha in [0,1]: synchronized Euler transport time;

(s,r) near (0,0): detector/generator cocycle deformations. (AS.2)
```

For a fixed finite visible set `S`, Proof 253 supplies

```text
E_alpha=E_(S,alpha),
R_alpha=R_(S,alpha),
B_alpha=E_alpha-R_alpha,
C_alpha=I-E_alpha.                                    (AS.3)
```

The complete right logarithmic derivative is

```text
X_(S,alpha)
 =T_S'(alpha)T_S(alpha)^(-1)

 =-sum_(p in S)sum_(m>=1)
    alpha^(m-1)p^(-m/2)U_(m log p).                   (AS.4)
```

Its real Mellin multiplier is

```text
h_(S,alpha)=Re(X_(S,alpha)),
H_alpha=M_(h_(S,alpha)).                              (AS.5)
```

Equation `(AS.5)` is the second leg in Proof 253's Dirichlet pairing.  It is
not the endpoint metric `H_S=T_S*T_S` used in the endpoint Schur formulas of
Proof 262.

## 3. Moving band cocycle

Let the compact-root detector be

```text
W=C_g* C_g=M_w.                                       (AS.6)
```

At each fixed `alpha`, introduce the independent deformations

```text
U_s=exp(sW),
V_(alpha,r)=exp(r H_alpha).                            (AS.7)
```

Short from `E_alpha=R_alpha direct-sum B_alpha` onto `B_alpha`:

```text
S_(B_alpha)(Y)
 =B_alpha Y B_alpha
  -B_alpha Y R_alpha
   (R_alpha Y R_alpha)^(-1)
   R_alpha Y B_alpha.                                 (AS.8)
```

Proof 281's ordinary band cocycle is

```text
L_(S,alpha)(s,r)
 =S_(B_alpha)(U_sV_(alpha,r))
  S_(B_alpha)(V_(alpha,r))^(-1)
  S_(B_alpha)(U_s)^(-1).                              (AS.9)
```

Proof 261 gives `[W,E_alpha],[W,R_alpha] in S1` for every fixed finite `S`
and `alpha`.  Therefore

```text
L_(S,alpha)(s,r)-B_alpha in S1                       (AS.10)
```

near `(0,0)`, and

```text
ell_(S,alpha)(s,r)=det_(B_alpha)(L_(S,alpha)(s,r))    (AS.11)
```

is genuine.  The trace-ideal constant may depend on `S`; no uniform estimate
is inferred.

## 4. Correct factor two

Proof 281 gives the mixed jet

```text
partial_(s,r)log ell_(S,alpha)|_(0,0)

 =S_(E_alpha)(W,H_alpha)-S_(R_alpha)(W,H_alpha)

 =Tr(B_alpha W C_alpha H_alpha B_alpha)
  -Tr(R_alpha W B_alpha H_alpha R_alpha).             (AS.12)
```

Proof 277's convention for the extended Dirichlet pairing is

```text
D_J(W,H)=Tr([W,J]*[H,J])=2S_J(W,H).                  (AS.13)
```

Proofs 253 and 261 identify the instantaneous endpoint flow with

```text
Tr(W B_(S,alpha)')
 =D_(E_alpha)(W,H_alpha)-D_(R_alpha)(W,H_alpha)

 =2 partial_(s,r)log ell_(S,alpha)|_(0,0).            (AS.14)
```

The factor `2` in `(AS.14)` is structural.  Omitting it confuses the Toeplitz
covariance with the full commutator Dirichlet pairing.

## 5. Exact endpoint integral

Proof 261 makes the moving derivative trace-norm integrable.  Integrating
`(AS.14)` gives

```text
Tr(W(B_(S,1)-B_(S,0)))

 =2 integral_0^1
    partial_(s,r)log ell_(S,alpha)(s,r)|_(0,0)
   dalpha

 =2 integral_0^1 [
    Tr(B_alpha W C_alpha H_alpha B_alpha)
   -Tr(R_alpha W B_alpha H_alpha R_alpha)
   ] dalpha.                                          (AS.15)
```

Equation `(AS.15)` is the exact same-object owner for the analytic Gate 3U
response.  The common `R_alpha-C_alpha` crossing has canceled pointwise, but
the two surviving branches and different flow times must remain inside the
single integral until the final absolute value.

## 6. Why a pointwise bound is not the target

The route needs

```text
|right side of (AS.15)|
 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),                    (AS.16)
```

uniformly in finite `S`.  It does not require

```text
integral_0^1 2[
 |Tr(B_alpha W C_alpha H_alpha B_alpha)|
 +|Tr(R_alpha W B_alpha H_alpha R_alpha)|
] dalpha.                                             (AS.17)
```

The default actual-path certificate shows the cost.  At cutoff `p=2`, the
positive quantity `(AS.17)` is `35.695` times the absolute endpoint response.
Thus a branchwise triangle estimate can lose more than one order of magnitude
before any large-`S` issue appears.

Cancellation may occur in two directions:

```text
between the outer-band and Sonin-band branches at fixed alpha;

between different synchronized flow times alpha.      (AS.18)
```

Neither direction may be removed without a new theorem.

## 7. Actual finite-S certificate

The companion certificate imports Proof 253's actual data:

```text
prime-log translations U_(log p);
complete product T_S(alpha);
transported E_(S,alpha),R_(S,alpha);
complete generator h_(S,alpha);
compact four-mode pre-root detector.
```

At every Gauss--Legendre node it independently computes

```text
direct transported-projection derivative;
D_E-D_R;
2 times the moving-band crossing difference;
finite-difference mixed jet of the band Fredholm cocycle.
```

The default cohort (`size=128`, `step=0.08`) reports

```text
maximum exact algebra error                 1.25e-13,
maximum endpoint integration error          3.10e-8,
maximum cocycle mixed-jet error             8.42e-7.
```

The alternate cohort (`size=160`, `step=0.064`) reports

```text
maximum exact algebra error                 1.89e-13,
maximum endpoint integration error          1.49e-9,
maximum cocycle mixed-jet error             9.56e-7.
```

Representative default values are

```text
+--------+-----------+-----------+-----------+--------------------+
| p <=   | endpoint  | 2 int band| abs paths | cancellation ratio |
+--------+-----------+-----------+-----------+--------------------+
|      2 |  0.04305  |  0.04305  |  1.53680  | 35.695             |
|      5 | -0.45973  | -0.45973  |  1.49794  |  3.258             |
|     11 | -0.20957  | -0.20957  |  1.27078  |  6.064             |
+--------+-----------+-----------+-----------+--------------------+
```

The alternate discretization changes the diagnostic signs and magnitudes, as
expected for a nonconverged periodic section, but every exact identity and the
factor `2` remain stable.  These values are not a continuous estimate.

## 8. Source boundary

Primary and route sources:

```text
CCM24 semilocal Sonin transport:
https://arxiv.org/abs/2310.18423

Proof 253 synchronized Dirichlet owner:
docs/proofs/253_nested_berezin_synchronized_flow.md

Proof 261 fixed-S S1 legality:
docs/proofs/261_fixed_s_trace_class_gate.md

Proof 277 covariance/Dirichlet factor two:
docs/proofs/277_sonin_toeplitz_covariance_reduction.md
```

CCM24 supplies semilocal Sonin transport and explicitly presents further
semilocal positivity as a program; it does not supply `(AS.16)`.  Equations
`(AS.12)--(AS.15)` are obtained by composing the exact local route identities,
not by importing a positivity claim from that paper.

## 9. Reproduction

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/282_moving_band_cocycle_integral_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/282_moving_band_cocycle_integral_probe.py \
  --size 160 --step 0.064 --root-width 0.64 \
  --prime-cutoffs 2,11,29 --quadrature-order 10 \
  --cocycle-nodes 4
```

Both runs verify the algebra, cocycle jet, and endpoint integral.  The
certificate explicitly reports

```text
endpoint_metric_substitution=REJECTED,
pointwise_crossing_bound_required=FALSE,
uniform_integrated_bound=OPEN,
RH=UNPROVED.
```

## 10. Route judgment

Proof 282 repairs the flow-time owner and removes two false targets: a single
endpoint metric in the covariance slot and a pointwise bound on separate band
crossings.  The determinant and trace domains are closed; the hard theorem is
the uniform estimate of the full synchronized integral `(AS.15)`.

The next attack is

```text
moving band integral (AS.15)
  -> write both detector crossings in one real-line coordinate
  -> identify path pairs with equal translated history
  -> cancel paths missing both moving boundaries
  -> apply compact 2B_root displacement stopping
  -> retain only the stopped causal residual
  -> prove (AS.16)
  -> Gate 3U.                                             (AS.19)
```

The uniform integrated bound, stopped causal theorem, finite-S sign,
arithmetic same-object trace identity, negative-owner integration, Burnol's
all-zero identity, and RH remain open.  No Lean owner or route consumer is
changed.

Successor note: Proof 283 extends `(AS.15)` to distinct compact roots, proves
the complex moving-to-endpoint transgression, and recovers it by four-term
polarization without support growth.  It retains Proof 263's prohibition on a
raw point translation trace.
