# Proof 419: Cumulative-delay terminal anomaly guard

Date: 2026-07-19

Status: exact carrier and trace-ownership audit for the scalar all-pass
dilation proposed after Proof 349.  Appending a fixed model space to the
cumulative Euler-delay model produces source and target terminal bands which
are unitarily conjugate by a scalar boundary multiplier commuting with every
detector multiplier.  Their ordinary finite-dimensional detector trace is
therefore identical.  The actual fixed-carrier Euler response is already
nonzero in dimension one.

Consequently a scalar cumulative-delay dilation can preserve Gate 3U only
through an explicitly proved infinite-dimensional relative trace anomaly and
the weighted Burnol coupling.  Range equality and finite trace cyclicity are
insufficient.  This does not prove that such an anomaly identity exists, bound
Gate 3U, prove the finite-`S` sign, Burnol's identity, or RH.

## 1. Result

```text
+------------------------------------------------------+---------------------------+
| layer                                                | judgment                  |
+------------------------------------------------------+---------------------------+
| Proof 320 `sameObjectResidual`                       | bookkeeping definition    |
| active detector-smallness owner                      | full band response        |
| appended cumulative-delay source band               | `Alpha K_Phi`             |
| transported terminal band                           | `Beta K_Phi`              |
| relation between those two bands                     | scalar unitary conjugacy  |
| finite / separately trace-class detector response    | exactly zero              |
| actual fixed `K_z` response for one Euler factor     | exactly `2ca`             |
| naive finite scalar dilation as Gate bridge          | rejected                  |
| possible infinite relative-trace anomaly             | must remain explicit      |
| Gate 3U / finite-S sign / Burnol / RH                 | open / open / open / open |
+------------------------------------------------------+---------------------------+
```

The central distinction is

```text
same range algebra
  + commuting detector
  + finite trace cyclicity
  -> zero terminal response;

root-relative infinite trace
  -> cyclicity is not automatic
  -> any surviving value is the trace anomaly itself.       (TA.1)
```

## 2. First fix the residual ownership

Proof 320 defines on the actual common-log carrier

```text
projectionResponse = W(B_S-B_0),
arithmeticOperator = selected finite-prime crossing sum,
sameObjectResidual = projectionResponse-arithmeticOperator.  (TA.2)
```

The equality

```text
projectionResponse
 =arithmeticOperator+sameObjectResidual                (TA.3)
```

is therefore definitional bookkeeping.  Repository search finds
`sameObjectResidual` only inside
`CCM24FiniteSProjectionTrace.lean`; no later Gate module replaces the full
band response by that residual.

Proof 265's exact Gate scalar is

```text
Q_S(eta,xi)=Tr_B(K* W K Gamma^(-1)-W_B),              (TA.4)
```

the detector response of the transported band.  Its specialization `R=0`
is the actual finite-prime boundary series

```text
-log(p) sum_(m>=1)p^(-m/2)
  [F(m log(p))+F(-m log(p))].                          (TA.5)
```

Thus Proof 418's half-power term is not removed merely by naming the
Proof 320 residual.  Gate smallness requires cancellation inside the complete
band response.

## 3. General appended-model range identity

Work in scalar Hardy space.  Let `Alpha` and `Phi` be inner functions.  Let
`q,q^(-1)` belong to `H^infinity`, and suppose the boundary function

```text
qSharp=Alpha conjugate(q)                              (TA.6)
```

has an analytic inner quotient

```text
Beta=qSharp/q.                                         (TA.7)
```

The Euler owner from Proof 349 has exactly this form:

```text
Alpha=Theta_S=product_p theta_(log p),
q=q_S=product_p(1-p^(-1/2)theta_(log p)),
Beta=beta_S=product_p
  [theta_(log p)-p^(-1/2)]/[1-p^(-1/2)theta_(log p)]. (TA.8)
```

Proof 349 gives `q^(-1)K_Alpha=K_Beta`.  The same proof works after appending
an arbitrary fixed inner factor:

```text
q^(-1) K_(Alpha Phi)=K_(Beta Phi).                    (TA.9)
```

For the forward inclusion, take `f in K_(Alpha Phi)`, put `g=f/q`, and test
against `Beta Phi h`.  Boundary identity `(TA.6)` gives

```text
<g,Beta Phi h>
 =<f,Alpha Phi(h/q)>
 =0.                                                   (TA.10)
```

The converse follows by multiplying by `q` and testing the
`K_(Beta Phi)` orthogonality with `q h`.  No determinant or asymptotic theorem
is used.

## 4. The terminal bands are scalar-unitarily conjugate

The model-space product identity gives the orthogonal decompositions

```text
K_(Alpha Phi)=K_Alpha direct-sum Alpha K_Phi,
K_(Beta Phi) =K_Beta  direct-sum Beta  K_Phi.         (TA.11)
```

Transport both nested spaces by multiplication with `q^(-1)`.  Equations
`(TA.9)--(TA.11)` show that their nested-complement bands are exactly

```text
B_0=Alpha K_Phi,
B_1=Beta K_Phi.                                       (TA.12)
```

On boundary `L2`, multiplication by

```text
u=Beta conjugate(Alpha)                               (TA.13)
```

is unitary and maps `B_0` onto `B_1`.  Hence

```text
P_(B_1)=M_u P_(B_0) M_u*.                             (TA.14)
```

Every scalar detector multiplier `W=M_w` commutes with `M_u`.  If the two
compressed detector operators are separately trace class, in particular in
finite dimension, ordinary cyclicity gives

```text
Tr(W P_(B_1))=Tr(W P_(B_0)),
Tr(W(P_(B_1)-P_(B_0)))=0.                             (TA.15)
```

Equation `(TA.15)` is not licensed in the actual infinite Burnol problem.
There only the completed root-sandwiched difference is known to be trace
class; neither summand has an ordinary trace.  A unitary conjugation difference
can then carry a nonzero index or Toeplitz trace anomaly.

The valid infinite target would have to define and compute

```text
mathfrakA_(u,B_0)(W)
 :=Tr_root[W(M_u P_(B_0)M_u*-P_(B_0))],              (TA.16)
```

without cycling either divergent term.  Merely observing `[W,M_u]=0` does not
prove `(TA.16)=0`.

## 5. Exact one-dimensional failure of the finite bridge

Take disk Hardy space and

```text
Alpha(z)=z,
Phi(z)=z,
q(z)=1-a z,
Beta(z)=(z-a)/(1-a z),
W=I+c(M_z+M_z*),       0<a,c<1.                       (TA.17)
```

For a positive detector take, as in the certificate, `0<c<1/2`.

The appended source and target terminal bands are

```text
B_0=z K_z=span{z},
B_1=Beta K_z=span{Beta}.                              (TA.18)
```

Since both `z` and `Beta` are inner,

```text
<z,Wz>=1=<Beta,W Beta>,                               (TA.19)
```

so the terminal response is zero.

Now remove the appended delay block and transport the actual fixed carrier
`K_z=span{1}`.  The normalized endpoint vector is

```text
v_a(z)=sqrt(1-a^2)/(1-a z).                           (TA.20)
```

Its Taylor coefficients are `sqrt(1-a^2)a^n`, so

```text
<v_a,M_z v_a>=a,
<v_a,W v_a>-<1,W 1>=2ca.                             (TA.21)
```

Thus the finite appended terminal compression changes the genuine nonzero
fixed-carrier response into zero.  This is the same half-power mechanism as
Proofs 402 and 418, now placed directly against the proposed scalar dilation.

## 6. Where an infinite bridge could still live

The result does not reject every dilation.  It fixes what a successful one
must retain:

```text
fixed Burnol extremal weight `h_0=|g_0|^2`;
outer-minus-Sonin/prolate coupling;
the nonorthogonal Schur complement;
the relative trace anomaly `(TA.16)`;
root completion before cyclicity.                    (TA.22)
```

Proof 415's weighted boundary form already has the correct noncyclic owner:

```text
Lambda_S(F)
 =Tr[
   G_S^(-1) mathcalB_(h_S)(w_F)
   -G_0^(-1) mathcalB_(h_0)(w_F)].                    (TA.23)
```

Proof 419 shows why replacing `(TA.23)` by the ordinary terminal trace of
`K_(Beta_S Phi)-K_(Theta_S Phi)` deletes the quantity being estimated.  A
future all-pass bridge must prove that `(TA.23)` equals a relative anomaly or
a coupled off-diagonal block of the dilation; it may not use `(TA.15)`.

## 7. Anomaly cocycle

For commuting scalar unitaries `u,v`, the formal relative anomaly obeys the
exact telescoping identity whenever all displayed completed differences are
trace class:

```text
mathfrakA_(uv,P)(W)
 =mathfrakA_(u,vPv*)(W)+mathfrakA_(v,P)(W).            (TA.24)
```

Indeed, insert and subtract `vPv*` before taking the one legal trace.  This is
the determinant-line analogue of Proof 400's local trace cocycle.  It does not
make the local terms absolutely summable.

For the Euler product,

```text
u_S=Beta_S conjugate(Theta_S)=conjugate(q_S)/q_S.     (TA.25)
```

Thus an anomaly bridge, if constructed, would automatically carry the same
ordered all-pass factors as Proof 349.  The missing theorem is the
identification with `(TA.23)` and its canonical-energy bound, not the algebraic
cocycle `(TA.24)`.

## 8. Source boundary

The model-space identities used above are the elementary identities already
audited in Proof 349.  Primary references for the underlying Crofoot and
model-space transforms are:

```text
Crofoot, Multipliers between invariant subspaces of the backward shift,
https://msp.org/pjm/1994/166-2/p03.xhtml

Lopatto--Rochberg, Schatten-class Truncated Toeplitz Operators,
https://arxiv.org/abs/1410.1906
```

Neither source states the weighted Burnol anomaly identity `(TA.23)=(TA.16)`.
Proof 264's unilateral-shift guard is direct repository evidence that such a
relative trace must not be erased by finite cyclicity.

## 9. Reproducible certificate

The companion script uses truncated Hardy coefficients for `(TA.17)`.  It
checks

```text
q^(-1)K_z=K_Beta;
q^(-1)K_(z^2)=K_(Beta z);
the transported nested band is `Beta K_z`;
the appended terminal response is zero;
the fixed-carrier response is `2ca`.                  (TA.26)
```

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/419_cumulative_delay_terminal_anomaly_guard_probe.py
```

The default WSL2 run reports

```text
maximum range error          0
maximum terminal response    4.440892098501e-16
maximum fixed-response error 3.885780586188e-16
minimum response separation  1.400000000000e-1
```

The exact response formulas are analytic.  The coefficient truncation only
checks their implementation.

## 10. Decision

```text
Proof 320 residual as a replacement Gate owner:      rejected;
appended model-space range identity:                 exact `(TA.9)`;
terminal band conjugacy:                             exact `(TA.14)`;
finite/separately legal terminal response:           zero `(TA.15)`;
actual fixed-carrier one-factor response:            nonzero `(TA.21)`;
naive finite scalar all-pass bridge:                 rejected;
weighted relative anomaly bridge:                    open `(TA.16),(TA.23)`;
Gate 3U / finite-S sign / Burnol / RH:                open / open / open / unproved.
```
