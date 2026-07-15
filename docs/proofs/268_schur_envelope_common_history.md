# Proof 268: Schur envelope, common history, and raw-innovation guard

Date: 2026-07-15

Status: exact first-jet refinement and rejection guard for Proof 267.  The
derivative of a Schur shorting has an envelope formula: the derivatives of its
graph coordinates cancel, leaving one compression of the ambient derivative.
Applied to the relative Jacobi cocycle, this formula recovers Proof 266's
ordered causal Gram response without cycling `Gamma^(-1)`.

The probability lift gives a difference between a normalized constant-channel
frame and the full random-unitary frame.  Compact support does not delete raw
translation paths separately.  The centered response first removes common
translation history, after which compact support clips the remaining relative
displacement.  Large comparable distinct primes can still have small relative
displacement and remain in the source response.

A raw prime-martingale estimate also fails quantitatively.  For one normalized
Euler factor with `a=p^(-1/2)`, the innovation defect has exact norm
`4a/(1+a)^2`, which is order `p^(-1/2)`.  The missing square must come from the
complete detector/Sonin/prolate first jet before prime orthogonality is used.

No uniform Gate 3U bound, finite-`S` sign, same-object arithmetic trace
identity, Burnol identity, Lean owner, route rewire, or RH proof is claimed.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Schur shorting graph owner                    | exact                        |
| Schur envelope derivative                    | exact                        |
| ordered causal Gram first jet                | recovered                    |
| lifted constant/full frame first jet         | exact                        |
| raw absolute-path support clip               | false                        |
| common translation-history cancellation      | exact half-line guard        |
| compact clip of reduced displacement          | exact half-line trace        |
| raw prime innovation square gain              | false, exact O(p^(-1/2))     |
| large comparable-prime cancellation           | open, source-specific        |
| Gate 3U                                       | open                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The active first jet is

```text
R'_0
 =F_0* mathcalW F_0 Gamma^(-1)
  -F_1* mathcalW F_1,                                 (AE.1)
```

where `F_0` is the constant-probability residual frame, `F_1` is the full
random-unitary frame, and `F_0*F_0=Gamma`, `F_1*F_1=B`.  The position of
`Gamma^(-1)` in `(AE.1)` is part of the theorem.

## 2. Schur shorting and its graph

Let `C` and `B` be orthogonal projections.  Let `X` be positive and boundedly
invertible on `Ran(C+B)`.  Define

```text
L_X=(C X C)^(-1)C X B,
Z_X=B-C L_X.                                           (AE.2)
```

Then

```text
C X Z_X=0,                                             (AE.3)

Short_B|C(X)
 =B X B-B X C(C X C)^(-1)C X B
 =Z_X* X Z_X.                                         (AE.4)
```

The map `Z_X` is the graph frame whose image is `X`-orthogonal to `Ran(C)`.

## 3. Envelope derivative

Let `X_s` be a differentiable positive path and write `Z_s=Z_(X_s)`.  Since

```text
Z_s'= -C L_s'                                         (AE.5)
```

has range in `C`, equation `(AE.3)` kills both graph-derivative terms in

```text
partial_s(Z_s* X_s Z_s).
```

Therefore

```text
partial_s Short_B|C(X_s)
 =Z_s* X_s' Z_s.                                      (AE.6)
```

Equation `(AE.6)` is an operator envelope theorem.  It removes derivatives of
the conditioned graph without estimating them.

For bounded cross detectors, complex polarization reduces the required first
jet to the self-adjoint paths used in `(AE.6)`.

## 4. Recover the ordered causal Gram response

Use Proof 267's two paths

```text
M_s=M exp(-sW),
G_s=exp(-sW),
M=A* A.                                                (AE.7)
```

Put

```text
Z=Z_M,
Gamma=Short_B|C(M).                                   (AE.8)
```

The causal triangular factorization gives

```text
A Z=E A B=K.                                           (AE.9)
```

Indeed, relative to `C direct-sum E`, write

```text
    [A_C  X]
A = [      ].                                          (AE.10)
    [ 0   A_E]
```

Then `(C M C)^(-1)C M B=A_C^(-1)X B`, and multiplying
`B-C A_C^(-1)X B` by `A` deletes the `C` component exactly.

Proof 267's ordered shorted ratio is

```text
mathcalR_s
 =Gamma Short_B|C(M_s)^(-1) Short_B|C(G_s).           (AE.11)
```

Differentiate `(AE.11)` at zero.  Equation `(AE.6)` gives

```text
mathcalR'_0
 =Z* M W Z Gamma^(-1)-B W B

 =K* W K Gamma^(-1)-B W B.                            (AE.12)
```

This is Proof 266's ordered causal Gram operator.  No trace cycle moves
`Gamma^(-1)` to the left.  Proof 264's central anomaly would make that cycle
false in the source space.

## 5. Lift the first jet

Use the probability dilation

```text
V*V=I,
M=V*P_0V,
mathcalW=I_(Omega_S) tensor W.                         (AE.13)
```

Since `V` intertwines the Euler translations with the detector,

```text
Z* M W Z
 =(P_0VZ)* mathcalW(P_0VZ),

B W B
 =(VB)* mathcalW(VB).                                  (AE.14)
```

Define

```text
F_0=P_0VZ,
F_1=VB.                                                (AE.15)
```

Their Gram operators are

```text
F_0*F_0=Gamma,
F_1*F_1=B.                                             (AE.16)
```

Substitution of `(AE.14)--(AE.16)` into `(AE.12)` proves `(AE.1)`.

The formula compares two frames in their determinant-line ordering.  Replacing
`F_0` by `F_0 Gamma^(-1/2)` inside an ordinary trace discards the similarity
anomaly from Proof 264.

## 6. Raw paths do not stop individually

Consider `ell2(Z)`.  Let

```text
E=P_(n>=0),
U_x e_n=e_(n+x),
W=C_F,
supp(F) subset [-L,L].                                 (AE.17)
```

Expand one pair of shifts in the centered outer numerator:

```text
D_(x,y)
 =E U_x* E W E U_y E
  -E W E E U_x* E U_y E.                              (AE.18)
```

For `y>=x` and `y>=L`, both paths have moved beyond the detector boundary
before their relative motion is read.  Direct shift algebra gives

```text
D_(x,y)=0.                                             (AE.19)
```

For `x>y` and `y>=L`, the common history `y` cancels and

```text
D_(x,y)
 =E W(I-E)U_(y-x)E,                                   (AE.20)
```

which depends on the relative displacement `x-y`, not on the common absolute
translation.  Thus

```text
D_(x+k,y+k)=D_(x,y)                                   (AE.21)
```

once the artificial far boundary is absent.

The trace of `(AE.20)` is a completed half-line crossing.  It vanishes for
`|x-y|>L` under the corresponding convolution support convention, while the
operator itself can remain nonzero off the diagonal.  Compact support clips
the scalar relative crossing after common-history cancellation.

Large comparable distinct primes satisfy

```text
|log(p)-log(q)|<=2B_root                               (AE.22)
```

for infinitely many possible pairs as the visible set grows.  Equation
`(AE.21)` does not remove them.  The complete `E/R/Q/K_prol` first jet must
control their signed aggregate.

## 7. The raw prime innovation has the wrong scale

For one normalized Euler inverse factor, put

```text
A_a(theta)=(1-a)/(1-a exp(i theta)),
0<a<1.                                                 (AE.23)
```

The random-unitary innovation Gram is

```text
I-A_a* A_a.                                            (AE.24)
```

Its operator norm is the maximum of

```text
1-|A_a(theta)|^2.
```

The maximum occurs at `theta=pi`, giving

```text
norm(I-A_a* A_a)
 =1-((1-a)/(1+a))^2
 =4a/(1+a)^2
 =O(a).                                                (AE.25)
```

At the Euler value `a=p^(-1/2)`, equation `(AE.25)` has the forbidden
`p^(-1/2)` scale.  Orthogonality of raw probability martingale differences
does not create the missing square.

## 8. Corrected innovation target

Proof 268 rejects this order:

```text
I-P_0
  -> prime martingale differences
  -> raw square function
  -> detector and Sonin shorting.                     (AE.26)
```

The required order is

```text
ordered relative first jet (AE.1)
  -> common-history cancellation
  -> compact clip of relative displacement
  -> complete E/R/Q/K_prol cancellation
  -> martingale or Euler-product square function
  -> one absolute value.                              (AE.27)
```

The next sufficient theorem must factor the complete centered frame difference
in `(AE.1)` into source-owned innovations with one of these gains:

```text
single-prime contribution:  poly(log p) p^(-1);

mixed contribution: an orthogonal or determinant-resummed family whose total
is polynomial in B_root and independent of S.          (AE.28)
```

Proof 251 rules out termwise absolute control of mixed Hessians.  Equation
`(AE.28)` must apply to the complete endpoint or its relative determinant,
not to a fixed Taylor degree.

## 9. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/268_schur_envelope_common_history_probe.py
```

The default run reports

```text
+--------------------------------------+----------------+
| check                                | value          |
+--------------------------------------+----------------+
| Schur envelope derivative error      | 7.97e-10       |
| lifted first-jet error               | 1.13e-9        |
| common translation error             | 0              |
| forward common-history error         | 0              |
| far relative trace error             | 0              |
| surviving near relative trace mass   | 3.10e-1        |
| one-prime defect formula error        | 1.67e-16       |
| minimum defect/a ratio               | 1.83           |
+--------------------------------------+----------------+
```

The common-history layer uses zero-fill shifts only inside a protected finite
window; no path reaches its artificial far boundary.  It certifies the local
shift algebra in `(AE.18)--(AE.21)`, not a global finite-section limit.

## 10. Route judgment

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Proof 267 shorted determinant first jet       | explicit envelope formula    |
| graph/coframe derivative                      | cancels exactly              |
| causal Gram ordering                          | retained                     |
| lifted constant/full frame owner              | exact                        |
| raw pathwise compact stopping                 | rejected                     |
| common-history reduction                      | exact half-line model        |
| raw prime martingale square gain              | rejected by (AE.25)          |
| full Sonin/prolate innovation gain            | open, active Gate 3U         |
| negative-owner integrated smallness           | open                         |
| same-object finite-S trace identity            | open                         |
| Burnol all-zero identity                       | open                         |
| Lean owner or route rewire                     | none                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

Proof 268 narrows the next attack to the centered, ordered frame difference
`(AE.1)`.  Compact support acts on its reduced displacement after common
history cancels.  The complete Sonin/prolate geometry must supply the extra
half-power before prime orthogonality can yield a uniform bound.
