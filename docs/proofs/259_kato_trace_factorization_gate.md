# Proof 259: Kato trace-factorization gate

Date: 2026-07-15

Status: rejects Proof 258's covariant leakage as the owner of the route trace.
The Kato transport remains exact, but `C_t=Q mathcalU_tB` records only the
`Q`-corner of the moving band.  It neither determines the full projection
response nor supplies the second Hilbert--Schmidt factor required by the
project trace standard.  A four-dimensional Q-preserving nested path has
constant nonzero `C_t` and a nonzero route response even though the detector
commutes with the source transport.

The trace-compatible Kato identity uses the full generator
`A_t=[B_t',B_t]=Y_t-Y_t*`.  It exposes a possible pair of localized Schatten
crossings but does not prove the ordinary route trace or a uniform bound.
Proof 260 sharpens the successor: two Hilbert--Schmidt factors are a sufficient
legality certificate, but their positive norm product cannot carry the
support-sensitive uniform estimate.  Ordinary trace legality and the signed
scalar estimate are separate gates.  Proof 261 closes the fixed-`S` legality
gate; the signed uniform estimate remains open.  No Lean owner or route rewire
is authorized, and RH remains unproved.

## 1. Result first

```text
+------------------------------------------------+------------------------------+
| object                                         | judgment                     |
+------------------------------------------------+------------------------------+
| Kato generator and unitary transport           | exact                        |
| C_t=Q mathcalU_tB                              | exact Q-corner owner         |
| C_t as owner of Tr(W(B_t-B_0))                 | rejected                     |
| natural Kato-frame two-factor trace            | illegal: one factor not HS   |
| restricted-Grassmannian Schatten propagation   | assumes the missing ideal    |
| full-generator commutator trace identity       | exact                        |
| source-specific trace-class legality           | closed by Proof 261          |
| uniform bound by two-HS factor norms           | rejected by Proof 260        |
| signed complete-trace estimate                 | open, Gate 3U                |
| same-object finite-S trace identity            | open                         |
| RH                                             | unproved                     |
+------------------------------------------------+------------------------------+
```

The ownership correction is

```text
C_t=Q mathcalU_tB
  |
  +-- knows Q B_t Q
  +-- misses (I-Q) mathcalU_tB
  +-- cannot determine the route trace
  |
  X

A_t=Y_t-Y_t*
  |
  +-- contains the complete band derivative
  +-- must remain recombined through root smoothing
  |
  v
source-specific crossing factorization of Y_t.                 (V.1)
```

## 2. Proof 227 and Proof 258 use the same Kato transport

Proof 257 writes the complete lower off-diagonal band derivative as

```text
B_t'=Y_t+Y_t*,

Y_t
 =(I-E_t)X_tB_t-R_tX_t*Q B_t.                         (V.2)
```

The range relations give

```text
Y_t=(I-B_t)Y_tB_t,
B_tY_t=0,
Y_tB_t=Y_t.                                           (V.3)
```

Consequently

```text
[B_t',B_t]
 =(Y_t+Y_t*)B_t-B_t(Y_t+Y_t*)
 =Y_t-Y_t*.                                           (V.4)
```

Proof 227 called the right side `K_t`; Proof 258 called it `A_t`.  Their
unitary differential equations agree:

```text
mathcalU_t'=(Y_t-Y_t*)mathcalU_t,
B_t=mathcalU_tB mathcalU_t*.                          (V.5)
```

Proof 258 adds one observation map,

```text
C_t=Q mathcalU_tB.                                    (V.6)
```

Thus Proof 258 changes the observed corner, not the Kato mechanism.

## 3. The covariant leakage does not determine the route trace

Put

```text
V_t=mathcalU_tB,
D_t=(I-Q)V_t.
```

Then

```text
V_t*V_t=B,
V_tV_t*=B_t,
C_t=QV_t,

B_t
 =C_tC_t*+C_tD_t*+D_tC_t*+D_tD_t*.                   (V.7)
```

Proof 258's equality

```text
C_tC_t*=Q B_tQ                                        (V.8)
```

controls the first term in `(V.7)`.  The route detector is a convolution and
does not factor through `Q`.  Its response sees the other three terms.

Differentiation has the same loss:

```text
C_t'=Q A_tV_t=QY_tV_t.                                (V.9)
```

Equation `(V.9)` sees only the `Q`-part of the lower crossing.  The outer
component `(I-Q)Y_tV_t` and the adjoint component in `B_t'` do not follow from
`C_t'`.

### 3.1 Exact nested guard

Work in `C^4` with orthonormal basis `e_0,e_1,e_2,e_3`.  Define

```text
Q=|e_0><e_0|+|e_1><e_1|,
R=|e_0><e_0|,

0<theta_0<theta<pi/2,

v_(theta_0)
 =cos(phi)e_1
   +sin(phi)(cos(theta_0)e_2+sin(theta_0)e_3),

v_theta
 =cos(phi)e_1
   +sin(phi)(cos(theta)e_2+sin(theta)e_3),

B_theta=|v_theta><v_theta|,
E_theta=R+B_theta.                                    (V.10)
```

Use the diagonal source transport

```text
T_theta
 =c_theta diag(1,1,
                cos(theta)/cos(theta_0),
                sin(theta)/sin(theta_0)),              (V.10a)
```

where the positive scalar `c_theta` makes `T_theta*T_theta>=I`.  This transport
fixes `Ran(Q)` and maps `v_(theta_0)` to a scalar multiple of `v_theta`.  The
detector `W=|e_3><e_3|` commutes with `T_theta` and its logarithmic derivative.
Also

```text
R=Ran(E_theta) intersection Ran(Q),
(I-Q)XQ=0.                                            (V.10b)
```

The Kato partial frame from the base band is

```text
V_theta=|v_theta><v_(theta_0)|.
```

Its leakage is constant and nonzero:

```text
C_theta=Q V_theta
       =cos(phi)|e_1><v_(theta_0)|,
C_theta'=0.                                           (V.10c)
```

The commuting positive detector gives

```text
Tr(W(B_theta-B_(theta_0)))
 =sin(phi)^2 [sin(theta)^2-sin(theta_0)^2],

Tr(W B_theta')
 =sin(phi)^2 sin(2 theta).                             (V.10d)
```

At `phi=pi/4`, `theta_0=pi/6`, and `theta=pi/3`, `(V.10c)` remains constant
while `(V.10d)` equals `1/4` at the endpoint and `sqrt(3)/4` at the derivative.
This model satisfies detector/transport commutation, exact Q-preservation,
nestedness, a normalized metric at least the identity, and the complete
orthogonal projection flow.  It proves that no theorem based only on `C_t`,
`C_t'`, or `C_tC_t*` can recover the route response.

The model leaves Proof 257's second-boundary branch zero.  It is a logical
guard against the proposed owner, not a continuous counterexample to the
source-specific three-branch estimate.

## 4. The natural Kato-frame factorization is not trace legal

The Kato frame satisfies

```text
V_t'=A_tV_t,
B_t'=V_t'V_t*+V_tV_t'*.                               (V.14)
```

For root convolutions `C_eta,C_xi`, `(V.14)` suggests

```text
C_eta B_t' C_xi*
 =(C_eta A_tV_t)(C_xiV_t)*
   +(C_etaV_t)(C_xiA_tV_t)*.                          (V.15)
```

Each product in `(V.15)` needs two Hilbert--Schmidt factors.  Kato transport
does not make `C_xiV_t` or `C_etaV_t` Hilbert--Schmidt.

The failure already occurs for one half-line.  On `L2(R)`, let

```text
P_+=1_[0,infinity),
(C_g f)(x)=integral_R g(x-y)f(y)dy,
g in L2(R), g nonzero.
```

The kernel of `C_gP_+` is `g(x-y)1_(y>=0)`, hence

```text
norm(C_gP_+)_HS^2
 =integral_(y>=0) integral_R |g(x-y)|^2 dx dy
 =integral_(y>=0) norm(g)_2^2 dy
 =infinity.                                           (V.16)
```

The completed boundary crossing has a different count.  For a translation
`U_b`, `b>0`,

```text
norm(C_g[P_+,U_b])_HS^2=b norm(g)_2^2.                (V.17)
```

Only an interval of length `b` remains in `(V.17)`.  The local project source
records this calculation at
`docs/proofs/037_metric_sonin_ideal_closure.md:50--61`; the same finite-interval
geometry underlies `SelectedCrossingKernel` and
`SelectedCrossingOperatorBridge`.

Thus `(V.15)` repeats the bounded-times-Hilbert--Schmidt error rejected by the
finite-interval calculation in
`docs/proofs/037_metric_sonin_ideal_closure.md:50--61`.  The second factor is a
smoothed infinite frame, not a smoothed crossing.

## 5. The full Kato generator gives the compatible trace identity

Let

```text
A_t=[B_t',B_t]=Y_t-Y_t*,
W_(xi,eta)=C_xi* C_eta.                               (V.18)
```

Whenever the source-specific trace products are legal, cyclicity gives

```text
q_t(eta,xi)
 :=Tr(C_eta B_t' C_xi*)

  =Tr(W_(xi,eta)[A_t,B_t])
  =Tr([B_t,W_(xi,eta)]A_t).                           (V.19)
```

Expand the detector commutator before taking a norm:

```text
[B_t,C_xi* C_eta]
 =[B_t,C_xi*]C_eta+C_xi*[B_t,C_eta].                  (V.20)
```

At the scalar trace level, `(V.19)--(V.20)` become

```text
q_t(eta,xi)
 =Tr([B_t,C_xi*] (C_eta A_t))
   +Tr([B_t,C_eta] (A_t C_xi*)).                      (V.21)
```

The two displayed products meet the project trace rule if

```text
[B_t,C_xi*] in S2,      C_eta A_t in S2,
[B_t,C_eta] in S2,      A_t C_xi* in S2.              (V.22)
```

Since `A_t*=-A_t`, the second generator condition is the adjoint of the first
with the matching root.  Hilbert--Schmidt Holder then gives

```text
abs(q_t(eta,xi))
 <=norm([B_t,C_xi*])_2 norm(C_eta A_t)_2
   +norm([B_t,C_eta])_2 norm(A_t C_xi*)_2.             (V.23)
```

Equation `(V.21)` keeps

```text
A_t
 =[(I-E_t)X_tB_t-R_tX_t*Q B_t]
   -[(I-E_t)X_tB_t-R_tX_t*Q B_t]*                     (V.24)
```

whole.  A proof of `C_eta A_t in S2` must insert Proof 257's completed
second-support leakage before applying a norm.  The outer crossing,
second-boundary crossing, and base prolate term must remain in the same
operator sum.

Equations `(V.21)--(V.23)` identify a compatible scalar trace factorization.
They do not by themselves prove that the original operator
`C_eta B_t'C_xi*` is trace class.  The route still needs a source-specific
operator identity which factors the complete `Y_t` through a common crossing
space:

```text
Y_t=L_t R_t,
C_eta L_t in S2,
R_t C_xi* in S2,

C_eta Y_t C_xi*
 =(C_eta L_t)(R_t C_xi*) in S1.                        (V.25)
```

The adjoint supplies the second half of `B_t'`.  A direct-sum factorization
which places the three source branches in separate summands loses their
cancellation in the Hilbert--Schmidt norm.  Proof 260 shows that this loss is
unavoidable for any estimate based only on the positive factor norms: even an
optimal factorization can have a strictly positive nuclear cost when compact
root support makes the scalar trace exactly zero.  Thus `(V.25)` remains a
sufficient legality contract, not the quantitative route owner.

This is Proof 227's local complete-crossing contract with its two trace factors
made explicit.  Proof 258 supplies no estimate for either factor in `(V.25)`.

## 6. Restricted-Grassmannian and Kato source audit

The literature confirms the algebra in Proof 258 and does not supply the
missing localized ideal theorem.

```text
+-------------------------------+---------------------------------------------+
| source                        | source statement and route consequence      |
+-------------------------------+---------------------------------------------+
| Avron--Fraas--Graf--Grech     | Section 2.1, equations (5)--(7), defines    |
| arXiv:1106.4661v2             | T'=[P',P]T and proves range transport.  It  |
|                               | asserts no Schatten gain from a bounded     |
|                               | projection path.                            |
+-------------------------------+---------------------------------------------+
| Andruchow--Larotonda          | Sections 1--3 put Gr_res^0(p) inside        |
| arXiv:0808.2525v1             | p+S2 and define its tangent space in S2.    |
|                               | The ideal property is part of the manifold. |
+-------------------------------+---------------------------------------------+
| Andruchow--Larotonda--Recht   | Proposition 2.2 solves the horizontal lift  |
| arXiv:0808.2274v1             | with an S2-valued generator and obtains a   |
|                               | unitary in I+S2.  It assumes the S2 tangent.|
+-------------------------------+---------------------------------------------+
| Lazarovici                    | Section 2.3 models restricted-Grassmannian  |
| arXiv:1310.1778               | charts by graphs of Hilbert--Schmidt maps.  |
|                               | The cross-corner condition is a definition. |
+-------------------------------+---------------------------------------------+
| Andruchow--Corach             | arXiv:1701.03737 studies pairs with PQ      |
|                               | compact as a special geometric class.       |
|                               | Kato transport alone does not place a pair  |
|                               | in that class.                              |
+-------------------------------+---------------------------------------------+
```

Source URLs:

```text
https://arxiv.org/abs/1106.4661
https://arxiv.org/abs/0808.2525
https://arxiv.org/abs/0808.2274
https://arxiv.org/abs/1310.1778
https://arxiv.org/abs/1701.03737
```

If one assumes an `S2` path in the first place, the unitary Kato flow avoids an
exponential Gronwall loss and obeys a bound by the restricted-Grassmannian
length `integral norm(B_t')_2 dt`.  That premise is stronger than the route's
localized crossing claim.  The unsmoothed Euler boundary generator need not
belong to `S2`, and a termwise estimate of its prime channels returns the
rejected `p^(-m/2)` majorant.

The literature therefore supplies no shortcut around `(V.25)`.

## 7. Reproducible certificate

Run from the Windows source snapshot in WSL2:

```text
OPENBLAS_NUM_THREADS=4 python3 -B \
  docs/proofs/259_kato_trace_factorization_gate_probe.py
```

The trace-factorization check reports

```text
+--------------------------------------+-----------+
| check                                | error     |
+--------------------------------------+-----------+
| A_t*=-A_t                            | 0         |
| [B_t',B_t]=A_t                       | 0         |
| commutator trace identity            | 1.98e-16  |
| two-factor scalar trace identity     | 9.88e-17  |
+--------------------------------------+-----------+
```

The nested leakage guard reports

```text
+--------------------------------------+-----------+
| check                                | value     |
+--------------------------------------+-----------+
| Q-invariance error                   | 0         |
| detector/transport commutator        | 0         |
| minimum metric eigenvalue            | 1         |
| source band-flow error               | 3.45e-16  |
| Kato commutator error                | 1.34e-16  |
| leakage change norm                  | 0         |
| leakage derivative norm              | 4.45e-17  |
| route endpoint response              | 0.25      |
| route derivative response            | 0.433013  |
+--------------------------------------+-----------+
```

The maximum algebra error is `3.45e-16`.  Finite matrices certify the
identities and the logical blindness of `C_t`; they prove no continuous
Schatten bound.

## 8. Route judgment

```text
+--------------------------------------------------+---------------------------+
| layer                                            | judgment                  |
+--------------------------------------------------+---------------------------+
| Proof 258 Kato algebra                           | retained                  |
| C_t as prolate/leakage diagnostic                | retained                  |
| C_t as complete route-trace owner                | rejected exactly          |
| seminorm norm(C_g C_t)_2 as active bottom        | retired                   |
| natural frame factor C_g mathcalU_tB            | not Hilbert--Schmidt       |
| full A_t trace-commutator identity               | exact                     |
| full fixed-S source-specific trace legality      | closed by Proof 261       |
| uniform estimate by two-HS factor norms          | rejected by Proof 260     |
| signed polynomial-support bound                  | open, Gate 3U             |
| negative-owner integrated smallness              | open                      |
| same-object finite-S trace identity              | open                      |
| Burnol all-zero identity                         | open                      |
| Lean owner or route rewire                       | none                      |
| RH                                               | unproved                  |
+--------------------------------------------------+---------------------------+
```

Proof 261 proves ordinary trace-class legality of the complete root-sandwiched
`Y_t+Y_t*` for each fixed finite set.  The remaining uniform estimate must be
proved on the recombined signed scalar trace, not by multiplying the norms of
two Hilbert--Schmidt factors.  Estimating `C_t`, `B_t'`, `X_t`, or the three
source branches in separate norms does not meet Gate 3U.  See
`docs/proofs/260_schatten_legality_signed_trace_gate.md` and
`docs/proofs/261_fixed_s_trace_class_gate.md`.
