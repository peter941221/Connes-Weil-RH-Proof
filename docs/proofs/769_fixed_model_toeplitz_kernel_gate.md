# Proof 769: Weighted Toeplitz-kernel Gate owner

Date: 2026-08-03

Status: identifies the correct weighted fixed-model analytic carrier for the
finite-Euler Gram-corrected Sonin range. It replaces a tempting but generally
false direct all-pass model-space substitution by an exact Toeplitz-kernel
identity with the mandatory Burnol weight retained. This is a carrier
reduction and a producer contract, not a support-polynomial Gate 3U estimate.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| layer                                                | judgment             |
+------------------------------------------------------+----------------------+
| unweighted model under q_S                           | Toeplitz kernel      |
| actual Sonin range M_0=g_0 K_(Theta)                 | weighted frame       |
| Gram-corrected projection                            | exact weighted form  |
| direct replacement by K_(beta_S)                     | generally false      |
| Crofoot obstruction for a fixed finite-type model    | exact                |
| root-relative Toeplitz-kernel determinant estimate   | open                 |
| support-polynomial Gate 3U                           | open                 |
+------------------------------------------------------+----------------------+
```

The correct conditional bridge is

```text
fixed Burnol Sonin range M_0=g_0 K_(Theta)
       |
       | M_(q_S)
       v
g_0 ker T_(conj(Theta) q_S^(-1))
       |
       | Gram-corrected orthogonal projection
       v
the transported Sonin projection P_(R_S).             (TK.1)
```

It is not Proof 349's inverse-Euler all-pass identity

```text
q_S^(-1) K_(Theta_S) = K_(beta_S).                   (TK.2)
```

The actual Sonin transport uses the forward multiplier `q_S`, while `(TK.2)`
uses its inverse and the cumulative-delay source inner function `Theta_S`.
Neither substitution preserves the fixed weighted Burnol source range.

## 2. Exact Toeplitz-kernel identity

Work in either the disk or upper-half-plane Hardy space. Let `Theta` be
inner, let

```text
K_(Theta) = H2 minus-orthogonal Theta H2,
```

and let `q` be an invertible analytic multiplier:

```text
q, q^(-1) in H_infinity.                              (TK.3)
```

For the Toeplitz operator

```text
T_phi = P_+ M_phi restricted-to H2,
```

the transported range has the exact description

```text
q K_(Theta) = ker T_(conj(Theta) q^(-1)).             (TK.4)
```

Indeed, if `h=q f` with `f in K_(Theta)`, then

```text
T_(conj(Theta) q^(-1)) h = T_(conj(Theta)) f = 0.
```

Conversely, if the left Toeplitz operator kills `h`, then `f=q^(-1)h` lies in
`H2` and `conj(Theta) f` has no nonnegative Hardy component. Hence
`f in K_(Theta)` and `h=q f`. Both inclusions use only `(TK.3)`.

This is the useful ownership correction: a bounded outer multiplier always
produces a closed Toeplitz kernel here, even when it does not produce a
standard model space.

## 3. The actual source carries a mandatory weight

Proofs 375 and 407 give a model-form owner which is not the bare model space.
It is a nearly invariant Sonin range

```text
M_0 = g_0 K_(Theta),
h = abs(g_0)^2,                                      (TK.4a)
```

where multiplication by `g_0` is isometric on `K_(Theta)` in the prescribed
source norm. Proof 375 uses CCM24's actual range transport to represent the
forward finite Euler transport by `tau_S=q_S`. Multiplication then commutes
before compression and gives the range-level identity

```text
M_S = tau_S M_0
    = g_0 (q_S K_(Theta))
    = g_0 ker T_(conj(Theta) q_S^(-1)).              (TK.4b)
```

The last equality uses `(TK.4)`. It is the correct weighted Toeplitz-kernel
range owner, not an equality of the actual Sonin range with an unweighted
model space.

At the finite/frame level, write

```text
A_0 = M_(g_0) P_Theta,
A_S = M_(g_0 q_S) P_Theta.
```

Then the source metric is the compressed weighted form

```text
A_S* A_S = P_Theta M_(h abs(q_S)^2) P_Theta.         (TK.4c)
```

The identity `P_Theta M_h P_Theta=I` at `S=empty` is only the isometry in
`(TK.4a)`. It does not delete `h` from `(TK.4c)` after the Euler multiplier is
inserted. This is exactly Proof 407's weighted-compression guard.

## 4. The Gram correction is exactly the projection in (TK.1)

Let `P_Theta` project onto `K_(Theta)` and set

```text
A = M_(q) P_Theta.
```

The unweighted orthogonal projection onto the range in `(TK.4)` is

```text
P_(ker T_(conj(Theta) q^(-1)))
 =M_(q) P_Theta
   [P_Theta M_(abs(q)^2) P_Theta]^(-1)
   P_Theta M_(conj(q)).                               (TK.5)
```

Formula `(TK.5)` is the ordinary frame projection

```text
A (A* A)^(-1) A*.
```

Thus it has exactly the inverse-after-compression order which must be kept in
the actual Gate. It does not replace that inverse by an ambient inverse or by
an average of pointwise inverses.

The actual weighted source projection from `(TK.4a)--(TK.4c)` is instead

```text
P_(M_S)
 =M_(g_0 q_S) P_Theta
   [P_Theta M_(h abs(q_S)^2) P_Theta]^(-1)
   P_Theta M_(conj(g_0) conj(q_S)).                   (TK.5a)
```

At `S=empty`, the corresponding formula is

```text
P_(M_0)
 =M_(g_0) P_Theta [P_Theta M_h P_Theta]^(-1)
   P_Theta M_(conj(g_0)).                             (TK.5b)
```

Equations `(TK.5a)--(TK.5b)` are the weighted relative Gram owner from
Proof 407. They are the formulas relevant to the source endpoint. The
unweighted `(TK.5)` is only its Toeplitz-kernel coordinate skeleton.

## 5. The source gives the range, not the detector trace implementation

Burnol's Theorem 8 identifies `B(E_lambda)` isometrically with `S_lambda`,
the space of completed Mellin transforms of functions in the Sonin space
`K_lambda`. In the projection notation used by this repository, that supplies
the fixed-range map

```text
U_R : Ran(R) -> K_(Theta_lambda).                    (TK.6b)
```

after division by the Hermite--Biehler structure function. CCM24's actual
range transport, used in Proof 375, then supplies `(TK.4b)`. This is enough
to identify the moving subspace and its weighted frame.

Proof 407 gives the compact detector at the weighted compression-form level.
It does not construct its continuous root-sandwiched trace/determinant domain
or identify the full physical outer-minus-Sonin-prolate bracket with the
weighted Toeplitz-kernel trace. Those are required to identify `(TK.11)` with
the literal Gate scalar.

Therefore the inference

```text
Burnol Theorem 8
  -X-> continuous root-trace implementation of (TK.11)
```

is invalid. A valid future proof must construct the continuous trace-domain
intertwining and full physical-bracket readout on the actual Sonin range. The
cited source establishes neither item. This is the same carrier gap isolated
by Proofs 406--407.

## 6. Why the all-pass shortcut fails on a fixed carrier

Suppose, more strongly, that an inner `Alpha` satisfied

```text
q K_(Theta) = K_(Alpha).                              (TK.7)
```

Crofoot's multiplier criterion gives a necessary and sufficient boundary
condition. With `a=q`, it is

```text
Alpha conj(q) / (Theta q) = constant,
```

or equivalently

```text
Alpha = constant * Theta * q / conj(q).               (TK.8)
```

For the finite Euler denominator

```text
q_S = product_(p in S) (1-a_p theta_p),
theta_p(s)=exp(i log(p) s),
Theta_S=product_(p in S) theta_p,
q_S_sharp=product_(p in S) (theta_p-a_p),
beta_S=q_S_sharp/q_S,
```

the boundary identity is

```text
conj(q_S) = Theta_S^(-1) q_S_sharp.
```

Therefore `(TK.8)` forces

```text
Alpha = constant * Theta * Theta_S * beta_S^(-1).    (TK.9)
```

Formula `(TK.9)` is not the all-pass model `K_(beta_S)`: it contains the
reciprocal all-pass factor `beta_S^(-1)`, which is not an analytic multiplier
without an additional source-specific cancellation.

For the forbidden direct replacement by `K_(beta_S)`, set `Alpha=beta_S` in
Crofoot's condition. It would force

```text
Theta = constant * Theta_S^(-1) * beta_S^2.          (TK.10)
```

The finite all-pass factor `beta_S` has zero exponential mean type, whereas
`Theta_S` has type

```text
D_S = sum_(p in S) log(p).
```

For a fixed scalar inner `Theta` of finite nonnegative exponential mean type,
the right side of `(TK.10)` has negative type and grows on the positive
imaginary axis. Thus it cannot equal `Theta` once `D_S` is positive. This
rejects the direct `K_(beta_S)` replacement in the actual forward orientation.

The orientation is already visible in a one-dimensional disk model. Let

```text
Theta(z)=z,
K_(Theta)=span{1},
q(z)=1-a z,
beta(z)=(z-a)/(1-a z),
0<a<1.
```

Then

```text
q K_(Theta)       = span{1-a z},
q^(-1) K_(Theta)  = span{(1-a z)^(-1)} = K_(beta)
```

up to a nonzero scalar normalization. Thus the all-pass identity belongs to
the inverse multiplier, while the actual forward Sonin transport has the
different Toeplitz-kernel owner `(TK.4)`.

This recovers Proof 349's mean-type guard with the exact multiplier criterion:
the obstacle is not a missing normalization constant. It is the fact that
the transported fixed carrier is a Toeplitz kernel rather than a model space.

## 7. The actual Gate producer after this correction

If the root-detector and completed-trace implementation is established, the
outer-fixed same-object compact-root endpoint is the negative of the
root-sandwiched relative Toeplitz-kernel trace. Here `W_root` denotes the
actual compact-root detector in the same coordinate. The sign is the existing
outer-preservation identity `B_S-B=R-R_S`.

```text
-Tr[
   W_root
   (P_(g_0 ker T_(conj(Theta_lambda) q_S^(-1)))-P_(g_0 K_(Theta_lambda)))
 ].                                                   (TK.11)
```

The required theorem is not a generic Toeplitz-kernel norm bound. It must
prove, after inserting the full outer-minus-Sonin-prolate bracket and before
the first absolute value,

```text
abs (TK.11)
 <= C (1+B_root)^d
    norm(eta)_(H^r) norm(xi)_(H^r),                   (TK.12)
```

with constants independent of the finite visible set. The desired proof may
use a root-relative determinant or a source-specific Hitt/Sarason-type
factorization of the Toeplitz kernel, but it must preserve:

```text
the fixed Burnol Sonin range and outer-fixed endpoint difference;
the complete q_S before expansion;
the Gram-corrected projection in (TK.5);
the compact-root trace domain;
the outer, reflected second-support, and prolate cancellation;
the half-density cancellation and the far-tail split.
```

Replacing `(TK.11)` by `K_(beta_S)`, by a generic multiplier equivalence, or
by a separate bound for the three physical branches would lose one of those
requirements and does not prove Gate 3U.

## 8. Evidence

The multiplier criterion used in `(TK.8)` is Proposition 2.1 of the primary
source:

```text
C. Camara, C. Carteiro, W. T. Ross,
Multipliers and equivalence of functions, spaces, and operators,
arXiv:2307.05453, Proposition 2.1.
https://arxiv.org/abs/2307.05453
```

It says exactly that a bounded invertible multiplier `a` maps one scalar
model space onto another only when
`Alpha conj(a)/(Theta a)` is unimodular constant. The source proves an
equivalence statement; it does not provide `(TK.12)`, the continuous
root-detector trace implementation of `(TK.11)`, or a root-relative
determinant bound.

Burnol's original Theorem 8 is also primary evidence for the scope boundary:

```text
J.-F. Burnol,
Sur les espaces de Sonine associes par de Branges a la transformation de
Fourier, Theorem 8, arXiv:math/0208121.
https://arxiv.org/pdf/math/0208121
```

It identifies the completed Mellin transforms of the Sonin space `K_lambda`
with `B(E_lambda)`. Together with CCM24 transport it supports `(TK.4b)`, but
it does not identify the continuous completed trace needed for `(TK.11)`.

Project owner evidence for the two separate facts is

```text
Proof 375, (NI.3)--(NI.7):
  M_0=g_0 K_(Theta_lambda),
  M_S=q_S g_0 K_(Theta_lambda);

Proof 407, Section 2:
  the multiplier forms carry the mandatory weight h=abs(g_0)^2.
```

Those facts justify the range/frame coordinate. They do not construct the
continuous root-sandwiched trace equality in `(TK.11)`.

## 9. Route judgment

```text
fixed-model transported range -> Toeplitz kernel:       exact;
weighted compressed Gram projection:                    exact frame formula;
direct fixed-model all-pass replacement:                 rejected;
actual weighted Toeplitz-kernel range (TK.4b):              closed source-level;
continuous root-trace / physical-bracket readout:            not supplied;
generic quadratic response from the Toeplitz carrier:        rejected by Proof 785;
root-relative weighted Toeplitz-kernel estimate (TK.12):  open;
support-polynomial Gate 3U / finite-S sign / RH:         open.
```
