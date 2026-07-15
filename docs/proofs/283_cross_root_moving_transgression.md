# Proof 283: Cross-root moving transgression

Date: 2026-07-15

Status: exact sesquilinear bridge between Proof 263's legal compact-root
endpoint response and Proof 282's moving-band cocycle integral.  For two
distinct compact roots, the complex endpoint response equals twice the time
integral of the corresponding moving band mixed jet.  Complex polarization
recovers it from four diagonal root squares without enlarging support.

This places compact cross-correlation support outside the complete
synchronized time integral while preserving every branch and flow-time
cancellation.  It does not define a raw point response, prove the uniform
cross-root bound, close Gate 3U, or prove RH.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| compact cross-root endpoint form              | exact Proof 263 owner        |
| complex moving-band cocycle                   | exact                        |
| endpoint/moving transgression                  | exact                        |
| complex polarization                          | exact                        |
| support window under polarization             | preserved                    |
| raw point trace Tr(U_z(B_S-B))                 | unnecessary and forbidden    |
| uniform cross-root bound                      | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The bridge is

```text
compact roots eta,xi
  -> cross-correlation F_(eta,xi)
  -> legal endpoint response Q_S(eta,xi)
  = twice the complete moving-band cocycle integral
  -X-> no unsmoothed point response.                         (AT.1)
```

## 2. Legal cross-root detector

Let `eta,xi` be compact smooth roots and write

```text
W_(eta,xi)=C_xi* C_eta.                               (AT.2)
```

Proof 263 defines the legal endpoint response

```text
Q_S(eta,xi)
 =Tr(C_eta(B_(S,1)-B_(S,0))C_xi*)

 =Tr(W_(eta,xi)(B_(S,1)-B_(S,0))).                   (AT.3)
```

The ordinary trace in `(AT.3)` is licensed by Proof 261's root-sandwiched
`S1` theorem.  It is linear in `eta`, conjugate-linear in `xi`, and Hermitian:

```text
Q_S(xi,eta)=conj(Q_S(eta,xi)).                        (AT.4)
```

The detector is convolution by

```text
F_(eta,xi)=xi^star*eta.                               (AT.5)
```

If both roots are supported in `[-B_root,B_root]`, then

```text
supp(F_(eta,xi)) subset [-2B_root,2B_root].           (AT.6)
```

Equation `(AT.6)` is a property of the complete endpoint functional, not of a
pointwise translated trace.

## 3. Complex moving cocycle

At synchronized time `alpha`, retain Proof 282's moving projections and real
generator multiplier

```text
E_alpha,R_alpha,B_alpha,C_alpha,
H_alpha=M_(h_(S,alpha)).                              (AT.7)
```

Use independent deformation parameters `(s,r)` and put

```text
U_(eta,xi,s)=exp(s W_(eta,xi)),
V_(alpha,r)=exp(r H_alpha).                           (AT.8)
```

For cross roots, `W_(eta,xi)` need not be self-adjoint.  Nevertheless its
detector commutators with `E_alpha,R_alpha` are trace class by polarization of
Proof 261, and all shorted compressions stay invertible near `(0,0)`.  Thus
Proof 281's band cocycle defines an analytic Fredholm determinant

```text
ell_(eta,xi,S,alpha)(s,r).                            (AT.9)
```

Its mixed jet is linear in the cross detector:

```text
partial_(s,r)log ell_(eta,xi,S,alpha)|_0

 =Tr(B_alpha W_(eta,xi) C_alpha H_alpha B_alpha)
  -Tr(R_alpha W_(eta,xi) B_alpha H_alpha R_alpha).
                                                               (AT.10)
```

No positivity of the cross detector is used.

## 4. Transgression identity

Proof 282's derivation is linear in `W`.  Applying it to `(AT.2)` gives

```text
Q_S(eta,xi)

 =2 integral_0^1
    partial_(s,r)log ell_(eta,xi,S,alpha)(s,r)|_0
   dalpha

 =2 integral_0^1 [
    Tr(B_alpha W_(eta,xi) C_alpha H_alpha B_alpha)
   -Tr(R_alpha W_(eta,xi) B_alpha H_alpha R_alpha)
   ] dalpha.                                          (AT.11)
```

Equation `(AT.11)` is the moving-to-endpoint transgression.  It gives the same
functional two complementary coordinates:

```text
endpoint coordinate:
  compact cross-correlation F_(eta,xi);

moving coordinate:
  synchronized signed band cocycle integral.          (AT.12)
```

Use the endpoint coordinate to expose compact support and the moving
coordinate to preserve complete Euler/branch cancellation.  Neither
coordinate may be replaced by separate positive norms.

## 5. Polarization without support growth

Proof 263's complex polarization is

```text
Q_S(eta,xi)
 =1/4 sum_(k=0)^3 i^k
    Q_S(eta+i^k xi,eta+i^k xi).                       (AT.13)
```

Every combined root in `(AT.13)` remains supported in the same window.
Therefore a uniform diagonal estimate and the cross-root estimate are
equivalent up to a fixed constant.  The same polarization applies to the
right side of `(AT.11)` because its mixed jet is linear in `W_(eta,xi)`.

This is the legal way to pass between Hermitian detectors and complex
cross-correlations.  It does not require extending the response to every
arbitrary compact test function.

## 6. Why raw point responses remain forbidden

The compact convolution factorization `(AT.5)` may suggest the notation

```text
kappa_S(z)=Tr(U_z(B_(S,1)-B_(S,0))).                  (AT.14)
```

Proofs 260 and 263 show that `(AT.14)` need not be an ordinary trace.  Proof
283 never uses it.  The allowed order is

```text
factorized compact roots
  -> trace-class endpoint response
  -> moving transgression
  -> compact-support stopping inside the complete scalar.       (AT.15)
```

Disintegrating `(AT.11)` into pointwise `z` values would add a new trace-domain
premise and is not part of the route.

## 7. Actual finite-S certificate

The certificate uses two distinct compact roots in one source window.  Their
Fourier multipliers form the genuinely complex detector

```text
w_(eta,xi)=conj(xi_hat) eta_hat.                       (AT.16)
```

It reuses Proof 253's actual prime-log translations, moving projections, and
complete generator.  Independently checked quantities are

```text
complex endpoint response;
twice the moving-band integral;
direct transported-projection integral;
complex band-cocycle mixed jet;
four-term diagonal polarization.                      (AT.17)
```

The default cohort (`size=96`, `step=0.08`) reports

```text
maximum exact algebra error          3.18e-16,
maximum endpoint error               2.13e-10,
maximum cocycle mixed-jet error      9.51e-9,
maximum polarization error           1.29e-17.
```

The alternate cohort (`size=128`, `step=0.064`) reports

```text
maximum exact algebra error          2.80e-16,
maximum endpoint error               2.38e-11,
maximum cocycle mixed-jet error      1.19e-8,
maximum polarization error           5.48e-18.
```

The endpoint responses have nonzero real and imaginary parts in both cohorts;
the certificate is not accidentally testing only a Hermitian diagonal.
Numerical values remain finite-section diagnostics, not a continuous bound.

## 8. Active norm contract

The remaining theorem is exactly Proof 263's cross-root contract, now with the
moving owner identified:

```text
|Q_S(eta,xi)|

 =|2 integral_0^1
    partial_(s,r)log ell_(eta,xi,S,alpha)|_0 dalpha|

 <=C(1+B_root)^d
   norm(eta)_(H^r)norm(xi)_(H^r),                    (AT.18)
```

uniformly in finite `S`.  The compact support in `(AT.6)` must be applied
before any Markov/prime disintegration or absolute value.

Proof 283 does not prove `(AT.18)`.  It removes three distractions from the
active bottom:

```text
no endpoint/moving owner mismatch;
no need for a pointwise translated trace;
no need to prove diagonal and cross-root bounds separately.      (AT.19)
```

## 9. Reproduction

Run in WSL2:

```text
OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/283_cross_root_moving_transgression_probe.py

OPENBLAS_NUM_THREADS=1 python3 -B \
  docs/proofs/283_cross_root_moving_transgression_probe.py \
  --size 128 --step 0.064 --root-width 0.576 \
  --prime-cutoffs 2,11,29 --quadrature-order 10 \
  --cocycle-nodes 3
```

Both runs report

```text
sesquilinear_endpoint_owner=EXACT,
complex_polarization=EXACT,
moving_band_transgression=EXACT,
compact_root_support_preserved=EXACT,
raw_point_translation_trace_required=FALSE,
uniform_cross_root_bound=OPEN,
RH=UNPROVED.
```

## 10. Route judgment

Proof 283 makes compact support and synchronized cancellation simultaneous
properties of one response functional.  The active proof should now work
directly with the factorized cross-root functional `(AT.11)`, not with raw
point translations or separate band branches.

The next attack is

```text
factorized cross-root moving response (AT.11)
  -> source one-sided causal path representation
  -> keep F_(eta,xi) support before path expansion
  -> pair equal histories across both moving boundaries
  -> stop the unmatched residual at displacement 2B_root
  -> uniform bound (AT.18)
  -> Gate 3U.                                             (AT.20)
```

The causal path representation, uniform bound, finite-S sign, arithmetic
same-object trace identity, negative-owner integration, Burnol's all-zero
identity, and RH remain open.  No Lean owner or route consumer is changed.

## 11. Successor audit

Proof 284 carries the non-Hermitian cross detector into Proof 270's causal
renewal columns.  The import requires one adjoint correction:

```text
L_P(W)=A R W* Q B,
```

not the Hermitian-only `A R W Q B`.  With the corrected complete left reward,
the response in `(AT.11)` is exactly

```text
Q_S(eta,xi)=Tr_B(C_(L,W_(eta,xi))* C_K).
```

The successor still keeps compact support before causal scalar
disintegration; it does not license a raw point trace or a positive column
norm estimate.  See
`docs/proofs/284_cross_root_causal_observability.md`.
