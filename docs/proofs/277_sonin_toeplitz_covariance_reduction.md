# Proof 277: Sonin Toeplitz covariance reduction

Date: 2026-07-15

Status: exact algebraic refinement of Proofs 275 and 276.  The moving
projection Dirichlet first jet is twice a Toeplitz semicommutator.  Proof 276's
static CC20 remainder controls the uncompressed Toeplitz trace, but it does not
control the compressed Toeplitz product.  A three-point model with a strictly
positive detector has zero static product trace and a nonzero Dirichlet
pairing, so the distinction is structural.

The missing one-prime estimate is now a half-power bound for one named Toeplitz
covariance.  The relative Jacobi determinant must retain its mixed-prime
version.  Gate 3U and RH remain open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| Dirichlet pairing as Toeplitz semicommutator  | exact                        |
| semicommutator as completed crossing          | exact                        |
| static CC20 displacement exponent             | fixed-support control only   |
| polynomial support-width cost                 | still open                   |
| compressed Toeplitz product term              | open                         |
| static trace alone controls covariance        | false by positive guard      |
| relative Jacobi mixed resummation             | open                         |
| Gate 3U and RH                                 | unproved                     |
+------------------------------------------------+------------------------------+
```

The new ownership flow is

```text
moving Sonin first jet
  =static Toeplitz coefficient
   -compressed Toeplitz product
  -> Proof 276 controls only the first line
  -> compressed covariance remains.                       (AN.1)
```

## 2. Exact Toeplitz identity

Let `J` be an orthogonal projection and let `W,H` be commuting self-adjoint
multipliers.  On `Ran(J)` define

```text
T_W^J=J W J|_(Ran(J)),
T_H^J=J H J|_(Ran(J)),
T_(WH)^J=J W H J|_(Ran(J)).                          (AN.2)
```

Proof 253's extended Dirichlet pairing is

```text
D_J(W,H)=Tr([W,J]* [H,J]).                            (AN.3)
```

Under Proof 261's completed fixed-`S` trace-legality contract, expand the two
commutators and cycle only trace-class products:

```text
D_J(W,H)
 =2 Tr_(Ran(J))(T_(WH)^J-T_W^J T_H^J).                (AN.4)
```

Equivalently,

```text
D_J(W,H)
 =2 Tr(J W(I-J)H J).                                 (AN.5)
```

Equation `(AN.5)` is the completed boundary crossing from Proof 275.  Equation
`(AN.4)` identifies its Toeplitz covariance owner.

For the route, take

```text
J=R,
W=M_w,  w=|g_hat|^2,
H=M_(h_z),                                             (AN.6)
```

where `h_z` is the scalar-free translation mode at displacement `z`.  Up to
the fixed real-orientation convention, Proof 275's `q_R(z;g)` is `(AN.3)`.

## 3. What Proof 276 controls

The first trace in `(AN.4)` is static:

```text
Tr(T_(w h_z)^R)=Tr(M_(w h_z)R).                       (AN.7)
```

On the source CC20 carrier, the Sonin trace identity in Proof 276 owns this
coefficient as the sum of the regular `W_infinity` term and `epsilon`; both
have the half-power tail.  Multiplication by the compact-root symbol `w` becomes
convolution with its compactly supported cross-correlation in the logarithmic
displacement variable.  If `supp(F_g) subset [-2B_root,2B_root]`, Proof 276
Proof 276 `(AM.13c)` gives for `z>2B_root+log 2`

```text
|Tr(T_(w h_z)^R)|
 <=C exp(B_root)(1+z+B_root)
   exp(-z/2)norm(F_g)_1.                              (AN.8)
```

Indeed every shifted argument `z-u`, `|u|<=2B_root`, stays in the CC20 tail,
and

```text
exp(-(z-u)/2)<=exp(B_root)exp(-z/2).                  (AN.9)
```

The displayed `exp(B_root)` is not a polynomial support cost and cannot be
absorbed into Gate 3U's desired bound.  Proof 276 proves the displacement
half-power for every fixed support window; it does not close the uniform
support-width ledger.  A valid successor must use the exact location before
the absolute value, rather than the supremum over all `|u|<=2B_root` used in
`(AN.9)`.

## 4. The compressed term is genuinely new

The second trace is

```text
Tr(T_w^R T_(h_z)^R)=Tr(R W R H R).                    (AN.10)
```

It depends on the two-point Sonin projection kernel.  It is exactly the term
which turns the static coefficient into Proof 253's double-difference energy.
Neither the pointwise tail of `epsilon` nor the scalar identity `(AM.7)`
controls `(AN.10)`.

The companion guard makes this failure finite and exact.  On `C^3`, let `J`
project onto the uniform vector and take the commuting diagonal multipliers

```text
W=diag(1,1,2)>0,
H=diag(1,1,-1).                                       (AN.11)
```

Then

```text
Tr(T_(WH)^J)=0,
Tr(T_W^J T_H^J)=4/9,
D_J(W,H)=-8/9.                                       (AN.12)
```

Thus even a zero static product trace with a strictly positive detector can
leave a nonzero Toeplitz covariance.  The guard does not model CC20 geometry;
it proves that a source-specific estimate of `(AN.10)` is logically necessary.

## 5. Correct one-prime target

Combining Proof 275 `(AL.11)` with `(AN.4)`, the exact one-prime theorem is

```text
|Tr(T_(w h_z)^R-T_w^R T_(h_z)^R)|
 <=C(1+z)^(2d)exp(-z/2)norm(g)_(H^r)^2.              (AN.13)
```

Proof 276 supplies only the fixed-support displacement exponent for the first
term.  The active source bottom must also retain polynomial support cost.  It
is either

```text
a direct exp(-z/2) estimate for the compressed product (AN.10) together with
a location-aware polynomial support bound for (AN.7),

or a same-object cancellation estimate for the whole covariance (AN.13).
                                                                    (AN.14)
```

The second form is safer because Proofs 258 and 273 forbid separate physical
branch norms.  A proof of `(AN.10)` may be used only if it retains the complete
CC20 `E/E_hat/K_prol` identity.

## 6. Determinant connection

Toeplitz semicommutators are the infinitesimal objects naturally generated by
the relative Jacobi cocycle in Proof 267.  Equation `(AN.4)` explains why the
static CC20 trace and the central compressed covariance must appear together
when that determinant is differentiated.

This does not authorize an ambient strong Szego or BOGC theorem.  The whole
Euler multiplier is not identity plus trace class, and Proof 264's trace
anomaly remains active.  The legal owner is still the source-specific relative
determinant followed by Proof 273's renewal.

## 7. Reproduction

Run in WSL2:

```text
python3 -B docs/proofs/277_sonin_toeplitz_covariance_reduction_probe.py

python3 -B docs/proofs/277_sonin_toeplitz_covariance_reduction_probe.py \
  --ambient-size 30 --rank 11 --seed 2277
```

The random layer checks `(AN.4)--(AN.5)` for commuting multipliers and a
non-coordinate projection.  The deterministic three-point layer checks
`(AN.11)--(AN.12)`.  Finite matrices certify the algebra and the ownership
guard, not the CC20 half-power estimate `(AN.13)`.

## 8. Route judgment

Proof 277 identifies the missing one-prime object as a Toeplitz covariance,
not a raw static Sonin coefficient.  Proof 276 supplies the correct
displacement exponent for one side at fixed support.  Its polynomial
support-width cost and the compressed side both remain open.

The active Gate 3U sequence is

```text
prove the complete Sonin Toeplitz covariance bound (AN.13)
  -> insert it into the signed first-missing scalar of Proof 273
  -> keep distinct-prime terms inside the relative Jacobi determinant
  -> apply compact-support stopping before one absolute value.          (AN.15)
```

The finite-S sign, arithmetic same-object trace identity, negative-owner
integration, Burnol's identity, and RH remain open.  No Lean owner or route
rewire is authorized.
