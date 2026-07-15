# Proof 285: Support-first two-boundary renewal functional

Date: 2026-07-15

Status: exact fixed-`S` trace-functional reduction after Proof 284.  On the
convolution commutant of the causal Euler inverse, the outer,
second-support, and prolate numerator branches recombine into one signed
outer-minus-Sonin boundary kernel.  The compact cross detector then sits
outside that kernel before the common renewal is expanded.

This is not an operator identity for the endpoint projection difference.  It
is not valid for arbitrary noncommuting detectors.  The real-line
first-missing prime disintegration, the extra-half-power estimate, Gate 3U,
the finite-`S` sign, the arithmetic same-object identity, Burnol's identity,
and RH remain open.

## 1. Result

```text
+------------------------------------------------+------------------------------+
| layer                                          | judgment                     |
+------------------------------------------------+------------------------------+
| three physical numerator branches             | exact, Proof 266             |
| second-support plus prolate recombination      | exact                        |
| outer-minus-Sonin boundary functional          | exact on convolution owner   |
| detector outside common renewal                | exact for fixed S            |
| compact-support clip before renewal expansion  | exact at paired-kernel level |
| boundary kernel = endpoint operator difference | false                        |
| extension to noncommuting detectors            | false                        |
| first-missing prime scalar disintegration      | open                         |
| extra half-power, Gate 3U, and RH              | open / unproved              |
+------------------------------------------------+------------------------------+
```

The new owner is

```text
Q_S(eta,xi)
 =Lambda_(eta,xi)(Z_S)
 =sum_(k>=0)Lambda_(eta,xi)(Z_(S,k)),               (AV.1)
```

where `Lambda_(eta,xi)` is the legal factorized cross-root trace functional
and each `Z_(S,k)` retains both physical boundaries.  The support of
`F_(eta,xi)=xi^star*eta` acts on `(AV.1)` before `Delta^k` is split into
missing-channel or prime paths.

## 2. Source notation

Let

```text
R<=E,
B=E-R,
C=I-E,
A=T_S^(-1).                                         (AV.2)
```

Write

```text
iota_B:H_B -> H
```

for the isometric inclusion of `H_B=Ran(B)`, so

```text
iota_B iota_B*=B,
iota_B* iota_B=I_(H_B).                             (AV.3)
```

Define the killed causal frame and its covariance by

```text
K=E A iota_B,
Gamma=K* K,
Delta=I_(H_B)-Gamma.                                (AV.4)
```

For fixed finite `S`, Proof 266 gives

```text
0<Gamma<=I_(H_B),
Gamma^(-1)=sum_(k>=0)Delta^k.                       (AV.5)
```

For compact roots `eta,xi`, put

```text
W=W_(eta,xi)=C_xi* C_eta.                           (AV.6)
```

Both `W` and `W*` commute with `A` and `A*` because all four are whole-line
convolution multipliers.  This commutant premise is part of the result.

## 3. Recombine the physical branches

Proof 266's centered numerator is

```text
N_W=O_W+S_W+P_W,                                    (AV.7)

O_W=-iota_B* A* C[W,E]E A iota_B,

S_W=iota_B*(I-Q)[W,Q]R A*K,

P_W=iota_B*Q W R A*K.                              (AV.8)
```

Because `EK=K`, `CE=0`, and `QR=R`,

```text
C[W,E]K=C W K,

(I-Q)[W,Q]R=(I-Q)W R.                              (AV.9)
```

Therefore the three branches recombine exactly as

```text
N_W
 =-iota_B* A* C W K
   +iota_B* W R A* K.                              (AV.10)
```

Equation `(AV.10)` does not delete the prolate branch.  It adds the
second-support and prolate branches back into the complete Sonin projection
`R` before any estimate.  This is precisely the cancellation required by
Proof 258.

## 4. Extract the detector only inside the trace

Proof 284 gives

```text
Q_S(eta,xi)=Tr_(H_B)(N_W Gamma^(-1)).                (AV.11)
```

Use fixed-`S` trace legality from Proof 261 to cycle the two completed terms
in `(AV.10)`, but do not claim an ambient operator cycle.  Define the signed
boundary renewal kernel

```text
Z_S
 :=R A* K Gamma^(-1)iota_B*
   -K Gamma^(-1)iota_B* A* C.                       (AV.12)
```

Then

```text
Q_S(eta,xi)
 =Lambda_(eta,xi)(Z_S),                             (AV.13)
```

where the notation on the right means the sum of the two root-completed
traces obtained from `(AV.11)`:

```text
Lambda_(eta,xi)(Z_S)
 :=Tr_root(W R A*K Gamma^(-1)iota_B*)
   -Tr_root(W K Gamma^(-1)iota_B*A*C).              (AV.14)
```

The subscript `root` is a reminder that `(AV.14)` is owned by the factorized
trace-class products.  It is not a license to define `Tr(U_z Z_S)` pointwise.

Combining Proofs 283--285 gives

```text
2 integral_0^1 movingBandJet_(eta,xi,alpha) dalpha
 =Tr_(H_B)(C_(L,W)* C_K)
 =Lambda_(eta,xi)(Z_S).                             (AV.15)
```

Thus the moving, causal-column, and support-first boundary coordinates are
three exact representations of the same cross-root response.

## 5. Expand only after the support clip

Insert `(AV.5)` into `(AV.12)` only after the detector has been extracted:

```text
Z_(S,k)
 :=R A* K Delta^k iota_B*
   -K Delta^k iota_B* A* C,

Lambda_(eta,xi)(Z_S)
 =sum_(k>=0)Lambda_(eta,xi)(Z_(S,k)).                (AV.16)
```

Each summand in `(AV.16)` is one signed two-boundary scalar.  The two terms
must not receive separate absolute values.

The detector is convolution by

```text
F_(eta,xi)=xi^star*eta,

supp(F_(eta,xi)) subset [-2B_root,2B_root].          (AV.17)
```

At the paired-kernel level, `(AV.17)` removes every matrix/kernel coefficient
whose relative displacement exceeds `2B_root`.  The allowed order is

```text
three branches recombine into Z_(S,k)
  -> pair with F_(eta,xi)
  -> clip |x-y|>2B_root
  -> factor Delta through actual missing channels
  -> expose the first unmatched prime displacement
  -> one absolute value after the full signed sum.             (AV.18)
```

This is the support-first order requested by Proofs 273 and 284.  It avoids
both a positive left-column norm and a prime-path expansion of an unclipped
operator.

## 6. Why this is not an operator identity

Let

```text
P_K=K Gamma^(-1)K*                                  (AV.19)
```

be the transported band projection.  The endpoint response is also

```text
Q_S(eta,xi)=Tr_root(W(P_K-B)).                       (AV.20)
```

Equations `(AV.13)` and `(AV.20)` do not imply

```text
Z_S=P_K-B.                                          (AV.21)
```

They prove only that the two operators define the same completed trace
functional on the route's convolution commutant.  A detector that does not
commute with `A` sees their difference.

This distinction is useful rather than cosmetic.  `P_K-B` hides both source
boundaries inside an orthogonal projection difference.  `Z_S` exposes them,
but only after using the special Euler/detector commutation.  Promoting
`(AV.13)` to `(AV.21)` would discard exactly that source input.

## 7. Positive kernel norms remain forbidden

Compact support controls the scalar pairing, not the size of the discarded
kernel.  In the default certificate, clipping the boundary kernel outside the
detector band leaves the response unchanged to machine precision, while the
discarded part has Frobenius mass

```text
0.180887...
```

The alternate cohort gives

```text
0.193519....                                         (AV.22)
```

Thus neither

```text
norm(Z_S-Z_S^clipped)
```

nor the sum of the two boundary norms can represent the support cancellation.
This is the same mechanism as Proof 260's zero-trace/positive-nuclear-mass
guard, now inside the complete renewal owner.

## 8. Finite certificate

The companion probe uses zero-extension convolutions of two distinct compact
roots.  Their cross detector is non-Hermitian, has displacement radius
`2B_root`, and commutes exactly with the repeated causal Jordan factor.

The default cohort (`multiplicity=10`, `root-radius=2`, `seed=285`) reports

```text
maximum exact error                  5.58e-16,
boundary-kernel/operator gap         2.03e-1,
discarded kernel mass                1.81e-1,
noncommuting trace-functional gap    2.02e-2.
```

The alternate cohort (`multiplicity=12`, `root-radius=2`, `seed=2285`)
reports

```text
maximum exact error                  9.34e-16,
boundary-kernel/operator gap         2.23e-1,
discarded kernel mass                1.94e-1,
noncommuting trace-functional gap    1.77e-2.          (AV.23)
```

Both responses have nonzero real and imaginary parts.  The probe checks the
support clip separately at every renewal level.  It also uses a full random
detector to reject `(AV.21)` and the noncommuting extension.  These are finite
algebra and support certificates, not the continuous extra-half-power bound.

A deterministic cancellation guard (`multiplicity=10`, `root-radius=2`,
`seed=408`) has complete response magnitude `9.03e-4`.  Taking absolute
values after each completed renewal term costs

```text
3.09845 times the final response,
```

while also separating the outer and Sonin boundary terms costs

```text
20.8263 times the final response.                            (AV.24)
```

The maximum exact-algebra error remains `6.03e-16`.  This is a finite guard,
not a continuous lower bound, but it rejects both termwise absolute-value
orders as candidate proofs.

## 9. Active analytic target

Proof 285 moves the support clip to the correct side of the renewal, but it
does not yet identify the first unmatched prime scalar.  The next theorem
must start from the already clipped functional in `(AV.16)` and then use

```text
Delta=I_rand*I_rand+I_C*I_C                         (AV.25)
```

from Proof 271.  Only after the `2B_root` clip may `I_rand` be split into its
orthogonal Doob prime channels.  Equal causal translation histories on the
two legs must be canceled before the local geometric mode is read.

The required output is a signed scalar coefficient

```text
Phi_(S,p,m)(z;eta,xi)                               (AV.26)
```

that includes both terms of `Z_(S,k)`, every renewal level, and the complete
second-support/prolate recombination.  It must vanish outside the relative
support window and earn the extra `p^(-m/2)` required by Proof 274 `(AK.12)`.

No total-variation measure, branch norm, renewal-term absolute sum, or raw
point trace is an acceptable substitute for `(AV.26)`.

## 10. Reproduction

Run from the repository root:

```text
python3 -B docs/proofs/285_support_first_boundary_renewal_probe.py

python3 -B docs/proofs/285_support_first_boundary_renewal_probe.py \
  --multiplicity 12 --root-radius 2 --seed 2285

python3 -B docs/proofs/285_support_first_boundary_renewal_probe.py \
  --seed 408
```

Both runs report

```text
three_branch_to_two_boundary_recombination=EXACT,
detector_extraction_on_convolution_commutant=EXACT,
compact_support_before_renewal_expansion=EXACT,
boundary_kernel_operator_identity=FALSE,
noncommuting_detector_extension=REJECTED,
positive_kernel_norm_estimate=REJECTED,
first_missing_prime_scalar_disintegration=OPEN,
complete_signed_extra_half_power=OPEN,
gate_3u=OPEN,
RH=UNPROVED.
```

## 11. Route judgment

Proof 285 makes one structural advance: compact support now appears before the
renewal/prime path expansion without taking a positive operator norm.  It does
so by exploiting the exact convolution commutant and retaining the complete
outer-minus-Sonin boundary functional.

The next attack is

```text
support-clipped Z_(S,k)
  -> actual missing-channel factorization of Delta
  -> pair equal causal histories before expansion
  -> first unmatched prime/mode scalar
  -> determinant-resummed mixed-channel cancellation
  -> extra half-power (AK.12)
  -> Gate 3U.                                             (AV.27)
```

The first-missing scalar theorem, the uniform bound, finite-`S` sign,
arithmetic same-object trace identity, negative-owner integration, Burnol's
all-zero identity, and RH remain open.  No Lean owner or route consumer is
changed.

## 12. Successor audit

Proof 286 factors each nonzero `Z_(S,k)` through Proof 271's actual missing
channels after the support-first step.  For the complete two-boundary reward
`H_(S,k)(W)`, it proves

```text
Lambda_W(Z_(S,k))
 =Tr(M_C H_(S,k)(W)M_C*)
  +sum_p Tr(M_p H_(S,k)(W)M_p*).
```

Inside a prime channel the common Doob past disappears by unitary trace
conjugacy, while `A_>p` remains.  The centered local geometric innovation is
the signed relative-mode identity

```text
1/2 sum_(r in Z)
  [(1-a_p)/(1+a_p)]a_p^|r|
  Tr((U_(r log p)-I)Y(U_(r log p)-I)*).
```

This exposes one route-owned Euler coefficient and makes the missing second
half-power a bound on one named real-line two-boundary second difference.
Termwise relative-mode absolute values remain forbidden.  See
`docs/proofs/286_first_missing_relative_mode.md`.
