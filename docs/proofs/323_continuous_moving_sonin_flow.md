# Proof 323: continuous moving Sonin flow

## Result

The result is positive but does not close Gate 3U.

This batch replaces Proof 322's finite-matrix moving projection surrogate by
the actual infinite-dimensional Gram-corrected Sonin projection on the common
logarithmic Hilbert carrier. It proves its operator-norm derivative, aligns the
zero and one endpoints with the existing source and finite-S bands, and
recombines the complete outer/second-support/prolate crossing before root
smoothing.

The remaining bottom is analytic: prove trace-class legality for the actual
oriented crossing from the real-line compact-support geometry and then prove
the resulting signed scalar estimate uniformly in the visible finite set.

## 1. Same-object Euler generator

For the actual ordered product

```text
T_S(alpha)=product_(p in S)(I-alpha A_p),
A_p=p^(-1/2) U_(-log p),
```

the commuting-factor calculation now proves

```text
T_S'(alpha) T_S(alpha)^(-1)
  =sum_(p in S) -A_p(I-alpha A_p)^(-1).
```

Thus the right logarithmic derivative is the genuine additive prime-power
translation generator constructed in Proof 322. It is not an independently
chosen channel family.

## 2. Actual moving Sonin projection

On the fixed source Sonin subtype, define the rectangular frame and Gram
operator

```text
A_alpha=T_S(alpha)|Sonin_0,
G_alpha=A_alpha^dagger A_alpha.
```

The new calculus proves operator-norm derivatives for `A_alpha`, its adjoint,
`G_alpha`, and the canonical ring inverse. The ring inverse is identified with
Proof 316's exact Gram inverse. Therefore

```text
R_alpha=A_alpha G_alpha^(-1) A_alpha^dagger
```

is the actual orthogonal projection onto the moving Sonin intersection, and

```text
R_alpha'
 =(I-R_alpha) X_S(alpha) R_alpha
  +R_alpha X_S(alpha)^dagger (I-R_alpha).
```

The oblique similarity `T_S R_0 T_S^(-1)` is used only as an algebraic ledger
and is never identified with this orthogonal projection.

## 3. Root-sandwiched response

For the selected convolution root `C`, put

```text
L_alpha=C(I-R_alpha)X_S(alpha)R_alpha C^dagger.
```

The completed derivative is exactly

```text
C R_alpha' C^dagger=L_alpha+L_alpha^dagger.
```

Consequently, for any named Hilbert basis, an explicit proof that `L_alpha`
has a summable diagonal gives

```text
Tr(C R_alpha' C^dagger)=2 Re Tr(L_alpha).
```

This is a legal infinite-dimensional consumer, not a trace-class producer.
The theorem keeps the `IsTraceClassAlong` witness explicit; this batch does
not prove that witness for the actual moving crossing.

## 4. Endpoint alignment

At `alpha=0`, every Euler factor is the identity. The actual bounded
equivalence, Hardy--Titchmarsh involution, Fourier support, Sonin intersection,
and canonical Gram projection all return to their source owners.

At `alpha=1`, the path returns to the existing finite-S CCM24 owners. Hence

```text
C[(E-R_1)-(E-R_0)]C^dagger
```

is definitionally the existing `rootSandwichedBandResponse` attached to the
same `FinitePrimePowerFamily`. No second visible-prime list is introduced.

## 5. Completed five-branch crossing

With

```text
A_alpha=E Q_alpha E,
R_alpha=A_alpha-K_alpha,
```

the signed oriented crossing is proved equal to the single recombined owner

```text
(I-E)X E
 -(I-A_alpha)X A_alpha
 +(I-A_alpha)X K_alpha
 -K_alpha X A_alpha
 +K_alpha X K_alpha.
```

These are the outer, compressed second-support, two prolate interference, and
prolate-square branches. Root sandwiching occurs only after this equality.
No branchwise absolute value or preliminary deletion of `K_alpha` is used.

## 6. Verification

The WSL2 commands were

```text
lake build ConnesWeilRH.Source.CCM25Concrete
lake build
lake build ConnesWeilRH.Dev.CCM24FiniteSContinuousMovingAudit
```

Results:

```text
CCM25 aggregate: 3634 jobs
full build:       3719 jobs
focused audit:    3208 jobs
audited axioms:   [propext, Classical.choice, Quot.sound]
```

The new modules contain no `sorry`, `admit`, `sorryAx`, stored route premise,
or new axiom.

## 7. Remaining bottom

Proof 323 does not prove any of the following:

```text
trace-class legality of the actual oriented moving crossing;
trace-norm continuity needed to integrate the scalar trace path;
the compact-support bound for the recombined five-branch owner uniformly in S;
Gate 3U, the finite-S sign, Burnol's identity, or RH.
```

The immediate successor is a real-line kernel factorization of the complete
root-smoothed crossing. It must use compact correlation support before any
absolute value and retain the five-branch cancellation through the estimate.
