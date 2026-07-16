# Proof 322: support-first moving Euler owner

## Result

The result is positive but does not close Gate 3U.

This batch replaces the rejected termwise displacement truncation with an
exact support-first moving-projection owner.  It also constructs the genuine
parameterized CCM24 Euler product, inverse, prime-power generator series, and
same-object right logarithmic generator on the common-log `L²` carrier.

The remaining theorem is analytic: identify the continuous moving
outer/Sonin projections with this owner and bound their completed signed
kernel uniformly in the visible finite set.

## 1. Why the previous truncation cannot be used

The Proof 321 atom has the form

```text
U_left P_transported-Sonin U_right.
```

The middle orthogonal projection is not translation invariant.  Therefore
compact support of the detector does not allow the two translations to be
merged and truncated by their total displacement.

The legal order is instead

```text
compact cross-correlation
  -> moving projection trace
  -> complete signed E-R two-point kernel
  -> complete synchronized generator
  -> one real part / absolute value last.
```

## 2. Finite support-first covariance

`CCM24FiniteSSupportFirstCovariance.lean` defines

```text
S_m(w,h)=sum_(x,y) w(x)(h(x)-h(y))m(x,y)
```

and proves, for symmetric kernel mass,

```text
S_m(w,h)
 =1/2 sum_(x,y)
   (w(x)-w(y))(h(x)-h(y))m(x,y).
```

`CCM24FiniteSProjectionKernelCovariance.lean` and
`CCM24FiniteSMatrixCovariance.lean` identify this scalar with the literal
finite matrix trace

```text
Tr(P W (I-P) H P).
```

`CCM24FiniteSSynchronizedCovariance.lean` then keeps the complete generator
inside the signed outer-minus-Sonin response.  Compact correlation support is
applied before the channel sum is separated.

## 3. Moving projection derivative

`CCM24FiniteSMovingProjectionCovariance.lean` constructs the finite
orthogonal-projection derivative

```text
P'=(I-P) X P+P X^dagger (I-P)
```

and proves for a Hermitian diagonal detector

```text
Tr(W P')=2 Re Tr(P W (I-P) X P).
```

Consequently, `CCM24FiniteSMovingSupportFirst.lean` proves the ordered owner

```text
Tr(W(E'-R'))
 =2 Re sum_(u in support(F)) F(u)
      sum_channel [S_E(character_u,h_channel)
                   -S_R(character_u,h_channel)].
```

Neither inner sum is placed under an absolute value.

## 4. Completed Sonin kernel

For the exact CC20 identity

```text
R=E Q E-K_prol,
```

`CCM24FiniteSCompletedSoninKernel.lean` expands the complete kernel mass as

```text
|E|^2
-|E Q E|^2
+conjugate(E Q E) K_prol
+conjugate(K_prol) E Q E
-|K_prol|^2.
```

The two interference terms and the prolate square remain in the same kernel.
This prevents the invalid preliminary deletion of `K_prol` and preserves the
cancellation guarded by Proof 258.

## 5. Genuine parameterized Euler generator

On the actual common-log carrier, put

```text
A_p=p^(-1/2) U_(-log p),
T_p(alpha)=I-alpha A_p.
```

`CCM24FiniteSParameterizedEulerGenerator.lean` constructs

```text
T_p(alpha)^(-1)=sum_(n>=0)(alpha A_p)^n,
X_p(alpha)=-A_p T_p(alpha)^(-1),
X_p(alpha)T_p(alpha)=-A_p.
```

Every generator mode has the exact source readback

```text
-alpha^(m-1) p^(-m/2) U_(-m log p),  m>=1.
```

`CCM24FiniteSGeneratorTranslationSeries.lean` legally evaluates the
operator-norm series on `L²` vectors and assembles the finite signed prime sum.

## 6. Same-object complete product

`CCM24FiniteSParameterizedEulerProduct.lean` constructs

```text
T_S(alpha)=product_(p in S) T_p(alpha),
T_S(alpha)^(-1)=reverse product of the one-prime inverses,
D_S(alpha)=the recursive product-rule derivative,
X_S^right(alpha)=D_S(alpha)T_S(alpha)^(-1).
```

It proves both inverse identities and

```text
X_S^right(alpha) T_S(alpha)=D_S(alpha).
```

The endpoint is not a surrogate:

```text
T_S(1)=ccm24FiniteEulerTransportEquiv(S).toContinuousLinearMap.
```

## 7. Verification

The WSL2 commands were

```text
lake build ConnesWeilRH.Source.CCM25Concrete \
  ConnesWeilRH.Dev.CCM24FiniteSSupportFirstMovingAudit

lake build
```

Results:

```text
aggregate + audit: 3615 jobs
full build:         3699 jobs
audited axioms:     [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, stored route premise, or new axiom was introduced.

## 8. Remaining bottom

Proof 322 does not prove any of the following:

```text
X_S^right(alpha)=sum_(p in S) X_p(alpha)
  for the actual commuting translation factors;

the continuous moving E_alpha/R_alpha projection derivative and
root-sandwiched trace-class identity;

a uniform-in-S bound for the completed
outer/second-support/prolate two-point kernel;

Gate 3U, the finite-S sign, Burnol's identity, or RH.
```

The immediate successor is the continuous commutation theorem identifying
the same-object right generator with the additive prime-power translation
series, followed by the actual moving Sonin projection bridge.  Only after
those identifications may the support-first completed kernel be used in the
uniform Gate 3U estimate.
