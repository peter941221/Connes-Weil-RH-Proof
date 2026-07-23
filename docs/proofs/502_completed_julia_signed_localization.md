# Proof 502: completed Julia signed localization

## 1. Result

The result is good for localizing the polar part and for isolating the exact
remaining source theorem.  It does not close Gate 3U or RH.

```text
+------------------------------------------------------+------------------+
| item                                                 | status           |
+------------------------------------------------------+------------------+
| local first-jet contribution                         | explicit         |
| local route endpoint defect                          | explicit         |
| local polar contribution sign                        | fixed            |
| polar contribution through actual left co-defect     | proved           |
| route/polar ordering residual                        | explicit         |
| full three-term local raw decomposition              | proved           |
| full-list ordering-defect recurrence                 | proved           |
| non-polar gap through the same Julia co-defect        | still open       |
| family-uniform square-energy bound                   | still open       |
| Gate 3U / finite-S sign / Burnol identity / RH       | still open       |
+------------------------------------------------------+------------------+
```

The new Lean owner is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaSignedLocalization.lean
```

## 2. Why the sign matters

Let

```text
F_(p,S)=suffixEulerFrameTransition(lambda,p,S),
R_(p,S)=suffixEulerFrameReverseTransition(lambda,p,S),
rho_p=primeSchurMarkovScalar(p).
```

The unscaled route endpoint increment is

```text
RouteEndpoint(p,S)
 =rho_p Endpoint(p::S)-F_(p,S) Endpoint(S) R_(p,S).
```

The existing local relative numerator has the opposite endpoint orientation:

```text
RelativeNumerator(p,S)
 =F_(p,S) PolarCompression(S) R_(p,S)
   -rho_p PolarCompression(p::S).
```

The polar term occurring in the completed raw response is therefore

```text
PolarJulia(p,S)=-RelativeNumerator(p,S).
```

Using the wrong sign would reverse the contribution in the corrected signed
cocycle.  Lean fixes the sign in

```text
suffixActualBandLocalPolarJuliaContribution
```

and proves the complete decomposition rather than relying on a naming
convention.

## 3. Exact local decomposition

Proof 502 defines

```text
FirstJet(p,S)
 =rho_p FirstJetResponse(p::S)
   -F_(p,S) FirstJetResponse(S) R_(p,S),

OrderingResidual(p,S)
 =RelativeNumerator(p,S)-RouteEndpoint(p,S).
```

The raw local defect is exactly

```text
LocalRawDefect(p,S)
 =FirstJet(p,S)+PolarJulia(p,S)+OrderingResidual(p,S).
```

Indeed, the two polar numerators cancel only after all three terms have been
assembled:

```text
FirstJet-RelativeNumerator
  +(RelativeNumerator-RouteEndpoint)
 =FirstJet-RouteEndpoint.
```

Lean ownership:

```text
suffixActualBandLocalFirstJetContribution
suffixActualBandLocalRouteEndpointDefect
suffixActualBandLocalPolarJuliaContribution
suffixActualBandLocalRoutePolarOrderingResidual
suffixActualBandLocalRawDefect_eq_signedLocalization
```

## 4. Actual Julia localization

Proof 501 proved the boundary identity

```text
BoundaryDefect(p,S)
 =-LeftCoDefect(p,S) Factor(p,S)^dagger Detector NewFrame(S).
```

Proof 502 also retains the reverse transition.  Because

```text
RelativeNumerator(p,S)=BoundaryDefect(p,S) R_(p,S),
```

the signed polar contribution is

```text
PolarJulia(p,S)
 =LeftCoDefect(p,S)
    Factor(p,S)^dagger Detector NewFrame(S) R_(p,S).
```

This is a real defect-localized factorization, not the generic
`A T A^dagger` lift used for the full raw defect in Proof 501.

Lean ownership:

```text
suffixActualBandLocalPolarJuliaRightFactor
suffixActualBandLocalPolarJuliaContribution_eq_leftCoDefect
```

## 5. The exact remaining source theorem

The unresolved term is kept whole:

```text
NonpolarGap(p,S)=FirstJet(p,S)+OrderingResidual(p,S).
```

Lean proves

```text
LocalRawDefect(p,S)=PolarJulia(p,S)+NonpolarGap(p,S).
```

For every proposed completion right factor `Q`, it then proves the exact
equivalence

```text
LocalRawDefect
 =LeftCoDefect (PolarJuliaRightFactor+Q)

if and only if

NonpolarGap=LeftCoDefect Q.
```

The declaration is

```text
suffixActualBandLocalRawDefect_eq_leftCoDefect_iff_nonpolarGap
```

This theorem does not postulate or construct `Q`.  It identifies the smallest
missing source-specific statement: the first jet and route/polar ordering
residual must factor together through the same actual Julia defect slot.

## 6. Suffix scaling and global ordering

Let `rho_S=suffixEulerSchurMarkovScalar(S)`.  Lean proves separately that

```text
LocalFirstJetDefect=rho_S FirstJet,
LocalEndpointDefect=rho_S RouteEndpoint,
ScaledPolarJulia=rho_S PolarJulia,
ScaledOrderingResidual=rho_S OrderingResidual.
```

Consequently the existing local completed defect has the exact scaled split

```text
LocalCompletedDefect
 =LocalFirstJetDefect
   +ScaledPolarJulia
   +ScaledOrderingResidual.
```

The arbitrary-list global ordering owner is

```text
GlobalOrdering(S)
 =RelativeNumeratorProduct(S)-rho_S Endpoint(S).
```

Its one-step recurrence is

```text
GlobalOrdering(p::S)
 =F_(p,S) GlobalOrdering(S) R_(p,S)
   +ScaledOrderingResidual(p,S).
```

On `family.visiblePrimes`, this is exactly identified with the existing
corrected-cocycle term

```text
suffixEulerScaledPolarOrderingDefect(owner,lambda,family).
```

Lean ownership:

```text
suffixActualBandLocalCompletedDefect_eq_scaledSignedLocalization
suffixActualBandRoutePolarOrderingDefect
suffixActualBandRoutePolarOrderingDefect_cons
suffixActualBandEndpointCycledResponse_eq_actual
suffixActualBandRoutePolarOrderingDefect_eq_existing
```

## 7. Gate 3U boundary

The valid implication chain is now

```text
[actual left Julia co-defect]
             |
             +--> polar contribution              proved
             |
             +--> non-polar gap                   open
                       |
                       +--> full local raw defect
                                |
                                +--> chronological synthesis energy
                                         |
                                         +--> unscaled Gate 3U bound
```

The next proof must construct a right factor for `NonpolarGap` using the
actual source first-jet and route-ordering algebra, then assemble those local
right factors in one fixed full-list Julia carrier.  A generic isometric lift
does not meet this contract because it supplies no defect-coordinate energy
gain.

The finite-S sign, negative-owner integration, Burnol identity, and
`_root_.RiemannHypothesis` remain open.

## 8. Verification contract

The focused audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaSignedLocalizationAudit.lean
```

It checks every public definition and prints the axiom set of the principal
identities.  The Ubuntu 24.04 WSL2 acceptance batch is:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 502 focused axiom audit            |  3319 | PASS   |
| CCM25Concrete aggregate                  |  3779 | PASS   |
| full repository                          |  3860 | PASS   |
+------------------------------------------+-------+--------+
```

All twelve audited principal theorems use exactly
`[propext, Classical.choice, Quot.sound]`.  The source and audit contain no
`sorry`, `admit`, or user axiom declaration, have no line longer than 100
characters, and emit no new linter warning.  The Windows sources and WSL2
verification copies are byte-identical.  The WSL localhost-proxy notice is
external to the repository.
