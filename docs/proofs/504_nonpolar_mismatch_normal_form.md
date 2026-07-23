# Proof 504: non-polar mismatch normal form

## 1. Result

The result is good for combining Proof 502's first jet and Proof 503's
route/polar kernel defect into one actual source-carrier object.  It does not
prove a factorization, a uniform bound, Gate 3U, the finite-S sign, or RH.

```text
+------------------------------------------------------+------------------+
| item                                                 | status           |
+------------------------------------------------------+------------------+
| polar/raw mismatch kernel                            | explicit         |
| mismatch = route/polar kernel - first jet            | proved           |
| non-polar gap as one relative defect                 | proved           |
| full local raw two-term signed readback              | proved           |
| common left-co-defect factorization                  | still open       |
| family-uniform Gate 3U bound                         | still open       |
| finite-S sign / Burnol identity / RH                 | still open       |
+------------------------------------------------------+------------------+
```

The Lean owner is

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaNonpolarMismatchNormalForm.lean
```

## 2. The algebraic cancellation

Proof 502 leaves

```text
NonpolarGap(p,S)
 =FirstJetContribution(p,S)+OrderingResidual(p,S).
```

Proof 503 gives

```text
OrderingResidual(p,S)
 =F_(p,S) RoutePolarKernel(S) R_(p,S)
  -rho_p RoutePolarKernel(p::S).
```

The first-jet contribution has the opposite orientation:

```text
FirstJetContribution(p,S)
 =rho_p FirstJetResponse(p::S)
  -F_(p,S) FirstJetResponse(S) R_(p,S).
```

The two terms therefore combine without taking a norm or a trace.  Define the
actual mismatch on the literal source Sonin carrier by

```text
Mismatch(S)
 =PolarCompression(S)-RawResponse(S).
```

Lean proves the independent route form

```text
Mismatch(S)
 =RoutePolarKernel(S)-FirstJetResponse(S).
```

This is the key invariant: the mismatch is not a newly postulated response;
both sides are built from existing polar, raw, route, and first-jet owners.

## 3. Single-object local defect

Proof 504 defines

```text
MismatchDefect(p,S)
 =F_(p,S) Mismatch(S) R_(p,S)
  -rho_p Mismatch(p::S).
```

The main theorem is

```text
NonpolarGap(p,S)=MismatchDefect(p,S).
```

The full local raw defect consequently has the two-term signed readback

```text
LocalRawDefect(p,S)
 =PolarJulia(p,S)+MismatchDefect(p,S).
```

The polar Julia term remains the actual `leftCoDefect` factor from Proof 502.
The new mismatch defect is deliberately kept whole; no primewise absolute
value, trace interchange, or generic Julia lift is used.

Lean ownership:

```text
suffixActualBandRoutePolarRawMismatchKernel
suffixActualBandRoutePolarRawMismatchKernel_eq_routePolarKernel_sub_firstJet
suffixActualBandLocalRoutePolarRawMismatchDefect
suffixActualBandLocalNonpolarLocalizationGap_eq_routePolarRawMismatchDefect
suffixActualBandLocalRawDefect_eq_polarJulia_add_routePolarRawMismatchDefect
```

## 4. Gate 3U boundary

The active chain is now

```text
[polar Julia defect]
             |
             +--> actual left-co-defect factorization       proved
             |
             +--> [polar compression - raw response]
                       |
                       +--> one synchronized relative defect   proved
                                  |
                                  +--> common left-co-defect
                                      factorization / signed bound  open
```

This removes the invalid temptation to estimate the first jet and ordering
residual independently.  It does not provide the missing source-specific
factorization or the family-independent Gate 3U estimate.

The finite-S sign, negative-owner integration, Burnol identity, and
`_root_.RiemannHypothesis` remain open.

## 5. Verification contract

The focused audit is

```text
ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaNonpolarMismatchNormalFormAudit.lean
```

The audit checks the mismatch bridge, the single-defect localization, and the
two-term raw readback.  Every audited theorem must remain axiom-clean with

```text
[propext, Classical.choice, Quot.sound]
```

The Ubuntu 24.04 WSL2 acceptance batch passed:

```text
+------------------------------------------+-------+--------+
| target                                   | jobs  | result |
+------------------------------------------+-------+--------+
| Proof 504 focused axiom audit            |  3321 | PASS   |
| CCM25Concrete aggregate                  |  3781 | PASS   |
| full repository                           |  3862 | PASS   |
+------------------------------------------+-------+--------+
```

The new source and audit contain no `sorry`, `admit`, or user axiom
declaration, have no line longer than 100 characters, and emit no new linter
warning.  The finite-S sign, Gate 3U, Burnol identity, and RH remain open.
