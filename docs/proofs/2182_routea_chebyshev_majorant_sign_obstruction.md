# 2182 — Route A Chebyshev majorant sign obstruction

Date: 2026-09-29  
Status: scoped no-go for the unsigned Chebyshev shortcut; the same-owner
signed C3′ producer remains open.

## Consumer and exact owner

The consumer is unchanged:

```text
same selected healthy CompactLog owner g
  -> qw(g) >= 0
  -> SourceRH
  -> Mathlib RH.
```

The owner is an `OrbitG8Geometry rho g` with its actual support-derived
visible-prime range. No ROOT-support test, fixed-prime model, or narrow-root
surrogate is used in this screen.

## Audited mechanism

`C1P2DirectChebyshevSharpenedDecoupling.lean` proves, for the exact owner,

```text
finitePrimeSum g.convolutionSquare
  <= visibleChebyshevPrimeSum geometry
       * orbitChebyshevSharpenedBound geometry,
```

and the right-hand side is nonnegative. Its SourceRH theorem therefore still
requires the producer premise

```text
visibleChebyshevPrimeSum geometry
  * orbitChebyshevSharpenedBound geometry
  <= -archimedeanTerm g.convolutionSquare.
```

The sharpened factor only improves the magnitude of an unsigned majorant; it
does not preserve the signed cancellation in the physical prime aggregate.

## Obstruction

The existing healthy-owner package gives positivity of the local Weil square,
but the theorem converting that positivity into
`archimedeanTerm > 0` requires the additional ROOT-support hypothesis
`support(g.convolutionSquare.test) ⊆ (-log 2, log 2)`. The actual selected
owner is only known to have its parameterized support bound and triple
vanishing. Hence that theorem cannot be applied to the selected owner.

Conversely, the Chebyshev majorant can close only on a branch where the
selected owner's Archimedean term is already nonpositive with enough margin.
No such same-owner theorem or certified margin is present. Replacing the
owner by the ROOT-support object would change the B5 consumer and is
inadmissible.

Decision:

```text
SCOPED-NO-GO-CHEBYSHEV-UNSIGNED-SHORTCUT
```

This rules out the unsigned Chebyshev/absolute-value shortcut as the missing
producer under the current owner hypotheses. It does not rule out the direct
signed physical-kernel/C3′ certificate, in particular the retained
owner-preserving weighted-zero-measure candidate A.005.1.

No Route-A producer GO and no RH conclusion are claimed.

