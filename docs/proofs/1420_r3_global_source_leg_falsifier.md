# 1420 — R3-F0: global source-leg trace-class falsifier

Date: 2026-09-14.

Status: **OPEN, first structural gate**. This record starts the R3 attack; it
does not construct `G8SameOwnerReadbackData`, does not add a limit theorem,
and does not claim RH.

Consumer: the healthy-`CompactLog`, B5-shaped same-owner statement
`0 <= C1SameOwnerWeil.qw g` for the detector selected against a hypothetical
off-line zero.

## 1. Exact question

The finite G8 source trace is built from

```text
J† B_n† G_S B_n J,

J   = sourceInclusion lambda,
B_n = fullBoundaryPositiveOperator g (cutoffLower g n) (cutoffUpper g n),
G_S = g8AdjointShearGram owner lambda family.
```

The committed definitions identify the finite cutoff factor on the Schwartz
core with a reflected-window restriction of global convolution by
`g.involution.test`, through
`fullBoundaryRootFactor_eq_globalConvolution`
(`Source/CC20Concrete/CompactRootHalfLinePair.lean:563-581`). Thus the first
apparent limit, if it exists, is a source compression of a global convolution
expression. It is not automatically Hilbert--Schmidt merely because every
`B_n` is.

The first honest falsifier is therefore:

```text
Can the global source leg
    G_S^(1/2) * B_infinity * J
be Hilbert--Schmidt on the named source basis?
```

In the concrete pair language this asks for a summable limiting column energy:

```text
sum_i || G_S^(1/2) * B_infinity * J (sourceBasis i) ||^2 < infinity.
```

Without it, an expanding-window trace may diverge, and no scalar remainder
tending to zero can turn that trace into a finite `qw` readback.

## 2. Source evidence

| fact | evidence | status |
| :-- | :-- | :-- |
| `finiteSCarrier` is `cc20GlobalLogCrossingL2` | `CCM24FiniteSProjectionTrace.lean:73` | FORMAL |
| every finite-window `B_n` has square-summable columns | `C1PositiveTraceWindowProducer.lean:138-154` | FORMAL |
| every finite G8 source trace is trace-class and positive | `C1G8AdjointShearGram.lean:499-577` | FORMAL |
| the source trace is the bounded sandwich `J† B_n† G_S B_n J` | `C1G8AdjointShearGram.lean:521-542` | FORMAL |
| the cutoff factor is a restricted global convolution | `CompactRootHalfLinePair.lean:563-581` | FORMAL |
| `B_infinity` is Hilbert--Schmidt on the source carrier | no declaration found | OPEN |
| the limiting source sandwich is trace-class | no declaration found | OPEN |
| its trace equals `qw` up to a vanishing remainder | `G8SameOwnerReadbackData` remains unconstructed | OPEN |

The finite-window Hilbert--Schmidt proof uses the compact output interval.
When the interval expands, that proof loses its finite-measure factor. The
plain-window predecessor makes the danger exact: its trace is

```text
(cutoffUpper g n - cutoffLower g n) * integral ||g.test x||^2 dx,
```

and is cofinally unbounded for a nonzero test, by
`cutoffPositiveBasisData_trace_re_unbounded_of_test_ne_zero` in
`C1PositiveTraceCutoffGrowth.lean`. This is not yet a no-go for G8, because
`G_S` may smooth or cancel the bulk term. It is a no-go against importing the
plain-window argument unchanged.

## 3. Correct conditional reduction

R3-F0 must first produce a named limiting operator and a genuine domination or
tail estimate. A sufficient contract is:

```text
there exist B_infinity and b : sourceIndex -> Real such that

  Summable b,
  every source diagonal of G8_n converges to the corresponding
    diagonal of G8_infinity,
  every finite diagonal is bounded in norm by b,
  and real(trace(G8_infinity)) is identified with
    qw(owner.sourceTest) + remainder_limit.
```

The generic Tannery theorem already exists in
`C1PositiveTraceTraceContinuity.lean:20-78`; it consumes this kind of
majorant and supplies only trace convergence. It does not produce the
majorant or identify the limit with `qw`.

A stronger sufficient route is a source-basis Hilbert--Schmidt tail:

```text
sum_i ||(B_n - B_infinity) (sourceBasis i)||^2 -> 0.
```

With a fixed bounded G8 middle operator this yields trace convergence through
the Hilbert--Schmidt ideal estimates, after the endpoint comparison is also
supplied. Pointwise strong convergence of interval restrictions is not enough.

## 4. Immediate falsifier and stop rule

The next mathematical test is not a numerical sign test and not a Lean
wrapper. It is the operator question

```text
F0 = prove or refute
     IsTraceClassAlong sourceBasis
       (J† * B_infinity† * G_S * B_infinity * J).
```

The refutation side must exhibit orthonormal source vectors whose G8 diagonal
energies stay above a fixed positive amount, and must connect those vectors to
the finite-window diagonals. Then positive partial traces grow without bound,
ruling out a finite trace limit. The proof side must give an actual summable
source-column majorant or an equivalent trace-ideal theorem.

If the limiting operator is not trace-class, the current ordinary-trace G8
route needs an explicitly positive renormalized trace or must be closed. It
may not be repaired by changing the detector, square, finite-prime family, or
by defining the remainder from the desired `qw` value.

## 5. A proved paper-level obstruction and the only possible escape

There is a simple obstruction before the Sonin compression. Let `k` be a
nonzero compactly supported convolution kernel. Choose a compactly supported
`u` with `k * u` nonzero, and translate `u` by mutually separated amounts.
The translates are an orthonormal sequence after normalization, convolution
commutes with translation, and the output translates remain mutually
orthogonal with the same nonzero norm. Hence the global convolution operator
is not compact, and therefore cannot be Hilbert--Schmidt.

This does **not** close G8: F0 contains the source inclusion `J` and the G8
middle factor, so the source compression could in principle remove the
translation escape. But it identifies the only viable positive route:

```text
the Sonin source carrier must prove an antiresonance theorem that destroys
the translated-column obstruction strongly enough to make
G_S^(1/2) * B_infinity * J Hilbert--Schmidt.
```

This is strictly stronger than pointwise cutoff convergence and is the
operator form of the antiresonant column-energy premise already isolated in
records 1327--1328. Conversely, if the source carrier contains an orthogonal
translated family on which the G8 energy is bounded below, F0 is refuted by
the preceding partial-trace argument.

## 6. R3 status

```text
R3 finite-cutoff algebra               GREEN
R3 finite-cutoff trace positivity      GREEN
R3 global source-leg trace class       OPEN — F0
R3 window-to-global trace convergence   BLOCKED on F0
R3 endpoint-to-qw identification       OPEN after F0
R3 G8SameOwnerReadbackData              NOT CONSTRUCTED
```

This is a sharper target than the former phrase “prove the R3 limit”. It is
analytic source evidence, not a numerical verdict and not a route closure.

RH is not claimed.
