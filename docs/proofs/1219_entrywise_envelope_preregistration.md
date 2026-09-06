# Record 1219 - entrywise envelope discharge of the 20 same-parity facts

Pre-registration.  Committed BEFORE any certificate run of this
campaign (law 42).  Status: REGISTERED, brick E1 in flight.  Consumers:
records 1217 (boxes), 1218 (consumption chain,
`q28_absolute_1218_of_sameParity`).  No P2, no SourceRH, no RH.

## 1. Target

Discharge the named hypothesis of the landed record-1218 chain:

```text
hsp : forall i j : Fin 8, Even (i + j) ->
        MLo_q28M i j <= gateMatrix (classTestFamily 2 htwo) i j /\
          gateMatrix (classTestFamily 2 htwo) i j <= MHi_q28M i j
```

20 independent entries (10 even-even + 10 odd-odd with i <= j;
box widths <= 2.395e-13, record 1217).  Composing with
`q28_absolute_1218_of_sameParity` then closes the whole (2,8)
consumption chain with NO numeric named hypothesis beyond the
representation/normalization slots.

## 2. Structural facts already landed (the attack surface)

```text
C1GateMatrixRepresentation:377  gateMatrix w i j = ICgate (pairTest w i j)
C1LocalConfigurationDomination:73  ICgate F = archimedeanTerm F
                                     + finitePrimeSum F
C1GateMatrixParity:61  (pairTest (classTestFamily a ha) i j).test x
                       = (integral t, W i (-t) * W j (x - t) : real)
C1GateMatrixRepresentation:110  pairTest support <= (-2B, 2B)
C1ClassGramOwner:108  classTestFamily support <= (-a, a)
C1SameOwnerWeil:61  archimedeanTerm = (log 4pi + gamma) * F(0)
                      + (integral y > 0, [e^{y/2}(F(y)+F(-y))
                          - 2 F(0)] / (e^y - e^{-y})).re
C1SameOwnerWeil:36  finitePrimeTerm n = Lambda(n)/sqrt(n)
                      * (F(log n) + F(-log n))
C1SameOwnerWeil:145  globalPrimeIndexSet = finite visible set
```

At a = 2 the pair test is supported in (-4, 4), so the visible prime
powers satisfy |log n| < 4 (n <= 54: exactly the 24 prime powers of the
record-1217 engine) and the archimedean y-integral tail beyond y = 4
reduces to the explicit convergent kernel integral (the record-1217
`log(tanh 2)` folding).

## 3. Bricks

```text
E1  formula brick (Lean, no numerics): pin
      gateMatrix (classTestFamily 2 htwo) i j
        = archimedeanTerm (pairTest ...) + finitePrimeSum (pairTest ...)
    plus the real-correlation readout of the pair test and the
    support bound.  Reduces hsp entrywise to a rational interval
    obligation on the correlation readouts.
E2  correlation envelope: Lean-certified rational intervals for
    C_ij(x) := (pairTest ...).test x at the required readout points
    x = 0, x = log n (24 prime powers), and uniform rational interval
    bounds on x in the quadrature cells of (0, 4) - the 1131-1139
    IntegralEnvelope machinery ported to the two-window correlation
    integrand (partition of (-2, 2), pointwise rational bounds on the
    window product, tail budget).
E3  archimedean enclosure: rational quadrature of the y-integral on
    (0, 4) through the E2 cell intervals + the explicit tail term;
    per-cell error budgets accumulated exactly.
E4  log readouts: rational enclosures of Real.log n for the 24 visible
    prime powers (pow-comparison bisection, width <= 1e-45).
E5  assembly: per-entry interval arithmetic (exact rationals in Lean)
    combining E2/E3/E4; entry interval inside [MLo_q28M i j,
    MHi_q28M i j]; hsp discharged; composition with the 1218 headline.
```

Scale estimate: E2 is the 1131-1139 construction on a 2-parameter
integrand family (~2x); E3/E4/E5 are mechanical given E2.

## 4. Falsifiers

```text
F1  any E2/E3 cell interval or tail budget fails to certify at the
    claimed width -> report the achieved width, ABORTED-UNINFORMATIVE
F2  the assembled entry interval is not inside the 1217 box (the
    quadrature/rounding overhead eats the 2.4e-13 budget) -> report,
    ABORTED-UNINFORMATIVE; the legal recovery is a record-1217 prereg
    amendment and box regeneration (never hand-widening, 1097)
F3  any Lean lemma of E1/E5 fails to build -> shrink the record claim
    to the surviving entries, report
```

## 5. Acceptance

```text
A1  E1 module builds green (no numerics asserted there)
A2  E2/E3/E4 certificates committed with exact generation-time asserts
    BEFORE their Lean consumers (law 42 order: numeric layer first)
A3  E5 builds green; `#print axioms` on the discharged hsp instance
    and the composed chain shows only the approved standard axioms
A4  per-entry margins reported numerically in the verdict record
A5  hygiene scan before push; upstream read-back after
```

RH NOT claimed.
