# Record 1802 — TailStart quantifier audit: withdraw the 1801b cap

Date: 2026-09-21.

Status: source audit. No Lean theorem, numerical result, signed-budget
estimate, or RH claim is added.

## Result

The ``empty tailStart window`` conclusion of record 1801b is not valid for
the committed `OrbitG8Geometry` constructor and is withdrawn as route
evidence.

The error was a quantifier substitution. Record 1801b imposed an external
Cartwright/Riemann--von Mangoldt capacity estimate on a hand-built surrogate
and treated it as an upper bound on `tailStart`. That upper bound is absent
from the committed construction.

## Committed construction order

`C1G8R0OrbitGeometry.exists_orbitG8Geometry_of_sourceNontrivialZero_right`
contains the relevant order exactly:

```text
1. Obtain base, threshold T, and hconstruction.
2. Obtain tailStart from
   exists_dyadic_tail_start_with_budget_lt_xiMultiplicity T 1 rho.
3. Define
   R = 2^(tailStart + 1) + 2 + dist(2, rho).
4. Invoke hconstruction R hR.
5. Receive correction, orbitIndex, square_zero_control, and raw_square_tail.
```

Source locations:

```text
ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean:162-178
ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean:226-240
```

The supplier `hconstruction` is quantified as follows:

```text
forall R : Real, 0 <= R ->
  exists correction, C, n,
    correction support inside (-1, 1)
    and selected-owner support
    and all requested finite ball zeros
    and fourth-order tail data.
```

Source location:

```text
ConnesWeilRH/Dev/C1HealthyYoshidaUnscaledOrbit.lean:492-504
```

Thus, for every `tailStart` furnished by the tail-budget lemma, the required
finite radius is supplied to the interpolation constructor afterwards. A
separate entire-function zero-counting estimate may study a particular
surrogate family, but cannot reject the already-constructed Lean witness
without deriving a contradiction from its actual fields.

## What remains valid from record 1801

The k=1 gate-matrix collapse is a formal algebraic observation. The numerical
gate readings are diagnostics only for their stated finite interpolation
families. Neither establishes the sign on the constructor-selected correction,
because the rigs did not instantiate its complete ball-zero and fourth-order
tail fields.

## Correct next target

The live B5 consumer is unchanged:

```text
for every right-hand off-line zero rho,
construct OrbitG8Geometry rho g and prove
ICgate(g.convolutionSquare) <= 0.
```

The construction already supplies the geometric and tail legs. The missing
mathematics is a signed estimate for its same-owner finite prime profile. The
next useful analytic work is therefore a readback of the actual correction
construction into that profile, not a width scan based on an uncommitted cap.
