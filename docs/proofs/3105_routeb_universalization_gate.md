# Route-B universalization gate: fixed row-B caps are local (3105)

Date: 2026-10-25.

This record closes the first half of Gate U. A fixed compact-log owner with
fixed support radius and fixed first derivative L1 budget cannot supply unit
Laplace targets at arbitrarily large heights inside a fixed real strip.

At the row-B strip scale `|Re(s)| <= 1`, the reusable theorem is:

```text
|Im(s)| <= exp(B) * derivOrderL1(1,f)
```

whenever `support(f) ⊆ [-B,B]` and `|laplaceAt(f,s)| >= 1`. The companion
no-go rejects a universal fixed-owner statement over all heights.

For an actual `OrbitG8Geometry`, the same owner-specific cost is exposed as:

```text
|Im(rho)| <= exp(|Re(rho)-1/2| * L) * derivOrderL1(1,g)

1 / (L * exp(L) * |Re(rho)-1/2|)
    <= l1Mass(orbitRawFactor geometry)

L = orbitIndex + 2
```

The first inequality is the height cost. The second is the inverse-gap cost
from the two opposite interpolation values `1` and `-1`. The terms are
necessary costs for a rho-dependent detector; they do not assert that any
off-line zero exists.

The formal consequence is a routing decision:

```text
fixed row-B owner and fixed caps
              |
              +--> cannot cover arbitrary heights      CLOSED
              |
              v
rho-dependent owner / support / derivative budget      REQUIRED
              |
              +--> must also pay inverse-gap mass      REQUIRED
```

The module does not claim that the parameterized route succeeds. Its purpose
is to prevent silently applying the stored `hNorm`/`hIm` caps to every
hypothetical zero. Cardinal pins, `hgate24`, `htarget`, `hzero`, `SourceRH`
and RH remain open.

The paired Lean audit has five declarations, no errors or `sorryAx`, and the
standard axiom trio only.
