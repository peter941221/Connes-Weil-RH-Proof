# Record 2013 - desk: the certified-evaluation layer, priced for its three consumers

Date: 2026-09-26.

Status: desk record. No Lean brick, no rig run, no theorem proved, no RH
claim. This prices the cross-cutting brick that three separate live lanes
consume, and fixes the order in which its parts must be built. It changes no
route ruling and no obligation.

## 1. Why one brick serves three lanes

Three committed records ask for the same missing object from three directions.

```text
record 1985   D was replicated at the registered point to 12 stable digits
              (D = -1073742.85377) but `cert_ok = FALSE` on conditions (ii)
              and (iii): the dxi ladder shows arithmetic dregs (~1e-18) rather
              than a convergence signal, and the [8,24] annulus measured the
              quadrature ALIASING FLOOR of W (Delta = 2.54e18, W(35.18) =
              3.8e4 where the true transform decays superfast). The value is
              right; the error certificate is missing.

record 1997   the F2 un-gating bridge needs a rig measurement of the owner
              window's tail decay below that same aliasing floor, plus an
              owner-window derivative ladder with explicit constants.

record 2010   the health witness is the residual of a cancellation of order
              f = mm / A (f = 7196 / 86087 / 133 / 51 at the four registered
              owners), so certifying C > 0 needs a relative accuracy of order
              1 / (1 + f) on the signed masses.
```

All three need the same thing: **a bound on the difference between the rig's
finite-grid functional and the functional it is standing in for, with an
explicit constant, on the same owner and the same finite visible-prime set.**

## 2. The cancellation arithmetic, stated exactly

The record-1919 readout writes the gate entries as moments of one signed
measure `mu = K * W * dxi`:

```text
C = A = sum(mu) = mp + mm,        |mm| / |A| = f  (for A > 0)
```

If each mass is evaluated with relative accuracy `eps`, the induced absolute
error on `A` is `eps * (|mp| + |mm|) = eps * (1 + f) * |A|`, so

```text
C > 0 is certified as soon as        eps  <  1 / (1 + f).
```

Registered values at the four 2010 owners, with `1 / (1 + f)` and the plain
`1 / f` reading:

```text
owner   f = mm / A      1 / (1 + f)     1 / f
G5-H    7.1963e+03      1.3893e-04      1.3896e-04
G5-W    8.6087e+04      1.1616e-05      1.1616e-05
G7-H    1.3280e+02      7.5264e-03      7.5301e-03
G8-H    5.1246e+01      1.9514e-02      1.9514e-02
```

So a certified health screen at `gamma_5` costs about four and a half digits
more accuracy than at `gamma_8`, and the cost is a property of the owner, not
of the resolution alone. This is the same quantity record 2010 section 4
identified as the route-A numeric exposure, now as a requirement rather than
a diagnosis.

## 3. The three bricks, with consumers and decisions

```text
P1  discretization-error bound  E(dxi)  for the rig density functional
    what      an explicit bound on | <g, K W_rig> - <g, K W_true> | for the
              functionals actually used (g = 1, P, P^2, and the Laplace
              functional of the F2 lane), with the constant carried through
              the committed owner construction (kill pools, widths, pins)
    consumers (a) D interval certificate, (b) F2 tail measurement,
              (c) health-witness certification
    settles   whether a Lean-consumable bracket at the registered point is
              buildable, and at what dxi it closes

P2  mass-split arithmetic  on top of E(dxi)
    what      directed-rounding evaluation of mp, mm with the P1 budget, so
              the certified relative accuracy on the masses is controlled
    consumers (a) D interval certificate, (c) health screen
    settles   at which heights C > 0 is certifiable WITHOUT a new selector:
              G7-H and G8-H need ~1e-2, G5-H ~1.4e-4, G5-W ~1.2e-5

P3  owner-window derivative ladder with explicit constants
    what      the rungs that exist for the family window (records 1986-1988,
              `gevreyInner`) rebuilt for the OWNER's kill-pool windows, whose
              constants are currently unpriced
    consumers (b) only
    settles   whether the F2 domination comparison has constants at
              T_0 ~ 31.88, where the Cut-1 target needs M_n <~ 7.5e-13 at
              lam = 1 and M_n <~ 7.7e-09 at lam+ ~ 70 (record 1997 section 2)
```

Order of construction: `P1 -> P2 -> P3`. `P1` is the root; `P2` is arithmetic
once `P1` exists; `P3` is only needed by the F2 lane and stays gated until the
record-1993 member-versus-domination question is settled by measurement.

## 4. What is NOT missing

```text
value accuracy      already there: 12 stable digits on D (1985), the
                    record-1919 identity reproduced to <= 1.2e-11 on refined
                    grids, dxi-convergence law measured in the float pipeline
binary precision    already there: 30-digit paths exist and are used
                    (record 1985's rig, record 1983's v2 decay probe)
```

What is missing is the *certificate*: a bound, not a precision. The record-1985
failure was not that the number was wrong - it was that the ladder could not
distinguish a converged value from an aliasing floor, so the number could not
be consumed by anything that has to be exact.

## 5. Interaction with records 2011 and 2012

```text
record 2011 (A-HD)      if A-HD-GAIN, the health screen's accuracy demand
                        drops by the attained C ratio, which is a way of
                        paying part of P2's price with selector freedom
                        instead of resolution
record 2012 (COVER)     the width law is read through the sign of C, i.e.
                        through the f-fragile coordinate; the P2 budget is
                        what says whether a pinched C-window is a fact or an
                        artefact, and the registered f-readout of that scan is
                        the first cheap look at the same question
```

Neither of those two records is a substitute for `P1`: they can reduce the
needed accuracy and re-read the window, but they cannot certify a
discretization error.

## 6. Scope

This desk prices; it does not build. No gate sign is proved, no bound is
proved, the binding obligation (`D < 0` on the selected healthy owner) is
unchanged, the F2 gate of record 1993 section 4 stands, and RH is not claimed.

See also: 1981 (live program item 1), 1982 (bracket target ~1e-06 relative),
1985 (the failure conditions), 1986-1988 (family rungs 1-3), 1989/1990
(constant budget c_0 <= 4, c_env in [0.21, 0.59]), 1997 (F2 bridge order),
2010 (the f values), 2011 and 2012 (this date).