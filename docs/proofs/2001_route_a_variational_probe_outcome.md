# Record 2001 - Route A A-V variational probe outcome

Date: 2026-09-26.

Status: scoped no-go for the pre-registered A-V selector. No Lean theorem,
no producer closure, and no RH claim.

## Verdict

```text
A-V-NO-GO
```

The probe used the actual Route-A EXT owner constructor, two width copies per
owner node, the minimum H1 selector, the registered spectral cutoff, and the
committed three-route gate instrument. It did not replace the owner by a
fixed-prime, ROOT, or continuous surrogate.

## Results

```text
case  C                 D                  det                status
G5-H  -5.026740e+03     -1.787481e+22      +3.649921e+25       fail
G5-W  +7.264329e+02     -4.613574e+21      -7.226417e+24       unresolved pins/rank
G7-H  -7.970373e+02     -7.842632e+21      -1.288589e+24       certified but unhealthy
G8-H  -4.095022e+03     -5.185232e+21      +1.333090e+25       certified but unhealthy
```

The G7 and G8 rows are fully certified by the registered instrument, with
three live routes and finite constraints. Both have C < 0, so the minimum H1
selector leaves the healthy-owner class. G8 also has determinant > 0.

G5-H and G5-W expose numerical conditioning at the registered spectral cutoff:
rank 32/34 and correction pin errors 6.55e-6 and 1.77e-6 respectively. They
cannot be used as positive evidence. The G5-H sign failure is nevertheless
consistent with the certified high-height failures and is not needed for the
no-go.

## Scope

This kills only:

```text
A-V = unconstrained minimum H1 energy over the interpolation fibre,
      using the registered two-copy source family and cutoff.
```

It does not kill:

```text
- a health-constrained selector with an independently justified C > 0 cone;
- a phase/variation selector with a proved dual certificate;
- the window-track COVER experiment;
- every Route-A signed-kernel mechanism.
```

However, adding `C > 0` after seeing this result would be a new mechanism,
not a repair. It must be pre-registered and justified as an existing healthy
owner condition, while the missing `D < 0` margin remains an independent
conclusion.

## Decision

Do not formalize the unconstrained A-V minimizer. The next admissible Route-A
probe is A-H: first characterize the feasible healthy cone in the same owner
fibre, then test whether a minimum-energy point exists inside that cone with a
strict D margin. If the healthy cone is empty or its best certified D is
nonnegative on the registered owners, record a second scoped no-go and move the
main effort to Route B.

Source artifact:

```text
results/2000_route_a_variational_probe.json
```