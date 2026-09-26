# Record 2002 - A-H health-constrained selector probe preregistration

Date: 2026-09-26.

Status: pre-registration. No run result is included here.

## Mechanism

A-H tests whether the A-V failure is caused by leaving the healthy-owner
region. It preserves the actual Route-A EXT owner and all interpolation
constraints. The base selector is the committed interpolation selector on
the original family. The correction selector varies on a fixed feasible
segment between:

```text
c_min  = minimum-H1 correction in the overcomplete owner family
c_ref  = committed correction coefficients embedded in that same family
c(t)   = (1 - t) c_min + t c_ref
```

Because both endpoints satisfy the same owner interpolation equations, every
c(t) preserves the owner pins. The health condition `C > 0` is measured, not
assumed. No `D < 0`, determinant, or residual condition is inserted into the
selector constraints.

## Registered cases and grid

```text
case        delta   gamma       scale
G5-H        0.10    30.424876   0.92
G5-W        0.10    30.424876   0.90
G7-H        0.10    37.586178   0.92
G8-H        0.10    40.918719   0.88
```

For every case use exactly:

```text
t in {0.0, 0.1, 0.2, ..., 1.0}
three width copies per owner node: 0.8a, 1.0a, 1.2a
k = 30, n = 0, xi_max = 40, dxi = 0.004
```

The committed profile at width `a` is the middle copy, so the reference
selector is embedded exactly rather than reconstructed approximately.

## Decision rules

```text
A-H-GO-CANDIDATE:
  at least three of four cases have a certified t with
  C > 0, D < 0, det < 0, and route spread_D < 1/3;
  all interpolation pin errors <= 1e-6.

A-H-NO-GO:
  no registered case has a certified healthy point, or every certified
  healthy point has D >= 0 or det >= 0.

A-H-UNRESOLVED:
  conditioning, pin errors, or route coverage prevents the registered
  decision on at least one case and the remaining cases do not satisfy
  either GO or NO-GO.
```

A-H-GO-CANDIDATE only authorizes a continuum health-cone and dual-certificate
desk. It is not a producer theorem. A-H-NO-GO is scoped to this segment and
three-copy owner family; it does not kill every sign-constrained selector.