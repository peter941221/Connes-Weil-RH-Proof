# 2181 — Route A zero-mass even-bump screen

Date: 2026-09-29  
Status: scoped no-go for the tested even-bump shape family; no Route-A
producer ruling changes.

## Consumer and scope

The intended consumer remains the same-owner selected healthy `CompactLog`
detector and its `qw(g) >= 0` obligation. This screen tests only a narrow
zero-mass physical-kernel shape family. It does not use or replace the exact
closed-ball source-zero owner, so it cannot be promoted to a producer result.

## Probe

The existing scripts `zero_mass_even_bump_probe_2163.py`,
`zero_mass_even_bump_eigen_2164.py`, and
`zero_mass_even_translated_eigen_2165.py` were rerun unchanged.

For the even bump-width families, the largest restricted quadratic-form
eigenvalues were:

```text
[0.10, 0.18, 0.26, 0.346] : -0.0295138161
[0.08, 0.14, 0.20, 0.26, 0.32, 0.346] : -0.0221767082
[0.05, 0.10, 0.16, 0.22, 0.28, 0.34] : -0.0296505565
```

The direct two-bump scan stayed negative over all tested ratios and widths;
its best values were approximately `-0.04949`, `-0.05411`, `-0.05733`, and
`-0.05004` for the four tested outer widths, stable from `dx=4e-4` to
`dx=1e-4`. The translated-bump null-mass eigen scan gave
`-0.0025472` at `dx=4e-4` and `-0.0026381` at `dx=2e-4`.

## Decision

`SCOPED-NO-GO-EVEN-BUMP-ZERO-MASS`: the tested even-bump and translated
zero-mass families do not supply the required positive direction. This is a
shape-family result only. It does not close the owner-preserving,
non-interpolating weighted-zero-measure certificate `A.005.1` from record
2177, whose weight must still be derived from the actual physical-kernel
formula and priced on the exact owner.

No `GO` is claimed. The next admissible probe must change the named
mechanism, not merely resample this family.
