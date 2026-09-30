# 2286: MPFR-directed corrected-owner atom preflight

Date: 2026-09-30

Decision: the first finite-window evaluator primitive is numerically viable at the fixed-atom level; no quadrature certificate is claimed.

## Scope

The corrected width-a^2 owner is evaluated at fixed `(xi, y)` points for `xi` in `{40, 120, 200}` and nine interior y points. Each family term is propagated with 256-bit MPFR using directed rounding:

```text
RNDD -> lower endpoint
RNDU -> upper endpoint
```

The complex phase uses endpoint plus periodic-extremum bounds for sine and cosine. The full 30-family sum is accumulated as an interval before any modulus is taken. The owner keeps the support-derived 41136 prime-power count as a provenance guard.

## Result

```text
quantity                         maximum interval radius
base complex atom                1.3393730569e-12
corr complex atom                2.0685391178e-9
```

All 27 sampled atoms are finite. This is materially tighter than the initial safe `[-1,1]` trigonometric envelope, which was intentionally rejected as too loose.

## Boundary of the result

This is not an integral enclosure. It does not bound the quadrature remainder, panel interpolation error, finite-window functional, or infinite xi tail. It is only the arithmetic foundation for the next evaluator layer.

The next gate is to add a panel rule whose remainder is independently bounded, then compare partition and precision changes while retaining the same-owner 41136-term guard.

## Reproduction

The runtime requires WSL/Linux `libmpfr.so.6`:

```text
wsl.exe bash -lc "python3 /mnt/c/Projects/Connes-Weil-RH-Proof/scripts/routea_mpfr_owner_atom_preflight_2286.py"
python -m unittest discover -s scripts -p 'routea_mpfr_owner_atom_selftest_2286.py' -v
```
