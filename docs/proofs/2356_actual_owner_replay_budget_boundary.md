# 2356 - Actual-owner replay exposes the current budget boundary

日期：2026-10-01。

## Result

Using the existing WSL `/home/peter/rh/.venv-flint` environment, the 2337
marked-sign certificate and the 2339 repair/norm transfer were replayed
without changing the project source or the Mathlib checkout.

The 2337 Arb run completed and retained the marked-square numerical sign, but
all eight mandatory source values failed to contain their nominal targets.
The recorded source imaginary residuals are about `3e-9` to `7e-9`; this is a
captured numerical sign certificate only, not exact interpolation.

The 2339 run does not fit the old pin on replay:

```text
all_nodes_fit_existing_pin = false
failed_sufficient_bound_nodes = [-50]
maximum_min_product_upper = 2644543.1669421422...
existing_pin = 2644542.8515
unweighted_full_line_upper = 3.6014017043843067...
```

Thus the old 2339 pin cannot be used as the current selected-owner margin.
This is not a proof that the owner is impossible; it is a certified-budget
replay boundary showing that the existing pin must be recomputed or replaced
before any signed physical-kernel charge is consumed by the producer.

## Consequence for the route

Do not import the 2337 marked sign as an exact detector gate, and do not
transfer the old 2339 pin to the live producer. The next valid numerical
target is a same-run, same-owner budget reconstruction with explicit forward
error and a new pin. Only after that pin closes can the complete prime-power
book and signed Fourier/kernel readback be priced.

No healthy detector, producer GO, map-103 reopening, or RH claim follows from
this replay.
