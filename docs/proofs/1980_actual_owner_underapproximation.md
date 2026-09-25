# 1980 — Actual-owner under-approximation and powered-seed stress test

Date: 2026-09-25.

Status: NO-GO for the current smoothSeed numerical selector at the required
owner scale; powered-seed route remains a quantitative candidate, not GO.
This record does not claim a determinant theorem or RH.

## Consumer and owner

The consumer is the same-owner four-point span: one `rho`, one `N`, one base,
one correction, one `n`, and `lambda = b / C` must satisfy the gate signs and
the same-index tail inequality. The formal correction owner is
`healthyCorrectionNodes` from `C1ExplicitHealthyCorrectionBudget.lean`.

The numerical owner is only an under-approximation: known `mpmath.zetazero`
zeros in the formal closed ball, plus the hypothetical orbit and all healthy
target nodes. It is therefore a stress test and cannot certify the full source
zero owner.

## Current smoothSeed selector

For `rho = 0.55 + 14.134725141734693 i`, the finite-grid base quadratic
envelope is about `Cb = 4.077e4`. The displayed height-budget inequality

```text
Cb^2 * (2*pi)^4 < 2^(4*(N+1))
```

first passes at `N = 10` on this grid. At that `N`, the known-zero
under-approximation has 400 source zeros and 408 total owner nodes; the minimum
separation is 0.05. Target node products overflow binary64 before the gate can
be evaluated, and the gate route reports non-finite values. The correction C2
scan is likewise non-finite. This is a selector/conditioning failure, not an
all-seed mathematical no-go.

Reproduction:

```text
python scripts/fourpoint_actual_owner_1980.py
```

The result is written to `results/1980_actual_owner_underapprox.json` with
status `UNDERAPPROXIMATION_NUMERIC_OVERFLOW`.

## Explicit changed assumption: powered interpolation seed

The only tested change is to replace the seed transform by

```text
L_powered(s) = L_smoothSeed(0.5 * s)^10
```

which corresponds analytically to a rescaled ten-fold convolution seed. This
is a real construction change: support, seed mass, correction constants, and
the visible-prime owner must all be re-proved together.

On the same known-zero under-approximation with `N = 4` (27 total nodes, 19
known source zeros, minimum separation 0.05), the finite-grid envelopes are

```text
base C4 <= 1.53e2
correction C2 <= 6.84e2
base C2 <= 2.5e1
```

The gate and tail use the same `n` and the same vertex `lambda`:

```text
n = 0: C = +2.37e3, b = +2.68e6, D = +2.93e9,
      det = -2.58e11, lambda = 1.13e3,
      tail proxy L_n / lambda^2 = 2.14e28

n = 4: C = +3.00e6, b = +4.31e9, D = +6.20e12,
      det = -1.42e16, lambda = 1.44e3,
      tail proxy L_n / lambda^2 = 5.22e25
```

Thus the powered seed repairs the numerical owner overflow and gives a
sign-side candidate, but it does not give GO: the same-index tail margin is
still larger than one by roughly 25--28 orders of magnitude in the tested
range. Increasing `n` also enlarges the selected support and its finite prime
owner; no interval-certified `n` with the complete owner has been found.

## Decision

```text
current smoothSeed + actual-owner under-approximation:
  NUMERICALLY BLOCKED before determinant/tail certification

powered seed (scale 0.5, power 10):
  gate signs: promising on an under-approximation
  same-index tail: FAIL
  route status: OPEN, not GO
```

The four-point span route is still the binding route. No determinant Lean work
should begin until a powered seed with explicit support/decay constants also
produces a finite, interval-certified same-index tail ratio below one.
