# 073 M3A Upstream Consumer Death Verdict

Date: 2026-07-12

Result: stop the M3A Q-root/kernel lane before empirical implementation. The
Q-root survives its local algebraic and Mellin gates, but the only planned
consumer is already dead upstream.

## Local Gates

Proof records 071 and 072 establish that no cheap local contradiction was
found:

```text
g=(d/dx+1/2)xi
g* * g=Q(xi* * xi)
triple Mellin zeros are preserved
off-line detection can be renormalized
compact support and smoothness are preserved
```

CC20 Theorem `thmqkey1` supplies the unconditional archimedean shape

```text
D o Q(xi*xi*)=<xi,(-2 Id+K_I)xi>,
```

with `K_I` Hilbert-Schmidt on the bounded support interval. The abstract M4
finite-net theorem then gives a finite-dimensional control space outside which
the real quadratic form is nonpositive.

None of these facts supplies a detector.

## Fatal Consumer Chain

Plan 016 requires M5C to combine the M4 orthogonality rows with one M5B test
that retains a strict source zero-sum sign. That sign still requires the same
test to detect the marked off-line zero and control every other source zero.

```text
M3A + M4
  -> finite-codimension local remainder sign only
  -> M5C still consumes M5B strict same-test source sign
  -> M5B consumes the all-other-zero detector contract
  -> rejected P2 contract
```

The rejection is already recorded in:

```text
plan/016_2026-07-10_unified_remaining_gaps_plan.md:3-17
docs/proofs/016_yoshida_model_verdict.md
docs/proofs/023_qeasy_radius_count_verdict.md
docs/proofs/024_pre_cutoff_scattering_consumer_screen.md
```

The normalized fixed-window construction has a radius/count cycle:

```text
choose nearby radius R
  -> obtain interpolation-dependent constants
  -> choose convolution count n
  -> far estimate starts only beyond (n+1)T
  -> need R >= (n+1)T with no producing bound.
```

Moreover, the completed all-other-zero detector contract together with the
CC20 finite-vanishing criterion proves source RH. It is not a lower producer
that may be assumed to feed M5C.

## Exhausted Rejection Checks

```text
+---------------------------------------+----------------------------------+
| gate                                  | verdict                          |
+---------------------------------------+----------------------------------+
| Q-root algebra/sign                   | survives                         |
| compact support and smoothness        | survives                         |
| triple Mellin nodes                   | survives                         |
| off-line detector multiplier          | survives                         |
| Hermitian companion collision         | excluded in the open strip       |
| Q normalization                       | matches CC20                      |
| compact remainder finite conditioning | abstract M4 theorem exists       |
| same-test global detector consumer    | rejected / RH-level bottom       |
+---------------------------------------+----------------------------------+
```

## Decision

```text
M3A as a local source theorem: mathematically pending
M3A as an executable Plan 016 lane: rejected
Q-root Lean implementation: do not start
K_I numerical/empirical stage: do not start
route rewiring: forbidden
```

Reopening requires a new source-sign consumer strictly weaker than the M5B
all-other-zero detector, or a new same-test detector construction that closes
the radius/count cycle without assuming an RH-equivalent premise. Improving
the local M3A producer alone cannot reopen the route.
