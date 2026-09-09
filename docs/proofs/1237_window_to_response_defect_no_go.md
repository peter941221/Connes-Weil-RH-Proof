# 1237 - Window-to-response defect is not a vanishing counterterm

Date: 2026-09-09.

Status: FORMAL no-go from the active C1 projection ledger. Consumer: the
healthy-`CompactLog` B5 projection-cutoff route.

## Candidate rejected

The exact finite-window bridge is

```text
finiteWindow = projectionResponse + D₁ + D₂,
D₂ = windowedDetector - projectionResponse.
```

A tempting internal repair is to treat `D₂` as a transient response defect
and require its trace to vanish, so that only the projection response remains
in the finite-part ledger.

## Formal verdict

For every nonzero selected source test, assuming the projection response is
trace-class, the theorem
`canonicalCutoffWindowToResponseDefect_not_tendsto_zero` proves that

```text
Re Tr(D₂,n) ↛ 0.
```

Therefore the response defect cannot be discarded as a vanishing remainder.
Subtracting it externally is not a positive-kernel construction, while
absorbing it internally must change the cutoff kernel and re-prove positivity.

## Consequence

Together with record 1236, the canonical identity complement and the
canonical `D₂ → 0` repair are both closed.  A surviving Fork-B object must be
a genuinely moving, operator-valued two-channel correction whose positivity
and same-owner trace readback are proved simultaneously.

Evidence: `C1ProjectionSquareCanonicalCutoffGuard.lean`, theorem
`canonicalCutoffWindowToResponseDefect_not_tendsto_zero`, backed by the exact
three-term bridge in `C1Stage3ProjectionResponseBridge.lean`.

RH is not claimed.
