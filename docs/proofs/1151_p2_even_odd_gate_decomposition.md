# Record 1151 — P2 even/odd gate decomposition

Date: 2026-09-06

## Result

`C1P2EvenOddGateDecomposition.lean` proves finite-prime additivity for
arbitrary compact-log test sums.  The proof uses the union of the three
visible-index sets, so possible cancellation in the summed owner cannot lose
any nonzero term.  It then combines this with the existing convolution-square
expansion.

If `f` is even and `g` is odd, the polarized cross test is odd.  Its bilateral
profile, every finite-prime term, and its complete finite-prime sum vanish.
The existing archimedean odd-kill therefore yields the full gate identity

```text
ICgate((f + g)□) = ICgate(f□) + ICgate(g□).
```

The owning and audit modules build successfully in 3681 jobs.  The audited
declarations use only `[propext, Classical.choice, Quot.sound]`; there are no
`error:` lines and no `sorryAx`.

## Route meaning

This is a FORMAL Line-C structural reduction, not a positivity theorem.  The
odd correction is invisible only in the polarized cross channel; its own
square can still contribute finite-prime mass.  Thus the even/odd family
reduces the producer to two diagonal gate contributions, but does not remove
the open archimedean/finite-prime sign problem.

No route selection changes.  P2/C3 remains OPEN and RH is not claimed.
