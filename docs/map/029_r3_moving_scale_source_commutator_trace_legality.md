# 029 — R3 moving-scale source commutator trace legality

**Date:** 2026-09-15.
**Status:** FORMAL source-side trace legality at every selected scale;
G8 cutoff transport and same-owner readback remain OPEN.
**Consumer:** healthy-`CompactLog`, B5 detector-specific `qw >= 0` for the
same tower-selected test, followed by the existing `SourceRH` contradiction.

This supporting record updates the R3 trace ledger without changing the
binding route in [003](003_b1_b5_minimal_exit_route_selection.md). Lean now
proves `sourceSoninDetectorCommutator_isTraceClassAlong_all_scales` for the
actual source Sonin projection and detector, along any explicitly named
global basis, with the source support and boundary bases in the inputs. The
proof uses the exact source-to-three-branch commutator identity and the
all-scale prolate-factor square-sum from [1465](../proofs/1465_r3_moving_scale_detector_root_range_energy.md).
The same basis also supports an exact ordinary-trace decomposition into the
outer pair plus the still-coupled source second-support/prolate remainder.
See [1466](../proofs/1466_r3_moving_scale_source_commutator_trace_legality.md).

This is a trace-ideal and trace-ledger theorem for the complete signed source
commutator. It does not assert an isolated leakage estimate or a positivity
result. The following are still required to reach `G8SameOwnerReadbackData`:

```text
G8 cutoff/source compatibility
  -> same-owner signed remainder convergence
  -> trace-to-qw readback
  -> detector-specific semi-local positivity
```

The conditional R3-to-`SourceRH` implication remains as recorded in
[012](012_g8_same_owner_readback_rh_reachability.md). No RH conclusion is
claimed.
