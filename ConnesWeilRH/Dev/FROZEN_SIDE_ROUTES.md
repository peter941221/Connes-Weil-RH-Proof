# Frozen Side Routes

This directory contains both the active C1/RH development leaves and old
diagnostic experiments. The following families are frozen from 2026-08-19:

- `*Gate3U*`, `*RouteA*`, `*RawRenewal*`, and physical cancellation audits.
- `C1LaneR*` and the constrained `C1XiCenterTwoGamma*` prefix/sign leaves.
- Numerical probes and audit-only modules whose endpoint is not
  `SourceRH`, detector-criterion coverage, or a direct consumer of those
  statements.

The frozen files remain in place when shared imports or historical references
need them. They are provenance only: do not import them into a new RH theorem,
do not strengthen their status, and do not treat a conditional contract as a
producer. The active RH-facing leaves are the C1 same-owner, explicit-formula,
Yoshida-detector, and route-exit modules named by `RH_MAINLINE_FREEZE.md`.

