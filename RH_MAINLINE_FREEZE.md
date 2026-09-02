# RH Mainline Freeze

Status: revised 2026-08-31 by route record 1076.

## Active Objective

The repository has one active mathematical objective: close the unconditional
Connes--Weil route to the Riemann Hypothesis through the healthy `CompactLog`
owner. The active dependency graph is

```text
assume an off-line zero
  -> selected orbit detector with qw(g) < 0      [formal]
  -> detector-specific semi-local positivity: qw(g) >= 0  [open]
  -> SourceRH                                    [formal implication]
  -> Mathlib RiemannHypothesis

ROOT-window CC20 positivity                      [shared local base]
  -> applies only with a matching support theorem or a semi-local extension
```

`normalizedSelectedFinalRouteDetectorCriterionCoverageRoot` stays in the output
audit because Lean proves that socket RH-equivalent.  It is not the mathematical
producer target: its `normalizedCC20TestSpace` owner uses the rejected additive
convolution model.  A healthy-owner proof may discharge or replace the socket
only after it reaches `SourceRH` without consuming the socket, `SourceRH`, or an
equivalent no-off-line-zero premise.

The repository does not contain an unconditional RH proof.  The ROOT-window
base does not imply the detector-specific semi-local step.

## Frozen Routes

The following are archival context only and receive no new theorem work:

- Physical Gate 3U, including the finite/decaying-band Route-A deliverable.
- The infinite-carrier Gate-3U cancellation and leakage identities.
- Gate-3U source owners, renewal/trace probes, and physical audit modules.
- Lane R and Gamma_R prefix/tail sign experiments that do not imply global
  spectral nonnegativity.
- The universal B1 globalization: positivity for all compact supports or a
  density/partition lift from the ROOT window.
- New producer work on `normalizedCC20TestSpace` or the literal normalized B5
  coverage socket.  Its additive convolution fails the Mellin product law.
- Nyman--Beurling, Mobius, Burnol, adelic, Clifford, and the historical
  prolate/Sonin routes rejected in their named records.  The paper-scale local
  CC20 prolate certificates and a new healthy detector-specific semi-local
  owner are the only active exceptions.

The independent finite-band deliverable is physically archived at
`archive/diagnostic_gate3u/deliverable_finite_gate/`. The untracked narrow
Lane-R prefix leaf was archived at
`archive/diagnostic_lane_r/lean/C1XiCenterTwoGammaFinitePrefixNarrow.lean`.
Shared source modules
that are still imported by the RH-facing interfaces remain in place for build
compatibility, but are frozen and may not gain new consumers.

## Allowed Work

New Lean or analytic work is allowed only when the proposed theorem names a
direct consumer in the active healthy-owner chain.  The open consumers are:

1. The paper-scale `gamma + alpha/beta + delta` ROOT-local certificate package.
2. An explicit support radius and finite visible-prime set for the formal
   compact-log orbit detector.
3. Semi-local positive-trace/readback data for that selected detector on the
   same healthy owner.
4. Maintenance of the formal detector-specific contradiction interface to
   `SourceRH`.

Before editing, record which consumer is being advanced. A bound that ends at
a physical trace, finite band, numerical scan, universal-B1 placeholder, or
the normalized additive owner is not an RH step and must remain frozen.

The repository check is `scripts/check_rh_mainline_freeze.ps1`. It is read-only
and fails closed on changes under frozen route namespaces. Use its archival
override only for an explicitly reviewed provenance edit.

## Unfreeze Rule

A frozen route may be reopened only after a checked theorem supplies a named
premise of the healthy detector-specific semi-local chain or proves `SourceRH`
on the healthy owner.  The proof may not consume the normalized coverage
socket, `SourceRH`, or an equivalent RH statement.  Record the theorem
statement, assumptions, build evidence, and axiom audit in `MEMORY.md` before
reactivation.
