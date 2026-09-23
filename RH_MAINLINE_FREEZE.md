# RH Mainline Freeze

Status: revised 2026-09-23 by route records 089--094 and the core-progress gate.

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

Producer-target state (2026-09-23, map records
[`089`](docs/map/089_base_contraction_zero_target_no_go.md)--
[`094`](docs/map/094_two_point_differential_annihilation_and_spectral_decomposition.md)):
the actual orbit detector's support-derived visible-prime cutoff, finite owner,
carrier reparameterization, phase readbacks, and the four-point same-owner
finite-prefix transport are formal.  The geometric-contraction branch is a
scoped no-go.  The live producer is either the actual same-owner signed
physical-kernel/C3' budget, or the equivalent phase-balanced two-span
contradiction: the optimal span already has semi-local nonnegativity, and must
still be proved spectrally negative while retaining the selected off-line-zero
contribution and controlling the explicit weighted high-shell tail.  Neither
sign estimate is currently proved.

## Frozen Routes

The following are archival context only and receive no new theorem work:

- Physical Gate 3U, including the finite/decaying-band Route-A deliverable.
- The infinite-carrier Gate-3U cancellation and leakage identities.
- Gate-3U source owners, renewal/trace probes, and physical audit modules.
- Lane R and Gamma_R prefix/tail sign experiments that do not imply global
  spectral nonnegativity.
- The universal B1 globalization: positivity for all compact supports or a
  density/partition lift from the ROOT window.
- The Line-B Bombieri finite-positive-owner campaign: all mass, Hermitian,
  residual, spectral-tail, canonical-prefix, direct real-Gamma, and indirect
  same-owner positive-readback variants are frozen by records 1192--1195.
  No new Line-B producer, wrapper, coordinate transformation, or numerical
  falsifier may be opened without Peter's explicit instruction.
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
   It may advance only when the theorem names and discharges a premise of the
   healthy detector-specific semi-local producer.
2. The unconditional same-owner signed physical-kernel/C3' estimate for the
   actual selected orbit detector and its already-formal finite visible-prime
   owner.
3. The phase-balanced two-span spectral contradiction of records 091--094:
   construct one test that simultaneously has the proved semi-local
   nonnegativity and a strict negative spectral value with an explicit margin.
4. Maintenance of the already-formal contradiction interface to `SourceRH`
   only when required by a producer change; new consumer-only exits are frozen.
5. Read-only new-math idea generation under the record 1227 NM loop (map
   document 006): literature and corpus sweeps, paper-only shape screens
   against the committed corridor spec, and MODEL-labeled prototypes that
   must reproduce the committed positive control before any detector
   claim. The loop produces no Lean work by itself; any landing out of
   the loop names its direct consumer under the rule above.

Before editing, record which consumer is being advanced. A bound that ends at
a physical trace, finite band, numerical scan, universal-B1 placeholder, or
the normalized additive owner is not an RH step and must remain frozen.

## Core-Progress Gate

Until the actual selected-detector sign contradiction is proved or refuted,
generic `MasterExit`, tail-reduction, coordinate-transport, symmetry, readback,
and conditional-certificate expansion is frozen.  Such declarations are
infrastructure, not RH-core progress, unless the same change discharges a named
hypothesis of one of Allowed Work items 2 or 3.

Every substantive campaign starts with a short same-owner assumption ledger:
the exact target inequality, all current hypotheses, the hypothesis to be
removed in that campaign, and a failure criterion.  It must finish with at
least one of:

1. an unconditional quantitative bound with an explicit margin on the actual
   selected owner;
2. a named reproducible counterexample or no-go ruling; or
3. a strictly smaller quantitative obligation with at least one previous
   premise proved rather than renamed or repackaged.

Replacing one open estimate by an equivalent open estimate is not progress and
does not authorize another interface round.  Numerical probes are permitted
only to adjudicate a candidate sign, locate explicit constants, or generate an
exact certificate that Lean can verify.

The repository check is `scripts/check_rh_mainline_freeze.ps1`. It is read-only
and fails closed on changes under frozen route namespaces. Use its archival
override only for an explicitly reviewed provenance edit.

## Unfreeze Rule

A frozen route may be reopened only after a checked theorem supplies a named
premise of the healthy detector-specific semi-local chain or proves `SourceRH`
on the healthy owner.  The proof may not consume the normalized coverage
socket, `SourceRH`, or an equivalent RH statement.  Record the theorem
statement, assumptions, build evidence, and axiom audit in `MEMORY.md` before
reactivation.  For Line B specifically, Peter's explicit instruction is also
required before any new work is opened, even if the proposed work satisfies
the general consumer rule.
