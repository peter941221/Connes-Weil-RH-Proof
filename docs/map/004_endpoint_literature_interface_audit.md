# 004 — Endpoint literature and C3 interface audit

Status: binding companion to [003]. Compressed 2026-09-23; RH is not claimed.

## Evidence levels

- `FORMAL`: checked in Lean on the named owner.
- `LITERATURE-BACKED`: located in a primary source, but not yet transported to
  the repository owner.
- `PROJECT CANDIDATE`: internal derivation or proposed estimate.

An external compact-window theorem cannot be promoted directly to `FORMAL` or
to detector-specific positivity. Its hypotheses, normalization, support,
kernel, and quantifiers must first be matched.

## The two C3 branches

C3 is the missing nonnegative sign for the same detector already carrying
strict spectral negativity.

```text
C3-local:
  prove the selected detector lies in the ROOT window
  -> consume the fixed-window endpoint theorem

C3-semi-local:
  keep the detector's actual support-derived finite prime set
  -> prove archimedeanTerm(square) + finitePrimeSum(square) <= 0
  -> obtain qw(detector) >= 0
```

The first branch has no matching support theorem. The second branch is the
active shape and is represented by [047], [075], [079]--[082].

## Formal route facts

The following boundary is checked in the project:

- `HealthyYoshidaDetectorData` exists for every hypothetical right off-line
  zero on the healthy `CompactLog` owner;
- the same selected detector satisfies `qw(g) < 0`;
- `healthy_sourceRH_of_right_detector_specific_qw_nonneg` needs only
  `0 <= qw(g)` for that detector;
- `orbitWindowSemiLocalGate` is an equivalent sign-facing consumer after the
  triple-vanishing identity;
- the support of the detector determines a finite visible-prime-power set;
- the contradiction and `SourceRH`/Mathlib RH wiring are formal.

Principal modules are `C1HealthyYoshidaDetector.lean`,
`C1HealthyYoshidaSpectralNegativity.lean`, `C1SameOwnerWeil.lean`,
`C1OrbitWindowSemiLocalGate.lean`, `C1MinimalWeilCriterion.lean`, and
`C1WeilCriterionEquivalence.lean`, with paired audits.

## Sign bookkeeping

For triple-vanishing tests, the semi-local gate is the exact owner of the
desired sign. The prime term is finite because of compact support, but its
index set changes with that support. Replacing it by a fixed truncation, a
continuous density, or a larger unsigned majorant changes the mathematical
problem unless a proved comparison restores the exact sign.

The detector sign audit [047] gives the current physical-energy and prime
discrepancy normal forms. Those identities expose candidate estimates; they
do not prove the sign. The signed C3' owner [080] is the current formal socket.

## ROOT endpoint interface

The local endpoint package [001] may feed C3 only through one of these checked
interfaces:

1. a theorem proving the selected detector's support is inside the ROOT
   window; or
2. a semi-local theorem extending the endpoint estimate to the detector's
   exact finite visible-prime set.

Neither interface is currently supplied. `C1HealthyDetectorRootSupportExit`
is a conditional consumer, not a support producer.

## External-source rule

When importing an endpoint result, record:

- the source theorem and page/equation;
- the exact function space and normalization;
- whether support is open, closed, or almost-everywhere;
- the operator/kernel owner and any regularization;
- uniformity in scale and endpoint parameters;
- the Lean declaration that will consume it.

If any item differs, first prove an explicit transport theorem. Similar
notation or a shared word such as "prolate", "trace", or "positivity" is not
an interface.

## Binding conclusion

The shortest live route remains detector-specific semi-local positivity on
the healthy owner. ROOT-window work is shared infrastructure, not the exit.
The open theorem is still:

```text
for every hypothetical off-line zero rho,
for the detector g_rho already selected by the construction,
prove qw(g_rho) >= 0.
```

No stored conclusion, `SourceRH` premise, universal positivity premise, or
RH-equivalent coverage socket may be used as analytic source data.
