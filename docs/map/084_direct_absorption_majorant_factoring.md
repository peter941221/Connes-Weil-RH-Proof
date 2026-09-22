# 084 — Direct absorption majorant and prime weight factoring

Date: 2026-09-22.

Status: formal majorant factoring landed; connects factored profile bounds directly to Mathlib RH.
Subordinate to binding B5 route ruling in [003](003_b1_b5_minimal_exit_route_selection.md).

Consumer: the healthy `CompactLog`, detector-specific B5 statement `0 <= qw g`,
through `SourceRH` and Mathlib RH.

## Result

`C1P2DirectAbsorptionMajorant.lean` decouples the finite visible-prime book from the
detector profile by factoring:

```text
sum_{n in visible} (Lambda(n)/sqrt(n)) * |profile(log n)|
  <= (sum_{n in visible} Lambda(n)/sqrt(n)) * B
  <= (sum_{n in visible} Lambda(n)) * B
```

It proves:
- `riemannHypothesis_of_uniform_profile_bounds`: if for every right-hand zero there exists
  a geometry and a uniform profile bound B such that `visiblePrimeWeightSum * B <= - archimedeanTerm`,
  then Mathlib's canonical `RiemannHypothesis` holds.
- `riemannHypothesis_of_chebyshev_bounds`: if `visibleChebyshevPrimeSum * B <= - archimedeanTerm`,
  then Mathlib's canonical `RiemannHypothesis` holds.

## Boundary and Open Obligation

The arithmetic summation is decoupled from the detector. The remaining open mathematical
obligation is to bound the single scalar B for the actual selected orbit owner and
verify that `visiblePrimeWeightSum * B <= - archimedeanTerm`.

Evidence: `ConnesWeilRH/Dev/C1P2DirectAbsorptionMajorant.lean` and
`C1P2DirectAbsorptionMajorantAudit.lean`; build log `build-logs/1835_direct_absorption_majorant.log`
(clean, standard axioms, zero sorryAx).
