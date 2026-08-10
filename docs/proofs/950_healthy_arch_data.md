# 950 — data-bearing healthy archimedean term (SCAL/SCB 前置对象，axiom-clean)

Date: 2026-08-10. Status: verification note. RH NOT claimed.
Mirror: `cwr-lanb-archlift`. Build: `Dev.HealthyArchData` 2957 jobs green,
axioms `[propext, Classical.choice, Quot.sound]`, 0 sorry / 0 project axiom.

## What closed

lane-B `SourceScopedArchimedeanContributionBalance` (SCB) reads
`W.archimedeanTerm (W.convolutionStar f f)`.  To give that value a *data-bearing*
owner (AGENTS 6) pinned to the real CCM25 Eq.3.7 term, new `Dev/HealthyArchData.lean`
builds, on the healthy carrier's `healthySymbols = healthyWeilForm.toWeilFormSymbols`:

  * `healthyArchData_readOff f`: `healthySymbols.archimedeanTerm
      (healthySymbols.convolutionStar f f) =
     totalArchimedean (healthyConvolutionStar f f)`
  * `healthyArchData f : SourceArchimedeanTermData healthySymbols f` with
    `sourceArchimedeanTerm = totalArchimedean (healthyConvolutionStar f f)` and
    both read-offs (square + arch).

Both are axiom-clean.  This is the data object the SCB statement is stated
against; it does NOT prove the analytic balance (Wall-A 1.4 still open).

## Honest scope

No RH claim.  The analytic `psi`/`qwLambda` explicit-formula balance (1.3/1.4)
remains open; the data-facing front is now concrete and verified.