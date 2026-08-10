# 948 — lane-B total archimedean term CLOSED (Wall-A sub-steps 1.1 + 1.2)

Date: 2026-08-10. Status: verification note, axiom-clean. RH NOT claimed.
Mirror: `cwr-lanb-archlift` (isolated ext4, warm seed, Windows sources). Builds
below: `Dev.WellFormHealthyRepoint + CompactSCealBalance + Wall1StrictWeilInput`
3189 jobs green.

## What closed

945 flagged the healthy carrier's `archimedeanTerm` slot as the literal
placeholder `fun _ => 0` in every constructible carrier. Wall-A D&C sub-steps
1.1 and 1.2 now replace that with the real CCM25 Eq.3.7 term:

  * `Dev/CompactLogArchimedeanLift.lean` (1.1): `compactLogArchimedeanTerm :
    CompactLogTest -> R`, the Eq.3.7 archimedean explicit-formula term
    (real part), on compact-log tests. Axiom-clean.
  * `Dev/CompactArchTotal.lean` (1.2): `totalArchimedean : TestFunction -> R`
    with the classical total extension -- on a test carrying a `CompactLogTest`
    representation it returns the Eq.3.7 term there, else `0` -- plus:
      - consistency `compactLogArchimedean_test_congr` (equal `.test` -> equal term),
      - match `totalArchimedean_eq_compact` (returns Eq.3.7 value on compact inputs).
  * `Dev/WellFormHealthyRepoint.lean`: `healthyWeilForm.archimedeanTerm` is now
    `totalArchimedean` (was `fun _ => 0`), and
    `healthyArchimedean_eq_compact` / `healthyArchimedean_matches_compactTerm`
    tie the carrier slot to the CCM25 Eq.3.7 real term on any compact-log test.
  * (follow-up wiring) `Dev/WellFormHealthyRepoint.lean` adds the SCAL/SCB-facing
    connectives: `healthySymbols_archimedeanTerm_eq` (``healthy toWeilFormSymbols
    .archimedeanTerm F = totalArchimedean F``) and
    `healthySymbols_archimedeanTerm_square` (the convolution-square read), so the
    lane-B SCAL/SCB statement operates on the real Eq.3.7 term.
    Axiom-clean; 2956 jobs green.

`#print axioms` for `totalArchimedean`, `totalArchimedean_eq_compact`,
`compactLogArchimedean_test_congr`, `healthyArchimedean_eq_compact`,
`healthyArchimedean_matches_compactTerm`, `healthySymbols_archimedeanTerm_eq`,
`healthySymbols_archimedeanTerm_square`, and `healthyWeilForm` (in-module) =
`[propext, Classical.choice, Quot.sound]`, 0 sorry / 0 project axiom.

## Honest scope / still open

This is the definitional front (sub-steps 1.1/1.2) of Wall-A. It fills the
placeholder and gives the healthy carrier a genuine data path into Eq.3.7, but
the *analytic identity* -- Wall-A sub-steps 1.3/1.4 (the healthy
`psi`/`qwLambda` = Weil explicit-formula balance, closing `SCAL`/`SCAB` on the
healthy symbols) -- remains OPEN and is real analysis, not leaf assembly. Lane-C
(Wall-B, the infinite-carrier Gate identity `(I-P)F = -(I-P)D`) and the
RH-equivalent C1 discharge (946 (a)/(b)) also stay open. RH NOT claimed.