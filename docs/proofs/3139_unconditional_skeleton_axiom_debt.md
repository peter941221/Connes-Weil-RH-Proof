# Record 3139: Unconditional skeleton axiom-debt audit

Date: 2026-10-27.

Status: audit only. The development skeleton is not a verified RH proof and
is not promoted to Producer GO.

## Finding

`ConnesWeilRH/Dev/UnconditionalSkeleton.lean:18-29` states that the module is
a temporary development skeleton. Its unresolved bottoms are intentionally
represented by declarations named `...Root`. Therefore a value of
`RouteCertificate` constructed in that module is not evidence that the route
has been discharged under the standard axiom trio.

The new audit module
`ConnesWeilRH/Dev/UnconditionalSkeletonAxiomAudit3139.lean` prints axiom
dependencies for the first trace object, cleared ledgers, the route certificate,
and both RH outlets.

```text
construction exists
        |
        +-- trace readout exists
        +-- ledgers-cleared value exists
        +-- route certificate exists
        v
axiom audit
        |
        +-- standard trio only       => eligible evidence
        +-- any `...Root` axiom       => unresolved producer debt
        +-- `sorryAx`                 => immediate rejection
```

## Root inventory visible in the source

The following unresolved roots are declared in the skeleton and must not be
silently treated as numerical certificates:

- `normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot`
- `normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot`
- `normalizedCoreS2B1TracePackageRemaindersRoot`
- `normalizedCoreCC20PropositionC1SourceCriterionRoot`
- `normalizedSourceObjectBridgeReadOffRowsInputRoot`
- `normalizedSourceObjectScalarRemainderRowsProviderRoot`
- `normalizedSelectedFinitePrimeIndexDifferenceInputRoot`
- `normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsRoot`
- `normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot`
- `normalizedSelectedFinalRouteConcreteCanonicalRoutePackageCoverageRoot`
- `normalizedSelectedFinalRouteCanonicalSquareDataTraceRowsPackageRoot`
- `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`
- `normalizedSelectedFinalRouteCertificateCarrierRoot`

The exact declarations are searchable in
`ConnesWeilRH/Dev/UnconditionalSkeleton.lean` with `rg -n "axiom .*Root"`.

## L657 contract boundary on the current probe carrier

The old unconditional balance contract cannot be repaired by simply supplying
a numerical manifest.  The contract was narrowed so that the scoped equality
is required only when the global prime index set is covered by the restricted
prime index set.  `ConnesWeilRH/Dev/R1Step6Probe984_assembly.lean` now proves,
for the concrete `{2}`-supported bump carrier `W0` and its common test `f0`,

```text
¬ W0.globalPrimeIndexSet ⊆ W0.restrictedPrimeIndexSet 0
```

The reason is that the restricted set is empty at the drained window while the
global carrier contains the visible prime `2`.  Thus the coverage premise is
false.  The new balance proposition is vacuous at `lambda = 0`; this does not
prove that `CommonFinitePrimeArithmeticSourceData W0` is uninhabited.  The
coverage proof is supplied by `L657DiagProbe.probe_coverage_false` and uses only
`[propext, Classical.choice, Quot.sound]`.

The first-principles shape is now:

```text
current CommonFinitePrimeArithmeticSourceData contract
        |
        +-- coverage guard before scoped balance
        +-- drained lambda = 0 is not covered
        v
scoped balance is vacuous at lambda = 0
```

Option 1 implements the contract-scope repair: balance is restricted to covered
windows while the function signatures remain compatible.  A future producer
proof must still supply an actual coverage proof at every lambda where it uses
the balance equality; the drained counterexample cannot be silently reused as
such a proof.

## Consequence for the RH target

The skeleton can serve as a dependency map, but it cannot be used as the final
proof outlet. The first-priority debt is not to generate another owner JSON.
It is to replace the roots that feed the selected route certificate, then
re-run the axiom audit and require exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Until that audit passes for the final route certificate and RH theorem, the
project must continue to report `SourceRH` and RH as unproved.

## Decision

Keep `UnconditionalSkeleton.lean` as a map of obligations. Do not import it
into the production root and do not cite `unconditional_rh_skeleton` as an RH
result. The next implementation target is the first root on the selected
certificate dependency path, but only after the L657 scope/model decision; a
concrete replacement must then pass a fresh axiom audit.
