# Lean Source Interface Map

Status: phase-1 interface map.

This file maps the Lean source-interface names to the public source lines used
by the manuscript. These Lean declarations do not prove CCM24, CCM25, or CC20.
They name the exact theorem-source obligations that the route proof may use.

Current phase-1 Lean declarations use symbolic source-interface statements:

| class | status |
|---|---|
| CCM24 semilocal model, support transport, bounded comparison, and Sonin comparison obligations | expressed over `ConnesWeilRH.SemilocalModelSymbols` |
| CCM25 `QW`, `QW_lambda`, finite-prime, and pole obligations | expressed as formulas over `ConnesWeilRH.WeilFormSymbols` |
| CC20 archimedean trace, trace-class, Mellin, and sign obligations | expressed over `ConnesWeilRH.ArchimedeanTraceSymbols` |
| CC20 finite-vanishing RH exit | expressed as `Nonempty ConnesWeilRH.FiniteVanishingCriterionPackage` |

No source-interface obligation in `ConnesWeilRH/Source` now uses
`statement := True`. These declarations still do not prove the source papers.
They state the contracts that later Lean phases must connect to the analytic
definitions and proofs.

## CCM24

| Lean name | source file | source lines | manuscript role |
|---|---|---|---|
| `ConnesWeilRH.Source.ccm24CanonicalSemilocalModel` | `mainc2m24fine.tex` | `237-253, 786-804` | canonical fixed-S Hilbert model, `V_S=M_S U_S`, and Fourier grading |
| `ConnesWeilRH.Source.ccm24SupportTransport` | `mainc2m24fine.tex` | `761-771, 983-1003` | support and Fourier-support transport for Lemmas A and B |
| `ConnesWeilRH.Source.ccm24BoundedComparison` | `mainc2m24fine.tex` | `806-823` | bounded comparison map with bounded inverse |
| `ConnesWeilRH.Source.ccm24SoninComparison` | `mainc2m24fine.tex` | `1050-1060` | fixed support-window comparison used in exhaustion |

Lean status:

```text
ConnesWeilRH.SemilocalModelSymbols
ConnesWeilRH.SemilocalModelSymbols.CanonicalSemilocalModelStatement
ConnesWeilRH.SemilocalModelSymbols.SupportTransportStatement
ConnesWeilRH.SemilocalModelSymbols.BoundedComparisonStatement
ConnesWeilRH.SemilocalModelSymbols.SoninComparisonStatement
ConnesWeilRH.Source.CCM24Interface.semilocalSymbols
```

These are symbolic semilocal-model interfaces. They do not yet implement the
Hilbert spaces, Fourier grading, support transport maps, bounded operators, or
Sonin comparison from CCM24.

`ConnesWeilRH.SemilocalModelSymbols` now also names
`windowContainedInLambda`. Route-level lambda compatibility can therefore
expose the symbolic `I subset [lambda^(-1), lambda]` leg separately from the
final `lambdaCompatible window lambda` predicate.

## CCM25

| Lean name | source file | source lines | manuscript role |
|---|---|---|---|
| `ConnesWeilRH.Source.ccm25QWDefinition` | `mc2arXiv.tex` | `445-470` | `QW(f,g)=Psi(f^* * g)`, finite-prime terms, archimedean sign, and pole functional |
| `ConnesWeilRH.Source.ccm25QWLambdaFormula` | `mc2arXiv.tex` | `530-540` | restricted `QW_lambda` formula and prime-power operator pairing |
| `ConnesWeilRH.Source.ccm25FinitePrimeNormalization` | `mc2arXiv.tex` | `445-470, 530-540` | finite-prime sign and von Mangoldt normalization |
| `ConnesWeilRH.Source.ccm25PoleNormalization` | `mc2arXiv.tex` | `465-470, 533-535` | pole functional and restricted pole pairing |

Lean status:

```text
ConnesWeilRH.WeilFormSymbols.QWDefinitionStatement
ConnesWeilRH.WeilFormSymbols.PsiSignStatement
ConnesWeilRH.WeilFormSymbols.QWLambdaFormulaStatement
ConnesWeilRH.WeilFormSymbols.FinitePrimeNormalizationStatement
ConnesWeilRH.WeilFormSymbols.FinitePrimeVisibilityStatement
ConnesWeilRH.WeilFormSymbols.PoleNormalizationStatement
```

These are symbolic formula interfaces. They do not yet implement the analytic
test-function space or the actual source distributions.

The finite-prime sums no longer use an empty placeholder index set. The
symbolic CCM25 layer now names `WeilFormSymbols.globalPrimeIndexSet` for the
full `Psi`/`QW` formula and `WeilFormSymbols.restrictedPrimeIndexSet lambda`
for the restricted `QW_lambda` formula. Later phases must replace these fields
with concrete prime-power support definitions.

## CC20

| Lean name | source file | source lines | manuscript role |
|---|---|---|---|
| `ConnesWeilRH.Source.cc20ArchimedeanTraceSquare` | `weil-compo.tex` | `378-387` | archimedean support-square trace formula and `traceequa` |
| `ConnesWeilRH.Source.cc20TraceClassTemplate` | `weil-compo.tex` | `448-464, 2106-2121` | trace-class verification and quantized-calculus trace ideal template |
| `ConnesWeilRH.Source.cc20MellinHalfDensityConvention` | `weil-compo.tex` | `2014-2030` | Mellin/Fourier half-density convention |
| `ConnesWeilRH.Source.cc20FiniteVanishingRhExit` | `weil-compo.tex` | `2072-2085` | finite-vanishing Weil positivity criterion implying RH |
| `ConnesWeilRH.Source.cc20SignsAndNormalizations` | `weil-compo.tex` | `2131-2165` | `u_infty`, `qd u`, and archimedean sign normalization |

Lean status:

```text
ConnesWeilRH.ArchimedeanTraceSymbols
ConnesWeilRH.ArchimedeanTraceSymbols.TraceSquareStatement
ConnesWeilRH.ArchimedeanTraceSymbols.TraceClassTemplateStatement
ConnesWeilRH.ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
ConnesWeilRH.ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
ConnesWeilRH.FiniteVanishingCriterionPackage
ConnesWeilRH.WeilPositivityInput
ConnesWeilRH.Source.CC20Interface.archimedeanSymbols
ConnesWeilRH.Source.CC20Interface.finiteVanishingRhExit
```

The final route theorem consumes
`inputs.cc20.finiteVanishingRhExit.criterion`. This keeps the RH exit inside the
CC20 source interface instead of allowing a route-local certificate to provide
RH directly.

The trace and convention obligations now state the required abstract contract.
They do not yet implement the Hilbert-space operators, trace ideals, or Mellin
transform model from CC20.

## Route Bridges

The final route certificate now carries a source-backed fixed-`S` test:

```text
ConnesWeilRH.Route.SourceBackedFixedSTest
ConnesWeilRH.Route.finite_prime_visibility_statement_of_source_backed
ConnesWeilRH.Route.finite_primes_visible_of_source_backed
ConnesWeilRH.Route.WindowSupportContainment
ConnesWeilRH.Route.window_support_containment_of_source_backed
ConnesWeilRH.Route.admissible_for_theorem1_of_source_backed
ConnesWeilRH.Route.canonical_model_compatibility_of_source_backed
ConnesWeilRH.Route.support_transport_of_source_backed
ConnesWeilRH.Route.bounded_comparison_of_source_backed
ConnesWeilRH.Route.sonin_exhaustion_of_source_backed
ConnesWeilRH.Route.SourceBackedFullPositivity
ConnesWeilRH.Route.SourceTraceReadOffData
ConnesWeilRH.Route.fixed_s_read_off_of_source_trace_data
ConnesWeilRH.Route.cc20_trace_square_of_source_backed
ConnesWeilRH.Route.ccm25_weil_form_read_off_of_source_backed
ConnesWeilRH.Route.fixed_s_read_off_of_source_backed_full_positivity
ConnesWeilRH.Route.full_weil_positivity_of_source_backed
ConnesWeilRH.Route.SourceBackedLedgers
ConnesWeilRH.Route.rank_killed_of_source_backed_ledgers
ConnesWeilRH.Route.pole_killed_of_source_backed_ledgers
ConnesWeilRH.Route.cdef_exhausts_of_source_backed_ledgers
ConnesWeilRH.Route.ledgers_cleared_of_source_backed
ConnesWeilRH.CriticalVanishingPoint
ConnesWeilRH.TripleVanishingSymbols
ConnesWeilRH.TripleVanishingSymbols.TripleVanishingStatement
ConnesWeilRH.Route.triple_vanishing_statement_of_source_backed
ConnesWeilRH.Route.triple_vanishing_of_source_backed
```

`SourceBackedFixedSTest` ties the route-level fixed-`S` test to
`ConnesWeilRH.Source.CCM24Interface.semilocalSymbols`. The final route theorem
derives `AdmissibleForTheorem1` from this bridge instead of accepting a bare
route-local admissibility proof.

Finite-prime visibility now passes through CCM25. `SourceBackedFixedSTest`
carries a Weil test object and a bridge from
`ConnesWeilRH.WeilFormSymbols.FinitePrimeVisibilityStatement` to the route-level
`test.finitePrimesVisible` predicate. The theorem
`finite_prime_visibility_statement_of_source_backed` obtains that statement from
`inputs.ccm25.finitePrimeNormalization`.

Full Weil positivity now passes through a source-backed positivity bridge.
`SourceBackedFullPositivity` carries the fixed-S trace read-off bridge and the
ledger bridge. The theorem
`full_weil_positivity_of_source_backed` obtains the route-level
`FullWeilPositivity` from CC20 trace-class/trace-square contracts, CCM25
Weil-form contracts, source-backed admissibility, and cleared ledgers.

The fixed-S trace read-off bridge is split by `SourceTraceReadOffData`.
It owns the CC20 archimedean test object and its Hilbert-Schmidt gate, then
derives trace legality and the trace-square read-off from
`inputs.cc20.traceClassTemplate` and `inputs.cc20.archimedeanTraceSquare`.
`fixed_s_read_off_of_source_backed_full_positivity` now delegates both the CC20
trace-square leg and the CCM25 Weil-form read-off leg to the fixed-S trace
package.

The CCM25 Weil-form read-off is no longer a loose
`weilFormReadOff : Prop` field on `SourceBackedFullPositivity`.
`ConnesWeilRH.Route.CCM25WeilFormReadOff` records the selected test function,
the restricted parameter `lambda`, `WindowLambdaCompatibility`, the `QW`
definition, the `Psi` sign formula, the restricted `QW_lambda` formula, and
pole normalization. The Theorem 1 segment derives it from
`inputs.ccm25.qwDefinition`, `inputs.ccm25.qwLambdaFormula`, and
`inputs.ccm25.poleNormalization`.

`CCM25WeilFormReadOff` is split into `CCM25FullQWReadOff` and
`CCM25RestrictedQWReadOff`. The full leg comes from `inputs.ccm25.qwDefinition`;
the restricted leg comes from `inputs.ccm25.qwLambdaFormula` and
`inputs.ccm25.poleNormalization`. The full read-off equality source consumes
the full leg, and the restricted read-off equality source consumes the
restricted leg.

The full leg is itself split into `CCM25QWDefinitionReadOff` and
`CCM25PsiSignReadOff`. The restricted leg is split into
`WindowLambdaCompatibility`, `CCM25QWLambdaFormulaReadOff`, and
`CCM25PoleNormalizationReadOff`. This keeps the `QW` definition, the `Psi`
sign convention, the restricted `QW_lambda` formula, and the pole
normalization visible as separate replacement targets.

`WindowLambdaCompatibility` combines the analytic gate `1 < lambda`, the
explicit `WindowSupportContainment` package, and the CCM24 semilocal window
compatibility for the source-backed fixed-`S` test. The containment package
records source support in the CCM24 window, Fourier support in the same window,
convolution-support transport, and `windowContainedInLambda window lambda`.
`lambda_compatible_of_source_backed` derives the final compatibility from
those facts plus Sonin window exhaustion.

The final Weil identification now passes through
`ConnesWeilRH.Route.TraceWeilCompatibility`. That intermediate proposition
combines the CC20 no-defect trace read-off with the CCM25 Weil-form read-off
before `weilIdentificationBridge` derives the final identification used by
`FixedSPositiveTraceReadOff`. It also carries two named read-off equalities:
the CC20 source no-defect trace equals the CCM25 `QW` value, and the CC20
support-square trace equals the restricted CCM25 `QW_lambda` value.

Those equalities are no longer direct fields on `SourceTraceReadOffData`.
`FullTraceReadOffSource` and `RestrictedTraceReadOffSource` name the source
legs, and `fullTraceReadOffBridge` plus `restrictedTraceReadOffBridge` produce
the equalities before `traceWeilCompatibilityBridge` consumes them.
The full bridge now consumes `CC20NoDefectSourceReadOff`; the restricted bridge
now consumes `CCM25WeilFormReadOff`. `SourceTraceReadOffData` no longer carries
arbitrary source-proposition fields for these two read-off legs.
The equality targets are named separately as `FullTraceReadOffEquality` and
`RestrictedTraceReadOffEquality`; `FullTraceReadOffSource` and
`RestrictedTraceReadOffSource` bundle the corresponding source leg with the
corresponding equality.

`FixedSPositiveTraceReadOff` is no longer an alias for
`AdmissibleForTheorem1`. It is an existential proposition requiring separate
evidence for trace legality, no-defect source read-off, Weil identification, and
positive-trace nonnegativity. This keeps Theorem 1's hypotheses and its
positive-trace output distinct in the Lean route.

Ledger clearing now passes through `SourceBackedLedgers`. Rank clearing is
bridged from CCM24 bounded comparison plus CC20 sign normalization. Pole
clearing is bridged from CCM25 pole normalization. Cdef exhaustion is bridged
from CCM24 Sonin comparison plus CC20 Mellin convention. The resulting
`LedgersCleared` proof is obtained by `ledgers_cleared_of_source_backed`.

Triple vanishing now uses the explicit finite type `CriticalVanishingPoint`,
with constructors `zero`, `half`, and `one`. `TripleVanishingSymbols` records
vanishing at those three points, and `triple_vanishing_of_source_backed` obtains
the route-level `test.tripleVanishing` predicate through an explicit bridge on
`SourceBackedFixedSTest`.

## Audit Rule

The final Connes-Weil theorem may depend on these source-interface obligations
only if the dependency appears in `#print axioms` or in an explicit hypothesis
list. No route module may hide extra project-local assumptions.
