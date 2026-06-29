2026-06-30

- Continued Goal 4J by adding a normalized-seed constructor for expanded source
  rows.
- Updated `ConnesWeilRH/Source/ObjectExpandedRows.lean`.
- Added `SourceObjectExpandedRows.normalizedCC20SupportSquareComparison`,
  which packages the reflexive support-square comparison for
  `normalizedSeedTraceObjectPackage`.
- Added `SourceObjectExpandedRows.ofNormalizedCC20Trace`, which builds
  `SourceObjectExpandedRows` from a CCM24 row, a normalized CC20 trace seed,
  and CC20 trace remainder data, with `cc20Trace` set to
  `normalizedSeedTraceObjectPackage` and `cc20SupportSquareComparison` filled
  by construction.
- Added read-offs
  `of_normalized_cc20_trace_cc20_trace_eq` and
  `of_normalized_cc20_trace_support_square_comparison`.
- Boundary preserved: this proves the support-square witness for
  normalized-seed-constructed expanded rows. It does not identify an arbitrary
  manuscript/source `CC20TraceObjectPackage` with that normalized constructor.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.ObjectExpandedRows`, followed by
  `lake build ConnesWeilRH.Route.FixedTestFrontEnd
  ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.

2026-06-30

- Continued Goal 4J by tying the support-square comparison witness to the
  expanded source-object row package used by the route.
- Updated `ConnesWeilRH/Source/ObjectExpandedRows.lean`.
- Imported `ConnesWeilRH.Source.CC20Concrete.TraceScale` and added
  `SourceObjectExpandedRows.cc20SupportSquareComparison :
  CC20TracePackageSupportSquareComparison cc20Trace`.
- Added row-level read-offs:
  `SourceObjectExpandedRows.cc20_support_square_comparison` and
  `SourceObjectExpandedRows.cc20_support_square_existing_identification`.
- Added package-of-data read-offs:
  `SourceObjectPackageOfData.cc20_support_square_comparison` and
  `SourceObjectPackageOfData.cc20_support_square_existing_identification`,
  showing the same witness reaches the `cc20Trace` field of
  `sourceObjectPackageOfData`.
- Boundary preserved: this prevents support-square witness drift between
  expanded rows and the route package path. It still does not prove the
  witness from analytic CC20 trace definitions.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.ObjectExpandedRows`, followed by
  `lake build ConnesWeilRH.Route.FixedTestFrontEnd
  ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.

2026-06-29

- Continued Goal 4J by splitting the first existing-package comparison target
  out of the full normalized-seed comparison surface.
- Updated `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added `CC20TracePackageSupportSquareComparison`, a data-bearing witness for
  only the support-square trace comparison between an existing
  `SourceObject.CC20TraceObjectPackage` and a normalized-seed-constructed
  package.
- Added the reflexive constructor
  `CC20TracePackageSupportSquareComparison.forNormalizedSeedTraceObjectPackage`
  and support-square projections for the constructed and existing package legs.
- Added
  `CC20TracePackageNormalizedSeedComparison.supportSquareComparison` and
  `CC20TracePackageNormalizedSeedComparison.ofSupportSquareComparison`, so the
  full comparison can consume the support-square proof only when the remaining
  no-defect trace, positive trace, and Hilbert-Schmidt gate comparisons are
  supplied separately.
- Boundary preserved: this is a narrower implementable target for the first
  real source comparison field. It does not prove that an existing
  manuscript/source CC20 package matches the normalized seed.
- WSL ext4 narrow verification passed after syncing from the Windows source of
  truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale`.

2026-06-29

- Continued Goal 4J by completing the current trace-scale comparison surface.
- Updated `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added
  `CC20TracePackageNormalizedSeedComparison.forNormalizedSeedTraceObjectPackage`,
  which fills the comparison record by reflexivity for packages constructed
  from the normalized seed.
- Added comparison projections:
  `existing_source_no_defect_trace_identification`,
  `existing_positive_trace_identification`,
  `existing_hilbert_schmidt_gate_identification`, and
  `normalized_package_support_square_trace_identification`.
- The comparison interface now exposes named projections for support-square
  trace, source no-defect trace, positive trace, and Hilbert-Schmidt gate.
- Updated the ignored local plan and root `AGENTS.md` with the boundary:
  these projections prove comparison fields only for normalized-seed-constructed
  packages unless an existing package supplies the comparison fields.
- Next target remains proving `supportSquareTrace_eq` for an actual existing
  `CC20TraceObjectPackage`.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  ConnesWeilRH.Source.CC20Concrete ConnesWeilRH`.

2026-06-29

- Continued Goal 4J by adding an existing-package comparison interface.
- Updated `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added `normalizedSeedTraceObjectArchimedeanSymbols` to avoid fragile
  projection chains when comparing a normalized-seed-constructed package with
  an existing package.
- Added `CC20TracePackageNormalizedSeedComparison`, a data-bearing record that
  compares an arbitrary existing `CC20TraceObjectPackage` against a
  normalized-seed-constructed package.
- The comparison record currently names fields for support-square trace, source
  no-defect trace, positive trace, and Hilbert-Schmidt gate equality.
- Added projections:
  `CC20TracePackageNormalizedSeedComparison.constructedIdentification`,
  `constructed_support_square_trace_identification`, and
  `existing_support_square_trace_identification`.
- Updated the ignored local plan and root `AGENTS.md` with the boundary:
  this records the comparison fields but does not prove them from source
  definitions. The first concrete proof target is `supportSquareTrace_eq` for an
  actual existing CC20 package.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  ConnesWeilRH.Source.CC20Concrete ConnesWeilRH`.

2026-06-29

- Continued Goal 4J by adding a source-backed normalized CC20 trace package
  constructor.
- Updated `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added `CC20TracePackageRemainderData` to isolate the CC20 trace package
  fields not supplied by the normalized trace-scale seed: trace-test
  compatibility, operator identity, global Hilbert-Schmidt gate evidence,
  per-move cyclicity ledger, no-defect read-off marker, remainder orientation,
  post-`Q` transport, projection-defect normal form, rank/pole ledger
  identification, endpoint-strip `Cdef` domination, no-hidden-positive-defect,
  and trace-ideal transport.
- Added `normalizedSeedTraceObjectPackage`, which builds a real
  `SourceObject.CC20TraceObjectPackage` from
  `NormalizedLegalSquareTraceScaleSymbols` plus `CC20TracePackageRemainderData`.
- Added `normalizedSeedIdentificationForTraceObjectPackage`, filling the
  source-identification interface by reflexivity for packages constructed from
  the normalized seed.
- Added `normalized_seed_trace_object_support_square_identification` as a
  concrete read-off of the reflexive support-square trace identification.
- Updated the ignored local plan and root `AGENTS.md` with the boundary:
  this proves identification for normalized-seed-constructed packages only. It
  does not prove that an existing manuscript/source CC20 package is such a
  package.
- Next target recorded: prove a source comparison theorem, or named equality
  fields, showing the existing CC20 package's trace functions and gates match
  the normalized seed definitions.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  ConnesWeilRH.Source.CC20Concrete ConnesWeilRH`.

2026-06-29

- Continued Goal 4J by adding the source-identification interface from a real
  `CC20TraceObjectPackage` to the normalized concrete trace-scale seed.
- Updated `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added helper projections:
  `normalizedSeedConcreteSymbols`, `normalizedSeedSupportSquareTrace`,
  `normalizedSeedSourceNoDefectTrace`, `normalizedSeedPositiveTrace`,
  `normalizedSeedTraceClass`, `normalizedSeedCyclicLegal`, and
  `normalizedSeedHilbertSchmidtGate`.
- Added `CC20TracePackageNormalizedSeedIdentification`, a data-bearing record
  with named `HEq` fields for the test type, support-square trace, source
  no-defect trace, positive trace, trace-class predicate, cyclicity predicate,
  Hilbert-Schmidt gate, Mellin convention, and sign normalization fields.
- Added constructor/read-off projections:
  `CC20TracePackageNormalizedSeedIdentification.toCC20TraceModel`,
  `to_cc20_trace_model_trace_square`,
  `to_cc20_trace_model_trace_class_template`,
  `to_cc20_trace_model_ordinary_trace_support_square`,
  `support_square_trace_identification`,
  `positive_trace_identification`, and
  `hilbert_schmidt_gate_identification`.
- Updated the ignored local plan and root `AGENTS.md` with the boundary:
  this interface records the source-identification equalities. It does not
  prove them from CC20 definitions.
- Next target recorded: prove at least one identification field from concrete
  CC20 definitions, or replace a component with a source-backed constructor
  where the equality is definitional.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  ConnesWeilRH.Source.CC20Concrete ConnesWeilRH`.

2026-06-29

- Continued Goal 4J by adding a normalized no-proof-input CC20 trace-model
  seed.
- Updated `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added `CC20Concrete.TraceScale.NormalizedLegalSquareTraceScaleSymbols`, which
  fixes `mellinHalfDensityMatched`, `uInfinityNormalized`, `qduNormalized`, and
  `archimedeanSignNormalized` to `True`.
- Added
  `NormalizedLegalSquareTraceScaleSymbols.mellin_half_density_convention` and
  `NormalizedLegalSquareTraceScaleSymbols.signs_and_normalizations`.
- Added `normalizedLegalSquareTraceScaleToCC20TraceModel`, a constructor that
  builds a `CC20TraceModel` from the normalized concrete seed with no proof
  arguments.
- Added read-offs:
  `normalized_legal_square_trace_scale_to_cc20_trace_model_trace_square`,
  `normalized_legal_square_trace_scale_to_cc20_trace_model_trace_class_template`,
  `normalized_legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square`,
  `normalized_legal_square_trace_scale_to_cc20_trace_model_mellin`, and
  `normalized_legal_square_trace_scale_to_cc20_trace_model_signs`.
- Updated the ignored local plan and root `AGENTS.md` with the boundary:
  this discharges the CC20 trace-model rows only for the normalized seed. It
  does not identify the actual CC20 source operators or conventions with that
  seed.
- Next target recorded: add a source-identification interface from the real
  `CC20TraceObjectPackage` to `NormalizedLegalSquareTraceScaleSymbols`, with
  named equalities for support-square trace, no-defect trace, positive trace,
  Hilbert-Schmidt gate, Mellin convention, and sign normalization.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  ConnesWeilRH.Source.CC20Concrete ConnesWeilRH`.

2026-06-29

- Continued Goal 4J by adding a concrete trace-class/cyclicity legal-gate seed.
- Updated `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added `CC20Concrete.TraceScale.LegalSquareTraceScaleSymbols`, where
  `hilbertSchmidtGate g := traceClass g ∧ cyclicLegal g`.
- Added `LegalSquareTraceScaleSymbols.trace_class_template_statement`, proving
  the trace-class/cyclicity template by projecting the legal-gate pair.
- Added `LegalSquareTraceScaleSymbols.trace_square_statement`, reusing the
  square-form positivity seed.
- Added `legalSquareTraceScaleToCC20TraceModel`, which constructs a
  `CC20TraceModel` without taking positive-trace nonnegativity or
  trace-class/cyclicity as inputs.
- Added read-offs:
  `legal_square_trace_scale_to_cc20_trace_model_trace_square`,
  `legal_square_trace_scale_to_cc20_trace_model_trace_class_template`, and
  `legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square`.
- Updated the ignored local plan and root `AGENTS.md` with the boundary:
  this proves the template only for the concrete legal-gate seed. It does not
  prove that the actual CC20 Hilbert-Schmidt gate is this legal gate, and it
  does not discharge Mellin convention, signs/normalizations, or source
  identification of the CC20 operator trace.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  ConnesWeilRH.Source.CC20Concrete ConnesWeilRH`.

2026-06-29

- Continued Goal 4J by adding a square-form positive-trace seed.
- Updated `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added `CC20Concrete.TraceScale.SquareTraceScaleSymbols`, where
  `supportSquareTrace g := traceAmplitude g ^ 2`.
- Added `SquareTraceScaleSymbols.positive_trace_nonnegative_statement`, proving
  the positive-trace nonnegativity row by `sq_nonneg` for the square-form seed.
- Added `SquareTraceScaleSymbols.trace_square_statement`, combining the
  existing scalar read-off with the square-form nonnegativity theorem.
- Added `squareTraceScaleToCC20TraceModel`, which constructs a `CC20TraceModel`
  from square-form data without taking positive-trace nonnegativity as an input.
- Added read-offs:
  `square_trace_scale_to_cc20_trace_model_trace_square` and
  `square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square`.
- Updated the ignored local plan and root `AGENTS.md` with the boundary:
  this proves nonnegativity only for the square-form concrete seed. It still
  does not prove trace-class/cyclicity, Mellin convention, signs/normalizations,
  or source identification of the actual CC20 operator trace with this scalar.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  ConnesWeilRH.Source.CC20Concrete ConnesWeilRH`.

2026-06-29

- Started Goal 4J with a concrete CC20 trace-scale seed.
- Added `ConnesWeilRH/Source/CC20Concrete/TraceScale.lean`.
- Added `ConnesWeilRH/Source/CC20Concrete.lean` and imported it from
  `ConnesWeilRH.lean`.
- Introduced `CC20Concrete.TraceScale.ConcreteTraceScaleSymbols`, where
  `sourceNoDefectTrace` and `positiveTrace` are definitionally the same scalar
  family as `supportSquareTrace`.
- Proved concrete scalar read-offs:
  `ConcreteTraceScaleSymbols.ordinary_trace_support_square_statement` and
  `ConcreteTraceScaleSymbols.support_square_no_defect_statement`.
- Added `ConcreteTraceScaleSymbols.trace_square_statement_of_nonnegative`,
  which derives the full CC20 trace-square statement only after an explicit
  positive-trace nonnegativity input.
- Added `toCC20TraceModel`,
  `to_cc20_trace_model_ordinary_trace_support_square`, and
  `to_cc20_trace_model_trace_square` so the existing `CC20TraceModel` path can
  be filled from concrete trace-scale definitions for these scalar rows.
- Updated the ignored local plan and root `AGENTS.md` to record the boundary:
  this is a concrete definition seed, not full CC20 archimedean operator
  discharge. Positive-trace nonnegativity, trace-class/cyclicity, Mellin
  convention, and signs/normalizations remain explicit inputs.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20Concrete.TraceScale
  ConnesWeilRH.Source.CC20Concrete ConnesWeilRH`.

2026-06-29

- Completed Goals 4H and 4I as source-interface scalar replacements.
- First committed and pushed the previous Goal 4D-G milestone:
  `56532c6728b54139e240df30332789b6011dfdda`
  (`Name CC20 ordinary trace support-square row`), with a good local GPG
  signature and matching `origin/main`.
- Updated `ConnesWeilRH/Route/TraceFrontEnd.lean`.
- Added `no_defect_qw_lambda_theorem_data_of_source_trace_square`, which fills
  the support-square trace equals source no-defect trace leg from
  `cc20_trace_square_of_source_trace_data`.
- Added read-offs:
  `support_square_no_defect_source_interface_holds` and
  `no_defect_qw_lambda_source_trace_square_keeps_qw_lambda_obligation`.
- Added `cc20_no_defect_qw_lambda_theorem_data_of_source_interface`, which
  composes the CC20 no-defect read-off with
  `restricted_trace_read_off_of_source_trace_data` to prove source no-defect
  trace equals restricted `QW_lambda`.
- Added package-facing read-offs:
  `no_defect_qw_lambda_theorem_data_of_source_interface`,
  `support_square_no_defect_source_interface_full_holds`, and
  `no_defect_qw_lambda_source_interface_holds`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark Goals 4H/4I complete only at source-interface route
  composition level.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH`.
- Boundary preserved: Goals 4H/4I remove free theorem-data fields for the
  S2-B1 scalar path, but they still depend on source-interface rows. The next
  proof-bearing targets are replacing `CC20TraceModel.ordinaryTraceSupportSquare`,
  the CC20 trace-square row, and the restricted trace read-off row with
  concrete Lean definition theorems or accepted Lean imports.

2026-06-29

- Completed Goal 4G at the named source-interface row level.
- Inspected `ArchimedeanTraceSymbols`, `CC20TraceObjectPackage`,
  `SourceObjectPackage.provesTraceSquareStatement`, and the CC20 compact
  interface path.
- Updated `ConnesWeilRH/Basic.lean`.
- Added `ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement`, stating
  `positiveTrace g = supportSquareTrace g` under the same trace-class and
  cyclicity hypotheses used by the route.
- Updated `ConnesWeilRH/Source/Objects.lean`.
- Replaced the loose `sourceOrdinaryPositiveTrace : Prop` field on
  `CC20TraceObjectPackage` with data-bearing
  `sourceOrdinaryTraceSupportSquare :
  ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
  archimedeanSymbols`.
- Updated `ConnesWeilRH/Source/ObjectDerivations.lean` with
  `SourceObjectPackage.provesOrdinaryTraceSupportSquareStatement`.
- Updated `ConnesWeilRH/Source/CC20.lean` with the source obligation
  `cc20OrdinaryTraceSupportSquare`, the compact interface field
  `CC20Interface.ordinaryTraceSupportSquare`, the source-object-backed theorem
  `SourceObjectBackedCC20Interface.ordinary_trace_support_square`, and the
  `CC20Interface.ofSourceObjectPackage` projection.
- Updated `ConnesWeilRH/Source/CC20TraceModel.lean` and
  `ConnesWeilRH/Source/CC20TheoremBase.lean` so the theorem-base path carries
  the ordinary/support-square row explicitly.
- Updated `ConnesWeilRH/Route/TraceFrontEnd.lean` with
  `ordinary_trace_support_square_theorem_data_of_source_interface` and
  `ordinary_trace_support_square_source_interface_holds`, so Goal 4E can be
  filled from the compact CC20 source interface instead of a generic Prop.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark Goal 4G complete at source-interface level and set Goal
  4H/4I/4J as the next targets.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CC20TraceModel
  ConnesWeilRH.Source.CC20TheoremBase ConnesWeilRH.Source.CC20
  ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH`.
- Boundary preserved: Goal 4G removes the generic ordinary-trace Prop gap, but
  it is still source-conditional. The new row must later be filled from concrete
  CC20 definitions or an accepted Lean import before it counts as analytic
  discharge.

2026-06-29

- Continued the S2-B1 theorem replacement path after Goals 4D/E/F.
- Inspected the CC20 trace interface in `ConnesWeilRH/Route/Theorem1.lean` and
  `ConnesWeilRH/Source/Objects.lean`.
- Current evidence: `CC20TraceObjectPackage.sourceSupportSquareTraceReadOff`
  proves support-square trace equals source no-defect trace under trace-class
  and cyclicity evidence, and `sourcePositiveTraceNonnegative` proves positivity,
  but there is not yet a Lean theorem field proving ordinary positive trace is
  the same finite-lambda scalar as support-square trace.
- Updated `ConnesWeilRH/Route/TraceFrontEnd.lean`.
- Added `CC20OrdinaryTraceSupportSquareTheoremData`, tying the missing ordinary
  trace to support-square trace theorem to the exact `SourceTraceReadOffData`,
  `CC20TraceLegality`, and `CC20TraceSquareReadOff` used by the route.
- Added `ordinary_trace_support_square_theorem_data_of_cc20` plus read-offs:
  `ordinary_trace_support_square_constructor_uses_cc20_statement` and
  `ordinary_trace_support_square_constructor_holds`.
- Added `CC20NoDefectQWLambdaTheoremData`, tying the support-square/no-defect
  and no-defect/`QW_lambda` theorem legs to the exact trace-square read-off and
  restricted trace read-off source used by the route.
- Added `no_defect_qw_lambda_theorem_data_of_cc20` plus read-offs:
  `no_defect_qw_lambda_constructor_uses_support_square_statement` and
  `no_defect_qw_lambda_constructor_uses_qw_lambda_statement`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to set the next target as Goal 4G: prove or import the exact
  ordinary-positive-trace equals support-square-trace theorem for the same
  `SourceTraceReadOffData`.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH`.
- Axiom audit for the new source-shaped Goal 4G interface constructors reported
  only `[propext, Classical.choice, Quot.sound]`.
- Weak-placeholder scan over the touched route Lean files found no `sorry`,
  `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`, `.choose`,
  `choose_spec`, or `exists row, True` shells. The only match for `axiom` was
  the word `axioms` in the `RouteTheorem.lean` module comment.
- Boundary preserved: this is still theorem-interface replacement, not analytic
  discharge. The ordinary/support-square equality remains an explicit theorem
  obligation until filled from concrete CC20 definitions or accepted Lean import.

2026-06-29

- Completed Goals 4D/E/F as constructor/read-off staging for the S2-B1
  trace-scale path.
- Updated `ConnesWeilRH/Route/TraceFrontEnd.lean`.
- Added `OrdinaryTraceSupportSquareTheoremData`, which isolates the first S2-B1
  scalar leg: ordinary positive trace equals support-square trace.
- Added `NoDefectQWLambdaTheoremData`, which isolates the next two S2-B1 scalar
  legs: support-square trace equals no-defect source trace, and no-defect source
  trace equals `QW_lambda`.
- Added `trace_scale_no_missing_bulk_of_scalar_theorem_data` plus read-offs:
  `ordinary_trace_matches_support_square_of_scalar_theorem_data`,
  `ordinary_trace_support_square_theorem_holds`,
  `support_square_matches_no_defect_of_scalar_theorem_data`,
  `no_defect_matches_qw_lambda_of_scalar_theorem_data`,
  `support_square_no_defect_theorem_holds`, and
  `no_defect_qw_lambda_theorem_holds`.
- Updated `ConnesWeilRH/Route/RouteTheorem.lean`.
- Added `TraceScaleRouteFrontEndData.ofTraceData`, which builds the Goal 4D
  route-front-end data from a `TraceFrontEndData` object, route ledgers,
  common-tuple evidence, sign/defect classification, trace-scale ownership of
  the sign/defect remainder, restricted-to-full evidence, and final sign bridge
  source evidence.
- Added route/certificate constructors:
  `route_front_end_of_trace_scale_data`,
  `route_certificate_of_trace_scale_data`,
  `route_front_end_of_package_data`, and
  `route_certificate_of_package_data`.
- Added route/certificate read-offs:
  `of_trace_data_trace_scale_matches_trace_data`,
  `route_certificate_of_trace_scale_data_ledgers`, and
  `route_certificate_of_trace_scale_data_source_backed_test`.
- Updated root `AGENTS.md` to mark Goals 4D/E/F complete as staging and to set
  the next proof-bearing slice: replace one theorem-data field with an actual
  Lean theorem from CC20/CCM25 source definitions or accepted Lean imports,
  starting with ordinary positive trace equals support-square trace.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.
- Axiom audit for the Goal 4D/E/F constructors and read-offs reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak-placeholder scan over the touched Goal 4D/E/F Lean files found no
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`,
  `.choose`, `choose_spec`, or `exists row, True` shells. The only match for
  `axiom` was the word `axioms` in the `RouteTheorem.lean` module comment.
- Boundary preserved: Goals 4D/E/F do not prove the S2-B1 analytic scalar
  equalities. They split and route the obligations so later theorem replacement
  cannot skip ordinary trace/support-square/no-defect/`QW_lambda` compatibility.

2026-06-29

- Completed Goal 4C as a structured S2-B1 trace-scale obligation layer.
- Updated `ConnesWeilRH/Route/TraceFrontEnd.lean`.
- Added `TraceScaleNoMissingBulkData`, which names the ordinary trace to
  support-square scalar, support-square to no-defect source scalar, no-defect to
  `QW_lambda` scalar, rank/pole/`Cdef` ownership, and no-extra-bulk obligations.
- Replaced the loose `s2b1NoMissingBulkTarget : Prop` marker on
  `TraceFrontEndData` with a data-bearing `traceScaleNoMissingBulk` field tied
  to the same package, fixed-test front end, `lambda`, and CCM25 arithmetic
  package.
- Added Goal 4C read-offs:
  `trace_scale_no_missing_bulk`,
  `trace_scale_no_missing_bulk_ordinary_trace`,
  `trace_scale_no_missing_bulk_support_square`,
  `trace_scale_no_missing_bulk_no_defect_qw_lambda`,
  `trace_scale_no_missing_bulk_rank_pole_cdef`,
  `trace_scale_no_missing_bulk_no_extra_bulk`, and
  `trace_scale_no_missing_bulk_no_extra_bulk_holds`.
- Updated `ConnesWeilRH/Route/RouteTheorem.lean`.
- Added `TraceScaleRouteFrontEndData`, which makes the next route-front-end
  staging consume the same `TraceScaleNoMissingBulkData` as the trace front end
  before producing `ExpandedSourceRouteCertificateFrontEnd`.
- Added route-front-end read-offs:
  `toExpandedSourceRouteCertificateFrontEnd`,
  `route_front_trace_scale_matches_trace_data`,
  `route_front_no_extra_bulk`,
  `route_front_trace_scale_owns_sign_defect`,
  `route_front_ledgers`, and
  `route_front_sign_defect_classification`.
- Updated `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark Goal 4C complete and set Goal 4D as the next target:
  make sign/defect front-end construction consume `TraceScaleRouteFrontEndData`,
  then replace S2-B1 fields with proved Lean theorem constructors one scalar
  class at a time.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Route.TraceFrontEnd ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.
- Axiom audit for the Goal 4C read-offs and route-front staging constructor
  reported only `[propext, Classical.choice, Quot.sound]`.
- Weak-placeholder scan over the touched Goal 4C Lean files found no `sorry`,
  `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`, `.choose`,
  `choose_spec`, or `exists row, True` shells. The only match for `axiom` was
  the word `axioms` in the `RouteTheorem.lean` module comment.
- Boundary preserved: Goal 4C is structured obligation/read-off staging only.
  It does not prove the S2-B1 analytic scalar equalities, sign/defect,
  restricted-to-full, route certificate closure, or unconditional RH.

2026-06-29

- Completed Goal 4A/B trace-front-end data construction and trace tuple
  read-offs.
- Added `ConnesWeilRH/Route/TraceFrontEnd.lean` and imported it from
  `ConnesWeilRH.lean`.
- Added `TraceFrontEndData`, which carries the fixed `lambda`, CCM25 concrete
  arithmetic package, `TestAndQuotientCompatibility`,
  `FixedSQuantizedSupportSquareTransport`, full trace read-off bridge,
  restricted trace read-off bridge, and an explicit `s2b1NoMissingBulkTarget`
  field.
- Added `TraceFrontEndData.toExpandedSourceTraceReadOffFrontEnd` and
  `TraceFrontEndData.toSourceTraceReadOffData`.
- Added generic trace-front-end read-offs:
  `trace_front_lambda`, `trace_front_arithmetic_package`,
  `source_trace_archimedean_test`, `source_trace_lambda`,
  `source_trace_arithmetic_package`,
  `source_trace_test_and_quotient_compatibility`,
  `source_trace_support_square_transport`,
  `source_trace_full_trace_bridge`,
  `source_trace_restricted_trace_bridge`, and
  `source_trace_weil_test_eq_fixed_front`.
- Added package-data specializations:
  `toExpandedSourceTraceReadOffFrontEndOfPackageData`,
  `toSourceTraceReadOffDataOfPackageData`,
  `package_data_source_trace_archimedean_test`,
  `package_data_source_trace_lambda`,
  `package_data_source_trace_arithmetic_package`, and
  `package_data_source_trace_weil_test_eq_common`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark Goal 4A/B complete and set Goal 4C as the next
  proof-bearing slice: name S2-B1 no-missing-bulk as an explicit trace-scale
  obligation separate from trace legality and positive trace nonnegativity.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Route.TraceFrontEnd` and
  `lake build ConnesWeilRH`.
- Axiom audit for the Goal 4A/B constructor and read-offs reported only
  `[propext, Classical.choice, Quot.sound]`.
- Boundary preserved: Goal 4A/B constructs and checks trace-front-end data
  flow, but it does not prove trace legality, support-square transport,
  full/restricted trace read-off, S2-B1 no-bulk, sign/defect,
  restricted-to-full, route certificate, or unconditional RH.

2026-06-29

- Completed Goal 3B/C/D fixed-test front-end staging and made the route ready
  for the trace-front-end stage.
- Added `ConnesWeilRH/Route/FixedTestFrontEnd.lean` and imported it from
  `ConnesWeilRH.lean`.
- Added `FixedSTestObligationData`, which carries named fixed-test obligations
  plus tuple-consistency read-offs for the package common test, CCM24 source
  leg, CCM24 support window, and CCM25 symbols.
- Added Goal 3B constructors/read-offs:
  `FixedSTestObligationData.toFixedSTestFrontEndData`,
  `FixedSTestObligationData.toExpandedSourceFixedSTestFrontEnd`,
  `source_backed_weil_test_eq_common_test`,
  `source_backed_semilocal_test_eq_source_leg`,
  `source_backed_window_eq_source_window`, and
  `source_backed_ccm25_symbols_eq_package`.
- Added Goal 3C finite-prime visibility bridge:
  `finite_prime_visibility_statement_of_concrete_arithmetic_rows` and
  `finite_primes_visible_of_concrete_arithmetic_rows`, deriving visibility from
  the concrete CCM25 arithmetic rows attached to `pkg.commonTest.sourceTest`.
- Added Goal 3D triple-vanishing and package-data readiness read-offs:
  `triple_vanishing_of_obligation_data`,
  `admissible_for_theorem1_of_obligation_data`,
  `source_backed_triple_vanishing_of_obligation_data`,
  `source_backed_admissible_for_theorem1_of_obligation_data`,
  `toExpandedSourceFixedSTestFrontEndOfPackageData`,
  `package_data_source_backed_weil_test_eq_common`,
  `package_data_source_backed_window_eq_source_window`,
  `package_data_finite_prime_visibility_statement`, and
  `package_data_admissible_for_theorem1`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark Goal 3B/C/D complete and set Goal 4A trace-front-end data
  construction as the next proof-bearing slice.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Route.FixedTestFrontEnd` and
  `lake build ConnesWeilRH`.
- Axiom audit for the Goal 3B/C/D constructors and read-offs reported only
  `[propext, Classical.choice, Quot.sound]`.
- Boundary preserved: Goal 3 now prevents fixed-test tuple drift and derives
  fixed-test finite-prime visibility from concrete CCM25 arithmetic rows, but
  it does not prove trace legality, support-square transport, S2-B1 no-bulk,
  sign/defect, restricted-to-full, route certificate, or unconditional RH.

2026-06-29

- Completed Goal 3A fixed-test front-end data construction.
- Updated `ConnesWeilRH/Route/Definitions.lean`.
- Added `FixedSTestFrontEndData`, which carries the explicit fixed-test
  obligations needed to construct `ExpandedSourceFixedSTestFrontEnd`:
  admissible window evidence, triple-vanishing bridge/source evidence, and the
  finite-prime visibility bridge pinned to `pkg.commonTest.sourceTest`.
- Added `FixedSTestFrontEndData.toExpandedSourceFixedSTestFrontEnd` and
  read-offs:
  `test_of_expanded_source_fixed_test_front_end`,
  `triple_vanishing_symbols_of_expanded_source_fixed_test_front_end`, and
  `finite_prime_visibility_bridge_of_expanded_source_fixed_test_front_end`.
- Added downstream `SourceBackedFixedSTest` read-offs for Goal 3A:
  `weil_test_of_fixed_test_front_end_data`,
  `semilocal_window_of_fixed_test_front_end_data`, and
  `finite_prime_visibility_bridge_of_fixed_test_front_end_data`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark Goal 3A complete and set Goal 3B as the next
  proof-bearing slice: admissibility and tuple-consistency read-offs from the
  constructed source-object package and explicit fixed-test obligation data.
- Windows-side `lake` is not available, so verification ran from the WSL ext4
  mirror after syncing `ConnesWeilRH/Route/Definitions.lean` from the Windows
  source of truth.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Definitions` and
  `lake build ConnesWeilRH`.
- Axiom audit for the Goal 3A constructor/read-offs reported only
  `[propext, Classical.choice, Quot.sound]`.
- Boundary preserved: Goal 3A is a constructor/read-off slice. It does not
  prove the admissible window, triple vanishing, finite-prime visibility,
  trace front end, route certificate, or unconditional RH.

2026-06-29

- Completed Goal 2D as an explicit data-driven `SourceObjectPackage`
  constructor.
- Extended `ConnesWeilRH/Source/ObjectExpandedRows.lean`.
- Added `SourceObjectCrossObjectBridges`, which carries the remaining
  cross-object bridge data needed by `SourceObjectPackage`: RH-definition
  bridge equality to the base package, common-test involution, CCM24 common-test
  bridge, CC20 common-test bridge, convolution-square/F_g bridge, window
  controls, finite-prime support/window matching, and final sign bridge.
- Added read-offs:
  `SourceObjectCrossObjectBridges.ccm25_source_test_eq_arithmetic_rows` and
  `SourceObjectCrossObjectBridges.rh_definition_bridge_eq_base`.
- Added `sourceObjectPackageOfData`, constructing
  `SourceObject.SourceObjectPackage` from `SourceObjectTheoremBasePackage`,
  `SourceObjectCommonData`, `SourceObjectExpandedRows`, an expanded
  `SourceObject.CC20RHExitObjectPackage`, and
  `SourceObjectCrossObjectBridges`.
- Added package-constructor read-offs:
  `SourceObjectPackageOfData.ccm25_eq_rows`,
  `SourceObjectPackageOfData.commonTest_eq_common`,
  `SourceObjectPackageOfData.ccm25_source_test_eq_arithmetic_rows`,
  `SourceObjectPackageOfData.finite_prime_normalization`, and
  `SourceObjectPackageOfData.rh_definition_bridge_eq_base`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark Goal 2D complete and set Goal 3 fixed-test front-end
  construction as the next proof-bearing slice.
- WSL ext4 verification passed after syncing touched files from the Windows
  source of truth:
  `lake build ConnesWeilRH.Source.ObjectExpandedRows` and
  `lake build ConnesWeilRH`.
- Axiom audit for `sourceObjectPackageOfData`, the package-constructor
  read-offs, and the new cross-object bridge read-off reported only
  `[propext, Classical.choice, Quot.sound]`.
- Boundary preserved: Goal 2D constructs `SourceObjectPackage` from explicit
  data, but it does not construct the bridge data without assumptions, does not
  prove CCM24/CC20 analytic object witnesses from first principles, does not
  construct a route front end or `RouteCertificate`, and does not prove RH
  unconditionally.

2026-06-29

- Completed Goal 2C for the CCM25 concrete-consumption slice.
- Added `ConnesWeilRH/Source/ObjectExpandedRows.lean` and imported it from
  `ConnesWeilRH.lean`.
- Added `SourceObjectCommonData`, which carries a `CommonTestObject`, concrete
  CCM25 arithmetic rows, and the equality tying the common CCM25 source test to
  `CCM25Concrete.Rows.source_test_of_arithmetic_rows`.
- Added `SourceObjectCommonData.toCCM25WeilObjectPackage`,
  `finite_prime_normalization`, `toFinitePrimeTheoremBase`,
  `toPartialQWFinitePrime`, and
  `toCCM25TheoremBaseWithConcreteFinitePrime`; these make the expanded CCM25
  row consume Goal 0E finite-prime normalization through concrete arithmetic
  rows.
- Added `SourceObjectExpandedRows`, with CCM24 and CC20 trace rows kept as
  explicit inputs and the CCM25 row computed from `SourceObjectCommonData`
  rather than accepted as an independent field.
- Added read-offs:
  `SourceObjectExpandedRows.ccm25_source_test_eq_arithmetic_rows`,
  `SourceObjectExpandedRows.finite_prime_normalization`, and
  `SourceObjectExpandedRows.toPartialQWFinitePrime`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark the Goal 2C CCM25 slice complete and set Goal 2D as the
  next proof-bearing target.
- WSL ext4 verification passed after syncing touched files from the Windows
  source of truth:
  `lake build ConnesWeilRH.Source.ObjectExpandedRows` and
  `lake build ConnesWeilRH`.
- Axiom audit for the new Goal 2C read-offs and constructors reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak-placeholder scan over the touched Goal 2C/0E Lean files found no
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`,
  `.choose`, `choose_spec`, or `exists ... True` shells.
- Boundary preserved: Goal 2C now blocks the CCM25 expanded-row drift channel,
  but it does not construct CCM24/CC20 analytic object witnesses, build
  `SourceObjectPackage`, construct a `RouteCertificate`, or prove RH
  unconditionally. The next slice is Goal 2D cross-object bridge data plus an
  explicit `SourceObjectPackage` constructor.

2026-06-29

- Completed Goal 0E finite-prime theorem-base replacement.
- Updated `ConnesWeilRH/Source/CCM25TheoremBase.lean`.
- Added the direct concrete theorem:
  `ccm25_finite_prime_normalization_of_concrete_arithmetic_rows`.
- Added `CCM25TheoremBaseFinitePrime` and
  `CCM25TheoremBaseFinitePrime.ofArithmeticRows` so finite-prime
  normalization can be staged as its own theorem-base slice from concrete
  arithmetic rows.
- Added `CCM25TheoremBasePartialQWFinitePrime` and
  `ofSourceModelAndArithmeticRows`; this keeps the current QW field on the
  source-model staging path while routing finite-prime normalization through
  concrete arithmetic rows.
- Added `CCM25TheoremBase.dischargedWithConcreteFinitePrime`, a mixed
  constructor that replaces only the finite-prime normalization field with the
  concrete theorem path and leaves `Psi`, `QW_lambda`, and pole normalization
  on their current source-model staging path.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` and root
  `AGENTS.md` to mark Goal 0E complete and set Goal 2C concrete expanded-row
  consumption as the next proof-bearing slice.
- WSL ext4 verification passed after syncing the touched Lean file from the
  Windows source of truth:
  `lake build ConnesWeilRH.Source.CCM25TheoremBase ConnesWeilRH`.
- Axiom audit for
  `ccm25_finite_prime_normalization_of_concrete_arithmetic_rows`,
  `CCM25TheoremBaseFinitePrime.finite_prime_normalization_of_arithmetic_rows`,
  `CCM25TheoremBasePartialQWFinitePrime.ofSourceModelAndArithmeticRows`, and
  `CCM25TheoremBase.dischargedWithConcreteFinitePrime` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Boundary preserved: Goal 0E does not prove full CCM25, build
  `SourceObjectPackage`, construct a `RouteCertificate`, or prove RH
  unconditionally. It removes one avoidable law-field projection for
  finite-prime normalization.

2026-06-29

- Completed Goal 0D concrete fixed-lambda support.
- Added `ConcreteCommonFixedLambdaPrimePowerSupport` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean`.
- The new Goal 0D support record wraps the existing
  `SourcePrimePowerArithmeticSupportSkeletonAtLambda` but forces its
  `sourceTest` to equal the same `CommonSourceTest.ConcreteCommonSourceTest`
  evaluator from Goal 0A/0B.
- Added read-offs tying fixed-lambda support to the concrete common visibility
  predicate:
  `source_test_eq_common`,
  `support_visibility_iff_common_visibility`,
  `route_visibility_iff_common_visible_atom_data`,
  `global_exact_common_visible_atom_data`,
  `restricted_exact_common_visible_atom_data`,
  `concrete_visible_atom_has_lambda_cut`,
  `concrete_visible_atom_one_lt`, and
  `concrete_visible_atom_le_lambda_sq`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` to mark Goal 0D
  done and set Goal 0E as the next finite-prime source-definition slice.
- WSL ext4 verification passed after syncing from Windows source:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate
  ConnesWeilRH.Source.CCM25Concrete ConnesWeilRH`.
- Axiom audit for the new Goal 0D read-offs reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak-placeholder scan over the touched Goal 0C/0D Lean files found no
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`,
  `.choose`, `choose_spec`, or `exists ... True` shells.
- Boundary preserved: Goal 0D closes the main fixed-lambda support drift
  channel, but it does not yet replace
  `CCM25SourceModel.finitePrimeNormalization`, discharge a red analytic row, or
  prove unconditional RH. The next proof-bearing slice is Goal 0E.

2026-06-29

- Completed Goal 0C concrete common prime-power evaluation.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` so Goal 0C now
  targets concrete-common evaluation consumption rather than duplicating the
  existing generic source-point layer.
- Added `ConcreteCommonPrimePowerEvaluation` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerEvaluation.lean`.
- The new Goal 0C evaluation record ties the generic
  `SourceConvolutionEvaluationModel` to the same
  `CommonSourceTest.ConcreteCommonSourceTest` from Goal 0A/0B, including the
  same source-test evaluator, same concrete source square, and the source
  points `n` and `n^-1`.
- Added read-offs:
  `ConcreteCommonPrimePowerEvaluation.source_test_read_off`,
  `source_evaluator_test_read_off`,
  `model_evaluator_test_read_off`,
  `source_convolution_square_eq_common_square`,
  `forward_value_at_concrete_square`,
  `inverse_value_at_concrete_square`,
  `source_visibility_iff_concrete_visibility`, and
  `source_visibility_iff_common_visibility`.
- Added `ConcreteCommonPrimePowerPairingData` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerPairing.lean`.
- The new Goal 0C pairing data forces the pairing model's `sourceEvaluation`
  leg to equal the concrete-common evaluation model, then proves the concrete
  common source-evaluator formula
  `concrete_common_prime_power_pairing_formula_source_evaluator`.
- WSL ext4 verification passed after syncing from Windows source:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluation`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerPairing`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- Axiom audit for the new Goal 0C read-offs and pairing formula reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak-placeholder scan over the touched Goal 0C Lean files found no `sorry`,
  `admit`, `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`, `.choose`,
  `choose_spec`, or `exists ... True` shells.
- Boundary preserved: Goal 0C closes the main prime-power evaluation drift
  channel, but it does not yet prove fixed-lambda support, replace
  `CCM25SourceModel.finitePrimeNormalization`, discharge a red analytic row, or
  prove unconditional RH. The next source-definition slice is Goal 0D:
  fixed-lambda support using the concrete common visibility predicate.

2026-06-29

- Finished Goal 2B concrete consumption.
- Updated `ConnesWeilRH/Source/Objects.lean` so `CommonTestObject` now owns
  `concreteCommonTest : CCM25Concrete.CommonSourceTest.ConcreteCommonSourceTest W`.
- Added concrete read-off fields to `CommonTestObject`:
  `sourceTestReadOff`,
  `sourceConvolutionSquareConcreteReadOff`, and
  `ccm25SourceTestConcreteReadOff`.
- Added `CommonTestObject.ofConcrete` to build a common-test object directly
  from `ConcreteCommonSourceTest`.
- Added helper projections:
  `CommonTestObject.source_test_eq_concrete`,
  `CommonTestObject.source_square_eq_concrete`,
  `CommonTestObject.ccm25_source_test_eq_concrete`, and
  `CommonTestObject.route_visibility_iff_concrete_visibility`.
- Updated `external-opinions/003-unconditional-rh-completion-plan.md` to mark
  Goal 2B complete at the concrete-consumption layer and to set Goal 0C as the
  next finite-prime slice.
- WSL ext4 verification passed after syncing from Windows source:
  `lake build ConnesWeilRH.Source.Objects`,
  `lake build ConnesWeilRH.Source.ObjectDerivations`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- Boundary preserved: Goal 2B now blocks the main common-test bypass, but the
  arithmetic rows still have their own source-test bridge to
  `source_test_of_arithmetic_rows`; Goal 0C must next force prime-power
  evaluation objects through the concrete square and points.

2026-06-29

- Renamed ignored local folder `external-opinions/` from its previous
  non-English name and updated `.gitignore` plus path references in project
  memory. No non-English folder names remain under the project root.
- Implemented Goal 0B in
  `ConnesWeilRH/Source/CCM25Concrete/CommonSourceTest.lean`.
- Added the concrete source visibility predicate
  `sourceAtomVisibleOfConcreteTest W g n`, defined as CCM25 finite-prime
  visibility at the concrete Goal 0A square.
- Added Goal 0B read-offs:
  `route_visibility_iff_concrete_source_visibility`,
  `concrete_source_visibility_read_off`,
  `ConcreteCommonSourceTest.source_atom_visible_read_off`, and
  `concrete_evaluator_visibility_uses_concrete_predicate`.
- Updated `external-opinions/003-unconditional-rh-completion-plan.md` to mark
  Goal 0B done and list the implemented declarations.
- Re-examined the plan after Goal 0B. Current judgment: the plan can lead to
  unconditional proof only if each staging layer is forced to consume concrete
  Goal 0 data. Goal 0A/0B remove a common-test visibility drift channel, but
  they do not discharge a red analytic row by themselves.
- Updated the plan's work order: the best next step is Goal 2B consumption of
  `ConcreteCommonSourceTest` and `concreteSourceTestEvaluationInterface`,
  before adding more isolated Goal 0 slices.
- Boundary preserved: Goal 0B removes one free source-visibility predicate for
  the common test, but it still does not migrate
  `PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda` or
  replace a `CCM25SourceModel` finite-prime law-field projection.

2026-06-29

- Implemented Goal 0A after committing and pushing the previous working tree.
- Pushed signed commit `25418e5` (`Stage unconditional RH source objects`) to
  `origin/main`; local signature verification reported a good signature from
  Peter's configured key.
- Added `ConnesWeilRH/Source/CCM25Concrete/CommonSourceTest.lean`.
- The new module defines the concrete CCM25 common source square and source
  test object:
  `concreteSourceConvolutionSquare`,
  `ConcreteCommonSourceTest`,
  `concreteCommonSourceTest`, and
  `concreteSourceTestEvaluationInterface`.
- Proved the Goal 0A read-offs:
  `concrete_source_convolution_square_read_off`,
  `ConcreteCommonSourceTest.source_convolution_square_read_off`,
  `ConcreteCommonSourceTest.route_visibility_iff_source_visibility`,
  `ConcreteCommonSourceTest.evaluator_square_eq_concrete_square`,
  `concrete_source_test_evaluator_square_read_off`, and
  `concrete_route_visibility_iff_source_visibility`.
- Wired the module into `ConnesWeilRH/Source/CCM25Concrete.lean`.
- Updated the ignored local plan
  `external-opinions/003-unconditional-rh-completion-plan.md` to mark Goal 0A done and
  list the implemented objects/read-offs.
- WSL verification used the reset ext4 mirror at the pushed commit plus only
  the Goal 0A changes. Builds passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- Axiom audit for all new Goal 0A read-offs reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak-placeholder scan over the new Goal 0A files found no `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`, `.choose`,
  `choose_spec`, or `exists ... True`.
- Boundary preserved: Goal 0A fixes the common test/square by definition and
  provides concrete read-offs, but it does not yet implement Goal 0B
  fixed-source visibility migration, Goal 0C evaluation migration, or replace a
  `CCM25SourceModel` law-field projection.

2026-06-29

- Sliced Goal 0 in `external-opinions/003-unconditional-rh-completion-plan.md` into
  implementable proof-bearing steps.
- Goal 0A now targets a concrete CCM25 common source test and convolution
  square, with a square read-off theorem proved by unfolding definitions rather
  than projecting an arbitrary interface field.
- Goal 0B targets a concrete source visibility predicate attached to the same
  square.
- Goal 0C targets prime-power evaluation points and values tied to the same
  concrete square and the points `n` and `n^-1`.
- Goal 0D targets fixed-lambda support using the concrete visibility predicate.
- Goal 0E targets replacement of one `CCM25SourceModel` law-field projection,
  preferably finite-prime normalization, with a theorem from Goal 0A-0D data.
- Updated the work order: implement Goal 0A first, make Goal 2B consume it,
  then proceed through concrete visibility, evaluation points, support, and
  theorem-base replacement.
- Updated `AGENTS.md` with the sliced Goal 0 rule.
- Boundary preserved: this was a planning/documentation change only; no Lean
  code changed in this pass.

2026-06-29

- Revised `external-opinions/003-unconditional-rh-completion-plan.md` after auditing the
  current Goal 1B source-model layer.
- Added Goal 0 as the correctness gate before any source-model theorem-base
  projection can count as unconditional analytic discharge.
- Corrected Goal 1B wording: the current CCM24/CCM25/CC20 theorem-base fields
  are projected from explicit source-model assumptions, not yet proved from
  concrete analytic source definitions.
- Updated the completion gates and work order so the next first action is a
  Goal 0 seed before more source-object staging is treated as proof progress.
- Chosen first Goal 0 seed: CCM25 common source test and finite-prime evaluation
  object, because it feeds Goal 2B common-test data and later fixed-test
  restricted-to-full support equality.
- Updated `AGENTS.md` with the rule that `CCM24SourceModel`,
  `CCM25SourceModel`, and `CC20TraceModel` law fields remain assumptions until
  filled by theorems proved from concrete Goal 0 definitions.
- Boundary preserved: no Lean code changed in this pass, and no conditional
  source-model projection was promoted to unconditional proof.

2026-06-29

- Completed Goal 2A.
- Added `ConnesWeilRH/Source/ObjectTheoremBasePackage.lean`.
- The new `SourceObjectTheoremBasePackage` stages the Goal 1B source models
  before the full source-object layer:
  `ccm24Model : CCM24SourceModel`,
  `ccm25Model : CCM25SourceModel`, `cc20TraceModel : CC20TraceModel`,
  `rhDefinitionBridge : RHDefinitionBridge`, and
  `cc20RHExitObjectPackage : CC20RHExitObjectPackage rhDefinitionBridge`.
- Added projections:
  `SourceObjectTheoremBasePackage.toCCM24TheoremBase`,
  `SourceObjectTheoremBasePackage.toCCM25TheoremBase`,
  `SourceObjectTheoremBasePackage.toCC20TheoremBase`,
  `SourceObjectTheoremBasePackage.toSourceTheoremBase`,
  and compact interface projections.
- Updated `ConnesWeilRH.lean` to import
  `ConnesWeilRH.Source.ObjectTheoremBasePackage`.
- Updated `external-opinions/003-unconditional-rh-completion-plan.md` to mark Goal 2A
  done and Goal 2B as the next source-object staging target.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.ObjectTheoremBasePackage` and
  `lake build ConnesWeilRH`.
- Axiom audit for `toCCM24TheoremBase`, `toCCM25TheoremBase`,
  `toCC20TheoremBase`, `toSourceTheoremBase`, and the compact interface
  projections reports only `[propext, Classical.choice, Quot.sound]`.
- Weak-loophole scan over `ConnesWeilRH/**/*.lean` found no `sorry`, `admit`,
  declaration-level `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`,
  `.choose`, `choose_spec`, or `exists ... True`.
- `git diff --check` passed; Git only reported CRLF normalization warnings.
- Boundary preserved: Goal 2A does not build `SourceObjectPackage`,
  `CommonTestObject`, route front ends, `RouteCertificate`, or
  `unconditional_rh`.

2026-06-29

- Rewrote Goal 2 details in `external-opinions/003-unconditional-rh-completion-plan.md`
  after reviewing the full Goal 1-6 dependency chain.
- Correction: Goal 2 cannot jump straight from Goal 1B to a no-argument
  `SourceObjectPackage`, because `SourceObjectPackage` still owns common-test
  data, expanded object witnesses, cross-object bridges, and the expanded
  `SourceObject.CC20RHExitObjectPackage`.
- Split Goal 2 into staged targets:
  `SourceObjectTheoremBasePackage`, common-test data, expanded object rows, and
  the final `SourceObjectPackage` constructor.
- Recorded the naming boundary between compact
  `Source.CC20RHExitObjectPackage B` and expanded
  `Source.SourceObject.CC20RHExitObjectPackage`; Goal 2 must bridge these
  layers instead of treating them as the same object.
- Boundary preserved: this was a planning/documentation correction only. No
  Lean code changed in this pass.

2026-06-29

- Completed Goal 1B at the theorem-base/source-model layer.
- Added `ConnesWeilRH/Source/CCM24SourceModel.lean` with
  `CCM24SourceModel` and source projection theorems:
  `ccm24_source_canonical_semilocal_model`,
  `ccm24_source_support_transport`,
  `ccm24_source_bounded_comparison`, and
  `ccm24_source_sonin_comparison`.
- Extended `ConnesWeilRH/Source/CCM25SourceModel.lean` so
  `CCM25SourceModel` carries explicit laws for all theorem-base fields:
  `qw_eq_psi_convolution`, `psi_sign_formula`, `qw_lambda_formula`,
  `global_prime_index_coverage`, `restricted_prime_index_coverage`,
  `finite_prime_term_normalization`, and `pole_normalization`.
- Added CCM25 source projection theorems:
  `ccm25_source_qw_definition`, `ccm25_source_psi_sign`,
  `ccm25_source_qw_lambda_formula`,
  `ccm25_source_finite_prime_normalization`, and
  `ccm25_source_pole_normalization`.
- Added `ConnesWeilRH/Source/CC20TraceModel.lean` with `CC20TraceModel` and
  trace source projection theorems:
  `cc20_source_archimedean_trace_square`,
  `cc20_source_trace_class_template`,
  `cc20_source_mellin_half_density_convention`, and
  `cc20_source_signs_and_normalizations`.
- Added theorem-base constructors:
  `CCM24TheoremBase.discharged`,
  `CCM25TheoremBase.discharged`,
  `CC20TheoremBase.dischargedTraceBase`, and
  `SourceTheoremBase.dischargedTraceBase`.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CCM24SourceModel`,
  `lake build ConnesWeilRH.Source.CCM25SourceModel`,
  `lake build ConnesWeilRH.Source.CC20TraceModel`,
  `lake build ConnesWeilRH.Source.CCM24TheoremBase`,
  `lake build ConnesWeilRH.Source.CCM25TheoremBase`,
  `lake build ConnesWeilRH.Source.CC20TheoremBase`,
  `lake build ConnesWeilRH.Source.TheoremBase`, and
  `lake build ConnesWeilRH`.
- Axiom audit:
  CCM24 source projection theorems and `CCM24TheoremBase.discharged` report no
  axioms; CCM25 source projection theorems, `CCM25TheoremBase.discharged`,
  CC20 source projection theorems, `CC20TheoremBase.dischargedTraceBase`, and
  `SourceTheoremBase.dischargedTraceBase` report only
  `[propext, Classical.choice, Quot.sound]`.
- Weak-loophole scan over `ConnesWeilRH/**/*.lean` found no `sorry`, `admit`,
  declaration-level `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`,
  `.choose`, `choose_spec`, or `exists ... True`.
- `git diff --check` passed; Git only reported CRLF normalization warnings.
- Boundary preserved: this still does not build `SourceObjectPackage`,
  `RouteCertificate`, `SourceTheoremBase.discharged`, `unconditional_rh`, or
  the CC20 finite-vanishing RH exit. `SourceTheoremBase.dischargedTraceBase`
  still takes `CC20RHExitObjectPackage` as explicit Goal 5 data.

2026-06-29

- Corrected Goal 1B back to the approved QW-only slice after detecting an
  over-broad source-model discharge attempt.
- Removed the unapproved complete constructors
  `CCM25TheoremBase.discharged`,
  `CC20TheoremBase.dischargedTraceBase`, and
  `SourceTheoremBase.dischargedTraceBase`.
- Removed the unapproved CCM24 and CC20 source-model files from the active
  Lean import chain. CCM24 and CC20 remain at theorem-base target status only.
- Kept the approved CCM25 source slice:
  `ConnesWeilRH/Source/CCM25SourceModel.lean` defines
  `CCM25SourceModel` with explicit `qw`, `psi`, `convolutionStar`, and the law
  `qw_eq_psi_convolution`.
- `ConnesWeilRH.Source.ccm25_source_qw_definition` proves
  `WeilFormSymbols.QWDefinitionStatement M.toWeilFormSymbols` by projecting
  that source-model law.
- `ConnesWeilRH.Source.CCM25TheoremBasePartialQW.ofSourceModel` remains the
  only Goal 1B constructor. It is intentionally partial; `psiSign`,
  `qwLambdaFormula`, `finitePrimeNormalization`, and `poleNormalization`
  remain open.
- Updated the accepted-source status board and CCM24/CCM25/CC20 decision
  records so they no longer claim rows 1-3 are fully field-discharged.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CCM25SourceModel`,
  `lake build ConnesWeilRH.Source.CCM25TheoremBase`, and
  `lake build ConnesWeilRH`.
- Axiom audit:
  `ConnesWeilRH.Source.ccm25_source_qw_definition` and
  `ConnesWeilRH.Source.CCM25TheoremBasePartialQW.ofSourceModel` report only
  `[propext, Classical.choice, Quot.sound]`.
- Weak-loophole scan over `ConnesWeilRH/**/*.lean` found no `sorry`, `admit`,
  declaration-level `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`,
  `.choose`, `choose_spec`, or `exists ... True`.
- `git diff --check` passed; Git only reported CRLF normalization warnings.
- Boundary preserved: no `SourceObjectPackage`, `RouteCertificate`,
  `CCM25TheoremBase.discharged`, `SourceTheoremBase.discharged`, or
  `unconditional_rh` exists for this slice.

2026-06-29

- Started corrected Goal 1B field-by-field discharge without creating a fake
  global `SourceTheoremBase.discharged`.
- Added `ConnesWeilRH/Source/CCM25SourceModel.lean`.
- The new source model keeps the remaining CCM25 Weil-form data explicit and
  stores the source law `qw_eq_psi_convolution`, so the first source row field
  is discharged from model data rather than by `SourceObligation.Holds`,
  reviewer decision text, or a toy zero model.
- Proved `ConnesWeilRH.Source.ccm25_source_qw_definition`:
  `WeilFormSymbols.QWDefinitionStatement M.toWeilFormSymbols`.
- Added `CCM25TheoremBasePartialQW` and
  `CCM25TheoremBasePartialQW.ofSourceModel` in
  `ConnesWeilRH/Source/CCM25TheoremBase.lean`. This is intentionally partial:
  `psiSign`, `qwLambdaFormula`, `finitePrimeNormalization`, and
  `poleNormalization` remain open.
- Updated `ConnesWeilRH.lean` to import `ConnesWeilRH.Source.CCM25SourceModel`.
- Updated `docs/audits/ccm25-source-interface-referee-decision-record.md` to
  mark only the `QW(g,g)=Psi(F_g)` field as Lean discharged from
  `CCM25SourceModel`; the overall CCM25 source row remains not accepted-source
  and not fully discharged.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CCM25SourceModel`,
  `lake build ConnesWeilRH.Source.CCM25TheoremBase`, and
  `lake build ConnesWeilRH`.
- Axiom audit:
  `ConnesWeilRH.Source.ccm25_source_qw_definition` and
  `ConnesWeilRH.Source.CCM25TheoremBasePartialQW.ofSourceModel` report only
  `[propext, Classical.choice, Quot.sound]`.
- Weak-loophole scan over `ConnesWeilRH/**/*.lean` found no `sorry`, `admit`,
  declaration-level `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`,
  `.choose`, `choose_spec`, or `exists ... True`.
- Boundary preserved: this does not build `CCM25TheoremBase.discharged`,
  `SourceTheoremBase.discharged`, `SourceObjectPackage`, `RouteCertificate`,
  or `unconditional_rh`.

2026-06-29

- Implemented Goal 1's Lean theorem-base target layer without claiming source
  row discharge.
- Added `ConnesWeilRH/Source/CCM24TheoremBase.lean`,
  `ConnesWeilRH/Source/CCM25TheoremBase.lean`,
  `ConnesWeilRH/Source/CC20TheoremBase.lean`, and
  `ConnesWeilRH/Source/TheoremBase.lean`.
- Each base record carries the row's compact-interface fields and exposes a
  `.toInterface` constructor into `CCM24Interface`, `CCM25Interface`, or
  `CC20Interface`; the combined `SourceTheoremBase` exposes projection
  constructors for all three.
- Important correction during implementation: do not use toy `True`, empty
  finite-prime, or zero-symbol models to fill theorem-base fields. The final
  implementation keeps the records as theorem targets; the analytic source
  fields still must be proved from concrete source definitions before any row
  is discharged.
- Added explicit negative boundary props for the two base-row shortcuts:
  `CCM24AutomaticPostQTransportImported := False` with
  `ccm24_no_automatic_post_q_transport`, and
  `CCM25SpectralShortcutImported := False` with
  `ccm25_no_spectral_shortcut_import`.
- Updated the accepted-source status board and the first three decision
  records to mark rows 1-3 as `Lean theorem-base target implemented`, not
  accepted-source and not discharged.
- WSL ext4 verification passed after syncing from the Windows source of truth:
  `lake build ConnesWeilRH.Source.CCM24TheoremBase`,
  `lake build ConnesWeilRH.Source.CCM25TheoremBase`,
  `lake build ConnesWeilRH.Source.CC20TheoremBase`,
  `lake build ConnesWeilRH.Source.TheoremBase`, and
  `lake build ConnesWeilRH`.
- Axiom audit:
  `CCM24TheoremBase.toInterface` has no axioms;
  `CCM25TheoremBase.toInterface`, `CC20TheoremBase.toInterface`, and the three
  `SourceTheoremBase` projections report only
  `[propext, Classical.choice, Quot.sound]`;
  the two negative-boundary theorems have no axioms.
- Weak-loophole scan over `ConnesWeilRH/**/*.lean` found no `sorry`, `admit`,
  declaration-level `axiom`, `constant`, `opaque`, `unsafe`, `Nonempty`,
  `.choose`, `choose_spec`, or `exists ... True`.
- Boundary preserved: this opens the Lean theorem-base target layer for Goal 1.
  It does not build `SourceObjectPackage`, a route front end,
  `RouteCertificate`, `unconditional_rh`, or a source-row analytic proof.

2026-06-29

- Continued common-test unconditionalization by replacing another bare CCM25
  compatibility `Prop` with data-bearing equality.
- Added `ccm25SourceTest` to `CommonTestObject` in
  `ConnesWeilRH/Source/Objects.lean`, with type
  `CCM25Concrete.PrimePowerTest.SourceTestEvaluationInterface W sourceTest
  sourceTest`.
- Added `ccm25SourceTestSquareReadOff`, tying the evaluator interface's
  convolution square to `commonTest.sourceConvolutionSquare`.
- Changed `SourceObjectPackage.ccm25Test_eq_commonTest` from a bare `Prop` to
  the equality between `commonTest.ccm25SourceTest` and
  `CCM25Concrete.Rows.source_test_of_arithmetic_rows
  ccm25.concreteArithmeticRows commonTest.sourceTest commonTest.sourceTest`.
- Added source projection helpers in
  `ConnesWeilRH/Source/ObjectDerivations.lean`:
  `toCCM25CommonSourceTest`,
  `common_convolution_square_eq_ccm25_source_test_square`, and
  `common_ccm25_source_test_eq_arithmetic_rows`.
- Added route-facing projections in `ConnesWeilRH/Route/RouteTheorem.lean`:
  `expanded_source_common_test_eq_ccm25_arithmetic_source_test` and
  `expanded_source_common_square_eq_ccm25_source_test_square`.
- Updated `docs/audits/unconditional-rh-gap-ledger.md` and `AGENTS.md` to
  record that the CCM25 common-test bridge must stay tied to arithmetic rows by
  equality, not a bare `Prop`.
- WSL ext4 verification passed after syncing `Objects.lean`,
  `ObjectDerivations.lean`, and `RouteTheorem.lean`:
  `lake build ConnesWeilRH`.
- Axiom audit for
  `ConnesWeilRH.Source.SourceObject.SourceObjectPackage.common_ccm25_source_test_eq_arithmetic_rows`,
  `ConnesWeilRH.Route.expanded_source_common_test_eq_ccm25_arithmetic_source_test`,
  `ConnesWeilRH.Route.expanded_source_common_square_eq_ccm25_source_test_square`,
  and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Strict weak-loophole scan over Windows found no Lean declarations or witness
  shells matching `sorry`, `admit`, declaration-level `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Boundary preserved: this removes the CCM25 common-test evaluator drift
  channel but does not prove RH unconditionally or discharge the analytic red
  rows.

2026-06-29

- Continued the unconditionalization attack slice by hardening the common-test
  convolution square.
- Changed `CommonTestObject` in `ConnesWeilRH/Source/Objects.lean` to depend on
  the CCM25 `WeilFormSymbols` and changed `sourceConvolutionSquareReadOff` from
  a bare `Prop` to the concrete equality
  `sourceConvolutionSquare = W.convolutionStar sourceTest sourceTest`.
- Updated `SourceObjectPackage.commonTest` so it is a
  `CommonTestObject ccm25.weilSymbols`, binding the common test square to the
  same CCM25 symbols used by the route.
- Updated `ConnesWeilRH/Route/RouteTheorem.lean` so
  `ExpandedSourceRouteCertificateFrontEnd.commonTuple` is stored at
  `pkg.commonTest.sourceConvolutionSquare`; added
  `expanded_source_package_convolution_square_read_off`,
  `expanded_source_convolution_square_compatibility`,
  `expanded_source_route_common_tuple_on_route_square`,
  `expanded_source_route_common_test_on_route_square`, and
  `expanded_source_restricted_to_full_bridge_on_route_square`.
- The route certificate constructor now transports restricted-to-full and
  final-sign uses from the source square to the route square through the
  concrete source-square equality, rather than taking both directly at the
  route-square expression.
- Updated `docs/audits/unconditional-rh-gap-ledger.md` and `AGENTS.md` with the
  new rule that common-test convolution-square data must remain a concrete
  equality against the CCM25 Weil symbols.
- WSL ext4 verification passed after syncing `Objects.lean` and
  `RouteTheorem.lean`: `lake build ConnesWeilRH.Route.RouteTheorem` and
  `lake build ConnesWeilRH`.
- Axiom audit for
  `ConnesWeilRH.Route.expanded_source_package_convolution_square_read_off`,
  `ConnesWeilRH.Route.expanded_source_convolution_square_compatibility`,
  `ConnesWeilRH.Route.expanded_source_route_common_tuple_on_route_square`,
  `ConnesWeilRH.Route.expanded_source_restricted_to_full_bridge_on_route_square`,
  `ConnesWeilRH.Route.expanded_source_route_final_sign_bridge`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Strict weak-loophole scan over Windows found no Lean declarations or witness
  shells matching `sorry`, `admit`, declaration-level `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Boundary preserved: this removes one common-test drift channel but does not
  prove RH unconditionally or discharge the CCM24/CCM25/CC20 analytic red rows.

2026-06-29

- Shifted the active route strategy from additional interface polish to
  unconditionalization: the next work should remove or prove inputs to
  `final_connes_weil_rh`, not merely make already-visible assumptions prettier.
- Added `docs/audits/unconditional-rh-gap-ledger.md`.
- The new ledger starts from the current Lean boundary
  `RouteCertificate inputs -> _root_.RiemannHypothesis` and maps the missing
  unconditional chain:
  concrete source definitions / accepted imports / Lean analytic proofs ->
  `SourceObjectPackage` -> `ExpandedSourceFixedSTestFrontEnd` ->
  `ExpandedSourceTraceReadOffFrontEnd` ->
  `ExpandedSourceRouteCertificateFrontEnd` -> `RouteCertificate` -> RH.
- Classified top-level blockers as Green/Yellow/Red and identified the first
  attack slice as common-test/convolution compatibility, fixed tuple equality,
  CCM25 fixed-lambda finite-prime support and term normalization, then
  fixed-test restricted-to-full scalar equality.
- Linked the ledger from `docs/audits/README.md` and the root `README.md`.
- Started the first ledger attack slice in Lean by changing
  `ExpandedSourceRouteCertificateFrontEnd` in
  `ConnesWeilRH/Route/RouteTheorem.lean` to store the shared
  `SourceCommonTestTupleContract` and only the `SourceArchimedeanSignBridge`.
- Added `expanded_source_route_common_test` and
  `expanded_source_route_final_sign_bridge`, so the final-sign bridge is now
  derived from the same common tuple used by the restricted-to-full path rather
  than being supplied as a separate route-front field.
- WSL ext4 verification passed after syncing `RouteTheorem.lean`:
  `lake build ConnesWeilRH.Route.RouteTheorem` and `lake build ConnesWeilRH`.
- Axiom audit for
  `ConnesWeilRH.Route.expanded_source_route_common_test`,
  `ConnesWeilRH.Route.expanded_source_route_final_sign_bridge`,
  `ConnesWeilRH.Route.route_certificate_of_expanded_source_package`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Strict weak-loophole scan over Windows found no Lean declarations or witness
  shells matching `sorry`, `admit`, declaration-level `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Boundary preserved: this is a planning/audit artifact for removing the
  certificate/source-object inputs plus a small common-test drift guard. It
  does not prove RH unconditionally and does not discharge CCM24/CCM25/CC20
  analytic rows.

2026-06-29

- Migrated the common-atom restricted-to-full archimedean balance to scoped
  finite-prime evaluator sums.
- Changed `SourceCommonAtomArchimedeanContributionMatchesForRestriction` in
  `ConnesWeilRH/Route/Bridge.lean` so its stored balance uses
  `source_common_restricted_finite_prime_evaluator_scoped_sum` and
  `source_common_global_finite_prime_evaluator_scoped_sum`.
- Added
  `SourceCommonAtomFullArchimedeanContributionMatchesForRestriction` as the
  explicit compatibility shape for the old common full-sum balance.
- Added `source_common_atom_full_archimedean_contribution_matches_of_package`
  to derive the old common full-sum balance from common-scoped stored evidence
  through the package old/scoped bridges.
- Updated `source_common_atom_archimedean_contribution_matches_of_package` so
  it returns common-scoped balance as the main route-facing evidence while
  deriving the old package theorem only as an intermediate compatibility step.
- WSL ext4 verification passed after syncing the current Windows dirty Lean
  files: `lake build ConnesWeilRH.Route.Bridge` and
  `lake build ConnesWeilRH`.
- Axiom audit for
  `ConnesWeilRH.Route.source_common_atom_full_archimedean_contribution_matches_of_package`,
  `ConnesWeilRH.Route.source_common_atom_archimedean_contribution_matches_of_package`,
  `ConnesWeilRH.Route.common_atom_archimedean_contribution_of_qw_lambda_restriction`,
  and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Strict weak-loophole scans over Windows and WSL found no Lean declarations
  or witness shells matching `sorry`, `admit`, declaration-level `axiom`,
  `constant`, `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: common-atom balance is now scoped-first, but the
  route remains source-conditional and does not discharge the analytic
  CCM24/CCM25/CC20 source interfaces or prove RH unconditionally.

2026-06-29

- Migrated the restricted-to-full archimedean balance record itself to scoped
  finite-prime evaluator sums.
- Changed `SourceArchimedeanContributionMatchesForRestriction` in
  `ConnesWeilRH/Route/Bridge.lean` so its stored
  `archimedeanContributionMatches` field is the scoped balance using
  `source_restricted_finite_prime_evaluator_scoped_sum` and
  `source_global_finite_prime_evaluator_scoped_sum`.
- Added `source_full_archimedean_contribution_matches_of_package` as the
  explicit old/full-sum compatibility projection from the scoped stored
  evidence through the package old/scoped bridges.
- Updated old full-sum APIs such as
  `archimedean_contribution_equality_of_qw_lambda_restriction`,
  `source_common_atom_archimedean_contribution_matches_of_package`, and the
  legacy scalar-equality helpers to derive their old balance from the scoped
  record instead of reading old balance as stored evidence.
- Added scoped projection helpers
  `scoped_archimedean_contribution_equality_of_qw_lambda_restriction`,
  `scoped_archimedean_contribution_matches_of_scalar_witness`, and
  `scoped_archimedean_contribution_matches_of_scalar_restriction`.
- WSL ext4 verification passed after syncing the current Windows dirty Lean
  files: `lake build ConnesWeilRH.Route.Bridge` and
  `lake build ConnesWeilRH`.
- Axiom audit for
  `ConnesWeilRH.Route.source_full_archimedean_contribution_matches_of_package`,
  `ConnesWeilRH.Route.scoped_archimedean_contribution_matches_of_scalar_witness`,
  `ConnesWeilRH.Route.scoped_archimedean_contribution_matches_of_scalar_restriction`,
  `ConnesWeilRH.Route.scalar_equality_from_scoped_witness_components`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Strict weak-loophole scans over Windows and WSL found no Lean declarations
  or witness shells matching `sorry`, `admit`, declaration-level `axiom`,
  `constant`, `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: the route now stores the restricted-to-full
  archimedean balance in scoped finite-prime form, but the proof remains
  source-conditional and does not discharge the analytic CCM24/CCM25/CC20
  source interfaces or prove RH unconditionally.

2026-06-29

- Hardened the route-facing CCM25 scoped finite-prime read-off path.
- Added scoped finite-prime sum and scoped source-evaluator fields to
  `PackageBackedCCM25WeilFormReadOff` in
  `ConnesWeilRH/Route/Bridge.lean`, so route consumers can inspect scoped
  `Psi`, `QW`, and `QW_lambda` read-offs directly instead of only seeing them
  at the package/component layer.
- Added package-level old/scoped compatibility bridges in
  `ConnesWeilRH/Source/CCM25Concrete/Package.lean`:
  `source_common_global_scoped_sum_eq_common_global_sum_of_package`,
  `source_common_restricted_scoped_sum_eq_common_restricted_sum_of_package`,
  `source_global_scoped_sum_eq_global_sum_of_package`, and
  `source_restricted_scoped_sum_eq_restricted_sum_of_package`.
- Added `SourceScopedArchimedeanContributionMatchesForRestriction` and proved
  it from the existing archimedean balance through the old/scoped package
  bridges.
- Changed `scalar_equality_of_scalar_witness` to use
  `scalar_equality_from_scoped_witness_components`, whose equality chain reads
  `QW_lambda` and `QW` through scoped finite-prime evaluator sums.
- WSL ext4 verification passed after syncing the current Windows dirty Lean
  files:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package
  ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- Axiom audit for
  `ConnesWeilRH.Route.scalar_equality_from_scoped_witness_components`,
  `ConnesWeilRH.Route.scalar_equality_of_scalar_witness`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Strict weak-loophole scans over Windows and WSL found no Lean declarations
  or witness shells matching `sorry`, `admit`, declaration-level `axiom`,
  `constant`, `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: this makes restricted-to-full scalar equality use
  the scoped finite-prime read-off chain, but it remains source-conditional
  Lean interface hardening. It does not discharge the analytic CCM24/CCM25/CC20
  source interfaces or prove RH unconditionally.

2026-06-29

- Propagated CCM25 support-scoped finite-prime evaluator sums into the formula
  component layer.
- Added scoped finite-prime sum fields to
  `GlobalComponent.GlobalFinitePrimeSumReadOff` and
  `RestrictedComponent.RestrictedFinitePrimeSumReadOff`, alongside the existing
  compatibility fields for the older full arithmetic-normalization sums.
- Added global scoped read-off theorems:
  `global_finite_prime_scoped_sum_of_component`,
  `global_von_mangoldt_pairing_scoped_sum_of_component`,
  `psi_scoped_source_evaluator_of_component`, and
  `qw_scoped_source_evaluator_of_component`.
- Added restricted scoped read-off theorems:
  `restricted_finite_prime_scoped_sum_of_component`,
  `restricted_von_mangoldt_pairing_scoped_sum_of_component`, and
  `qw_lambda_formula_scoped_source_evaluator_of_component`.
- Exposed the same scoped read-offs through
  `ConnesWeilRH/Source/CCM25Concrete/FormulaComponents.lean` with
  `psi_scoped_source_evaluator_of_formula_components`,
  `qw_scoped_source_evaluator_of_formula_components`,
  `qw_lambda_formula_scoped_source_evaluator_of_formula_components`, and the
  global/restricted scoped sum projection theorems.
- Added package-level scoped finite-prime evaluator sums and bridges in
  `ConnesWeilRH/Source/CCM25Concrete/Package.lean`, including
  `source_global_finite_prime_evaluator_scoped_sum`,
  `source_restricted_finite_prime_evaluator_scoped_sum`,
  `source_common_global_finite_prime_evaluator_scoped_sum`,
  `source_common_restricted_finite_prime_evaluator_scoped_sum`, and the
  corresponding scoped bridge theorems.
- Propagated the scoped package read-offs into `ConnesWeilRH/Route/Bridge.lean`
  through the package stabilization and finite-prime sign-owned route records.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package` and
  `lake build ConnesWeilRH.Route.Bridge`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.GlobalComponent
  ConnesWeilRH.Source.CCM25Concrete.RestrictedComponent
  ConnesWeilRH.Source.CCM25Concrete.FormulaComponents
  ConnesWeilRH.Source.CCM25Concrete.Package ConnesWeilRH.Route.Bridge
  ConnesWeilRH`.
- Axiom audit for the new scoped global/restricted component theorems,
  formula-component scoped `QW`/`QW_lambda` theorems, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan found no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: global `QW/Psi` and restricted `QW_lambda` can now
  be read against support-scoped finite-prime evaluator sums at the component
  layer, but package and route consumers still need migration before the old
  full `forall n` arithmetic-normalization dependency is retired.

2026-06-29

- Began hardening CCM25 finite-prime arithmetic away from impossible
  all-natural-number atom assumptions.
- Added `SourceFinitePrimeArithmeticDataOnIndexSet` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean`, with
  `atIndex` requiring a membership proof `n in indexSet` before supplying
  `SourceFinitePrimeArithmeticData W f g n`.
- Added scoped evaluator sums:
  `SourceFinitePrimeEvaluatorSumOnIndexSet`,
  `SourceGlobalFinitePrimeEvaluatorSumOnIndexSet`, and
  `SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet`.
- Proved compatibility with the older global normalization interface through
  `source_finite_prime_evaluator_sum_on_index_set_of_global`,
  `source_global_finite_prime_evaluator_sum_on_index_set_of_global`, and
  `source_restricted_finite_prime_evaluator_sum_on_index_set_of_global`.
- Added certificate-level scoped projections in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`:
  `arithmetic_data_on_global_index_set_of_certificate`,
  `arithmetic_data_on_restricted_index_set_of_certificate`,
  `arithmetic_global_scoped_sum_eq_global_sum_of_certificate`, and
  `arithmetic_restricted_scoped_sum_eq_restricted_sum_of_certificate`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic` and
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate
  ConnesWeilRH.Source.CCM25Concrete.Package ConnesWeilRH.Route.Bridge
  ConnesWeilRH`.
- Axiom audit for the scoped evaluator compatibility theorems, certificate
  scoped-sum theorems, and `ConnesWeilRH.Route.final_connes_weil_rh` reported
  only `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan found no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: this introduces the correct support-scoped target
  shape for finite-prime arithmetic but does not yet migrate all CCM25 rows,
  packages, and route consumers away from the older full
  `forall n` arithmetic-normalization interface.

2026-06-29

- Hardened the `CC20FiniteVanishingRhExit` route-input path.
- Added `CC20PropositionC1RouteInputData` in
  `ConnesWeilRH/Source/CC20RHExit.lean` to wrap the constructed
  `CC20PropositionC1InputData` together with preservation fields proving that
  `tripleVanishingMatchesMellin` is the supplied route triple-vanishing input
  and `fullWeilPositivity` is the supplied route full-positivity input.
- Changed `cc20_proposition_c1_input_data` to return the new route-input
  wrapper, and updated source/package/route consumers to use `.c1InputData`
  when the downstream criterion needs the original C.1 input structure.
- Updated `ConnesWeilRH/Route/RouteTheorem.lean` so
  `route_backed_cc20_exit_input_data_of_route_bridge_certificate` explicitly
  builds the route-input wrapper before projecting the C.1 input data.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CC20RHExit ConnesWeilRH.Source.CC20
  ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`, followed by
  `lake build ConnesWeilRH.Route.RouteTheorem ConnesWeilRH` after the
  route-side projection fix.
- Axiom audit for the new C.1 route-input preservation theorems, source
  criterion factorization, CC20 interface finite-vanishing exits, route-backed
  C.1 input construction, and `ConnesWeilRH.Route.final_connes_weil_rh`
  reported only `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan found no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: this prevents C.1 input data from drifting away
  from the supplied route triple-vanishing and full-positivity evidence, but it
  does not prove the analytic Mellin bridge, final sign bridge, Proposition
  C.1, or RH unconditionally.

2026-06-29

- Hardened `RHDefinitionBridge` against Mathlib non-trivial-zero component
  drift.
- Changed `RHDefinitionBridge.MathlibNontrivialZero` in
  `ConnesWeilRH/Source/RHDefinition.lean` from an anonymous nested
  conjunction to a named `Prop` structure with fields `zeta_zero`,
  `not_negative_even`, and `not_pole`.
- Updated the component constructor/projections, `mathlib_rh_statement_iff_mathlib`,
  and the `standard` bridge to consume named fields instead of tuple
  projections `.1`, `.2.1`, and `.2.2`.
- Added `mathlib_rh_statement_iff_mathlib_components`, so the intermediate
  `MathlibRHStatement` is directly shown equivalent to Mathlib's component
  shape before converting to `_root_.RiemannHypothesis`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.RHDefinition` and
  `lake build ConnesWeilRH.Source.CC20 ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.
- Axiom audit printed Mathlib's current `_root_.RiemannHypothesis` definition
  as `forall s, riemannZeta s = 0 -> not negative-even -> s != 1 ->
  s.re = 1 / 2`, and the audited RH bridge/CC20 exit/final route theorems
  reported only `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan found no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: this confirms the bridge continues to target
  Mathlib's exact zeta-zero, negative-even exclusion, pole exclusion, and
  critical-line statement, but it does not prove the CC20 source RH predicate
  or RH unconditionally.

2026-06-29

- Hardened the CC20 trace read-off bridge contract in Lean.
- Added `FullTraceReadOffBridgeContract` and
  `RestrictedTraceReadOffBridgeContract` in
  `ConnesWeilRH/Route/Theorem1.lean`.
- Replaced bare `fullTraceReadOffBridge` and
  `restrictedTraceReadOffBridge` functions on `SourceTraceReadOffData` and
  `ExpandedSourceTraceReadOffFrontEnd` with contract structures that include
  preservation proofs for the input no-defect, full-`QW`, and restricted-`QW`
  evidence.
- Added projection theorems:
  `full_trace_read_off_bridge_preserves_no_defect`,
  `full_trace_read_off_bridge_preserves_full_qw`, and
  `restricted_trace_read_off_bridge_preserves_restricted_qw`.
- Updated bridge consumers to call `.build`, so the bridge can no longer
  silently return a read-off source whose named evidence fields drift from the
  supplied inputs.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1` and
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.
- Axiom audit for the new preservation theorems, bridge exits,
  `trace_weil_compatibility_of_source_trace_data`,
  `fixed_s_read_off_of_source_trace_data`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan found no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: this removes a route-level evidence-drift surface
  in the CC20 trace-to-`QW_lambda` path, but it does not prove the analytic
  trace read-off, sign/defect bridge, restricted-to-full bridge, final sign
  bridge, or RH unconditionally.

2026-06-29

- Began hardening the CC20 trace-to-read-off entry path in Lean.
- Added named route wrappers in `ConnesWeilRH/Route/Theorem1.lean`:
  `CC20TraceLegalityTemplateOutput` for the trace-class/cyclicity output of
  the CC20 trace-class template, and
  `CC20ArchimedeanTraceSquareOutput` for the no-defect/positive-trace output
  of the CC20 archimedean trace-square theorem.
- Replaced downstream `.1` / `.2` consumption in
  `cc20_trace_legality_of_source_trace_data`,
  `cc20_trace_square_of_source_trace_data`, and
  `SourceTraceReadOffData.ofExpandedSourcePackage` with named wrapper
  projections. The only remaining tuple unpacking is now localized inside the
  two wrapper constructors.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`, and `lake build ConnesWeilRH`.
- Axiom audit for the two wrappers, trace legality/read-off projections,
  `fixed_s_read_off_of_source_trace_data`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Logic boundary preserved: this makes the trace-class/cyclicity and
  no-defect/positive-trace route evidence more inspectable, but it does not
  prove the analytic CC20 trace-to-`QW_lambda`, cyclicity theorem, or
  sign/defect bridge unconditionally.

2026-06-29

- Hardened the CCM25 global/restricted formula component object identity.
- Added `commonConcreteObject` to
  `ConcreteCCM25FormulaComponents` in
  `ConnesWeilRH/Source/CCM25Concrete/FormulaComponents.lean`.
- Added explicit equality fields proving the global component concrete object
  and the restricted component concrete object are the same common concrete
  object, not merely objects with equal certificates.
- Exposed package-level projections:
  `common_concrete_object_of_package`,
  `global_concrete_object_eq_common_of_package`,
  `restricted_concrete_object_eq_common_of_package`, and
  `global_restricted_concrete_object_eq_of_package`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FormulaComponents`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package
  ConnesWeilRH.Route.Bridge ConnesWeilRH`, and `lake build ConnesWeilRH`.
- Axiom audit for the common concrete object projections and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Logic boundary preserved: this closes another CCM25 finite-prime
  normalization drift surface, but does not discharge CC20 trace read-off,
  final sign, restricted-to-full, or sign/defect analytically.

2026-06-29

- Hardened the CCM25 finite-prime sum formula witness path.
- Added `SourceGlobalFinitePrimeSumFormulaData` and
  `SourceRestrictedFinitePrimeSumFormulaData` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean` to bind each
  finite-prime term sum read-off to its matching Von Mangoldt pairing sum
  read-off for the same arithmetic normalization object.
- Replaced the four separate sum fields on
  `FixedLambdaFinitePrimeConcreteObject` with `globalSumFormulaData` and
  `restrictedSumFormulaData`, then exposed theorem-level projections for the
  four read-offs.
- Updated global/restricted components and package projections to consume the
  concrete-object sum projection theorems rather than reaching into
  independent concrete-object sum fields.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate
  ConnesWeilRH.Source.CCM25Concrete.GlobalComponent
  ConnesWeilRH.Source.CCM25Concrete.RestrictedComponent
  ConnesWeilRH.Source.CCM25Concrete.Package` and
  `lake build ConnesWeilRH`.
- Axiom audit for the new global/restricted sum formula data constructors,
  concrete-object sum projections, component/package pairing-sum projections,
  and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan found no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`.
- Logic boundary preserved: this binds finite-prime evaluator sums to one
  arithmetic normalization object, but it does not prove CC20 trace read-off,
  restricted-to-full, final sign, or sign/defect analytically.

2026-06-29

- Hardened the CCM25 local finite-prime formula witness path.
- Added `SourceFinitePrimeLocalFormulaData` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean` to bind the
  same local atom data to its Von Mangoldt weight read-off, prime-power
  pairing source-evaluator formula, and finite-prime term
  source-evaluator formula.
- Replaced the three separate formula fields on
  `FixedLambdaFinitePrimeConcreteObject` with one `localFormulaData` field,
  then exposed the old theorem-level projections through
  `concrete_object_weight_read_off`,
  `concrete_object_pairing_formula_source_evaluator`, and
  `concrete_object_term_formula_source_evaluator`.
- Updated the CCM25 interface, package, and route bridge layers to consume
  the concrete-object projection theorems rather than reaching directly into
  three independent formula fields.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate
  ConnesWeilRH.Source.CCM25Concrete.Interface
  ConnesWeilRH.Source.CCM25Concrete.Package
  ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- Axiom audit for the new local formula constructor/projections, the
  concrete-object formula projections, the package/route pairing projection,
  and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan found no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`. Remaining `.weightReadOff` / formula-field hits are now
  inside the local formula/atom-data definitions and their projection
  theorems, not in package or route consumers.
- Logic boundary preserved: this ties CCM25 local finite-prime arithmetic
  formulas to one atom witness, but it still does not construct the analytic
  CC20 trace-to-`QW_lambda` or sign/defect proof.

2026-06-29

- Hardened the CCM25 finite-prime support witness path.
- Added named support witness records in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean`:
  `SourceVisibleAtomData`, `SourceGlobalIndexData`, and
  `SourceRestrictedIndexData`, exposing `primePowerIndex`, `atomVisible`,
  and, on the restricted record, `lambdaCut`.
- Propagated the records through the prime-power support skeleton/support
  layer, while keeping the lower `FinitePrimeExact` boundary as explicit
  conjunctions to avoid a module import cycle.
- Propagated these records through the CCM25 concrete layers:
  `FinitePrimeCertificate.lean`, `FinitePrimeInterface.lean`, `Rows.lean`,
  `Interface.lean`, and `Package.lean`.
- Updated `ConnesWeilRH/Route/Bridge.lean` so
  `PackageFinitePrimeSupportStabilization.globalIndexSourceData` and
  `restrictedIndexSourceData` expose named support witnesses instead of
  anonymous `A ∧ B` / `A ∧ B ∧ C` tuples.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Rows
  ConnesWeilRH.Source.CCM25Concrete.Interface
  ConnesWeilRH.Source.CCM25Concrete.Package`,
  `lake build ConnesWeilRH.Route.Bridge
  ConnesWeilRH.Route.RouteTheorem`, and `lake build ConnesWeilRH`.
- Axiom audit for the support-to-exact-support conversion, the new
  certificate/package/route support-witness theorems, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan found no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, `unsafe`, `Nonempty`, `.choose`, `choose_spec`, or
  `exists ... True`. Remaining finite-prime conjunction hits are in the
  lower `FinitePrimeExact` exact-support mathematical boundary and one
  package theorem exposing that boundary, not in the support skeleton,
  certificate, package, or route support-witness exits.
- Logic boundary preserved: this hardens CCM25 finite-prime support plumbing,
  but it does not discharge the analytic CC20 trace-to-`QW_lambda`,
  sign/defect, or accepted-source obligations.

2026-06-29

- Hardened the CCM25 finite-prime visibility interface.
- `WeilFormSymbols.FinitePrimeVisibilityStatement` is now a named structure
  with `globalPrimeIndexCoverage`, `restrictedPrimeIndexCoverage`, and
  `finitePrimeTermNormalization`, instead of an anonymous nested conjunction.
- Updated `ConnesWeilRH/Route/AdmissibleWindow.lean` and
  `ConnesWeilRH/Source/ObjectDerivations.lean` to consume named fields rather
  than `.1`, `.2.1`, or `.2.2` at the finite-prime interface boundary.
- Updated the fixed-lambda certificate constructors in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeInterface.lean` to build the
  new named visibility structure explicitly.
- Also tightened `SourceFiniteVanishingCriterionPackage` by removing the
  redundant bare `finiteSetAdmissible : Prop` field; it now keeps only the
  actual `SourceFiniteSetAdmissibility` witness.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface
  ConnesWeilRH.Route.AdmissibleWindow
  ConnesWeilRH.Source.ObjectDerivations
  ConnesWeilRH.Source.CC20` and `lake build ConnesWeilRH`.
- Axiom audit for the finite-prime visibility constructor, source-backed
  finite-prime term normalization, source-object pointwise term proof, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Logic boundary preserved: this removes another CCM25 tuple-shaped proof
  shell, but it does not prove the analytic CC20 trace-to-`QW_lambda` or
  sign/defect bridge unconditionally.

2026-06-29

- Hardened the CCM25 full/restricted QW read-off interfaces in
  `ConnesWeilRH/Route/Theorem1.lean`.
- `CCM25FullQWReadOff` is now a named structure with
  `qwDefinitionReadOff` and `psiSignReadOff`, instead of
  `CCM25QWDefinitionReadOff ∧ CCM25PsiSignReadOff`.
- `CCM25RestrictedQWReadOff` is now a named structure with
  `windowLambdaCompatibility`, `qwLambdaFormulaReadOff`, and
  `poleNormalizationReadOff`, instead of the anonymous triple conjunction.
- Added projection theorems for the new full/restricted read-off structures,
  and updated package/source-backed constructors to fill named fields.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1
  ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for the final route theorem, the new CCM25 full/restricted
  read-off constructors, and the new projections reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan over `ConnesWeilRH/**/*.lean` found no `Nonempty`,
  `.choose`, `choose_spec`, `exists ... True`, `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, or `unsafe`.
- Logic boundary preserved: this makes the CCM25 QW/QW_lambda read-off fields
  explicit, but `CCM25WeilFormReadOff`, `TestHalfDensityCompatibility`,
  `FixedSProjectionTransport`, and the CC20 trace/sign-defect analytic bridges
  remain source-conditional work.

2026-06-29

- Hardened the upstream window/lambda gate in
  `ConnesWeilRH/Route/Theorem1.lean`.
- `WindowLambdaCompatibility` is now a named structure with
  `oneLtLambda`, `windowSupportContainment`, and `lambdaCompatible`, instead
  of the anonymous triple conjunction
  `1 < lambda ∧ WindowSupportContainment ∧ lambdaCompatible`.
- Added `window_lambda_compatibility_of_source_backed` and updated downstream
  constructors in `Theorem1.lean` and `Bridge.lean` to consume the named
  structure fields rather than rebuilding positional tuples.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1
  ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for the final route theorem, the new window/lambda constructor,
  the restricted-route window-control constructor, and the CCM25 restricted
  read-off constructors reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan over `ConnesWeilRH/**/*.lean` found no `Nonempty`,
  `.choose`, `choose_spec`, `exists ... True`, `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, or `unsafe`.
- Logic boundary preserved: this removes an upstream positional window gate,
  but larger Theorem 1 interfaces such as `CCM25FullQWReadOff`,
  `CCM25RestrictedQWReadOff`, `TestHalfDensityCompatibility`, and
  `FixedSProjectionTransport` still remain as source-conditional interface
  work.

2026-06-29

- Tightened the restricted-to-full window-control gate in
  `ConnesWeilRH/Route/Bridge.lean`.
- `SourceWindowControlsRestrictedRoute` is now a named structure with
  `windowLambdaCompatibility` and `windowSupportContainment`, instead of the
  anonymous conjunction
  `WindowLambdaCompatibility inputs g lambda ∧ WindowSupportContainment inputs g lambda`.
- Added route-level projections
  `window_lambda_compatibility_of_source_window_controls` and
  `window_support_containment_of_source_window_controls`, plus the constructor
  `source_window_controls_restricted_route_of_window_lambda`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Bridge
  ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for the final route theorem and the new window-control
  constructor/projections reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan over `ConnesWeilRH/**/*.lean` found no `Nonempty`,
  `.choose`, `choose_spec`, `exists ... True`, `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, or `unsafe`.
- Logic boundary preserved: this closes the restricted-route wrapper, but the
  upstream `WindowLambdaCompatibility` definition itself is still a conjunction
  and remains a later interface-hardening candidate.

2026-06-29

- Removed another positional conjunction surface in the restricted-to-full
  CCM25 route bridge.
- `SourceRestrictedQWLambdaDefinitionReadOff` is now a named structure with
  `qwLambdaFormulaReadOff` and `packageReadOff`, instead of
  `CCM25QWLambdaFormulaReadOff ∧ PackageBackedCCM25WeilFormReadOff`.
- `SourceFullQWDefinitionReadOff` is now a named structure with
  `qwDefinitionReadOff` and `packageReadOff`, instead of
  `CCM25QWDefinitionReadOff ∧ PackageBackedCCM25WeilFormReadOff`.
- Added route-level projections for the restricted/full definition read-off
  fields and removed the local `.2` projection at
  `package_read_off_of_qw_lambda_restriction`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Bridge
  ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for the final route theorem and the new definition read-off
  constructors/projections reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan over `ConnesWeilRH/**/*.lean` found no `Nonempty`,
  `.choose`, `choose_spec`, `exists ... True`, `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, or `unsafe`.
- Logic boundary preserved: this removes another hidden positional projection
  in the CCM25 restricted-to-full skeleton, but does not prove the analytic
  CC20 trace read-off or sign/defect bridge unconditionally.

2026-06-29

- Hardened the restricted-to-full scalar bridge in
  `ConnesWeilRH/Route/Bridge.lean`.
- Converted `SourceFinitePrimeEvaluatorSumsMatchForRestriction` from a bare
  equality into a named structure with both restricted/global evaluator-sum
  equality and common-atom restricted/global evaluator-sum equality.
- Converted `SourceArchimedeanPoleStabilityForRestriction` from a positional
  conjunction into a named structure exposing `poleNormalizationReadOff` and
  `packageReadOff`.
- Converted `SourceArchimedeanContributionMatchesForRestriction` from a bare
  equality into a named structure exposing the scalar contribution equality as
  `archimedeanContributionMatches`.
- Added route-level projections for the new restricted-to-full scalar bridge
  fields, including common-atom contribution read-off.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Bridge
  ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for the final route theorem and the new scalar bridge
  projections reported only `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan over `ConnesWeilRH/**/*.lean` found no `Nonempty`,
  `.choose`, `choose_spec`, `exists ... True`, `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, or `unsafe`.
- Logic boundary preserved: this makes the restricted-to-full scalar equality
  pathway more inspectable, but does not prove the analytic source trace
  read-off or sign/defect bridge unconditionally.

2026-06-29

- Converted `PackageFinitePrimeSupportStabilization` in
  `ConnesWeilRH/Route/Bridge.lean` from a long positional `Prop` conjunction
  into a named structure.
- The stabilization record now separately exposes global/restricted source
  index data, visible-atom lambda cuts, restricted/global index-set equality,
  restricted/global evaluator-sum equality, global/restricted finite-prime
  term sum read-offs, and global/restricted Von Mangoldt pairing sum read-offs.
- Added route-level projection theorems for the named stabilization fields,
  including `global_pairing_sum_of_package_stabilization` and
  `restricted_pairing_sum_of_package_stabilization`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Bridge
  ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for the final route theorem, package stabilization constructor,
  pairing-sum projections, and
  `finite_prime_stabilization_of_large_lambda_threshold` reported only
  `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan over `ConnesWeilRH/**/*.lean` found no `Nonempty`,
  `.choose`, `choose_spec`, `exists ... True`, `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, or `unsafe`.
- Logic boundary preserved: this removes a restricted-to-full finite-prime
  audit drift surface, but does not discharge the analytic trace/read-off or
  sign/defect source inputs.

2026-06-29

- Tightened the route-level CCM25 finite-prime sign ownership bridge.
- `SourceFinitePrimeSignOwnedByPackage` in `ConnesWeilRH/Route/Bridge.lean`
  now exposes global and restricted Von Mangoldt pairing sum read-offs in
  addition to the finite-prime term sums. These read-offs are populated from
  the package concrete finite-prime object, so the final sign side can audit
  both the term sum and the weight-times-pairing expansion through the same
  fixed-lambda object.
- Added route projections:
  `finite_prime_concrete_object_pairing_of_sign_owned_package`,
  `finite_prime_concrete_object_global_pairing_sum_of_sign_owned_package`, and
  `finite_prime_concrete_object_restricted_pairing_sum_of_sign_owned_package`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Bridge
  ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for the final route theorem and the new route-level pairing
  projections reported only `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan over `ConnesWeilRH/**/*.lean` found no `Nonempty`,
  `.choose`, `choose_spec`, `exists ... True`, `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, or `unsafe`.
- Logic boundary preserved: this closes another finite-prime sign ownership
  drift surface, but the analytic CCM25/CC20 source theorems, trace read-off,
  and sign/defect bridge remain source-conditional.

2026-06-29

- Pushed the CCM25 concrete finite-prime object down into the formula
  component layer.
- `GlobalFinitePrimeSumReadOff` and `RestrictedFinitePrimeSumReadOff` now
  carry the fixed-lambda `FixedLambdaFinitePrimeConcreteObject` plus an
  explicit certificate equality. Their constructors are `noncomputable def`
  because the concrete object is Type-level evidence.
- Added component/package projections showing global and restricted
  finite-prime term sums and Von Mangoldt pairing sums are read directly from
  the concrete object, not merely from a parallel certificate field.
- Added package-level certificate bridges tying the global and restricted
  component concrete objects back to the same common package certificate.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.GlobalComponent
  ConnesWeilRH.Source.CCM25Concrete.RestrictedComponent
  ConnesWeilRH.Source.CCM25Concrete.FormulaComponents
  ConnesWeilRH.Source.CCM25Concrete.Package`, then
  `lake build ConnesWeilRH.Route.Bridge
  ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for the final route theorem and the new concrete-object sum
  projections reported only `[propext, Classical.choice, Quot.sound]`.
- Weak loophole scan over `ConnesWeilRH/**/*.lean` found no `Nonempty`,
  `.choose`, `choose_spec`, `exists ... True`, `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, or `unsafe`.
- Logic boundary preserved: this removes another finite-prime normalization
  drift surface in the CCM25 Lean interface. It still does not discharge the
  analytic CCM25/CC20 source theorems or prove RH unconditionally.

2026-06-29

- Hardened the final sign/read-off bridge inputs in
  `ConnesWeilRH/Route/Bridge.lean`.
- `PackageBackedCCM25WeilFormReadOff` is now a named structure, not a
  tuple-shaped `Prop` conjunction. It exposes `windowLambdaCompatibility`,
  `qwDefinitionReadOff`, `psiSignReadOff`, `qwLambdaFormulaReadOff`,
  `poleNormalizationReadOff`, global/restricted finite-prime sum read-offs,
  and the three source-evaluator read-offs as named fields.
- `SourceCommonTestTupleContract` is now a named structure with
  `windowLambdaCompatibility`, `packageReadOff`, and `squareCompatibility`.
  `SourceQWUsesCommonTest` is now a named structure carrying the common tuple,
  package read-off, and convolution-square compatibility instead of aliasing a
  tuple contract.
- This removes the remaining hard-to-audit positional projections such as
  `h.2.2.2...` from the package-backed read-off and common-test bridge path.
- Earlier final sign bridge hardening is preserved: `SourceArchimedeanSignBridge`
  exposes trace legality, positive trace nonnegativity, CC20 sign/normalization,
  and Mellin/half-density convention; `SourceFinitePrimeSignOwnedByPackage`
  exposes finite-prime normalization plus global/restricted sum read-offs; and
  `SourceQWEqualsNegCC20WeilSum` keeps common-test, Psi expansion,
  archimedean sign, finite-prime sign, and pole-local-sum ownership visible.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Bridge`, then
  `lake build ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `[propext, Classical.choice, Quot.sound]`.
- Logic boundary preserved: this is source-conditional Lean interface
  hardening. It does not prove the analytic CCM25/CC20 sign equality,
  trace-class/cyclicity/no-defect read-off, or RH unconditionally.

2026-06-29

- Continued the CCM25 finite-prime concrete-object hardening pass.
- Added `FixedLambdaFinitePrimeConcreteObject` in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`. It binds
  one fixed-lambda arithmetic certificate to its exact support, source test,
  atom data, global/restricted index source data, Von Mangoldt weight read-off,
  source-evaluator pairing formula, pointwise finite-prime term formula, and
  global/restricted sum read-offs.
- Added constructors/projections through
  `ConnesWeilRH/Source/CCM25Concrete/Rows.lean`,
  `Interface.lean`, and `Package.lean`, including
  `finite_prime_concrete_object_of_package`. The package object is tied to the
  common certificate, so downstream code cannot mix support from one
  certificate with weight/pairing/term formulas from another.
- Updated `ConnesWeilRH/Route/Bridge.lean` so
  `SourceFinitePrimeSignOwnedByPackage` carries the fixed-lambda concrete
  finite-prime object in addition to finite-prime normalization and
  global/restricted sum read-offs.
- Because that object is Type-level evidence, upgraded
  `PrimePowerAtomStabilizationAtLarge`,
  `FinitePrimeStabilizationAtLarge`, and
  `RestrictedFinitePrimeSupportStabilizes` from Prop-style conjunctions into
  data-bearing structures/aliases, and changed downstream constructors from
  `theorem` to `def`/`noncomputable def` where Lean requires it.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Rows
  ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`,
  `lake build ConnesWeilRH.Route.Bridge`, and
  `lake build ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- Axiom audit for `ConnesWeilRH.Route.final_connes_weil_rh`,
  `ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate.concrete_object_of_arithmetic_certificate`,
  and
  `ConnesWeilRH.Route.finite_prime_concrete_object_term_of_sign_owned_package`
  reported only `[propext, Classical.choice, Quot.sound]`.
- Logic boundary preserved: this makes the fixed-lambda finite-prime
  support/weight/pairing/term object Lean-visible and consistently shared, but
  it still does not prove the analytic CCM25 source theorem or RH
  unconditionally.

2026-06-29

- Continued the Lean hardening pass on the first two objective blocks:
  `RHDefinitionBridge` and `CC20FiniteVanishingRhExit`.
- In `ConnesWeilRH/Source/RHDefinition.lean`, added
  `source_rh_point_iff_mathlib_components` and
  `source_rh_iff_mathlib_components`. These expose the exact Mathlib RH
  components at the bridge boundary: `riemannZeta s = 0`, negative-even
  exclusion, `s != 1`, and `s.re = 1 / 2`.
- In `ConnesWeilRH/Source/CC20RHExit.lean`,
  `SourceFiniteSetAdmissibilityForBridge` is now a named structure with
  `finiteSetAdmissible` and `finiteSetDisjointFromNontrivialZeros`, not a
  positional conjunction.
- In `ConnesWeilRH/Source/CC20.lean`, added
  `CC20FiniteVanishingRhExitWitness` plus named projections tying the source
  finite-vanishing package to the `CC20RHExitObjectPackage`. The
  `SourceObligation.statement` remains a non-empty Prop that requires the
  object package to equal the source-package conversion; it was not weakened
  to `exists witness, True`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.RHDefinition ConnesWeilRH.Source.CC20RHExit`,
  then
  `lake build ConnesWeilRH.Source.CC20 ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.
- Axiom audit for `ConnesWeilRH.Route.final_connes_weil_rh`,
  `ConnesWeilRH.Source.RHDefinitionBridge.source_rh_iff_mathlib_components`,
  and `ConnesWeilRH.Source.cc20_finite_vanishing_exit_witness_statement`
  reported only `[propext, Classical.choice, Quot.sound]`.
- Logic boundary preserved: this closes more definition-drift and witness
  audit surface, but the analytic CCM24/CCM25/CC20 source inputs remain
  source-conditional and RH is not proved unconditionally.

2026-06-29

- Cleaned up the remaining small Lean projection hotspots around the final
  exit.
- `SourceFiniteSetAdmissibility` in `ConnesWeilRH/Source/CC20RHExit.lean` is
  now a named structure with `zeroMem`, `halfMem`, `oneMem`, and
  `finiteSetIsTriple`, instead of a positional conjunction.
- `LedgersCleared` in `ConnesWeilRH/Route/Ledger.lean` is now a named
  structure with `rankKilled`, `poleKilled`, and `cdefExhausts`, instead of a
  positional conjunction.
- `ConnesWeilRH/Source/RHDefinition.lean` now exposes named projection
  theorems for `MathlibNontrivialZero` components before transporting back to
  the source zero predicate. This keeps the zeta-zero, nonnegative-even
  exclusion, and pole-exclusion legs inspectable at the definition bridge.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CC20RHExit ConnesWeilRH.Route.Ledger`, then
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `[propext, Classical.choice, Quot.sound]`.
- Logic boundary preserved: these are interface and auditability improvements;
  they do not discharge the source-conditional analytic inputs or prove RH
  unconditionally.

2026-06-29

- Hardened the fixed-lambda finite-prime exact-support path in
  `ConnesWeilRH/Route/Bridge.lean`.
- `PackageExactFinitePrimeSupportAtLambda` is now the actual
  `FinitePrimeExact.ExactSupportAtLambda` data, not a `Nonempty` wrapper.
- The direct exact-support data forced the downstream restricted-to-full guard
  layer to become data-bearing as well:
  `RestrictedToFullNoSpectralConvergenceImport`,
  `RestrictedToFullQWLowerBoundTransfer`, and
  `RestrictedToFullAllowedInputRows` now carry record evidence where they
  include exact-support or restriction-row data.
- Data-returning helpers were changed from theorem declarations to `def` or
  `noncomputable def` where required by Lean.
- WSL ext4 verification passed for
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this removes another Lean-visible wrapper around
  finite-prime exact support, but it still relies on the concrete CCM25 package
  data and does not prove the underlying analytic source theorem or RH
  unconditionally.

2026-06-29

- Hardened the threshold layer in `ConnesWeilRH/Route/Bridge.lean`.
- `FixedTestSupportThresholdAtLarge` is now the
  `FixedTestSupportCutoffData` record itself, not an `∃ cutoff, True`
  wrapper; window support and lambda compatibility now project directly from
  the record fields.
- `RestrictedToFullQWLambdaThreshold` is now the
  `RestrictedToFullQWLargeLambdaThreshold` record itself, not an
  `∃ threshold, True` wrapper.
- WSL ext4 verification passed for
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this tightens fixed-test threshold evidence in the
  restricted-to-full bridge, but it does not prove the analytic threshold or
  RH unconditionally.

2026-06-29

- Hardened the restricted-to-full `QW_lambda -> QW` core in
  `ConnesWeilRH/Route/Bridge.lean`.
- `SourceQWLambdaIsRestrictionOfQW` is now the
  `SourceQWLambdaRestrictionRows` record itself, not an `∃ rows, True`
  wrapper.
- `RestrictedToFullQWScalarRestrictionEquality` is now the
  `RestrictedToFullQWScalarRestrictionData` record itself, not an
  `∃ data, True` wrapper.
- The associated constructors were changed from theorem wrappers to `def`
  constructors, and downstream projections now read fields directly instead
  of using `choose`.
- WSL ext4 verification passed for
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH.Source.CC20RHExit ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this removes Lean-visible existential shells on
  the restricted-to-full scalar bridge, but it is still interface hardening,
  not an analytic proof of the CC20 trace read-off or RH unconditionally.

2026-06-29

- Hardened the route sign bridge contracts in `ConnesWeilRH/Route/Bridge.lean`:
  `RestrictedToFullQWBridgeContract` and `FinalSignBridgeContract` are now
  the data records themselves, not `∃ row, True` wrappers.
- This removed a real logical loophole: the bridge evidence can no longer be
  satisfied by an empty existence shell.
- WSL ext4 verification passed for
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH.Source.CC20RHExit ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this is bridge/interface hardening only, not a
  proof of CC20 trace-to-QW_lambda analytically or RH unconditionally.

2026-06-29

- Tightened the CC20 exit naming boundary so `CC20PropositionC1InputData`
  keeps the real `input.fullWeilPositivity` field instead of a misleading
  route-local `fullPositivityMatchesNonpositivity` name.
- `Route.RouteTheorem` now uses `fullWeilPositivity` consistently for the
  route-backed C.1 input data row, while the actual sign bridge remains
  isolated in `finalSignNonpositive : SourceQWNonnegativeToCC20Nonpositive`.
- WSL ext4 verification passed for
  `lake build ConnesWeilRH.Source.CC20RHExit ConnesWeilRH.Route.RouteTheorem
  ConnesWeilRH.Source.CC20 ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this is interface hardening only. It does not
  upgrade the source-conditional route to an unconditional RH proof.

2026-06-29

- Lowered the last remaining CCM25 package-level prime-power index facts
  (`one_lt` and lambda-cut companions) to the Rows / Interface layer.
- `ConnesWeilRH/Source/CCM25Concrete/Rows.lean` now proves
  `arithmetic_global_index_one_lt_of_arithmetic_rows`,
  `arithmetic_restricted_index_source_data_of_arithmetic_rows`, and
  `arithmetic_restricted_index_one_lt_of_arithmetic_rows` from the grouped
  arithmetic rows.
- `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` now exposes the same
  `one_lt` and source-data projections publicly.
- `ConnesWeilRH/Source/CCM25Concrete/Package.lean` now specializes the new
  interface projections for the global and restricted `one_lt` statements and
  source-data packaging, instead of directly invoking the low-level certificate
  one-lt/source-data lemmas.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Rows
  ConnesWeilRH.Source.CCM25Concrete.Interface
  ConnesWeilRH.Source.CCM25Concrete.Package`, then
  `lake build ConnesWeilRH`.
- `#print axioms` for the new rows/interface `one_lt` and source-data
  projections, the package global/restricted specializations, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no direct package-layer calls remain to
  `source_prime_power_index_one_lt`, `source_lambda_cut_one_lt`,
  `arithmetic_global_index_one_lt_of_certificate`, or
  `arithmetic_restricted_index_one_lt_of_certificate`; no `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, or `unsafe` appears under `ConnesWeilRH`.
  `git diff --check` reported only CRLF warnings.
- Logic boundary preserved: this is still interface hardening, not a proof of
  CCM25 source-paper exact support or RH unconditionally. It moves the `one_lt`
  and lambda-cut ownership to the concrete arithmetic rows before package-level
  specialization.

- Lowered the remaining CCM25 support/index/cut source-data packaging from the
  fixed-test package layer into the concrete rows and public interface layers.
- `ConnesWeilRH/Source/CCM25Concrete/Rows.lean` now proves
  `arithmetic_global_index_source_data_of_arithmetic_rows` and
  `arithmetic_restricted_index_source_data_of_arithmetic_rows` directly from
  `ConcreteCCM25ArithmeticRows`.
- `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` exposes the same two
  source-data projections through the public interface namespace.
- `ConnesWeilRH/Source/CCM25Concrete/Package.lean` now proves
  `common_certificate_global_index_source_data_of_package` and
  `common_certificate_restricted_index_source_data_of_package` by specializing
  the new interface projections, instead of re-deriving the source data from
  `FinitePrimeCertificate.arithmetic_*_source_data_of_certificate` inside the
  package layer.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Rows
  ConnesWeilRH.Source.CCM25Concrete.Interface
  ConnesWeilRH.Source.CCM25Concrete.Package`, then
  `lake build ConnesWeilRH`.
- `#print axioms` for the new rows/interface source-data projections, the
  package global/restricted source-data specializations, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no direct package-layer calls remain to
  `arithmetic_global_index_source_data_of_certificate` or
  `arithmetic_restricted_index_source_data_of_certificate`; no `sorry`,
  `admit`, `axiom`, `constant`, `opaque`, or `unsafe` appears under
  `ConnesWeilRH`. `git diff --check` reported only CRLF warnings.
- Logic boundary preserved: this is still interface hardening, not a proof of
  CCM25 source-paper support exactness or RH unconditionally. It only moves the
  source-data packaging authority down to the arithmetic rows before package
  specialization.

- Lowered CCM25 source weight, source pairing, and finite-prime term evaluator
  projections from the fixed-test package layer into the concrete rows layer.
- `ConnesWeilRH/Source/CCM25Concrete/Rows.lean` now proves
  `arithmetic_source_weight_read_off_of_arithmetic_rows`,
  `arithmetic_source_pairing_formula_source_evaluator_of_arithmetic_rows`,
  and `arithmetic_finite_prime_term_formula_source_evaluator_of_arithmetic_rows`
  directly from `ConcreteCCM25ArithmeticRows` and its fixed-lambda arithmetic
  certificate.
- `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` exposes the same three
  projections through the public concrete interface namespace.
- `ConnesWeilRH/Source/CCM25Concrete/Package.lean` now proves the global and
  restricted fixed-test weight, pairing, and finite-prime term formula
  projections by specializing the `Interface.arithmetic_*` projections, rather
  than calling the lower `PrimePowerArithmetic` atom formulas directly.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Rows
  ConnesWeilRH.Source.CCM25Concrete.Interface
  ConnesWeilRH.Source.CCM25Concrete.Package`, then
  `lake build ConnesWeilRH`.
- `#print axioms` for the new rows/interface source-weight, source-pairing,
  finite-prime-term projections, the package global/restricted specializations,
  and `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: the package layer now references
  `Interface.arithmetic_source_weight_read_off_of_arithmetic_rows` and
  `Interface.arithmetic_source_pairing_formula_source_evaluator_of_arithmetic_rows`
  for these formulas; no `sorry`, `admit`, `axiom`, `constant`, `opaque`, or
  `unsafe` appears under `ConnesWeilRH`. `git diff --check` reported only CRLF
  warnings.
- Logic boundary preserved: this does not prove the source-paper CCM25
  analytic rows or RH unconditionally. It moves the source Lambda/pairing/term
  read-off ownership to the concrete arithmetic rows before package-level
  fixed-test specialization.

- Split the remaining top-level CCM25 concrete row statements into named row
  groups.
- `ConnesWeilRH/Source/CCM25Concrete/Rows.lean` now has
  `ConcreteGlobalQWPsiRows`, `ConcreteRestrictedQWLambdaRows`, and
  `ConcretePoleNormalizationRows`. `ConcreteCCM25Rows`,
  `ConcreteCCM25AtomRows`, and `ConcreteCCM25ArithmeticRows` now carry those
  grouped rows as `globalRows`, `restrictedRows`, and `poleRows`, instead of
  carrying `qwDefinition`, `psiSign`, `qwLambdaFormula`, and
  `poleNormalization` directly at the top level.
- Updated `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` so
  `ccm25_interface_of_concrete_rows` projects QW/Psi, restricted
  `QW_lambda`, and pole normalization through the grouped row projections.
- Updated `GlobalComponent.lean` and `RestrictedComponent.lean` so their
  arithmetic-row constructors consume the grouped-row projections through
  `Interface.qw_definition_of_arithmetic_rows`,
  `Interface.psi_sign_of_arithmetic_rows`, and
  `Interface.qw_lambda_formula_of_arithmetic_rows`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Rows
  ConnesWeilRH.Source.CCM25Concrete.Interface
  ConnesWeilRH.Source.CCM25Concrete.GlobalComponent
  ConnesWeilRH.Source.CCM25Concrete.RestrictedComponent
  ConnesWeilRH.Source.CCM25Concrete.Package`, then
  `lake build ConnesWeilRH`.
- `#print axioms` for grouped-row QW/Psi/`QW_lambda`/pole projections,
  `CCM25Concrete.Interface.ccm25_interface_of_arithmetic_rows`,
  source-object QW/pole projections, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no `sorry`, `admit`, `axiom`, `constant`, `opaque`, or
  `unsafe` under `ConnesWeilRH`; `git diff --check` reported only CRLF
  warnings.
- Logic boundary preserved: this is still interface hardening, not a proof of
  the CCM25 analytic source rows or RH. The benefit is that the rows now expose
  the global QW/Psi, restricted `QW_lambda`, and pole-normalization obligations
  as separate named groups before compact-interface assembly.

- Further minimized the CCM25 expanded source-object package after the
  concrete rows hardening.
- `ConnesWeilRH/Source/Objects.lean` now makes
  `CCM25WeilObjectPackage` carry only `weilSymbols` and
  `CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows weilSymbols`. Removed the
  unused loose finite-prime/source bridge fields:
  `sourcePrimePowerIndex`, `sourceRestrictedLambdaCut`,
  `sourceVonMangoldtWeight`, `sourcePrimePowerPairing`,
  `sourceGlobalPrimePowerSupport`, `sourceRestrictedPrimePowerSupport`,
  `sourceVisibilityBeforeCut`, `sourceFixedSVisiblePrimeAdmissibility`,
  `sourceVonMangoldtWeightReadOff`, `sourcePrimePowerPairingReadOff`,
  `sourceFinitePrimeSignOwnership`, `sourceArchimedeanSignBridge`,
  `sourceRestrictionBridge`, and `restrictedToFullQWBridgeContract`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.Objects
  ConnesWeilRH.Source.ObjectDerivations ConnesWeilRH.Source.CCM25`, then
  `lake build ConnesWeilRH`.
- `#print axioms` for every source-object CCM25 projection, for
  `CCM25Interface.ofSourceObjectPackage`, and for
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: none of the removed CCM25 source-object fields remain in
  `Objects.lean`, `ObjectDerivations.lean`, or `CCM25.lean`; no `sorry`,
  `admit`, `axiom`, `constant`, `opaque`, or `unsafe` appears under
  `ConnesWeilRH`. `git diff --check` reported only CRLF warnings.
- Logic boundary preserved: this still does not prove CCM25 source-paper
  analytic rows or RH unconditionally. It removes unused broad `Prop` and
  source-local finite-prime escape hatches from the expanded source-object
  package.

- Hardened the CCM25 source-object boundary so compact CCM25 statements are
  now derived from concrete arithmetic rows rather than replaceable broad
  source-object fields.
- Added `ConnesWeilRH/Source/CCM25Concrete/Rows.lean` as the lower concrete
  rows layer below `CCM25Interface`. It defines `ConcreteCCM25Rows`,
  `ConcreteCCM25AtomRows`, and `ConcreteCCM25ArithmeticRows`, plus projections
  from arithmetic rows to QW definition, Psi sign, `QW_lambda`, finite-prime
  normalization, pointwise term normalization, source-test read-offs, and pole
  normalization.
- Updated `ConnesWeilRH/Source/Objects.lean` so
  `CCM25WeilObjectPackage` carries
  `CCM25Concrete.Rows.ConcreteCCM25ArithmeticRows weilSymbols` and no longer
  carries the broad fields `sourceQWDefinition`, `sourcePsiSignSplit`,
  `sourceRestrictedQWLambdaFormula`, `sourceFinitePrimePointwiseTerm`,
  `sourceFinitePrimeNormalization`, or `sourcePoleNormalization`.
- Updated `ConnesWeilRH/Source/ObjectDerivations.lean` so
  `SourceObjectPackage.provesQWDefinitionStatement`,
  `provesPsiSignStatement`, `provesQWLambdaFormulaStatement`,
  `provesFinitePrimeNormalizationStatement`,
  `provesFinitePrimePointwiseTermStatement`, and
  `provesPoleNormalizationStatement` all project through
  `CCM25Concrete.Rows`.
- Broke an import cycle by lowering
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrime.lean` from
  `ConnesWeilRH.Source.CCM25` to `ConnesWeilRH.Basic` and removing unused
  compact-interface projection theorems from that low-level finite-prime
  definitions file.
- Updated `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` so its concrete
  row names are abbrevs of `CCM25Concrete.Rows`, preserving existing component
  and package callers without creating a second row type.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Rows
  ConnesWeilRH.Source.Objects ConnesWeilRH.Source.ObjectDerivations
  ConnesWeilRH.Source.CCM25`, then
  `lake build ConnesWeilRH.Source.CCM25Concrete ConnesWeilRH`.
- `#print axioms` for the new rows projections, source-object CCM25
  derivations, `CCM25Interface.finite_prime_pointwise_term_of_source_object_package`,
  and `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no stale CCM25 broad source-object fields, no `sorry`,
  `admit`, `axiom`, `constant`, `opaque`, or `unsafe`, and no route-layer
  `structure/def/theorem .*SourceObject`. `git diff --check` reported only
  CRLF warnings.
- Logic boundary preserved: this does not prove CCM25 analytic arithmetic
  rows or RH unconditionally. It removes one Lean-visible drift loophole by
  forcing the expanded source-object package to consume the concrete arithmetic
  row path.

- Synced the public GitHub `README.md` to the latest Connes-Weil route and
  Lean-interface status.
- The README now states the current boundary up front: local route-evidence
  composition is closed at proof-package level, the pre-Lean matrix is
  complete, accepted-source and external referee certification remain open,
  the Lean route theorem is certificate-conditional, and an unconditional Lean
  RH theorem remains open.
- Added the current Lean theorem shape
  `RouteCertificate inputs -> _root_.RiemannHypothesis`, plus the explicit
  non-claim that the repository does not yet prove
  `theorem final_rh : _root_.RiemannHypothesis`.
- Added the latest source-object interface progress:
  `RouteInputs.ofExpandedSourcePackage`,
  `SourceBackedFixedSTest.ofExpandedSourcePackage`,
  `SourceTraceReadOffData.ofExpandedSourcePackage`,
  `route_certificate_of_expanded_source_package`,
  `ExpandedSourceFixedSTestFrontEnd`,
  `ExpandedSourceTraceReadOffFrontEnd`, and
  `ExpandedSourceRouteCertificateFrontEnd`.
- Added the current hard-input boundary:
  `SourceSignDefectClassification`,
  `RestrictedToFullQWBridgeContract`,
  `FinalSignBridgeContract`, and the explicit full/restricted trace-to-QW
  read-off bridges.
- Reflected the newest Lean guardrails in public-facing language:
  `RHDefinitionBridge.source_rh_to_mathlib_rh`, CC20 finite-vanishing package
  authority, CCM25 fixed-lambda exact support projection, CCM25 common atoms,
  package-owned fixed-test `QW_lambda = QW` scalar read-off, and
  `RestrictedToFullAllowedInputRows`.
- Preserved the public boundary: these are interface safeguards and
  source-conditional route evidence, not accepted-source certification,
  journal/Clay certification, or an unconditional Lean proof of RH.
- README hygiene checks passed: all listed local path references exist,
  public-hygiene grep found no internal `外部意见`, `MEMORY`, `AGENTS`, local
  absolute path, archive, zip, SHA256, `.git`, or `.lake` leakage, and
  `git diff --check README.md` reported only the existing LF-to-CRLF warning.

- Revised the Zulip plain-text draft style in
  `external-opinions/zulip-connes-weil-rh-feedback-post-plain.txt`.
- Clarified the notation `I` on first use as the support window/interval used
  to localize the fixed test, while preserving the route notation
  `(S,I,lambda,J)`.
- Removed sentence-final periods from standalone displayed formula lines so the
  draft reads more like a Zulip discussion post and less like a paper fragment.
- Kept the draft plain text with no Markdown code fences or bullet syntax.

- Reworked `external-opinions/zulip-connes-weil-rh-feedback-post-plain.txt` from a
  Lean-heavy status note into a mathematics-first Zulip draft for `#maths`.
- The revised draft now leads with the proof route:
  `F_g = g^* * g`, finite-lambda positive trace, trace read-off into
  `QW_lambda + Rank + PoleJetExtra + R`, triple-vanishing ledger killing,
  endpoint-strip `Cdef` exhaustion, fixed-test `QW_lambda = QW`, final sign
  bridge, and the Connes-Consani finite-vanishing exit to Mathlib RH.
- Lean content was reduced to a minimal boundary snippet
  `RouteCertificate -> final_connes_weil_rh`, plus a short current-status
  paragraph naming the remaining hard route inputs:
  `SourceSignDefectClassification`, `RestrictedToFullQWBridgeContract`,
  `FinalSignBridgeContract`, and trace-to-QW read-off bridges.
- The draft still records the latest Lean guardrails:
  `RHDefinitionBridge.source_rh_to_mathlib_rh`, CCM25 package-owned
  fixed-lambda exact support, and package-owned fixed-test
  `QW_lambda = QW` scalar read-off. These are described as interface
  safeguards, not analytic source theorem proofs.

- Added an explicit restricted-to-full allowed-input guard for the CCM25
  fixed-test scalar bridge.
- `ConnesWeilRH/Route/Bridge.lean` now defines
  `RestrictedToFullAllowedInputRows`, listing the actual permitted evidence:
  common tuple, fixed-test support threshold, prime-power atom stabilization,
  finite-prime stabilization, exact finite-prime support, restriction rows,
  finite-prime evaluator sum equality, archimedean/pole stability,
  archimedean contribution balance, the existing no-spectral-convergence
  witness, and lower-bound evidence.
- Added guard aliases
  `RestrictedToFullNoFiniteOperatorSpectralConvergenceImport`,
  `RestrictedToFullNoDeterminantConvergenceImport`, and
  `RestrictedToFullNoNumericalEigenvalueImport`, all defined through the same
  allowed-input row set rather than by adding new convergence assumptions.
- Added contract projections
  `restricted_to_full_allowed_input_rows_of_contract`,
  `no_finite_operator_spectral_convergence_import_of_contract`,
  `no_determinant_convergence_import_of_contract`, and
  `no_numerical_eigenvalue_import_of_contract`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the allowed-input row projection, the three forbidden
  convergence guard projections,
  `restricted_to_full_bridge_contract_of_common_tuple`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no stale RH transport field, no stale CC20 source-object
  duplicate finite-set fields, no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, or `unsafe`, and no route-layer
  `structure/def/theorem .*SourceObject`.
- Logic boundary preserved: the guard does not prove restricted-to-full
  analytically. It makes the accepted evidence shape explicit and excludes
  replacing the current fixed-test scalar bridge with spectral, determinant, or
  numerical eigenvalue convergence imports.

- Created a timestamped workspace cryptographic archive under `external-opinions/`.
- Final files:
  `external-opinions/connes-weil-rh-workspace-20260629-063945.zip`,
  `external-opinions/connes-weil-rh-workspace-20260629-063945.manifest.sha256.txt`,
  and `external-opinions/connes-weil-rh-workspace-20260629-063945.zip.sha256.txt`.
- The archive was created at local time `2026-06-29T06:39:45+08:00`.
  ZIP SHA256:
  `f49fa3ab7f38bd870b0f1fb1d7e690eb2f43a125390bff876274048c212073c0`.
- Scope: source/workspace files with a per-file SHA256 manifest. Excluded
  generated/heavy/cyclic directories and archive artifacts:
  `.git`, `.lake`, `.codegraph`, `node_modules`, `__pycache__`, `*.zip`,
  `*.7z`, `*.tar`, `*.gz`, `*.tmp`, `*.manifest.sha256.txt`, and
  `*.zip.sha256.txt`.

- Moved the CCM25 fixed-test `QW_lambda = QW` scalar read-off through the
  source-owned package layer.
- `ConnesWeilRH/Source/CCM25Concrete/Package.lean` now proves
  `source_common_restricted_sum_eq_common_global_of_package`,
  `common_atom_archimedean_contribution_matches_of_package`,
  `qw_lambda_eq_qw_of_common_atom_archimedean_contribution`, and
  `qw_lambda_eq_qw_of_archimedean_contribution`.
- These theorems keep the sign structure visible: `QW_lambda` is read as
  `archimedean + pole - restricted finite-prime evaluator`, while `QW` is read
  as `pole functional - archimedean - global finite-prime evaluator`; equality
  requires the explicit archimedean/pole balance plus the package finite-prime
  common-atom read-offs.
- `ConnesWeilRH/Route/Bridge.lean` now delegates
  `package_backed_source_common_restricted_sum_eq_common_global`,
  `source_common_atom_archimedean_contribution_matches_of_package`, and
  `scalar_equality_from_common_atom_witness_components` to the source package
  theorems instead of reconstructing those calculations in the route layer.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package
  ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new package common-sum equality, common-atom
  archimedean contribution bridge, package scalar equalities, route scalar
  equality, and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no stale RH transport field, no stale CC20 source-object
  duplicate finite-set fields, no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, or `unsafe`, and no route-layer
  `structure/def/theorem .*SourceObject`.
- Logic boundary preserved: this does not prove the analytic archimedean/pole
  balance. It makes the finite-prime and scalar read-off calculation
  source-package-owned once that balance is supplied.

- Added a plain-text Zulip discussion draft under
  `external-opinions/zulip-connes-weil-rh-feedback-post-plain.txt`.
- The draft is intentionally not a proof announcement. It states that the
  current Lean theorem is still certificate-conditional, shows the real
  `RouteCertificate`, `ExpandedSourceRouteCertificateFrontEnd`, and
  `RouteBridgeCertificate` shapes, and asks for feedback on trace-scale,
  sign/defect, restricted-to-full, final sign, and RH-definition bridges.
- Updated the draft to match the latest Lean interface-hardening status:
  source-object packages now reach the route-certificate boundary, while
  `SourceSignDefectClassification`, `RestrictedToFullQWBridgeContract`,
  `FinalSignBridgeContract`, and trace-to-QW read-off bridges remain explicit
  hard inputs.
- Also recorded the latest guardrails in the draft: source-RH to Mathlib-RH
  transport now goes through `RHDefinitionBridge.source_rh_to_mathlib_rh`, and
  fixed-lambda exact finite-prime support is projected from the CCM25 concrete
  arithmetic package before route consumption. These are interface safeguards,
  not analytic proofs or unconditional RH.

- Moved the package-level CCM25 exact finite-prime support projection into the
  source-owned concrete package layer.
- `ConnesWeilRH/Source/CCM25Concrete/Package.lean` now defines
  `exact_support_of_package` from the package common finite-prime arithmetic
  certificate, plus source-facing projections:
  `exact_support_uses_common_certificate_of_package`,
  `visibility_at_lambda_of_package_exact_support`,
  `global_exact_of_package_exact_support`,
  `restricted_exact_of_package_exact_support`,
  `visible_atoms_in_lambda_cut_of_package_exact_support`, and
  `exact_support_source_test_eq_package_source_test`.
- `ConnesWeilRH/Route/Bridge.lean` now consumes
  `Source.CCM25Concrete.Package.exact_support_of_package` instead of unfolding
  the finite-prime certificate construction locally in the route layer.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package
  ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new package exact-support projection, package
  visibility theorem, source-test equality theorem, route wrapper, route
  source-test wrapper, and `ConnesWeilRH.Route.final_connes_weil_rh` reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no stale RH transport field, no stale CC20 source-object
  duplicate finite-set fields, no `sorry`, `admit`, `axiom`, `constant`,
  `opaque`, or `unsafe`, and no route-layer
  `structure/def/theorem .*SourceObject`.
- Logic boundary preserved: this makes fixed-`lambda` exact support a
  CCM25Concrete package projection before the route consumes it. It does not
  prove CCM25 from the source paper; it prevents the route layer from owning
  finite-prime support construction details.

- Hardened the CC20 finite-vanishing exit authority inside the expanded
  source-object package.
- Removed the duplicate source-object finite-set fields
  `finiteVanishingSet`, `finiteSetIsZeroHalfOne`, `finiteSetAdmissible`, and
  `finiteSetAdmissibleData` from
  `SourceObject.CC20RHExitObjectPackage`.
- Updated `SourceObjectPackage.toFiniteVanishingCriterionPackage` so it is a
  projection of
  `pkg.cc20RHExit.sourceFiniteVanishingCriterionPackage` rather than a second
  independently assembled compact criterion.
- Updated `provesFiniteSetAdmissible` to derive admissibility from
  `SourceFiniteVanishingCriterionPackage.finite_set_admissible_of_source_package`.
- Updated the finite-vanishing factorization theorem so the compact criterion
  factors through
  `pkg.cc20RHExit.sourceFiniteVanishingCriterionPackage.sourceCriterion` and
  then through `RHDefinitionBridge.source_rh_to_mathlib_rh`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.Objects
  ConnesWeilRH.Source.ObjectDerivations ConnesWeilRH.Source.CC20` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the source-object finite-vanishing projection,
  admissibility proof, factorization theorem,
  `CC20Interface.finite_vanishing_mathlib_rh_of_c1_input_data`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no stale `sourceRH_to_mathlibRH`, no stale
  source-object duplicate finite-set projections, no `sorry`, `admit`,
  `axiom`, `constant`, `opaque`, or `unsafe`, and no route-layer
  `structure/def/theorem .*SourceObject`.
- Logic boundary preserved: this chooses one Lean authority for the CC20
  finite-vanishing package. It still does not prove the analytic CC20
  Proposition C.1 source criterion.

- Hardened the RH definition bridge at the expanded source-object boundary.
- Removed the free `sourceRH_to_mathlibRH : rhDefinitionBridge.SourceRH → RH`
  field from `SourceObject.CC20RHExitObjectPackage` and removed the loose
  `sourceRH_to_mathlibRH : Prop` field from `SourceObjectPackage`.
- Updated `SourceObjectPackage.toFiniteVanishingCriterionPackage` and the
  source-object-backed CC20 factorization theorem so every source-RH to Mathlib
  RH transport now calls
  `RHDefinitionBridge.source_rh_to_mathlib_rh
  pkg.cc20RHExit.rhDefinitionBridge` directly.
- Verified there are no remaining Lean-source matches for
  `sourceRH_to_mathlibRH`; the expanded source package can no longer supply a
  route-local arbitrary RH transport function.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.Objects
  ConnesWeilRH.Source.ObjectDerivations ConnesWeilRH.Source.CC20` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the changed finite-vanishing derivation path,
  `RHDefinitionBridge.source_rh_to_mathlib_rh`,
  `RHDefinitionBridge.source_rh_to_mathlib_rh_direct`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no `sourceRH_to_mathlibRH`, `allGood`, `everything`,
  `complete`, `exitWorks`, `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and no `structure/def/theorem .*SourceObject` under
  `ConnesWeilRH/Route`.
- Logic boundary preserved: this closes a definition-drift loophole only. It
  does not prove the source CC20 finite-vanishing criterion, nor does it make
  RH unconditional.

- Added the expanded source-package route-certificate assembly layer.
- `ConnesWeilRH/Route/RouteTheorem.lean` now defines
  `ExpandedSourceRouteCertificateFrontEnd`, which groups only the downstream
  route-certificate evidence that is still hard: `RouteLedgers`,
  `SourceSignDefectClassification`, `RestrictedToFullQWBridgeContract`, and
  `FinalSignBridgeContract`.
- Added `route_certificate_of_expanded_source_package`, connecting the expanded
  source package, fixed-S front end, trace-read-off front end, and explicit
  hard route bridges to the existing
  `route_certificate_of_sign_defect_classification`.
- Added projection checks
  `route_certificate_ledgers_of_expanded_source_package` and
  `route_certificate_source_trace_lambda_of_expanded_source_package`, proving
  by `rfl` that the assembled certificate uses the supplied ledger package and
  trace-front lambda.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.RouteTheorem` and `lake build ConnesWeilRH`.
- `#print axioms` for the expanded route-certificate constructor, its two
  projection checks, and `ConnesWeilRH.Route.final_connes_weil_rh` reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Grep gates passed: no `allGood`, `everything`, `complete`, `exitWorks`,
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, and no
  `structure/def/theorem .*SourceObject` under `ConnesWeilRH/Route`.
- Logic boundary preserved: the source-object package now reaches the route
  certificate boundary, but sign/defect classification, restricted-to-full
  scalar equality, and final sign normalization remain explicit inputs. This
  is still source-conditional interface hardening, not an unconditional RH
  proof.

- Added the first source-object-backed trace-read-off constructor for Theorem 1.
- `ConnesWeilRH/Route/Theorem1.lean` now defines
  `ExpandedSourceTraceReadOffFrontEnd`, carrying the still-hard trace-read-off
  inputs: the lambda, one-lt-lambda proof, concrete CCM25 arithmetic package,
  test/quotient compatibility, fixed-S support-square transport, and full plus
  restricted trace-read-off bridges.
- Added `SourceTraceReadOffData.ofExpandedSourcePackage`. It constructs
  `SourceTraceReadOffData` for the source-object-backed fixed-S test by taking
  the CC20 trace test, Hilbert-Schmidt gate, and positive-trace nonnegativity
  from the expanded CC20 trace object package.
- The constructor deliberately does not prove the full or restricted
  trace-to-QW equalities. Those remain explicit bridge fields in
  `ExpandedSourceTraceReadOffFrontEnd`, matching the hard boundary for
  `CC20 trace -> QW_lambda`.
- Added projection checks
  `SourceTraceReadOffData.archimedean_test_of_expanded_source_package` and
  `SourceTraceReadOffData.lambda_of_expanded_source_package`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1` and `lake build ConnesWeilRH`.
- Grep gates passed: no `allGood`, `everything`, `complete`, `exitWorks`,
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, and no
  `structure/def/theorem .*SourceObject` under `ConnesWeilRH/Route`.
- `#print axioms` for the expanded trace-read-off constructor, its projection
  theorems, `fixed_s_read_off_of_source_trace_data`,
  `trace_weil_compatibility_of_source_trace_data`, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this moves CC20 trace legality and positivity into
  the expanded source-object boundary, but the actual trace-to-Weil read-off
  equalities and downstream sign/defect bridge are still not proved.

- Added the first source-object-backed fixed-S test constructor.
- `ConnesWeilRH/Source/Objects.lean` now requires the expanded CCM24 package to
  carry direct fixed-test evidence: canonical model data, source support and
  Fourier support in the fixed window, Sonin-space comparison, lambda-window
  containment, and the lambda-compatibility bridge. This prevents the route
  fixed-S test from being built only from broad CCM24 theorem statements.
- `ConnesWeilRH/Route/Definitions.lean` now has
  `ExpandedSourceFixedSTestFrontEnd`, which explicitly carries the route-facing
  `FixedSTest`, admissible-window proof, triple-vanishing symbols and bridge,
  and finite-prime-visibility bridge.
- Added
  `SourceBackedFixedSTest.ofExpandedSourcePackage`, constructing a
  `SourceBackedFixedSTest (RouteInputs.ofExpandedSourcePackage pkg)` from the
  expanded source package plus the explicit fixed-test front end.
- Added projection checks
  `weil_test_of_expanded_source_package` and
  `semilocal_window_of_expanded_source_package`, confirming the constructed
  route test uses the common source test and CCM24 source window.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.Objects
  ConnesWeilRH.Route.Definitions` and `lake build ConnesWeilRH`.
- Grep gates passed: no `allGood`, `everything`, `complete`, `exitWorks`,
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, `unsafe`, and no
  `structure/def/theorem .*SourceObject` under `ConnesWeilRH/Route`.
- `#print axioms` for `RouteInputs.ofExpandedSourcePackage`,
  `SourceBackedFixedSTest.ofExpandedSourcePackage`, the source-test/window
  projections, and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this constructs only the fixed-S route test from
  expanded source objects plus explicit front-end evidence. It still does not
  construct `SourceTraceReadOffData`, restricted-to-full, final sign,
  sign/defect, or a final route certificate.

- Connected the expanded source-object package to the route input boundary.
- Added `ConnesWeilRH.Route.RouteInputs.ofExpandedSourcePackage` in
  `ConnesWeilRH/Route/Definitions.lean`. It constructs the compact
  `RouteInputs` triple from:
  `CCM24Interface.ofSourceObjectPackage`,
  `CCM25Interface.ofSourceObjectPackage`, and
  `CC20Interface.ofSourceObjectPackage`.
- The constructor deliberately stops at `RouteInputs`. It does not construct a
  `SourceBackedFixedSTest`, `SourceTraceReadOffData`, `RouteBridgeCertificate`,
  restricted-to-full bridge, final sign bridge, or full route certificate.
  Those remain hard obligations and cannot be smuggled in through the expanded
  source-object package.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Definitions` and `lake build ConnesWeilRH`.
- Grep gates passed: no `allGood`, `everything`, `complete`, `exitWorks`,
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, or `unsafe`; no
  `structure/def/theorem .*SourceObject` under `ConnesWeilRH/Route`.
- `#print axioms` for `RouteInputs.ofExpandedSourcePackage`,
  the source-object-to-CCM24/CCM25/CC20 constructors, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: the route can now start from expanded source
  objects at the input layer, but the full RH route still requires separate
  fixed-S admissibility, trace/read-off, restricted-to-full, sign/defect, and
  final bridge certificates.

- Wired the expanded source-object package into the source interfaces.
- `ConnesWeilRH/Source/CCM24.lean` now has
  `CCM24Interface.ofSourceObjectPackage`, deriving the compact CCM24 interface
  from `SourceObjectPackage.toSemilocalModelSymbols` and the source-object
  semilocal projection theorems.
- `ConnesWeilRH/Source/CCM25.lean` now has
  `CCM25Interface.ofSourceObjectPackage`, deriving the compact CCM25 interface
  from `SourceObjectPackage.toWeilFormSymbols`, and exposes
  `finite_prime_pointwise_term_of_source_object_package` so pointwise
  finite-prime normalization remains visible before any sum-level use.
- `ConnesWeilRH/Source/CC20RHExit.lean` now has
  `SourceFiniteVanishingCriterionPackage.toCC20RHExitObjectPackage`, the
  reverse bridge from the source-RH finite-vanishing package back to the
  existing CC20 RH-exit object package.
- `ConnesWeilRH/Source/Objects.lean` now binds the expanded
  `CC20RHExitObjectPackage` to an explicit `RHDefinitionBridge` and an
  existing `SourceFiniteVanishingCriterionPackage`. This removes the temporary
  free `sourceRH : Prop` and blocks a fresh RH-name-drift loophole.
- `ConnesWeilRH/Source/CC20.lean` now has
  `CC20Interface.ofSourceObjectPackage`, so the full compact CC20 interface can
  be constructed from the expanded source-object package without adding route
  fields.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CC20RHExit
  ConnesWeilRH.Source.Objects ConnesWeilRH.Source.ObjectDerivations
  ConnesWeilRH.Source.CCM24 ConnesWeilRH.Source.CCM25
  ConnesWeilRH.Source.CC20` and `lake build ConnesWeilRH`.
- Grep/diff gates passed: no route-module diff, no `sorry`, `admit`, `axiom`,
  `constant`, `opaque`, `unsafe`, or opaque package field names in
  `ConnesWeilRH/**/*.lean`.
- `#print axioms` for the source-object-to-CCM24/CCM25/CC20 constructors,
  the finite-vanishing reverse bridge, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: source-object packages now wire into source
  interfaces, but the analytic CCM24/CCM25/CC20 theorem content remains source
  package input. This still is not an unconditional RH proof.

- Added the first expanded source-object interface pass.
- Created `ConnesWeilRH/Source/Objects.lean` with source-boundary records under
  `ConnesWeilRH.Source.SourceObject`: `CommonTestObject`,
  `CCM24SemilocalObjectPackage`, `CCM25WeilObjectPackage`,
  `CC20TraceObjectPackage`, `CC20RHExitObjectPackage`, and
  `SourceObjectPackage`.
- Created `ConnesWeilRH/Source/ObjectDerivations.lean`, deriving the compact
  route-facing records from `SourceObjectPackage`:
  `SemilocalModelSymbols`, `WeilFormSymbols`, `ArchimedeanTraceSymbols`, and
  `FiniteVanishingCriterionPackage`.
- The derivation keeps the key hard gates visible: common source test and
  convolution square, fixed CCM24 window, pointwise CCM25 finite-prime term
  normalization, restricted-to-full bridge contract, trace legality before
  read-off, seven sign/defect rows including
  `cc20PostQRemainderFixedSSoninTransport`, final `QW` sign bridge, and
  source-RH-to-Mathlib-RH transport.
- During the Lean check, the initial attempt exposed a real interface weakness:
  `finiteSetAdmissible : Prop` alone was only a proposition name. The expanded
  CC20 RH-exit package now includes
  `finiteSetAdmissibleData : finiteSetAdmissible`, so the derived compact
  `FiniteVanishingCriterionPackage` cannot claim finite-set admissibility
  without evidence.
- WSL ext4 verification passed in the disposable verification copy:
  `lake build ConnesWeilRH.Source.Objects
  ConnesWeilRH.Source.ObjectDerivations` and `lake build ConnesWeilRH`.
- Grep gate passed for no `allGood`, `everything`, `complete`, `exitWorks`,
  `sorry`, `admit`, `axiom`, `constant`, `opaque`, or `unsafe` in
  `ConnesWeilRH/**/*.lean`.
- `#print axioms` for the new source-object derivation theorems and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this is an interface-hardening pass. It does not
  prove CCM24, CCM25, or CC20 analytic source theorems, and it does not make RH
  unconditional.

- Threaded CCM25 common finite-prime atoms into the restricted-to-full route
  bridge.
- In `ConnesWeilRH/Route/Bridge.lean`, added common-atom package projections:
  `package_backed_source_global_sum_eq_common_atoms`,
  `package_backed_source_restricted_sum_eq_common_atoms`,
  `package_backed_source_common_restricted_sum_eq_common_global`,
  `package_backed_psi_source_evaluator_common_atoms`,
  `package_backed_qw_source_evaluator_common_atoms`, and
  `package_backed_qw_lambda_source_evaluator_common_atoms`.
- Added `SourceCommonAtomArchimedeanContributionMatchesForRestriction` plus
  `source_common_atom_archimedean_contribution_matches_of_package`, deriving
  the common-atom archimedean contribution equality from the existing
  restricted/global evaluator equality and package common-atom read-offs.
- Added `scalar_equality_from_common_atom_witness_components` and changed
  `RestrictedToFullQWScalarRestrictionData.scalarEquality` to use it. The
  scalar restriction equality is now derived from the common-atom
  `QW_lambda` formula, common-atom archimedean contribution match, and
  common-atom `QW` formula.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new common-atom contribution theorem, common-atom
  scalar equality theorem, old scalar equality theorem, scalar restriction
  projection, and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: the scalar equality now consumes common-atom
  package formulas, but the archimedean contribution match remains an explicit
  source/restriction-form obligation, not an analytic Lean proof.

- Completed the current CCM25 package-level common-atom evaluator pass.
- Added common-atom source evaluator formulas for `Psi`, `QW`, and
  `QW_lambda` in `ConnesWeilRH/Source/CCM25Concrete/Package.lean`:
  `psi_source_evaluator_common_atoms_of_package`,
  `qw_source_evaluator_common_atoms_of_package`, and
  `qw_lambda_formula_source_evaluator_common_atoms_of_package`.
- These theorems make the global `Psi/QW` and restricted `QW_lambda` formulas
  read their finite-prime contribution from the same
  `formula_components h).commonCertificate.atoms` source as the package-level
  finite-prime sums.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new common-atom `Psi/QW/QW_lambda` evaluator
  theorems, the common global/restricted sum read-offs, and
  `ConnesWeilRH.Route.final_connes_weil_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: the package now prevents global/restricted
  finite-prime evaluator drift at the Lean object level, but the analytic
  construction of the evaluator, test function model, and CCM25 explicit
  formula remains a source/package obligation.

- Further tightened the CCM25 arithmetic package around a single common
  finite-prime atom source.
- Added package-level common-atom finite-prime evaluator sums:
  `source_common_global_finite_prime_evaluator_sum` and
  `source_common_restricted_finite_prime_evaluator_sum`.
- Added read-offs proving the existing global and restricted evaluator sums
  use the package's `commonCertificate.atoms`:
  `source_global_sum_eq_common_atoms_of_package` and
  `source_restricted_sum_eq_common_atoms_of_package`.
- Added common-atom versions of the global and restricted finite-prime sum
  formulas:
  `global_finite_prime_sum_common_atoms_of_package`,
  `global_von_mangoldt_pairing_sum_common_atoms_of_package`,
  `restricted_finite_prime_sum_common_atoms_of_package`, and
  `restricted_von_mangoldt_pairing_sum_common_atoms_of_package`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the common-atom evaluator-sum read-offs reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: global and restricted finite-prime sums now visibly
  share the package's common arithmetic atom normalization, but this still
  projects from the package input. It does not construct the analytic CCM25
  operator/evaluator model from first principles.

- Began the CCM25 `QW` / `QW_lambda` / finite-prime normalization pass after
  the RH-definition and CC20-exit milestone commit.
- In `ConnesWeilRH/Source/CCM25Concrete/Package.lean`, added package-level
  pointwise read-offs for both global and restricted finite-prime indices:
  `global_index_weight_read_off_of_package`,
  `global_index_pairing_formula_source_evaluator_of_package`,
  `global_index_finite_prime_term_formula_source_evaluator_of_package`,
  `restricted_index_weight_read_off_of_package`,
  `restricted_index_pairing_formula_source_evaluator_of_package`, and
  `restricted_index_finite_prime_term_formula_source_evaluator_of_package`.
- These expose, at package level, the concrete source objects behind each
  finite-prime term:
  Mathlib von Mangoldt weight, the source evaluator formula for
  `<f|T(n)f>`, and the source finite-prime evaluator atom.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the six new package-level finite-prime read-offs
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this is still an exposure/projection step from the
  arithmetic package. It does not construct analytic test functions,
  operators `T(n)`, or prove CCM25's explicit formula from first principles.

- Split the CC20 finite-set disjointness side condition into pointwise Lean
  projections for the three route points.
- In `ConnesWeilRH/Source/CC20RHExit.lean`, added
  `zero_not_source_nontrivial_zero_of_disjoint`,
  `half_not_source_nontrivial_zero_of_disjoint`, and
  `one_not_source_nontrivial_zero_of_disjoint`, plus corresponding projections
  from `CC20PropositionC1InputData` and
  `SourceFiniteVanishingCriterionPackage`.
- In `ConnesWeilRH/Route/RouteTheorem.lean`, added route-level projections
  `c1_zero_not_source_nontrivial_zero_of_route_backed_cc20_exit_input_data`,
  `c1_half_not_source_nontrivial_zero_of_route_backed_cc20_exit_input_data`,
  and `c1_one_not_source_nontrivial_zero_of_route_backed_cc20_exit_input_data`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CC20RHExit`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the source/package/route pointwise disjointness
  projections and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: the pointwise theorems are projections from the
  package disjointness obligation. They do not analytically prove that
  `0`, `1 / 2`, or `1` are absent from the source nontrivial-zero set.

- Tightened the CC20 finite-vanishing RH exit interface so the C.1 finite-set
  side condition is tied to the active `RHDefinitionBridge`.
- In `ConnesWeilRH/Source/CC20RHExit.lean`, added
  `criticalVanishingPointValue`, mapping route vanishing points to the complex
  source points `0`, `1 / 2`, and `1`.
- Added `SourceFiniteSetDisjointFromNontrivialZeros B F` and
  `SourceFiniteSetAdmissibilityForBridge B F`, making the C.1 finite-set
  admissibility depend on the same source nontrivial-zero predicate that the
  RH definition bridge transports.
- Extended `CC20PropositionC1InputData`, `CC20RHExitObjectPackage`, and
  `SourceFiniteVanishingCriterionPackage` with
  `finiteSetDisjointFromNontrivialZeros` so Proposition C.1 input data now
  carries the source-zero disjointness side condition explicitly.
- Updated `ConnesWeilRH/Source/CC20.lean` and
  `ConnesWeilRH/Route/RouteTheorem.lean` to thread the bridge-indexed C.1
  input data through the CC20 exit and final route theorem.
- Added route projection
  `c1_finite_set_disjoint_row_of_route_backed_cc20_exit_input_data`, so the
  final route exposes the finite-set disjointness row alongside triple
  vanishing and full-positivity rows.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CC20RHExit`,
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new disjointness projections, CC20 finite-vanishing
  exit projections, and `ConnesWeilRH.Route.final_connes_weil_rh` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: the finite-set disjointness row is now an explicit
  package obligation, not proved analytically. The route still depends on the
  CC20 Proposition C.1 source package and the proof that `{0,1/2,1}` is
  disjoint from the source nontrivial-zero set.

- Added RH definition theorem-contract projection names in
  `ConnesWeilRH/Source/RHDefinition.lean`:
  `SourceZetaEqualsMathlibZeta`, `SourceZeroToMathlibZero`,
  `MathlibZeroToSourceZero`, `SourceNontrivialZeroNoNegativeEven`,
  `SourceNontrivialZeroNoPole`,
  `MathlibHypothesesToSourceNontrivialZero`,
  `SourceCriticalLineIffReEqHalf`, `SourceRHImpliesMathlibRH`, and
  `MathlibRHImpliesSourceRH`.
- These are transparent projections from the existing `RHDefinitionBridge`
  data and direct RH transport theorem; they introduce no new source
  assumptions.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.RHDefinition` and
  `lake build ConnesWeilRH`.
- `#print axioms` for all nine contract-name projections reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: the RH definition bridge is now Lean-visible under
  the theorem-contract names, but this still only transports a supplied source
  RH statement to Mathlib RH. It does not prove the supplied CC20 source RH
  statement or the finite-vanishing exit.

- Tightened `ConnesWeilRH/Source/RHDefinition.lean` for the
  RHDefinitionBridge pass.
- Added explicit zero predicates `SourceZetaZero` and `MathlibZetaZero`, plus
  direct transport theorems
  `source_zeta_zero_to_mathlib_zeta_zero`,
  `mathlib_zeta_zero_to_source_zeta_zero`, and
  `source_zeta_zero_iff_mathlib_zeta_zero`.
- Added `source_rh_to_mathlib_rh_direct`, which consumes Mathlib RH
  hypotheses in Mathlib's order:
  `riemannZeta s = 0`, negative-even exclusion, `s != 1`, then constructs the
  source nontrivial-zero witness and returns `s.re = 1 / 2`.
- Added standard-bridge projections for the new zero transport and direct RH
  exit.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.RHDefinition` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new zero-transport and direct RH-exit theorems
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this closes more definition-drift surface in Lean,
  but it does not prove CC20 source RH or RH itself. It proves only that a
  supplied source RH conclusion transports to Mathlib's exact
  `_root_.RiemannHypothesis` through named zeta-zero, exclusion, and
  critical-line bridges.

- Added an explicit archimedean contribution bridge for the restricted-to-full
  scalar equality.
- Introduced `SourceArchimedeanContributionMatchesForRestriction`, expressing
  that the restricted source-evaluator expression
  `archimedeanTerm + polePairing - restrictedSourceSum` matches the global
  source-evaluator expression
  `poleFunctional - archimedeanTerm - globalSourceSum`.
- Threaded this bridge through `SourceQWLambdaRestrictionRows`,
  `RestrictedToFullNoSpectralConvergenceImport`, and
  `RestrictedToFullQWScalarRestrictionWitness`.
- Added projections:
  `archimedean_contribution_matches_of_qw_lambda_restriction`,
  `archimedean_contribution_matches_of_scalar_witness`, and
  `archimedean_contribution_matches_of_scalar_restriction`.
- Added `scalar_equality_from_witness_components`, deriving
  `qwLambda lambda g g = qw g g` from the package-backed restricted formula,
  the archimedean contribution bridge, and the package-backed global `QW`
  source-evaluator formula.
- Updated `RestrictedToFullQWScalarRestrictionData` so its `scalarEquality`
  field is produced by `scalar_equality_from_witness_components` rather than
  copied directly from a bare witness equality.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the archimedean contribution projections,
  `scalar_equality_from_witness_components`, and
  `scalar_equality_of_scalar_restriction` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: full scalar equality is now derived from named
  components, but the archimedean contribution bridge itself remains an
  explicit source/restriction-form obligation. It is not an accepted-source
  theorem or analytic formalization yet.
- Milestone commit plan: commit and push this as a GPG-signed checkpoint, then
  continue with larger Lean milestones before the next push.

- Exposed the finite-prime evaluator equality and pole-normalization legs from
  the restricted-to-full scalar witness.
- Added route projections from `SourceQWLambdaIsRestrictionOfQW`,
  `RestrictedToFullQWScalarRestrictionWitness`, and
  `RestrictedToFullQWScalarRestrictionEquality` for
  `SourceFinitePrimeEvaluatorSumsMatchForRestriction`.
- Added archimedean/pole stability projections:
  `pole_normalization_of_archimedean_pole_stability`,
  `package_read_off_of_archimedean_pole_stability`,
  `pole_pairing_eq_pole_functional_of_archimedean_pole_stability`,
  `archimedean_pole_stability_of_scalar_witness`,
  `pole_pairing_eq_pole_functional_of_scalar_witness`, and
  `pole_pairing_eq_pole_functional_of_scalar_restriction`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new finite-prime and pole-normalization scalar
  witness projections reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Logic boundary preserved: the scalar witness now exposes finite-prime
  evaluator equality and pole normalization as named legs. It still does not
  derive the final scalar equality from formula algebra; the equality remains
  the source restriction-form bridge output.

- Connected the finite-prime evaluator-sum equality into the restricted-to-full
  scalar witness.
- Added `SourceFinitePrimeEvaluatorSumsMatchForRestriction` and made
  `SourceQWLambdaRestrictionRows`,
  `RestrictedToFullNoSpectralConvergenceImport`, and
  `RestrictedToFullQWScalarRestrictionWitness` carry it explicitly.
- Added route projections:
  `finite_prime_evaluator_sums_match_of_qw_lambda_restriction`,
  `finite_prime_evaluator_sums_match_of_scalar_witness`, and
  `finite_prime_evaluator_sums_match_of_scalar_restriction`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new finite-prime evaluator-sum witness projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: the scalar witness now visibly includes the
  finite-prime evaluator equality, but full `QW_lambda(g,g)=QW(g,g)` still
  depends on the separate archimedean/pole stability and source restriction
  legs.

- Promoted finite-prime support equality to source evaluator sum equality.
- Added
  `Package.source_restricted_finite_prime_evaluator_sum_eq_global`, proving the
  restricted source finite-prime evaluator sum equals the global source
  evaluator sum by combining the package common-atoms equality with
  `restrictedPrimeIndexSet lambda = globalPrimeIndexSet`.
- Extended route `PackageFinitePrimeSupportStabilization` with the explicit
  source evaluator equality and added
  `Route.package_backed_source_restricted_sum_eq_global`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`,
  `lake build ConnesWeilRH.Route.Bridge`, and `lake build ConnesWeilRH`.
- `#print axioms` for the package/route evaluator-sum equality and route
  stabilization projection reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Logic boundary preserved: this closes the finite-prime evaluator-sum part of
  the restricted-to-full witness under the concrete package. The full scalar
  equality still separately needs archimedean/pole stability and the
  source restriction-form bridge.

- Promoted fixed-lambda finite-prime support stabilization from coverage-only
  evidence to a Lean-visible restricted/global index-set equality.
- Added
  `FinitePrimeExact.restricted_index_set_eq_global_of_exact_support`, proving
  `W.restrictedPrimeIndexSet lambda = W.globalPrimeIndexSet` from exact
  support plus `visibleAtomsInLambdaCut`.
- Lifted the equality through
  `FinitePrimeCertificate.restricted_index_set_eq_global_of_certificate`,
  `FinitePrimeCertificate.restricted_index_set_eq_global_of_arithmetic_certificate`,
  and `Package.restricted_index_set_eq_global_of_package`.
- Extended route `PackageFinitePrimeSupportStabilization` so it now includes
  the explicit index-set equality, and added
  `Route.package_backed_restricted_index_set_eq_global`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate
  ConnesWeilRH.Source.CCM25Concrete.Package ConnesWeilRH.Route.Bridge`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new source, package, and route index-set equality
  projections reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this proves the fixed-lambda restricted finite-prime
  index set equals the global visible index set under the concrete exact
  support certificate. It still does not by itself prove
  `QW_lambda(g,g)=QW(g,g)` because archimedean and pole stability plus the
  scalar restriction witness remain separate obligations.

- Split the restricted-to-full scalar equality bridge into an explicit witness
  layer instead of a bare equality field.
- Added `RestrictedToFullQWScalarRestrictionWitness`, carrying common-test
  data, source-window control, the CCM25 restriction leg, finite-prime support
  stabilization, exact finite-prime support, archimedean/pole stability, an
  explicit no-spectral-convergence guard, and the final scalar equality.
- Changed `RestrictedToFullQWLargeLambdaThreshold.scalarRestrictionAtLarge`
  so large-lambda data must return this witness, not just
  `qwLambda lambda g g = qw g g`.
- Added witness projections:
  `scalar_equality_of_scalar_witness`,
  `no_spectral_convergence_import_of_scalar_witness`,
  `scalar_witness_of_scalar_restriction`, and
  `no_spectral_convergence_import_of_scalar_restriction`.
- Updated the restricted-to-full bridge data and lower-bound transfer helper to
  consume the scalar witness path.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new scalar-witness projections and the route bridge
  projection reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved and made sharper: Lean now exposes the intended
  route-evidence composition for `QW_lambda(g,g)=QW(g,g)`, but the equality is
  still a bridge obligation supplied by the threshold witness, not a theorem
  derived from accepted CCM25 source imports or full analytic formalization.

- Tightened the restricted-to-full Lean bridge contract so finite-prime support
  stabilization can no longer masquerade as scalar equality.
- Added `scalarRestrictionAtLarge` to `RestrictedToFullQWLargeLambdaThreshold`.
  Any construction of the threshold must now explicitly provide the fixed-test
  equality
  `qwLambda lambda g.weilTest g.weilTest = qw g.weilTest g.weilTest`.
- Added `scalarEquality` to `RestrictedToFullQWScalarRestrictionData` and the
  projection `scalar_equality_of_scalar_restriction`.
- Updated `restricted_to_full_scalar_restriction_of_common_tuple`,
  `restricted_to_full_lower_bound_transfer_of_common_tuple`, and
  `restricted_to_full_bridge_data_of_common_tuple` so the scalar equality is
  passed from the threshold contract rather than inferred from finite-prime
  support rows.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new scalar-equality projection and restricted-to-full
  bridge projections reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Logic boundary preserved and clarified: exact finite-prime support aligns
  support/sum rows, but it does not by itself prove the full
  `QW_lambda(g,g)=QW(g,g)` scalar bridge because the source formulas also
  involve archimedean, pole, and sign-normalization terms. That equality is now
  an explicit bridge obligation.

- Extended the route bridge's package-backed CCM25 read-off contract to carry
  the source-evaluator formulas for `Psi`, global `QW`, and restricted
  `QW_lambda`, in addition to the global and restricted finite-prime sums.
- Added named route projections:
  `package_backed_global_finite_prime_sum`,
  `package_backed_restricted_finite_prime_sum`,
  `package_backed_psi_source_evaluator`,
  `package_backed_qw_source_evaluator`, and
  `package_backed_qw_lambda_source_evaluator`.
- Refactored `source_finite_prime_sign_owned_by_common_test` to consume the
  named finite-prime-sum projections instead of indexing directly into the
  nested conjunction. This avoids another fragile proof path after the
  package-backed read-off contract is extended.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- Logic boundary preserved: this does not prove the CCM25 analytic source
  formulas, restricted-to-full equality, final sign equality, or RH. It makes
  the route bridge carry the concrete package source-evaluator formulas as
  Lean-visible data before downstream sign/read-off steps consume the package.

- Connected the CCM25 common-certificate package hardening to the route bridge.
- Changed `Route.package_exact_finite_prime_support_at_lambda` so the exact
  support witness is constructed from
  `(Package.formula_components pkg).commonCertificate`, not from the restricted
  component certificate projection.
- Added route-level checks:
  `package_exact_support_uses_common_certificate` and
  `package_exact_support_source_test_eq_package_source_test`, showing the
  route exact-support witness uses the common certificate and its source
  visibility agrees with `Package.source_test_of_package`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the exact-support common-certificate route projection,
  exact-support source-test projection, package support stabilization, and
  visibility-at-lambda projection reported only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Logic boundary preserved: this does not prove restricted-to-full equality,
  source analytic CCM25 rows, or RH. It closes a route-level drift channel by
  making the exact-support witness consumed by restricted-to-full originate
  from the same common fixed-lambda arithmetic certificate and source test as
  the package formula components.

- Continued CCM25 package support hardening on top of the common-certificate
  source-test anchor.
- Added package-level support projections whose evidence path goes through
  `(formula_components h).commonCertificate`:
  `common_certificate_global_index_source_data_of_package`,
  `common_certificate_global_index_prime_power_of_package`,
  `common_certificate_global_index_visible_of_package`,
  `common_certificate_restricted_index_source_data_of_package`,
  `common_certificate_restricted_index_prime_power_of_package`,
  `common_certificate_restricted_index_visible_of_package`, and
  `common_certificate_restricted_index_lambda_cut_of_package`.
- Refactored the public package index projections
  `global_index_prime_power_of_package`, `global_index_visible_of_package`,
  `global_index_one_lt_of_package`, `restricted_index_prime_power_of_package`,
  `restricted_index_visible_of_package`,
  `restricted_index_lambda_cut_of_package`,
  `restricted_index_one_lt_of_package`, and
  `restricted_index_le_lambda_sq_of_package` so they now consume the
  common-certificate projections instead of bypassing the formula package
  through `Interface.*`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the common-certificate support projections and the
  refactored public package index projections reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove restricted-to-full equality,
  exact analytic CCM25 rows, or RH. It makes the global/restricted support
  facts used by the package visibly originate from the same fixed-lambda
  arithmetic certificate, source test, and atom normalization data.

- Extended the CCM25 common-certificate hardening to the source-test anchor.
- Strengthened `ConcreteCCM25FormulaComponents` so it now stores a
  `sourceTest` and a proof that `commonCertificate.support.sourceTest =
  sourceTest`.
- Added package-level projections tying the formula component source test back
  to `Package.source_test_of_package`:
  `Package.formula_components_source_test_eq_package_source_test`,
  `Package.common_certificate_source_test_of_package`,
  `Package.global_certificate_source_test_of_package`, and
  `Package.restricted_certificate_source_test_of_package`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FormulaComponents`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the source-test projections reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove global/restricted numerical
  equality, restricted-to-full equality, analytic CCM25 rows, or RH. It fixes
  the common source-test anchor for the shared fixed-lambda arithmetic
  certificate used by the global and restricted formula components.

- Continued CCM25 formula-component hardening after commit `d888e54`.
- Found and fixed a real certificate-drift issue: although
  `formula_components_of_arithmetic_rows` constructs the global and restricted
  components from the same fixed-lambda arithmetic certificate, an arbitrary
  `ConcreteCCM25FormulaComponents` value could previously carry unrelated
  global and restricted certificates. Therefore equality could not be proved
  by `rfl`.
- Strengthened `ConcreteCCM25FormulaComponents` with a
  `commonCertificate` field plus explicit
  `globalCertificate_eq_common` and `restrictedCertificate_eq_common` fields.
- Added Lean-visible projections:
  `FormulaComponents.global_restricted_certificate_eq_of_formula_components`,
  `FormulaComponents.global_restricted_atoms_eq_of_formula_components`,
  `FormulaComponents.global_certificate_eq_common_of_formula_components`,
  `FormulaComponents.restricted_certificate_eq_common_of_formula_components`,
  `Package.global_restricted_certificate_eq_of_package`,
  `Package.global_restricted_atoms_eq_of_package`,
  `Package.source_global_sum_uses_restricted_atoms_of_package`, and
  `Package.source_restricted_sum_uses_global_atoms_of_package`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FormulaComponents`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the common-certificate and common-atoms projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove global-to-restricted equality,
  restricted-to-full equality, analytic CCM25 rows, or RH. It proves only that
  the fixed-test global and restricted formula components in this concrete
  package use the same arithmetic certificate and atom normalization data.

- Completed the next CCM25 concrete source-sum milestone.
- Added global `Psi` and `QW` source-evaluator read-off theorems so the global
  formula path now reaches
  `poleFunctional - archimedeanTerm - SourceGlobalFinitePrimeEvaluatorSum`
  directly from the same arithmetic certificate used by the finite-prime
  normalization rows.
- New Lean bridges include
  `GlobalComponent.psi_source_evaluator_of_component`,
  `GlobalComponent.qw_source_evaluator_of_component`,
  `FormulaComponents.psi_source_evaluator_of_formula_components`,
  `FormulaComponents.qw_source_evaluator_of_formula_components`,
  `FormulaComponents.global_von_mangoldt_pairing_sum_of_formula_components`,
  `Package.psi_source_evaluator_of_package_components`,
  `Package.qw_source_evaluator_of_package_components`, and
  `Package.global_von_mangoldt_pairing_sum_of_package_components`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.GlobalComponent`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FormulaComponents`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new global source-evaluator bridges reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove CCM25 analytic formula rows,
  the final CCM25-to-CC20 sign bridge, restricted-to-full equality, or RH. It
  makes the global finite-prime sum used by `Psi/QW` Lean-visible as the
  concrete source evaluator sum from the same arithmetic certificate.

- Continued CCM25 `QW_lambda` finite-prime hardening.
- Added direct product-sum read-offs from
  `sum n in indexSet, W.vonMangoldtWeight n * W.primePowerPairing n f g`
  to `PrimePowerArithmetic.SourceFinitePrimeEvaluatorSum`, rather than relying
  only on the adjacent `W.finitePrimeTerm` sum.
- New Lean bridges include
  `PrimePowerArithmetic.source_von_mangoldt_pairing_product_formula_source_evaluator`,
  `FinitePrimeCertificate.arithmetic_von_mangoldt_pairing_sum_formula_of_certificate`,
  `FinitePrimeCertificate.arithmetic_restricted_von_mangoldt_pairing_sum_formula_of_certificate`,
  `Interface.arithmetic_restricted_von_mangoldt_pairing_sum_formula_of_arithmetic_rows`,
  `RestrictedComponent.restricted_von_mangoldt_pairing_sum_of_component`,
  `RestrictedComponent.qw_lambda_formula_source_evaluator_of_component`,
  `FormulaComponents.qw_lambda_formula_source_evaluator_of_formula_components`,
  and `Package.qw_lambda_formula_source_evaluator_of_package_components`.
- WSL ext4 verification ran through the CCM25 concrete chain and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new product-sum and `QW_lambda` source-evaluator
  bridges reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove restricted-to-full equality,
  the analytic CCM25 formula rows, or RH. It makes the restricted finite-prime
  product sum inside the `QW_lambda` formula Lean-equal to the concrete source
  evaluator sum supplied by the arithmetic certificate.

- Continued CCM25 finite-prime concrete hardening after commit `e539151`.
- Added source-test visibility projections across the arithmetic atom,
  atom-term, fixed-lambda certificate, common-source-test certificate, and
  concrete arithmetic rows layers.
- New Lean projections include:
  `PrimePowerArithmetic.source_atom_visible_in_source_test`,
  `PrimePowerArithmetic.source_atom_visible_in_pairing_source_test`,
  `PrimePowerArithmetic.source_atom_visible_uses_normalization_source_test`,
  `PrimePowerTerm.source_atom_visible_in_pairing_source_test`,
  `FinitePrimeCertificate.arithmetic_atom_visible_in_support_source_test_of_certificate`,
  `FinitePrimeInterface.certificate_atom_visible_in_source_test_of_source_test_certificates`,
  and `Interface.arithmetic_atom_visible_in_source_test_of_arithmetic_rows`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new source-test visibility projections and
  `Interface.finite_prime_normalization_of_arithmetic_rows` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove CCM25 analytic rows or
  restricted-to-full equality. It prevents arithmetic finite-prime atoms,
  pairing evaluations, support certificates, and concrete rows from using
  different source visibility predicates without a visible Lean projection.

- Began CCM25 finite-prime concrete object hardening after commit `64f4eae`.
- Tightened `ConnesWeilRH/Source/CCM25Concrete/PrimePowerTerm.lean` so
  `SourceFinitePrimeAtomData.sourcePrimePowerIndex` and
  `SourcePrimePowerTermAtIndex.sourcePrimePowerIndex` now carry the concrete
  `PrimePowerArithmetic.SourcePrimePowerIndex n` proof rather than a bare
  `Prop`.
- Updated `source_atom_data_of_arithmetic_data` so atom data preserves the
  source prime-power proof from
  `PrimePowerArithmetic.SourceFinitePrimeArithmeticData`.
- Added projections:
  `source_prime_power_index_of_atom_data`,
  `source_prime_power_index_one_lt_of_atom_data`,
  `source_prime_power_index_of_term_at_index`, and
  `source_prime_power_index_one_lt_of_term_at_index`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the updated atom/term constructors, prime-power
  projections, finite-prime atom normalization, and finite-prime certificate
  normalization reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove CCM25 arithmetic
  analytically. It prevents atom-level finite-prime normalization from losing
  the Mathlib-backed prime-power index proof.

- Continued CC20FiniteVanishingRhExit hardening after commit `dee6acb`.
- Added `RouteBackedCC20ExitInputData` in
  `ConnesWeilRH/Route/RouteTheorem.lean`, packaging the final route-side data
  used immediately before the CC20 finite-vanishing exit.
- The new route-side exit package records:
  `input`, `inputIsRouteInput`, `sourceBackedFullPositivity`,
  `finalSignBridge`, `finalSignNonpositive`, `tripleVanishing`,
  `fullWeilPositivity`, and the source-layer
  `CC20PropositionC1InputData`.
- Added `route_backed_cc20_exit_input_data_of_route_bridge_certificate`,
  deriving the exit package from `RouteBridgeCertificate`.
- Refactored `cc20_source_rh_of_route_certificate` to consume the named
  `RouteBackedCC20ExitInputData` instead of locally passing the
  triple-vanishing proof and full-positivity proof directly into the CC20
  source criterion.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.RouteTheorem` and
  `lake build ConnesWeilRH`.
- `#print axioms` for
  `route_backed_cc20_exit_input_data_of_route_bridge_certificate`,
  `cc20_source_rh_of_route_certificate`, and `final_connes_weil_rh` reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this still does not prove the sign bridge or
  Proposition C.1. It prevents the final route theorem from feeding CC20
  through ad hoc loose proofs; final sign evidence and route-backed full
  positivity are now visible in one exit package.

- Continued route-side CC20 exit hardening.
- Added `RouteBackedCC20NonpositivityInputData` in
  `ConnesWeilRH/Route/RouteTheorem.lean`, pairing the route input,
  `SourceBackedFullPositivity`, `FinalSignBridgeContract`,
  `SourceQWNonnegativeToCC20Nonpositive`, and the C.1 positivity row
  `input.fullWeilPositivity`.
- Updated `RouteBackedCC20ExitInputData` to carry this nonpositivity input
  package and derive its `fullWeilPositivity` field from
  `nonpositivityInput.fullPositivityMatchesNonpositivity`.
- Added `route_backed_cc20_nonpositivity_input_data_of_route_bridge_certificate`
  and projections:
  `nonpositivity_input_of_route_backed_cc20_exit_input_data`,
  `final_sign_nonpositive_of_route_backed_cc20_exit_input_data`,
  `c1_full_positivity_row_of_route_backed_cc20_exit_input_data`, and
  `c1_full_positivity_row_uses_route_nonpositivity_input`.
- The last projection is `rfl`, making the C.1 positivity row definitionally
  the route-backed nonpositivity package row.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.RouteTheorem` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new nonpositivity package constructor/projections,
  `cc20_source_rh_of_route_certificate`, and `final_connes_weil_rh` reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this still does not prove the analytic sign
  equality or CC20 Proposition C.1. It makes the final sign/nonpositive
  evidence part of the route-backed C.1 positivity input instead of merely
  adjacent data.

- Continued route-side CC20 exit hardening by source-backing the C.1 triple
  vanishing input row.
- Added `RouteBackedCC20TripleVanishingInputData` in
  `ConnesWeilRH/Route/RouteTheorem.lean`, carrying the route input,
  `TripleVanishingSymbols`, the source-backed triple-vanishing statement,
  the route bridge into `g.test.tripleVanishing`, and the C.1 row
  `input.tripleVanishing`.
- Updated `RouteBackedCC20ExitInputData` to carry both
  `tripleVanishingInput` and `nonpositivityInput`.
- Updated `route_backed_cc20_exit_input_data_of_route_bridge_certificate` so
  `propositionC1InputData` is built from
  `tripleVanishingInput.tripleVanishingMatchesMellin` and
  `nonpositivityInput.fullPositivityMatchesNonpositivity`.
- Added projections:
  `route_triple_vanishing_of_route_backed_cc20_exit_input_data`,
  `c1_triple_vanishing_row_of_route_backed_cc20_exit_input_data`, and
  `c1_triple_vanishing_row_uses_route_triple_input`.
- The C.1 triple row and C.1 positivity row both now have `rfl` links to their
  route-backed input packages.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.RouteTheorem` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the triple/nonpositive route-backed input packages,
  C.1 row projections, `cc20_source_rh_of_route_certificate`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Logic boundary preserved: this still does not prove Proposition C.1, the
  analytic sign equality, or unconditional RH. It removes another route theorem
  drift channel by making both C.1 input rows come from named source-backed
  route data.

- Continued CC20 finite-vanishing exit interface hardening after commit
  `d88e89b`.
- Changed `SourceFiniteVanishingCriterionPackage` in
  `ConnesWeilRH/Source/CC20RHExit.lean` so its core source criterion is now
  `sourceCriterionData`, consuming
  `CC20PropositionC1InputData finiteVanishingSet input` directly.
- Kept compatibility wrapper `sourceCriterion`, which constructs
  `CC20PropositionC1InputData` from the package's
  `finiteSetAdmissibleData`, `input.tripleVanishing`, and
  `input.fullWeilPositivity`.
- Added source-level C.1-data entry theorems:
  `source_criterion_data_output`,
  `source_criterion_uses_c1_input_data`,
  `criterion_source_output_of_c1_input_data`, and
  `criterion_source_output_uses_c1_input_data`.
- Added `CC20Interface.finite_vanishing_source_rh_of_c1_input_data` in
  `ConnesWeilRH/Source/CC20.lean`.
- Updated `cc20_source_rh_of_route_certificate` in
  `ConnesWeilRH/Route/RouteTheorem.lean` to call the C.1-data entry theorem
  directly with `exitInput.propositionC1InputData`, instead of passing the
  two loose input-row proofs.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CC20RHExit`,
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new source criterion data path, the CC20 interface
  C.1-data entry theorem, `cc20_source_rh_of_route_certificate`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Logic boundary preserved: this still does not prove CC20 Proposition C.1.
  It changes the formal API so the source finite-vanishing criterion's core
  input is the named C.1 data package rather than two loose proofs.

- Continued CC20 finite-vanishing exit API hardening.
- Added finite-set projections on `SourceFiniteVanishingCriterionPackage` in
  `ConnesWeilRH/Source/CC20RHExit.lean`:
  `finite_set_admissible_of_source_package`,
  `zero_mem_of_source_package_finite_set`,
  `half_mem_of_source_package_finite_set`,
  `one_mem_of_source_package_finite_set`, and
  `finite_set_is_triple_of_source_package`.
- Updated `toFiniteVanishingCriterionPackage` so the legacy
  `finiteSetAdmissible` output is derived from
  `SourceFiniteSetAdmissibility h.finiteVanishingSet`, backed by
  `finiteSetAdmissibleData`, rather than treated as the source of truth.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CC20RHExit`,
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the finite-set projections, C.1-data criterion path,
  `CC20Interface.finite_vanishing_source_rh_of_c1_input_data`,
  `cc20_source_rh_of_route_certificate`, and `final_connes_weil_rh` reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this still does not prove CC20 Proposition C.1.
  It reduces another drift channel by making the package finite set and its
  `{0,1/2,1}` admissibility rows projectable from data.

- Continued CC20 finite-vanishing exit API hardening after commit `bf180f7`.
- Added C.1-data RH exit theorems in
  `ConnesWeilRH/Source/CC20RHExit.lean`:
  `criterion_mathlib_rh_point_of_c1_input_data`,
  `criterion_mathlib_rh_statement_of_c1_input_data`, and
  `criterion_to_mathlib_rh_of_c1_input_data`.
- Refactored the older loose-proof theorem path
  `criterion_mathlib_rh_point`, `criterion_mathlib_rh_statement`, and
  `criterion_to_mathlib_rh` so each now constructs
  `CC20PropositionC1InputData` and delegates to the C.1-data theorem.
- Added CC20 interface C.1-data exits in `ConnesWeilRH/Source/CC20.lean`:
  `finite_vanishing_mathlib_rh_point_of_c1_input_data`,
  `finite_vanishing_mathlib_rh_statement_of_c1_input_data`, and
  `finite_vanishing_mathlib_rh_of_c1_input_data`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new C.1-data RH exits, legacy wrapper exits,
  `CC20Interface.finite_vanishing_mathlib_rh`, and `final_connes_weil_rh`
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this still does not prove C.1. It makes the
  preferred public path from C.1 input data to source RH, Mathlib RH statement,
  and Mathlib RH explicit, while the legacy loose-proof path is now a wrapper.

- Continued RHDefinitionBridge hardening after commit `becfccc`.
- Added `MathlibRHStatement` in `ConnesWeilRH/Source/RHDefinition.lean` as the
  named pointwise Mathlib RH specification:
  `forall s, MathlibNontrivialZero s -> MathlibCriticalLine s`.
- Added `mathlib_rh_statement_iff_mathlib`, proving the named statement is
  equivalent to Mathlib's canonical `_root_.RiemannHypothesis`.
- Added `source_rh_point_iff_mathlib_rh_point`, the pointwise bridge:
  `(B.sourceNontrivialZero s -> B.sourceCriticalLine s)` iff
  `(MathlibNontrivialZero s -> MathlibCriticalLine s)`.
- Added source/Mathlib statement bridge theorems:
  `source_rh_to_mathlib_rh_statement`,
  `mathlib_rh_statement_to_source_rh`, and
  `source_rh_iff_mathlib_rh_statement`.
- Refactored `source_rh_to_mathlib_rh` and `mathlib_rh_to_source_rh` to pass
  through the named pointwise statement, making the zero predicate and critical
  line transport visible before the final Mathlib theorem.
- Added `rfl`-level standard bridge facts:
  `standard_source_rh_eq_mathlib_rh_statement`,
  `standard_source_zeta_eq_mathlib`,
  `standard_source_nontrivial_zero_eq_mathlib`, and
  `standard_source_critical_line_eq_mathlib`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.RHDefinition` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new RHDefinitionBridge pointwise/statement/standard
  bridge theorems reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Source/RHDefinition.lean`.
- Logic boundary preserved: this proves no new analytic RH content. It only
  locks the definition bridge so source RH must pass through the exact Mathlib
  zero predicate, negative-even exclusion, pole exclusion, and critical-line
  conclusion.

- Began CC20FiniteVanishingRhExit hardening on top of the RHDefinitionBridge
  pointwise statement.
- Added `SourceFiniteVanishingCriterionPackage.criterion_mathlib_rh_statement`
  in `ConnesWeilRH/Source/CC20RHExit.lean`, so the finite-vanishing criterion
  now exposes `RHDefinitionBridge.MathlibRHStatement` before converting to
  `_root_.RiemannHypothesis`.
- Added `standard_criterion_mathlib_rh_statement` for the standard bridge.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CC20RHExit`,
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new CC20 exit statement theorem, the standard
  statement theorem, `criterion_to_mathlib_rh`,
  `CC20Interface.finite_vanishing_mathlib_rh`, and `final_connes_weil_rh`
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove CC20 Proposition C.1. It makes
  the final exit pass through the named pointwise Mathlib RH statement before
  concluding Mathlib's canonical RH theorem.

- Continued CC20FiniteVanishingRhExit hardening.
- Added `CC20PropositionC1InputData` in
  `ConnesWeilRH/Source/CC20RHExit.lean`, packaging the three Proposition C.1
  entry conditions as named fields:
  `finiteSetIsTriple`, `tripleVanishingMatchesMellin`, and
  `fullPositivityMatchesNonpositivity`.
- Refactored `CC20PropositionC1SourceCriterion` to consume
  `CC20PropositionC1InputData F input` rather than three loose implication
  arguments.
- Added constructor/projections:
  `cc20_proposition_c1_input_data`,
  `triple_vanishing_of_c1_input_data`,
  `full_positivity_of_c1_input_data`, and
  `finite_set_is_triple_of_c1_input_data`.
- Updated `SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage`
  so object-package criterion use now passes through the named Proposition C.1
  input data.
- Added `CC20Interface.finite_vanishing_mathlib_rh_statement` in
  `ConnesWeilRH/Source/CC20.lean`.
- Refactored `SourceFiniteVanishingCriterionPackage.criterion_to_mathlib_rh`
  so it concludes Mathlib RH through
  `RHDefinitionBridge.mathlib_rh_statement_iff_mathlib` and
  `criterion_mathlib_rh_statement`, not by manually re-expanding the pointwise
  theorem at the final step.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CC20RHExit`,
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new C.1 input-data constructor/projections, the
  refactored criterion path, `CC20Interface.finite_vanishing_mathlib_rh_statement`,
  `CC20Interface.finite_vanishing_mathlib_rh`, and `final_connes_weil_rh`
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this still does not prove Proposition C.1 or the
  final sign/nonpositivity bridge. It makes the C.1 call site auditable by
  named input rows before source RH and Mathlib RH are concluded.

- Continued restricted-to-full threshold hardening after commit `578ed4a`.
- Added `RestrictedToFullCurrentThresholdData` in
  `ConnesWeilRH/Route/Bridge.lean`, making the current-lambda threshold
  package explicit: large-lambda threshold, proof that the current lambda is
  above it, common tuple, fixed-test support, prime-power atom stabilization,
  and finite-prime stabilization.
- Added constructor/projections:
  `current_threshold_data_of_large_lambda_threshold`,
  `fixed_test_support_of_current_threshold_data`,
  `prime_power_atom_stabilization_of_current_threshold_data`, and
  `finite_prime_stabilization_of_current_threshold_data`.
- Extended `RestrictedToFullQWBridgeData` with `currentThresholdData` and
  updated downstream projections to consume the named current-threshold data
  instead of reconstructing support/stabilization proof terms at each use.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new current-threshold constructor/projections and
  affected restricted-to-full bridge projections reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Route/Bridge.lean`.
- Logic boundary preserved: this does not prove restricted-to-full equality.
  It only makes the current large-lambda threshold evidence Lean-visible and
  reusable by named projections.

- Continued restricted-to-full scalar restriction hardening after commit
  `483daee`.
- Replaced the old conjunction definition of
  `RestrictedToFullQWScalarRestrictionEquality` in
  `ConnesWeilRH/Route/Bridge.lean` with a structured
  `RestrictedToFullQWScalarRestrictionData` package.
- The scalar restriction data now has named fields:
  `commonTuple`, `restrictionRows`, and `exactFinitePrimeSupport`.
- Added constructors/projections:
  `restricted_to_full_scalar_restriction_data_of_common_tuple`,
  `restriction_rows_of_scalar_restriction`,
  `common_tuple_of_scalar_restriction`, and
  `exact_finite_prime_support_of_scalar_restriction`.
- Updated `restricted_to_full_bridge_data_of_common_tuple` and
  `prime_power_atom_stabilization_of_large_lambda_threshold` to consume these
  named projections instead of relying on `.1/.2` from a bare conjunction.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new scalar restriction data constructor/projections,
  `restricted_to_full_bridge_data_of_common_tuple`,
  `prime_power_atom_stabilization_of_large_lambda_threshold`, and
  `exact_finite_prime_support_of_restricted_to_full_contract` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove restricted-to-full equality.
  It makes the scalar restriction certificate auditable by named fields:
  common test tuple, QW-lambda restriction rows, and exact finite-prime
  support.

2026-06-28

- Continued restricted-to-full bridge hardening after commit `636e566`.
- Added direct `exactFinitePrimeSupport :
  PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg` to
  `RestrictedToFullQWBridgeData` in `ConnesWeilRH/Route/Bridge.lean`.
- Updated `restricted_to_full_bridge_data_of_common_tuple` so the bridge data
  now stores exact finite-prime support directly, not only inside the nested
  scalar-restriction equality proof.
- Added `exact_finite_prime_support_of_restricted_to_full_contract`, making
  exact support directly projectable from a
  `RestrictedToFullQWBridgeContract`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for
  `restricted_to_full_bridge_data_of_common_tuple`,
  `restricted_to_full_bridge_contract_of_common_tuple`,
  `exact_finite_prime_support_of_restricted_to_full_contract`,
  `exact_finite_prime_support_of_qw_lambda_restriction`,
  `visibility_at_lambda_of_package_exact_support`, and
  `scalar_restriction_equality_of_restricted_to_full_contract` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove restricted-to-full scalar
  equality. It removes another audit indirection by making exact support a
  direct field of the restricted-to-full bridge data.

2026-06-28

- Completed the next restricted-to-full exact-support hardening slice.
- Extended `SourceQWLambdaRestrictionRows` in
  `ConnesWeilRH/Route/Bridge.lean` with
  `exactFinitePrimeSupport :
  PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg`.
- Updated `source_qw_lambda_restriction_rows_of_common_tuple` so the row
  package now carries the exact finite-prime support object in addition to
  restricted/full QW read-offs, finite-prime stabilization, and
  archimedean/pole stability.
- Added `exact_finite_prime_support_of_qw_lambda_restriction`, making exact
  support projectable from `SourceQWLambdaIsRestrictionOfQW`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for
  `source_qw_lambda_restriction_rows_of_common_tuple`,
  `source_qw_lambda_is_restriction_of_common_tuple`,
  `exact_finite_prime_support_of_qw_lambda_restriction`,
  `visibility_at_lambda_of_package_exact_support`,
  `restricted_to_full_scalar_restriction_of_common_tuple`,
  `restricted_to_full_bridge_data_of_common_tuple`, and
  `restricted_to_full_bridge_contract_of_common_tuple` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove the scalar restricted-to-full
  equality analytically. It makes exact support visible in the restriction-row
  certificate so the next restricted-to-full audit does not have to infer it
  indirectly from coverage/stabilization.

2026-06-28

- Continued restricted-to-full CCM25 finite-prime bridge hardening after commit
  `5731d53`.
- Added `PackageExactFinitePrimeSupportAtLambda` in
  `ConnesWeilRH/Route/Bridge.lean`, exposing a route-facing
  `Nonempty ExactSupportAtLambda` object for a concrete CCM25 arithmetic
  package at the current lambda.
- Added `package_exact_finite_prime_support_at_lambda`,
  `package_exact_finite_prime_support_at_lambda_holds`,
  `exact_support_of_package_exact_support`, and
  `visibility_at_lambda_of_package_exact_support`.
- Refactored `package_finite_prime_support_stabilization` so its
  visible-atoms-in-lambda-cut leg is sourced through the exact-support object
  rather than directly through the local certificate internals.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new exact-support wrappers,
  `package_finite_prime_support_stabilization`,
  `finite_prime_stabilization_of_large_lambda_threshold`, and
  `scalar_restriction_equality_of_restricted_to_full_contract` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove restricted-to-full equality.
  It makes the exact-support certificate visible at the route bridge boundary
  so later restricted-to-full work does not rely only on coverage statements.

2026-06-28

- Continued CCM25 finite-prime arithmetic hardening.
- Added `sourcePrimePowerIndex : SourcePrimePowerIndex n` to
  `PrimePowerArithmetic.SourceFinitePrimeArithmeticData` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean`.
- Updated `source_arithmetic_data_of_pairing_data` so constructing arithmetic
  atom data now requires the source prime-power index proof for that `n`.
- Added projections
  `source_prime_power_index_of_arithmetic_data` and
  `source_prime_power_index_one_lt_of_arithmetic_data`, making the Mathlib
  prime-power condition and the derived `1 < n` fact available from every
  finite-prime arithmetic atom.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new prime-power index projections,
  `source_arithmetic_data_of_pairing_data`,
  `PrimePowerTerm.source_atom_data_of_arithmetic_data`,
  `FinitePrimeCertificate.arithmetic_global_index_prime_power_of_certificate`,
  `FinitePrimeInterface.finite_prime_visibility_of_common_source_test_certificates`,
  and `Package.finite_prime_normalization_of_package` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove CCM25 source arithmetic. It
  prevents an atom-level normalization package from carrying a finite-prime
  term without an explicit source prime-power proof for its index.

2026-06-28

- Continued CCM25 finite-prime normalization hardening after commit `866cb1b`.
- Added `finite_prime_visibility_of_common_source_test_certificates` and
  `finite_prime_normalization_of_common_source_test_certificates` in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeInterface.lean`.
- These derive the broad finite-prime visibility/normalization statement from
  one `FixedLambdaArithmeticSourceTestCertificatesForTest` family, keeping the
  common `sourceTest` visible while taking the base global/term rows and each
  restricted lambda row from that same family.
- Updated `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` so
  `finite_prime_visibility_of_arithmetic_rows` now uses
  `finite_prime_visibility_of_common_source_test_certificates` instead of the
  older wrapper path.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new common-source-test finite-prime theorems,
  `Interface.finite_prime_visibility_of_arithmetic_rows`,
  `Interface.finite_prime_normalization_of_arithmetic_rows`,
  `Package.finite_prime_normalization_of_package`, and
  `finite_prime_normalization_of_sign_owned_package` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Source/CCM25Concrete/FinitePrimeInterface.lean ConnesWeilRH/Source/CCM25Concrete/Interface.lean`.
- Logic boundary preserved: this does not prove CCM25 arithmetic analytically
  or remove the broad `forall lambda` interface. It narrows a drift channel by
  making the package-facing finite-prime route consume one common source-test
  certificate family.

2026-06-28

- Hardened the CC20 finite-vanishing RH exit interface.
- Added `DecidableEq` for `CriticalVanishingPoint` in `ConnesWeilRH/Basic.lean`
  so the final finite-vanishing set can be represented as a concrete `Finset`.
- Added source-layer CC20 RH-exit objects in
  `ConnesWeilRH/Source/CC20RHExit.lean`:
  `cc20TripleFiniteVanishingSet`,
  `RouteFiniteVanishingSetIsCC20Triple`,
  `SourceFiniteSetAdmissibility`,
  `RouteTripleVanishingMatchesCC20Mellin`,
  `RouteFullPositivityMatchesCC20Nonpositivity`,
  `CC20PropositionC1SourceCriterion`, and
  `CC20RHExitObjectPackage`.
- Added projections for finite-set admissibility:
  `zero_mem_of_source_finite_set_admissibility`,
  `half_mem_of_source_finite_set_admissibility`,
  `one_mem_of_source_finite_set_admissibility`, and
  `finite_set_is_triple_of_source_finite_set_admissibility`.
- Added `cc20_triple_finite_set_is_triple` and
  `cc20_triple_finite_set_admissibility`, proving the Lean-level finite set is
  exactly `{zero, half, one}` and contains all three named points.
- Added
  `SourceFiniteVanishingCriterionPackage.ofCC20RHExitObjectPackage`, deriving
  the older criterion package from the visible object package.
- Upgraded `ConnesWeilRH/Source/CC20.lean` so `CC20Interface` now stores
  `cc20RHExitObjectPackage : CC20RHExitObjectPackage rhDefinitionBridge`
  instead of directly storing a bare
  `SourceFiniteVanishingCriterionPackage rhDefinitionBridge`. The old
  `sourceFiniteVanishingRhExit` is now a derived function.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CC20RHExit`,
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new CC20 exit object constructors/projections,
  `CC20Interface.sourceFiniteVanishingRhExit`,
  `CC20Interface.finiteVanishingRhExit`,
  `CC20Interface.finite_vanishing_source_rh`,
  `finite_vanishing_rh_exit_holds`,
  `cc20_source_rh_of_route_certificate`, and `final_connes_weil_rh` reported
  only `propext`, `Classical.choice`, and `Quot.sound` or smaller subsets.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Basic.lean ConnesWeilRH/Source/CC20RHExit.lean ConnesWeilRH/Source/CC20.lean ConnesWeilRH/Route/Bridge.lean ConnesWeilRH/Route/RouteTheorem.lean`.
- Logic boundary preserved: this still does not prove CC20 Proposition C.1,
  the final sign inequality, or unconditional RH. It makes the final exit
  consume a visible finite-set/sign/vanishing/source-RH object package instead
  of a hidden direct `tripleVanishing -> fullWeilPositivity -> RH` criterion.

2026-06-28

- Continued RHDefinitionBridge / CC20 finite-vanishing exit hardening in the
  final route theorem.
- Added `cc20_source_rh_of_route_certificate` in
  `ConnesWeilRH/Route/RouteTheorem.lean`, making the final route first produce
  `inputs.cc20.rhDefinitionBridge.SourceRH` through
  `Source.CC20Interface.finite_vanishing_source_rh`.
- Refactored `final_connes_weil_rh` so the final Mathlib conclusion is now
  explicitly obtained through
  `Source.RHDefinitionBridge.source_rh_to_mathlib_rh
  inputs.cc20.rhDefinitionBridge`, rather than directly calling the combined
  `finite_vanishing_mathlib_rh` wrapper.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.RouteTheorem` and
  `lake build ConnesWeilRH`.
- `#print axioms` for `route_certificate_of_sign_defect_classification`,
  `cc20_source_rh_of_route_certificate`, `final_connes_weil_rh`,
  `RHDefinitionBridge.source_rh_to_mathlib_rh`, and
  `CC20Interface.finite_vanishing_source_rh` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this exposes the source-RH-to-Mathlib-RH
  definition bridge at the last theorem boundary. It does not discharge the
  analytic CC20 finite-vanishing criterion or prove unconditional RH.

2026-06-28

- Continued the final route certificate hardening after commit `cf8b18f`.
- Added `route_bridge_certificate_of_sign_defect_classification` in
  `ConnesWeilRH/Route/Bridge.lean`, constructing `RouteBridgeCertificate`
  directly from `SourceTraceReadOffData`, a concrete
  `SourceSignDefectClassification` at the same lambda, the restricted-to-full
  bridge contract, and the final sign bridge contract.
- Added `route_certificate_of_sign_defect_classification` in
  `ConnesWeilRH/Route/RouteTheorem.lean`, exposing the same sign/defect
  classification package at the outer `RouteCertificate` boundary.
- This preserves the route chain
  `SourceSignDefectClassification -> SourceBackedLedgers ->
  RouteBridgeCertificate -> RouteCertificate -> final_connes_weil_rh`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.RouteTheorem` and
  `lake build ConnesWeilRH`.
- `#print axioms` for
  `route_bridge_certificate_of_sign_defect_classification`,
  `route_certificate_of_sign_defect_classification`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Logic boundary preserved: these are top-level certificate constructors only.
  They do not prove CC20 trace equality, restricted-to-full equality, final
  sign equality, accepted-source status, or unconditional RH.

2026-06-28

- Continued the hard sign/defect bridge Lean interface pass by closing the
  Ledger consumer side.
- Added `cdef_norm_formula_of_cdef_exhausts`,
  `cdef_norm_formula_of_sign_defect_classification`,
  `source_backed_ledgers_of_sign_defect_classification`,
  `cdef_norm_formula_of_source_backed_ledgers`, and
  `ledgers_cleared_of_source_sign_defect_classification` in
  `ConnesWeilRH/Route/Ledger.lean`.
- This makes the route-facing consumption path explicit:
  `SourceSignDefectClassification -> SourceBackedLedgers ->
  LedgersCleared`, with the `CdefNormFormula` fields packed from the already
  exposed `L.cdefExhausts` ledger output.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Ledger`,
  `lake build ConnesWeilRH.Route.Bridge`, and `lake build ConnesWeilRH`.
- `#print axioms` for the new Ledger constructors and existing
  `ledgers_cleared_of_source_backed` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Re-ran `#print axioms` for the new Row4-Row7 sign/defect constructors; all
  again reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Route/SignDefect.lean ConnesWeilRH/Route/Ledger.lean`.
- Logic boundary preserved: this does not prove Rows 4-7 analytically or
  unconditionally. It prevents a Lean interface drift channel where a final
  ledger consumer could ignore the named sign/defect classification package.

2026-06-28

- Began the hard sign/defect bridge Lean interface pass.
- Added Row4-Row7 constructor wrappers in
  `ConnesWeilRH/Route/SignDefect.lean` without adding analytic claims:
  `projection_defect_normal_form_data_of_parts`,
  `fixed_s_projection_defect_normal_form_of_parts`,
  `rank_pole_ledger_identification_data_of_parts`,
  `source_rank_pole_ledger_identification_of_parts`,
  `endpoint_strip_cdef_domination_data_of_parts`,
  `source_endpoint_strip_remainder_cdef_domination_of_parts`,
  `no_hidden_positive_defect_data_of_parts`,
  `no_hidden_positive_defect_outside_cdef_of_parts`, and
  `source_sign_defect_classification_of_parts`.
- These constructors make the existing Row4 projection-defect normal form,
  Row5 rank/pole ledger identification, Row6 endpoint-strip `Cdef`
  domination, and Row7 no-hidden-positive-defect interfaces explicitly
  constructible from named row parts instead of only destructible by
  projections.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.SignDefect`,
  `lake build ConnesWeilRH.Route.Ledger`,
  `lake build ConnesWeilRH.Route.Bridge`, and `lake build ConnesWeilRH`.
- `#print axioms` for the new sign/defect constructors reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Route/SignDefect.lean`.
- Logic boundary preserved: this does not prove Rows 4-7 analytically. It
  makes the hard sign/defect chain easier to audit in Lean by naming the
  packing points for each row.

2026-06-28

- Continued trace-to-Weil compatibility constructor hardening.
- Added `full_trace_read_off_source_of_parts`,
  `restricted_trace_read_off_source_of_parts`,
  `trace_weil_compatibility_data_of_sources`, and
  `trace_weil_compatibility_of_sources` in
  `ConnesWeilRH/Route/Theorem1.lean`.
- Added `full_trace_read_off_source_of_bridge` and
  `restricted_trace_read_off_source_of_bridge`, making the two bridge fields in
  `SourceTraceReadOffData` explicit named entry points.
- Refactored `trace_weil_compatibility_of_source_trace_data` so it goes through
  `trace_weil_compatibility_of_sources` instead of manually assembling the
  compatibility data structure.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new trace compatibility constructors, bridge-field
  wrappers, `trace_weil_compatibility_of_source_trace_data`,
  `final_sign_bridge_contract_of_common_test`, and
  `final_sign_bridge_of_contract` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Route/Theorem1.lean ConnesWeilRH/Route/Bridge.lean`.
- Logic boundary preserved: this does not prove the CC20 trace equalities. It
  isolates the exact bridge-field entry points and makes
  `TraceWeilCompatibility` consume named full/restricted trace sources.

2026-06-28

- Continued CCM25 final-sign route-facing constructor hardening.
- Added common-test projections in `ConnesWeilRH/Route/Bridge.lean`:
  `source_psi_sign_expansion_of_common_test` and
  `source_pole_sign_in_cc20_local_sum_of_common_test`.
- Added `source_qw_equals_neg_cc20_weil_sum_of_common_test` and
  `source_qw_nonnegative_to_cc20_nonpositive_of_common_test`, deriving the
  final sign rows from one `SourceQWUsesCommonTest` plus the archimedean sign
  bridge.
- Added `final_sign_bridge_data_of_common_test` and
  `final_sign_bridge_contract_of_common_test`, making the final-sign contract
  constructible from the same common package tuple and archimedean sign data.
- Refactored `final_sign_bridge_of_contract` so it uses
  `source_qw_equals_neg_cc20_weil_sum_of_common_test` instead of manually
  reassembling Psi expansion, finite-prime ownership, and pole-sign rows.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new final-sign common-test constructors and
  `final_sign_bridge_of_contract` / `final_sign_nonnegative_to_nonpositive_of_contract`
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Route/Bridge.lean`.
- Logic boundary preserved: this still does not prove the analytic final sign
  equality. It makes the Lean route derive final sign package rows from one
  common tuple instead of treating the finite-prime and pole-sign pieces as
  separately assembled facts.

2026-06-28

- Completed the next CCM25 route-facing restricted/full constructor closure
  slice.
- Added `restricted_to_full_bridge_data_of_common_tuple`, constructing
  `RestrictedToFullQWBridgeData` from one
  `RestrictedToFullQWLargeLambdaThreshold`, current-above-threshold evidence,
  one `SourceCommonTestTupleContract`, and lower-bound evidence. Its
  `scalarRestrictionEquality` field is now derived through
  `restricted_to_full_scalar_restriction_of_common_tuple`, using the
  threshold-derived finite-prime stabilization rather than being supplied as an
  independent input.
- Added `restricted_to_full_bridge_contract_of_common_tuple`, packaging the
  same data into `RestrictedToFullQWBridgeContract`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for
  `restricted_to_full_bridge_data_of_common_tuple`,
  `restricted_to_full_bridge_contract_of_common_tuple`,
  `restricted_to_full_scalar_restriction_of_common_tuple`, and
  `restricted_to_full_lower_bound_transfer_of_common_tuple` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Route/Theorem1.lean ConnesWeilRH/Route/Bridge.lean`.
- Logic boundary preserved: this still does not prove analytic
  restricted-to-full equality. It closes a Lean interface drift channel by
  deriving scalar restriction evidence from common package-backed tuple data
  and threshold/stabilization evidence.

2026-06-28

- Continued CCM25 restricted/full route-facing constructor hardening.
- Added Bridge-level constructors from a single
  `SourceCommonTestTupleContract`:
  `source_restricted_qw_lambda_definition_read_off_of_common_tuple`,
  `source_full_qw_definition_read_off_of_common_tuple`, and
  `source_archimedean_pole_stability_of_common_tuple`.
- Added
  `source_qw_lambda_restriction_rows_of_common_tuple` and
  `source_qw_lambda_is_restriction_of_common_tuple`, making
  `SourceQWLambdaRestrictionRows` constructible from common package read-off
  plus `RestrictedFinitePrimeSupportStabilizes`.
- Added
  `restricted_to_full_scalar_restriction_of_common_tuple` and
  `restricted_to_full_lower_bound_transfer_of_common_tuple`, connecting the
  new package-backed restriction rows to the restricted-to-full scalar
  equality and lower-bound transfer interfaces.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new Bridge constructors reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Route/Theorem1.lean ConnesWeilRH/Route/Bridge.lean`.
- Logic boundary preserved: this still does not prove restricted-to-full
  equality analytically. It makes the Lean route for restricted/full
  definition rows consume one common package-backed tuple plus stabilization
  evidence instead of leaving those rows as independently supplied facts.

2026-06-28

- Continued CCM25 route-facing read-off hardening after the package-boundary
  milestone commit `6fe47bd`.
- Added package-backed CCM25 read-off projections in
  `ConnesWeilRH/Route/Theorem1.lean`:
  `ccm25_qw_definition_read_off_of_package`,
  `ccm25_psi_sign_read_off_of_package`,
  `ccm25_full_qw_read_off_of_package`,
  `ccm25_qw_lambda_formula_read_off_of_package`,
  `ccm25_pole_normalization_read_off_of_package`,
  `ccm25_restricted_qw_read_off_of_package`, and
  `ccm25_weil_form_read_off_of_package`.
- Refactored the source-trace-data projections
  `ccm25_weil_form_read_off_of_source_trace_data`,
  `ccm25_full_qw_read_off_of_source_trace_data`, and
  `ccm25_restricted_qw_read_off_of_source_trace_data` so they consume the new
  package-backed projection theorems instead of hand-assembling package
  component fields.
- Updated `ConnesWeilRH/Route/Bridge.lean` so
  `package_backed_ccm25_weil_form_read_off` uses the new package-backed
  read-off projection theorems for QW, Psi sign, QW_lambda, and pole
  normalization.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Bridge`, and `lake build ConnesWeilRH`.
- `#print axioms` for the new package-backed read-off projections, the
  source-trace-data projections, and
  `package_backed_ccm25_weil_form_read_off` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Route/Theorem1.lean ConnesWeilRH/Route/Bridge.lean`.
- Logic boundary preserved: this does not prove CCM25's analytic formula rows.
  It makes the route-facing QW/QW_lambda read-off path consume the concrete
  arithmetic package boundary instead of repeated hand-assembly.

2026-06-28

- Continued the CCM25 finite-prime package-boundary hardening.
- Added package-level finite-prime evaluator-sum names in
  `ConnesWeilRH/Source/CCM25Concrete/Package.lean`:
  `source_global_finite_prime_evaluator_sum` and
  `source_restricted_finite_prime_evaluator_sum`.
- Refactored `Package.global_finite_prime_sum_of_package_components` and
  `Package.restricted_finite_prime_sum_of_package_components` so their RHS is
  the new package-level evaluator-sum name rather than the internal
  `formula_components ... certificate.atoms` path.
- Updated `ConnesWeilRH/Route/Bridge.lean` so
  `PackageBackedCCM25WeilFormReadOff`,
  `SourceFinitePrimeSignOwnedByPackage`, and
  `PackageFinitePrimeSupportStabilization` consume
  `Package.source_global_finite_prime_evaluator_sum pkg` and
  `Package.source_restricted_finite_prime_evaluator_sum pkg`. A Route-layer
  search now has no matches for `formula_components pkg`,
  `finitePrimeSumReadOff.certificate.atoms`, `certificate.atoms`,
  `SourceGlobalFinitePrimeEvaluatorSum`, or
  `SourceRestrictedFinitePrimeEvaluatorSum`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new package evaluator-sum names, their package
  read-off theorems, `package_backed_ccm25_weil_form_read_off`,
  `package_finite_prime_support_stabilization`,
  `source_finite_prime_sign_owned_by_common_test`,
  `finite_prime_normalization_of_sign_owned_package`, and
  `finite_prime_normalization_of_legacy_sign_owned_formula` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean ConnesWeilRH/Source/CCM25Concrete/Interface.lean ConnesWeilRH/Source/CCM25Concrete/Package.lean ConnesWeilRH/Route/Bridge.lean`.
- Logic boundary preserved: this is still interface hardening, not a proof of
  CCM25 analytic finite-prime normalization. It closes another Lean drift
  channel by making Route consume package-level finite-prime sum objects
  instead of internal component certificates.

2026-06-28

- Continued the CCM25 finite-prime normalization hardening pass.
- Added global-index projections in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`:
  `arithmetic_global_index_prime_power_of_certificate`,
  `arithmetic_global_index_visible_of_certificate`, and
  `arithmetic_global_index_one_lt_of_certificate`.
- Added matching arithmetic-row projections in
  `ConnesWeilRH/Source/CCM25Concrete/Interface.lean`:
  `arithmetic_global_index_prime_power_of_arithmetic_rows`,
  `arithmetic_global_index_visible_of_arithmetic_rows`,
  `arithmetic_global_index_one_lt_of_arithmetic_rows`, plus
  `arithmetic_restricted_index_lambda_cut_of_arithmetic_rows`.
- Added package-level fixed-test projections in
  `ConnesWeilRH/Source/CCM25Concrete/Package.lean`:
  `source_test_of_package`, `global_index_prime_power_of_package`,
  `global_index_visible_of_package`, `global_index_one_lt_of_package`,
  `restricted_index_prime_power_of_package`,
  `restricted_index_visible_of_package`,
  `restricted_index_lambda_cut_of_package`,
  `restricted_index_one_lt_of_package`, and
  `restricted_index_le_lambda_sq_of_package`.
- Updated `ConnesWeilRH/Route/Bridge.lean` so
  `PackageFinitePrimeSupportStabilization` exposes
  `Package.source_test_of_package pkg` instead of directly naming
  `cert.support.sourceTest` in its global/restricted membership facts. The
  proof now derives prime-power, visibility, and lambda-cut facts through
  package-level projections.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`,
  `lake build ConnesWeilRH.Route.Bridge`, and `lake build ConnesWeilRH`.
- `#print axioms` for the new global/restricted package projections and
  `Route.package_finite_prime_support_stabilization` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean ConnesWeilRH/Source/CCM25Concrete/Interface.lean ConnesWeilRH/Source/CCM25Concrete/Package.lean ConnesWeilRH/Route/Bridge.lean`.
- Logic boundary preserved: this still does not prove CCM25's analytic
  finite-prime normalization or restricted-to-full equality. It reduces route
  dependence on internal certificate field shape and makes fixed-test
  global/restricted prime-power support facts available through package-level
  theorem names.

2026-06-28

- Began the next CCM25 finite-prime normalization hardening pass after the
  signed/pushed RH-exit bridge milestone.
- Added `PrimePowerSupport.source_lambda_cut_one_lt` and
  `PrimePowerSupport.source_lambda_cut_le_lambda_sq`, splitting
  `SourceLambdaCut lambda n` into the explicit `1 < n` and
  `(n : Real) <= lambda^2` facts needed by fixed-cutoff support audits.
- Added certificate-level restricted-index projections in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`:
  `arithmetic_restricted_index_prime_power_of_certificate`,
  `arithmetic_restricted_index_visible_of_certificate`,
  `arithmetic_restricted_index_one_lt_of_certificate`, and
  `arithmetic_restricted_index_le_lambda_sq_of_certificate`.
- Added arithmetic-row interface projections in
  `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` so downstream code can
  obtain restricted-index prime-power, source-test visibility, `1 < n`, and
  `(n : Real) <= lambda^2` without depending on the internal certificate field
  shape.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new finite-prime restricted-index projection
  theorems reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean ConnesWeilRH/Source/CCM25Concrete/Interface.lean`.
- Logic boundary preserved: this does not prove CCM25 finite-prime
  normalization or RH. It makes the fixed-lambda restricted finite-prime
  support facts directly Lean-visible for later restricted-to-full work.

2026-06-28

- Hardened the CC20 interface-level finite-vanishing exit in
  `ConnesWeilRH/Source/CC20.lean` and `ConnesWeilRH/Route/RouteTheorem.lean`.
- Added `CC20Interface.finite_vanishing_source_rh`, projecting the stored
  `sourceFiniteVanishingRhExit` package to source RH for a given
  `WeilPositivityInput`.
- Added `CC20Interface.finite_vanishing_mathlib_rh_point`, exposing the exact
  pointwise Mathlib RH output at the CC20 interface level.
- Added `CC20Interface.finite_vanishing_mathlib_rh`, the universal wrapper over
  the pointwise theorem.
- Updated `final_connes_weil_rh` so the final route uses
  `Source.CC20Interface.finite_vanishing_mathlib_rh inputs.cc20` instead of
  directly calling `inputs.cc20.finiteVanishingRhExit.criterion`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for `CC20Interface.finite_vanishing_source_rh`,
  `CC20Interface.finite_vanishing_mathlib_rh_point`,
  `CC20Interface.finite_vanishing_mathlib_rh`,
  `finite_vanishing_rh_exit_holds`, and `final_connes_weil_rh` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Source/RHDefinition.lean ConnesWeilRH/Source/CC20RHExit.lean ConnesWeilRH/Source/CC20.lean ConnesWeilRH/Route/RouteTheorem.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove the CC20 analytic
  criterion or RH. It makes the final route visibly consume the source-backed
  CC20 exit package and the exact pointwise Mathlib RH output rather than a
  broad black-box criterion field.

2026-06-28

- Hardened the CC20 finite-vanishing exit bridge in
  `ConnesWeilRH/Source/CC20RHExit.lean`.
- Added `criterion_mathlib_rh_point`, exposing the exact pointwise Mathlib RH
  conclusion obtained from a `SourceFiniteVanishingCriterionPackage`: given the
  route input, triple vanishing, full Weil positivity, `riemannZeta s = 0`,
  negative-even exclusion, and pole exclusion, it returns `s.re = 1 / 2`.
- Refactored `criterion_to_mathlib_rh` so it is only the universal wrapper
  around `criterion_mathlib_rh_point`.
- Added `standard_criterion_mathlib_rh_point` for the canonical
  `RHDefinitionBridge.standard`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.CC20RHExit` and
  `lake build ConnesWeilRH`.
- `#print axioms` for `criterion_source_output`,
  `criterion_mathlib_rh_point`, `criterion_to_mathlib_rh`,
  `standard_criterion_mathlib_rh_point`,
  `standard_criterion_to_mathlib_rh`,
  `standard_criterion_output_iff_mathlib`, and `final_connes_weil_rh` reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and
  `git diff --check -- ConnesWeilRH/Source/RHDefinition.lean ConnesWeilRH/Source/CC20RHExit.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove the CC20 analytic
  criterion or RH. It makes the final exit factor through source RH and then
  through the exact pointwise Mathlib RH signature, rather than exposing only a
  black-box `_root_.RiemannHypothesis` conclusion.

2026-06-28

- Added an exact-signature point theorem for the RH definition bridge in
  `ConnesWeilRH/Source/RHDefinition.lean`.
- Lean `#print _root_.RiemannHypothesis` confirms Mathlib's current target is
  exactly
  `∀ s : ℂ, riemannZeta s = 0 -> (¬∃ n, s = -2 * (n + 1)) -> s ≠ 1 -> s.re = 1 / 2`.
- Added `mathlib_rh_point_of_source_rh`, whose arguments match that Mathlib
  pointwise signature exactly: zeta zero, negative-even exclusion, pole
  exclusion, then the critical-line conclusion.
- Refactored `source_rh_to_mathlib_rh` so it is just the universal wrapper
  around `mathlib_rh_point_of_source_rh`.
- Added `standard_mathlib_rh_point_of_source_rh` for the canonical bridge.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.RHDefinition`,
  `lake build ConnesWeilRH.Source.CC20RHExit`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for `mathlib_rh_point_of_source_rh`,
  `source_rh_to_mathlib_rh`, `standard_mathlib_rh_point_of_source_rh`,
  `standard_source_rh_iff_mathlib`,
  `SourceFiniteVanishingCriterionPackage.criterion_to_mathlib_rh`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Source/RHDefinition.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove CC20 source RH or RH. It
  confirms and exposes the exact Mathlib pointwise RH signature consumed by
  the source-to-Mathlib definition bridge.

2026-06-28

- Completed another RH definition bridge decomposition pass in
  `ConnesWeilRH/Source/RHDefinition.lean`.
- Added `source_nontrivial_zero_of_mathlib_components`, making the reverse
  direction from Mathlib zeta zero, negative-even exclusion, and pole exclusion
  to the source nontrivial-zero predicate a named theorem.
- Added `mathlib_critical_line_of_source_critical_line` and
  `source_critical_line_of_mathlib_critical_line`, so the critical-line bridge
  no longer appears only as fields inside `source_critical_line_iff_mathlib`.
- Refactored `source_rh_to_mathlib_rh` and `mathlib_rh_to_source_rh` to use the
  named component theorems. The route is now visible as:
  Mathlib zero components -> source nontrivial zero -> source RH -> source
  critical line -> Mathlib critical line, and conversely through the source
  nontrivial-zero component projections.
- Added standard-bridge projections for reverse nontrivial-zero construction
  and both critical-line directions.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.RHDefinition`,
  `lake build ConnesWeilRH.Source.CC20RHExit`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new transport/critical-line component theorems,
  `source_rh_to_mathlib_rh`, `mathlib_rh_to_source_rh`,
  `source_rh_iff_mathlib`,
  `SourceFiniteVanishingCriterionPackage.criterion_to_mathlib_rh`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Source/RHDefinition.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove CC20 source RH or RH. It
  makes the final RH-definition transport path explicit enough to audit each
  object bridge separately.

2026-06-28

- Further decomposed the RH nontrivial-zero definition bridge in
  `ConnesWeilRH/Source/RHDefinition.lean`.
- Added component theorems
  `mathlib_zeta_zero_of_source_nontrivial_zero`,
  `mathlib_no_negative_even_of_source_nontrivial_zero`,
  `mathlib_no_pole_of_source_nontrivial_zero`, and
  `mathlib_nontrivial_zero_of_components`.
- Refactored `source_nontrivial_zero_to_mathlib` so it is assembled from the
  three named Mathlib nontrivial-zero components instead of proving the full
  conjunction directly.
- Added standard-bridge projections for the zeta-zero, negative-even exclusion,
  and pole-exclusion components.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.RHDefinition`,
  `lake build ConnesWeilRH.Source.CC20RHExit`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new component theorems,
  `source_nontrivial_zero_to_mathlib`,
  `source_nontrivial_zero_iff_mathlib`,
  the standard component projections,
  `SourceFiniteVanishingCriterionPackage.criterion_to_mathlib_rh`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Source/RHDefinition.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove CC20 source RH or RH. It
  makes the three Mathlib nontrivial-zero obligations separately auditable
  before the source-RH-to-Mathlib-RH bridge consumes them.

2026-06-28

- Hardened the RH definition bridge in
  `ConnesWeilRH/Source/RHDefinition.lean`.
- Added the component theorem `source_zeta_zero_iff_mathlib`, proving
  `B.sourceZeta s = 0 ↔ riemannZeta s = 0` directly from
  `B.sourceZeta_eq_mathlib`.
- Updated `source_nontrivial_zero_to_mathlib` so its zeta-zero leg now factors
  through `source_zeta_zero_iff_mathlib` instead of hiding the zeta identity
  inside a local rewrite.
- Added `standard_source_zeta_zero_iff_mathlib` for the canonical bridge.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Source.RHDefinition`,
  `lake build ConnesWeilRH.Source.CC20RHExit`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for `source_zeta_zero_iff_mathlib`,
  `source_nontrivial_zero_to_mathlib`,
  `source_nontrivial_zero_iff_mathlib`, `source_rh_iff_mathlib`,
  `standard_source_zeta_zero_iff_mathlib`,
  `standard_source_rh_iff_mathlib`,
  `SourceFiniteVanishingCriterionPackage.criterion_to_mathlib_rh`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Source/RHDefinition.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove the CC20 source RH
  theorem or RH. It makes the source-zeta-to-Mathlib-zeta zero bridge
  separately auditable before nontrivial-zero and RH transport consume it.

2026-06-28

- Generalized the restricted-to-full threshold projection in
  `ConnesWeilRH/Route/Bridge.lean`.
- Replaced the special-case signature of
  `restricted_to_full_qw_lambda_threshold_of_contract`, which had required
  `lambda = 1` and the dummy `RouteLedgers.mk False False False`, with a
  general projection from
  `RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg` to
  `RestrictedToFullQWLambdaThreshold inputs g F_g`.
- Confirmed the current restricted-to-full large-lambda layer already feeds the
  current package into `primePowerAtomStabilizationAtLarge` through
  `SourceCommonTestTupleContract inputs g lambda F_g pkg`; the change removes
  a misleading special-case theorem rather than adding a new analytic claim.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for
  `restricted_to_full_qw_lambda_threshold_of_contract`,
  `current_above_threshold_of_restricted_to_full_contract`,
  `fixed_test_support_threshold_of_large_lambda_threshold`,
  `prime_power_atom_stabilization_of_large_lambda_threshold`,
  `finite_prime_stabilization_at_large_of_threshold`,
  `finite_prime_stabilization_of_large_lambda_threshold`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove the analytic
  restricted-to-full equality. It removes a Lean-level audit hazard where a
  theorem name suggested a general threshold projection but its old type was
  tied to `lambda = 1` and a dummy ledger.

2026-06-28

- Strengthened the final-sign common-test leg in
  `ConnesWeilRH/Route/Bridge.lean`.
- Replaced the weaker definition of `SourceQWUsesCommonTest` with the full
  `SourceCommonTestTupleContract inputs g lambda F_g pkg`, so final sign, Psi,
  pole, and finite-prime rows now inherit the same
  `WindowLambdaCompatibility`, package-backed CCM25 read-off, and convolution
  square compatibility used by the restricted-to-full bridge.
- Added named projections
  `source_qw_common_tuple_of_common_test`,
  `source_qw_square_compatibility_of_common_test`, and
  `source_qw_package_read_off_of_common_test`; updated
  `source_finite_prime_sign_owned_by_common_test` to use the package read-off
  projection rather than depending on the old product shape of
  `SourceQWUsesCommonTest`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for `SourceQWUsesCommonTest`,
  `source_qw_common_tuple_of_common_test`,
  `source_qw_square_compatibility_of_common_test`,
  `source_qw_package_read_off_of_common_test`,
  `source_finite_prime_sign_owned_by_common_test`,
  `final_sign_bridge_of_contract`, and `final_connes_weil_rh` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove the analytic final sign
  theorem or RH. It removes a Lean-level drift hole where final sign could use
  a weaker local common-test predicate that did not explicitly include the
  shared window-lambda compatibility leg.

2026-06-28

- Hardened the final-sign finite-prime leg in
  `ConnesWeilRH/Route/Bridge.lean`.
- Added `source_finite_prime_sign_owned_by_common_test`, deriving
  `SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg` from the same
  `SourceQWUsesCommonTest inputs g lambda F_g pkg` package-backed read-off used
  by the QW, Psi, and pole legs.
- Removed the independently fillable finite-prime sign field from
  `FinalSignBridgeData`. The final sign bridge now stores only the package
  common-test leg and the CC20 archimedean sign bridge; the finite-prime sign
  row is derived from the common-test package in `final_sign_bridge_of_contract`.
- Verification caught and fixed a real strength distinction: applying
  `finite_prime_normalization_of_package pkg` to `g.weilTest g.weilTest`
  produces only `FinitePrimeVisibilityStatement` for that pair, not the full
  `FinitePrimeNormalizationStatement`. The final theorem now uses the
  unapplied package normalization theorem.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for `source_finite_prime_sign_owned_by_common_test`,
  `FinalSignBridgeData`, `FinalSignBridgeContract`,
  `final_sign_bridge_of_contract`,
  `final_sign_nonnegative_to_nonpositive_of_contract`,
  `final_sign_bridge_of_route_bridge_certificate`, and
  `final_connes_weil_rh` reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove the analytic final sign
  equality or RH. It removes a Lean-level loophole where the final sign
  certificate could carry a finite-prime sign row independently from the
  package-backed common-test row.

2026-06-28

- Closed a full-positivity construction bypass in
  `ConnesWeilRH/Route/Exhaustion.lean`.
- Replaced the public constructor theorem
  `full_weil_positivity_of_fixed_s`, which accepted a bare
  `LedgersCleared L`, with
  `full_weil_positivity_of_source_backed_fixed_s`, which requires
  `SourceBackedLedgers inputs g L`.
- Updated `full_weil_positivity_of_source_backed` so full Weil positivity is
  produced from fixed-S trace read-off, source-backed triple vanishing, and
  source-backed ledgers, with `LedgersCleared L` derived internally by
  `ledgers_cleared_of_source_backed`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Exhaustion` and `lake build ConnesWeilRH`.
- `#print axioms` for
  `full_weil_positivity_of_source_backed_fixed_s`,
  `full_weil_positivity_of_source_backed`,
  `full_weil_positivity_input_holds`, and `final_connes_weil_rh` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Route/Exhaustion.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove RH or the analytic
  sign/defect theorem. It prevents future route code from constructing
  `FullWeilPositivity` using a naked `LedgersCleared L` proof that bypasses the
  source-backed sign/defect classification.

2026-06-28

- Further hardened the top-level sign/defect classification in
  `ConnesWeilRH/Route/SignDefect.lean`.
- Minimized `SourceSignDefectClassification` to the two top-level generators:
  `oneLtLambda` and `noHiddenPositiveDefect`.
- Removed independently fillable Row 1--4 and Row 5--6 fields from the top-level
  classification: `sourceOrientation`, `sourceRemainderAfterQ`,
  `postQTermwiseFixedSTransport`, `postQSeriesTailTransport`,
  `postQFixedSTransport`, `projectionDefectNormalForm`,
  `rankPoleLedgerIdentification`, and `endpointStripCdefDomination`.
- Added named projections deriving the visible Row 1--4 outputs from Row 7
  positive-trace ownership and the current-lambda Row 4 endpoint/no-strip facts
  from Row 6 endpoint-strip domination. This keeps the Row 1--7 audit trail
  visible without letting the top-level certificate carry duplicate,
  independently fillable rows.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.SignDefect` and `lake build ConnesWeilRH`.
- `#print axioms` for `SourceSignDefectClassification`,
  `source_orientation_of_sign_defect_classification`,
  `source_remainder_after_q_of_sign_defect_classification`,
  `post_q_fixed_s_transport_of_sign_defect_classification`,
  `post_q_derivative_domain_of_sign_defect_classification`,
  `post_q_boundary_transport_of_sign_defect_classification`,
  `post_q_series_tail_of_sign_defect_classification`,
  `row4_no_strip_split_of_sign_defect_classification`,
  `row4_endpoint_strip_of_sign_defect_classification`, the Row 7
  sign-defect projections, and the ledger-clearing projections reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`
  and `git diff --check -- ConnesWeilRH/Route/SignDefect.lean MEMORY.md`.
- Logic boundary preserved: this still does not prove RH or the analytic
  sign/defect theorem unconditionally. It removes a Lean-level loophole where
  the top-level sign/defect certificate could separately assert Row 1--6 facts
  that should be read through the Row 7 no-hidden-positive-defect package.

2026-06-28

- Hardened Row 7 of the sign/defect bridge in
  `ConnesWeilRH/Route/SignDefect.lean`.
- Minimized `NoHiddenPositiveDefectOutsideCdefData` to three Row 7 generators:
  `sourcePositiveTraceRemainderOwnership`, `rankPoleLedgerIdentification`, and
  `endpointStripCdefDomination`.
- Removed independently fillable combination fields:
  `transportedSourceRemainderPartition`,
  `endpointStripRemainderBoundForRow7`, and
  `positiveTraceToRestrictedLowerBound`.
- Updated Row 7 projections so
  `row7_transported_partition_of_no_hidden_positive_defect`,
  `row7_endpoint_strip_bound_of_no_hidden_positive_defect`, and
  `row7_positive_trace_to_lower_bound_of_no_hidden_positive_defect` are
  derived from the Row 5 and Row 6 witnesses.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.SignDefect` and `lake build ConnesWeilRH`.
- `#print axioms` for `NoHiddenPositiveDefectOutsideCdefData`,
  `NoHiddenPositiveDefectOutsideCdef`, and the Row 7 projections reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/SignDefect.lean MEMORY.md`, and a
  shape scan confirming the removed Row 7 combination fields are gone.
- Logic boundary preserved: this does not prove the analytic no-hidden-positive
  defect equality. It prevents Row 7 from independently asserting transported
  partition, endpoint-strip bound, or lower-bound transfer apart from the
  positive-trace ownership, Row 5 rank/pole identification, and Row 6 Cdef
  domination inputs.

2026-06-28

- Hardened Row 6 of the sign/defect bridge in
  `ConnesWeilRH/Route/SignDefect.lean`.
- Minimized `EndpointStripCdefDominationData` to Row 6 generators:
  `row4EndpointStripInput`, `windowSupportContainment`,
  `postQSeriesTailBoundedComparison`, `row5RankPoleRemovalInput`, and
  `cdefExhausts`.
- Removed independently fillable combination fields:
  `endpointStripTermsCdefIndexed`, `traceNormDomination`,
  `remainderCdefBound`, and `fixedTestCdefExhaustion`.
- Updated Row 6 projections so
  `row6_endpoint_terms_indexed_of_cdef_domination`,
  `row6_trace_norm_domination_of_cdef_domination`,
  `row6_remainder_bound_of_cdef_domination`, and
  `row6_fixed_test_cdef_exhaustion_of_cdef_domination` are derived from the
  minimized data.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.SignDefect` and `lake build ConnesWeilRH`.
- `#print axioms` for `EndpointStripCdefDominationData`,
  `SourceEndpointStripRemainderCdefDomination`, and the Row 6 projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/SignDefect.lean MEMORY.md`, and a
  shape scan confirming the removed Row 6 combination fields are gone.
- Logic boundary preserved: this does not prove endpoint-strip Cdef domination
  analytically. It prevents Row 6 from independently asserting term indexing,
  trace-norm domination, remainder bound, or fixed-test exhaustion apart from
  the normal-form, support, tail-comparison, Row 5, and `Cdef` exhaustion
  inputs.

2026-06-28

- Hardened Row 5 of the sign/defect bridge in
  `ConnesWeilRH/Route/SignDefect.lean`.
- Minimized `RankPoleLedgerIdentificationData` to the actual Row 5 generators:
  `row4NoStripInput`, `noExtraNoStripChannel`, `rankKilled`, and `poleKilled`.
- Removed independently fillable fields for `noStripChannels`,
  `rankLedgerIdentification`, `poleLedgerIdentification`, and
  `ledgerVanishingGate`.
- Added derived projections
  `row5_rank_identification_of_rank_pole_identification`,
  `row5_pole_identification_of_rank_pole_identification`, and
  `row5_ledger_vanishing_gate_of_rank_pole_identification`; existing rank,
  pole, no-strip, and no-extra projections now derive from the minimized data.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.SignDefect` and `lake build ConnesWeilRH`.
- `#print axioms` for `RankPoleLedgerIdentificationData`,
  `SourceRankPoleLedgerIdentification`, and the Row 5 projections reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/SignDefect.lean MEMORY.md`, and a
  shape scan confirming the removed Row 5 combination fields are gone.
- Logic boundary preserved: this does not prove rank/pole ledger
  identification analytically. It prevents Row 5 from independently asserting
  rank/pole identification or the ledger vanishing gate apart from the
  no-strip input and killed-ledger facts.

2026-06-28

- Hardened Row 4 of the sign/defect bridge in
  `ConnesWeilRH/Route/SignDefect.lean`.
- Removed the independently fillable `classificationOutput` field from
  `ProjectionDefectNormalFormData`. The row already stores
  `noStripProjectionSplit` and `endpointStripNormalForm`, and
  `SourceRemainderRow4ClassificationOutput` is exactly their conjunction.
- Updated `row4_classification_output_of_normal_form` so it derives the
  classification output from `h.choose.noStripProjectionSplit` and
  `h.choose.endpointStripNormalForm`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.SignDefect` and `lake build ConnesWeilRH`.
- `#print axioms` for `ProjectionDefectNormalFormData`,
  `FixedSProjectionDefectNormalFormForSourceRemainder`, and the Row 4
  projections reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/SignDefect.lean MEMORY.md`, and a
  shape scan confirming `classificationOutput` is no longer a Row 4 data
  field.
- Logic boundary preserved: this does not prove the analytic projection-defect
  normal form. It prevents Row 4 from independently asserting a classification
  output detached from the no-strip split and endpoint-strip normal form rows.

2026-06-28

- Bound the final sign archimedean leg to the same CC20 trace object used by
  `SourceTraceReadOffData` in `ConnesWeilRH/Route/Bridge.lean`.
- Strengthened `SourceArchimedeanSignBridge` so it now takes
  `a : inputs.cc20.archimedeanSymbols.Test` and requires
  `CC20TraceLegality inputs a`, `CC20PositiveTraceNonnegative inputs a`, plus
  the CC20 signs/normalizations and Mellin half-density convention.
- Propagated the explicit archimedean test through
  `SourceQWEqualsNegCC20WeilSum`,
  `SourceQWNonnegativeToCC20Nonpositive`, `FinalSignBridgeData`, and
  `FinalSignBridgeContract`.
- Updated `RouteBridgeCertificate.finalSignBridge` and its projection so final
  sign consumes `sourceTraceReadOff.archimedeanTest`, the same CC20 trace object
  used by trace legality, trace-square read-off, and positive trace
  nonnegativity.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for `SourceArchimedeanSignBridge`,
  `SourceQWEqualsNegCC20WeilSum`,
  `SourceQWNonnegativeToCC20Nonpositive`, `FinalSignBridgeData`,
  `FinalSignBridgeContract`, `final_sign_bridge_of_contract`,
  `final_sign_nonnegative_to_nonpositive_of_contract`, and
  `final_sign_bridge_of_route_bridge_certificate` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`, and a
  shape scan confirming final sign is parameterized by
  `sourceTraceReadOff.archimedeanTest`.
- Logic boundary preserved: this does not prove the analytic archimedean sign
  equality. It prevents the final sign bridge from using CC20 sign conventions
  detached from the trace object used in the positive trace read-off.

2026-06-28

- Isolated the existential finite-prime sign formula entry in
  `ConnesWeilRH/Route/Bridge.lean`.
- Renamed `SourceFinitePrimeSignOwnedByFormula` to
  `LegacySourceFinitePrimeSignOwnedByFormula`, and renamed its projection to
  `finite_prime_normalization_of_legacy_sign_owned_formula`.
- The final sign bridge already consumes the package-backed row
  `SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg`; the existential
  entry was not used by `FinalSignBridgeData`, `FinalSignBridgeContract`, or
  `RouteBridgeCertificate`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the package-backed and legacy finite-prime sign rows,
  their finite-prime normalization projections, `FinalSignBridgeData`, and
  `final_sign_bridge_of_contract` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`, and a
  shape scan confirming the non-legacy existential name is gone.
- Logic boundary preserved: this does not prove finite-prime sign ownership.
  It prevents future final-sign work from accidentally treating an existential
  package witness as the package fixed by `sourceTraceReadOff`.

2026-06-28

- Bound the final sign Psi and pole legs to the same package-backed common-test
  leg in `ConnesWeilRH/Route/Bridge.lean`.
- Strengthened `SourcePsiSignExpansion` and `SourcePoleSignInCC20LocalSum` so
  both now take `lambda`, `F_g`, and the fixed-test CCM25 package, and both
  require `SourceQWUsesCommonTest inputs g lambda F_g pkg`.
- Removed independent `sourcePsiSignExpansion` and
  `sourcePoleSignInCC20LocalSum` fields from `FinalSignBridgeData`. The data
  structure now stores only the package-backed common-test leg, the
  archimedean sign bridge, and the package-backed finite-prime sign leg.
- `final_sign_bridge_of_contract` still produces the five-row final sign
  contract, but the Psi and pole rows are derived from the same common-test
  witness instead of being independently filled.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for `SourcePsiSignExpansion`,
  `SourcePoleSignInCC20LocalSum`, `FinalSignBridgeData`,
  `final_sign_bridge_of_contract`, and
  `final_sign_nonnegative_to_nonpositive_of_contract` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`, and a
  shape scan confirming `FinalSignBridgeData` no longer stores independent
  Psi or pole rows.
- Logic boundary preserved: this does not prove the analytic Psi sign
  expansion or pole sign theorem. It prevents the final sign certificate from
  mixing a package-backed common-test row with independent broad-interface Psi
  or pole rows.

2026-06-28

- Bound the final sign common-test leg to the same fixed-test CCM25 package and
  symbolic convolution square in `ConnesWeilRH/Route/Bridge.lean`.
- Strengthened `SourceQWUsesCommonTest` from a broad
  `CCM25FullQWReadOff inputs g` predicate to a package-indexed predicate:
  `SourceQWUsesCommonTest inputs g lambda F_g pkg`, requiring both
  `SourceConvolutionSquareCompatibility inputs g lambda F_g pkg` and
  `PackageBackedCCM25WeilFormReadOff inputs g lambda pkg`.
- Propagated the explicit `F_g` argument through
  `SourceQWEqualsNegCC20WeilSum`,
  `SourceQWNonnegativeToCC20Nonpositive`, `FinalSignBridgeData`, and
  `FinalSignBridgeContract`.
- Updated `RouteBridgeCertificate.finalSignBridge` and its projection so final
  sign consumes the same symbolic square
  `inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest` and the
  same `sourceTraceReadOff.ccm25ArithmeticPackage` as the trace and
  restricted-to-full bridge.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for `SourceQWUsesCommonTest`,
  `SourceQWEqualsNegCC20WeilSum`,
  `SourceQWNonnegativeToCC20Nonpositive`, `FinalSignBridgeData`,
  `FinalSignBridgeContract`, `final_sign_bridge_of_contract`,
  `final_sign_nonnegative_to_nonpositive_of_contract`, and
  `final_sign_bridge_of_route_bridge_certificate` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`, and a
  shape scan confirming `SourceQWUsesCommonTest` now requires the square
  compatibility and package-backed read-off.
- Logic boundary preserved: this does not prove the analytic final sign
  equality. It prevents the final sign bridge from using a common-test/QW
  read-off detached from the fixed trace package and restricted-to-full
  convolution square.

2026-06-28

- Hardened `FinalSignBridgeData` in `ConnesWeilRH/Route/Bridge.lean`.
- Removed the independently fillable `sourceQWEqualsNegCC20WeilSum` and
  `sourceQWNonnegativeToCC20Nonpositive` fields from the data structure.
- `FinalSignBridgeData` now stores only the five source legs:
  `sourceQWUsesCommonTest`, `sourcePsiSignExpansion`,
  `sourceArchimedeanSignBridge`, `sourceFinitePrimeSignOwnedByFormula`, and
  `sourcePoleSignInCC20LocalSum`.
- `final_sign_bridge_of_contract` now derives
  `SourceQWEqualsNegCC20WeilSum inputs g lambda pkg` by combining those five
  fields. Added `final_sign_nonnegative_to_nonpositive_of_contract`, deriving
  `SourceQWNonnegativeToCC20Nonpositive inputs g lambda pkg` from the same
  final sign equality.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for `FinalSignBridgeData`, `FinalSignBridgeContract`,
  `final_sign_bridge_of_contract`,
  `final_sign_nonnegative_to_nonpositive_of_contract`, and
  `final_sign_bridge_of_route_bridge_certificate` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`, and a
  shape scan confirming `FinalSignBridgeData` no longer stores the two
  combination rows.
- Logic boundary preserved: this does not prove the analytic CCM25-to-CC20
  sign equality or the inequality direction. It prevents a final sign
  certificate from bypassing the common-test, Psi, archimedean, finite-prime,
  and pole sign legs.

2026-06-28

- Removed the redundant `samePackageReadOff` field from
  `SourceQWLambdaRestrictionRows` in `ConnesWeilRH/Route/Bridge.lean`.
- `SourceRestrictedQWLambdaDefinitionReadOff`,
  `SourceFullQWDefinitionReadOff`, and
  `SourceArchimedeanPoleStabilityForRestriction` already each include the
  same `PackageBackedCCM25WeilFormReadOff inputs g lambda pkg` witness. Keeping
  an additional `samePackageReadOff` field allowed the package read-off row to
  be filled independently of the named restriction rows.
- `package_read_off_of_qw_lambda_restriction` now derives the package read-off
  from `h.choose.restrictedDefinition.2` instead of projecting a separate
  field.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for `SourceQWLambdaRestrictionRows`,
  `SourceQWLambdaIsRestrictionOfQW`, and the restriction-row projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`, and a
  shape scan confirming `samePackageReadOff` is gone.
- Logic boundary preserved: this does not prove the analytic
  `QW_lambda(g,g)=QW(g,g)` restriction equality. It removes a Lean-level
  same-package loophole from the restricted-to-full certificate.

2026-06-28

- Split the restricted-to-full lower-bound transfer layer in
  `ConnesWeilRH/Route/Bridge.lean`.
- Added `RestrictedToFullQWLowerBoundEvidence inputs g lambda L` for the
  endpoint-strip `Cdef` domination row by itself.
- Kept `RestrictedToFullQWLowerBoundTransfer inputs g lambda F_g L pkg` as the
  combined contract, but now derive it by
  `restricted_to_full_lower_bound_transfer_of_parts` from the scalar
  restriction equality plus the lower-bound evidence.
- Updated `RestrictedToFullQWBridgeData` so it stores
  `scalarRestrictionEquality` and `lowerBoundEvidence`, not an independently
  fillable `lowerBoundTransfer` field that redundantly contained the scalar
  equality again.
- Added projections:
  `scalar_restriction_equality_of_restricted_to_full_contract`,
  `lower_bound_evidence_of_restricted_to_full_contract`, and
  `lower_bound_transfer_of_restricted_to_full_contract`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the lower-bound evidence/transfer layer and projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`, and a
  shape scan confirming `RestrictedToFullQWBridgeData` stores
  `lowerBoundEvidence`.
- Logic boundary preserved: this does not prove scalar restriction equality,
  fixed-test `Cdef` exhaustion, lower-bound transfer analytically, final sign,
  or RH. It removes another Lean-level certification loophole where a bridge
  certificate could independently assert both a scalar equality and a
  lower-bound transfer that already included that equality.

2026-06-28

- Hardened the restricted-to-full common test tuple in
  `ConnesWeilRH/Route/Bridge.lean`.
- Replaced the weak `F_g = g.weilTest` leg inside
  `SourceCommonTestTupleContract` with
  `SourceConvolutionSquareCompatibility inputs g lambda F_g pkg`.
- The new compatibility structure stores only the minimal generator
  `F_g = inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest`.
  The QW read-off, Psi sign expansion, finite-prime visibility target, and
  visible-atom square equivalence are derived by projection theorems from that
  square equality and the same fixed-test CCM25 arithmetic package. This avoids
  a logic loophole where those rows could be filled independently of the
  package and square witness.
- Updated `RouteBridgeCertificate.restrictedToFullQWBridge` and its projection
  so the `F_g` argument is the actual symbolic convolution square, not
  `g.weilTest`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new common-tuple compatibility structure and
  projections reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Hygiene checks ran:
  `rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"`,
  `git diff --check -- ConnesWeilRH/Route/Bridge.lean MEMORY.md`, and a
  regression scan for `F_g = g.weilTest`.
- Logic boundary preserved: this does not prove the analytic convolution
  square, CCM25 source formulas, restricted-to-full equality, final sign
  bridge, or RH. It closes a Lean-visible object-drift hole in the route
  certificate.

2026-06-28

- Refined the fixed-test support threshold layer in
  `ConnesWeilRH/Route/Bridge.lean`.
- Added `FixedTestSupportCutoffData inputs g lambda`, exposing the concrete
  cutoff components used by `FixedTestSupportThresholdAtLarge`: `1 < lambda`,
  `supportInWindow`, `fourierSupportInWindow`,
  `convolutionSupportTransported`, `windowContainedInLambda`,
  `lambdaCompatible`, plus the bundled `WindowSupportContainment` and
  `WindowLambdaCompatibility`.
- Changed `FixedTestSupportThresholdAtLarge` from a direct alias of
  `SourceWindowControlsRestrictedRoute` into an existential over
  `FixedTestSupportCutoffData`.
- Added constructors/projections:
  `fixed_test_support_cutoff_data_of_source_backed`,
  `fixed_test_support_threshold_at_large_of_source_backed`,
  `window_support_containment_of_fixed_test_threshold`, and
  `window_lambda_compatibility_of_fixed_test_threshold`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the cutoff data, threshold, constructors, and projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this still does not unfold the analytic support of
  `g`, the true convolution support of `F_g`, or construct the large-lambda
  source theorem. It prevents the large-lambda threshold row from being only a
  vague window-compatibility alias.

2026-06-28

- Split the large-lambda restricted-to-full stabilization row in
  `ConnesWeilRH/Route/Bridge.lean`.
- Added `FixedTestSupportThresholdAtLarge`, `PrimePowerAtomStabilizationAtLarge`,
  and `FinitePrimeStabilizationAtLarge`.
- `RestrictedToFullQWLargeLambdaThreshold` now stores separate
  `supportThresholdAtLarge` and `primePowerAtomStabilizationAtLarge` fields.
  The former covers fixed-test window/support control after `lambda0`; the
  latter covers package finite-prime sign ownership plus package finite-prime
  support stabilization after `lambda0`.
- Removed the redundant `stabilizedAtLarge` structure field. The combined
  `FinitePrimeStabilizationAtLarge` proof is now derived by
  `finite_prime_stabilization_at_large_of_threshold` from the two named rows.
  This avoids a proof-integrity loophole where the combined field could be
  filled independently of the support-threshold and atom-stabilization fields.
- Added projections:
  `fixed_test_support_threshold_of_large_lambda_threshold`,
  `prime_power_atom_stabilization_of_large_lambda_threshold`,
  `finite_prime_stabilization_at_large_of_threshold`, and retained
  `finite_prime_stabilization_of_large_lambda_threshold` as the package-support
  stabilization projection.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the split threshold rows and projections reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not construct the analytic threshold or
  prove `QW_lambda(g,g)=QW(g,g)`. It makes the two large-lambda obligations
  separately auditable.

2026-06-28

- Replaced the restricted-to-full lambda threshold shape in
  `ConnesWeilRH/Route/Bridge.lean`.
- Added `RestrictedToFullQWLargeLambdaThreshold inputs g F_g`, which stores an
  explicit `lambda0`, a proof `1 < lambda0`, a threshold package, the common
  tuple at `lambda0`, and a `stabilizedAtLarge` field saying that every
  `lambda >= lambda0` package satisfying the same common tuple has
  `PackageFinitePrimeSupportStabilization`.
- `RestrictedToFullQWBridgeData` now stores this large-lambda threshold plus
  `currentAboveThreshold : lambda0 <= lambda`; the old broad
  `packageAt : forall lambda, 1 < lambda -> package` field was removed.
- Added projections:
  `current_above_threshold_of_restricted_to_full_contract` and
  `finite_prime_stabilization_of_large_lambda_threshold`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the large-lambda threshold structure and projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not construct the analytic threshold
  `lambda0` or prove the restricted-to-full equality. It makes the threshold
  obligation explicit and prevents the bridge from pretending that arbitrary
  `lambda > 1` packages automatically give fixed-test stabilization.

2026-06-28

- Refined restricted-to-full finite-prime stabilization in
  `ConnesWeilRH/Route/Bridge.lean`.
- Added `PackageFinitePrimeSupportStabilization inputs g lambda pkg`, which
  exposes concrete data from the same package's restricted finite-prime
  arithmetic certificate:
  global index source data, restricted index source data with
  `SourceLambdaCut`, visible-atoms-in-lambda-cut, global evaluator-sum
  read-off, and restricted evaluator-sum read-off.
- Added `package_finite_prime_support_stabilization`, deriving the new
  stabilization proposition from the package's restricted certificate and the
  package finite-prime sum projections.
- Strengthened `RestrictedFinitePrimeSupportStabilizes` so it now requires
  `SourceWindowControlsRestrictedRoute`, `SourceFinitePrimeSignOwnedByPackage`,
  and `PackageFinitePrimeSupportStabilization`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the finite-prime stabilization row and restricted-to-full
  consumers reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove an analytic large-`lambda`
  stabilization theorem or the equality `QW_lambda(g,g)=QW(g,g)`. It ensures
  the restricted-to-full contract can no longer mention finite-prime
  stabilization without exposing package-level source prime-power indices,
  lambda cuts, and evaluator-sum read-offs.

2026-06-28

- Split the restricted-to-full `SourceQWLambdaIsRestrictionOfQW` contract into
  named package-backed rows in `ConnesWeilRH/Route/Bridge.lean`.
- Added `SourceRestrictedQWLambdaDefinitionReadOff`,
  `SourceFullQWDefinitionReadOff`,
  `RestrictedFinitePrimeSupportStabilizes`, and
  `SourceArchimedeanPoleStabilityForRestriction`.
- Added `SourceQWLambdaRestrictionRows`, bundling those four rows plus the
  common `PackageBackedCCM25WeilFormReadOff` witness. The public
  `SourceQWLambdaIsRestrictionOfQW` now requires this structure instead of a
  loose conjunction of broad read-offs.
- Added projection theorems:
  `restricted_definition_of_qw_lambda_restriction`,
  `full_definition_of_qw_lambda_restriction`,
  `finite_prime_stabilization_of_qw_lambda_restriction`,
  `archimedean_pole_stability_of_qw_lambda_restriction`, and
  `package_read_off_of_qw_lambda_restriction`.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the new named restricted-to-full rows and projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this still does not prove the analytic
  `QW_lambda(g,g)=QW(g,g)` equality. It prevents that bridge from hiding the
  separate obligations for restricted definition, full definition,
  finite-prime stabilization, archimedean/pole stability, and same-package
  read-off behind one strong-sounding name.

2026-06-28

- Hardened the restricted-to-full `QW_lambda -> QW` bridge so its common test
  tuple, scalar restriction equality, lower-bound transfer, bridge data, and
  bridge contract are all parameterized by the same fixed-test
  `ConcreteCCM25ArithmeticPackage` used by `SourceTraceReadOffData`.
- Updated `ConnesWeilRH/Route/Bridge.lean` with
  `PackageBackedCCM25WeilFormReadOff inputs g lambda pkg`, an object-level
  proposition exposing the package-backed `QW`, `Psi`, `QW_lambda`, pole,
  global finite-prime sum, and restricted finite-prime sum read-offs.
- Added `package_backed_ccm25_weil_form_read_off`, constructing that
  proposition from the fixed window compatibility and the package projection
  theorems.
- `RestrictedToFullQWBridgeContract` now takes the package argument, and
  `RouteBridgeCertificate.restrictedToFullQWBridge` is tied to
  `sourceTraceReadOff.ccm25ArithmeticPackage`, matching the final sign bridge
  binding.
- Avoided a Lean proof-integrity trap: do not express same-source constraints
  by comparing proof terms such as `pkgProjection = (some Prop).1`. The correct
  shape is to write the formula/read-off statement as a proposition indexed by
  the package and construct it from package projections.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Bridge` and `lake build ConnesWeilRH`.
- `#print axioms` for the restricted-to-full package-backed bridge predicates
  and projections reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Logic boundary preserved: this does not prove the analytic
  restricted-to-full equality. It prevents the equality contract from being
  certified using CCM25 formula data detached from the fixed trace package.

2026-06-28

- Hardened the CC20 trace-to-CCM25 read-off spine so the fixed trace data now
  carries the same fixed-test CCM25 arithmetic package used by the final sign
  bridge.
- Updated `ConnesWeilRH/Route/Theorem1.lean`:
  `SourceTraceReadOffData inputs g` now has
  `ccm25ArithmeticPackage :
  ConcreteCCM25ArithmeticPackage inputs.ccm25.weilSymbols g.weilTest lambda`.
- The derived `ccm25_weil_form_read_off_of_source_trace_data`,
  `ccm25_full_qw_read_off_of_source_trace_data`, and
  `ccm25_restricted_qw_read_off_of_source_trace_data` now project
  `QW`, `Psi`, `QW_lambda`, and pole normalization from that package instead
  of directly from the broad `inputs.ccm25` interface.
- Removed the independent `traceWeilCompatibility` field from
  `SourceTraceReadOffData`; `trace_weil_compatibility_of_source_trace_data`
  is now constructed from the package-backed full/restricted read-off bridges.
- Updated `ConnesWeilRH/Route/Bridge.lean`:
  `SourceFinitePrimeSignOwnedByPackage` is parameterized by the exact package,
  and `FinalSignBridgeContract` is indexed by
  `sourceTraceReadOff.ccm25ArithmeticPackage`. This prevents the final sign
  bridge from using a finite-prime formula package different from the package
  used in the trace read-off data.
- WSL ext4 verification ran:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Bridge`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the package-backed trace/read-off and final-sign
  projections reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove the analytic CC20 trace
  equality, the restricted-to-full equality, the final sign equality, or RH. It
  removes a Lean-level same-source loophole between trace read-off,
  finite-prime read-off, and final sign data.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by adding a same-source
  arithmetic package tying the broad `CCM25Interface` and fixed-test formula
  components to one `ConcreteCCM25ArithmeticRows` input.
- Added `ConnesWeilRH/Source/CCM25Concrete/Package.lean`.
- The new `ConcreteCCM25ArithmeticPackage W f lambda` stores only `rows` and
  `oneLtLambda`; `ccm25_interface` and `formula_components` are computed
  projections, not overrideable fields. This prevents later bridges from
  accidentally mixing an interface built from one arithmetic row set with
  formula components built from another.
- Added package projections for finite-prime normalization, global `QW/Psi`
  rows, restricted `QW_lambda`, pole normalization, and global/restricted
  finite-prime evaluator sum read-offs.
- Updated `ConnesWeilRH/Source/CCM25Concrete.lean` to import the package.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the package constructors/projections reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this is a same-source packaging guard. It still
  does not prove the CCM25 analytic formulas, restricted-to-full equality,
  final sign bridge, CC20 trace read-off, or RH.
- Hardened `ConnesWeilRH/Route/Bridge.lean` so
  `SourceFinitePrimeSignOwnedByFormula inputs g lambda` now requires an
  existential `ConcreteCCM25ArithmeticPackage` at the same fixed test
  `g.weilTest` and cutoff `lambda`.
- The strengthened bridge exposes both the global finite-prime sum read-off
  and restricted finite-prime sum read-off from
  `Package.formula_components pkg`, instead of relying only on broad
  `ccm25FinitePrimeNormalization`.
- `FinalSignBridgeContract` is now indexed by the
  `sourceTraceReadOff.lambda` used by `RouteBridgeCertificate`, so the final
  sign bridge cannot silently float over a different cutoff.
- Added `finite_prime_normalization_of_sign_owned_formula` as a projection
  from the stronger same-source package witness back to the broad
  finite-prime normalization statement.
- WSL ext4 verification ran `lake build ConnesWeilRH.Route.Bridge` and
  `lake build ConnesWeilRH`; both passed.
- `#print axioms` for the strengthened bridge predicates and projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this still does not prove the analytic final sign
  equality `QW(g,g) = -sum_v W_v(F_g)`. It prevents a weaker Lean artifact from
  claiming that equality while consuming finite-prime data detached from the
  fixed-test CCM25 formula package.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by combining the global and
  restricted formula components into one fixed-test source-object package.
- Added `ConnesWeilRH/Source/CCM25Concrete/FormulaComponents.lean`.
- The new module defines `ConcreteCCM25FormulaComponents W f lambda`, bundling
  `GlobalComponent.GlobalQWPsiFormulaComponent W f f lambda` and
  `RestrictedComponent.RestrictedQWLambdaFormulaComponent W f lambda`.
- Added `formula_components_of_arithmetic_rows`, constructing the combined
  package from `Interface.ConcreteCCM25ArithmeticRows` for one fixed test and
  cutoff.
- Added projections for the global and restricted components, plus the four
  source-facing rows needed later:
  `qw_definition_of_formula_components`,
  `psi_sign_of_formula_components`,
  `qw_lambda_formula_of_formula_components`,
  `global_finite_prime_sum_of_formula_components`, and
  `restricted_finite_prime_sum_of_formula_components`.
- Updated `ConnesWeilRH/Source/CCM25Concrete.lean` to import the new combined
  component module.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FormulaComponents`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the combined component constructor and projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this creates a common input package for later
  sign and restricted-to-full bridges, but it does not prove the final
  CCM25-to-CC20 sign bridge, the restricted-to-full equality
  `QW_lambda(g,g)=QW(g,g)`, or any analytic source theorem.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by adding a global `QW/Psi`
  component layer mirroring the restricted component layer.
- Added `ConnesWeilRH/Source/CCM25Concrete/GlobalComponent.lean`.
- The new module defines `GlobalFinitePrimeSumReadOff`, which stores the
  fixed-lambda arithmetic certificate and the global finite-prime sum read-off
  to `SourceGlobalFinitePrimeEvaluatorSum`.
- It also defines `GlobalQWPsiFormulaComponent`, bundling `1 < lambda`, the
  `QW(f,g)=Psi(f^* * g)` row, the `Psi` sign expansion row, and the global
  finite-prime sum read-off.
- Added constructors from `Interface.ConcreteCCM25ArithmeticRows`:
  `global_finite_prime_sum_read_off_of_arithmetic_rows` and
  `global_qw_psi_formula_component_of_arithmetic_rows`.
- Added projection theorems `qw_definition_of_component`,
  `psi_sign_of_component`, and `global_finite_prime_sum_of_component`.
- Updated `ConnesWeilRH/Source/CCM25Concrete.lean` to import the new global
  component module.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.GlobalComponent`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the global component constructors and projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove the final CCM25-to-CC20 sign
  bridge or restricted-to-full equality. It only packages the global `QW/Psi`
  source rows together with the finite-prime evaluator-sum leg so later sign
  and trace bridges can consume the global finite-prime part explicitly.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by adding a restricted
  `QW_lambda` component layer that keeps the source formula and finite-prime
  evaluator sum read-off visible as separate fields.
- Added
  `ConnesWeilRH/Source/CCM25Concrete/RestrictedComponent.lean`.
- The new module defines `RestrictedFinitePrimeSumReadOff`, which stores the
  fixed-lambda arithmetic certificate and the restricted finite-prime sum
  read-off to `SourceRestrictedFinitePrimeEvaluatorSum`.
- It also defines `RestrictedQWLambdaFormulaComponent`, bundling `1 < lambda`,
  the original `QWLambdaFormulaStatement` instance at a fixed test, and the
  restricted finite-prime sum read-off.
- Added constructors from `Interface.ConcreteCCM25ArithmeticRows`:
  `restricted_finite_prime_sum_read_off_of_arithmetic_rows` and
  `restricted_qw_lambda_formula_component_of_arithmetic_rows`.
- Added projection theorems `qw_lambda_formula_of_component` and
  `restricted_finite_prime_sum_of_component`.
- Updated `ConnesWeilRH/Source/CCM25Concrete.lean` to import the new component
  module. The existing `Restricted.lean` stayed cycle-free and still exposes
  only the broad CCM25 interface statements.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Restricted`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.RestrictedComponent`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the restricted component constructors and projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this does not prove the CCM25 source formula or
  restricted-to-full equality. It only packages the fixed-test `QW_lambda`
  formula together with the finite-prime evaluator-sum read-off so later trace
  and restricted-to-full bridges can consume the finite-prime leg explicitly.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by lifting pointwise evaluator
  atom formulas to `Finset.sum` read-off skeletons.
- Added named finite-prime evaluator sums in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean`:
  `SourceFinitePrimeEvaluatorSum`,
  `SourceGlobalFinitePrimeEvaluatorSum`, and
  `SourceRestrictedFinitePrimeEvaluatorSum`.
- Added certificate-level sum read-off theorems in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`:
  `arithmetic_finite_prime_sum_formula_of_certificate`,
  `arithmetic_global_sum_formula_of_certificate`, and
  `arithmetic_restricted_sum_formula_of_certificate`. These use only
  `Finset.sum_congr` from the pointwise atom formula.
- Added top-level arithmetic-row projections in
  `ConnesWeilRH/Source/CCM25Concrete/Interface.lean`:
  `arithmetic_global_sum_formula_of_arithmetic_rows` and
  `arithmetic_restricted_sum_formula_of_arithmetic_rows`.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the named finite-prime evaluator sums, certificate-level
  global/restricted sum read-offs, and top-level arithmetic-row sum projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this proves only the algebraic lift from pointwise
  local atom formulas to matching `Finset.sum` expressions. It does not prove
  the CCM25 `Psi` or `QW_lambda` source formula, restricted-to-full equality,
  or any analytic support-stabilization theorem.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by lifting the evaluator-level
  local atom formula to fixed-lambda arithmetic certificates and index-set
  membership gates.
- Added
  `PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean` as the named
  local atom
  `Lambda(n) * (1 / sqrt(n)) * (evaluator(F_g,n) + evaluator(F_g,n^-1))`.
- Rewrote
  `source_finite_prime_term_formula_source_evaluator` and
  `PrimePowerTerm.finite_prime_term_formula_of_source_arithmetic_data` to use
  the named local atom, reducing repeated long evaluator expressions before
  the summation layer.
- Added fixed-lambda certificate projections in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`:
  `arithmetic_global_index_source_data_of_certificate`,
  `arithmetic_restricted_index_source_data_of_certificate`,
  `arithmetic_restricted_index_lambda_cut_of_certificate`,
  `arithmetic_atom_formula_of_certificate`,
  `arithmetic_atom_formula_of_global_index_certificate`, and
  `arithmetic_atom_formula_of_restricted_index_certificate`.
- These projections expose, for `n` in the global or restricted CCM25 index
  set, both the source prime-power/visibility data and the evaluator-level
  formula for the corresponding local finite-prime atom.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the named local atom, index-set source-data projections,
  and global/restricted atom formula projections reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this prepares the finite-prime summation layer but
  does not prove any finite sum equality, the CCM25 `QW_lambda` formula, exact
  restricted support stabilization across cutoffs, or the restricted-to-full
  `QW_lambda(g,g)=QW(g,g)` bridge.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by deriving an evaluator-level
  local atom formula before any finite-prime sum is formed.
- Added
  `PrimePowerArithmetic.source_finite_prime_term_formula_source_evaluator` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean`, proving
  `W.finitePrimeTerm n (W.convolutionStar f g)` equals the Mathlib-backed
  source von Mangoldt weight times
  `(1 / Real.sqrt n) * (evaluator(F_g,n) + evaluator(F_g,n^-1))`.
- Added
  `PrimePowerTerm.finite_prime_term_formula_of_source_arithmetic_data` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerTerm.lean`, exposing the same
  evaluator-level local atom formula through the term-normalization layer.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new local atom formula and the existing arithmetic
  normalization path reported only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Logic boundary preserved: this proves only the Lean-visible composition of
  the supplied source read-off data. It does not prove the CCM25 analytic
  source formula, actual evaluation semantics, finite-prime summation equality,
  exact restricted support stabilization, or the restricted-to-full
  `QW_lambda(g,g)=QW(g,g)` bridge.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by replacing bare
  forward/inverse evaluation values with a named source evaluator object.
- Updated
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerEvaluation.lean`:
  added `SourceEvaluationFunctional`, carrying the common
  `PrimePowerTest.SourceTestEvaluationInterface W f g`, its source
  convolution square, and a `valueAt : TestFunction -> Real -> Real`
  evaluator.
- `SourceConvolutionEvaluationModel` now carries `sourceEvaluator`,
  `evaluatorSourceTestReadOff`, `forwardValueReadOff`, and
  `inverseValueReadOff`, so the forward and inverse real values are no longer
  free scalars detached from a source evaluation object.
- Added projections identifying the forward and inverse values with
  `sourceEvaluator.valueAt (W.convolutionStar f g) n` and
  `sourceEvaluator.valueAt (W.convolutionStar f g) n^-1`.
- Updated
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerPairing.lean` and
  `PrimePowerArithmetic.lean` with formulas rewriting
  `W.primePowerPairing n f g` as
  `(1 / Real.sqrt n) * (evaluator(F_g,n) + evaluator(F_g,n^-1))`.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluation`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerPairing`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new source-evaluator projections and pairing
  formulas reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this closes the Lean-visible drift where
  forward/inverse finite-prime values were loose real fields, but it still
  does not define an analytic test-function application operation, prove
  source support exactness, prove the CCM25 source formula, or prove the
  restricted-to-full `QW_lambda(g,g)=QW(g,g)` bridge.

2026-06-28

- Continued CCM25 finite-prime Lean hardening by tying support visibility and
  prime-power pairing evaluation to the same source test object inside each
  arithmetic certificate.
- Updated
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean`:
  `SourceFinitePrimeArithmeticData` now carries a
  `PrimePowerTest.SourceTestEvaluationInterface W f g` and a
  `pairingSourceTestReadOff` equality requiring
  `sourcePairing.model.sourceEvaluation.sourceTest = sourceTest`.
- Added `PrimePowerArithmetic.UsesSourceTest` and projections showing that a
  normalization package's atom-level pairing/evaluation models all use the
  named source test.
- Updated
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`:
  `FixedLambdaFinitePrimeArithmeticCertificate` now requires
  `atomsUseSupportSourceTest`, so pointwise arithmetic atoms use the same
  `sourceTest` as the support skeleton.
- Added certificate and top-level interface projections exposing
  `arithmetic_atom_source_test...` and
  `arithmetic_atom_pairing_evaluation_source_test...` through
  `FinitePrimeInterface.lean` and `Interface.lean`.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new atom/source-test consistency projections
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this closes the Lean-visible drift where support
  visibility could use one source test while `<g|T(n)g>` evaluation used
  another, but it does not formalize actual test-function evaluation, prove
  CCM25 source formulas, prove source support exactness, or prove the
  restricted-to-full `QW_lambda(g,g)=QW(g,g)` bridge.

2026-06-28

- Continued the CCM25 finite-prime Lean hardening by making the shared source
  test object visible at the arithmetic row boundary.
- Added
  `FixedLambdaArithmeticSourceTestCertificatesForTest` and
  `FixedLambdaArithmeticSourceTestCertificatesForAllTests` in
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeInterface.lean`.
- The strengthened certificate package now carries one
  `PrimePowerTest.SourceTestEvaluationInterface W f g` and requires every
  fixed-`lambda` arithmetic certificate for that same `f,g` to use that exact
  `sourceTest`.
- Updated `ConcreteCCM25ArithmeticRows` in
  `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` so the top-level CCM25
  arithmetic constructor consumes the shared-source-test certificate package
  rather than only a `Nonempty` family of per-`lambda` arithmetic certificates.
- Added projection theorems exposing the top-level source test, each
  certificate's source-test equality, and finite-prime visibility derived
  through the strengthened source-test path.
- WSL ext4 verification was done by copying the current Windows edits into
  `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new shared-source-test projections, finite-prime
  visibility/normalization bridge, arithmetic-row projection, and
  `ccm25_interface_of_arithmetic_rows` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this closes the Lean-visible loophole where
  different cutoffs could be supplied by unrelated source-test certificates,
  but it does not prove the CCM25 analytic source formulas, actual
  test-function evaluation, source support exactness, or the
  `QW_lambda(g,g)=QW(g,g)` bridge from first principles.

2026-06-28

- Continued the hard sign/defect Lean pass by splitting Row 5 rank/pole ledger
  identification inside `ConnesWeilRH/Route/SignDefect.lean`.
- Added Row 5 predicates:
  `SourceNoStripChannelsForTransportedRemainder`,
  `SourceRankLedgerIdentification`, `SourcePoleLedgerIdentification`,
  `SourceNoExtraNoStripChannel`, and
  `SourceRankPoleLedgerVanishingGate`.
- Added `RankPoleLedgerIdentificationData`, forcing Row 5 evidence to use the
  Row 4 no-strip input before identifying zero-mode rank, Tate pole channels,
  no-extra-no-strip, and the vanishing gate.
- Updated `SourceRankPoleLedgerIdentification` so `rankKilled` and
  `poleKilled` are derived through the Row 5 data rather than directly from a
  conjunction.
- Added projection theorems exposing Row 5 no-strip channels, rank ledger,
  pole ledger, and no-extra-no-strip evidence, and updated the sign/defect
  `rankKilled`/`poleKilled` projections to use Row 5.
- WSL ext4 verification was done by copying the current Windows Lean source
  slice into `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Route.SignDefect`,
  `lake build ConnesWeilRH.Route.Ledger`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the Row 5 projection theorems and sign/defect
  `rankKilled`/`poleKilled` projections reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this prevents rank/pole clearing before Row 5
  identifies the no-strip channels, but it does not prove the zero-mode rank
  formula, Tate pole support, no-extra-no-strip theorem, or triple-vanishing
  ledger gate from analytic first principles.

2026-06-28

- Continued the hard sign/defect Lean pass by splitting Row 4 projection-defect
  normal form inside `ConnesWeilRH/Route/SignDefect.lean`.
- Added Row 4 predicates:
  `SourceRemainderOwnershipForProjectionDefectRow`,
  `SourceRemainderNoStripProjectionSplit`,
  `SourceProjectionOrderEndpointStripNormalForm`, and
  `SourceRemainderRow4ClassificationOutput`.
- Added `ProjectionDefectNormalFormData` so
  `FixedSProjectionDefectNormalFormForSourceRemainder` now requires source
  ownership of the Row 3 transported remainder, no-strip/projection-order
  split, endpoint-strip normal form, and classification output data.
- Added projection theorems from the normal-form evidence and from
  `SourceSignDefectClassification`, exposing Row 4 ownership, no-strip split,
  endpoint-strip normal form, and classification output.
- WSL ext4 verification was done by copying the current Windows Lean source
  slice into `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Route.SignDefect`,
  `lake build ConnesWeilRH.Route.Ledger`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the Row 4 projection theorems reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this prevents Row 4 from classifying a route-local
  leftover, but it does not prove source ownership, no-strip/projection split,
  endpoint-strip shifted-kernel normal form, or Row 4 exhaustiveness from
  analytic first principles.

2026-06-28

- Continued the hard sign/defect Lean pass by splitting Row 3 inside
  `ConnesWeilRH/Route/SignDefect.lean`.
- Added separate Row 3 subcontracts:
  `PostQDerivativeDomainCompatibility`,
  `PostQBoundaryEvaluationTransport`, and
  `PostQSeriesTailBoundedComparison`.
- Added route-facing combined gates:
  `CC20PostQTermwiseFixedSTransport`,
  `CC20PostQSeriesTailTransport`, and the combined
  `CC20PostQRemainderFixedSSoninTransport`.
- `SourceSignDefectClassification` now requires the termwise and series-tail
  Row 3 fields explicitly, so the full Row 3 transport cannot be supplied as a
  single undifferentiated proposition.
- Added projection theorems exposing the three Row 3 subcontracts from a
  sign/defect classification, plus
  `post_q_fixed_s_transport_of_subcontracts`.
- WSL ext4 verification was done by copying the current Windows Lean source
  slice into `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Route.SignDefect`,
  `lake build ConnesWeilRH.Route.Ledger`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the Row 3 combination/projection theorems reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this prevents Row 3 from being hidden behind one
  broad transport assumption, but it does not prove the derivative-domain,
  boundary-evaluation, or series-tail analytic subcontracts.

2026-06-28

- Switched the Lean-discharge path to the hardest sign/defect area.
- Added `ConnesWeilRH/Route/SignDefect.lean`.
- The new module exposes the Rows 1-7 sign/defect chain as Lean-visible data:
  `CC20SourceRemainderOrientation`, `CC20SourceRemainderAfterQ`,
  `CC20PostQRemainderFixedSSoninTransport`,
  `FixedSProjectionDefectNormalFormForSourceRemainder`,
  `SourceRankPoleLedgerIdentification`,
  `SourceEndpointStripRemainderCdefDomination`, and
  `NoHiddenPositiveDefectOutsideCdef`.
- Row 4 is not allowed to be `True`: it depends on the post-`Q` source
  remainder and Row 3 fixed-S transport.
- Row 5 and Row 6 depend on Row 4, and Row 7 depends on Row 5 and Row 6 before
  deriving `rankKilled`, `poleKilled`, and `cdefExhausts`.
- Refactored `ConnesWeilRH/Route/Ledger.lean`: `SourceBackedLedgers` now carries
  an existential `SourceSignDefectClassification` and no longer stores the old
  direct rank/pole/Cdef bridge fields.
- Existing final route theorem still compiles, but ledger clearing now passes
  through the Rows 1-7 sign/defect contract.
- WSL ext4 verification was done by copying the current Windows Lean source
  slice into `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Route.SignDefect`,
  `lake build ConnesWeilRH.Route.Ledger`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for `ledgers_cleared_of_sign_defect_classification`,
  `rank_killed_of_source_backed_ledgers`, and
  `ledgers_cleared_of_source_backed` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this starts formalizing the hardest sign/defect
  surface and removes a direct ledger-clearing bypass, but it does not prove the
  CC20 source remainder formulas, Row 3 fixed-S transport, Row 4 normal form,
  Row 5 rank/pole identification, Row 6 Cdef domination, or Row 7 no-hidden
  defect theorem from analytic first principles.

2026-06-28

- Refactored the CC20 Lean source interface so the finite-vanishing exit no
  longer stores a direct `FiniteVanishingCriterionPackage` field.
- Updated `ConnesWeilRH/Source/CC20.lean`:
  `cc20FiniteVanishingRhExit` now states that there exists an
  `RHDefinitionBridge B` with a `SourceFiniteVanishingCriterionPackage B`.
- `CC20Interface` now stores `rhDefinitionBridge` and
  `sourceFiniteVanishingRhExit`.
- Added the derived projection
  `CC20Interface.finiteVanishingRhExit`, which converts the source-RH exit into
  the existing `FiniteVanishingCriterionPackage` only through
  `SourceFiniteVanishingCriterionPackage.toFiniteVanishingCriterionPackage`.
- Existing route code still compiles through
  `inputs.cc20.finiteVanishingRhExit.criterion`, but that accessor is no longer
  a direct source-interface field.
- WSL ext4 verification was done by copying the current Windows Lean source
  slice into `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for `CC20Interface.finiteVanishingRhExit` and
  `finite_vanishing_rh_exit_holds` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this removes the old direct Mathlib-RH exit field
  from `CC20Interface`, but it does not prove the source finite-vanishing
  criterion, Proposition C.1, sign/defect, restricted-to-full, trace-scale, or
  any source paper theorem.

2026-06-28

- Continued the no-external-reviewer Lean-discharge path by factoring the CC20
  finite-vanishing exit through the new RH definition bridge.
- Added `ConnesWeilRH/Source/CC20RHExit.lean`.
- The new module defines `SourceFiniteVanishingCriterionPackage B`, whose
  analytic criterion concludes `B.SourceRH` for an explicit
  `RHDefinitionBridge B`, rather than directly concluding Mathlib RH.
- Added `toFiniteVanishingCriterionPackage`, which converts the source-RH
  criterion into the existing `FiniteVanishingCriterionPackage` only by calling
  `RHDefinitionBridge.source_rh_to_mathlib_rh`.
- Added `criterion_factors_through_source_rh` as a definitional audit theorem
  proving the converted criterion factors exactly through the source RH bridge.
- Updated `ConnesWeilRH.lean` to import the new module.
- WSL ext4 verification was done by copying the current Windows Lean source
  slice into `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.CC20RHExit` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the two new CC20 RH-exit bridge declarations reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this prevents the CC20 exit from bypassing the RH
  definition bridge, but it does not prove Proposition C.1, the CC20 source RH
  criterion, sign/defect, restricted-to-full, trace-scale, or any source paper
  theorem.

2026-06-28

- Began the no-external-reviewer Lean-discharge path with the smallest
  definition-drift target.
- Added `ConnesWeilRH/Source/RHDefinition.lean`.
- The new module defines `Source.RHDefinitionBridge` with explicit fields for:
  source zeta, source non-trivial zero predicate, source critical-line
  predicate, source zeta equality with Mathlib `riemannZeta`, source/Mathlib
  zero transport, negative-even exclusion, pole exclusion at `s=1`, and the
  two critical-line directions.
- Proved:
  `RHDefinitionBridge.source_rh_to_mathlib_rh`,
  `RHDefinitionBridge.mathlib_rh_to_source_rh`, and
  `RHDefinitionBridge.standard_source_rh_iff_mathlib`.
- Updated `ConnesWeilRH.lean` to import the new RH definition bridge module.
- WSL ext4 verification was done by copying the current Windows Lean source
  slice into `~/projects/Connes-Weil-RH-Proof` and running:
  `lake build ConnesWeilRH.Source.RHDefinition` and
  `lake build ConnesWeilRH`.
- `#print axioms` for the three new RH-definition bridge theorems reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this discharges the Mathlib-definition transport
  shape for any supplied source RH bridge. It does not prove CC20 source RH,
  Proposition C.1, sign/defect, restricted-to-full, trace-scale, or any source
  paper theorem.

2026-06-28

- Continued the CCM25 finite-prime Lean-facing discharge with a combined
  fixed-lambda certificate.
- Added `SourcePrimePowerSupportSkeletonAtLambda` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean` so support
  exactness and pointwise coefficient normalization remain separate source
  obligations.
- Added `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`.
- The new certificate composes:
  `SourcePrimePowerSupportSkeletonAtLambda` plus
  `SourcePrimePowerTermNormalization` into
  `SourcePrimePowerSupportAtLambda`, then `ExactSupportAtLambda`, then
  `FinitePrimeVisibilityAtLambdaStatement`.
- WSL ext4 verification was done from a fresh copy of current Windows source:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new support/certificate rows reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: this proves only the fixed-`lambda` composition
  from supplied source-facing obligations. It does not prove CCM25 source
  formulas and does not upgrade fixed-window visibility to `forall lambda`.

2026-06-28

- Started the plan to discharge source interfaces by small Lean-facing pieces.
- Added the CCM25 concrete-normalization split:
  `ConnesWeilRH/Source/CCM25Concrete/Global.lean`,
  `ConnesWeilRH/Source/CCM25Concrete/Restricted.lean`,
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrime.lean`, and the aggregate
  `ConnesWeilRH/Source/CCM25Concrete.lean`.
- Updated `ConnesWeilRH.lean` to import the aggregate module.
- Added `docs/proofs/ccm25-concrete-normalization-spine.md`.
- Added `docs/audits/ccm25-concrete-normalization-axiom-audit.md`.
- Verified from a temporary WSL ext4 copy after copying current Windows source
  files into that copy:
  `lake build ConnesWeilRH.Source.CCM25Concrete.Global`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Restricted`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrime`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- Ran `#print axioms` for the new CCM25 concrete theorem rows. The only axioms
  reported were `propext`, `Classical.choice`, and `Quot.sound`.
- Logic boundary preserved: the new finite-prime module exposes that current
  CCM25 finite-prime normalization proves one-way coverage, not exact support.
  Exact finite-prime source support remains open and is the next small target.
- No commit or push was made; this is a small source-interface split, not a
  larger milestone.

2026-06-28

- Continued the CCM25 finite-prime discharge in smaller Lean pieces.
- Added `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeExact.lean`.
- The new module defines a fixed-`lambda` `ExactSupportAtLambda` certificate,
  avoiding the stronger and currently unjustified jump to `forall lambda`.
- It proves that exact support at one cutoff implies:
  `GlobalPrimeIndexCoverageStatement`,
  `RestrictedPrimeIndexCoverageStatement` for that cutoff,
  `FinitePrimeTermNormalizationStatement`, and the combined
  `FinitePrimeVisibilityAtLambdaStatement`.
- Copied the current Windows source files into a fresh WSL ext4 verification
  copy and ran:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- Ran `#print axioms` for the fixed-`lambda` exact-support theorem rows. The
  only reported axioms were `propext`, `Classical.choice`, and `Quot.sound`.
- Updated the CCM25 concrete-normalization axiom audit to mark
  `FinitePrimeExact` as built and audited.

2026-06-28

- Continued the CCM25 finite-prime exact-support pass after the normalization
  spine commit.
- Added `ConnesWeilRH/Source/CCM25Concrete/PrimePowerSupport.lean`.
- The new module defines `SourceLambdaCut lambda n` as
  `1 < n ∧ (n : Real) <= lambda^2` and a fixed-`lambda`
  `SourcePrimePowerSupportAtLambda` record.
- It proves that this more concrete source prime-power support record produces
  `FinitePrimeExact.ExactSupportAtLambda` and hence fixed-window finite-prime
  visibility.
- WSL ext4 verification was done by copying current Windows source files into
  a fresh verification tree and running:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the two new prime-power support rows reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- This still does not prove the CCM25 source support theorem. It prevents the
  next pass from using arbitrary support/cutoff predicates in place of source
  prime-power support and the numeric lambda cut.

2026-06-28

- Added `ConnesWeilRH/Source/CCM25Concrete/PrimePowerTerm.lean`.
- The module isolates pointwise finite-prime term normalization before any
  finite-prime sum is formed.
- It defines `SourcePrimePowerTermAtIndex` and
  `SourcePrimePowerTermNormalization`, then proves that the record implies
  `WeilFormSymbols.FinitePrimeTermNormalizationStatement`.
- The local atom is kept as
  `vonMangoldtWeight n * primePowerPairing n f g`; the negative sign remains
  owned by the surrounding `Psi` or `QW_lambda` formula.
- WSL ext4 verification was done from a fresh copy of current Windows source:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new pointwise term theorem reported only `propext`,
  `Classical.choice`, and `Quot.sound`.

2026-06-28

- Continued accepted-source theorem upgrade work without touching Lean.
- Added `docs/audits/accepted-source-referee-decision-form.md`.
- The decision form defines allowed verdicts:
  `accepted as stated`, `accepted after listed correction`,
  `rejected for listed obstruction`, `requires formalization before judgment`,
  and `out of scope for this reviewer`.
- Added `docs/audits/accepted-source-certification-status-board.md`.
- The board tracks all nine accepted-source packets from `packet written` to
  accepted-source decision. Current status for every row remains
  `packet written`; no accepted-source decision has been recorded.
- Updated `README.md`, `docs/audits/README.md`,
  `docs/audits/accepted-source-packet-completion-audit.md`, and `AGENTS.md`.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/audits/accepted-source-decision-evidence-matrix.md`.
- The matrix lists all nine accepted-source decisions with decision record,
  source anchors, project evidence, minimum acceptance evidence, named
  rejection paths, and route consequence if rejected.
- Updated README, the audit index, review dossier, certification status board,
  packet completion audit, and theorem-upgrade ledger to point to the matrix.
- Current status remains unchanged: the matrix makes external review more
  executable, but no row is accepted-source until a decision record receives an
  external decision, accepted independent proof, or Lean theorem with axiom
  audit.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Continued accepted-source theorem-decision work without touching Lean.
- Added the remaining five theorem-decision records:
  `docs/audits/sign-defect-referee-decision-record.md`,
  `docs/audits/restricted-to-full-referee-decision-record.md`,
  `docs/audits/final-sign-referee-decision-record.md`,
  `docs/audits/cc20-exit-referee-decision-record.md`, and
  `docs/audits/rh-definition-referee-decision-record.md`.
- Updated README, the audit index, the review dossier, the certification
  status board, the packet completion audit, and the theorem-upgrade ledger to
  record theorem-decision coverage for all nine accepted-source packets.
- Current status: all nine packets now have explicit decision records, but
  every verdict remains pending external decision, accepted independent proof,
  or Lean theorem with axiom audit.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Continued accepted-source theorem upgrade work without touching Lean.
- Added `docs/audits/ccm24-source-interface-accepted-source-packet.md`.
- The CCM24 packet covers fixed-S model, support/window transport, bounded
  comparison, fixed-window Sonin comparison, and the rule that post-`Q`
  derivative/boundary/tail transport is not automatic.
- Added `docs/audits/ccm25-source-interface-accepted-source-packet.md`.
- The CCM25 packet covers `QW`, `Psi`, `QW_lambda`, finite-prime atoms,
  finite-prime support, pole normalization, and the no-spectral boundary.
- Added `docs/audits/cc20-trace-source-interface-accepted-source-packet.md`.
- The CC20 trace packet covers support-square trace, trace-class legality,
  cyclicity, Mellin/half-density convention, and local signs.
- Added `docs/audits/accepted-source-packet-completion-audit.md`.
- The completion audit records that every source-facing row now has an
  accepted-source review packet, while accepted-source certification remains
  open for every row until external referee, accepted proof, or Lean theorem
  discharge.
- Updated `README.md`, `docs/audits/accepted-source-certification-audit.md`,
  `docs/audits/accepted-source-theorem-upgrade-ledger.md`,
  `docs/audits/README.md`, and `AGENTS.md`.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Continued accepted-source theorem upgrade work without touching Lean.
- Added `docs/audits/final-sign-accepted-source-packet.md`.
- The final sign packet states referee checks for common test identity,
  `QW=Psi`, `Psi` sign expansion, archimedean sign, finite-prime sign, pole
  sign, `QW(g,g)=-sum_v W_v(F_g)`, and the inequality direction.
- Added `docs/audits/cc20-exit-accepted-source-packet.md`.
- The CC20 exit packet states checks for Proposition C.1, the finite set
  `F={0,1/2,1}`, route triple-vanishing to Mellin vanishing, the CC20 sign
  inequality, and the source RH conclusion.
- Added `docs/audits/rh-definition-accepted-source-packet.md`.
- The RH definition packet states checks for source zeta to standard zeta,
  zero predicate equivalence, negative-even trivial-zero exclusion, pole
  exclusion at `s=1`, critical-line equivalence, and the standard RH predicate.
- Updated `README.md`, `docs/audits/accepted-source-certification-audit.md`,
  `docs/audits/accepted-source-theorem-upgrade-ledger.md`,
  `docs/audits/README.md`, and `AGENTS.md` to point to the new final-exit
  packets.
- No row was marked accepted-source. The new files are review packets, not
  external acceptance.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Continued accepted-source theorem upgrade work without touching Lean.
- Added `docs/audits/sign-defect-accepted-source-packet.md`.
- The sign/defect packet states the referee checks for Rows 1-7:
  CC20 source orientation, fixed-S post-`Q` bulk/boundary/tail transport, Row 4
  normal form, Row 5 rank/pole identification, Row 6 endpoint-strip `Cdef`
  domination, and Row 7 no-hidden-positive-defect equality.
- Added `docs/audits/restricted-to-full-accepted-source-packet.md`.
- The restricted-to-full packet states the review target
  `RestrictedToFullQWAcceptedTheorem(g,F_g)`, proving eventual fixed-test
  scalar equality `QW_lambda(g,g)=QW(g,g)` from CCM25 restriction-definition,
  common test, support containment, finite-prime stabilization, and no spectral
  input.
- Updated `README.md`, `docs/audits/accepted-source-certification-audit.md`,
  `docs/audits/accepted-source-theorem-upgrade-ledger.md`,
  `docs/audits/README.md`, and `AGENTS.md` to point to the two new packets.
- No row was marked accepted-source. The new files are review packets, not
  external acceptance.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Started the accepted-source theorem upgrade phase without touching Lean.
- Added `docs/audits/accepted-source-theorem-upgrade-ledger.md`.
- The ledger states row-level theorem candidates, source anchors, current
  evidence, and upgrade blockers for CCM24, CCM25, CC20, trace-scale,
  sign/defect, restricted-to-full, final sign, CC20 exit, and RH definition
  rows.
- It explicitly does not mark any row as accepted-source. Promotion still
  requires exact theorem statements, exact hypotheses, object/test/sign bridges,
  limit order, and an external referee, accepted proof, or Lean theorem.
- Added `docs/audits/trace-scale-source-term-ledger.md` as the first S2-B1
  accepted-source review packet.
- The S2-B1 packet maps possible positive-trace source scalars to route classes:
  `QW_lambda`, rank, pole, endpoint-strip `Cdef`, or the obstruction
  `BulkScaleTerm_(S,I,lambda,g)`.
- Updated `README.md`, `docs/audits/accepted-source-certification-audit.md`,
  and `docs/audits/README.md` to point to the new accepted-source upgrade
  files.
- Updated `AGENTS.md` with the rule that accepted-source status cannot be
  self-assigned from project proof packages.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added local second external-opinion record:
  `external-opinions/002-divergent-bulk-spectral-and-semilocal-review.md`.
- Added public audit `docs/audits/second-external-opinion-audit.md`.
- The audit maps the second opinion into four public review rows:
  S2-B1 divergent bulk / trace-scale incompatibility, S2-B2 spectral
  pollution and domain mismatch, S2-B3 even-sector spectral assumption, and
  S2-B4 semilocal fourth defect plus `S(g)` uniformity.
- The current judgment is that S2-B1 is the strongest direct attack: a
  source-owned `BulkScaleTerm_(S,I,lambda,g)` outside `QW_lambda`, rank, pole,
  and endpoint-strip `Cdef` would stop the route at the positive-trace
  read-off.
- The spectral-pollution and even-sector objections attack the CCM25 spectral
  program. They hit the current route only if a route row imports finite
  operator spectral convergence, determinant convergence, numerical
  eigenvalue convergence, or an even-sector minimum-eigenvector assumption.
- Updated `README.md` with a "Self-Review After The Second External Opinion"
  section and new falsification tests for spectral shortcut import and
  even-sector assumption import.
- Updated `docs/audits/README.md` to index the new audit.
- Updated `AGENTS.md` with the second-opinion gotchas: divergent bulk is
  source-critical, and spectral/even-sector claims must stay non-importable
  for the current route.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Self-reviewed the public README after the first external-review blocker
  milestone.
- Updated `README.md` to make the remaining attack surface more explicit:
  `closed` now means local proof-package/audit coverage only, not
  accepted-source, referee, or Lean certification.
- Expanded the hard reviewer questions from B1/B3 only to include B4
  dynamic `S(g)`, CCM25 finite-prime pointwise normalization, and the final
  CCM25-to-CC20 sign bridge.
- Added a "Self-Review After The First External Opinion" section that maps
  B1-B4 to local answers and strongest remaining attacks.
- Added a "Falsification Tests For Reviewers" section that names concrete
  ways to reject the route and points each test to the first file to inspect.
- Ran public documentation hygiene checks: `git diff --check`,
  unfinished-marker scan, ASCII scan, private-path scan, and Lean-file diff
  scan. Checks passed except for normal LF/CRLF warnings.
- Committed and pushed the README update:
  `ba5209c8d2774c77059afefe6ee5a16e567a2ae8`
  (`Clarify README review attack surface`).
- Local GPG verification passed with EDDSA key
  `828A1CFCEC8286BD8D671DF6F84F18CD20BE8255`.
- GitHub commit verification returned `verified=true` and `reason=valid`.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Committed and pushed the first external-review blocker milestone:
  `efdc7a0d03ac04e080e911ef196392a7b62c1f63`
  (`Address first external review blockers`).
- The milestone covers B1 trace-scale compatibility, B2 Sonin-projection
  repair rejection, B3 semilocal fourth-defect ledger, and B4 dynamic `S(g)`
  quantifier audit.
- Staged hygiene passed before commit: no `AGENTS.md`, `MEMORY.md`,
  `external-opinions/`, private workflow files, private paths, or Lean files were
  staged.
- Local GPG verification passed with EDDSA key
  `828A1CFCEC8286BD8D671DF6F84F18CD20BE8255`.
- GitHub commit verification returned `verified=true` and `reason=valid`.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/audits/s-local-global-quantifier-audit.md`.
- This closes B4 from the first external opinion at route-evidence level.
- The audit records the safe quantifier order:
  `forall g`, then choose finite `S(g)`, then choose the fixed-test
  `lambda0(g,S,I,J)`, then return the global scalar `QW(g,g) >= 0`.
- It records that the route does not need one finite `S` for all tests or
  constants uniform over the whole test-function space, because the route uses
  a pointwise forall-g proof rather than a density, closure, or
  uniform-convergence argument.
- It also records what would reopen B4: an S-dependent final scalar, omitted or
  duplicated finite-prime atoms, a uniform-in-g requirement in CC20 Proposition
  C.1, or a final sign bridge applied to a different test.
- Updated README and the audit index to point reviewers to the B4 audit.
- No commit or push was made yet under the "larger milestones only" rule.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/audits/semilocal-fourth-defect-ledger.md`.
- This closes B3 from the first external opinion at project proof-package
  level.
- The ledger maps every possible semilocal cross-term hiding place through the
  Rows 1-7 sign/defect chain: source formula, post-`Q` image, fixed-S
  transport, projection/model mismatch, no-strip class, endpoint-strip class,
  and Row 7 equality.
- The current judgment is that any surviving fourth positive defect would have
  to be a source-owned term outside rank, pole, and endpoint-strip `Cdef`,
  which would reopen the route. No such term is present in current route
  evidence.
- Updated README and the audit index to point reviewers to the B3 ledger.
- No commit or push was made under the "larger milestones only" rule.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/audits/sonin-projection-repair-rejection-audit.md`.
- This closes B2 from the first external opinion as a rejected repair path:
  the route does not replace the positive trace
  `Tr((P_hat P theta_S(g))^*(P_hat P theta_S(g)))` by a Sonin-projection trace
  such as `Tr(S_lambda theta_S(F_g))`.
- The audit records that any future Sonin-projection replacement must prove a
  new trace-scale compatibility theorem, including positivity after
  normalization, same-scale read-off, and a nontrivial limit.
- Updated README and the audit index to list the rejected repair path.
- No commit or push was made under the "larger milestones only" rule.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/proofs/trace-scale-compatibility-proof-package.md`.
- This closes B1 trace-scale compatibility at project proof-package level.
- The package proves, within route-evidence strength, that ordinary positive
  trace, support-square trace, no-defect source trace, and CCM25 `QW_lambda`
  use the same finite-lambda read-off scale, with all terms outside
  `QW_lambda` named as rank, pole, or endpoint-strip `Cdef`.
- It explicitly leaves accepted-source certification, external referee
  certification, Lean theorem status, and RH proof status open.
- Updated README, the B1 audit, the B1 discharge attempt, and the audit index
  to record B1 as project proof-package coverage instead of an open blocker.
- No commit or push was made under the "larger milestones only" rule.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/audits/trace-scale-compatibility-discharge-attempt.md`.
- The audit checks whether existing trace-legality, fixed-S no-defect read-off,
  no-hidden-defect, and restricted-to-full packages already discharge B1.
- Result: B1 is not closed. Existing packages partially cover ordinary trace
  definition, support-square equality order, and `QW_lambda` read-off. The
  remaining focused subtargets are `SourceConventionConversionLedger` and
  `NoMissingTraceScaleBulk`.
- Updated the B1 audit and audit index to link the discharge attempt.
- No commit or push was made under the new "larger milestones only" rule.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/proofs/trace-scale-compatibility-theorem-contract.md`.
- This advances B1 from an audit into a theorem-contract target without
  claiming discharge.
- The contract requires same-scalar equality from ordinary positive trace to
  support-square trace, a source-convention conversion ledger, no-defect trace
  equality with CCM25 `QW_lambda`, a no-missing-bulk theorem, and limit
  compatibility before positive trace can feed `QW_lambda`.
- Updated `README.md`, `docs/audits/README.md`, and the B1 audit to point to
  the theorem contract.
- Per Peter's instruction, this was not committed or pushed because it is not
  yet a large milestone.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Started the B1 trace-scale compatibility attack before any Lean work.
- Added `docs/audits/trace-scale-compatibility-audit.md` as the first public
  blocker audit derived from the local external opinion record.
- The audit records that the repository has trace-legality and read-off
  packages, but does not yet discharge the stronger same-scale theorem tying
  ordinary positive trace, support-square trace, no-defect source trace, and
  CCM25 `QW_lambda` to one finite-lambda scalar.
- Updated `README.md` so external reviewers see trace-scale compatibility as
  the first open review row before the no-hidden-fourth-defect row.
- Updated `docs/audits/README.md` to index the new audit.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added local ignored directory `external-opinions/`.
- Added `external-opinions/001-trace-scale-and-defect-review.md` as the first external
  opinion record.
- The note records four blockers from the latest external critique:
  trace-scale compatibility, Sonin-projection trivialization as a blocked
  repair path, semilocal fourth-defect risk, and dynamic `S(g)` quantifier
  risk.
- The planned attack order is now: B1 trace-scale compatibility first, then
  B3 no-fourth-defect term ledger, then B4 `S(g)` quantifier/global-object
  audit, then final sign and external accepted-source review.
- Updated `.gitignore` so `external-opinions/` stays local and is not published.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Rewrote `README.md` as the single external-review entry point.
- The README now contains the status boundary, evidence classes, complete proof
  spine, step-by-step route, non-importable shortcuts, row-by-row review
  checklist, Lean status, and verification commands.
- It is written so an external reviewer can judge the project from the README
  first and then inspect cited audit/proof-package files for the rows they
  want to accept or reject.
- The README keeps the hard boundary: source-conditional route evidence only;
  no accepted-source certificate, completed Lean proof, or public proof of RH.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/audits/pre-lean-completion-audit.md`.
- This is the local non-Lean completion gate for the current route.
- It records that all local pre-Lean proof-package rows are written and
  indexed, including source objects, CCM24, CCM25, CC20 trace legality,
  Rows 1-7 sign/defect, restricted-to-full, final sign, and RH definition
  bridge.
- It also records the hard boundary: no source-interface row has become an
  accepted-source theorem, external referee-certified result, or Lean theorem
  with audited axioms.
- Updated `README.md`, `docs/audits/README.md`, and `AGENTS.md` to point to
  the audit and to keep Lean closed until Peter explicitly reopens it.
- No Lean files were edited and no Lean build was run.

2026-06-28

- Added `docs/audits/accepted-source-certification-audit.md`.
- This is the external-review checklist for upgrading the current
  proof-package matrix to accepted-source or Lean theorem strength.
- It records that the route-evidence chain is complete, the hostile
  sign/defect criticism is answered at project proof-package strength, and
  CCM25 spectral convergence is not imported.
- It also records the boundary: no source-interface row is yet accepted-source
  certified or discharged as a Lean theorem.
- Updated `docs/audits/README.md` and
  `docs/audits/source-import-legitimacy-audit.md` to index the audit.
- Rewrote `README.md` as an external-review entry point for the latest route:
  source-conditional status first, then the full proof spine, sign/defect
  discharge chain, restricted-to-full bridge, final sign bridge, RH definition
  bridge, and row-by-row review targets.
- Updated `AGENTS.md` to require reading the accepted-source certification
  audit before sending the route to outside reviewers.

2026-06-28

- Added `docs/proofs/cc20-source-remainder-rows1-2-referee-discharge.md`.
- This is a mathematics-only, referee-facing project proof package for Rows 1
  and 2 of the sign/defect bridge.
- It fixes the CC20 source obstruction object and sign orientation:
  `D=L-W_infty`, `E=S-W_infty`, hence `W_infty=L-D` and `W_infty=S-E`.
- It fixes the post-`Q` image handed to Row 3: `D circ Q` as the control
  target and `E circ Q` as the displayed `Q epsilon` formula with bulk term,
  moving lower-boundary term, fixed upper-boundary term, and series tail.
- Updated `docs/proofs/sonin-prolate-defect-referee-discharge.md` so the
  sign/defect bridge now reads as Rows 1-7 closed at project proof-package
  level.
- Updated `docs/audits/README.md`,
  `docs/audits/sign-defect-blocker-audit.md`,
  `docs/audits/source-import-legitimacy-audit.md`,
  `docs/audits/sonin-prolate-defect-discharge-ledger.md`, and `AGENTS.MD` to
  record the corrected status.
- Accepted-source certification, external review, Lean proof status, and
  unconditional RH proof status remain open.
- No Lean files were edited.

2026-06-28

- Added `docs/proofs/sonin-prolate-defect-referee-discharge.md`.
- This is a mathematics-only, referee-facing discharge package for the
  sign/defect bridge.
- It confirms that Rows 3 through 7 are already closed as one project proof
  chain: Row 3 fixed-S post-`Q` transport, Row 4 two-class split, Row 5
  rank/pole no-strip identification, Row 6 endpoint-strip `Cdef` domination,
  and Row 7 no-hidden-positive-defect equality.
- It proves the finite-lambda consequence
  `QW_lambda(g,g) >= -C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)` after rank and
  pole ledgers vanish, without claiming finite-lambda positivity of
  `QW_lambda`.
- It explicitly leaves Rows 1-2 source-orientation discharge, accepted-source
  certification, external review, Lean proof status, and unconditional RH proof
  status open.
- Updated `docs/audits/README.md`,
  `docs/audits/sign-defect-blocker-audit.md`, and
  `docs/audits/source-import-legitimacy-audit.md` to index the new package and
  record the corrected status: Rows 3-7 are closed as a project proof chain,
  while Rows 1-2 source orientation and accepted-source certification remain
  open.
- No Lean files were edited.

2026-06-28

- Added `docs/proofs/source-conditional-rh-route-closure-proof-package.md`.
- This composes the current route-evidence packages into
  `SourceConditionalRHRouteClosure`.
- The composition chain is: Row 7 restricted lower bound, endpoint-strip
  `Cdef` exhaustion, restricted-to-full fixed-test equality, final
  CCM25-to-CC20 sign bridge, CC20 Proposition C.1 finite-vanishing exit, and
  RH definition bridge to Mathlib's `_root_.RiemannHypothesis`.
- The package states route-evidence closure only. It explicitly leaves
  accepted source-import status, Lean proof status, external certification,
  and unconditional public RH proof status open.
- Updated the audit index, formal-gate spine audit, source-interface
  completion audit, source-import audit, AGENTS rule set, and project memory.
- No Lean files were edited.

2026-06-28

- Added `docs/proofs/final-sign-bridge-proof-package.md`.
- This advances the final CCM25-to-CC20 sign bridge:
  `FinalSignBridgeContract`.
- The proof package closes the bridge at route-evidence level by proving
  `QW(g,g)=Psi(F_g)`, the source `Psi` sign expansion, the CC20 local Weil sum
  sign, `QW(g,g)=-sum_v W_v(F_g)`, and the inequality direction
  `QW(g,g)>=0 -> sum_v W_v(F_g)<=0`.
- Added `docs/proofs/rh-definition-bridge-proof-package.md`.
- This advances the RH definition bridge:
  `RHDefinitionBridgeContract`.
- The proof package closes `CC20SourceRH -> _root_.RiemannHypothesis` at
  route-evidence level by unpacking Mathlib's `riemannZeta s = 0`, negative
  even exclusion, `s != 1`, and `s.re=1/2` predicate.
- These packages explicitly do not prove accepted source-import legitimacy,
  Lean theorem status, CC20 Proposition C.1 itself, or RH.
- Updated the audit index, formal-gate spine audit, source-interface
  completion audit, source-import audit, AGENTS rule set, and project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/proofs/restricted-to-full-qw-bridge-proof-package.md`.
- This advances the fixed-test restricted-to-full gate:
  `RestrictedToFullQWBridgeContract`.
- The proof package closes the bridge at route-evidence level by fixing `g`
  and `F_g`, choosing a fixed-test `lambda0`, stabilizing visible prime-power
  support, and using CCM25's restriction definition to get eventual scalar
  equality `QW_lambda(g,g)=QW(g,g)`.
- It explicitly avoids finite-operator spectral convergence, determinant
  convergence, zero convergence, and RH-equivalent convergence claims.
- It proves transfer from the Row 7 finite-lambda lower bound to
  `QW(g,g)>=0` at route-evidence level, but it does not prove accepted
  source-import legitimacy, Lean theorem status, the CC20 finite-vanishing
  final exit, or RH.
- Updated the audit index, restricted-to-full contracts and source-readiness
  audit, source-import audit, sign/defect audit, core defect ledger, fast-route
  audit, formal-gate spine audit, AGENTS rule set, and project memory.
- No Lean files were edited.

2026-06-27

- Added
  `docs/proofs/no-hidden-positive-defect-outside-cdef-theorem-contract.md`.
- Added
  `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md`.
- This advances Row 7 of the sign/defect discharge ledger:
  `NoHiddenPositiveDefectOutsideCdef`.
- The proof package closes Row 7 at route-evidence level by composing source
  read-off remainder ownership, Row 3 transported source remainder, Row 4
  no-strip/endpoint-strip exhaustive split, Row 5 rank/pole no-strip
  identification, and Row 6 endpoint-strip `Cdef` domination.
- It proves the finite-lambda consequence
  `QW_lambda(g,g) >= -C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)` after ledger
  killing, but it does not claim direct finite-lambda positivity.
- It explicitly does not prove accepted source-import legitimacy, Lean theorem
  status, restricted-to-full `QW_lambda -> QW`, full Weil positivity, or RH.
- Updated the sign/defect ledger, sign/defect blocker audit, source-import
  audit, audit index, Sonin/prolate defect theorem contract, AGENTS rule set,
  and project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md`.
- Added `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md`.
- This advances Row 6 of the sign/defect discharge ledger:
  `SourceEndpointStripRemainderCdefDomination`.
- The proof package closes Row 6 at route-evidence level by matching
  endpoint-strip source-remainder terms to route `Cdef` summands, proving the
  finite-strip trace-norm domination, and recording fixed-test `Cdef`
  exhaustion.
- It explicitly does not prove Row 7
  `NoHiddenPositiveDefectOutsideCdef`, the final positive-trace read-off
  equality, accepted source import status, Lean theorem status, or RH.
- Updated the sign/defect ledger, sign/defect blocker audit, source-import
  audit, audit index, Sonin/prolate defect theorem contract, AGENTS rule set,
  and project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/proofs/source-rank-pole-ledger-identification-theorem-contract.md`.
- Added `docs/proofs/source-rank-pole-ledger-identification-proof-package.md`.
- This advances Row 5 of the sign/defect discharge ledger:
  `SourceRankPoleLedgerIdentification`.
- The proof package closes Row 5 at route-evidence level by using the Row 4
  no-strip split, Battle 1 quotient-channel identification, rank-repair
  zero-mode normal form, CCM25 pole separation, and the no-defect
  no-extra-channel read-off.
- It identifies no-strip channels as `Rank_(S,I)(g)` or
  `PoleJetExtra_(S,I)(g)` and records that triple vanishing kills those ledgers
  only after identification.
- It explicitly does not prove endpoint-strip `Cdef` domination,
  no-hidden-positive-defect equality, sign/defect discharge, or RH.
- Updated the sign/defect ledger, sign/defect blocker audit, source-import
  audit, audit index, Sonin/prolate defect theorem contract, AGENTS rule set,
  and project memory.
- No Lean files were edited.

2026-06-27

- Added
  `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-theorem-contract.md`.
- Added
  `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md`.
- This advances Row 4 of the sign/defect discharge ledger:
  `FixedSProjectionDefectNormalFormForSourceRemainder`.
- The proof package closes Row 4 at route-evidence level by tying the Row 3
  object `TransportedCC20PostQRemainder` to the existing fixed-S projection
  calculus: common `V_S=M_S U_S` coordinate, no-strip versus projection-order
  split, listed projection commutators, endpoint-strip shifted-kernel normal
  form, and post-`Q` boundary terms with a strip factor before evaluation.
- It explicitly does not prove rank/pole ledger identification, endpoint-strip
  `Cdef` domination, no-hidden-positive-defect equality, sign/defect discharge,
  or RH.
- Updated the sign/defect ledger, sign/defect blocker audit, source-import
  audit, audit index, Sonin/prolate defect theorem contract, fast-route audit,
  AGENTS rule set, and project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/audits/cc20-post-q-series-tail-source-decision-audit.md`.
- This audit classifies the third Row 3 subcontract,
  `PostQSeriesTailBoundedComparison`, as project-proof-required rather than
  source-import-discharged.
- Source result: CC20 gives the post-`Q` infinite series, bulk and boundary
  majorants, and a source-side uniform tail estimate; CCM24 gives bounded
  comparison. Neither source gives fixed-S graph or trace-norm preservation of
  that tail.
- Added
  `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-theorem-contract.md`.
- Added
  `docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md`.
- The proof package closes `FixedSPostQSeriesTailBoundedComparison` at
  route-evidence level using termwise fixed-S transport, a named fixed-S
  tail graph norm, CC20 summable majorants, and fixed bounded-comparison
  constants before the `N -> infinity` tail limit.
- Added `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md`.
- This combined Row 3 package closes
  `CC20PostQRemainderFixedSSoninTransport` at route-evidence level by combining
  bulk transport, boundary transport, and series-tail bounded comparison.
- It explicitly does not prove projection-defect normal form, rank/pole/Cdef
  classification, no-hidden-defect equality, sign/defect discharge, or RH.
- Updated the Row 3 contract, tail contract, sign/defect blocker audit,
  source-import audit, discharge ledger, fast-route audit, audit index, and
  project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/audits/cc20-post-q-boundary-evaluation-source-decision-audit.md`.
- This audit classifies the second Row 3 subcontract,
  `PostQBoundaryEvaluationTransport`, as project-proof-required rather than
  source-import-discharged.
- Source result: CC20 gives the endpoint terms, their domain-repair origin,
  and scalar boundary estimates; CCM24 gives fixed-S model/window/Sonin
  transport. Neither source gives fixed-S endpoint-functional transport.
- Added `docs/proofs/fixed-s-post-q-boundary-functional-transfer-theorem-contract.md`.
- Added `docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md`.
- The proof package closes `FixedSPostQBoundaryFunctionalTransfer` at
  route-evidence level by combining source endpoint ownership, log endpoint
  translation, finite-strip Sobolev trace continuity, fixed finite-S graph
  boundedness, and the common `V_S=M_S U_S` coordinate.
- It explicitly does not prove series-tail bounded comparison, full Row 3
  transport, rank/pole/Cdef classification, no-hidden-defect equality, or RH.
- Updated the boundary contract, sign/defect blocker audit, source-import
  audit, discharge ledger, fast-route audit, audit index, and project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md`.
- This is the route-evidence proof package for
  `FixedSPostQBulkGraphTransfer`, the project bridge for the first Row 3
  subcontract.
- It proves at project level: source-to-log graph translation, fixed finite-S
  Euler graph boundedness, fixed-S bulk representative, and source-bulk
  equality before Row 4.
- It explicitly does not prove boundary evaluation transport, series-tail
  bounded comparison, endpoint-strip `Cdef` domination, full Row 3 transport,
  or the sign/defect bridge.
- Updated the theorem contract, derivative-domain source-decision audit,
  sign/defect blocker audit, source-import audit, discharge ledger,
  source-readiness audit, fast-route audit, audit index, AGENTS rule set, and
  project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md`.
- This is the project-proof target for discharging the first Row 3 subcontract,
  `PostQDerivativeDomainCompatibility`.
- It is intentionally narrow: it covers only the CC20 post-`Q` bulk term and
  aims to prove fixed-S graph-domain transport plus source-bulk equality before
  Row 4 classification.
- It does not cover boundary evaluation transport, series-tail bounded
  comparison, rank/pole/Cdef classification, or no-hidden-defect equality.
- Linked the contract into the derivative-domain source-decision audit,
  derivative-domain theorem contract, sign/defect blocker audit, source-import
  audit, discharge ledger, audit index, fast-route audit, AGENTS rule set, and
  project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/audits/cc20-post-q-derivative-domain-source-decision-audit.md`.
- This audit classifies the first Row 3 subcontract,
  `PostQDerivativeDomainCompatibility`, as project-proof-required rather than
  source-import-discharged.
- Source result: CC20 gives the archimedean post-`Q` bulk formula, domain
  warning, and derivative estimates; CCM24 gives fixed-S Hilbert/Sonin
  comparison. Neither source gives the fixed-S graph-domain transport theorem.
- Project route evidence exists in the graph/Cdef packages:
  fixed finite-S multipliers are graph-bounded, finite shifts commute with
  logarithmic `D_u`, and `Q` raises only fixed graph order. This supports a
  project proof route but does not discharge the source import.
- New next bridge target:
  `FixedSPostQBulkGraphTransfer(S,I,lambda,g,F_g,n)`.
- Linked the audit into the sign/defect blocker audit, source-import audit,
  source-readiness audit, derivative/domain theorem contract, fast-route audit,
  audit index, AGENTS rule set, and project memory.
- No Lean files were edited.

2026-06-27

- Added
  `docs/proofs/cc20-post-q-series-tail-bounded-comparison-theorem-contract.md`.
- This is the third Row 3 subcontract under
  `CC20PostQRemainderFixedSSoninTransport`.
- It targets the infinite-series tail in CC20 `Q epsilon`.
- Key source evidence: `weil-compo.tex:2168-2211` bounds the bulk contribution
  `A_n(rho)`; `weil-compo.tex:2215-2240` bounds the boundary contribution
  `B_n(rho)`; `weil-compo.tex:2243-2250` gives a uniform source-side tail
  estimate for `rho in [1,2]`.
- Current mathematical status: CC20 source-side scalar convergence is located,
  but fixed-S graph/trace-norm tail preservation is not proved or
  source-import discharged.
- Linked the contract into the Row 3 contract, CCM24 obstruction audit, term
  map, sign/defect ledger, sign/defect blocker audit, source-import audit,
  source-readiness audit, fast-route search audit, audit index, AGENTS rule
  set, and project memory.
- No Lean files were edited.

2026-06-27

- Added
  `docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md`.
- This is the second Row 3 subcontract under
  `CC20PostQRemainderFixedSSoninTransport`.
- It targets the two CC20 post-`Q` endpoint terms:
  `rho^(-1/2)(D_u xi_n)(rho^-1) zeta_n(1)` and
  `-rho^(1/2) xi_n(1)(D_u zeta_n)(rho)`.
- Key source evidence: `weil-compo.tex:1260-1270` says boundary terms appear
  because the formal `D_u` identity fails for `xi_n,zeta_n`;
  `weil-compo.tex:1308-1333` derives the endpoint terms by integration by
  parts; `weil-compo.tex:2215-2236` defines and bounds `B_n(rho)`.
- Current mathematical status: boundary-evaluation transport is now stated as
  a precise theorem target, but is not proved or source-import discharged.
- Linked the contract into the Row 3 contract, CCM24 obstruction audit, term
  map, sign/defect ledger, sign/defect blocker audit, source-import audit,
  source-readiness audit, fast-route search audit, audit index, AGENTS rule
  set, and project memory.
- No Lean files were edited.

2026-06-27

- Added
  `docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md`.
- This is the first Row 3 subcontract under
  `CC20PostQRemainderFixedSSoninTransport`.
- It targets the CC20 post-`Q` bulk term containing
  `D_u xi_n` and `D_u zeta_n`.
- Key source evidence: `weil-compo.tex:1260-1264` says the formal `D_u`
  identity cannot be applied directly because `xi_n,zeta_n` are not in the
  domain of `D_u`; `weil-compo.tex:1267-1270` and `1338-1346` give the repaired
  bulk-plus-boundary formula; `weil-compo.tex:2171-2207` gives source bounds
  for the derivative factors.
- Current mathematical status: derivative/domain compatibility is now stated
  as a precise theorem target, but is not proved or source-import discharged.
- Linked the contract into the Row 3 contract, CCM24 obstruction audit, term
  map, sign/defect ledger, sign/defect blocker audit, source-import audit,
  source-readiness audit, fast-route search audit, audit index, AGENTS rule
  set, and project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md`.
- This fast Row 3 audit rereads CCM24 around the fixed-S canonical model,
  support/Fourier transport, bounded comparison, Sonin-space isomorphism, and
  the semilocal Hermite warning.
- Positive result: CCM24 supports the common fixed-S model/window/Sonin
  framework needed for Row 3.
- Negative result: `mainc2m24fine.tex:846-852` blocks the naive shortcut that
  semilocal Hermite, derivative, multiplication, and boundary structures
  commute with the archimedean ones under `eta_S`.
- Row 3 is now split into three sharper open subcontracts:
  `PostQDerivativeDomainCompatibility`,
  `PostQBoundaryEvaluationTransport`, and
  `PostQSeriesTailBoundedComparison`.
- Linked the audit into the Row 3 contract, term map, sign/defect ledger,
  sign/defect blocker audit, source-import audit, source-readiness audit,
  fast-route search audit, audit index, AGENTS rule set, and project memory.
- No Lean files were edited.

2026-06-27

- Added `docs/audits/cc20-post-q-remainder-term-map.md`.
- This is the first item-level Row 3 audit. It rereads CC20 source lines for
  the vanishing operator `Q`, `D=L-W_infty`, `W_infty=S-E`, and the
  `Q epsilon` formula.
- The source formula splits the post-`Q` `E` remainder into four visible
  classes: a bulk integral term, a moving lower-boundary term, a fixed
  upper-boundary term, and the infinite series tail. No escaped fourth class
  appears in the displayed formula, but no fixed-S transport theorem is proved.
- Linked the term map into the Row 3 theorem contract, sign/defect discharge
  ledger, sign/defect blocker audit, source-import legitimacy audit,
  fast-route search audit, and audit index.
- Current mathematical status: Row 3 is now attackable item by item through
  `CC20PostQTermwiseFixedSTransport` and
  `CC20PostQSeriesTailTransport`, but remains open.
- No Lean files were edited.

2026-06-27

- Added `docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md`.
- This is the Row 3 theorem contract selected by the fast-route search. It
  states `CC20PostQRemainderFixedSSoninTransport(S,I,lambda,g,F_g)`:
  the CC20 `D circ Q` / `E circ Q` bulk and boundary pieces must be
  transported into the same fixed-S CCM24/Sonin/window coordinate as the
  positive trace and restricted `QW_lambda` before Rows 4-6 may classify them
  by projection-defect normal form, rank/pole ledgers, or endpoint-strip
  `Cdef`.
- Linked the Row 3 contract into the audit index, sign/defect blocker audit,
  source-import legitimacy audit, formal-gate spine audit, source-interface
  discharge audits, Lean-readiness note, source-object interface plan, risk
  audit, workplan, and AGENTS rule set.
- This does not discharge sign/defect. It makes the next fast mathematical
  check sharper: verify whether the CC20 post-`Q` formula exposes every bulk
  and boundary term in a form transportable by the CCM24 fixed-window Sonin
  comparison.
- No Lean files were edited.

2026-06-27

- Added `docs/audits/fast-route-search-2026-06-27.md`.
- This switches the current mathematics-first work into a bounded rapid
  route-search sprint for the two urgent blockers: sign/defect and source
  import legitimacy.
- The fast-search verdict is:
  1. best sign/defect attack is Row 3,
     `CC20PostQRemainderFixedSSoninTransport`, transporting the CC20
     `D circ Q` / `E circ Q` bulk and boundary pieces through the same fixed-S
     CCM24 Sonin window before any projection-defect normal form or `Cdef`
     claim;
  2. best source-import attack is the fixed-test restricted-to-full bridge,
     using the CCM25 restriction definition plus common-test/window and
     finite-prime support equality, not spectral convergence;
  3. CvS finite real-zero theorems, determinant convergence, and generic
     prolate concentration are rejected for this sprint because they do not
     directly discharge the hostile positive-trace-to-Weil read-off objection.
- Linked the fast-search audit into `docs/audits/README.md`.
- No Lean files were edited.

2026-06-27

- Temporarily downloaded the official arXiv source package for CC20
  `2006.13771` outside the repository and reread `weil-compo.tex` source lines
  for the sign/defect blocker.
- Added `docs/proofs/cc20-source-remainder-orientation-theorem-contract.md`.
- This mathematics-only contract advances Rows 1 and 2 of
  `docs/audits/sonin-prolate-defect-discharge-ledger.md`: it fixes the source
  orientation `W_infty=L-D` from the `delta` trace-remainder and
  `W_infty=S-E` from the Sonin `epsilon` remainder, and records that `D circ Q`
  / `E circ Q` are the objects that must be controlled after the finite
  vanishing operator `Q`.
- Linked the contract into the audit index, sign/defect blocker audit,
  source-import legitimacy audit, source-interface discharge audits, core
  defect ledger, formal-gate spine audit, Lean-readiness note, source-object
  interface plan, risk audit, workplan, and AGENTS rule set.
- Current mathematical status: Row 1/2 source orientation is now pinned by a
  theorem contract, but the fixed-S transport of the post-`Q` source bulk and
  boundary pieces into rank, pole, or endpoint-strip `Cdef` remains open.
- No Lean files were edited.

2026-06-27

- Added `docs/audits/sonin-prolate-defect-discharge-ledger.md`.
- This mathematics-only ledger advances the sign/defect hard blocker from one
  large target, `SoninProlateDefectEqualsEndpointStripCdef`, into seven
  discharge rows: CC20 source remainder object and orientation, the source
  remainder after `Q`, fixed-S Sonin transport, fixed-S projection-defect
  normal form, rank/pole ledger identification, endpoint-strip `Cdef`
  domination, and the final no-hidden-positive-defect equality.
- Linked the ledger into the audit index, sign/defect blocker audit,
  source-import legitimacy audit, formal-gate spine audit,
  source-interface discharge audits, core defect ledger, Lean-readiness note,
  source-object interface plan, risk audit, workplan, and AGENTS rule set.
- Current mathematical status: Rows 4-6 have route-evidence packages, but Rows
  1-3 remain source-risk rows and Row 7 remains the hostile-objection decision
  point. The sign/defect bridge is not discharged.
- No Lean files were edited.

2026-06-27

- Added `docs/proofs/restricted-to-full-qw-bridge-theorem-contract.md`.
- This mathematics-only contract advances the restricted-to-full QW gate from
  a scalar target to a concrete composition bridge: CCM25 restriction
  definition plus common-test, fixed tuple/window, and finite-prime support
  contracts imply eventual scalar `QW_lambda(g,g)=QW(g,g)`.
- Linked the bridge into the audit index, formal-gate spine audit,
  source-import legitimacy audit, source-interface discharge audits,
  restricted-to-full source-readiness audit, sign/defect blocker audit,
  source-object replacement audit, Lean-readiness note, source-object
  interface plan, risk audit, workplan, and AGENTS rule set.
- This reduces the source-import blocker by isolating the missing bridge, but
  it does not discharge the bridge. The sign/defect blocker remains open at
  `SoninProlateDefectEqualsEndpointStripCdef`.
- No Lean files were edited.

2026-06-27

- Created this repository as the dedicated working area for the Connes-Weil RH
  proof manuscript and future Lean formalization.
- Copied the current internal, source-conditional manuscript draft into:
  `docs/manuscripts/connes-weil-rh-proof-draft.md`.
- Established the repository boundary:
  - this repository holds the formal manuscript and future Lean work;
  - the control/archive repository keeps route history, experiments, and
    bus-level memory.
- Current manuscript status:
  `v0.1 referee-readable source-conditional manuscript`.
- Current explicit boundary:
  the manuscript is not a public proof certificate, journal acceptance, Clay
  acceptance, or Lean formalization.

2026-06-27

- Upgraded `docs/manuscripts/connes-weil-rh-proof-draft.md` from an internal
  completed draft to a v0.1 referee-readable source-conditional manuscript.
- Added source-line audit entries based on official arXiv source files:
  CCM24 `mainc2m24fine.tex`, CCM25 `mc2arXiv.tex`, and CC20
  `weil-compo.tex`.
- Expanded Theorem 1 into five referee-checkable steps: positivity,
  support-square transport, trace legality, CCM read-off, and ledger
  collection.
- Added appendices for operator/domain conventions, trace-class and cyclicity
  ledger, source normalization and sign audit, and the finite-set side
  condition.
- Kept the boundary explicit: this is not a public proof certificate, journal
  acceptance, Clay acceptance, or Lean formalization.

2026-06-27

- Hardened Theorem 1 against strict referee attacks.
- Added admissible-window conditions tying `S`, `I`, `lambda`, and `g`
  together: `supp(g) subset I subset [lambda^(-1),lambda]`, and `S` must
  contain every finite prime visible to `F_g=g^* * g`.
- Added the positive-trace-class gate: Lemma 2 now states
  `P_hat P theta_S(g)` is Hilbert-Schmidt before Theorem 1 uses
  `Tr(A^*A) >= 0`.
- Clarified that commutators with `M_S` are taken in one common scattering
  coordinate, not between different Hilbert spaces.
- Replaced the compressed "read through CCM" language in Theorem 1 with an
  explicit no-defect source-trace read-off chain.
- Added a quotient-ledger check: only `hat g(0)`, `hat g(+i/2)`, and
  `hat g(-i/2)` occur as no-strip finite-dimensional channels.
- Updated the hostile audit and completion audit to include these Theorem 1
  hardening gates.

2026-06-27

- Prepared the repository for the Lean-start phase without opening a Lake
  project yet.
- Added `docs/audits/source-reread-v0.2.md`, based on official arXiv source
  packages for CCM24 `mainc2m24fine.tex`, CCM25 `mc2arXiv.tex`, and CC20
  `weil-compo.tex`.
- The source reread found no immediate Lean-blocking citation mismatch in the
  critical ranges used for the fixed-S model, support/Fourier transport,
  `QW_lambda`, trace-class legality, signs, Mellin convention, and RH exit.
- Added `formalization/lean-readiness.md` with the first Lean scaffold plan:
  declare explicit CCM24/CCM25/CC20 source theorem interfaces first, then prove
  the project route composition from those interfaces.
- Updated repository docs so the next Lean task starts from the readiness map
  and source reread audit instead of starting with broad analytic plumbing.

2026-06-27

- Copied existing Lean/Lake work from `C:\Projects\RiemannHypothesis` into this
  repository.
- Copied only the root module import closure and Lake project files:
  `RiemannHypothesis.lean`, `RiemannHypothesis/`, `lakefile.toml`,
  `lake-manifest.json`, and `lean-toolchain`.
- Did not copy `.lake`, `.git`, private memory files, large manuscript/control
  notes, or the unimported `RiemannHypothesis/Search/IntuitionFunnel.lean`
  scratch file, which contains `sorry`.
- Verified that copied root imports have no missing local `RiemannHypothesis.*`
  files.
- Found explicit `axiom` declarations in
  `RiemannHypothesis/Toy/RobinNicolasLandauPrimitive.lean`; these must be
  treated as theorem-source contracts or unfinished boundaries, not completed
  proof.
- WSL has Lean/Lake 4.30.0 available and matches the copied `lean-toolchain`.
- `lake build` was not verified: initial dependency checkout timed out, a stale
  Mathlib checkout lock was cleared, then dependency update/cache retrieval
  timed out again after creating `.lake/packages/*`. The `.lake/` directory is
  ignored by git.

2026-06-27

- Added Lean proof-integrity rules to `AGENTS.md` and
  `formalization/lean-readiness.md`.
- The final Connes-Weil theorem must target Mathlib's
  `_root_.RiemannHypothesis`, not a project-local substitute.
- Every custom route object must have a bridge theorem tying it to manuscript or
  source-paper notation.
- Source-paper assumptions must be quarantined under a source-interface layer.
- Final-route modules must not contain hidden `axiom`, `constant`, `opaque`,
  `unsafe`, `sorry`, or `admit`.
- Before external review, `#print axioms <final_theorem>` must be recorded. Any
  project-local axiom outside approved CCM24/CCM25/CC20 source interfaces blocks
  the artifact.

2026-06-27

- Investigated why `lake update`, `lake exe cache get`, and `lake build`
  appeared to time out.
- Found lingering WSL child processes from timed-out Lake commands:
  `lake update`, Mathlib `cache get`, and an old `lake build` in the previous
  `RiemannHypothesis` project kept running after the PowerShell tool timeout.
  These were stopped.
- Found the main performance cause: the active worktree lives under
  `/mnt/c/Projects/Connes-Weil-RH-Proof`, so WSL accesses Mathlib through the
  Windows filesystem boundary.
- Measured `/mnt/c` metadata cost on the Mathlib package:
  `git status` about 7.3 seconds, `lake env lean --print-prefix` about
  10.9 seconds, and `find .lake/packages/mathlib -type f` about 9.8 seconds.
- Copied the same Mathlib package to WSL ext4 under `/tmp`; there `git status`
  took about 0.55 seconds and `find` was effectively instantaneous. This points
  to WSL-on-NTFS metadata overhead, not Lean CPU work.
- Windows-native `lake`, `lean`, and `elan` were not available in PowerShell.
  The recommended fix is to run the Lean worktree from WSL ext4, not to switch
  to Windows.

2026-06-27

- Switched from full legacy `RiemannHypothesis` builds to a segmented
  `ConnesWeilRH` Lake target.
- Added `ConnesWeilRH.lean` and the initial segment modules:
  `Basic`, `Source/CCM24`, `Source/CCM25`, `Source/CC20`,
  `Route/Definitions`, `Route/AdmissibleWindow`, `Route/Ledger`,
  `Route/Theorem1`, `Route/Exhaustion`, and `Route/RouteTheorem`.
- Changed `lakefile.toml` default target to `ConnesWeilRH` while keeping the
  copied legacy `RiemannHypothesis` library available for separate audits.
- Added `docs/audits/lean-segment-build.md`.
- Built the segmented target from the WSL ext4 mirror with:
  `lake build ConnesWeilRH`. It completed successfully in about 56 seconds.
- Ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output was
  `[propext, Classical.choice, Quot.sound]`, with no project-local axiom in the
  current route skeleton.

2026-06-27

- Strengthened the Lean source-interface layer from loose field names to
  `SourceObligation` records with `sourceKey`, `sourceFile`, `lineRange`,
  `manuscriptRole`, and `statement`.
- Added source obligations for the current CCM24, CCM25, and CC20 line ranges
  used by the manuscript.
- Added `docs/audits/lean-source-interface-map.md` to map Lean names to source
  files, line ranges, and manuscript roles.
- Added Appendix E to
  `docs/manuscripts/connes-weil-rh-proof-draft.md` documenting the segmented
  Lean target, current axiom audit, and source-conditional boundary.
- Current phase-1 source obligations still use `statement := True` as a
  buildable placeholder. This is not a source theorem proof; the next Lean step
  is to replace each placeholder with a precise theorem statement.
- Rebuilt `ConnesWeilRH` on the WSL ext4 mirror. `lake build ConnesWeilRH`
  completed successfully in about 52 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.

2026-06-27

- Replaced the CCM25 `statement := True` placeholders with symbolic formula
  statements over `ConnesWeilRH.WeilFormSymbols`.
- Added `WeilFormSymbols` to `ConnesWeilRH.Basic`, including symbolic fields
  for `QW`, `QW_lambda`, `Psi`, convolution, finite-prime terms, archimedean
  terms, pole terms, prime-power pairings, and von Mangoldt weights.
- Added symbolic CCM25 statement predicates:
  `QWDefinitionStatement`, `PsiSignStatement`, `QWLambdaFormulaStatement`,
  `FinitePrimeNormalizationStatement`, and `PoleNormalizationStatement`.
- Updated `docs/audits/lean-source-interface-map.md` and Appendix E of the
  manuscript to say that CCM25 now has symbolic Lean statements, while CCM24 and
  CC20 still use buildable placeholders.
- Rebuilt `ConnesWeilRH` successfully on the WSL ext4 mirror and rechecked
  `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; no project-local
  axiom appeared.

2026-06-27

- Confirmed that the Lean formalization should proceed by segment instead of
  full legacy builds.
- Fixed the interrupted CC20 finite-vanishing exit refactor. The final route
  theorem now consumes `inputs.cc20.finiteVanishingRhExit.criterion`, supplied
  by `ConnesWeilRH.Source.CC20Interface`, instead of a route-local RH exit
  certificate field.
- Added `ConnesWeilRH.WeilPositivityInput` and
  `ConnesWeilRH.FiniteVanishingCriterionPackage` as the explicit shape of the
  CC20 finite-vanishing RH exit.
- Rebuilt `ConnesWeilRH` successfully on the WSL ext4 mirror:
  `lake build ConnesWeilRH` completed in about 49 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  and `unsafe`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-segment-build.md`,
  `docs/audits/lean-source-interface-map.md`,
  `formalization/lean-readiness.md`, and Appendix E of the manuscript with the
  segmented build rule and CC20 exit status.

2026-06-27

- Replaced the remaining CC20 `statement := True` trace/convention/sign
  placeholders with symbolic statements over
  `ConnesWeilRH.ArchimedeanTraceSymbols`.
- Added `ArchimedeanTraceSymbols` to `ConnesWeilRH.Basic`, with fields for the
  abstract test type, support-square trace, source no-defect trace, positive
  trace, trace-class gate, cyclic legality gate, Hilbert-Schmidt gate, Mellin
  half-density convention, and archimedean sign normalizations.
- Updated `ConnesWeilRH.Source.CC20Interface` so CC20 supplies
  `archimedeanSymbols` plus four statement proofs:
  `TraceSquareStatement`, `TraceClassTemplateStatement`,
  `MellinHalfDensityConventionStatement`, and
  `SignsAndNormalizationsStatement`.
- Built the edited segment on the WSL ext4 mirror:
  `lake build ConnesWeilRH.Source.CC20` completed successfully in about
  51 seconds.
- Rebuilt downstream route checks:
  `lake build ConnesWeilRH.Route.RouteTheorem` completed successfully in about
  10 seconds, and `lake build ConnesWeilRH` completed successfully in about
  3 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  and `unsafe`; none were found.
- `rg -n "statement := True" ConnesWeilRH/Source -g "*.lean"` now reports only
  the four CCM24 source-interface placeholders.

2026-06-27

- Added two hard-blocker audits for the current mathematics-first phase:
  `docs/audits/sign-defect-blocker-audit.md` and
  `docs/audits/source-import-legitimacy-audit.md`.
- The sign/defect audit treats the hostile objection as open until an accepted
  import or formal theorem proves that positive fixed-S trace reads as
  `QW_lambda` plus only killed ledgers and endpoint-strip `Cdef`, with no
  uncontrolled Sonin/prolate defect subtracted from `QW_lambda`.
- The source-import audit separates source definitions/formula candidates from
  strategy, numerical, and project-package claims. It explicitly marks CCM25
  spectral convergence and determinant convergence as non-importable unless
  later proved as theorems.
- Linked the two audits from the audit README, source-interface discharge audit,
  source-interface completion audit, core defect ledger, and Lean readiness map.

2026-06-27

- Added two theorem contracts for the hard-blocker audits:
  `docs/proofs/sonin-prolate-defect-cdef-theorem-contract.md` and
  `docs/proofs/restricted-to-full-qw-exhaustion-theorem-contract.md`.
- The Sonin/prolate contract states the formal/import target needed to prove
  that the CC20 prolate/Sonin difference is exactly rank, pole, or
  endpoint-strip `Cdef`, with no hidden positive defect outside the trace-norm
  bound.
- The restricted-to-full contract states the scalar fixed-test
  `QW_lambda(g,g) -> QW(g,g)` target and explicitly forbids importing CCM25
  spectral convergence or determinant convergence as that theorem.
- Updated the audit index, core defect ledger, source-interface audits,
  formal-gate spine audit, Lean-readiness note, and source-object interface
  plan to consume these contracts as mandatory gates.

2026-06-27

- Replaced the four CCM24 `statement := True` placeholders with symbolic
  statements over `ConnesWeilRH.SemilocalModelSymbols`.
- Added `SemilocalModelSymbols` to `ConnesWeilRH.Basic`, with fields for
  abstract place sets, support windows, tests, canonical Hilbert models, scaling
  action, Fourier grading, support and Fourier-support transport, bounded
  comparison maps, inverse comparison maps, and Sonin/exhaustion compatibility.
- Updated `ConnesWeilRH.Source.CCM24Interface` so CCM24 supplies
  `semilocalSymbols` plus four statement proofs:
  `CanonicalSemilocalModelStatement`, `SupportTransportStatement`,
  `BoundedComparisonStatement`, and `SoninComparisonStatement`.
- Built the edited segment on the WSL ext4 mirror:
  `lake build ConnesWeilRH.Source.CCM24` completed successfully in about
  55 seconds.
- Rebuilt downstream route checks:
  `lake build ConnesWeilRH.Route.RouteTheorem` completed successfully in about
  48 seconds, and `lake build ConnesWeilRH` completed successfully in about
  3 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  and `unsafe`; none were found.
- `rg -n "statement := True" ConnesWeilRH/Source -g "*.lean"` now finds no
  remaining source-interface placeholder.
- Updated `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`,
  Appendix E of the manuscript, `README.md`, and `formalization/README.md` to
  reflect the current source-interface state.

2026-06-27

- Added the first route-level bridge from fixed-`S` tests back to the CCM24
  semilocal source interface.
- Added `ConnesWeilRH.Route.SourceBackedFixedSTest`, which carries a
  route-level `FixedSTest` together with a CCM24 place set, support window,
  semilocal test object, canonical-model evidence, support-window evidence,
  Fourier-support evidence, Sonin-comparison evidence, and the route-level
  admissibility/triple-vanishing/finite-prime visibility fields.
- Added bridge lemmas in `ConnesWeilRH.Route.AdmissibleWindow`:
  `admissible_for_theorem1_of_source_backed`,
  `canonical_model_compatibility_of_source_backed`,
  `support_transport_of_source_backed`,
  `bounded_comparison_of_source_backed`, and
  `sonin_exhaustion_of_source_backed`.
- Updated `ConnesWeilRH.Route.RouteTheorem.RouteCertificate` so final route
  certificates consume `SourceBackedFixedSTest` and derive
  `AdmissibleForTheorem1` from
  `admissible_for_theorem1_of_source_backed` instead of accepting a bare
  route-local admissibility field.
- Built the affected segments on the WSL ext4 mirror. The aggregate command
  exceeded the tool timeout after all four printed successful build output, so
  the final targets were re-run with clean exit codes:
  `lake build ConnesWeilRH.Route.RouteTheorem` completed successfully in about
  15 seconds, and `lake build ConnesWeilRH` completed successfully in about
  2 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the source-backed route certificate status.

2026-06-27

- Added a CCM25-backed finite-prime visibility bridge.
- Added `ConnesWeilRH.WeilFormSymbols.FinitePrimeVisibilityStatement` as the
  selected-test finite-prime normalization statement.
- Updated `ConnesWeilRH.Route.SourceBackedFixedSTest` with a `weilTest` field
  and a `finitePrimeVisibilityBridge` from
  `FinitePrimeVisibilityStatement inputs.ccm25.weilSymbols weilTest weilTest`
  to `test.finitePrimesVisible`.
- Removed the direct `finitePrimesVisible : test.finitePrimesVisible` proof
  field from `SourceBackedFixedSTest`.
- Added `finite_prime_visibility_statement_of_source_backed`, which derives the
  selected-test finite-prime visibility statement from
  `inputs.ccm25.finitePrimeNormalization`.
- Added `finite_primes_visible_of_source_backed`, which applies the explicit
  bridge to obtain the route-level `test.finitePrimesVisible` predicate.
- Rebuilt the affected segments on the WSL ext4 mirror:
  `lake build ConnesWeilRH.Basic` completed in about 52 seconds,
  `lake build ConnesWeilRH.Route.Definitions` in about 4 seconds,
  `lake build ConnesWeilRH.Route.AdmissibleWindow` in about 3 seconds,
  `lake build ConnesWeilRH.Route.RouteTheorem` in about 9 seconds, and
  `lake build ConnesWeilRH` in about 3 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the finite-prime bridge status.

2026-06-27

- Added a source-backed full Weil positivity bridge.
- Added `ConnesWeilRH.Route.SourceBackedFullPositivity`, which carries a CC20
  archimedean test object, Hilbert-Schmidt gate, symbolic CCM25 Weil-form
  read-off proposition, a bridge from CCM25 `QW`, `QW_lambda`, and pole
  obligations to that proposition, a trace read-off bridge from CC20 trace data
  and CCM25 read-off to `FixedSPositiveTraceReadOff`, and cleared ledgers.
- Added `cc20_trace_square_of_source_backed`, which derives the CC20
  trace-square/nonnegativity result from `inputs.cc20.traceClassTemplate` and
  `inputs.cc20.archimedeanTraceSquare`.
- Added `ccm25_weil_form_read_off_of_source_backed`, which derives the symbolic
  Weil-form read-off from `inputs.ccm25.qwDefinition`,
  `inputs.ccm25.qwLambdaFormula`, and `inputs.ccm25.poleNormalization`.
- Added `fixed_s_read_off_of_source_backed_full_positivity` and
  `full_weil_positivity_of_source_backed`.
- Updated `ConnesWeilRH.Route.RouteTheorem.RouteCertificate` so final route
  certificates consume `SourceBackedFullPositivity`; the final theorem now gets
  `FullWeilPositivity` from `full_weil_positivity_of_source_backed` instead of
  directly calling `full_weil_positivity_of_fixed_s`.
- Rebuilt the affected segments on the WSL ext4 mirror:
  `lake build ConnesWeilRH.Route.Exhaustion` completed in about 46 seconds,
  `lake build ConnesWeilRH.Route.RouteTheorem` in about 3 seconds, and
  `lake build ConnesWeilRH` in about 3 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the source-backed full positivity status.

2026-06-27

- Added source-backed ledger clearing.
- Added `ConnesWeilRH.Route.SourceBackedLedgers`, with symbolic source
  propositions and witnesses for rank, pole, and Cdef ledger clearing.
- Rank clearing now bridges from CCM24 bounded comparison and CC20 sign
  normalization; pole clearing bridges from CCM25 pole normalization; Cdef
  exhaustion bridges from CCM24 Sonin comparison and CC20 Mellin convention.
- Added `rank_killed_of_source_backed_ledgers`,
  `pole_killed_of_source_backed_ledgers`,
  `cdef_exhausts_of_source_backed_ledgers`, and
  `ledgers_cleared_of_source_backed`.
- Updated `ConnesWeilRH.Route.SourceBackedFullPositivity` so it consumes
  `SourceBackedLedgers` instead of a direct `LedgersCleared` field.
- Rebuilt the affected segments on the WSL ext4 mirror:
  `lake build ConnesWeilRH.Route.Ledger` completed in about 50 seconds,
  `lake build ConnesWeilRH.Route.Exhaustion` in about 54 seconds,
  `lake build ConnesWeilRH.Route.RouteTheorem` in about 3 seconds, and
  `lake build ConnesWeilRH` in about 3 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the source-backed ledger status.

2026-06-27

- Added an explicit triple-vanishing bridge.
- Added `ConnesWeilRH.CriticalVanishingPoint`, with constructors `zero`,
  `half`, and `one`, and `ConnesWeilRH.TripleVanishingSymbols`.
- Added `TripleVanishingSymbols.TripleVanishingStatement`, which requires
  vanishing at every `CriticalVanishingPoint`.
- Updated `ConnesWeilRH.Route.SourceBackedFixedSTest` so it carries
  `tripleVanishingSymbols`, a proof of
  `TripleVanishingStatement tripleVanishingSymbols`, and a bridge from that
  statement to `test.tripleVanishing`.
- Removed the direct `tripleVanishing : test.tripleVanishing` proof field from
  `SourceBackedFixedSTest`.
- Added `triple_vanishing_statement_of_source_backed` and
  `triple_vanishing_of_source_backed`.
- Updated `ConnesWeilRH.Route.Exhaustion` and `RouteTheorem` so they use
  `triple_vanishing_of_source_backed` instead of directly reading
  `sourceBackedTest.tripleVanishing`.
- Rebuilt the affected segments on the WSL ext4 mirror:
  `lake build ConnesWeilRH.Basic` completed in about 47 seconds,
  `lake build ConnesWeilRH.Route.Definitions` in about 52 seconds,
  `lake build ConnesWeilRH.Route.AdmissibleWindow` in about 5 seconds,
  `lake build ConnesWeilRH.Route.Exhaustion` in about 5 seconds,
  `lake build ConnesWeilRH.Route.RouteTheorem` in about 5 seconds, and
  `lake build ConnesWeilRH` in about 3 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the triple-vanishing bridge status.

2026-06-27

- Split the fixed-S trace read-off bridge into smaller stages.
- Added `ConnesWeilRH.Route.SourceTraceReadOffData`, with fields for an
  archimedean trace-square proposition, a Weil-form read-off proposition,
  trace legality, no-defect source read-off, and final Weil identification.
- Added `fixed_s_read_off_of_source_trace_data`.
- Updated `ConnesWeilRH.Route.SourceBackedFullPositivity` so it carries
  `SourceTraceReadOffData`, a bridge from the CC20 trace-square result into the
  trace read-off data, and a bridge from the CCM25 Weil-form read-off result
  into the trace read-off data.
- Updated `fixed_s_read_off_of_source_backed_full_positivity` so it consumes
  both `cc20_trace_square_of_source_backed` and
  `ccm25_weil_form_read_off_of_source_backed` before producing
  `FixedSPositiveTraceReadOff`.
- Rebuilt the affected segments on the WSL ext4 mirror:
  `lake build ConnesWeilRH.Route.Theorem1` completed in about 45 seconds,
  `lake build ConnesWeilRH.Route.Exhaustion` in about 3 seconds,
  `lake build ConnesWeilRH.Route.RouteTheorem` in about 3 seconds, and
  `lake build ConnesWeilRH` in about 3 seconds.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the trace-read-off split status.

2026-06-27

- Hardened `ConnesWeilRH.Route.FixedSPositiveTraceReadOff` so it is no longer
  definitionally equal to `AdmissibleForTheorem1`.
- `FixedSPositiveTraceReadOff` now requires an existential package containing
  trace legality, no-defect source read-off, Weil identification, and
  positive-trace nonnegativity evidence.
- Updated `SourceTraceReadOffData` with separate bridge fields for those four
  outputs. The fixed-S read-off theorem now consumes both the CC20 trace-square
  result and the CCM25 Weil-form read-off result before constructing the final
  fixed-S positive trace package.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the fixed-S trace output hardening status.

2026-06-27

- Moved the CC20 archimedean test object and Hilbert-Schmidt gate into
  `ConnesWeilRH.Route.SourceTraceReadOffData`.
- Added concrete Theorem 1 helper predicates:
  `CC20TraceLegality`, `CC20NoDefectSourceReadOff`,
  `CC20PositiveTraceNonnegative`, and `CC20TraceSquareReadOff`.
- Added `cc20_trace_legality_of_source_trace_data` and
  `cc20_trace_square_of_source_trace_data`, so the Theorem 1 segment derives
  trace-class/cyclicity legality and trace-square/nonnegativity from
  `inputs.cc20.traceClassTemplate` and `inputs.cc20.archimedeanTraceSquare`.
- Removed the duplicate CC20 archimedean test, Hilbert-Schmidt gate, and
  trace-square bridge from `SourceBackedFullPositivity`; downstream positivity
  now supplies only the CCM25 Weil-form read-off to the fixed-S trace package.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the CC20 trace-gate ownership status.

2026-06-27

- Replaced the loose CCM25 `weilFormReadOff : Prop` and free read-off bridge on
  `SourceBackedFullPositivity` with
  `ConnesWeilRH.Route.CCM25WeilFormReadOff`.
- `CCM25WeilFormReadOff` records the selected test function, restricted
  parameter `lambda`, the `1 < lambda` gate, the `QW` definition, the `Psi`
  sign formula, the restricted `QW_lambda` formula, and pole normalization.
- `SourceTraceReadOffData` now carries `lambda` and `oneLtLambda`.
  `ConnesWeilRH.Route.ccm25_weil_form_read_off` derives the read-off from
  `inputs.ccm25.qwDefinition`, `inputs.ccm25.qwLambdaFormula`, and
  `inputs.ccm25.poleNormalization`.
- `SourceBackedFullPositivity` no longer carries a route-local
  `weilFormReadOff` proposition, a bridge from source obligations into that
  proposition, or a bridge into the trace data.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, `statement := True`, and stale `weilFormReadOff` bridge fields;
  none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the CCM25 read-off hardening status.

2026-06-27

- Recorded Peter's commit policy in `AGENTS.md`: future major milestone commits
  and pushes should use GPG-signed commits that GitHub shows as Verified.
- Checked current Git signing configuration with `git config --get
  commit.gpgsign`, `user.signingkey`, and `gpg.format`; no signing config was
  present in the current repository scope. Before the next milestone commit,
  verify the secret key and enable signing rather than creating an unsigned
  milestone commit.
- Split final Weil identification through a new intermediate
  `ConnesWeilRH.Route.TraceWeilCompatibility` proposition.
- `SourceTraceReadOffData` now has `traceWeilCompatibility`,
  `traceWeilCompatibilityBridge`, and a narrower `weilIdentificationBridge`.
  The first bridge combines admissibility, CC20 no-defect trace read-off, and
  CCM25 Weil-form read-off. The second bridge combines that compatibility with
  positive-trace nonnegativity to produce the final Weil identification.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the trace-Weil compatibility split status.

2026-06-27

- Bound the restricted parameter `lambda` to the CCM24 semilocal window instead
  of treating it as a route-local free parameter.
- Added `SemilocalModelSymbols.lambdaCompatible`.
- Added `SourceBackedFixedSTest.lambdaCompatibilityBridge`, which turns CCM24
  support transport, convolution-support transport, and Sonin window exhaustion
  into `lambdaCompatible window lambda` for every `lambda` with `1 < lambda`.
- Added `ConnesWeilRH.Route.WindowLambdaCompatibility` and
  `lambda_compatible_of_source_backed`.
- Updated `CCM25WeilFormReadOff` so it is indexed by the source-backed fixed-`S`
  test and includes `WindowLambdaCompatibility inputs g lambda`, not just
  `1 < lambda`.
- Updated `FixedSPositiveTraceReadOff`, `FullWeilPositivity`, and
  `toWeilPositivityInput` so fixed-S positivity now stays attached to
  `SourceBackedFixedSTest` rather than a bare `FixedSTest`.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Basic`,
  `lake build ConnesWeilRH.Route.Definitions`,
  `lake build ConnesWeilRH.Route.AdmissibleWindow`,
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the lambda/window compatibility status.

2026-06-27

- Hardened `ConnesWeilRH.Route.TraceWeilCompatibility` from a simple
  conjunction into a named read-off equality package.
- `SourceTraceReadOffData` now carries `fullTraceReadOff`, identifying the CC20
  source no-defect trace with the CCM25 `QW` value, and
  `restrictedTraceReadOff`, identifying the CC20 support-square trace with the
  restricted CCM25 `QW_lambda` value.
- `traceWeilCompatibilityBridge` now consumes those two named equalities before
  producing `traceWeilCompatibility`; `weilIdentificationBridge` remains the
  final step from compatibility plus positive-trace nonnegativity to Weil
  identification.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the trace-Weil read-off equality status.

2026-06-27

- Replaced direct `fullTraceReadOff` and `restrictedTraceReadOff` equality
  fields on `SourceTraceReadOffData` with source-backed bridge data.
- Added `ConnesWeilRH.Route.FullTraceReadOffSource` and
  `ConnesWeilRH.Route.RestrictedTraceReadOffSource`.
- `SourceTraceReadOffData` now carries `fullTraceReadOffSource`,
  `restrictedTraceReadOffSource`, their proof fields, and bridge functions that
  produce the concrete read-off equalities consumed by
  `traceWeilCompatibilityBridge`.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the source-backed read-off equality bridge
  status.

2026-06-27

- Tightened the source-backed read-off equality bridges again.
- Removed arbitrary `fullTraceReadOffSource : Prop` and
  `restrictedTraceReadOffSource : Prop` certificate fields from
  `SourceTraceReadOffData`.
- `fullTraceReadOffBridge` now consumes `CC20NoDefectSourceReadOff` directly
  before producing `FullTraceReadOffSource`.
- `restrictedTraceReadOffBridge` now consumes `CCM25WeilFormReadOff` directly
  before producing `RestrictedTraceReadOffSource`.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, `statement := True`, and stale arbitrary read-off source fields;
  none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the direct-leg read-off bridge status.

2026-06-27

- Factored read-off equality targets out of the source bundles in
  `ConnesWeilRH.Route.Theorem1`.
- Added `FullTraceReadOffEquality` for the equality between the CC20 source
  no-defect trace and the CCM25 `QW` value.
- Added `RestrictedTraceReadOffEquality` for the equality between the CC20
  support-square trace and the restricted CCM25 `QW_lambda` value.
- Updated `FullTraceReadOffSource` and `RestrictedTraceReadOffSource` so each
  bundles a concrete source leg with the corresponding named equality.
- Updated `traceWeilCompatibilityBridge` so it consumes the named equality
  propositions instead of raw equality expressions.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the read-off equality factoring status.

2026-06-27

- Split the CCM25 read-off in `ConnesWeilRH.Route.Theorem1` into
  `CCM25FullQWReadOff` and `CCM25RestrictedQWReadOff`.
- `CCM25FullQWReadOff` uses `inputs.ccm25.qwDefinition`, covering the full
  `QW` definition and `Psi` sign formula for the selected test.
- `CCM25RestrictedQWReadOff` uses `WindowLambdaCompatibility`,
  `inputs.ccm25.qwLambdaFormula`, and `inputs.ccm25.poleNormalization`.
- `CCM25WeilFormReadOff` now bundles the full and restricted legs.
- `FullTraceReadOffSource` now bundles `CC20NoDefectSourceReadOff`,
  `CCM25FullQWReadOff`, and `FullTraceReadOffEquality`.
- `RestrictedTraceReadOffSource` now bundles `CCM25RestrictedQWReadOff` and
  `RestrictedTraceReadOffEquality`.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Checked `ConnesWeilRH` for `sorry`, `admit`, `axiom`, `constant`, `opaque`,
  `unsafe`, and `statement := True`; none were found.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the CCM25 full/restricted read-off split.

2026-06-27

- Enabled repository-local GPG signing defaults for future milestone commits:
  `commit.gpgsign=true` and `gpg.format=openpgp`.
- Verified available signing keys:
  - Windows GPG secret key: `F84F18CD20BE8255`.
  - WSL GPG secret key: `4A3DF2D26A5B704F`.
  - WSL git resolves `user.signingkey=4A3DF2D26A5B704F` from the user config.
- Next milestone commit should be made from the WSL workflow unless the Windows
  signing key is chosen explicitly. Before pushing, verify
  `git log --show-signature -1` locally and confirm GitHub renders the commit as
  Verified.

2026-06-27

- Split the CCM25 read-off legs in the documentation down to the current Lean
  granularity.
- `CCM25FullQWReadOff` now documents two visible sub-obligations:
  `CCM25QWDefinitionReadOff` and `CCM25PsiSignReadOff`.
- `CCM25RestrictedQWReadOff` now documents three visible sub-obligations:
  `WindowLambdaCompatibility`, `CCM25QWLambdaFormulaReadOff`, and
  `CCM25PoleNormalizationReadOff`.
- Added `SemilocalModelSymbols.windowContainedInLambda` and
  `Route.WindowSupportContainment`.
- `WindowLambdaCompatibility` now carries `1 < lambda`,
  `WindowSupportContainment`, and `lambdaCompatible window lambda`. The
  containment package records support in the CCM24 window, Fourier support in
  the same window, convolution-support transport, and
  `windowContainedInLambda window lambda`.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Basic`,
  `lake build ConnesWeilRH.Route.Definitions`,
  `lake build ConnesWeilRH.Route.AdmissibleWindow`,
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`,
  Appendix E of the manuscript, `README.md`, and `formalization/README.md` with
  the GPG signing gate and the explicit window-containment status.

2026-06-27

- Removed the empty finite-prime placeholder sums from the CCM25 symbolic Lean
  formulas.
- Added `WeilFormSymbols.globalPrimeIndexSet` for the full `Psi`/`QW`
  finite-prime sum and `WeilFormSymbols.restrictedPrimeIndexSet` for the
  restricted `QW_lambda` finite-prime sum.
- Updated `CCM25PsiSignReadOff` and `CCM25QWLambdaFormulaReadOff` to use those
  explicit index sets instead of `Finset.range 0`.
- Rebuilt the affected WSL ext4 segments:
  `lake build ConnesWeilRH.Basic`,
  `lake build ConnesWeilRH.Source.CCM25`,
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully after a brief Lean
  indentation fix in `Theorem1.lean`.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Updated `AGENTS.md`, `docs/audits/lean-source-interface-map.md`,
  `docs/audits/lean-segment-build.md`, `formalization/lean-readiness.md`, and
  Appendix E of the manuscript with the explicit finite-prime index-set status.

2026-06-27

- Stopped work after recording progress per Peter's instruction.
- Public repository hygiene note: the repository is public. Do not stage or
  publish root private workflow files such as `AGENTS.md` or `MEMORY.md`.
- Created and pushed the public milestone commit:
  `cba83caa74ac2695a17450ddc7588cfdfd2e6633`
  (`Add source-conditional Lean route scaffold`).
- The milestone commit was GPG-signed with WSL key
  `00663BFB2C84E7A6302D29DA4A3DF2D26A5B704F`.
- Verified locally from WSL:
  `Good signature from "peter941221 <peter941221@gmail.com>"`.
- Verified through GitHub API:
  `verified=true`, `reason=valid`.
- Confirmed remote `origin/main` points to
  `cba83caa74ac2695a17450ddc7588cfdfd2e6633`.
- Public milestone contents:
  `ConnesWeilRH.lean`, `ConnesWeilRH/`, `docs/audits/`,
  `formalization/lean-readiness.md`, `lakefile.toml`, `lake-manifest.json`,
  `lean-toolchain`, and public README/manuscript updates.
- Excluded from public milestone:
  root `AGENTS.md`, root `MEMORY.md`, and the copied legacy
  `RiemannHypothesis/` tree. The legacy tree remains local/untracked.
- After the push, added a local Lean hardening that has not been committed:
  `FinitePrimeVisibilityStatement` now splits finite-prime visibility into:
  `GlobalPrimeIndexCoverageStatement`,
  `RestrictedPrimeIndexCoverageStatement`, and
  `FinitePrimeTermNormalizationStatement`.
- Updated `finite_prime_visibility_statement_of_source_backed` to consume the
  new combined CCM25 interface, and added route helper theorems:
  `global_prime_index_covers_of_source_backed`,
  `restricted_prime_index_covers_of_source_backed`, and
  `finite_prime_term_normalization_of_source_backed`.
- Rebuilt the affected WSL ext4 segments after the local hardening:
  `lake build ConnesWeilRH.Basic`,
  `lake build ConnesWeilRH.Source.CCM25`,
  `lake build ConnesWeilRH.Route.AdmissibleWindow`,
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` all completed successfully.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the output
  remained `[propext, Classical.choice, Quot.sound]`.
- Current local state at stop:
  - tracked public files modified but not committed:
    `ConnesWeilRH/Basic.lean`,
    `ConnesWeilRH/Route/AdmissibleWindow.lean`;
  - local untracked legacy files:
    `RiemannHypothesis.lean`, `RiemannHypothesis/`;
  - ignored private files:
    `AGENTS.md`, `MEMORY.md`;
  - no running Lake/Lean process was found by the WSL process check.
- Next safe continuation:
  update the public audit/manuscript/readiness docs for the new finite-prime
  coverage split, rerun hygiene scans, then wait for the next major milestone
  before another signed public commit.

2026-06-27

- Reviewed the imported exploration log `docs/ConnesWeilPositivity.md`.
- Found that it is useful as a route map, not as proof evidence:
  it starts with "The route is not closed" and later marks several items as
  route-note or paper-level closed.
- Extracted the three hard positive-trace-to-Weil proof packages into public
  audit docs:
  `docs/audits/core-defect-gap-ledger.md` and
  `docs/audits/three-battle-workplan.md`.
- Added `docs/audits/README.md` so the new audit docs are discoverable.
- The three battle targets are now:
  `TestAndQuotientCompatibility(S,I,lambda)`,
  `FixedSQuantizedSupportSquareTransport(S,I,lambda)`, and
  `CdefNormFormula/FixedTestCdefExhaustion`.
- The audit files state that route-note labels such as `paper-closed` are not
  proof certificates; the route remains source-conditional until the three
  theorem packages and source interfaces are discharged.
- Ran document hygiene checks on the new audit files:
  `git diff --check`, private path/artifact scan, and non-ASCII scan all passed.
- Current public-worktree caution remains:
  `docs/ConnesWeilPositivity.md` is a large untracked exploration log and
  should not be committed without a separate public-hygiene review.

2026-06-27

- Added `docs/audits/battle-1-test-quotient-compatibility.md`.
- The audit decomposes Battle 1 into three theorem obligations:
  `TestHalfDensityCompatibility(lambda)`,
  `TateDirectionsToPoleLedger(lambda)`, and
  `RankRepairToZeroModeLedger(S,I)`.
- Current judgment: Battle 1 is located and decomposed, not proved.
- The half-density leg is the strongest candidate, but still needs exact source
  formula citation in the final proof.
- The rank-repair leg is the weakest part; it needs a finite normal-form lemma
  splitting pure zero-mode terms from projection-defect terms charged to
  endpoint-strip `Cdef`.
- Updated `docs/audits/README.md` and
  `docs/audits/core-defect-gap-ledger.md` to point to the Battle 1 audit.

2026-06-27

- Added `docs/audits/battle-2-fixed-s-support-square-transport.md`.
- The audit decomposes Battle 2 into five theorem obligations:
  `FixedSProjectionTransport(S,lambda)`,
  `FixedSPhasePullback(S,lambda)`,
  `FixedSNoDefectSupportSquareTemplate(S,I,lambda)`,
  `FixedSDefectClassification(S,I,lambda,J)`, and
  `TraceClassCyclicSupportSquareIdentity(S,I,lambda)`.
- Current judgment: Battle 2 is located and decomposed, not proved.
- The weakest algebraic step is replacing `u_infty` by `u_S` in the CC20
  support-square template after transport through `V_S=M_S U_S`; the phrase
  "same quantized-calculus expansion" must be replaced by a term-by-term
  proof.
- Updated `docs/audits/README.md`,
  `docs/audits/core-defect-gap-ledger.md`, and
  `docs/audits/three-battle-workplan.md` to point to the Battle 2 audit.

2026-06-27

- Added `docs/audits/battle-3-cdef-exhaustion.md`.
- The audit decomposes Battle 3 into five theorem obligations:
  `EndpointStripNormalForm(S,I,lambda,J)`,
  `EndpointStripTraceNormBound(S,I,lambda,J)`,
  `QEndpointStripStability(S,I,lambda,J)`,
  `CdefGraphComparison(S,I,lambda,J,J')`, and
  `FixedTestCdefExhaustion(S_A,I,g,J')`.
- Current judgment: Battle 3 is located and decomposed, not proved.
- The critical limit gate is fixed-test exhaustion:
  `Cdef_graph_(S_A,I,lambda,J')(g) -> 0` with `g`, `I`, and `S_A` fixed before
  `lambda -> infinity`.
- Updated `docs/audits/README.md`,
  `docs/audits/core-defect-gap-ledger.md`, and
  `docs/audits/three-battle-workplan.md` to point to the Battle 3 audit.

2026-06-27

- Peter set the project priority: finish the mathematical proof before further
  Lean work.
- Added the rule to root `AGENTS.md`: complete
  `TestAndQuotientCompatibility`,
  `FixedSQuantizedSupportSquareTransport`, and
  `CdefNormFormula/FixedTestCdefExhaustion` mathematically before adding more
  Lean scaffolding.

2026-06-27

- Added `docs/proofs/battle-1-test-quotient-proof-package.md`.
- The proof package closes the half-density leg and Tate pole leg at the
  current source-interface level, using the manuscript/source-reread anchors
  for `QW(f,g)=Psi(f^* * g)`, `W_(0,2)`, `QW_lambda`, and the CC20
  half-density convention.
- Battle 1 remains conditional on one project lemma:
  `RankRepairFiniteNormalForm(S,I)`.
- The remaining rank-repair proof must classify no-strip fixed-S rank repair
  terms as scalar zero-mode terms and route all non-pure terms through
  endpoint-strip `Cdef`.

2026-06-27

- Added `docs/proofs/rank-repair-finite-normal-form.md`.
- The rank-repair proof package proves the pure zero-mode rank part at the
  current route-evidence level and records the endpoint-strip defect normal
  form plus `Q` defect-continuity skeleton.
- It does not close `RankRepairFiniteNormalForm(S,I)`.
- The remaining rank-repair gap is now sharper:
  `SemilocalQCompactFormIdentity(S,I)` plus
  `BoundaryJetRankCdefDichotomy(S,I)`.
- Updated `docs/proofs/battle-1-test-quotient-proof-package.md` to point to
  the rank-repair proof package and to state the reduced gap explicitly.

2026-06-27

- Added `docs/proofs/semilocal-q-compact-form.md`.
- The semilocal compact-form package proves the projection-defect side of the
  rank-repair compact-form gap at route-evidence level:
  canonical boundary-jet quarantine, projection-defect normal form,
  endpoint-strip `Q` trace ideal stability, and projection-defect boundary
  dichotomy.
- Battle 1 is now reduced more sharply to
  `FixedSNoDefectCompactFormReadOff(S,I)`, rather than the broader pair
  `SemilocalQCompactFormIdentity(S,I)` plus
  `BoundaryJetRankCdefDichotomy(S,I)`.
- Updated `docs/proofs/rank-repair-finite-normal-form.md`,
  `docs/proofs/battle-1-test-quotient-proof-package.md`,
  `docs/audits/battle-1-test-quotient-compatibility.md`, and
  `docs/audits/README.md` to reflect the narrower gap.

2026-06-27

- Added `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md`.
- The Battle 2 package expands `FixedSQuantizedSupportSquareTransport` into:
  `FixedSProjectionTransport`, `FixedSPhasePullback`,
  `FixedSNoDefectSupportSquareTemplate`,
  `FixedSDefectClassification`, and
  `TraceClassCyclicSupportSquareIdentity`.
- It replaces the unsafe phrase "same quantized-calculus expansion" with a
  term-by-term transport chain through `V_S=M_S U_S`.
- Battle 2 remains conditional on adjacent packages: the Battle 1 rank/pole
  ledger and the Battle 3 endpoint-strip `Cdef` norm package.
- Updated the Battle 2 audit, three-battle workplan, core defect ledger, and
  audit README to point to the proof package.

2026-06-27

- Added `docs/proofs/battle-3-cdef-exhaustion-proof-package.md`.
- The Battle 3 package defines the trace-norm
  `Cdef_(S,I,lambda,J)(g)` using endpoint-strip normal-form terms and
  `Q` boundary-strip traces.
- It proves the route-evidence chain:
  endpoint-strip index set, trace-norm formula, finite-strip trace-norm bound,
  `Q` endpoint-strip stability, graph comparison, and fixed-test exhaustion.
- The fixed-test limit is recorded in the correct order:
  choose `g`, choose `I`, choose `S_A`, fix graph order, then send
  `lambda -> infinity`.
- Battle 3 remains conditional on the graph/prolate fixed-test exhaustion
  input for `Cdef_graph_(S_A,I,lambda,J')(g) -> 0`.
- Updated the Battle 3 audit, three-battle workplan, core defect ledger, and
  audit README to point to the proof package.

2026-06-27

- Added `docs/proofs/fixed-s-no-defect-compact-form-read-off.md`.
- This package discharges `FixedSNoDefectCompactFormReadOff(S,I)` at
  source-interface level by separating:
  source test identification `F_g=g^* * g`,
  CCM25 sign and pole normalization,
  restricted `QW_lambda` read-off,
  and absence of extra no-strip channels after the Battle 1/Battle 2 ledger
  split.
- Updated Battle 1 proof and audit docs so the rank-repair leg is now marked
  closed at route-evidence level, with the boundary that it remains
  source-conditional and depends on the endpoint-strip `Cdef` package.

2026-06-27

- Added `docs/proofs/fixed-test-graph-cdef-exhaustion.md`.
- This package discharges the previous graph/prolate exhaustion input used by
  Battle 3 for fixed `g`, fixed `I`, fixed `S_A`, and fixed graph order.
- The proof separates support-tail exhaustion, Fourier-tail exhaustion from
  Schwartz Mellin/Fourier decay, endpoint-strip commutator tails, and finite
  summation of graph-Cdef seminorms.
- Updated Battle 3 proof and audit docs so Battle 3 is now marked closed at
  route-evidence level rather than conditional on an opaque
  `Cdef_graph -> 0` input.

2026-06-27

- Synchronized the three-battle status:
  - Battle 1 is closed at route-evidence level, source- and Cdef-conditional.
  - Battle 2 is closed at route-evidence level, source-conditional.
  - Battle 3 is closed at route-evidence level.
- This does not make the repository a public proof certificate. The route still
  depends on the cited CCM24, CCM25, and CC20 source interfaces, and the
  manuscript still needs a final one-notation pass before any public claim.

2026-06-27

- Integrated the three battle packages into
  `docs/manuscripts/connes-weil-rh-proof-draft.md` through a new
  `Three-Battle Integrated Gate` section.
- The manuscript now points from one notation to the Battle 1, Battle 2, and
  Battle 3 proof packages and records the integrated consequence:
  positive trace equals `QW_lambda` plus rank, pole, and `Cdef` ledgers, with
  the triple-killed test class removing rank and pole and the fixed-test limit
  removing `Cdef`.
- Added `docs/audits/three-battle-completion-audit.md`.
- The completion audit marks:
  `TestAndQuotientCompatibility`,
  `FixedSQuantizedSupportSquareTransport`, and
  `CdefNormFormula/FixedTestCdefExhaustion`
  as passing at route-evidence level.
- The boundary remains unchanged: this is source-conditional route evidence,
  not a Lean proof, journal acceptance, Clay acceptance, or public proof
  certificate.

2026-06-27

- Added `docs/audits/source-interface-discharge-audit.md`.
- The new audit turns the remaining source-conditional boundary into a concrete
  discharge matrix for CCM24, CCM25, and CC20.
- It records, for each Lean source contract, the source line ranges, the exact
  proof or import still needed, and the first failure mode to attack.
- The recommended next hard target is
  `CCM25RestrictedReadOffDischarge(lambda,g)`, because it simultaneously checks
  lambda-window compatibility, finite-prime coverage, finite-prime term
  normalization, pole normalization, and the sign convention in the restricted
  `QW_lambda` read-off.
- Updated `docs/audits/README.md` and `formalization/lean-readiness.md` so the
  post-three-battle path is explicit: stop adding route scaffolding, and start
  discharging CCM24/CCM25/CC20 source interfaces.

2026-06-27

- Added `docs/proofs/ccm25-restricted-read-off-discharge.md`.
- This is the first proof package for the source-interface discharge phase.
- It attacks `CCM25RestrictedReadOffDischarge(lambda,g)` by splitting the
  restricted CCM25 read-off into six auditable gates:
  window-lambda compatibility, source test identification `F_g=g^* * g`,
  restricted `QW_lambda` formula, finite-prime coverage and term normalization,
  pole normalization, and restricted sign pattern.
- The package maps those gates to the current Lean targets:
  `WindowLambdaCompatibility`, `CCM25QWLambdaFormulaReadOff`,
  `CCM25PoleNormalizationReadOff`,
  `RestrictedPrimeIndexCoverageStatement`, and
  `FinitePrimeTermNormalizationStatement`.
- Updated `docs/audits/README.md` and
  `docs/audits/source-interface-discharge-audit.md` to point to the new proof
  package.
- Boundary remains unchanged: this is a source-interface proof package, not a
  formal proof of CCM25 inside Lean and not a completed RH certificate.

2026-06-27

- Created and pushed signed milestone commit:
  `2e3c560242e9072f89cc82aaa3c76e8911b26a21`
  (`Add source-discharge proof packages`).
- Commit was made from the WSL ext4 workflow and signed with OpenPGP key
  `00663BFB2C84E7A6302D29DA4A3DF2D26A5B704F`.
- Local `git log --show-signature -1` reported a good signature from
  `peter941221 <peter941221@gmail.com>`.
- GitHub API verification for the pushed commit reported
  `verified=true`, `reason=valid`.
- `origin/main` now points to the same commit.
- Pre-commit checks run from WSL ext4:
  `git diff --cached --check`,
  staged public-path/private-artifact scan,
  staged document ASCII scan,
  `rg` forbidden Lean token scan,
  `lake build ConnesWeilRH`, and
  `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`.
- `lake build ConnesWeilRH` completed successfully, and the final theorem axiom
  audit remained `[propext, Classical.choice, Quot.sound]`.
- Excluded from the public commit: root `AGENTS.md`, root `MEMORY.md`, local
  legacy `RiemannHypothesis/`, and the large exploration log
  `docs/ConnesWeilPositivity.md`.

2026-06-27

- Continued after the signed milestone from the WSL ext4 worktree, because the
  Windows worktree still showed the already-pushed milestone files as local
  changes on the older `cba83ca` HEAD.
- Added `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md`.
- This package attacks the finite-prime subtargets left by
  `CCM25RestrictedReadOffDischarge(lambda,g)`:
  `RestrictedPrimeIndexCoverageStatement W lambda F_g` and
  `FinitePrimeTermNormalizationStatement W g g`.
- It splits the finite-prime discharge into prime-power atom shape, restricted
  index coverage, von Mangoldt weight normalization, prime-power pairing
  normalization, finite-prime term normalization, and fixed-S visibility before
  the lambda exhaustion.
- Updated `docs/audits/README.md`,
  `docs/audits/source-interface-discharge-audit.md`, and
  `formalization/lean-readiness.md` to reference the finite-prime package.
- Boundary remains unchanged: this is a source-interface proof package and does
  not yet replace the symbolic `WeilFormSymbols` fields with formal source
  definitions or accepted imports.

2026-06-27

- Peter changed the operating rule: use the Windows worktree
  `C:\Projects\Connes-Weil-RH-Proof` as the single source of truth.
- Do not treat the WSL ext4 mirror as authoritative. If WSL is used later for
  verification, sync from Windows first.
- Peter also set the proof priority: continue the mathematical proof and do not
  advance Lean for now.
- Reverted the attempted new Lean scaffold layer from this turn:
  `PrimePowerSupportSymbols`, `PrimePowerSupportPairingStatement`,
  `ccm25FinitePrimeSupportPairing`, and the route bridge theorem were removed.
- Kept the mathematics-only finite-prime proof package:
  `docs/proofs/ccm25-finite-prime-support-pairing-discharge.md`, plus its audit
  references.

2026-06-27

- Continued from the Windows worktree as the single source of truth.
- Did not touch Lean after Peter's instruction to focus on the mathematical
  proof first.
- Confirmed CodeGraph is initialized but indexes zero files in this repository;
  used `rg` and direct file reads for Markdown proof-package work.
- Downloaded the official CC20 arXiv source package `2006.13771` only for local
  source-line verification and checked `weil-compo.tex` ranges:
  `378-387`, `448-464`, `2014-2030`, `2072-2085`, `2106-2121`, and
  `2131-2165`.
- Added `docs/proofs/cc20-trace-legality-mellin-discharge.md`.
- The new package attacks `cc20ArchimedeanTraceSquare`,
  `cc20TraceClassTemplate`, `cc20MellinHalfDensityConvention`, and
  `cc20SignsAndNormalizations` at source-interface proof-package level.
- It separates the proof into Hilbert-Schmidt before positivity, trace-class
  before cyclicity, CC20 source trace-square read-off, archimedean sign
  normalization, and Mellin half-density compatibility with `F_g=g^* * g`.
- Updated `docs/audits/README.md` and
  `docs/audits/source-interface-discharge-audit.md` to point to the new CC20
  proof package.
- Document checks passed for the changed public docs:
  `git diff --check`, ASCII scan, private path/artifact scan, and placeholder
  marker scan.
- No Lean build was run.

2026-06-27

- Continued the mathematics-only source-discharge phase from the Windows
  worktree as the single source of truth.
- Added `docs/proofs/cc20-finite-vanishing-rh-exit-discharge.md`.
- The package attacks `cc20FiniteVanishingRhExit` at source-interface
  proof-package level.
- It proves the final exit chain: route triple vanishing translates to CC20
  Mellin vanishing on `F={0,1/2,1}`; that set is finite, contains `{0,1}`, and
  is disjoint from non-trivial zeros; route full Weil positivity feeds CC20
  Proposition C.1 only through the sign bridge
  `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)`.
- Updated `docs/audits/README.md` and
  `docs/audits/source-interface-discharge-audit.md` to reference the final
  CC20 exit package.
- Added the sign-bridge and Proposition C.1 finite-set pitfalls to root
  `AGENTS.MD`.
- Document checks passed for the changed public docs: `git diff --check`,
  direct trailing-whitespace scan, ASCII scan, private path/artifact scan, and
  placeholder marker scan.
- No Lean files were edited in this step and no Lean build was run.

2026-06-27

- After the signed public milestone
  `21eb6274da6834cc2ce7d2ff2433540473714415`, continued from a clean Windows
  `origin/main` worktree.
- Added `docs/audits/source-interface-discharge-completion-audit.md`.
- The audit confirms that every CCM24, CCM25, and CC20 source-interface row now
  has a named proof package.
- The audit also records the boundary: none of the source-interface rows is
  yet discharged by a formal Lean theorem or accepted imported theorem with
  audited hypotheses.
- Updated `docs/audits/README.md` to reference the new completion audit.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Inspected local Mathlib's canonical RH definition in
  `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean`.
- Mathlib defines `_root_.RiemannHypothesis` as: for every complex `s`,
  `riemannZeta s = 0`, no negative-even trivial-zero witness
  `s = -2 * (n + 1)`, and `s != 1` imply `s.re = 1/2`.
- Added `docs/proofs/source-rh-to-mathlib-rh-definition-bridge.md`.
- The package decomposes the source-to-Mathlib bridge into same zeta function,
  same non-trivial zero predicate, same trivial-zero and pole exclusions, and
  same critical-line equation.
- Updated `docs/audits/README.md` and
  `docs/audits/source-interface-discharge-audit.md` to reference the definition
  bridge package.
- Added the rule to root `AGENTS.MD`: a source theorem concluding "RH" must be
  transported to Mathlib's exact `_root_.RiemannHypothesis` before
  certification; same name is not enough.
- No Lean files were edited in this step and no Lean build was run.

2026-06-27

- Verified the official CCM24 arXiv source package `2310.18423` and checked
  `mainc2m24fine.tex` ranges: `237-253`, `761-771`, `786-804`, `806-823`,
  `983-1003`, and `1050-1060`.
- Added `docs/proofs/ccm24-support-window-transport-discharge.md`.
- The package attacks `ccm24CanonicalSemilocalModel`,
  `ccm24SupportTransport`, `ccm24BoundedComparison`, and
  `ccm24SoninComparison` at source-interface proof-package level.
- It proves the fixed-S drift guard: the positive trace, CCM25 `QW_lambda`
  read-off, and endpoint-strip `Cdef` exhaustion must use one CCM24
  source-backed support window through `eta_S`, Fourier-support transport,
  `V_S=M_S U_S`, bounded comparison, and `theta_S`/Sonin comparison.
- Updated `docs/audits/README.md` and
  `docs/audits/source-interface-discharge-audit.md` to reference the CCM24
  support-window transport package.
- Added the one-window CCM24 transport rule to root `AGENTS.MD`.
- Document checks passed for the changed public docs: ASCII scan,
  direct trailing-whitespace scan, private path/artifact scan, and placeholder
  marker scan.
- No Lean files were edited in this step and no Lean build was run.

2026-06-27

- Verified the official CCM25 arXiv source package `2511.22755` and checked
  `mc2arXiv.tex` ranges `445-470` and `530-540`.
- Added `docs/proofs/qw-to-cc20-weil-inequality-sign-bridge.md`.
- The package proves the source-interface sign bridge from CCM25 `QW` to the
  CC20 Proposition C.1 inequality:
  `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)`, hence
  `QW(g,g) >= 0` implies `sum_v W_v(g * bar(g)^sharp) <= 0`.
- The package uses the CCM25 formulas
  `QW(f,g)=Psi(f^* * g)`,
  `Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)`, and `W_R=-W_infty`, plus the
  restricted `QW_lambda` sign check.
- Updated `docs/audits/README.md` and
  `docs/audits/source-interface-discharge-audit.md` to reference the new sign
  bridge package.
- Added the rule to root `AGENTS.MD`: before final certification, the Lean exit
  must expose the sign bridge instead of accepting opaque route-local
  `fullWeilPositivity : Prop`.
- No Lean files were edited in this step and no Lean build was run.

2026-06-27

- Added `docs/audits/source-object-definition-ledger.md`.
- The ledger turns the remaining formal gate "source object definitions" into
  concrete replacement rows for `TestFunction`, `SemilocalModelSymbols`,
  `WeilFormSymbols`, `ArchimedeanTraceSymbols`, and
  `FiniteVanishingCriterionPackage`.
- It records, for each symbolic Lean field, the source object needed, source
  line evidence, bridge theorem required, and the failure mode if the object
  stays opaque.
- Updated `docs/audits/README.md` and
  `docs/audits/source-interface-discharge-completion-audit.md` to point to the
  ledger.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/source-test-convolution-compatibility.md`.
- This proof package attacks the first source-object replacement gate:
  `SourceTestFunctionCompatibility` and `SourceConvolutionSquareReadOff`.
- It ties the CCM24 fixed-S support test, the CCM25 half-density test and
  convolution square `F_g=g^* * g`, and the CC20 Mellin/Fourier test to one
  source-backed object at proof-package level.
- Updated `docs/audits/README.md`,
  `docs/audits/source-object-definition-ledger.md`, and
  `docs/audits/source-interface-discharge-audit.md` to reference the package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/ccm25-qw-psi-definition-sign-discharge.md`.
- This proof package attacks the CCM25 global source-object replacement gate:
  `SourceQWDefinition`, `SourcePsiSignSplit`,
  `SourceGlobalPrimeIndexCoverage`, `SourceArchimedeanSignBridge`, and
  `SourcePoleNormalization`.
- It keeps the global source spine visible:
  `QW(f,g)=Psi(f^* * g)`,
  `Psi(F)=W_(0,2)(F)-W_R(F)-sum_p W_p(F)`, and `W_R=-W_infty`.
- Updated `docs/audits/README.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-interface-discharge-audit.md`, and
  `docs/audits/source-interface-discharge-completion-audit.md` to reference the
  package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/audits/source-object-replacement-consistency-audit.md`.
- The audit checks the four source-object replacement packages as one batch:
  CCM24 semilocal objects, CCM25 finite-prime indices, CC20 trace objects, and
  CC20 RH exit objects.
- It records five cross-package invariants: one source test, one lambda window,
  pointwise finite-prime terms, the sign bridge from `QW >= 0` to the CC20
  nonpositivity inequality, and transport from source RH to Mathlib RH.
- Tightened three presentation issues found during the audit: quantified the
  source index `n` in the CCM25 finite-prime package, included both
  support-square and no-defect trace read-off in the CC20 trace package, and
  included support/Fourier transport in the CCM24 semilocal combined result.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/ccm24-semilocal-object-normalization-discharge.md`.
- This source-object replacement package expands `SemilocalModelSymbols` into
  CCM24 source-owned components: fixed finite place set, support window,
  common source test, canonical coordinate `V_S=M_S U_S`, eta/theta support
  transport, bounded comparison with inverse, trace-ideal preservation through
  comparison, and fixed-window Sonin exhaustion.
- Updated `docs/audits/README.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-interface-discharge-audit.md`, and
  `docs/audits/source-interface-discharge-completion-audit.md` to reference the
  package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/cc20-rh-exit-object-normalization-discharge.md`.
- This source-object replacement package expands the compact
  `FiniteVanishingCriterionPackage` into source-owned components:
  `F={0,1/2,1}`, finite-set admissibility against the CC20 non-trivial-zero
  predicate, route triple vanishing as CC20 Mellin vanishing on `F`, route full
  positivity as the CC20 Weil inequality, CC20 Proposition C.1, and the
  source-RH-to-Mathlib-RH definition bridge.
- Updated `docs/audits/README.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-interface-discharge-audit.md`, and
  `docs/audits/source-interface-discharge-completion-audit.md` to reference the
  package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/cc20-trace-object-normalization-discharge.md`.
- This source-object replacement package sharpens the CC20 trace gate from
  symbolic `ArchimedeanTraceSymbols` fields to source-backed targets: CC20
  trace test compatibility, Hilbert-Schmidt gate, trace-class and cyclicity
  template, positive trace `Tr(A^*A)`, support-square to no-defect trace
  read-off, Mellin half-density compatibility, and CC20 sign normalizations.
- Updated `docs/audits/README.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-interface-discharge-audit.md`, and
  `docs/audits/source-interface-discharge-completion-audit.md` to reference the
  package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/ccm25-finite-prime-index-normalization-discharge.md`.
- This source-object replacement package sharpens the finite-prime gate from
  coverage statements to source definitions: source prime-power index, global
  support, restricted lambda cut `1 < n <= lambda^2`, von Mangoldt weight
  `Lambda(n)`, source pairing `<g|T(n)g>`, and pointwise finite-prime term
  normalization.
- Updated `docs/audits/README.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-interface-discharge-audit.md`, and
  `docs/audits/source-interface-discharge-completion-audit.md` to reference the
  package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/ccm25-restricted-qwlambda-window-discharge.md`.
- This proof package attacks the restricted CCM25 source-object replacement
  gate: `SourceRestrictedQWLambdaFormula`,
  `SourceRestrictedPrimeIndexCoverage`, `SourcePoleNormalization`, and
  `SourceWindowLambdaContainment`.
- It ties `QW_lambda(g,g)`, `restrictedPrimeIndexSet lambda`, restricted pole
  pairing, and `WindowLambdaCompatibility` back to the global CCM25
  `QW/Psi` source spine.
- Updated `docs/audits/README.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-interface-discharge-audit.md`, and
  `docs/audits/source-interface-discharge-completion-audit.md` to reference the
  package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `formalization/source-object-interface-plan.md`.
- The plan maps the source-object replacement batch to the next Lean interface
  pass without editing Lean code.
- It requires an expanded `SourceObjectPackage` shape with common test,
  CCM24 semilocal, CCM25 Weil/finite-prime, CC20 trace, and CC20 RH-exit
  subpackages.
- It keeps `SemilocalModelSymbols`, `WeilFormSymbols`,
  `ArchimedeanTraceSymbols`, and `FiniteVanishingCriterionPackage` as derived
  views rather than final source evidence.
- Updated `formalization/lean-readiness.md` and `docs/audits/README.md` to
  point to the new interface plan.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/source-object-derived-compact-records.md`.
- The package proves, at proof-package level, that the expanded source-object
  packages can derive the existing compact route-facing records:
  `SemilocalModelSymbols`, `WeilFormSymbols`, `ArchimedeanTraceSymbols`, and
  `FiniteVanishingCriterionPackage`.
- It specifies the future Lean derivation layer:
  `ConnesWeilRH.Source.Objects` for expanded packages and
  `ConnesWeilRH.Source.ObjectDerivations` for projections to compact records.
- Updated `docs/audits/README.md` and
  `formalization/source-object-interface-plan.md` to reference the derivation
  package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `formalization/source-object-interface-risk-audit.md`.
- The audit defines pre-Lean blocking rules for the source-object interface
  pass: source objects must stay in `ConnesWeilRH/Source`, compact records must
  be derived views, named bridges must replace opaque bundled `Prop` fields,
  finite-prime normalization must remain pointwise, trace legality must precede
  trace read-off, and source RH must be transported to Mathlib RH explicitly.
- It records grep gates, build gate, and axiom-audit gate for the future Lean
  interface pass.
- Updated `docs/audits/README.md` and
  `formalization/source-object-interface-plan.md` to reference the risk audit.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `formalization/source-object-interface-workplan.md`.
- The workplan translates the source-object interface plan and risk audit into
  a file-level future Lean pass: add `ConnesWeilRH/Source/Objects.lean`, add
  `ConnesWeilRH/Source/ObjectDerivations.lean`, derive compact records, then
  wire source interfaces after the derivation layer builds.
- It records build order, grep gates, axiom-audit gate, review checklist, and
  rollback plan.
- Updated `docs/audits/README.md`,
  `formalization/source-object-interface-plan.md`, and
  `formalization/source-object-interface-risk-audit.md` to reference the
  workplan.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/source-object-definition-spine-discharge.md`.
- This mathematics-only proof package attacks the first remaining formal gate:
  source object definitions.
- It introduces the proof-package target
  `SourceDefinitionSpine(S,I,lambda,g)`, tying one common test `g`, one
  convolution square `F_g=g^* * g`, one CCM24 window, CCM25 Weil objects,
  CC20 trace objects, the CC20 finite-vanishing exit, and the Mathlib RH bridge
  into one source-owned dependency spine.
- Updated `docs/audits/README.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-interface-discharge-audit.md`,
  `docs/audits/source-interface-discharge-completion-audit.md`, and
  `docs/audits/source-object-replacement-consistency-audit.md` to point to the
  new spine package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/cc20-analytic-trace-legality-spine-discharge.md`.
- This mathematics-only proof package attacks the second remaining formal gate:
  analytic trace legality.
- It introduces the proof-package target
  `CC20AnalyticTraceLegalitySpine(S,I,lambda,g)`, forcing the order:
  operator identity, Hilbert-Schmidt witness, trace-class witness, per-move
  cyclicity witness ledger, ordinary positive trace, support-square trace,
  no-defect source trace, then CCM25 Weil-form read-off.
- Updated `docs/audits/README.md`,
  `docs/audits/source-interface-discharge-audit.md`,
  `docs/audits/source-interface-discharge-completion-audit.md`,
  `docs/audits/source-object-definition-ledger.md`, and
  `formalization/source-object-interface-risk-audit.md` to point to the trace
  legality spine package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/ccm25-finite-prime-normalization-spine-discharge.md`.
- This mathematics-only proof package attacks the third remaining formal gate:
  finite-prime normalization.
- It introduces the proof-package target
  `CCM25FinitePrimeNormalizationSpine(lambda,g)`, forcing the order:
  source prime-power atom, visibility in `F_g`, restricted lambda cut
  `1<n<=lambda^2`, source `Lambda(n)`, source `<g|T(n)g>`, pointwise finite
  prime term equality, then global or restricted finite-prime sums.
- Updated `docs/audits/README.md`,
  `docs/audits/source-interface-discharge-audit.md`,
  `docs/audits/source-interface-discharge-completion-audit.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-object-replacement-consistency-audit.md`, and
  `formalization/source-object-interface-risk-audit.md` to point to the
  finite-prime normalization spine package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/final-sign-bridge-spine-discharge.md`.
- This mathematics-only proof package attacks the fourth remaining formal gate:
  final sign bridge.
- It introduces the proof-package target `FinalSignBridgeSpine(g)`, forcing the
  order: `QW(g,g)=Psi(F_g)`, source `Psi` expansion, archimedean sign bridge,
  finite-prime local signs owned by the formula, pole sign in the CC20 local
  Weil sum, `QW(g,g)=-sum_v W_v(F_g)`, then
  `QW(g,g)>=0 -> sum_v W_v(F_g)<=0`.
- Updated `docs/audits/README.md`,
  `docs/audits/source-interface-discharge-audit.md`,
  `docs/audits/source-interface-discharge-completion-audit.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-object-replacement-consistency-audit.md`, and
  `formalization/source-object-interface-risk-audit.md` to point to the final
  sign-bridge spine package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/rh-definition-bridge-spine-discharge.md`.
- This mathematics-only proof package attacks the fifth remaining formal gate:
  RH definition bridge.
- It introduces the proof-package target `RHDefinitionBridgeSpine`, forcing the
  order: source zeta, Mathlib `riemannZeta`, source zero predicate, Mathlib zero
  equation plus negative-even and pole exclusions, source critical line,
  `s.re = 1/2`, then `_root_.RiemannHypothesis`.
- Updated `docs/audits/README.md`,
  `docs/audits/source-interface-discharge-audit.md`,
  `docs/audits/source-interface-discharge-completion-audit.md`,
  `docs/audits/source-object-definition-ledger.md`,
  `docs/audits/source-object-replacement-consistency-audit.md`, and
  `formalization/source-object-interface-risk-audit.md` to point to the RH
  definition-bridge spine package.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/audits/formal-gate-spine-consistency-audit.md`.
- This mathematics-only audit checks the five remaining formal-gate spine
  packages as one Lean-facing source-discharge target:
  source-definition, trace-legality, finite-prime normalization, final sign
  bridge, and RH definition bridge.
- The audit records seven cross-spine invariants: one `g` and `F_g`, one
  `(S,I,lambda)` tuple and window, trace legality before read-off, pointwise
  finite-prime terms before sums, finite-prime sign ownership by `Psi/QW`,
  sign equality before inequality direction, and source RH transport to
  Mathlib RH.
- Updated the audit index, source-interface completion audit,
  source-interface discharge audit, source-object replacement audit,
  Lean-readiness note, source-object interface plan, and source-object
  interface risk audit to point to the new formal-gate spine audit.
- Ran documentation hygiene checks over the current batch:
  `git diff --check`, ASCII scan, unfinished-marker scan, private-path scan,
  trailing-whitespace scan, and Lean-file status scan. The checks passed.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/cc20-analytic-trace-legality-theorem-contract.md`.
- This mathematics-only contract strengthens the CC20 trace-legality spine from
  proof-package order into formal/import theorem targets.
- The contract fixes required targets for `SourceTraceOperatorIdentity`,
  `SourceHilbertSchmidtForThetaSmoothedOperator`,
  `SourceTraceClassForPositiveSquare`,
  `SourcePositiveTraceEqualsOrdinaryTrace`, `SourcePositiveTraceNonnegative`,
  `SourceCyclicMoveWitnessLedger`, `SourceSupportSquareTraceAfterLegality`,
  `SourceNoDefectTraceAfterSupportSquare`, and
  `SourceBoundedComparisonTraceIdealTransport`.
- Updated the audit index, formal-gate spine audit, source-interface discharge
  audit, source-interface completion audit, source-object definition ledger,
  source-object replacement audit, Lean-readiness note, source-object
  interface plan, source-object interface risk audit, and source-object
  interface workplan to point to the new theorem contract.
- Used `research-stack`/Jina to confirm the CC20 paper identity and public PDF:
  Alain Connes and Caterina Consani, "Weil positivity and Trace formula, the
  archimedean place", arXiv:2006.13771.
- Ran documentation hygiene checks over the updated public docs:
  `git diff --check`, ASCII scan, unfinished-marker scan, private-path scan,
  trailing-whitespace scan, and Lean-file status scan. The checks passed.
- No Lean files were edited and no Lean build was run.
- No commit or push was made for this single-gate contract pass.

2026-06-28

- Opened the first accepted-source theorem decision records without touching
  Lean:
  `docs/audits/ccm24-source-interface-referee-decision-record.md`,
  `docs/audits/ccm25-source-interface-referee-decision-record.md`,
  `docs/audits/cc20-trace-source-interface-referee-decision-record.md`, and
  `docs/audits/s2-b1-trace-scale-referee-decision-record.md`.
- Added `docs/audits/accepted-source-review-dossier.md` as the ordered external
  review entry point.
- Updated README, the audit index, the theorem-upgrade ledger, the packet
  completion audit, and the certification status board to distinguish
  `decision record opened` from `accepted-source`.
- Current status: base source-interface rows and S2-B1 now have explicit
  theorem-decision records, but all verdicts remain pending external decision,
  accepted independent proof, or Lean theorem with axiom audit.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Downloaded official arXiv e-print source packages temporarily for CCM24
  `2310.18423`, CCM25 `2511.22755`, and CC20 `2006.13771` to reread the hard
  blocker source lines.
- Added `docs/audits/sonin-prolate-defect-source-readiness-audit.md`.
  It finds CC20 local prolate/Sonin ingredients and CCM24 semilocal Sonin
  comparison, but no source theorem directly proving that the fixed-S
  prolate/Sonin defect is exactly rank, pole, or endpoint-strip `Cdef`.
- Added `docs/audits/restricted-to-full-qw-source-readiness-audit.md`.
  It finds a CCM25 source-definition route: `QW_lambda` is defined as the
  restriction of `QW`, so after common-test and support bridges the route
  should use eventual equality `QW_lambda(g,g)=QW(g,g)` rather than spectral
  convergence.
- Updated the two theorem contracts and hard-blocker audits to reflect this
  split: Sonin/prolate remains a hard blocker; restricted-to-full QW is
  import-ready after object/support bridges.

2026-06-27

- Added `docs/proofs/source-object-definition-theorem-contract.md`.
- This mathematics-only contract strengthens the source-object definition spine
  from proof-package order into formal/import theorem targets.
- The contract fixes required targets for `SourceCommonTestAndConvolution`,
  `SourceRouteTupleFixed`, `SourceWindowControlsRestrictedRoute`,
  `SourceCCM25WeilObjects`, `SourceCC20TraceObjects`,
  `SourceCC20RHExitObjects`, and
  `SourceObjectPackageDerivesCompactRecords`.
- Linked the source-object definition theorem contract into the audit index,
  formal-gate spine audit, source-interface discharge audit, source-interface
  completion audit, source-object definition ledger, source-object replacement
  audit, Lean-readiness note, source-object interface plan, source-object
  interface risk audit, source-object interface workplan, and source-definition
  spine package.
- The five remaining formal gates now all have theorem-contract targets:
  source-object definitions, CC20 analytic trace legality, CCM25 finite-prime
  normalization, final sign bridge, and RH definition bridge.
- Ran documentation hygiene checks over the current public-doc batch:
  `git diff --check`, ASCII scan, unfinished-marker scan, private-path scan,
  trailing-whitespace scan, and Lean-file status scan. The checks passed.
- No Lean files were edited and no Lean build was run.
- Committed and pushed the larger theorem-contract milestone:
  `9c73dfb75c4231eaf522726e9b2f4fe61be20fa0`
  (`Add remaining formal gate theorem contracts`).
- Local signature verification passed with EDDSA key
  `828A1CFCEC8286BD8D671DF6F84F18CD20BE8255`.
- GitHub commit verification returned `verified=true` and `reason=valid`.

2026-06-27

- Added `docs/audits/source-object-theorem-discharge-ledger.md`.
- This mathematics-only audit advances the source-object definition gate from
  theorem-contract naming to row-by-row discharge criteria.
- The ledger covers seven rows:
  `SourceCommonTestAndConvolution`, `SourceRouteTupleFixed`,
  `SourceWindowControlsRestrictedRoute`, `SourceCCM25WeilObjects`,
  `SourceCC20TraceObjects`, `SourceCC20RHExitObjects`, and
  `SourceObjectPackageDerivesCompactRecords`.
- It records acceptance evidence, current repository evidence, discharge
  requirements, rejected shortcuts, and current status for each row.
- Linked the ledger into the audit index, source-interface discharge audit,
  source-interface completion audit, source-object definition ledger,
  source-object replacement audit, formal-gate spine audit, Lean-readiness note,
  source-object interface plan, source-object interface risk audit, and
  source-object interface workplan.
- Ran documentation hygiene checks over the current public-doc batch:
  `git diff --check`, ASCII scan, unfinished-marker scan, private-path scan,
  trailing-whitespace scan, and Lean-file status scan. The checks passed.
- No Lean files were edited and no Lean build was run.
- No commit or push was made for this small post-milestone step.

2026-06-27

- Added `docs/proofs/source-common-test-tuple-theorem-contract.md`.
- This mathematics-only contract advances rows 1 and 2 of the source-object
  theorem-discharge ledger from proof-package evidence to import-ready theorem
  targets.
- The contract fixes formal/import targets for `SourceCommonTestObject`,
  `SourceConvolutionSquareOwned`, `SourceRouteTupleFixed`,
  `SourceTupleCarriesWindowAndSquare`, and the combined
  `SourceCommonTestTupleContract`.
- Linked the contract into the audit index, source-object theorem-discharge
  ledger, source-interface discharge audit, source-interface completion audit,
  source-object definition ledger, source-object replacement audit,
  formal-gate spine audit, Lean-readiness note, source-object interface plan,
  source-object interface risk audit, source-object interface workplan,
  source-test proof package, and source-object definition theorem contract.
- Rows 1 and 2 now have import-ready targets but remain undischarged until a
  Lean theorem or accepted source theorem proves them with audited hypotheses.
- Ran documentation hygiene checks over the current public-doc batch:
  `git diff --check`, ASCII scan, unfinished-marker scan, private-path scan,
  trailing-whitespace scan, and Lean-file status scan. The checks passed.
- No Lean files were edited and no Lean build was run.

2026-06-27

- Added `docs/proofs/rh-definition-bridge-theorem-contract.md`.
- This mathematics-only contract strengthens the RH definition bridge spine
  from proof-package order into formal/import theorem targets.
- The contract fixes required targets for `SourceZetaEqualsMathlibZeta`,
  `SourceZeroToMathlibZero`, `MathlibZeroToSourceZero`,
  `SourceNontrivialZeroNoNegativeEven`, `SourceNontrivialZeroNoPole`,
  `MathlibHypothesesToSourceNontrivialZero`,
  `SourceCriticalLineIffReEqHalf`, `SourceRHImpliesMathlibRH`, and
  `MathlibRHImpliesSourceRH`.
- Confirmed local Mathlib evidence:
  `.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean`
  defines `_root_.RiemannHypothesis` through `riemannZeta s = 0`, negative-even
  exclusion, `s != 1`, and `s.re = 1/2`; it also records the negative-even
  trivial zeros.
- Updated the audit index, formal-gate spine audit, source-interface discharge
  audit, source-interface completion audit, source-object definition ledger,
  source-object replacement audit, Lean-readiness note, source-object
  interface plan, source-object interface risk audit, source-object interface
  workplan, and RH definition spine package to point to the new theorem
  contract.
- Ran documentation hygiene checks over the updated public docs:
  `git diff --check`, ASCII scan, unfinished-marker scan, private-path scan,
  trailing-whitespace scan, and Lean-file status scan. The checks passed.
- No Lean files were edited and no Lean build was run.
- No commit or push was made for this single-gate contract pass.

2026-06-27

- Added `docs/proofs/final-sign-bridge-theorem-contract.md`.
- This mathematics-only contract strengthens the final CCM25-to-CC20 sign
  bridge spine from proof-package order into formal/import theorem targets.
- The contract fixes required targets for `SourceQWUsesCommonTest`,
  `SourcePsiSignExpansion`, `SourceArchimedeanSignBridge`,
  `SourceFinitePrimeSignOwnedByFormula`, `SourcePoleSignInCC20LocalSum`,
  `SourceQWEqualsNegCC20WeilSum`, and
  `SourceQWNonnegativeToCC20Nonpositive`.
- Updated the audit index, formal-gate spine audit, source-interface discharge
  audit, source-interface completion audit, source-object definition ledger,
  source-object replacement audit, Lean-readiness note, source-object
  interface plan, source-object interface risk audit, source-object interface
  workplan, and final sign spine package to point to the new theorem contract.
- Ran documentation hygiene checks over the three-contract batch:
  `git diff --check`, ASCII scan, unfinished-marker scan, private-path scan,
  trailing-whitespace scan, and Lean-file status scan. The checks passed.
- No Lean files were edited and no Lean build was run.
- This batch is large enough for a signed milestone commit after staged hygiene:
  it contains CC20 trace-legality, CCM25 finite-prime normalization, and final
  sign-bridge theorem contracts.

2026-06-27

- Added `docs/proofs/ccm25-finite-prime-normalization-theorem-contract.md`.
- This mathematics-only contract strengthens the CCM25 finite-prime
  normalization spine from proof-package order into formal/import theorem
  targets.
- The contract fixes required targets for `SourcePrimePowerIndexFactorization`,
  `SourceGlobalPrimePowerSupport`, `SourceRestrictedPrimePowerSupport`,
  `SourceVisiblePrimePowerBeforeLambdaCut`,
  `FixedSVisiblePrimeSetBeforeLimit`,
  `SourceVonMangoldtWeightNormalization`,
  `SourcePrimePowerPairingNormalization`,
  `SourceFinitePrimeTermPointwiseNormalization`, and
  `SourceFinitePrimeFormulaOwnsSign`.
- Updated the audit index, formal-gate spine audit, source-interface discharge
  audit, source-interface completion audit, source-object definition ledger,
  source-object replacement audit, Lean-readiness note, source-object
  interface plan, source-object interface risk audit, and source-object
  interface workplan to point to the new theorem contract.
- Used `research-stack`/Jina to search for the CCM25 paper identity by the
  project arXiv/id terms. The search did not directly confirm the paper
  identity in this session, so the public contract relies only on the
  project-audited source-file anchors `mc2arXiv.tex:445-470,530-540`.
- Ran documentation hygiene checks over the updated public docs:
  `git diff --check`, ASCII scan, unfinished-marker scan, private-path scan,
  trailing-whitespace scan, and Lean-file status scan. The checks passed.
- No Lean files were edited and no Lean build was run.
- No commit or push was made for this single-gate contract pass.

2026-06-28

- Split Row 6 of `ConnesWeilRH.Route.SignDefect` into named Lean-visible
  pieces:
  `SourceEndpointStripTermsCdefIndexed`,
  `SourceEndpointStripTraceNormDomination`,
  `SourceEndpointStripRemainderCdefBound`,
  `SourceEndpointStripFixedTestCdefExhaustion`, and
  `EndpointStripCdefDominationData`.
- Updated `SourceEndpointStripRemainderCdefDomination` so `L.cdefExhausts`
  now comes through the Row 6 data projection instead of a bare conjunction.
- `lake build ConnesWeilRH.Route.SignDefect`, `lake build ConnesWeilRH.Route.Ledger`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and `lake build ConnesWeilRH`
  all completed successfully in the WSL ext4 mirror.
- `#print axioms` for the new Row 6 projection theorems showed only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Avoided a recurrence of the earlier PowerShell/WSL sync pitfall by copying
  the Windows worktree into WSL without deleting the Windows source tree.

2026-06-28

- Split Row 7 of `ConnesWeilRH.Route.SignDefect` into named Lean-visible pieces:
  `SourcePositiveTraceRemainderOwnership`,
  `TransportedSourceRemainderPartition`,
  `EndpointStripRemainderBoundForRow7`,
  `PositiveTraceToRestrictedLowerBound`, and
  `NoHiddenPositiveDefectOutsideCdefData`.
- Updated `NoHiddenPositiveDefectOutsideCdef` so the row is carried by an
  existential data package instead of a bare conjunction.
- `lake build ConnesWeilRH.Route.SignDefect`, `lake build ConnesWeilRH.Route.Ledger`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and `lake build ConnesWeilRH`
  all completed successfully after the Row 7 split.
- The first attempt at `#print axioms` hit name-resolution issues in the
  temporary audit script, so the temporary audit files were removed instead of
  being left behind.

2026-06-28

- Added `ConnesWeilRH/Route/Bridge.lean` to hold the restricted-to-full QW
  bridge and final sign bridge interfaces as explicit Lean data.
- The bridge module now carries:
  `RestrictedToFullQWLambdaThreshold`,
  `RestrictedToFullQWScalarRestrictionEquality`,
  `RestrictedToFullQWLowerBoundTransfer`,
  `RestrictedToFullQWBridgeData`,
  `RestrictedToFullQWBridgeContract`,
  `SourceQWUsesCommonTest`,
  `SourcePsiSignExpansion`,
  `SourceArchimedeanSignBridge`,
  `SourceFinitePrimeSignOwnedByFormula`,
  `SourcePoleSignInCC20LocalSum`,
  `SourceQWEqualsNegCC20WeilSum`,
  `SourceQWNonnegativeToCC20Nonpositive`,
  `FinalSignBridgeData`, and `FinalSignBridgeContract`.
- `lake build ConnesWeilRH.Route.Bridge`, `lake build ConnesWeilRH.Route.RouteTheorem`,
  and `lake build ConnesWeilRH` all completed successfully after the bridge
  module was added.
- The main Lean target now imports the bridge module directly from
  `ConnesWeilRH.lean`.

2026-06-28

- `ConnesWeilRH/Route/Bridge.lean` now builds in WSL and exposes the
  restricted-to-full QW bridge and final sign bridge as explicit Lean data
  objects.
- `lake build ConnesWeilRH.Route.Bridge`, `lake build ConnesWeilRH.Route.RouteTheorem`,
  and `lake build ConnesWeilRH` all passed after the bridge module sync.
- `#print axioms` on the bridge projections reported only
  `propext`, `Classical.choice`, and `Quot.sound`.

2026-06-28

- Added `RouteBridgeCertificate` to `ConnesWeilRH/Route/Bridge.lean` so the
  route can carry `SourceTraceReadOffData`, the restricted-to-full QW bridge,
  and the final sign bridge as one explicit Lean-visible certificate.
- The new certificate projections
  `restricted_to_full_qw_bridge_of_route_bridge_certificate` and
  `final_sign_bridge_of_route_bridge_certificate` build successfully and
  still report only `propext`, `Classical.choice`, and `Quot.sound` in
  `#print axioms`.

2026-06-28

- Refined `RouteCertificate` in `ConnesWeilRH/Route/RouteTheorem.lean` so it now
  carries `RouteBridgeCertificate` in addition to `SourceBackedFullPositivity`.
- `final_connes_weil_rh` now depends on the bridge certificate projections
  `restricted_to_full_qw_bridge_of_route_bridge_certificate` and
  `final_sign_bridge_of_route_bridge_certificate` before invoking the CC20
  exit criterion.
- `lake build ConnesWeilRH.Route.RouteTheorem` and `lake build ConnesWeilRH`
  both passed after this tightening.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `propext`, `Classical.choice`, and `Quot.sound`.

2026-06-28

- Removed the direct `positivity` field from `RouteCertificate` so the final
  theorem now reaches the CC20 exit only through `RouteBridgeCertificate`.
- Added `source_backed_full_positivity_of_route_bridge_certificate` as the
  bridge from `RouteBridgeCertificate` back to `SourceBackedFullPositivity`.
- `lake build ConnesWeilRH.Route.Bridge`, `lake build ConnesWeilRH.Route.RouteTheorem`,
  and `lake build ConnesWeilRH` all passed after the certificate tightening.
- `#print axioms` on the new bridge projections still reports only
  `propext`, `Classical.choice`, and `Quot.sound`.

2026-06-28

- Removed the unused `hcompat` local from `ConnesWeilRH/Route/Theorem1.lean`
  so the source trace read-off helper no longer carries a dead bridge witness.
- `lake build ConnesWeilRH.Route.Theorem1` and
  `lake build ConnesWeilRH.Route.RouteTheorem` both passed after syncing the
  WSL mirror with the Windows worktree edit.
- Re-ran `#print axioms ConnesWeilRH.Route.final_connes_weil_rh`; the result
  is still exactly `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Audited the current route theorem dependency chain and found no Lean-side
  constructors for `RouteInputs`, `SourceBackedFixedSTest`, `CC20Interface`,
  `CCM24Interface`, or `CCM25Interface`.
- `ConnesWeilRH.Route.final_connes_weil_rh` therefore remains conditional on
  externally supplied route certificates; the repository does not yet contain
  a path that unconditionally produces RH from within Lean.

2026-06-28

- Began the four-part unconditionalization plan with the smallest target:
  `RHDefinitionBridge`.
- Added Lean-visible Mathlib target predicates
  `MathlibNontrivialZero` and `MathlibCriticalLine`, plus component-level
  no-drift theorems:
  `source_nontrivial_zero_iff_mathlib`,
  `source_critical_line_iff_mathlib`, and the standard-bridge specializations.
- `lake build ConnesWeilRH.Source.RHDefinition`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` passed in the WSL ext4 mirror.
- `#print axioms` for `source_rh_iff_mathlib`,
  `standard_source_rh_iff_mathlib`,
  `standard_source_nontrivial_zero_iff_mathlib`, and
  `standard_source_critical_line_iff_mathlib` reports only
  `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Continued the unconditionalization plan with the CC20 finite-vanishing exit
  wrapper in `ConnesWeilRH/Source/CC20RHExit.lean`.
- Added Lean-visible exit projections
  `criterion_source_output`, `criterion_to_mathlib_rh`,
  `standard_criterion_to_mathlib_rh`, and
  `standard_criterion_output_iff_mathlib`. These do not prove CC20 Proposition
  C.1; they make the route exit explicitly factor through source RH and then
  through the standard Mathlib RH bridge.
- `lake build ConnesWeilRH.Source.CC20RHExit`,
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Route.RouteTheorem`, and
  `lake build ConnesWeilRH` passed in the WSL ext4 mirror.
- `#print axioms` for the new CC20 exit wrapper theorems reports only
  `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Started the CCM25 finite-prime normalization part of the four-part plan by
  strengthening
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeCertificate.lean`.
- Added direct certificate projections for fixed-`lambda` finite-prime data:
  `one_lt_lambda_of_certificate`, `visible_iff_of_certificate`,
  `global_exact_of_certificate`, `restricted_exact_of_certificate`,
  `visible_atoms_in_lambda_cut_of_certificate`, and
  `term_normalization_of_certificate`.
- This is a concrete-support strengthening only. It still does not construct a
  full `CCM25Interface` or prove the broad `forall lambda`
  `FinitePrimeNormalizationStatement`.
- `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH` passed in the WSL ext4 mirror.
- `#print axioms` for the new finite-prime certificate projections reports
  only `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Extended the CCM25 finite-prime work from fixed-`lambda` projections to a
  broad-interface constructor.
- Added
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeInterface.lean`, defining
  `FixedLambdaCertificatesForTest` and
  `FixedLambdaCertificatesForAllTests`, and proving that certificates for every
  `lambda > 1` imply `FinitePrimeVisibilityStatement` and
  `FinitePrimeNormalizationStatement`.
- Added `ConnesWeilRH/Source/CCM25Concrete/Interface.lean`, defining
  `ConcreteCCM25Rows` and `ccm25_interface_of_concrete_rows`. This constructs
  a `CCM25Interface` from explicit rows for `QW`, `Psi`, `QW_lambda`,
  fixed-`lambda` finite-prime certificates, and pole normalization.
- This is a real Lean constructor layer for `CCM25Interface`, but it still
  assumes the analytic CCM25 rows as input; those rows are not yet derived from
  source-paper definitions.
- `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH` passed in the WSL ext4 mirror.
- `#print axioms` for the finite-prime interface bridge and the new
  `CCM25Interface` constructor reports only
  `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Further strengthened the CCM25 finite-prime concrete layer so pointwise term
  normalization must pass through named source arithmetic data.
- Added `SourceFinitePrimeAtomData` and
  `SourceFinitePrimeAtomNormalization` in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerTerm.lean`. The new atom data
  separates source prime-power status, visibility, source von Mangoldt weight,
  source prime-power pairing, weight read-off, pairing read-off, and pointwise
  finite-prime term read-off before deriving the old
  `finitePrimeTerm = vonMangoldtWeight * primePowerPairing` statement.
- Added atom-level fixed-`lambda` certificates and bridges in
  `FinitePrimeCertificate.lean` and `FinitePrimeInterface.lean`, so
  atom-level certificates for every `lambda > 1` imply the broad
  `FinitePrimeNormalizationStatement`.
- Extended `ConnesWeilRH/Source/CCM25Concrete/Interface.lean` with
  `ConcreteCCM25AtomRows` and `ccm25_interface_of_atom_rows`, allowing a
  `CCM25Interface` to be constructed from QW/Psi/QW_lambda/pole rows plus
  atom-level finite-prime certificates.
- This still does not prove the CCM25 arithmetic rows from source definitions;
  it makes the required source Lambda and source pairing data Lean-visible
  before the finite-prime sum is used.
- `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH` passed in the WSL ext4 mirror.
- `#print axioms` for the new atom-level finite-prime normalization and
  `CCM25Interface` constructor theorems reports only
  `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Added `ConnesWeilRH/Source/CCM25Concrete/PrimePowerArithmetic.lean` to tie
  the CCM25 finite-prime arithmetic layer to Mathlib instead of leaving the
  prime-power index and von Mangoldt weight as fully route-local names.
- The new module defines `SourcePrimePowerIndex n := IsPrimePow n` and
  `SourceVonMangoldtWeight n := ArithmeticFunction.vonMangoldt n`, using
  Mathlib evidence from
  `.lake/packages/mathlib/Mathlib/Algebra/IsPrimePow.lean:27,70,128` and
  `.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean:65,73,89`.
- Added `SourceFinitePrimeArithmeticData` and
  `SourceFinitePrimeArithmeticNormalization`. These records still keep the
  source pairing `<g|T(n)g>` as read-off data because the current phase-1
  boundary has `TestFunction := Type` and no evaluation/operator model.
- Extended `PrimePowerTerm.lean`,
  `FinitePrimeCertificate.lean`, `FinitePrimeInterface.lean`, and
  `Interface.lean` so arithmetic certificates imply the previous atom-level
  certificates, fixed-`lambda` certificates, finite-prime normalization, and
  `CCM25Interface` constructor.
- This closes a Lean-visible arithmetic drift loophole for `IsPrimePow` and
  `Lambda(n)`. It does not prove CCM25 analytic rows, source support
  exactness, source pairing normalization, or the `QW_lambda -> QW` bridge.
- WSL ext4 builds passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new arithmetic bridge and arithmetic-row
  `CCM25Interface` constructors reports only
  `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Tightened the CCM25 finite-prime support/certificate layer so arithmetic
  certificates no longer start from an arbitrary support predicate plus a
  separate `supportIndexReadOff` field.
- Added
  `PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda`, whose
  visible/global/restricted exactness statements directly use
  `PrimePowerArithmetic.SourcePrimePowerIndex n`.
- Added
  `PrimePowerSupport.support_skeleton_of_arithmetic_support_skeleton` as the
  compatibility conversion into the older generic support skeleton.
- Updated
  `FinitePrimeCertificate.FixedLambdaFinitePrimeArithmeticCertificate` so its
  `support` field consumes the arithmetic support skeleton directly; the
  previous `supportIndexReadOff` escape hatch was removed.
- This closes another Lean-visible finite-prime drift route: the strongest
  CCM25 arithmetic certificate path now fixes the prime-power predicate at the
  support-source boundary. The older generic support/exact records still exist
  as compatibility targets, but arithmetic certificates do not originate from
  them.
- WSL ext4 builds passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new support skeleton conversion, arithmetic
  certificate support-index theorem, exact support conversion, and arithmetic
  finite-prime normalization path reports only
  `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Added `ConnesWeilRH/Source/CCM25Concrete/PrimePowerPairing.lean` to name the
  CCM25 source `<g|T(n)g>` pairing before it is multiplied by `Lambda(n)`.
- The new `SourcePrimePowerPairingModel` records the source convolution square,
  forward evaluation, inverse evaluation, normalizing factor, source
  `T(n)`-pairing value, and the formula
  `sourceTPairing = sourceNormalizationFactor *
  (sourceForwardEvaluation + sourceInverseEvaluation)`.
- The current Lean boundary still has `TestFunction := Type`, so the module
  deliberately does not pretend to define actual evaluation at `n` or
  `n^(-1)`. The normalizing factor is named as source data rather than
  fake-formalizing `n^(-1/2)` at this phase.
- Extended `SourceFinitePrimeArithmeticData` with a `sourcePairing` field and
  added `source_arithmetic_data_of_pairing_data`, so arithmetic atom data can
  now be built from a named source pairing object instead of a bare real
  `sourcePrimePowerPairing`.
- Added the theorem `source_pairing_formula`, exposing that the route
  `W.primePowerPairing n f g` reads off as the source normalizing factor times
  the two source evaluation legs.
- WSL ext4 builds passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerPairing`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the new pairing formula/read-off, pairing-to-arithmetic
  constructor, arithmetic source pairing formula, and downstream finite-prime
  normalization path reports only
  `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Tightened the CCM25 prime-power pairing normalizing factor in
  `ConnesWeilRH/Source/CCM25Concrete/PrimePowerPairing.lean`.
- Added `SourceNormalizationFactor n := 1 / Real.sqrt (n : Real)`, using
  Mathlib's `Real.sqrt` from
  `.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:112`.
- Added `normalizationFactorReadOff` to
  `SourcePrimePowerPairingModel`, so the source `T(n)` pairing model no longer
  carries an arbitrary normalizing scalar.
- Added `source_prime_power_pairing_formula_inv_sqrt` and
  `source_prime_power_pairing_formula_real_sqrt`, exposing
  `W.primePowerPairing n f g =
  (1 / Real.sqrt (n : Real)) *
  (sourceForwardEvaluation + sourceInverseEvaluation)`.
- Added arithmetic-level projections
  `source_pairing_formula_inv_sqrt` and `source_pairing_formula_real_sqrt`.
- This closes the normalizing-factor drift in the CCM25 pairing layer. It does
  not yet formalize source evaluation at `F_g(n)` or `F_g(n^(-1))`; the
  forward and inverse evaluation legs remain explicitly named source data until
  the test-function/evaluation model is introduced.
- WSL ext4 builds passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerPairing`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the normalizing-factor read-off, inv-sqrt pairing
  formulas, arithmetic projections, and downstream finite-prime normalization
  path reports only `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Added `ConnesWeilRH/Source/CCM25Concrete/PrimePowerEvaluation.lean` to name
  the CCM25 source evaluation object for finite-prime pairings.
- The new module defines source evaluation points
  `SourceForwardPoint n := (n : Real)` and
  `SourceInversePoint n := (n : Real)^-1`, plus
  `SourceConvolutionEvaluationModel`, which records the common source
  convolution square `W.convolutionStar f g`, the forward/inverse source
  points, and the two source evaluation values.
- Extended `SourcePrimePowerPairingModel` with a `sourceEvaluation` field and
  read-off fields connecting `sourceForwardEvaluation` and
  `sourceInverseEvaluation` to the evaluation model's forward and inverse
  values.
- Added
  `source_prime_power_pairing_formula_source_evaluations` and
  `source_pairing_formula_source_evaluations`, exposing the route pairing as
  `(1 / Real.sqrt (n : Real)) *
  (sourceEvaluation.forwardValue + sourceEvaluation.inverseValue)`.
- This closes the previous gap where the two evaluation legs were just loose
  real fields on the pairing model. It still does not define actual function
  application for `TestFunction`; that requires a later source test/evaluation
  interface replacing the current phase-1 `TestFunction := Type` boundary.
- WSL ext4 builds passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluation`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerPairing`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the evaluation point read-offs, source evaluation
  read-offs, source-evaluation pairing formula, arithmetic projection, and
  downstream finite-prime normalization path reports only
  `[propext, Classical.choice, Quot.sound]`.

2026-06-28

- Added `ConnesWeilRH/Source/CCM25Concrete/PrimePowerTest.lean` to introduce a
  common CCM25 source test/evaluation interface for the finite-prime layer.
- The new `SourceTestEvaluationInterface` records the source left/right tests,
  the common source convolution square, and a source finite-prime visibility
  predicate together with the read-off
  `W.finitePrimeAtomVisible n sourceConvolutionSquare <->
  sourceAtomVisible n`.
- Updated `PrimePowerEvaluation.SourceConvolutionEvaluationModel` so each
  prime-power evaluation model now carries a `sourceTest` and reads its
  `sourceConvolutionSquare` from that common test interface.
- Updated
  `PrimePowerSupport.SourcePrimePowerArithmeticSupportSkeletonAtLambda` so
  arithmetic support exactness uses the same `sourceTest.sourceAtomVisible`
  predicate rather than an independent `sourceAtomVisible : Nat ->
  TestFunction -> Prop` field.
- This closes a Lean-visible object-drift loophole between finite-prime
  visibility and prime-power pairing evaluation: both now project from the
  same source convolution-square package. It still does not define the
  analytic test-function class or actual evaluation operation behind the
  phase-1 `TestFunction := Type` boundary.
- WSL ext4 builds passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTest`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluation`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Interface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete`, and
  `lake build ConnesWeilRH`.
- `#print axioms` for the common test read-offs, route/source visibility
  equivalence, evaluation square read-off, arithmetic support conversion,
  exact support conversion, and downstream finite-prime normalization path
  reports only `[propext, Classical.choice, Quot.sound]`.

2026-06-29

- Hardened `ConnesWeilRH/Route/SignDefect.lean` Rows 4 through 7 against
  existential witness drift.
- Replaced the remaining `exists row, True` shells for
  `FixedSProjectionDefectNormalFormForSourceRemainder`,
  `SourceRankPoleLedgerIdentification`,
  `SourceEndpointStripRemainderCdefDomination`, and
  `NoHiddenPositiveDefectOutsideCdef` with direct data-bearing abbreviations
  over their corresponding records.
- Changed the Row 5 rank/pole identification interface from an internal
  existential `lambda` to a fixed-`lambda` data object:
  `SourceRankPoleLedgerIdentification inputs g lambda L`. This forces Row 5
  rank/pole removal, Row 6 endpoint-strip `Cdef` domination, and Row 7
  no-hidden-positive-defect evidence to use the same cutoff.
- Updated Row 7 wrappers `TransportedSourceRemainderPartition` and
  `PositiveTraceToRestrictedLowerBound` from `Prop` conjunctions to structures,
  because they now carry Type-level endpoint-strip and rank/pole evidence.
- Removed all `.choose` / `choose_spec` projections from
  `ConnesWeilRH/Route/SignDefect.lean`; field projections now read the explicit
  row data directly.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.SignDefect`,
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `[propext, Classical.choice, Quot.sound]`.
- This is Lean interface hardening only. It does not prove the CC20 analytic
  source rows, accepted-source certification, or unconditional RH.

2026-06-29

- Hardened the trace-to-Weil read-off and ledger evidence interfaces after the
  sign/defect Row 4-7 data pass.
- In `ConnesWeilRH/Route/Theorem1.lean`, changed `TraceWeilCompatibility` from
  `exists row, True` to a direct abbreviation for
  `TraceWeilCompatibilityData`. The compatibility object now exposes
  `FullTraceReadOffEquality`, `RestrictedTraceReadOffEquality`,
  `FullTraceReadOffSource`, and `RestrictedTraceReadOffSource` directly.
- Changed `trace_weil_compatibility_of_sources` from a theorem constructing an
  existential shell into a `def` returning the data object. This keeps the
  CC20 no-defect trace to CCM25 `QW` equality and the support-square trace to
  `QW_lambda` equality inspectable by downstream route code.
- In `ConnesWeilRH/Route/Ledger.lean`, changed `SourceBackedLedgers` from an
  existential sign/defect classification to explicit fields:
  `lambda : Real` and
  `signDefectClassification : SourceSignDefectClassification inputs g lambda L`.
  This preserves the same sign/defect cutoff at the ledger layer and removes
  the previous `choose_spec` projections.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Ledger`, and
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `[propext, Classical.choice, Quot.sound]`.
- Remaining intentional weak/compatibility points include the legacy
  `LegacySourceFinitePrimeSignOwnedByFormula` existential package bridge and
  `FinitePrimeInterface` `Nonempty` wrappers for broad forall-lambda
  certificate compatibility. These are not the main route witness drift fixed
  in this pass.
- This is still source-conditional Lean interface hardening, not a proof of
  unconditional RH.

2026-06-29

- Hardened the CCM25 finite-prime fixed-`lambda` certificate interface.
- In `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeInterface.lean`, changed
  `FixedLambdaCertificatesForTest`, `FixedLambdaAtomCertificatesForTest`, and
  `FixedLambdaArithmeticCertificatesForTest` from `Prop` predicates returning
  `Nonempty` certificates into `Type 1` function interfaces returning the
  concrete certificate for each `lambda` and proof `1 < lambda`.
- Removed `Classical.choice` from the finite-prime visibility path:
  `finite_prime_visibility_of_fixed_lambda_certificates` now directly uses
  `h 2 ...` for the global normalization witness and `h lambda hlambda` for
  restricted visibility at the active cutoff.
- Updated conversion helpers from theorem/existence wrappers into data-returning
  `def` / `noncomputable def` values. The noncomputability comes from the
  arithmetic-to-atom certificate conversion, not from an existential witness.
- Marked the dependent CCM25 arithmetic row/interface/package constructors as
  `noncomputable` where they pass through the arithmetic-to-atom conversion:
  `Rows.atom_rows_of_arithmetic_rows`,
  `Rows.concrete_rows_of_arithmetic_rows`,
  `Interface.atom_rows_of_arithmetic_rows`,
  `Interface.concrete_rows_of_arithmetic_rows`,
  `Interface.ccm25_interface_of_arithmetic_rows`, and
  `Package.ccm25_interface`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface`,
  `lake build ConnesWeilRH.Source.CCM25Concrete.Package ConnesWeilRH.Source.CCM25Concrete ConnesWeilRH.Source.CCM25 ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `[propext, Classical.choice, Quot.sound]`.
- Remaining searched weak points after this pass are
  `ConnesWeilRH/Source/CC20.lean`'s finite-vanishing source package
  `Nonempty` and the legacy finite-prime formula `choose_spec` in
  `ConnesWeilRH/Route/Bridge.lean`. The main CCM25 finite-prime interface no
  longer uses `Nonempty` wrappers.
- This remains source-conditional Lean interface hardening. It does not prove
  CCM25 analytic finite-prime support from first principles or unconditional RH.

2026-06-29

- Hardened the remaining CC20 finite-vanishing source-obligation witness and
  the legacy finite-prime sign-owned wrapper.
- In `ConnesWeilRH/Source/CC20.lean`, added
  `CC20FiniteVanishingRhExitData`, carrying the exact `RHDefinitionBridge`, the
  matching `SourceFiniteVanishingCriterionPackage`, and the derived
  `CC20RHExitObjectPackage`.
- Replaced the old source-obligation statement
  `exists B, Nonempty (SourceFiniteVanishingCriterionPackage B)` with
  `CC20FiniteVanishingRhExitStatement`, a Prop that quantifies over the
  data-bearing record and asserts that its object package is exactly the
  package-to-object conversion. This keeps `SourceObligation.statement : Prop`
  while removing the `Nonempty` witness shell.
- Updated `finite_vanishing_rh_exit_holds` to build the new data-bearing
  statement from `CC20Interface.sourceFiniteVanishingRhExit` and
  `cc20.cc20RHExitObjectPackage`.
- In `ConnesWeilRH/Route/Bridge.lean`, changed
  `LegacySourceFinitePrimeSignOwnedByFormula` from an existential package
  wrapper into a structure with explicit `package` and `signOwned` fields, and
  removed the last `choose_spec` projection from
  `finite_prime_normalization_of_legacy_sign_owned_formula`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Source.CC20`,
  `lake build ConnesWeilRH.Source.CC20RHExit ConnesWeilRH.Source.CC20 ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`,
  and `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `[propext, Classical.choice, Quot.sound]`.
- A repository search over `ConnesWeilRH/**/*.lean` now finds no remaining
  `Nonempty`, `Classical.choice`, `choose_spec`, `.choose`, or `exists row,
  True`-style shells.
- This does not make the proof unconditional. It means the current Lean route
  interface no longer hides its remaining source-conditional assumptions behind
  these witness shells.

2026-06-29

- Hardened the CCM25 concrete/source interface boundary further.
- `CCM25Interface` now carries `qwDefinition` and `psiSign` as separate fields
  instead of bundling them into one pair-shaped proof object.
- Updated the concrete rows, global/component, and package layers to stop
  projecting `qwDefinition.1/.2`; the downstream route now consumes the named
  fields directly.
- Added explicit package-level read-off lemmas for the global/restricted
  finite-prime sums and the global/restricted common-atom sum equality.
- Added package-level source-test and index-data helpers so the finite-prime
  visibility path stays explicit instead of being rebuilt from positional
  tuple projections.
- WSL ext4 verification passed for the hardened slice:
  `lake build ConnesWeilRH.Source.CCM25
  ConnesWeilRH.Source.CCM25Concrete.Interface
  ConnesWeilRH.Source.CCM25Concrete.Global
  ConnesWeilRH.Source.CCM25Concrete.Package
  ConnesWeilRH.Route.Theorem1`.
- `#print axioms` on the new package lemmas and the route read-off helper still
  reports only `[propext, Classical.choice, Quot.sound]`.
- Logic boundary preserved: this is interface hardening only. It makes the
  CCM25 read-off path easier to audit, but it does not close the CC20
  analytic/sign-defect gap or upgrade the overall RH claim.

2026-06-29

- Hardened the trace-to-`QW`/`QW_lambda` read-off source legs in
  `ConnesWeilRH/Route/Theorem1.lean`.
- Changed `FullTraceReadOffSource` from a tuple-shaped `Prop` conjunction into
  a structure with named fields:
  `noDefectSourceReadOff`, `ccm25FullQWReadOff`, and
  `fullTraceReadOffEquality`.
- Changed `RestrictedTraceReadOffSource` from a tuple-shaped `Prop`
  conjunction into a structure with named fields:
  `ccm25RestrictedQWReadOff` and `restrictedTraceReadOffEquality`.
- Updated `trace_weil_compatibility_data_of_sources` to read the full and
  restricted equalities from named fields instead of positional projections
  `hfull.2.2` and `hrestricted.2`.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `[propext, Classical.choice, Quot.sound]`.
- This is still interface hardening. It makes the read-off source/equality
  legs inspectable but does not prove the analytic CC20 trace-class,
  cyclicity, no-defect trace, or restricted `QW_lambda` read-off from first
  principles.

2026-06-29

- Hardened the upstream fixed-S positive-trace evidence feeding the CC20 exit.
- In `ConnesWeilRH/Route/Theorem1.lean`, changed `CC20TraceLegality` from a
  tuple-shaped conjunction into a structure with named fields `traceClass` and
  `cyclicLegal`.
- Changed `CC20TraceSquareReadOff` into a structure with named fields
  `noDefectSourceReadOff` and `positiveTraceNonnegative`.
- Changed `FixedSPositiveTraceReadOff` from an existential `Prop` package into
  a data structure carrying the archimedean test, fixed `lambda`, trace
  legality, test/quotient compatibility, fixed-S support-square transport,
  no-defect read-off, CCM25 Weil-form read-off, and positive-trace
  nonnegativity.
- In `ConnesWeilRH/Route/Exhaustion.lean`, changed `FullWeilPositivity` from a
  tuple-shaped `Prop` into a structure carrying the fixed-S read-off, triple
  vanishing, and cleared ledgers.
- In `ConnesWeilRH/Basic.lean`, widened
  `WeilPositivityInput.fullWeilPositivity` from `Prop` to `Sort 1`. This is
  intentional: the final CC20 exit input can now carry structured positivity
  evidence instead of erasing it back into a proposition.
- Updated dependent declarations that return structured evidence from
  `theorem` to `def`, including fixed-S read-off and full-positivity
  projection helpers.
- Adjusted the route C1 full-positivity audit theorem so it no longer claims
  arbitrary Type-level evidence equality between separate fields; it now tracks
  the C1 projection through the named route projection.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1`,
  `lake build ConnesWeilRH.Route.Exhaustion`,
  `lake build ConnesWeilRH.Route.Bridge ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- `#print axioms ConnesWeilRH.Route.final_connes_weil_rh` still reports only
  `[propext, Classical.choice, Quot.sound]`.
- This preserves more route evidence at the final input boundary, but it still
  does not prove the analytic trace-class/cyclicity/no-defect/source read-off
  rows unconditionally.

2026-06-29

- Hardened `TestHalfDensityCompatibility`, `TateDirectionsToPoleLedger`,
  `TestAndQuotientCompatibility`, and `CCM25WeilFormReadOff` in
  `ConnesWeilRH/Route/Theorem1.lean`.
- Converted the remaining route gates from anonymous conjunctions into named
  structures with explicit fields and projection theorems.
- Added source-backed constructors for the new gate structures so the route no
  longer depends on hidden tuple-shaped evidence at this layer.
- WSL ext4 verification passed:
  `lake build ConnesWeilRH.Route.Theorem1 ConnesWeilRH.Route.Bridge
  ConnesWeilRH.Route.Exhaustion ConnesWeilRH.Route.RouteTheorem ConnesWeilRH`.
- The build previously failed once because I incorrectly put a proposition into
  a proof field; that was fixed by wiring `inputs.cc20.mellinHalfDensityConvention`
  into the new structure constructor.
- Logic boundary preserved: these are interface hardening changes only. The CC20
  trace/sign-defect bridge and the analytic source-discharge steps remain the
  real hard part.

2026-06-29

- Created `external-opinions/003-unconditional-rh-completion-plan.md`.
- The plan records the updated constraint that no external reviewer path is
  available, so accepted-source packets are now only Lean theorem
  specifications.
- It reframes the remaining route from source-conditional evidence to a
  Lean-only completion path: prove CCM24/CCM25/CC20 source rows in Lean, build
  `SourceObjectPackage`, construct the fixed-S/trace/route front ends without
  assumptions, construct `RouteCertificate`, and finish with an unconditional
  `_root_.RiemannHypothesis` theorem plus clean axiom audit.
- Boundary preserved: no row was marked accepted-source, and the repository
  still does not prove RH unconditionally.

2026-06-29

- Reviewed and corrected `external-opinions/003-unconditional-rh-completion-plan.md`.
- Fixed the plan's Lean verification criteria: theorem statement checks are now
  separated from `#print axioms`, because axiom audit reports dependencies and
  does not by itself prove that `RouteCertificate` or `SourceObjectPackage`
  disappeared from the theorem statement.
- Kept the nine accepted-source rows as audit/tracking rows instead of allowing
  deletion; Lean-only completion must mark them discharged by theorem and axiom
  audit.
- Removed the suggestion to add failing theorem stubs to imported Lean modules;
  unproved targets must stay as document contracts or non-imported scratch notes,
  not `axiom`, `constant`, `opaque`, `sorry`, or `admit`.
- Clarified the actual Lean package path
  `Source.SourceObject.SourceObjectPackage` and recorded that its current
  `Prop` fields must be filled by named theorems rather than renamed
  assumptions.
