# AGENTS.md


- MUST output all in English unless the user inputs Chinese directly.
- do not use Codegraph MCP in this project.
## [1] Project Overview

This repository is the dedicated working area for the Connes-Weil RH proof
manuscript and its future Lean formalization.

The control/archive repository keeps route history, experiments, and broad
project memory. This repository keeps the formal proof artifact:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md
```

Current status:

```text
v0.1 referee-readable source-conditional manuscript
```

This status does not claim journal acceptance, Clay acceptance, or Lean
verification.

## [2] Commands

This repository now has a Lake project for the segmented Lean scaffold.

Useful checks:

```text
git status --short
git diff --check
rg -n "task-marker|fix-marker|proof-sketch|named-gap" docs
rg -n "[^\x00-\x7F]" docs
rg -n "sorry|admit|axiom" formalization -g "*.lean"
rg -n "\bsorry\b|\badmit\b|^\s*(axiom|constant|opaque|unsafe)\b" ConnesWeilRH -g "*.lean"
```

Lean commands that work from the WSL ext4 mirror
`~/projects/Connes-Weil-RH-Proof`:

```text
lake update
lake exe cache get
lake build ConnesWeilRH
lake env lean /tmp/connes_axiom_audit.lean
```

Use `lake build ConnesWeilRH` for current route work. Do not use bare
`lake build` unless intentionally auditing the legacy copied
`RiemannHypothesis` target.

For narrow Lean work, build the smallest segment that contains the change:

```text
lake build ConnesWeilRH.Basic
lake build ConnesWeilRH.Source.CCM24
lake build ConnesWeilRH.Source.CCM25
lake build ConnesWeilRH.Source.CC20
lake build ConnesWeilRH.Route.Definitions
lake build ConnesWeilRH.Route.AdmissibleWindow
lake build ConnesWeilRH.Route.Ledger
lake build ConnesWeilRH.Route.Theorem1
lake build ConnesWeilRH.Route.Exhaustion
lake build ConnesWeilRH.Route.RouteTheorem
lake build ConnesWeilRH
```

## [3] Project Structure

```text
docs/manuscripts/
  Drafts and paper-facing manuscript files.

docs/audits/
  Source reread and readiness audits that connect the manuscript to external
  source files.

ConnesWeilRH/
  Segmented Lean formalization target for the current Connes-Weil route.

formalization/
  Future Lean 4 formalization workspace notes, readiness map, and setup.

README.md
  Public-facing repository overview.

MEMORY.md
  Local project memory and audit history.
```

## [4] Coding And Writing Conventions

- Keep mathematical claims source-backed.
- Distinguish source theorems, project lemmas, and external certification.
- Do not blur internal route-paper closure with public proof certification.
- Prefer theorem/lemma statements with explicit dependencies over prose-only
  claims.
- Keep manuscript text ASCII unless a target journal format requires otherwise.

## [4a] Lean Proof Integrity Rules

The Lean formalization must make the final claim hard to attack for definition
drift, hidden axioms, or toy-route leakage.

- Current operating rule after the source-discharge milestone: treat the
  Windows worktree `C:\Projects\Connes-Weil-RH-Proof` as the single source of
  truth. Do not treat the WSL ext4 mirror as authoritative. If WSL is used later
  for verification, sync from Windows first and copy results back deliberately.
- Current proof priority: finish the mathematical source-discharge proof
  packages before further Lean work. Do not add more Lean scaffolding or Lean
  interface refinements until Peter explicitly reopens the Lean phase.
- The final CC20 finite-vanishing RH exit must keep the sign bridge visible:
  route `QW(g,g) >= 0` may feed Connes--Consani Proposition C.1 only after the
  source normalization proves `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)`, so
  that it is exactly the CC20 inequality `sum_v W_v(...) <= 0`.
- Before final certification, replace any opaque route-local
  `fullWeilPositivity : Prop` exit with a Lean-visible bridge or equality
  proving `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)`. A bare nonnegative `QW`
  field is not enough to apply CC20 Proposition C.1.
- Current priority: finish the mathematical proof packages first, then continue
  Lean work. In particular, complete the three hard proof packages before
  adding more Lean scaffolding: `TestAndQuotientCompatibility`,
  `FixedSQuantizedSupportSquareTransport`, and
  `CdefNormFormula/FixedTestCdefExhaustion`. Lean should mirror proved
  mathematics, not hide unfinished analytic gaps behind finer interface names.
- The final theorem for RH must conclude Mathlib's canonical
  `_root_.RiemannHypothesis`, not a project-local replacement.
- A source theorem that concludes "RH" must be transported to Mathlib's exact
  `_root_.RiemannHypothesis` definition before certification. The bridge must
  expose the same zeta function, non-trivial-zero predicate, negative-even
  trivial-zero exclusion, `s != 1` exclusion, and critical-line equation
  `s.re = 1/2`.
- In `RHDefinitionBridge`, Mathlib non-trivial-zero evidence should remain the
  named `MathlibNontrivialZero` structure with `zeta_zero`,
  `not_negative_even`, and `not_pole` fields. Do not re-collapse this bridge
  to an anonymous nested conjunction whose `.1` / `.2.1` / `.2.2` projections
  can obscure component order.
- Project-local RH names may exist only as abbreviations or bridge predicates
  with proved equivalence to `_root_.RiemannHypothesis`.
- Every project-defined analytic object used in the final route must have a
  bridge theorem tying it to the manuscript/source-paper object it represents.
- Final-route certificates should consume source-backed bridge structures, not
  bare route-local `Prop` fields, whenever the corresponding source-interface
  object is available.
- Finite-prime visibility in the final route should pass through the CCM25
  finite-prime normalization interface. Do not reintroduce a direct
  `test.finitePrimesVisible` proof field on the final certificate.
- Full Weil positivity in the final route should pass through
  `SourceBackedFullPositivity`, not a direct call to
  `full_weil_positivity_of_fixed_s` from a final certificate.
- Ledger clearing in the final route should pass through
  `SourceBackedLedgers`, not a direct `LedgersCleared` proof field on the final
  certificate or positivity package.
- Triple vanishing in the final route should pass through
  `TripleVanishingSymbols` and `triple_vanishing_of_source_backed`, not a
  direct `test.tripleVanishing` proof field on the final certificate.
- Fixed-S trace read-off in the final route should pass through
  `SourceTraceReadOffData`, with separate trace-legality, no-defect read-off,
  and Weil-identification stages.
- `FixedSPositiveTraceReadOff` must remain distinct from
  `AdmissibleForTheorem1`. The former is Theorem 1 output evidence; the latter
  is an input-side admissibility gate.
- `SourceTraceReadOffData` should own the CC20 archimedean test object and the
  Hilbert-Schmidt gate used to derive trace-class/cyclicity legality. Do not
  move that gate back into a downstream positivity certificate.
- CC20 trace read-off bridges in `SourceTraceReadOffData` should pass through
  `FullTraceReadOffBridgeContract` and
  `RestrictedTraceReadOffBridgeContract`. Do not reintroduce bare
  `fullTraceReadOffBridge` or `restrictedTraceReadOffBridge` function fields
  that can return read-off source evidence disconnected from the supplied
  no-defect, full-`QW`, or restricted-`QW` inputs.
- CCM25 Weil-form read-off should pass through `CCM25WeilFormReadOff` derived
  from `inputs.ccm25.qwDefinition`, `inputs.ccm25.qwLambdaFormula`, and
  `inputs.ccm25.poleNormalization`. Do not reintroduce a loose
  `weilFormReadOff : Prop` field on `SourceBackedFullPositivity`.
- `CCM25WeilFormReadOff` should remain split into
  `CCM25FullQWReadOff` and `CCM25RestrictedQWReadOff`. The full leg should use
  `inputs.ccm25.qwDefinition`; the restricted leg should use
  `inputs.ccm25.qwLambdaFormula` and `inputs.ccm25.poleNormalization`.
- The CCM25 full leg should keep separate `CCM25QWDefinitionReadOff` and
  `CCM25PsiSignReadOff` propositions. The restricted leg should keep separate
  `WindowLambdaCompatibility`, `CCM25QWLambdaFormulaReadOff`, and
  `CCM25PoleNormalizationReadOff` propositions.
- CCM25 finite-prime sums must not use empty placeholder index sets such as
  `Finset.range 0`. Keep the global Weil-form sum indexed by
  `WeilFormSymbols.globalPrimeIndexSet` and the restricted `QW_lambda` sum
  indexed by `WeilFormSymbols.restrictedPrimeIndexSet lambda` until those sets
  are replaced by concrete prime-power support definitions.
- CCM25 finite-prime coverage is not exact support. A theorem proving
  `finitePrimeAtomVisible n F -> n in indexSet` is not enough for
  restricted-to-full or final-sign certification; the next finite-prime
  discharge must prove exact source prime-power support, lambda cut, weight,
  pairing, and pointwise atom normalization before any sum equality consumes
  the index set.
- CCM25 finite-prime support skeletons do not include coefficient
  normalization. A fixed-`lambda` support skeleton must be paired with a
  pointwise term-normalization theorem before deriving `ExactSupportAtLambda`
  or finite-prime visibility.
- CCM25 finite-prime arithmetic should move toward support-scoped data such as
  `SourceFinitePrimeArithmeticDataOnIndexSet`, not stronger full
  `forall n` atom assumptions. A record containing
  `SourcePrimePowerIndex n` for every natural number is too strong to be a
  final source interface; keep compatibility theorems only as migration
  bridges until downstream rows/packages are scoped to concrete index sets.
- CCM25 global/restricted formula components should expose and prefer scoped
  finite-prime evaluator read-offs, e.g.
  `psi_scoped_source_evaluator_of_formula_components`,
  `qw_scoped_source_evaluator_of_formula_components`, and
  `qw_lambda_formula_scoped_source_evaluator_of_formula_components`, before
  package and route layers consume finite-prime sums.
- Route-facing CCM25 read-off records should expose scoped finite-prime sums
  directly. In particular, `PackageBackedCCM25WeilFormReadOff` should keep
  scoped `Psi`, `QW`, and `QW_lambda` source-evaluator read-offs, and
  restricted-to-full scalar equality should use the scoped read-off chain as
  the main path. Full `forall n` evaluator sums may remain only as explicit
  compatibility bridges until all downstream rows are scoped.
- Restricted-to-full archimedean balance should be stored in scoped
  finite-prime form. `SourceArchimedeanContributionMatchesForRestriction`
  should expose the scoped restricted/global evaluator sums as its primary
  field; old full-sum balance statements should be projection/compatibility
  theorems derived from old/scoped package bridges, not the stored evidence.
- Common-atom archimedean balance should also be scoped first.
  `SourceCommonAtomArchimedeanContributionMatchesForRestriction` should use
  `source_common_restricted_finite_prime_evaluator_scoped_sum` and
  `source_common_global_finite_prime_evaluator_scoped_sum` as its stored
  balance. The old common full-sum balance belongs only in an explicit
  compatibility theorem such as
  `SourceCommonAtomFullArchimedeanContributionMatchesForRestriction`.
- CCM25 finite-prime support witness data should pass through the named
  records `SourceVisibleAtomData`, `SourceGlobalIndexData`, and
  `SourceRestrictedIndexData` from
  `PrimePowerSupport.lean`. Rows, interfaces, packages, and route bridges
  should not re-expose this evidence as anonymous
  `SourcePrimePowerIndex n ∧ atomVisible n` or
  `SourcePrimePowerIndex n ∧ atomVisible n ∧ SourceLambdaCut lambda n`
  tuples.
- CCM25 local finite-prime formula data should pass through
  `SourceFinitePrimeLocalFormulaData`. Do not let package or route layers
  consume independent fields for Von Mangoldt weight read-off, prime-power
  pairing source-evaluator formula, and finite-prime term formula when those
  fields are meant to come from the same local atom.
- CCM25 finite-prime sum read-offs should pass through
  `SourceGlobalFinitePrimeSumFormulaData` and
  `SourceRestrictedFinitePrimeSumFormulaData`. Do not expose separate concrete
  object fields for finite-prime term sums and Von Mangoldt pairing sums when
  both are meant to come from the same arithmetic normalization object.
- CCM25 formula components should expose global/restricted concrete-object
  equality through a common concrete object. Certificate equality alone is not
  enough to rule out drift in exact support, local formula data, or sum formula
  data attached to the concrete object.
- CC20 trace-class/cyclicity and archimedean trace-square outputs should be
  unpacked through named route wrappers such as
  `CC20TraceLegalityTemplateOutput` and
  `CC20ArchimedeanTraceSquareOutput`. Keep anonymous `.1` / `.2` projections
  localized at the source-interface unpacking boundary, not in downstream
  trace-to-read-off code.
- CCM25 exact finite-prime support should first be proved at a fixed
  `lambda`. Do not promote fixed-cutoff support coverage to
  `forall lambda` until the lambda quantifier, source support containment, and
  fixed-test choice of cutoff have been proved separately.
- When refining CCM25 finite-prime support in Lean, prefer a concrete
  source-prime-power record over arbitrary predicates. The fixed restricted cut
  should expose `1 < n` and `(n : Real) <= lambda^2` before it feeds
  `restrictedPrimeIndexSet lambda`.
- CCM25 finite-prime term normalization should be pointwise before summation.
  The local atom is `Lambda(n) * <g|T(n)g>`; the minus sign belongs to the
  surrounding `Psi` or `QW_lambda` formula and must not be absorbed into the
  pointwise atom and then subtracted again.
- `FinitePrimeVisibilityStatement` should remain split into three visible
  obligations: `GlobalPrimeIndexCoverageStatement`,
  `RestrictedPrimeIndexCoverageStatement`, and
  `FinitePrimeTermNormalizationStatement`. Do not collapse finite-prime
  visibility back into only the normalization equality
  `finitePrimeTerm = vonMangoldtWeight * primePowerPairing`.
- Final Weil identification should pass through `TraceWeilCompatibility`.
  First combine the CC20 no-defect trace read-off with the CCM25 Weil-form
  read-off, then derive the final identification. Do not collapse this into a
  one-step bridge that consumes all assumptions at once.
- `TraceWeilCompatibility` should include named read-off equalities for the
  CC20 source no-defect trace against CCM25 `QW`, and the CC20 support-square
  trace against CCM25 `QW_lambda`. Do not reduce it to a bare conjunction of
  `CC20NoDefectSourceReadOff` and `CCM25WeilFormReadOff`.
- The read-off equalities inside `TraceWeilCompatibility` should be produced
  through `FullTraceReadOffSource` and `RestrictedTraceReadOffSource` bridge
  fields, not accepted as direct equality proof fields on
  `SourceTraceReadOffData`.
- The full read-off bridge should consume `CC20NoDefectSourceReadOff`; the
  restricted read-off bridge should consume `CCM25WeilFormReadOff`. Do not add
  arbitrary `fullTraceReadOffSource : Prop` or `restrictedTraceReadOffSource :
  Prop` certificate fields.
- Read-off equality statements should be named separately as
  `FullTraceReadOffEquality` and `RestrictedTraceReadOffEquality`. Keep the
  source leg and equality leg visible; do not hide the equalities inside an
  undifferentiated source conjunction.
- The restricted parameter `lambda` in `CCM25WeilFormReadOff` should pass
  through `WindowLambdaCompatibility`, combining `1 < lambda` with the CCM24
  semilocal window compatibility for the source-backed fixed-`S` test. Do not
  treat `lambda` as a route-local free parameter.
- `WindowLambdaCompatibility` should expose the containment chain through
  `WindowSupportContainment`: source support in the CCM24 window, Fourier
  support in the same window, convolution-support transport, and
  `windowContainedInLambda window lambda` should remain visible before the
  final `lambdaCompatible window lambda` conclusion.
- CCM24 support-window transport must keep one source-backed window through the
  positive trace, CCM25 `QW_lambda` read-off, and endpoint-strip `Cdef`
  exhaustion. Do not let these steps use separate route-local cutoffs.
- The restricted-to-full `QW_lambda(g,g) -> QW(g,g)` step must pass through
  `RestrictedToFullQWBridgeContract`: common source test, fixed tuple/window,
  CCM25 restriction definition, and finite-prime support equality. Do not
  replace it with a bare limit, finite-operator spectral convergence, or
  determinant convergence claim.
- The sign/defect bridge must not be compressed into a single opaque
  `defectControlled` or `harmlessDefect` field. Keep the seven discharge rows
  from `docs/audits/sonin-prolate-defect-discharge-ledger.md` visible: source
  remainder object, remainder after `Q`, fixed-S Sonin transport,
  projection-defect normal form, rank/pole identification, endpoint-strip
  `Cdef` domination, and no-hidden-positive-defect equality.
- The CC20 source remainder orientation must remain visible in the
  sign/defect bridge: `W_infty=L-D` and `W_infty=S-E`. Positive trace
  functionals `L` or `S` do not imply Weil positivity until `D` or `E` after
  `Q` is classified as rank, pole, or endpoint-strip `Cdef`.
- Row 3 of the sign/defect bridge must pass through
  `CC20PostQRemainderFixedSSoninTransport`: the CC20 `D circ Q` / `E circ Q`
  bulk and boundary pieces must first be transported into the same fixed-S
  CCM24/Sonin/window coordinate as the positive trace and restricted
  `QW_lambda`. Do not apply projection-defect normal form or `Cdef`
  domination to route-local leftovers before this source-remainder transport
  is visible.
- CCM24's fixed-S Sonin isomorphism must not be used as automatic transport
  for CC20 post-`Q` derivative, endpoint, or series-tail terms. The warning
  `mainc2m24fine.tex:846-852` means Row 3 must expose
  `PostQDerivativeDomainCompatibility`, `PostQBoundaryEvaluationTransport`,
  and `PostQSeriesTailBoundedComparison` before Row 4 classification.
- `PostQDerivativeDomainCompatibility` is mandatory before classifying the
  CC20 post-`Q` bulk term. CC20 `weil-compo.tex:1260-1264` says the formal
  `D_u` identity cannot be applied directly to `xi_n,zeta_n`; do not treat
  `D_u xi_n` or `D_u zeta_n` as automatically transported by the CCM24 Sonin
  isomorphism.
- The derivative/domain Row 3 subcontract is classified as
  project-proof-required, not source-import-discharged. The next bridge is
  `FixedSPostQBulkGraphTransfer`; do not cite CC20 or CCM24 source lines as a
  completed fixed-S graph-domain transport theorem.
- `FixedSPostQBulkGraphTransfer` covers only the post-`Q` bulk term. It must
  prove source-to-log graph translation, fixed finite-S Euler graph
  boundedness, common `V_S` coordinate, and source-bulk equality before Row 4.
  It must not classify the term as `Cdef`.
- The `FixedSPostQBulkGraphTransfer` route-evidence proof package closes only
  the first Row 3 subcontract at project level. Boundary evaluation transport,
  series-tail bounded comparison, and combined Row 3 transport now also have
  route-evidence packages, but none of these packages is a source import, Lean
  theorem, or sign/defect discharge.
- `PostQBoundaryEvaluationTransport` is mandatory before classifying the CC20
  post-`Q` endpoint terms. Do not let triple vanishing, rank/pole ledgers, or
  endpoint-strip `Cdef` consume the lower moving endpoint or upper fixed
  endpoint terms until their fixed-S boundary functionals are named.
- `PostQSeriesTailBoundedComparison` is mandatory before passing from
  transported finite post-`Q` partial sums to the full transported source
  remainder. CC20 scalar tail convergence is not automatically fixed-S
  graph/trace-norm convergence for route `Cdef`.
- Row 4 of the sign/defect bridge now has a route-evidence proof package:
  `FixedSProjectionDefectNormalFormForSourceRemainder`. It may be used only to
  split the transported CC20 source remainder into no-strip channels and
  endpoint-strip projection-defect normal forms. It does not identify rank/pole
  ledgers, prove `Cdef` domination, or close the sign/defect bridge.
- The next mathematical target after Row 4 is
  `SourceRankPoleLedgerIdentification`: no-strip channels must be identified as
  the rank ledger or the pole ledger before triple vanishing is applied. This
  target now has a route-evidence proof package, but it is not a source import,
  Lean theorem, or sign/defect discharge.
- The next mathematical target after Row 5 is
  `SourceEndpointStripRemainderCdefDomination`: endpoint-strip normal-form
  channels must be matched to the exact route `Cdef_(S,I,lambda,J)(g)`
  trace-norm summands before the route can claim the defect is bounded by
  `Cdef`. This target now has a route-evidence proof package, but it is not a
  source import, Lean theorem, final read-off equality, or sign/defect
  discharge.
- The next mathematical target after Row 6 is
  `NoHiddenPositiveDefectOutsideCdef`: combine Rows 3 through 6 into the exact
  positive-trace read-off equality and prove that no fourth positive defect
  survives outside the killed rank/pole ledgers and endpoint-strip `Cdef`
  remainder. This target now has a route-evidence proof package, but it is not
  a source import, Lean theorem, restricted-to-full bridge, full Weil
  positivity theorem, or RH proof.
- The restricted-to-full `QW_lambda -> QW` step now has a route-evidence proof
  package:
  `RestrictedToFullQWBridgeContract`. It uses fixed-test support containment,
  finite-prime support stabilization, and the CCM25 restriction definition. It
  must not be described as accepted-source or Lean discharged until formalized
  or source-certified.
- The final CCM25-to-CC20 sign bridge now has a route-evidence proof package:
  `FinalSignBridgeContract`. It proves `QW(g,g)=-sum_v W_v(F_g)` and the
  direction `QW(g,g)>=0 -> sum_v W_v(F_g)<=0` at route-evidence level only.
- The RH definition bridge now has a route-evidence proof package:
  `RHDefinitionBridgeContract`. It targets Mathlib's exact
  `_root_.RiemannHypothesis` by exposing zeta equality, zero transport,
  negative-even exclusion, pole exclusion, and `s.re=1/2`. It is not a Lean
  theorem or accepted source import.
- The full current route now has a source-conditional route-evidence closure
  package: `SourceConditionalRHRouteClosure`. It composes sign/defect,
  restricted-to-full, final sign, CC20 finite-vanishing exit, and RH definition
  bridge into Mathlib RH at route-evidence level only. Do not describe it as
  unconditional RH, accepted source proof, journal proof, Clay proof, or Lean
  proof.
- The sign/defect bridge now has a referee-facing project proof package:
  `sonin-prolate-defect-referee-discharge.md`. Treat Rows 3 through 7 as one
  project proof chain closed at project proof-package level: fixed-S post-`Q`
  transport, projection-defect split, rank/pole identification, endpoint-strip
  `Cdef` domination, and no-hidden-positive-defect equality. Do not reopen
  Rows 3 through 7 as missing route packages unless a new source term is found.
  Rows 1 through 2 now also have a referee-facing project proof package:
  `cc20-source-remainder-rows1-2-referee-discharge.md`. Treat the full Rows
  1-7 sign/defect bridge as closed at project proof-package level. The
  remaining sign/defect certification work is accepted-source/external-review
  discharge of the CC20 source formulas and fixed-S transport, not another
  route-evidence package.
- In the Lean sign/defect route, Rows 4 through 7 must remain data-bearing
  records, not `exists row, True` shells. Row 5 rank/pole identification, Row 6
  endpoint-strip `Cdef` domination, and Row 7 no-hidden-positive-defect evidence
  must share the same fixed `lambda`; do not reintroduce an existential
  `lambda` inside Row 5 that can drift from the Row 6/7 cutoff.
- `TraceWeilCompatibility` must remain a data-bearing bridge exposing
  `FullTraceReadOffEquality`, `RestrictedTraceReadOffEquality`,
  `FullTraceReadOffSource`, and `RestrictedTraceReadOffSource`. Do not wrap it
  as `exists row, True`; downstream trace-to-`QW_lambda` work must be able to
  inspect both read-off equalities directly.
- `FullTraceReadOffSource` and `RestrictedTraceReadOffSource` must remain
  data-bearing structures, not tuple-shaped `Prop` conjunctions. The full leg
  must expose the CC20 no-defect source read-off, CCM25 full `QW` read-off, and
  full trace equality as named fields; the restricted leg must expose the
  CCM25 restricted `QW_lambda` read-off and restricted trace equality as named
  fields.
- `CC20TraceLegality`, `CC20TraceSquareReadOff`,
  `FixedSPositiveTraceReadOff`, and `FullWeilPositivity` are data-bearing
  structures. Do not collapse them back into tuple-shaped `Prop` conjunctions.
  `WeilPositivityInput.fullWeilPositivity` is intentionally `Sort 1` so the
  final CC20 exit can consume structured positivity evidence without erasing
  the fixed-S trace, no-defect read-off, `QW/QW_lambda`, and ledger fields.
- The final sign bridge must keep its major legs data-bearing:
  `SourceArchimedeanSignBridge`, `SourceFinitePrimeSignOwnedByPackage`, and
  `SourceQWEqualsNegCC20WeilSum` should expose named fields for trace legality,
  positive trace, signs/normalizations, Mellin convention, finite-prime
  normalization, global/restricted finite-prime sum read-offs, common-test
  usage, psi expansion, and pole-local-sum ownership. Do not collapse these
  back into positional `Prop` conjunctions.
- `PackageBackedCCM25WeilFormReadOff`, `SourceCommonTestTupleContract`, and
  `SourceQWUsesCommonTest` must remain named structures. The final sign bridge
  needs inspectable fields for window compatibility, package read-off,
  convolution-square compatibility, QW/Psi/QW_lambda formulas, pole
  normalization, and global/restricted finite-prime evaluator sums; do not
  reintroduce tuple projections such as `h.2.2.2` on these bridge inputs.
- `SourceBackedLedgers` must keep an explicit `lambda` field together with the
  `SourceSignDefectClassification inputs g lambda L` field. Do not hide the
  sign/defect classification behind `exists lambda`; ledger evidence should
  preserve the same cutoff used by the sign/defect bridge.
- The CCM25 finite-prime main interface must return explicit fixed-`lambda`
  certificates, not `Nonempty` wrappers consumed through `Classical.choice`.
  Keep `FixedLambdaCertificatesForTest`,
  `FixedLambdaAtomCertificatesForTest`, and
  `FixedLambdaArithmeticCertificatesForTest` as data-returning function types
  so global/restricted finite-prime visibility can inspect the certificate at
  the exact cutoff being used.
- `SourceObligation.statement` is a `Prop`, so source obligations cannot store
  Type-level evidence records directly. When a source row needs data-bearing
  evidence, define a data record plus a Prop statement that quantifies over the
  record and ties its fields together. For CC20 finite-vanishing, keep
  `CC20FiniteVanishingRhExitData` and `CC20FiniteVanishingRhExitStatement`
  instead of reverting to `exists B, Nonempty package`.
- Goal 1 theorem-base records such as `CCM24TheoremBase`,
  `CCM25TheoremBase`, and `CC20TheoremBase` are target/interface records, not
  analytic discharges by themselves. Do not fill them with toy `True`, empty
  finite-prime, or zero-symbol models and call the source row proved. A row is
  discharged only when those fields are proved from concrete source
  definitions or already audited Lean theorem dependencies.
- Legacy compatibility wrappers should also carry explicit data records when
  they are kept. In particular,
  `LegacySourceFinitePrimeSignOwnedByFormula` must keep the concrete package
  and `SourceFinitePrimeSignOwnedByPackage` evidence as fields, not an
  existential package consumed with `choose_spec`.
- All theorem-source assumptions must live in an explicit source-interface
  layer such as `ConnesWeilRH/Source/CCM24.lean`,
  `ConnesWeilRH/Source/CCM25.lean`, and
  `ConnesWeilRH/Source/CC20.lean`.
- No `axiom`, `constant`, `opaque`, `unsafe`, `sorry`, or `admit` may appear in
  final Connes-Weil route modules outside the approved source-interface layer.
- Before treating a Lean theorem as a proof artifact, run and record
  `#print axioms <theorem_name>`. The remaining axioms must be exactly the
  declared source theorem interfaces or Mathlib/kernel foundations.
- Legacy `RiemannHypothesis/Toy/*` modules may be used for examples or borrowed
  lemmas only after their assumptions are audited. They must not sit in the
  final Connes-Weil import chain unless their `#print axioms` output is
  acceptable.
- A result that depends on source-interface axioms must be described as
  source-conditional. It becomes a full Lean proof only after those interfaces
  are discharged by proofs or replaced by imported accepted theorems.

## [5] Git, Branching, And PR Norms

- Keep commits focused on manuscript, formalization, or project documentation.
- Do not mix control/archive experiments into this repository.
- Commit major manuscript or formalization milestones.
- Major milestone commits and pushes should use GPG-signed commits that GitHub
  shows as Verified. Before committing, verify `commit.gpgsign`,
  `user.signingkey`, and the available secret key; do not create an unsigned
  milestone commit unless Peter explicitly overrides this rule.
- Current repository config sets `commit.gpgsign=true`, `gpg.format=openpgp`,
  and `user.signingkey=F84F18CD20BE8255`. The matching local secret key exists
  as `828A1CFCEC8286BD8D671DF6F84F18CD20BE8255`.
  Before the next push, verify the commit locally with
  `git log --show-signature -1` and confirm the matching public key is
  registered with GitHub so the commit renders as Verified.
- Before commit or push, check staged files and staged diff for accidental
  control/archive artifacts.

## [6] Environment, Secrets, And Deployment

- Do not commit credentials, local machine paths, or private workflow artifacts.
- This repository is private by default.
- Public communication about the proof requires separate review.

## [7] Known Pitfalls

- The manuscript is source-conditional. It depends on the cited CCM24, CCM25,
  and CC20 source theorems as stated.
- The current artifact is not a Lean proof.
- The current artifact is not a Clay or journal certificate.
- Unconditionalization work must remove or prove the inputs to
  `final_connes_weil_rh`, especially `RouteCertificate`,
  `SourceObjectPackage`, and the expanded source front-end records. Do not
  count proof-package coverage, clean route-composition axiom output, or
  interface reshaping as an unconditional RH proof.
- Source-model theorem-base staging is not analytic discharge by itself. A
  law stored as a field on `CCM24SourceModel`, `CCM25SourceModel`, or
  `CC20TraceModel` remains an assumption until a concrete Goal 0 source
  definition layer proves that law and uses the theorem to fill the field.
- The next unconditionalization correctness gate is Goal 0: define concrete
  analytic source objects and prove at least one source law from those
  definitions. The first recommended seed is the CCM25 common source test and
  finite-prime evaluation object, because it feeds Goal 2B common-test staging
  and later restricted-to-full support equality.
- Slice Goal 0 into implementable proof-bearing steps. Start with Goal 0A:
  define a concrete CCM25 common source test and convolution square, prove the
  square read-off by unfolding definitions, and make Goal 2B's
  `CommonTestObject` consume that concrete object. Then proceed to concrete
  visibility, prime-power evaluation points, fixed-lambda support, and finally
  replacement of one `CCM25SourceModel` law-field projection by a theorem from
  those concrete slices.
- Goal 0C is complete at the concrete-common evaluation bridge layer:
  `ConcreteCommonPrimePowerEvaluation` and
  `ConcreteCommonPrimePowerPairingData` force the prime-power evaluator and
  pairing path to use the same `ConcreteCommonSourceTest`, concrete source
  square, and points `n` / `n^-1`. Do not redo Goal 0C as another generic
  source-point layer.
- Goal 0D is complete at the concrete fixed-lambda support bridge layer:
  `ConcreteCommonFixedLambdaPrimePowerSupport` forces fixed-lambda support data
  to use the same concrete common source test and proves concrete-visible atoms
  have the `SourceLambdaCut lambda n`. Do not redo Goal 0D as a generic
  support predicate over an unrelated source-test interface. The next Goal 0
  proof-bearing slice, Goal 0E, is complete at the finite-prime normalization
  theorem-base replacement layer:
  `ccm25_finite_prime_normalization_of_concrete_arithmetic_rows`,
  `CCM25TheoremBaseFinitePrime`, and
  `CCM25TheoremBasePartialQWFinitePrime` route finite-prime normalization
  through concrete arithmetic rows instead of
  `CCM25SourceModel.finitePrimeNormalization` law-field projection. Do not
  describe this as full CCM25 discharge: `QW`, `Psi`, `QW_lambda`, and pole
  normalization still need concrete definitions or accepted Lean theorem
  inputs. Goal 2C is complete for the CCM25 concrete-consumption slice:
  `SourceObjectCommonData` and `SourceObjectExpandedRows` force the expanded
  CCM25 object row to consume the same concrete arithmetic rows, common source
  test equality, and Goal 0E finite-prime theorem path. Do not describe this as
  constructed CCM24/CC20 analytic object witnesses. Goal 2D is complete as an
  explicit data-driven constructor:
  `SourceObjectCrossObjectBridges` and `sourceObjectPackageOfData` construct
  `SourceObjectPackage` from the staged base, common data, expanded rows, RH
  exit data, and named bridge fields. Do not describe this as a no-assumption
  source-object proof: the bridge data and CCM24/CC20 analytic witnesses remain
  explicit inputs. Goal 3A is complete at the fixed-test front-end constructor
  layer: `FixedSTestFrontEndData` and
  `FixedSTestFrontEndData.toExpandedSourceFixedSTestFrontEnd` build
  `ExpandedSourceFixedSTestFrontEnd` from explicit fixed-test obligations, and
  the read-offs preserve `pkg.commonTest.sourceTest`,
  `pkg.ccm24.sourceSupportWindow`, and the finite-prime visibility bridge.
  Do not describe this as proving admissibility, triple vanishing, or
  finite-prime visibility. Goal 3B/C/D are complete in
  `ConnesWeilRH/Route/FixedTestFrontEnd.lean`: `FixedSTestObligationData`
  turns named fixed-test obligations into the fixed-test front end, derives
  finite-prime visibility from concrete CCM25 arithmetic rows for
  `pkg.commonTest.sourceTest`, connects source triple-vanishing symbols to the
  route test, and specializes the read-offs to `sourceObjectPackageOfData`.
  Do not describe this as proving trace legality, support-square transport,
  sign/defect, restricted-to-full, route certificate, or unconditional RH. The
  next proof-bearing slice is Goal 4A: trace-front-end data construction from
  the exact Goal 2D package and Goal 3 fixed-test front end while keeping
  trace/read-off bridge obligations explicit. Goal 4A/B are complete in
  `ConnesWeilRH/Route/TraceFrontEnd.lean`: `TraceFrontEndData` constructs
  `ExpandedSourceTraceReadOffFrontEnd` and `SourceTraceReadOffData` from the
  exact package/fixed-test tuple, preserves the CC20 trace test, lambda, CCM25
  arithmetic package, test-and-quotient compatibility, support-square
  transport, and full/restricted trace bridges, and specializes these read-offs
  to `sourceObjectPackageOfData`. Goal 4C is complete as a structured
  trace-scale obligation layer: `TraceScaleNoMissingBulkData` names the ordinary
  trace/support-square/no-defect/`QW_lambda` scalar path, rank/pole/`Cdef`
  ownership, and no-extra-bulk evidence, while `TraceScaleRouteFrontEndData`
  forces route-front-end staging to carry that same evidence before producing
  an `ExpandedSourceRouteCertificateFrontEnd`. Do not describe this as proving
  the S2-B1 analytic scalar equalities, sign/defect, restricted-to-full, route
  certificate, or unconditional RH. Goals 4D/E/F are complete as constructor
  staging: `route_certificate_of_trace_scale_data` and package-data helpers make
  route-certificate construction pass through `TraceScaleRouteFrontEndData`,
  while `OrdinaryTraceSupportSquareTheoremData` and
  `NoDefectQWLambdaTheoremData` split the S2-B1 scalar path into ordinary-trace
  to support-square, support-square to no-defect source, and no-defect to
  `QW_lambda` theorem legs. Do not describe these constructors as proving the
  analytic scalar equalities. The next proof-bearing slice is to replace one of
  those theorem-data fields with a theorem from CC20/CCM25 source definitions or
  accepted Lean imports, starting with the ordinary positive trace equals
  support-square trace leg. The source-shaped records
  `CC20OrdinaryTraceSupportSquareTheoremData` and
  `CC20NoDefectQWLambdaTheoremData` are now the immediate replacement targets:
  do not bypass them with generic propositions, and do not claim S2-B1 is proved
  until those records are filled by the exact CC20/CCM25 theorem path rather
  than by assumption fields.
- Goal 4G is complete at the named source-interface level:
  `ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement`,
  `CC20TraceObjectPackage.sourceOrdinaryTraceSupportSquare`,
  `cc20OrdinaryTraceSupportSquare`, `CC20Interface.ordinaryTraceSupportSquare`,
  and `ordinary_trace_support_square_theorem_data_of_source_interface` now make
  the ordinary positive trace to support-square scalar equality an explicit CC20
  source row. Do not revert this to `sourceOrdinaryPositiveTrace : Prop`.
  This row is still source-conditional until filled from concrete CC20
  definitions or an accepted Lean import.
- Goals 4H and 4I are complete as source-interface scalar replacements:
  `no_defect_qw_lambda_theorem_data_of_source_trace_square` fills the
  support-square trace equals source no-defect trace leg from
  `cc20_trace_square_of_source_trace_data`, and
  `no_defect_qw_lambda_theorem_data_of_source_interface` composes that leg with
  `restricted_trace_read_off_of_source_trace_data` to obtain source no-defect
  trace equals restricted `QW_lambda`. This is still source-conditional route
  composition, not analytic discharge. The next proof-bearing targets are to
  replace `CC20TraceModel.ordinaryTraceSupportSquare`, the CC20 trace-square
  source row, and the restricted trace read-off row with theorems from concrete
  CC20/CCM25 definitions or accepted Lean imports.
- Goal 4J now has a concrete CC20 trace-scale seed:
  `CC20Concrete.TraceScale.ConcreteTraceScaleSymbols` defines
  `sourceNoDefectTrace := supportSquareTrace` and
  `positiveTrace := supportSquareTrace`, so
  `ordinary_trace_support_square_statement` and
  `support_square_no_defect_statement` are proved by unfolding definitions.
  Treat `toCC20TraceModel` as a staging constructor only: it still requires
  explicit proofs for positive-trace nonnegativity, trace-class/cyclicity,
  Mellin half-density convention, and signs/normalizations. The next CC20
  concrete target is to prove one of those inputs from concrete operator/test
  definitions, not to hide it in another model field.
- Goal 4J now also has a square-form positivity seed:
  `CC20Concrete.TraceScale.SquareTraceScaleSymbols` defines
  `supportSquareTrace g := traceAmplitude g ^ 2`, and
  `positive_trace_nonnegative_statement` proves nonnegativity by `sq_nonneg`.
  `squareTraceScaleToCC20TraceModel` removes the positive-trace nonnegativity
  input for this concrete seed only. It still requires trace-class/cyclicity,
  Mellin convention, and sign/normalization inputs, and it does not identify
  the actual CC20 operator trace with the square-form scalar. The next concrete
  CC20 target is either a trace-class/cyclicity theorem for a named
  Hilbert-Schmidt gate or a source-identification theorem for the CC20 operator
  trace value.
- Goal 4J now has a concrete legal-gate seed:
  `CC20Concrete.TraceScale.LegalSquareTraceScaleSymbols` defines
  `hilbertSchmidtGate g := traceClass g ∧ cyclicLegal g`, so
  `trace_class_template_statement` proves the trace-class/cyclicity template by
  projection. `legalSquareTraceScaleToCC20TraceModel` removes both the
  positive-trace nonnegativity input and the trace-class/cyclicity input for
  this seed. Do not treat this as the analytic CC20 Hilbert-Schmidt theorem.
  The remaining CC20 concrete targets are a source-identification theorem tying
  the actual CC20 operator trace/gate to this concrete seed, plus Mellin
  half-density and sign/normalization proofs.
- Goal 4J now has a normalized no-proof-input CC20 trace-model seed:
  `NormalizedLegalSquareTraceScaleSymbols` fixes the Mellin and sign
  normalization propositions to `True`, and
  `normalizedLegalSquareTraceScaleToCC20TraceModel` builds a `CC20TraceModel`
  without external proof arguments for the normalized seed. Do not treat this
  as a model of the actual CC20 operators. The next useful target is a
  source-identification interface from the real `CC20TraceObjectPackage` to
  `NormalizedLegalSquareTraceScaleSymbols`, with named equalities for
  support-square trace, no-defect trace, positive trace, Hilbert-Schmidt gate,
  Mellin convention, and sign normalization.
- Common-test data must keep the convolution square as a concrete equality
  against the CCM25 Weil symbols, not as a bare `Prop`. The expanded route
  should store common-tuple evidence at the source square and transport
  restricted-to-full/final-sign route-square uses through that equality.
- The CCM25 common-test bridge must keep the
  `PrimePowerTest.SourceTestEvaluationInterface` tied by equality to
  `CCM25Concrete.Rows.source_test_of_arithmetic_rows` for the same common
  source test. Do not reintroduce a bare `ccm25Test_eq_commonTest : Prop`.
- Route-search notes belong in the control/archive repository unless they are
  directly needed by the manuscript or formalization.
- Theorem 1 must only be used on admissible tuples `(S,I,lambda,g)`: the support
  of `g` must lie in `I subset [lambda^(-1),lambda]`, and `S` must contain every
  finite prime visible to `F_g=g^* * g`. Otherwise the fixed-S trace cannot be
  read as the full restricted `QW_lambda` form.
- CCM24 transport is the fixed-S drift guard: `eta_S`, Fourier-support
  transport, `V_S=M_S U_S`, bounded comparison, and `theta_S`/Sonin comparison
  must refer to the same source test/window before the route takes a
  `lambda -> infinity` limit.
- The positive trace in Theorem 1 must be trace-class before positivity is used:
  check the Hilbert-Schmidt assertion for `P_hat P theta_S(g)` first.
- Trace legality is not trace-scale compatibility. Before positive trace feeds
  `QW_lambda`, the route must prove same-scalar and same-cutoff compatibility
  among ordinary positive trace, support-square trace, no-defect source trace,
  and the CCM25 restricted scalar, with no missing divergent bulk or hidden
  finite-part subtraction.
- The second external opinion makes the divergent-bulk test source-critical:
  if a source-owned term like
  `BulkScaleTerm_(S,I,lambda,g) ~ C log(lambda) ||g||^2` survives outside
  `QW_lambda`, rank, pole, and endpoint-strip `Cdef`, the route stops at the
  positive-trace read-off.
- Accepted-source status cannot be self-assigned from a project proof package.
  A row may be promoted only after an exact theorem candidate has source
  anchors, exact hypotheses, object/test/sign bridges, limit order, and an
  external referee, accepted proof, or Lean theorem accepting that exact row.
- Accepted-source packet coverage is now tracked by
  `docs/audits/accepted-source-packet-completion-audit.md`. Packet coverage
  being complete means every source-facing row has a referee-checkable packet;
  it still does not mean any row is accepted-source.
- Accepted-source decisions must use
  `docs/audits/accepted-source-referee-decision-form.md` or an equivalent
  formal theorem record, and the result must be reflected in
  `docs/audits/accepted-source-certification-status-board.md` before README or
  certification audits claim accepted-source status.
- `decision record opened` is not an accepted-source theorem status. It means
  the row has a theorem candidate, evidence bundle, required checks, and
  rejection names ready for review. Keep all accepted-source decision records
  pending until an external referee, independent proof, or Lean theorem fills
  the decision block.
- Base source-interface packets must be checked before downstream packets:
  `docs/audits/ccm24-source-interface-accepted-source-packet.md`,
  `docs/audits/ccm25-source-interface-accepted-source-packet.md`, and
  `docs/audits/cc20-trace-source-interface-accepted-source-packet.md`.
- The first accepted-source upgrade target is S2-B1. Use
  `docs/audits/trace-scale-source-term-ledger.md` to classify every
  positive-trace source scalar as `QW_lambda`, rank, pole, or endpoint-strip
  `Cdef` before claiming no missing divergent bulk.
- The next accepted-source packets are
  `docs/audits/sign-defect-accepted-source-packet.md` and
  `docs/audits/restricted-to-full-accepted-source-packet.md`. Rows 1-7
  sign/defect classification and fixed-test `QW_lambda(g,g)=QW(g,g)` must pass
  those packet checks before the route can treat them as certified inputs.
- The final accepted-source packets are
  `docs/audits/final-sign-accepted-source-packet.md`,
  `docs/audits/cc20-exit-accepted-source-packet.md`, and
  `docs/audits/rh-definition-accepted-source-packet.md`. The route cannot call
  the final exit certified until the sign equality, CC20 Proposition C.1 use,
  and source-RH-to-standard-RH definition bridge pass those packet checks.
- Do not import CCM25 finite-operator spectral convergence, determinant
  convergence, numerical eigenvalue convergence, or even-sector
  minimum-eigenvector assumptions as accepted inputs for the current route.
  The current restricted-to-full step must remain the fixed-test scalar
  restriction bridge from `QW_lambda(g,g)` to `QW(g,g)`.
- Proposition C.1 should never be replaced by a route-local density claim. It
  already allows an extra finite vanishing set `F` containing `{0,1}` and
  disjoint from non-trivial zeros; the route uses `F={0,1/2,1}` and must prove
  the Mellin/half-density translation to that exact set.
- CC20 Proposition C.1 route input should pass through
  `CC20PropositionC1RouteInputData` before projecting
  `CC20PropositionC1InputData`. Do not construct C.1 input data in a way that
  can drift from the supplied route triple-vanishing or full-positivity
  evidence.
- Do not treat a source-paper statement ending in "RH" as identical to Mathlib
  RH by name alone. The final bridge must unpack CC20's non-trivial zero set
  against Mathlib's `riemannZeta s = 0`, `not exists n, s = -2*(n+1)`, and
  `s != 1` hypotheses.
- The inequality direction at the final exit is fixed by
  `QW(g,g) = - sum_v W_v(g * bar(g)^sharp)`: route nonnegativity becomes the
  CC20 nonpositivity hypothesis only after multiplying by `-1`.
- Commutators with `M_S` are interpreted only after all terms have been moved to
  the common scattering coordinate. Do not treat `[P,M_S]` as a commutator
  between two different Hilbert spaces.
- Before opening the Lean scaffold, read `formalization/lean-readiness.md` and
  `docs/audits/source-reread-v0.2.md`.
- Before sending the current proof route to outside reviewers, read
  `docs/audits/accepted-source-certification-audit.md`. Treat it as the
  boundary between route-evidence proof packages and accepted-source or Lean
  theorem strength.
- Before reopening Lean work, read
  `docs/audits/pre-lean-completion-audit.md`. Treat it as the local non-Lean
  completion gate: proof-package coverage is complete, but accepted-source,
  external referee, and Lean theorem certification remain open.
- The first Lean pass should prove route composition from explicit CCM24,
  CCM25, and CC20 source interfaces. Do not try to formalize all source-paper
  analytic content before the route theorem skeleton builds.
- Copied legacy Lean files may contain theorem-source `axiom` contracts. Any
  result depending on those axioms is conditional on those contracts, not a
  complete proof unless the axioms are later discharged or replaced by imported
  Mathlib/source-paper theorems.
- For Lean/Lake work, do not run the main build from `/mnt/c` under WSL. Mathlib
  has thousands of small files, and WSL access to the Windows filesystem makes
  dependency checks and builds much slower. Keep the active Lean worktree on the
  WSL ext4 filesystem, for example under `~/projects/`, and sync back only
  source files when needed.
- Build the Connes-Weil route by segments. The current default Lake target is
  `ConnesWeilRH`; the copied legacy `RiemannHypothesis` target imports large toy
  and small-case files and should be audited separately.
- When a segment fails, fix the first failing module before touching downstream
  modules. A downstream failure is usually an interface mismatch, not evidence
  that the whole route must be rebuilt.
- Keep low-level CCM25 concrete finite-prime definitions below the compact
  `CCM25Interface` layer. In particular, files such as
  `ConnesWeilRH/Source/CCM25Concrete/FinitePrime.lean` and the concrete rows
  layer should import `ConnesWeilRH.Basic` or lower concrete certificate files,
  not `ConnesWeilRH.Source.CCM25`; otherwise `Objects -> ObjectDerivations ->
  CCM25 -> CCM25Concrete -> Objects` forms an import cycle.
- `CCM25Interface` now separates `qwDefinition` and `psiSign` as distinct
  fields. When extending the concrete rows or route read-off layers, consume
  the named fields directly; do not rebuild the old pair-shaped proof object or
  reintroduce `.1/.2` projections at the interface boundary.
- `WeilFormSymbols.FinitePrimeVisibilityStatement` is a named structure with
  `globalPrimeIndexCoverage`, `restrictedPrimeIndexCoverage`, and
  `finitePrimeTermNormalization`. Do not reintroduce the old nested
  conjunction shape or consume this interface with `.1/.2.1/.2.2` projections.
