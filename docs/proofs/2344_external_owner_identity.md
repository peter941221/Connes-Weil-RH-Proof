2344 - Symbolic external-owner identity and exact binding controls

Date: 2026-10-01.
Status: SYMBOLIC-OWNER-IDENTITY-CERTIFIED / NUMERICAL-ENDPOINTS-EXTERNAL.

The new Lean model describes the same compactly supported function as
correctedPhysical. A compact support means the function is exactly zero outside
a finite interval. Here each of the 30 family terms has radius storedWidth^2.
The proof splits the inside/outside support cases and uses exp(a+b)=exp(a)exp(b).
It holds for arbitrary coefficient and modulation vectors, not just sampled data.

This closes a symbolic function-identity obligation. It does not prove that the
Python interval program implements that symbolic function correctly, nor does it
import the repaired coefficients or numerical integral bounds into Lean.

Proof structure


def externalFamilyValue2344 := coefficient * exp(bump exponent + phase)
theorem externalPhysical2344_eq_correctedPhysical

The actual source is in ConnesWeilRH/Dev/C1RouteAExternalOwnerIdentity.lean.
The second-derivative equality follows by rewriting equal functions; it does NOT
prove the explicit Python derivative-factor formula. The norm equalities then
feed frozenStripHypothesis_of_external_endpoint_bounds with explicit endpoint
inequalities. The eight endpoint facts remain assumptions, not stored conclusions.


theorem externalPhysical2344_eq_correctedPhysical :
  externalPhysical2344 coefficients modulations =
    correctedPhysical coefficients modulations

This is the key equality: the consumer cannot silently substitute another owner.

Validation

The focused Linux Lake build completes successfully with 3708 build-plan jobs.
All six audit leaves depend on exactly [propext, Classical.choice, Quot.sound].
There are no new-source warnings. Existing dependency warnings remain unchanged.
The build log is build-logs/2344_external_owner_identity_build.log.

The exact binding checker compares every captured binary64 width, represented
as a rational number, to the corresponding Lean storedWidth entry. It also
compares all four rounded Lean constants to the exact rational endpoint uppers
in the 2342 artifact. All 30 widths match, all exact squared radii match by
construction, and all four constant slacks are strictly positive.

Eight selftests pass. Mutation tests replace every captured width in turn,
swap distinct rows, remove a family, inject unsupported Lean syntax, lower each
constant, and remove an endpoint. These checks establish literal input binding,
not analytic soundness of the external program. Identical-width rows cannot be
distinguished by this width-only checker; modulation and coefficient binding are
separate obligations.

Evidence: results/2344_external_owner_binding.json,
results/2344_external_owner_identity_validation.json, and
build-logs/2344_external_owner_binding_selftest.log.

Remaining proof boundary

```text
definition identity: proved in Lean
stored widths and constant rounding: externally checked exactly
Python evaluator and derivative semantics: not proved in Lean
2338 exact coefficient realization: not imported into Lean
endpoint integral inequalities: not proved in Lean
selected-detector health and signed complete-support budget: still open
```

The external 2342 min-product bound remains 1852190.2152630097 against the
unchanged 2644542.8515 pin. This is an upper bound on unsigned weighted norms,
not evidence that the selected signed Weil functional is nonnegative. No live
owner handoff, producer GO, or RH claim occurs.

Next steps

1. Prove the interior analytic second-derivative formula and its zero extension
   for the same family definition. This ties the interval program's derivative
   channel to Lean deriv; completion requires a theorem, not sample agreement.

2. Formalize the one-sided chord-panel integral inequality for complex-valued
   functions. It turns finitely many node upper bounds plus a derivative bound
   into an integral upper bound without differentiating the modulus. Completion
   requires a checked theorem with all smoothness and grid hypotheses explicit.

3. Instantiate the exact repaired coefficients and certify the actual endpoint
   inequalities before activating the norm supplier. Then return to the selected
   detector's signed physical-kernel budget; unsigned norms alone cannot finish RH.

