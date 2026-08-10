import ConnesWeilRH.Dev.UnconditionalSkeleton

/-!
# RhOutputAxiomLedger — auditable residual axiom ledger for the RH output

Verification hook, not a source module.
Refreshing, per milestone the authoritative "#print axioms" residual-count
audit (AGENTS 8, docs/proofs/887).  As of 2026-08-10 the output
`rhDefinitionBridgeToMathlibFromTheorems` depends on exactly these project
axioms (verified on the Linux-side mirror):

  1. normalizedCoreCC20PropositionC1SourceCriterionRoot   (RH-equivalent)
  2. normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot
  3. normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot
  4. normalizedCoreS2B1TracePackageRemaindersRoot
  5. normalizedSelectedFinalRouteDetectorCriterionCoverageRoot

plus the mathlib foundations. Each milestone that turns one of these into a
theorem removes one row from the next audit output below.
-/
namespace ConnesWeilRH
namespace Dev

#print axioms ConnesWeilRH.Dev.UnconditionalSkeleton.rhDefinitionBridgeToMathlibFromTheorems

end Dev
end ConnesWeilRH
