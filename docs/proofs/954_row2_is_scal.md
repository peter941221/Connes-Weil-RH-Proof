# 954 - Residual axiom row 2 embeds Wall-A 1.4 (SCAL)

Date: 2026-08-10.  Status: finding (not a closure).  RH NOT claimed.

## What

The residual axiom

    normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot :
      CommonFinitePrimeArithmeticSourceData (core.toWeilFormSymbols)

is a data-bearing structure with three fields:

  1. commonTestFunction
  2. finitePrimeData : FinitePrimeArithmeticSourceData ... (arithmetic rows)
  3. scopedArchimedeanContributionBalance :
       forall lambda, forall globalData, forall restrictedData,
         SourceScopedArchimedeanContributionBalance W common lambda gd rd

Field 3 is exactly the analytic global-vs-restricted arch balance (SCAL), the
same Wall-A 1.4 identity to which the whole SCB reduced (docs/951/952).  On the
non-zero healthy arch term (totalArchimedean) it is NOT provable by data wiring;
on the zero arch term it is FALSE (L657DiagProbe.probe_balance_false).

## Consequence

Residual row 2 cannot be discharged by more arithmetic/data bricks: it is
constitutively equal to the open analytic SCAL identity.  The only path to
removing row 2 from RhOutputAxiomLedger is proving that identity (Wall-A 1.4),
which is genuine analytic research (Weil explicit formula), not Lean assembly.

## Confirmation chain

- ScabNormalForm.scab_iff_pole_arch_target : SCAL pair equality iff
  ScabPoleArchTarget (pole/pole scalar identity).  (see docs/951)
- ScabHealthyTarget pins that target on the healthy carrier.  (docs/952)
- CommonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance
  is the live field forcing SCAL.

RH NOT claimed.  Any acceptance here is a step in understanding, not a proof.
