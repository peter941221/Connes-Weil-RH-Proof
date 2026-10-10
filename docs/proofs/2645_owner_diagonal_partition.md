Record 2645: owner-moment-matrix diagonal partition (the 30 entry certificates assembled into one statement)
Date: 2026-10-10

Result

Positive: the diagonal campaign closes into a single theorem. The new
module `ConnesWeilRH/Dev/C1RouteAOwnerDiagonalPartition2645.lean`
imports the 30 certified probe stacks (ZProbe2628K00..K29) and states
`actualOwnerMomentMatrix2351_diagonal_mem2645`:

    forall d : Fin 30,
      (analyticMomentInterval2597 d d).Mem
        (ownerMomentMatrix2351 capturedModulations2584 capturedNodes2584 d d)

proved by `fin_cases d` + an ordered 30-argument `exacts` discharging
one certified capstone per index
(`actualOwnerMomentMatrix2351_entry{00..29}_mem2628`, records
2634-2644). Single-target build on the Linux-native workspace: Built
line green at 123 s over a 20057-job graph (all 30 probe oleans
reused, zero recompilation), full error list empty, `uses sorry`
zero. Mechanical preflight before the build: import block = 30 probes
in order and opening the file (AGENTS 2cf), exacts census 30/30 with
every capstone name verified present in its probe, statement form
identity, namespace wrapper.

Scope

This is partition assembly at exactly the certified scope: the
conjunction of the 30 single-entry memberships, now addressable as
one quantified fact. No off-diagonal entry is claimed; the analytic
interval table still carries only the diagonal. Static consumer,
complex scalar engine (record 2624 GO route: degree-55 complex
polynomial, exp(i psi c) rotation mandatory), Producer GO, SourceRH,
and RH remain open. Axiom status is inherited unchanged from the 30
capstones (the campaign's axiom trio); no new axiom was introduced.

Pipeline notes

- The assembly module is 85 lines: 30 imports, one docstring, one
  theorem, `end`. The heavy lifting (roughly 16300 family modules and
  30 probes) was already certified; this layer only re-addresses it.
- fin_cases + ordered exacts worked first-try: the substituted goals
  (Fin.mk k proofs) are definitionally equal to the capstones' bare
  numeral statements, so `exact` closes each case without massaging.
- Single-target build cost (123 s) is dominated by olean load of the
  30 probe imports, not elaboration.

Next obligations

1. Static consumer: consume `actualOwnerMomentMatrix2351_diagonal_mem2645`
   in the partition layer's consumer statement.
2. Complex scalar engine (record 2624 GO route: degree-55 complex
   polynomial, exp(i psi c) rotation mandatory).
3. Producer GO / SourceRH / RH remain out of scope.
