# 1264 — G8 physical-endpoint readback strategy

Date: 2026-09-10.

Status: RESEARCH STRATEGY / FORMAL-BOUNDARY RESTATEMENT.  This record makes
no new Lean claim, opens no numerical campaign, and does not change the
binding healthy-`CompactLog`, B5-shaped route.  Its consumer is the existing
`G8SameOwnerReadbackData` positive-trace exit of record 1257, hence the
detector-specific semi-local `SourceRH` composition of map records 003, 004,
and 007.

## 1. Exact target

Fix one `SelectedWeilSquareOwner` with source test `g`, a Sonin scale
`lambda`, a finite prime-power family `S`, and the already constructed G8
physical endpoint.  Write

```text
  W       = detectorOperator owner,
  M       = finite Euler metric coframe,
  F       = actual-band forward coframe,
  E       = F + M,
  J       = sourceInclusion lambda,
  L_n     = J* (g8SourceCutoffPairData ... n).left,
  P_n     = L_n* (E* W E) L_n,
  T_n     = (g8SourceCutoffPairData ... n).traceProduct.
```

`P_n` is the physical-endpoint finite-cutoff carrier; `T_n` is the original
G8 finite-cutoff carrier currently used by `G8SameOwnerReadbackData`.  They
are not definitionally the same sequence.  The established finite-cutoff facts
are

```text
  P_n is trace class, positive, self-adjoint;
  Tr(P_n) is real and 0 <= Tr(P_n).                         [FORMAL]
```

The actual next theorem is not another positivity lemma.  It first needs an
**alignment choice** between `P_n` and `T_n`, and then a same-owner readback.
The two permitted outcomes are:

```text
  (A) prove Tr(T_n) - Tr(P_n) -> 0 (or a named internal residual with
      zero limit), then use P_n for the arithmetic readback and transport
      that result to the already-existing G8 contract; or

  (B) give P_n its own direct PositiveTraceOperatorLimitFamily instance,
      with r_n -> 0 and Tr(P_n) - r_n -> qw(g), without adding a generic
      interface or changing owner.
```

In outcome (A), the final two limits are exactly the analytic fields of
`G8SameOwnerReadbackData`.  In outcome (B), the already-existing generic
positive-trace bridge consumes the physical pair directly.  In either case,
the formal bridge returns `0 <= qw g`.  The healthy detector contradiction is
outside this producer premise, as required by the record-1225 quantifier
repair.

## 2. What G8 has genuinely bought

G8 is viable only as a Fork-B operator-level correction: its compensation is
inside the positive Gram, never an external divergent scalar subtraction.
The following identities are formal and remove the algebraic ambiguity:

```text
  J* G8 J = M* W M
          = (u (survivor + boundarySum))* W (u (survivor + boundarySum)),

  E* W E = M* W M + (F* W M + M* W F + F* W F).
```

At finite cutoff, the original G8 trace also has the legal four-channel
ledger: base, cross, adjoint-cross, and leakage.  The cross plus adjoint-cross
trace is exactly twice the real part of the cross trace.  The physical-endpoint
carrier additionally absorbs the forward correction while preserving
positivity.  Thus no missing proof is merely a trace-class, adjoint, or
real-scalar bookkeeping issue.

The remaining obstacle is a comparison of *actual operators*.  Existing
finite-prime infrastructure reads

```text
  projectionResponse = EulerBoundary + residual,
  Tr(EulerBoundary) = finite visible-prime sum,
```

whereas the original contract is based on `T_n` and the physical endpoint
candidate is `P_n`.  Neither the uncut cross-response identity nor the
survivor/boundary factorization identifies either cutoff sequence with that
projection-response owner; neither does it align `T_n` with `P_n`.  Records
1258 and 1263 therefore forbid treating an adapter, a numerical resemblance,
or a formal four-channel split as this missing theorem.

## 3. Required proof decomposition

The attack should proceed in this order.

```text
G8-P0  Carrier alignment
       Prove a finite-cutoff equality or zero-limit discrepancy connecting
       T_n to P_n, OR select P_n as the direct positive-trace family and
       record that direct consumer.  This cannot be skipped: the present G8
       readback contract is parameterized by T_n, not P_n.

G8-P1  Finite-cutoff operator comparison
       Derive an equality on the selected source carrier which expands its
       trace into a literal finite visible-prime Euler-boundary trace plus
       named archimedean/survivor/internal terms.  Every term must retain the
       literal cutoff leg L_n, g, lambda, and S until the equality is complete.

G8-P2  Internal cancellation/readback
       Use the concrete E = F + M expansion to show that the non-Euler terms
       form one canonical remainder r_n.  This is an identity, not a chosen
       scalar counterterm.  In particular, no term may be subtracted outside
       the positive operator family.

G8-P3  Analytic limit
       Prove r_n -> 0 and identify the limit of the Euler-plus-archimedean
       expression with the existing same-owner Weil formula
       -archimedeanTerm(g.square) - finitePrimeSum(g.square).

G8-P4  Contract assembly
       In alignment outcome (A), package P0--P3 as G8SameOwnerReadbackData;
       in outcome (B), instantiate the existing positive-trace bridge with
       the physical pair.  Only then invoke the B5 capstone.
```

The finite-cutoff metric/internal expansion in record 1265 is now landed.
P0 is the immediate next mathematical brick: it determines whether the
physical endpoint is a genuine repair of the existing G8 consumer or a new
direct instance of it.  P2 is deliberately separate:
without a finite-cutoff identity, a proposed remainder has no owner-local
meaning; without P2, an identity cannot transfer positivity to the limit.
P3 is analytic work, not a Lean-wrapper task.

## 4. Non-negotiable guards and falsifiers

1. **Same owner.**  The finite-prime readback must be derived for `P_n`, not
   for the uncut `finiteEulerTargetCommutatorResponse`, a differently
   sandwiched projection response, or a normalized additive carrier.
2. **No external renormalization.**  A formula of the form
   `Tr(P_n) - B_n -> qw g` with divergent externally subtracted `B_n` cannot
   feed the positive-trace limit contract.  The correction must be in `E*WE`
   (or an equal positive Gram) before `C_n` is applied.
3. **No bounded-response shortcut.**  The projection obstruction records show
   that a cutoff response with bounded real trace cannot cancel the cofinal
   window bulk.  If P1 exposes such an uncancelled bulk term, this physical
   endpoint candidate fails its intended L4 readback and receives a kill-ledger
   entry; it is not repaired by declaring that term a vanishing remainder.
4. **Value, not only convergence.**  A finite trace may converge to a scalar
   different from `qw g`; the record-1213 `-3.321` model mismatch is a warning,
   not evidence about G8.  P3 must prove the exact same-owner value identity.
5. **No numerical substitute.**  The L4 fixed-rank scout is closed.  No new
   run is licensed by this strategy record.  Any future new candidate mechanism
   must enter the map-006 NM loop with its own generation and translation
   cards.

## 5. Lean-facing deliverables

The next implementation batch should be small and theorem-led:

```text
1. State and prove the P0 carrier-alignment identity before changing a
   readback structure or introducing a limit.
2. Define the literal selected-carrier finite-cutoff Euler/readback expression.
3. Prove the P1 equality before introducing any Tendsto statement.
4. Define r_n only as the P1 residual; prove its realness from the established
   self-adjoint physical trace and the real Euler scalar.
5. State P3 as two explicit analytic hypotheses/theorems, then in outcome
   (A) construct `G8SameOwnerReadbackData`, or in outcome (B) instantiate the
   existing positive-trace bridge directly; add no generic interface.
6. Run the owning G8 module plus its paired audit only after this related batch.
```

## 7. Implementation finding (2026-09-10)

An exploratory Lean proof of the ambient projection expansion was not
promoted: unfolding the concrete `g8SourceCutoffPairData.left` inside the
projection identity drove the kernel into a deterministic timeout (the
longest run was 648 seconds).  This is an elaboration constraint, not a
mathematical no-go.  The implementation route is therefore fixed to keep the
finite-window leg opaque and use the already-owned channel-pair and
trace-cycle theorems when introducing the P0/P1 equality.  No generic
projection interface or unproved alignment declaration is to be added merely
to bypass that constraint.

The acceptance condition for P0 is an axiom-clean relation naming both actual
cutoff carriers, not an informal claim that they are "the same G8".  The
acceptance condition for P1 is an axiom-clean equality whose two sides contain
the same literal cutoff leg `L_n` and the same `owner.sourceTest`.  The acceptance
condition for P3 is the two fields of `G8SameOwnerReadbackData` in outcome
(A), or their direct physical-pair counterparts in outcome (B), not merely a
new positive finite operator.

## 6. Evidence basis

Formal inputs: records 1243--1257 and 1259--1263, especially
`C1G8AdjointShearGram.lean`; record 1258's owner-level boundary audit; and the
existing `G8SameOwnerReadbackData` consumer.  The operator correction and
finite-cutoff carrier are formal Lean results with only the standard three
axioms.  The P1--P3 assertions above are project candidates/open analytic
obligations, not literature-backed endpoint claims.

RH is not claimed.
