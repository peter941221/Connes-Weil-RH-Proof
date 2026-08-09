# 905 — Gate-3U carrier re-point: architecture assessment (design proposal)

Date: 2026-08-08. Lane: Gate-3U trace bridge (docs/860, docs/872 blocker). Status:
PROPOSAL, not a code change. Re-pointing the Gate carrier is an architecture-level
decision (AGENTS section 3b / section 6: needs Peter). This document is the
source-backed impact / risk / migration assessment so the decision is evidence-first.

## 0. One-paragraph answer

The only remaining Gate-3U open piece (hdecay : |Re Tr tail| <= bound) is blocked NOT
by a missing analytic theorem but by a type-level carrier mismatch: all closed
trace-class machinery lives on `finiteSCarrier := cc20GlobalLogCrossingL2`
(ProjectionTrace:73) parameterized by a `HilbertBasis nu Cc finiteSCarrier`, while
the Gate readout is taken on the closed Sonin subspace `sourceSoninCarrier lambda`
(FrameGramCalculus:109), which carries no HilbertBasis, no Nonempty and no
FiniteDimensional instance, and therefore no IsTraceClassAlong certificate.
Re-pointing the Gate to a carrier that possesses such a basis converts the
impossible step into wiring an existing certificate — but every candidate
replacement is currently blocked by a distinct structural wall.

## 1. The exact gap (source-backed)

docs/proofs/860 final verdict (2026-08-07):
- tail operator = infinite Nat-multi-index renewal sandwiched around the A+ A
  Fourier-multiplier, neither compact / Hilbert-Schmidt / trace-class on the
  uncompressed carrier.
- the only way forward is wiring the tail's own trace-class certificate to one
  already in the closed prolate bundle (sourceProlateCommutator_isTraceClassAlong,
  CCM24SourceProlateTrace).
- that bundle is parameterized by `finiteSCarrier := cc20GlobalLogCrossingL2`
  via a global HilbertBasis; the Gate is on `sourceSoninCarrier`, a closed subspace
  of the same ambient carrying no such basis. There is no in-library
  IsTraceClassAlong source for the Gene carrier, no nuclear/HS bound, and no
  finite-basis instance. This is a structural seam.

docs/867 (infinite seam): `hfactor := Summable |sourceProlateHVFactor lambda
(globalBasis i)|^2` appears only as an assumption in every prolate trace thread
and has zero call-sites; at unit scale it is the difference of two infinite-rank
projections, generically not trace-class.

docs/872 section 7-8: the whole Proof-717 / Gate reduces to ONE open identity on
the perp of range-P: `(I-P)F = -(I-P)D`. The only family Lean closes is the nil
family (visiblePrimes = [], degenerate). Any nonempty finite-prime family has
genuine off-Sonin leakage (probes 815-824: the outer channel never decays).

docs/861: Route-A finite-band Gate IS closed and axiom-clean (bandTerminalGate).
It does NOT close the infinite-carrier form; that seam stays open.

## 2. Repoint options (blast radius + migration cost)

+--------+------------------------------------+-----------------+--------------+------------------------+
| Option | What it repoints                    | Blast radius    | Migrate cost | Blocks on              |
+--------+------------------------------------+-----------------+--------------+------------------------+
| A      | Gate onto a finiteSCarrier (global basis) | whole Gate readout + call-site | low-med | trace lives on L2, loses Sonin constraint |
| B      | Build a Sonin-subspace HilbertBasis | add basis + Nonempty instance | high | no such object in-library, not reachable  |
| C      | Bridge tail trace-certificate to existing bundle | add IsTraceClassAlong bridge | med | A1/A2 seam (no LegacyTestEquiv) blocks    |
+--------+------------------------------------+-----------------+--------------+------------------------+

## 3. Numeric verdict is binding for all three

AGENTS section 8c hygiene is decisive: the honest outer channel (I - P) D has been
measured around 0.62 on the transported-Sonin frame and never decays with
resolution (probe 824) nor with log-scale sweep (probe 884). Therefore:

- Option A changes the meaning of the Gate readout (Sonin projection lost) and the
  leak L = F + (D - J) still has a genuine nonzero orthogonal part; A does not make
  the cancellation (star) decidable.
- Option B is unreachable as a Lean object today (no explicit PSWF in-library; the
  Slepian dpss is the mathematically-correct family but not repo-owned, and it does
  not make the outer leak decay).
- Option C is exactly the hdecay wiring, which the Gate/Test-Equiv structural seam
  kills.

Net: NO re-point of the carrier makes the remaining analytic identity (star) or the
Sonin trace-class hfactor constructible with in-library objects. Every candidate is
blocked by a real analytic/structural bottom the numeric chain already measured as
nonvanishing.

## 4. Honest recommendation

Re-pointing is REJECTED as a standalone fix: it renames the wall, it does not cross it.
It is worth doing ONLY as one concrete sub-action that removes a false impression:
the infinite-carrier seam should be made explicit and auditable at the consumer.

Two actions that DO advance the route:

- (1) [needs Peter] Re-read the Gate readout onto the finite-band branch (bandTerminalGate,
  axiom-clean), recording the infinite seam as an explicitly open non-blocking premise.
- (2) [decide autonomously] Close the finite-band hdecay wiring by carrying the
  prolate/commutator trace certificate to the finite carrier basis; if it compiles
  axiom-clean + audit, that is a real finite-band trace-class Gate leaf.

## 5. What this document does not claim

- It does not claim re-pointing is impossible; it claims it is not sufficient given
  the measured non-damping of (I-P)D.
- It does not claim RH. The infinite Gate, Lane-R/B axioms, and the arch-phase
  identity all remain open (see docs/887).

## 6. Next actions (for Peter to pick)

1. Authorize (1): rebase the Gate readout to the finite-band branch, record the
   infinite seam explicitly.
2. Ok (2) under standing authorisation, then axiom-audit as an isolated leaf.
3. If neither, keep this document as the auditable record that re-point is a rename,
   not a fix, and the next real move is the Lane-R/B question.

## 8. Decisive finding (option-1 depth read, 2026-08-08): the finite-band Gate is ORPHANED from the RH route

Re-reading the actual consumers (not the docs) decisively reframes option (1):

- `ConnesWeilRH/Dev/RouteATailBandBound.lean` (finite-band Gate, `bandTerminalGate`)
  imports TailBound / ProlateTrace and closes a REAL route tail bound axiom-clean.
  But `rg bandTerminalGate | RouteATailBandBound` across the repo shows it has
  NO consumer: the module is a self-contained producer leaf.

- The RH pathway `unconditional_rh_skeleton` (UnconditionalSkeleton.lean:8061)
  imports Route / CC20RouteRealization / Ledger / AnalyticSourceModel /
  Yoshida / ZetaHalf / S2B1TraceScale / CCM25SourceDataGuards.  It routes through
  `normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems`, and its real
  archimedean step consumes `sourceTrace.hilbertSchmidtGate`
  (RouteTheorem.lean:1332) — the archimedean Hilbert-Schmidt gate, NOT
  `canonicalRealGate3UAt` / not `bandTerminalGate`.

- Therefore the whole "Gate-3U tail-trace-bound" lane (finite-band `bandTerminalGate`
  AND the infinite seam `docs/85 860`) is a DIVERGENT lane from the two hard
  gates the skeleton actually leans on: `hilbertSchmidtGate` (Lane-A/R sign) and
  the Lane-B/R axioms (SourceWeilModel, C1/Yoshida).

### What this means for option (rebase)

1. "Rebase the Gate readout onto the finite-band branch" does NOT touch the RH
   pathway — the skeleton never references `sourceSoninCarrier` band bounds. It
   only cleans up an already-orphaned leaf. It changes RH distance by ZERO.

2. The action that WOULD matter is wiring a trace-class / sign gate into the
   actual `hilbertSchmidtGate` dependency at RouteTheorem.lean:1332 — which
   bisects to the arch-phase `Re[Gamma(a+I/2)^4]>=0` (the 904 leaf) plus the
   carrier-nonempty gate (A2). That is the Lane-A lever, and it is what option
   (2) can actually close as "true global HS trace nonnegative."

3. So the honest fork for Peter is not "infinite-vs-finite band". It is:

   +---------------+--------------------------------------------------+------------------+
   | choice        | effect                                         | RH distance      |
   +---------------+--------------------------------------------------+------------------+
   | rebase Gate   | clean orphaned finite-band leaf; no consumer   | 0 (does not move)|
   | close HS gate | feeds RouteTheorem:1332 hilbertSchmidtGate    | moves Lane-A #1  |
   +---------------+--------------------------------------------------+------------------+

Recommendation: skip the cosmetic finite-band Gate rebase (orphan, zero RH
value). The root-and-effect next action is to attack the HS gate consumed
by RouteTheorem:1332, i.e. close the arch-phase sign on the operator side, not
the tail-trace lane.


## 906 routing correction (same day): the arch-phase Gamma^4 line is NOT the 1332 gate

After closing the sector lemma (docs/906), wiring it into `RouteTheorem:1332` was
attempted and is impossible: `hilbertSchmidtGate` there is `SourceTraceScaleData.hilbertSchmidtGate g = traceClass g ∧ cyclicLegal g` (a trace-legality gate), NOT
`Re[Gamma^4]`. The `Re[Gamma(1+I/2)^4]>=0` line (docs/901-904, 906) has no consumer
in `Route/` or the skeleton. The true gate-side levers are:
  H1 wire `HilbertTraceModelClosure.retypedTraceModel`/`HilbertCarrierReTypedSymbols`
     (already axiom-clean: `Gate_nonempty`, `scalarTrace=sq_norm>=0`,
     `archimedeanSignNormalized := Nonempty HilbertSignArchCorrected.HilbertArchSignDatum`
     via the `F†F` PSD) into the skeleton's concrete `sourceObject.cc20Trace` —
     an architecture/model re-point (needs Peter, §3b).
  H2) Lane-B: re-type the broken concrete SourceWeilFormData/shareFinitePrime/additive-
     convolution model.
The 906 `Re[Gamma^4]` sector leaf remains a correct, orthogonal leaf for the docs/902/903
Euler-log line (not yet on any RH-route consumer).  This supersedes the earlier §8
"attack the HS gate ... (the 904 arch-phase leaf)" phrasing.
