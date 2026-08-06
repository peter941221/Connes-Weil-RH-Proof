# Route C (design): replace the operator-norm Gate 3U with a Hilbert–Schmidt trace-class gate

Date: 2026-08-06 · Status: **design + carrier-relocation, NOT a proof.** A
numerically-motivated reframing of where the open identity lives.  This route
moves the Gate from an *RH-scale operator-norm estimate* (Proof 717) to a
*trace-class carrier-existence* question (the A0 lane).  RH stays conditional.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/825_prime_weight_renormalization_verdict.md`,
`docs/proofs/gate3u-right-energy-leakage-norm-bottom.md`,
`docs/proofs/823_gate3u_consolidated_status.md`
EVIDENCE: `ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean`,
`.../RootSandwichedTrace.lean`, `.../HilbertSchmidtIdeal.lean`

## 1. Why the current gate is an operator-norm gate (and why that is the whole wall)

Gate 3U's readout is a scalar *norm* comparison:

```
canonicalRealGate3UAt  ⟺  |re Tr(sourceGramResponse λ canonicalFamily)| ≤ bound
```

but the closure exploits the adjoint identity to reduce it to a single
right-energy inequality, and that inequality is:

```
RightEnergy = Σ' ‖pair.right ∘L sourcePhysicalCoframeLeakage λ f (basis i)‖²
           ≤  ‖sourcePhysicalCoframeLeakage‖² · (fixed majorant)
```

Only the RIGHT factor has the fixed majorant
(`sourceThreeBranchPairData_right_basisEnergy_le_fixedMajorant`,
`CCM24FiniteSFixedPhysicalEnergyBound.lean:249`).  The only genuinely new scale is
`‖sourcePhysicalCoframeLeakage‖`, and the exact norm gate is proof-717
**equivalent** (`CCM24FiniteSEndpointContractionGuard.lean:245-252`):

```
‖combined endpoint‖ ≤ 1  ⟺  forward + physicalLeakage = 0
```

So the entire open bottom is: *prove a norm of a sum of two operators is ≤ 1,
which is equivalent to one off-radial cancellation identity*.  Both probes
(824, 825) attacked exactly me: 824 showed the outer channel is a positive floor
(no inner-carrier escape), 825 showed no per-prime re-weighting of the
transport closes it.  Both negatives were *norm-scale* negatives about the
metric-frame.

## 2. The creative-relabel: replace the NORM estimate by a TRACE-CLASS identity

The trace machinery already below the gate is far less sensitive to the 717
norm wall than the current norm chain admits.  In `PositiveTrace.lean`:

- `TraceAlong basis (A† ∘L B)` is a **diagonal series**, legal as soon as a
  `BasisHilbertSchmidtPairData` supplies sink-able `‖A‖²`+`‖B‖²` — **no ‖A‖≤1
  comparison anywhere.**
- `ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint` (:520) IS full Hilbert–
  Schmidt cyclicity, already proven.
- `ordinaryTrace_positiveComposition_re_nonnegative` (:238) gives `Tr(A†A) ≥ 0`
  already proven.

So the Creative idea C:

> Route the Gate through the **commutator trace-class** object rather than the
> **metric endpoint-norm** object.  The zero-corridor is detected not by
> `‖left∘A‖≤1` (needs ‖A‖≤1, the 717 wall) but by whether a Hilbert–Schmidt
> pair of *compressed/theta-smoothed* operators is trace-class with a **finite
> Hilbert–Schmidt norm** — a question about the *carrier* (Paley-Wiener/band),
> NOT a sharp norm inequality on two infinite-rank operators.

Concretely the replacement closure ladder:

```
closureC :  CC-square source -> (e.g. CompactRootPair, smuggling HS pair)
                  |   BasisHilbertSchmidtPairData (left, right)
                  |   source Summable E → trace-cert
                  v
        Q = .trace (positive signed diagonal)            (AGENTS §9, Contract M3)
                  |   Tr(A†A) ≥ 0                     (PositiveTrace:238, proven)
                  v
        weighted trace identity with explicit remainder
                  Q  read as *Tr(A†A) ≤ *QWlambda* + remainder D_S
```

The *difference from the norm-chain*: trace-class legality does NOT need a norm
≤ precomputed bound; it needs **summability of the absolute diagonal**.  The
summability is a *type-theoretic* fact about the HS pair (proven by the
pair-data), not an *analytic* fact about an operator norm.  In Lean, the
`traceProduct_adjoint_isCompactOperator` + `traceProduct_isTraceClassAlong`
closure is *already built*.  So Gate-3U's analytic wall, if re-instantiated by C,
becomes a **symmetry/creativity arrow**: no new adjac-net from a norm ≤1.

## 3 (real). The honest relocation: this only moves the gate to A0

The trade-off must be stated plainly, not sold:

- In the current norm-Gate, the bottom is Proof 717 (RH-scale: `‖A‖=‖A‖≤1` from
  a full-infinite/finite-family cancellation, beyond a finite grid).
- In the trace-Gate, the bottom is the **carrier-existence question** of A0 /
  `A1SeamBOperatorCarrierProbe`: does a NONZERO `CompactLogTest` test admit an
  HS / trace-class witness through the Hilbert basis?  The whole 824/825 numeric
  apparatus (transported-Sonin, finite grid) is exactly the wrong tool for that
  too.

So C does **not** prove RH and does **not** lower the analytic-floor to zero.  It
reframes the floor as:

```
new bottom (H0) : exists a nonzero CompactLog remember, ∀ n [p(0)=0] test z
                  with src/Tr identity and finite trace witness,
                  tie to Q = htt-class finite remainder.
```

That state is atomic between the current "operator-norm-717" bottom and the
"trivial positive-trace" machinery.

## 4. Honest OK-verdict

C is **recommended as a plan-worthy redesign** because:
1. It uses already-proven HS cyclicity + positivity traces (no new analytic
   norm estimate of the 717 kind has to be blasted from first principles).
2. It relocates the open object from "RH-scale operator wall" (numeric-unfriendly,
   no more numeral at 824/825) to "carrier existence on a concrete compact band"
   (the A0 corridor, which probes 024/073/this have ALREADY localized as the one
   real seam that A2 can't patch by a type-swap).
3. It is backward-compatible: nothing has to be removed; contract new trace-Gates
   `Ccomposer` next door; old norm-Gate stays ratioed as status.

BUT — the same discipline that botched 824/825's overclaim must apply here:

- It is **not** a lower-ordering, not a Lean lemma, not RH.  The trace lane still
  bottoms at **carrier existence for a nonzero band-L2 test with an HS trace
  witness**, which is the **A0 open item**, and that is *genuinely* an analytic
  band estimate, not a sign/type move.

## 5. Next step (concrete, small, reversible)

Carve a new Dev Probe `C1TraceGateRelocationProbe.lean` that does the following
with ZERO new math: restate Gate 3U's scalar as the ordinary positive trace of a
Hilbert-Schmidt pair on the CompactLog band, proving (using only existing HS
cyclicity + positivity + tail-bound theorems) that **whenever a nonzero HS
witness exists (the A0 hypothesis), the Gate becomes a *trivially*-provable
trace inequality**, i.e.

```
Gate3U-at-source  <=  Tr(A†A)-bound   provided   nonzero-HS-witness(v)  (A0)
```

This separates the analytic research (A0 carrier existence) from the *formal*
closure (trace-class plumbing that PositiveTrace already gives).  If that
separation is right, then the only real crunch is building a nonzero
`CompactLogTest` with a windowed boundary detector; if it is wrong (carrier
instrumentation throws off the identity), the probe pins exactly where.

That probe is the defensible fork action of route C.  It needs no new math, only
a pencil-shaped assembly of existing theorems, so it is a safe, reversible
first step. Its build/axiom audit is the deliverable that decides whether C is
worth a full plan.