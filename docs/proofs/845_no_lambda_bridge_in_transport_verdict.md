# Gate-3U 攻击 845:NEGATIVE — "unit-λ × transport-norm" 桥是死路, transport 从不改 λ,generic-λ `hfactor` 无 transport 可达路径

Date: 2026-08-07 · Status: source-verified structural verdict (no new build needed;
840/843/844 的 Lean 结构事实直接决定)
This self-created attack on the 3U open (844: exactly ONE premise left, generic-λ
`hfactor`) tried the 843/844-suggested lever:
> "unit-λ HS (axiom-clean) × finite-Euler transport-norm (T = log-p shifts, norm-preserving)
> ⇒ bound ≤ C·‖unit factor‖, to close generic-λ hfactor".

**Reading the real `transport`/Gram/band source shows this lever CANNOT move λ.**
845 is a decisive negative: the finite-Euler transport acts **at one fixed λ** on both
sides, so there is **no transport path from the unit-scale HS theorem to a generic-λ gate**.

## 0. 先讲结论

**845's proposed bridge is not "hard", it is structurally absent.** The transport
`T = ccm24FiniteEulerTransportEquiv` is **λ-independent** (built purely from `List
CCM24VisiblePrime` of log-p shifts, `CCM24EulerTransport.lean:76/202`). Every place it
acts (`finiteEulerFrame`, `restrictedTheta`, the Gram) connects two **same-λ**
subspaces. So:

```
  correct 845 lever   :  unit-λ HS   --transport-->  generic-λ HS   (NOT FOUND)
  actual structure    :  unit-λ HS   ;  transport acts at the SAME λ, never moves λ
```

The only HS theorem with the setting-free factor is **hard-pinned to `unitSoninScale`**
(`sourceProlateHilbertSchmidtFactor_unit_summable_of_rawCrossing`,
UnitScaleProlateTraceReduction:514). To get generic-λ you need HS at the **chosen λ** —
and there is **no** transport, conjugation, or scaling bridge that carries a same-factor
HS from unit to that arbitrary λ. 840 already found this ("scattering phase non-
translation-invariance"); 845 now pins the *reason* in the current objects: the
lambda-dependence lives in **one radial cutoff `E_λ = ccm24LogRadialSupport λ`**
(ProjectionTrace:76-83), which the transport simply does not touch.

## 1. Evidence (each Lean object/compare, no new build)

### 1a. transport is λ-free

`CCM24EulerTransport.lean:76` `ccm24PrimeEulerTransportEquiv (p : CCM24VisiblePrime)`
and `:202` `ccm24FiniteEulerTransportEquiv (S : List CCM24VisiblePrime)` have **no
`lambda` in their signature**. All they do is compose shifts by `-Real.log p`
(TransportBounds:46-94). Only-place-it-appears-in-a-subspace:
`CCM24FiniteEulerRestrictedSoninData.restrictedTheta` connects
`λ-LogRadialSupport ⊓ λ-FourierSupport` on **both** sides (FiniteEulerSoninTransport.lean
:20-45) — the **same λ** is on both ends of `T`. λ is never an *argument being moved*.

### 1b. the Gate runs at one fixed λ

`canonicalRealGate3UAt {rho} owner λ sourceBasis bound : Prop`:
`|(ordinaryTraceAlong sourceBasis (finiteEulerTargetCommutatorResponse owner λ (canonicalFamily owner))).re| ≤ bound`
(FiniteSCanonicalRealGate.lean:62). The `λ` on the left of the `≤` and the `λ` inside
`finiteEulerTargetCommutatorResponse ... λ ...` are **the same λ**. There is no
quantifier over a second λ; `canonicalFamily owner` is the fixed family.

### 1c. the source-band trace needs the factor at the SAME λ

`sourceBandGramResponse owner λ family` (FiniteSBandTrace:359) = `-sourceGramResponse
owner λ family`, and its one true commutator-only identity
`sourceBandGramResponse_eq_completedCommutator owner λ family`:
```
(sourceInclusion λ)† ∘L sourceBoundaryCommutator owner λ ∘L
  finiteEulerAmbientGram family ∘L sourceInclusion λ ∘L finiteEulerGramInv λ family
```
Every `λ` is the same λ; the `ambientGram (family) : finiteEulerAmbientGram` (GramResponse
:377) = `frame† ∘ frame`, with `frame = T ∘ sourceInclusion λ` — **even the Gram's transport
is post-composed with `sourceInclusion λ`, forcing the same λ**. The factor
`Q_λ∘(E_λ∘R_λ)` (SourceProlateTrace:35) has λ only through the radial cutoff `E_λ`.

### 1d. the only HS theorem, and its unit pin

`sourceProlateHilbertSchmidtFactor_unit_summable_of_rawCrossing` states, for a basis on
the **unit**-scale carrier `H`:
```
Summable ‖sourceProlateHilbertSchmidtFactor unitSoninScale (basis i)‖^2
```
The single word `unitSoninScale` is the entire λ-vs-unit distinction. There is **no
generic-λ twin** of this theorem, nor a transport identity `Factor λ = T(unit)` (that
would be conjugation by a λ-map the repo does not have; 840 already blocked the only
candidate `m(2πξ)`).

## 2. Why this is a HARD no, not a "still open" 

Four independent routes, same wall:

| route | would need | actual reason it is blocked |
|---|---|---|
| transport-norm bridge (843/844) | `Factor λ ≈ T·Factor(unit)` to transfer a bound | transport `T` never touches λ; cannot produce `at λ` |
| conjugation (840) | unitary SU(2) λ↔1 | scattering phase `m(2πξ)=Γ(1/2−2πiξ)/Γ(1/2+...)` not log-translation-invariant (840) |
| a λ generic HS **slab** | produce `Summable ‖Factor λ‖²` | no such repo theorem (only `unit`), and factor's λ is not a norm-to-norm lift |
| trace-arithmetic-only | `|Tr(sourceBand)|≤|Majorant|` needs Trace class at λ | the Gate-3U bound itself needs λ-residence (`sourceProlateRemainder_isTrace...` must be at λ) |

So: **generic-λ `hfactor` is not reachable through the transport.** It is reachable
only if there is a genuine analytic family `λ ↦ Summable ‖Factor λ‖²` (840 route A,
"make λ appear in a transport-based diagonal"), which the repo **does not have**.

## 3. Where this leaves Gate-3U (honest)

- NO new axiom or sorry, and **no claim "Gate-3U done"**.
- The structural collapse (843/844) is real and Lean-verified: *if* HS holds at the
  end λ, Gate ⟺ `|Tr(sourceBand λ)|` or nil.
- The single operator-generic open (844) is *still* the generic-λ HS of the prolate
  factor, **and** there is no transport/conjugation/scaling bridge in the repo to
  supply it. So "打穿 3U" via transport is **closed as a dead road**.

**The only live roads (unchanged from 840/842, now with the transport-dead pinned):**
1. **genuine λ-dependent analysis**: an analytic family `λ ↦ ‖prolateFactor λ‖²`
   (a real analytic piece, no sieve), OR
2. **Route-C / trace-lane**: move the whole 3U off the operator wall (see 841/842),
   accepting the relocation (not a reduction) to the pole-pairing floor, OR
3. **decide the one sign (842)**: prove the concrete Canonical-Weil ≤0 sign is
   positive, or prove primary-density-diff=const>0 is impossible — the non-`hs`.
All three are **new analysis**, not transport plumbing.

## 4. Honest cost / state

| item | state |
|---|---|
| Gate-3U collapse to `|Tr(sourceBandλ)|≤·` + outer=0 | Lean-verified (844) |
| unit-λ HS | axiom-clean (839) |
| generic-λ HS | **open**, and 840/845: no transport/conjugation/scaling bridge exists |
| 845 "transp-norm" lever | **dead** (transport λ-invariant) |
| live next | genuine-λ analysis / Route-C / 842 sign decision |

RH is still not claimed; nothing here is unconditional.

## Repro / evidence

No new code. Read:
```
Source/CC20Concrete/CCM24EulerTransport.lean:76,202      (transport defs, no λ)
Source/CC20Concrete/CCM24FiniteEulerSoninTransport.lean:20-45 (theta: same λ both sides)
Source/CCM25Concrete/CCM24FiniteSTransportBounds.lean:46-144  (upper/lower bounds for this T)
Source/CCM25Concrete/CCM24FiniteSProjectionTrace.lean:76-109  (E_λ, Q_λ, R_λ)
Source/CCM25Concrete/CCM24FiniteSGramResponse.lean:97-153     (finiteEulerFrame/Gram/GramInv)
Source/CCM25Concrete/CCM24FiniteSBandTrace.lean:375-426       (sourceBandGramResponse →)
Source/CCM25Concrete/CCM24SourceProlateTrace.lean:33-40       (factor = Q∘(E−R₀))
Source/CCM25Concrete/CCM24FiniteSCanonicalRealGate.lean:62     (gate at one λ)
Source/CCM25Concrete/CCM24UnitScaleProlateTraceReduction.lean:514 (unit-only HS)
```