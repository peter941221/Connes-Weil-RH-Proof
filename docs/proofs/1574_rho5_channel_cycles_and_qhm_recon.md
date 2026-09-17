# 1574 — boundary-carrier cycles of the leakage channels (LANDed) + the Q-hM delay/advance verdict

Date: 2026-09-17.

Status: FORMAL LEAF + PAPER RECON. This record carries two deliverables of
step (c) of the 1568-ordered wave: the cycle leaf
`C1G8R5LeakageChannelCycles` (GREEN, try11, 3957 jobs, standard axioms, zero
`sorryAx`), and the adjudication of the `Q-hM` identity question that records
1572/1573 left as "the single next question". No estimate is proved; the
gate (★), B4, the rho5 combined-row identity, the source/ambient transport
and the R4 wrapper stay OPEN. RH not claimed.

## 1. The landed declarations

File: `ConnesWeilRH/Dev/C1G8R5LeakageChannelCycles.lean` (+ `...CyclesAudit.lean`),
imports only the record-1569 split leaf. Three theorems, all `ordinaryTraceAlong`
identities transported by `ordinaryTraceAlong_traceProduct_eq_cyclic`
through the committed Hilbert-Schmidt pair owners:

```text
(1) ordinaryTraceAlong_g8R5LeakageResponseChannel_eq_cyclic
      tr_source (K^dag J1^dag K)
        = tr_{actualBandPairCarrier} (pair-leg sandwich on pairedBoundaryBasis)

(2) ordinaryTraceAlong_g8R5LeakageTotalChannel_eq_cyclic
      tr_source (K^dag (-G^dag) K)
        = - tr_{commonBoundaryCarrier} (baseG.left o K o (baseG.right o K)^dag)
      (the minus is carried by the cycled operand as an operator Neg,
       NOT as a scalar (-1 : C) • - see section 3, hazard (i))

(3) ordinaryTraceAlong_g8R5LeakageRemainderChannel_eq_cyclic_pairSum
      tr_source (K^dag R^dag K) = [RHS of (2)] + [RHS of (1)]
      (the 1569 trace split transported through both cycles; `abel` closes
       the scalar rearrangement)
```

What they buy: the ρ5 producer's channel traces are now indexed on the
BOUNDARY carriers - the same carrier side where the records 1492/1493/1495
boundary-leg machinery and the map-042 OUT-side live, and the cycled
operands are exactly the pair legs `M oL J oL N`-shaped transports
(`baseG.left oL K`, `baseG.right oL K`) of record 1534's column shape. Pure
cyclicity bookkeeping: no estimate, no sign premise, no identification of
either side with `qw` components (law F24 respected: the channels stay as
compiled named operators).

## 2. Acceptance, try by try (log numbers are this wave's lake logs)

```text
try1  (1750): 31 errors - missing opens (copied the PSplit open union),
               set_option placement (moved above docstring per house rule)
try2  (1751): rw-direction class: htp needs the def name in the rw list;
               `rw [← htp] at hcyc` backwards -> `rw [htp] at hcyc`;
               thm3 `rw [← hsplit]` backwards -> `rw [hsplit]; abel`
try3-6(1752-55): deterministic typeclass timeouts (20000 hb) at every
               `(-1 : C) •` on a non-endo CLM with huge head expression,
               in statements AND in `have := rfl` proofs
               -> sign restructured as Neg everywhere (pairU redesign:
               no smulRight in the pair; plain K^dag/K sandwich; sign moved
               to the trace by two def-level `ordinaryTraceAlong` rewrites)
try7  (1756): •-in-a-have produced "Unknown constant Subtype.adjoint"
               (same hazard, new face); thm1 :119 whnf-timeout flake
               (did not recur try9+)
try8  (1757): `rw [← htpU]` backwards -> `rw [htpU, g8R5LeakageTotalChannel];
               simp`; `tsum_neg` inside the same rw list misses (the lambda
               body head is not syntactically a negation yet) -> split:
               rw ordinaryTraceAlong first, then simp only the flip set
try9  (1758): simp stall - the negation sits in the RIGHT inner slot
               (`⟪b i, -(T (b i))⟫`), `inner_neg_left` cannot match;
               needs `inner_neg_right` (precedent C1G8P1EndpointOrientation)
try10 (1759): `apply neg_injective` applied the wrong direction: it is
               `Function.Injective Neg.neg`, so applying it to goal
               `-a = -b` matches the CONCLUSION `a = b` and leaves the
               double-negation goal `- -a = - -b`. Correct closing term
               for `-a = -b` from `h : a = b` is `congrArg Neg.neg h`.
try11 (1760): GREEN - footer "Build completed successfully (3957 jobs)",
               zero ^error:, zero sorryAx, audit 3/3
               [propext, Classical.choice, Quot.sound]
```

## 3. The Q-hM verdict (the 1572 "single next question", adjudicated)

Question (record 1573 section 2): does the 1535 shortcut premise

```text
hM : E oL M_p oL sourceInclusion = M_p oL sourceInclusion
```

hold for the ACTUAL forward-Euler-exposed factor `M_p` of the record-1499 B2
factorization? Transcribed evidence, mechanism first:

- The Sonin carrier is radial BY DEFINITION:
  `ccm24ArchimedeanSoninClosedSubspace = ccm24LogRadialSupportClosedSubspace ⊓
  ccm24ArchimedeanFourierSupportClosedSubspace`
  (`Source/CC20Concrete/CCM24HardyTitchmarsh.lean:379-381`). So the
  SOURCE columns are already radial - but `hM` is a statement about the
  IMAGE of `M_p` applied to them, and the inf definition constrains only
  the domain side. `E` must re-act on `M_p (sourceSoninCarrier)` columns.
- The prime Euler transport is a DELAY:
  `ccm24PrimeEulerTransportEquiv p u =ᵐ[μ] fun t => u t - c_p • u (t - log p)`
  (`Source/CC20Concrete/CCM24EulerTransport.lean:97-110`). A delay
  preserves lower half-line support: `supp u ⊆ [tau, ∞)` gives
  `supp(Tu) ⊆ [tau, ∞)` (it reads further RIGHT, where u may vanish).
- The actual `M_p` contains ADJOINTS of such transports:
  `M_p = (suffixEulerAmbientProduct S)^dag oL (I - frame frame^dag) oL
  (normalizedPrimeEulerFrameTransport p)^dag oL parameterizedFiniteEulerFactor 1 (p::S)`
  (`Bridge:66-85`). The adjoint of the delay is an ADVANCE - it reads
  `u(t + log p)`, i.e. pulls mass LEFTWARD across the boundary `tau`. A
  column that is nonzero anywhere in the first log-period `[tau, tau + log p)`
  is mapped to something nonzero on `[tau - log p, ∞)`, which provably
  escapes the FIXED-scale half-line region defining `E`.

Typed verdict: **the fixed-scale `hM` shortcut is blocked for the actual
`M_p` by the advance-in-the-adjoint mechanism**; the 1534 warning
("certificates do not cover arbitrary actual M") now has its concrete
mechanism. This is a PAPER mechanism note against transcribed definitions,
not a formal no-go theorem: no Lean statement asserts `¬hM`, and the
escape claim needs one written-down support computation before it could be
promoted to a lemma.

Consequences registered:

1. B4 does NOT collapse to the single gap square-sum for the actual
   columns; slot (2) of the 1573 chain keeps BOTH premises unless the
   scale-adapted alternative below is formalized.
2. Candidate replacement (next registered paper item, no spend yet): a
   SCALE-ADAPTED `hM'`: `E_{lambda'} oL M_p oL sourceInclusion =
   M_p oL sourceInclusion` with `lambda'` finitely shifted (the advance is
   exactly `log p` per factor; a finite `k = #S`-shift absorbs all of
   them). The 1535 consumer is stated at one fixed scale, so this needs
   the consumer re-instantiated at `lambda'` - which the consumer's
   quantifier over `lambda` already permits.
3. If the adapted identity fails to localize cleanly, the fallback is
   honest: estimate the radial defect column too (1534 style), paying the
   support-EDGE cost that record 1572 section 2 priced at logarithmic.

## 4. What moves, what does not

- MOVED: the ρ5 channel traces now have committed boundary-carrier
  presentations (section 1); the Q-hM question has a typed verdict with its
  mechanism written down; three new formal hazards are registered in
  AGENTS §7b (non-endo `•` typeclass timeout; `inner_neg_right`; the
  `neg_injective`/`congrArg Neg.neg` direction).
- NOT MOVED: no summability, no trace-class margin, no `qw` identification
  anywhere. (★), B4 (both premises, pending `hM'`), the rho5 combined-row
  identity, the source/ambient transport and the R4 wrapper remain OPEN
  exactly as registered in map 042. WO-S / WO-B statuses unchanged.
  RH not claimed.
