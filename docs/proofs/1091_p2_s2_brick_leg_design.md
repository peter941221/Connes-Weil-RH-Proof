# 1091 - P2/S2 brick leg design: per-term C-absorbed pairData (recon pin)

Date: 2026-09-01. Follows 1090 (PROBE-P2 verdict Q2-OPTIMAL-TERMS), 1073
(the D-weighted re-route that OWES producers P1/P2), and the committed record
1065 brick `Dev/C1ProlateRootCommutatorPairOwner.lean`. This is a RECON / design
note, not a Lean change: it pins the exact leg shape of the S2 producer so the
module can be written in one pass. RH unclaimed; GATE 1 mainline untouched.

Numbering: committed HEAD is record 1087; 1088/1089 are reserved in prose for
mainline ("endpoint audit = map 004", "CC20 re-anchor design"); 1090 was this
producer thread's P2 gate + probe. This takes the next free number **1091**, out
of sequence, flagged here so neither reservation is double-claimed on resume.

## 0. Verdict up front (what recon decided)

```text
ROUTE = B2: two SEPARATE per-term pairData with C-ABSORBED legs, combined by the
          already-committed l2Sum + smulRight(-1), fed into the EXISTING generic
          _of_pairData.  NOT a re-shape of 1065's shared (F_K, F_K) base pair.

SINGLE NEW ANALYTIC LEMMA OWED = one "balanced nuclear leg" helper: for each named
term T in {C o K_S, K_S o C}, exhibit left, right with left^dagger . right = T and
BOTH column-norm sums O(1) over globalBasis.  The mechanism (the decaying root
symbol row-weighting the prolate kernel to nuclear-bounded legs) is IDENTICAL for
both terms -> ONE shared helper, not two ad-hoc proofs.

EVERYTHING ELSE IS PLUMBING already committed in record 1065:
   - traceProduct identities (CK / KC / signed [C,K_S])     : C1ProlateRootCommutatorPairOwner.lean:110-180
   - l2Sum + smulRight(-1) -> [C, K_S]                      : 1065 :154-180
   - _of_pairData -> S2 (generic over ANY pairData w/ the right traceProduct)
   - two-contract corollary consuming P1 + P2               : C1ProlateResponseTraceLegalityUnitScale.lean:370-381

LEAF UNCHANGED: targetProlateDetectorRootCommutatorTraceLegality (S2 statement) and
the _of_rightSmoothing_and_rootCommutator corollary keep their exact signatures; the
new per-term brick simply supplies hcomm.
```

## 1. Why 1065's structure cannot be reused as-is

The committed brick factors `[C,K_S]` through ONE shared base pair:

```text
targetProlateRemainderSquarePairData (base) : left = F_K, right = F_K     [needs F_K in HS]
    |  boundedSandwich C id        -> CK term : new_right = F_K  (BARE)   <- fails for {2,3,5}
    |  boundedSandwich id C        -> KC term : new_left  = F_K  (BARE)   <- fails for {2,3,5}
```

`boundedSandwich` keeps a leg Hilbert-Schmidt ONLY by the HS ideal property
(`summable_normSq_precomp`): composing an HS operator by a BOUNDED one stays HS.
So it PRESERVES whatever the base leg's summability already is - it cannot TAME a
non-HS base leg, because `F_K . (bounded)` still has non-summable columns when F_K
alone does not.

```text
  [source sibling]                [1065 target brick]              [why the asymmetry]
  prolate factor A in HS          base leg = bare F_K               source prolate genuinely
  (F2, measured flat)             needs F_K in HS                   HS; target F_K is not
        |                               |                           (1067: Tr(K_S)_model grows)
   boundedSandwich D              boundedSandwich C
        v                               v
  legs stay HS                     legs need F_K HS -> FAILS
```

This is the exact reason S2-FK-HS fails on target but holds on source, and why the
D-weighted re-route (1073) exists: P2 must be produced WITHOUT `F_K in HS`, by a leg
construction that folds the root's decaying symbol INTO each leg.

## 2. What the probe licenses (existence + bound witness, not yet proof)

From PROBE-P2 (record 1090 s4), deciding family `{2,3,5}`, k=1:

```text
+---------------------------+----------+----------+----------+----------+---------+
| quantity                  | N1025    | N2049    | N4097    | N8193    | slope8x |
+---------------------------+----------+----------+----------+----------+---------+
| C o K_S nuclear           |   4.6636 |   4.6391 |   4.6280 |   4.6266 | -0.004  |
| K_S o C nuclear           |   4.6636 |   4.6391 |   4.6280 |   4.6266 | -0.004  |
| ||K_S||_F^2 (control)     |   8.3477 |   8.3830 |  10.1132 |  11.4231 | +0.151  |
+---------------------------+----------+----------+----------+----------+---------+
```

Each NAMED term is INDIVIDUALLY nuclear with a flat, decreasing O(1) norm (~4.63), while
bare `||K_S||_F^2` grows (+0.151). Nuclearity of T guarantees the EXISTENCE of an HS-leg
factorization `T = left^dagger . right` with `‖left‖_HS, ‖right‖_HS <= O(nuclear(T))`; the
balanced split has leg HS-norm squared at most the nuclear norm. So a bounded-leg pairData for
each term EXISTS and is uniformly O(1) across octaves - but the flatness is model evidence of
existence + bound, NOT yet a Lean proof of column-summability. That gap is the owed lemma (s4).

## 3. The pinned leg shape

Two per-term pairData, each built DIRECTLY from explicit analytic legs (not via a shared base):

```text
pairData_CK : BasisHilbertSchmidtPairData (G := finiteSCarrier) globalBasis
    left  := <C-absorbed leg>      right := <prolate-kernel leg>       traceProduct = C o K_S
    left_summable_normSq / right_summable_normSq : O(1), proven by the balanced-nuclear-leg helper

pairData_KC : ...
    left  := <prolate-kernel leg>  right := <C-absorbed leg>           traceProduct = K_S o C
    (same helper, roles mirrored)

targetProlateRootCommutatorPairData   [REBUILT on these two legs; name + traceProduct kept]
    := l2Sum(pairData_CK, smulRight(pairData_KC, -1))                 : 1065 :161-164 carries over

targetProlateDetectorRootCommutatorTraceLegality_of_pairData           [UNCHANGED, generic]
    (pairData = rebuilt commutator pairData) (hpair = traceProduct = cc20Commutator C K_S)
        ->  S2
```

Because the leaf's `_of_pairData` is GENERIC over any `BasisHilbertSchmidtPairData` whose
traceProduct equals `cc20Commutator C K_S`, the rebuilt brick drops in with no change to the
S2 statement, the two-contract corollary, or the capstone.

### 3a. Mechanism of the leg (model picture; Lean form owed)

In xi-basis C is diagonal `diag(c_amp)` with decaying Schwartz symbol `c_amp`, and K_S has kernel
`K_tilde`. Then `(C o K_S)(xi, eta) = c(xi) * K_tilde(xi, eta)`: weighting the prolate kernel's
ROWS by the decaying Gaussian keeps the resulting operator nuclear-bounded (the same "any
Schwartz weight beats the sub-polynomial raw mass" mechanism as records 1063/1068). The balanced-nuclear-leg
helper exhibits `left` / `right` from this row-weighted kernel and proves both column-norm sums are
O(1) - the O(1) bound is exactly what PROBE-P2 measured (nuclear ~4.63 flat).

## 4. What is OWED vs PLUMBING (the split that sizes the Lean turn)

| piece | status | pin |
|-------|--------|-----|
| traceProduct identities CK / KC / signed [C,K_S] | COMMITTED (reuse) | 1065 :110-180 |
| l2Sum + smulRight(-1) -> [C,K_S] | COMMITTED (reuse) | 1065 :154-164 |
| `_of_pairData` generic consumption of any such pairData | COMMITTED (reuse) | C1ProlateResponseTraceLegalityUnitScale.lean:243 |
| two-contract corollary (P1 + P2 -> F1') | COMMITTED (reuse) | C1ProlateResponseTraceLegalityUnitScale.lean:370-381 |
| **balanced-nuclear-leg helper** (C-absorbed O(1)-HS legs for each term, summability PROVEN) | **OWED - the only new analytic work** | this record s3 / s4 |
| owner transfer (Gaussian stand-in root -> actual selected convolution root per-owner) | OWED separately; Q1 shows any Schwartz h qualifies identically, so bounded bookkeeping | 1090 s5.2 |

## 5. Dedup before writing the module

The balanced-nuclear-leg helper is a NEW leg-construction primitive. Before adding it, dedup
against the existing pairData/leg importers so it lands in the shared layer (`CC20Concrete`,
next to `PositiveTrace.lean` / `HilbertSchmidtIdeal.lean`) rather than as a private Dev def:

- The 7 committed importers of `DividedDifferenceKernel.lean` (incl. `RootSandwichedTrace.lean`,
  sibling `MovingDividedDifferenceKernel.lean`) already build kernel-derived legs - check whether
  the row-weighting leg is an instance of a helper they already expose.
- `boundedSandwich` / `l2Sum` / `smulRight` in `HilbertSchmidtIdeal.lean` are reused, not redefined.

## 6. Honesty ledger

- This record adds NO Lean object; it pins the leg shape from (a) the committed 1065 brick
  source, (b) the source-side sibling's confirmed base-factor-HS requirement, and (c) PROBE-P2's
  per-term nuclear-O(1) flatness. RH unclaimed; GATE 1 mainline untouched; non-mainline / gated.
- The balanced-nuclear-leg helper is NAMED but not yet written or proven; its O(1) bound rests on
  the model (record 1090 s4), to be promoted to a Lean summability proof in the module turn.

## 7. Next steps

1. [DONE this record] Pin the leg shape: route B2, two per-term C-absorbed pairData, one shared
   balanced-nuclear-leg helper owed; plumbing reused from committed 1065 + leaf.
2. OWED - write the Lean module (non-mainline, gated): the balanced-nuclear-leg helper in the
   shared `CC20Concrete` layer, then rebuild `targetProlateRootCommutatorPairData` on the two new
   legs; verify it feeds the unchanged `_of_pairData`. Dedup per s5 first.
3. OWED - owner transfer: replace the Gaussian Schwartz stand-in root with the actual selected
   convolution root per-owner (bounded bookkeeping, Q1 already shows any Schwartz h qualifies).
