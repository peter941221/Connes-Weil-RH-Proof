# 1093 - P2/S2 balanced-leg owner: drop the bare-F_K premise (task #8)

Date: 2026-09-02. Follows 1091 (leg-design recon pin), record 1092 (the per-term
C-absorbed brick that LANDED GREEN but still rests on record 1065's bare prolate-factor
premise), and the committed record 1065 brick `Dev/C1ProlateRootCommutatorPairOwner.lean`.
This lands **task #8**: a Lean owner for S2 whose legs are ALL named operators, so neither
leg is the bare prolate factor `F_K` and record 1065's premise disappears entirely. RH
unclaimed; GATE 1 mainline untouched; non-mainline / gated (local, not yet committed).

Numbering: takes the next free number **1093**, out of sequence, alongside this producer
thread's 1090/1091/1092. Committed HEAD is record 1087; 1088/1089 are reserved in prose for
mainline and neither is double-claimed here (flagged as in 1090/1091).

## 0. Verdict up front

```text
ROUTE = A: the "product of two Hilbert--Schmidt operators" split, legs drawn from {C, C^dagger, K_S}.

  pairData_CK : left := C^dagger , right := K_S    traceProduct = C o K_S
  pairData_KC : left := K_S      , right := C       traceProduct = K_S o C   (uses K_S self-adjointness)

S2 now follows from THREE named column-sum contracts, each WEAKER than record 1065's premise:
  targetProlateRootFactorHS          : Summable ‖C e_i‖^2       (flat / true for any Schwartz symbol)
  targetProlateRootFactorAdjointHS   : Summable ‖C^dagger e_i‖^2 (adjoint-invariant twin of the above)
  targetProlateRemainderHS           : Summable ‖K_S e_i‖^2     (= PROBE-P2 control row Tr(K_S^2), finite per window)

NO leg is bare F_K.  Record 1065's `targetProlateRemainderFactorSummable` (Tr(K_S) < inf,
measured growing ~xi^0.4 for {2,3,5} in record 1067 = FAILING) is REPLACED by the strictly weaker
`K_S in HS` (= Tr(K_S^2)) plus two flat root contracts.  This SUPERSEDES record 1092's absorbed-leg brick
for the S2 obligation.
```

## 1. Why this split drops the premise (the argument)

Record 1065/1092 factor `[C, K_S]` through a base pair that carries the bare prolate factor `F_K`:
either as an explicit leg (1092's `{F_K . C^dagger, F_K}` / `{F_K, F_K . C}`) or via `boundedSandwich`
(1065).  Either way one leg is `F_K`, so the owner needs `F_K in HS`.

The balanced-leg route instead factors EACH commutator term directly as `(HS)^dagger . (HS)` using only
named operators:

```text
  C o K_S   =  (C^dagger)^dagger . K_S      legs {C^dagger, K_S}    both HS by contract
  K_S o C   =  (K_S)^dagger . C             legs {K_S, C}            both HS by contract

  [C, K_S]  =  (C o K_S) - (K_S o C)        reassembled by l2Sum + smulRight(-1)
```

Because `BasisHilbertSchmidtPairData.traceProduct` is always `left^dagger . right`, and because the HS-norm
is adjoint-invariant (`A in HS iff A^dagger in HS`), each term is a product of two named HS operators - hence
trace-class by Cauchy-Schwarz along any orthonormal basis.  That is exactly S2, and it NEVER touches `F_K`.

## 2. The three contracts vs record 1065's premise

```text
+------------------------------------+------------------------------+---------------------------+
| contract                           | what it IS                   | model status            |
+------------------------------------+------------------------------+---------------------------+
| targetProlateRootFactorHS          | C is a Fourier multiplier    | FLAT, true: ‖C‖_HS =    |
|   (KC right leg)                    | by F(h); HS norm = ‖F h‖_2  | ‖F h‖_2 < inf for any   |
|                                     |                              | Schwartz h; window-free |
+------------------------------------+------------------------------+---------------------------+
| targetProlateRootFactorAdjointHS   | same fact on C^dagger        | identical (adjoint      |
|   (CK left leg)                     |                              | invariance of HS norm)  |
+------------------------------------+------------------------------+---------------------------+
| targetProlateRemainderHS           | Tr(K_S^2) = ‖K_S‖_F^2        | PROBE-P2 control row    |
|   (CK right + KC left legs)         |                              | 8.35->11.42, FINITE at  |
|                                     |                              | every window; strictly  |
|                                     |                              | WEAKER than Tr(K_S)<inf |
+------------------------------------+------------------------------+---------------------------+

vs record 1065 premise targetProlateRemainderFactorSummable = Tr(F_K^dagger F_K) = Tr(K_S),
   measured growing 16.2 -> 34.3 over four octaves (~xi^0.4) in record 1067 => FAILS O(1).
```

Why `K_S in HS` is strictly weaker than `F_K in HS`: `K_S = F_K^dagger . F_K` is a positive contraction with
every eigenvalue in `[0,1]`, so `lambda <= lambda^2` reverses to `sum lambda >= sum lambda^2`; therefore
`{sum lambda < inf} => {sum lambda^2 < inf}`.  The premise that FAILED (record 1067) implies the one this
owner needs; the converse is not asserted, so the new obligation is genuinely smaller.

## 3. What is PROVEN here vs OWED

PROVEN in `Dev/C1ProlateRootCommutatorBalancedLegOwner.lean` (module builds green):

```text
  - pairData_CK.traceProduct = C o K_S      (adjoint algebra: (C^dagger)^dagger = C)
  - pairData_KC.traceProduct = K_S o C       (needs K_S self-adjointness, derived inline from
                                              targetProlateRemainderFactor_adjoint_comp_self)
  - the l2Sum + smulRight(-1) reassembly has traceProduct = cc20Commutator(C, K_S)
  - S2 closes through the UNCHANGED generic consumer _of_pairData (leaf :243), so the leaf's
    targetProlateDetectorRootCommutatorTraceLegality statement and the two-contract F1' corollary
    (:370-381) keep their exact signatures.

OWED to producers (none is a Lean proof yet, same status as record 1065's premise was):
  - discharge targetProlateRootFactorHS / ...AdjointHS : flat/true for any Schwartz symbol C; the
    owner transfer (Gaussian stand-in root -> actual selected convolution root per-owner) is owed
    separately and is bounded bookkeeping (record 1090 Q1 shows any Schwartz h qualifies identically).
  - discharge targetProlateRemainderHS : this IS PROBE-P2's control row, finite at every measured window;
    a Lean summability proof over globalBasis remains to be written.
```

## 4. Relationship to the sibling bricks (dedup note)

Three owners now exist for the S2 trace product; they are NOT duplicates - each rests on a different analytic
posture and is kept so the strict weakening chain is auditable:

```text
  record 1065  C1ProlateRootCommutatorPairOwner         : base (F_K,F_K) + boundedSandwich   -> needs F_K in HS [COMMITTED]
  record 1092  ...PerTermPairOwner                      : legs {F_K . C^dagger, F_K} / {F_K, F_K . C} -> still needs F_K in HS (LOCAL)
  record 1093  ...BalancedLegOwner  (THIS RECORD)       : legs {C^dagger, K_S} / {K_S, C}    -> needs only C,C^dagger,K_S in HS (LOCAL)
```

All three close S2 through the SAME generic `_of_pairData`; only the leg construction and the named contracts
differ.  1093 is the intended canonical owner once its three contracts are discharged; 1065 stays as the committed
reference, 1092 as the intermediate stepping-stone (both local until commit).  No new shared-layer primitive was
required - unlike recon 1091 §4's prediction (which anticipated a SVD-leg "balanced nuclear leg" helper), this split
uses only named operators and the already-committed `l2Sum` / `smulRight` / `_of_pairData`, so there is nothing to dedup
against the seven `DividedDifferenceKernel.lean` importers for THIS turn.

## 5. Honesty ledger

- Adds ONE Lean module; no change to the leaf S2 statement, the two-contract F1' corollary, or GATE 1 mainline.
- RH unclaimed. Non-mainline / gated (local build green; not committed).
- The three contracts are NAMED but not yet PROVEN in Lean; their model support is documented in §2.

## 6. Next steps

1. [DONE this record] Land the balanced-leg owner `Dev/C1ProlateRootCommutatorBalancedLegOwner.lean` green, dropping
   record 1065's bare-F_K premise via legs `{C^dagger, K_S}` / `{K_S, C}` and three named HS contracts.
2. OWED - discharge the three contracts (producers): `targetProlateRemainderHS` is PROBE-P2's finite control row;
   the two root contracts are flat/true for any Schwartz symbol. Owner transfer (stand-in -> selected root) owed separately.
3. OWED - commit 1092 + 1093 together (staged-file hygiene check first): promote `...BalancedLegOwner` to the canonical
   S2 owner; keep 1065 as committed reference, retire or annotate 1092's absorbed-leg brick as superseded.
