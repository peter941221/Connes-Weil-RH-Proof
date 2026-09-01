# 1094 - P2/S2 balanced-leg contract reduction: three named contracts -> two (task #9)

Date: 2026-09-02. Follows record 1093 (`C1ProlateRootCommutatorBalancedLegOwner`,
GREEN + warning-clean), which closed S2 through **three** named column-sum contracts, and the
committed record 1065 brick it supersedes for the S2 obligation. This lands **task #9**: reduce
that contract set and pinpoint exactly what is genuinely owed analytically. RH unclaimed; GATE 1
mainline untouched; non-mainline / gated (local build green, not yet committed).

Numbering: takes the next free number **1094**, out of sequence alongside this producer thread's
1090/1091/1092/1093. Committed HEAD is record 1087; 1088/1089 are reserved in prose for mainline and
neither is double-claimed here (flagged as in 1090/1091).

## 0. Verdict up front

```text
ROUTE = reduce record 1093's THREE named contracts to TWO, then name what remains genuinely owed:

  #1  targetProlateRootFactorHS         : Summable ‖C e_i‖^2        (KC right leg)
  #2  targetProlateRootFactorAdjointHS  : Summable ‖C^dagger e_i‖^2 (CK left leg)   <- DROPS: #2 follows from #1
  #3  targetProlateRemainderHS          : Summable ‖K_S e_i‖^2      (= Tr(K_S^2), PROBE-P2 control row)

Reduction proven here (committed machinery only):
  P1  #2  =>  #1     HS column sum is adjoint-invariant (summable_adjoint_normSq, same global basis).
  P2  C o K_S col-summable from #3 + ‖C‖<inf alone   (postcomp, committed two-sided HS ideal property).
  P3  K_S o C col-summable from #3 + ‖C‖<inf alone   (precomp , same property via the adjoint).

Genuinely OWED analytic contract (NAMED, not yet discharged in Lean):
  targetProlateCommutatorTermNuclearity : each TERM C o K_S and K_S o C is IsTraceClassAlong
      (= summable DIAGONAL) along globalBasis - strictly STRONGER than each term being HS.
      On the continuum carrier it does NOT reduce to a bare-root contract (#1/#2), which FAIL for a
      generic Schwartz symbol (see section 2). PROBE-P2 measures it flat O(1), nuclear norm ~4.63.

S2 closes from just TWO named contracts via ..._of_twoContractBalancedPairData (#1 + #3, #2 derived).
```

## 1. The reduction argument (why #2 drops; why #3 carries the HS weight)

**#2 follows from #1.** `BasisHilbertSchmidtPairData.summable_adjoint_normSq`
(`Source/CC20Concrete/PositiveTrace.lean`, inside the `...PairData` namespace opened at L257) states
that a Hilbert--Schmidt column sum is **adjoint-invariant**: if `Summable ‖A e_i‖^2` then
`Summable ‖A^dagger f_j‖^2`, read on the same basis. Applied to `A = C = rootConvolution owner`, it
derives contract #2 (the CK left leg) directly from #1 (the KC right leg). So the two bare-root
contracts of record 1093 are one fact, not two - S2 needs only **one** named root contract.

**At the Hilbert--Schmidt level, each commutator term is col-summable from #3 + ‖C‖<∞ alone.** The
committed HS ideal property (`Source/CC20Concrete/HilbertSchmidtIdeal.lean`) is two-sided:

```text
  summable_normSq_postcomp   : A col-sum, B bounded  =>  (B o A) col-sum      [L36]
  summable_normSq_precomp    : A col-sum, B bounded  =>  (A o B) col-sum      [L56, via the adjoint cycle]
```

With `A = K_S` (col-summability is exactly #3) and `B = C` (a Fourier multiplier, hence bounded with
‖C‖ = ‖F h‖_inf):

```text
  P2   C o K_S   col-summable    from  postcomp(A=K_S, B=C)
  P3   K_S o C   col-summable    from  precomp (A=K_S, B=C)
```

So the **remainder contract #3 carries all of each term's Hilbert--Schmidt weight**; the bare-root
leg is a bounded factor and contributes no analytic content at this level. This is why record 1092's
absorbed-leg brick (which needed the bare prolate factor in HS) was over-strong: here even the root
factor enters only as `bounded`.

## 2. What is genuinely owed: per-term nuclearity, not a bare-root contract

The two lemmas above give each term being **Hilbert--Schmidt** (col-summable). That is *necessary* but
not *sufficient* for the leaf's obligation: `IsTraceClassAlong basis T := Summable fun i => <T e_i, e_i>`
is **conditional diagonal summability**, and a single HS operator need not have a summable diagonal
(the classic counterexample is `diag(1/n)`, which is in HS but whose diagonal diverges). A product of
**two** HS operators does (Cauchy--Schwarz along the basis - exactly what record 1093's pairData route
uses via `summable_traceProduct_diagonal`), so the owed analytic fact is that each **term** is nuclear:

```text
+----------------------------------------+--------------------------------------------------+
| named contract                         | model / analytic status                          |
+----------------------------------------+--------------------------------------------------+
| #1  C in HS   (Summable ‖C e_i‖^2)     | FALSE on the continuum carrier for a generic     |
|                                         | non-trivial root: C = convolution by a Schwartz |
|                                         | kernel, symbol F h never vanishes => spectrum has|
|                                         | interior => NOT compact => NOT HS. Holds only in |
|                                         | the finite-grid model (finite dim => all HS).    |
+----------------------------------------+--------------------------------------------------+
| #2  C^dagger in HS                     | identical to #1 (adjoint-invariant); same status.|
+----------------------------------------+--------------------------------------------------+
| #3  K_S in HS   (= Tr(K_S^2))          | TRUE per window: PROBE-P2 control row            |
|                                         | 8.35 -> 11.42, finite at every measured window;  |
|                                         | weaker than record 1065's failed Tr(K_S) premise.|
+----------------------------------------+--------------------------------------------------+
| targetProlateCommutatorTermNuclearity  | THE OWED CONTRACT: each term C o K_S and         |
|   (each term IsTraceClassAlong)         | K_S o C has a summable DIAGONAL (= nuclear).     |
|                                         | PROBE-P2: flat O(1), per-term nuclear norm ~4.63, |
|                                         | slope -0.004 (decreasing); the Gaussian symbol   |
|                                         | absorbs the growth that drives control up.       |
+----------------------------------------+--------------------------------------------------+
```

The analytic point that separates this from record 1093's posture: on `L2(R, volume)` an infinite-
measure non-atomic carrier, a convolution root with a non-trivial Schwartz symbol is **not compact**
(bounded below by epsilon on sets of arbitrarily large finite measure for small enough epsilon), hence
not HS. So #1/#2 are *false premises* for the real carrier - they hold in the model only because the
grid is finite-dimensional. A named-false premise is worse than none, so the clean obligation to prove
is **per-term nuclearity** directly: it is a statement about the *products* `C o K_S` / `K_S o C`, which
are HS (from #3 + boundedness, P2/P3) and - per PROBE-P2's flat O(1) measurement - in fact nuclear. It
does **not** require C itself to be HS.

## 3. What is PROVEN here vs OWED

PROVEN in `Dev/C1ProlateRootCommutatorBalancedLegContractReduction.lean` (module builds GREEN, zero
warnings/errors name the file; WSL ext4 replay, `Build completed successfully (3200 jobs)`):

```text
  P1   targetProlateRootFactorAdjointHS_of_HS
         #2 => #1, one line: summable_adjoint_normSq on the same global basis.
  P2   targetProlateRootLeftTermHS_of_RemainderHS
         C o K_S col-summable from #3 + ‖C‖<inf (postcomp HS ideal property).
  P3   targetProlateRemainderRightTermHS_of_RemainderHS
         K_S o C col-summable from #3 + ‖C‖<inf (precomp HS ideal property, via the adjoint).
  def  targetProlateCommutatorTermNuclearity
         NAMED Prop: both terms IsTraceClassAlong along globalBasis. Not yet discharged.
  thm  ..._of_twoContractBalancedPairData
         S2 from #1 + #3 only (#2 derived by P1) - record 1093's three-contract closure with one leg collapsed.
```

OWED to producers (none is a Lean proof yet):

```text
  1. Discharge targetProlateCommutatorTermNuclearity in Lean: formalize PROBE-P2's flat O(1) per-term
     nuclear-norm bound (~4.63, decreasing). This is the analytic core; #3 (K_S in HS) is a supporting
     fact that is also true per window and can be discharged on its own terms.
  2. Add the continuum-correct glue theorem "S2 => per-term nuclearity" via isTraceClassAlong_add on the
     two terms - this route needs NO bare-root contract at all, so it sidesteps the false #1/#2 entirely
     and is the closure to promote once (1) lands.
  3. Owner transfer: Gaussian stand-in root -> actual selected convolution root per-owner (bounded
     bookkeeping; record 1090 Q1 shows any Schwartz h qualifies identically).
```

## 4. Relationship to the sibling bricks (dedup note)

Four owners now exist for the S2 trace product. They are NOT duplicates - each rests on a different
analytic posture and is kept so the strict weakening chain stays auditable:

```text
+----------+----------------------------------------------+------------------------------+---------------+
| record   | module                                        | legs / premise                     | status        |
+----------+----------------------------------------------+------------------------------+---------------+
| 1065     | ...RootCommutatorPairOwner                    | base (F_K,F_K) + boundedSandwich;  | COMMITTED,    |
|          |                                              needs F_K in HS (= Tr(K_S)<inf)   | ref, FAILS      |
|          |                                              measured ~xi^0.4 for {2,3,5}         | for {2,3,5}     |
+----------+----------------------------------------------+------------------------------+---------------+
| 1092     | ...PerTermPairOwner                          | legs {F_K . C^dagger,F_K}/{F_K,..};| LOCAL,        |
|          |                                              still needs F_K in HS                 | superseded      |
+----------+----------------------------------------------+------------------------------+---------------+
| 1093     | ...BalancedLegOwner                          | legs {C^dagger,K_S}/{K_S,C};       | LOCAL (green),|
|          |                                              three named contracts #1/#2/#3           | canonical target|
+----------+----------------------------------------------+------------------------------+---------------+
| 1094     | ...BalancedLegContractReduction (THIS)      | REDUCES 1093: drops #2, names the  | LOCAL (green),|
|          |                                              per-term nuclearity that is truly owed    | this record     |
+----------+----------------------------------------------+------------------------------+---------------+
```

All four close S2 through the SAME generic leaf `_of_pairData`; only the leg construction and the named
contracts differ. 1094 adds no new shared-layer primitive (it reuses `summable_adjoint_normSq` and the two
HS-ideal lemmas, all already committed), so there is nothing to dedup against the seven
`DividedDifferenceKernel.lean` importers this turn.

## 5. Honesty ledger

- Adds ONE Lean module; no change to the leaf S2 statement, the two-contract F1' corollary, or GATE 1 mainline.
- RH unclaimed. Non-mainline / gated (local build green + warning-clean for this file; not committed).
- P1/P2/P3 are proven from committed machinery only. The per-term nuclearity contract is NAMED but not yet
  PROVEN in Lean - it is the producer's target, and section 2 records that #1/#2 (which record 1093 threads
  through) are false for generic continuum roots, so this named contract is the correct thing to discharge.

## 6. Next steps

1. [DONE this record] Land `Dev/C1ProlateRootCommutatorBalancedLegContractReduction.lean` green + warning-clean:
   drop #2 (adjoint-invariance), prove each term HS from #3 alone at the col-sum level, name per-term nuclearity,
   and close S2 from two named contracts (#1+#3).
2. OWED - discharge `targetProlateCommutatorTermNuclearity` in Lean (formalize PROBE-P2's flat O(1) ~4.63), then add
   the glue theorem "S2 => per-term nuclearity" via `isTraceClassAlong_add`; that route needs no bare-root contract and
   is the closure to promote as canonical for the continuum carrier.
3. OWED - commit 1092 + 1093 + 1094 together (staged-file hygiene check first): promote the reduced two-contract owner
   as canonical; keep 1065 as committed reference, retire/annotate 1092's absorbed-leg brick as superseded.
