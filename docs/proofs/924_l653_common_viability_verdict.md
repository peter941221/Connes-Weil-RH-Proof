# 924 — L653/L657 decisive reconciliation: the `Common Wconcrete` axiom

Date: 2026-08-09. Type: authoritative verdict, repo-verified. No new axiom or sorry.
Resolves the contradiction between 923 (claims empty) and this-session's MEMORY correction
(probe-failure). RH NOT claimed.

## 0. Bottom line

- `Common Wconcrete -> False` (923) is NOT provable: the `commonTestFunction` field is a
  free existential, and a degenerate common test (whose squared convolution vanishes at
  `t = 2`) escapes the draining-lambda contradiction.
- The amended statement IS provable, axiom-clean: `probe_balance_false` for the fixed
  `f0 = commonBump` (already built, `Dev/L657DiagProbe.lean`).
- The `UnconditionalSkeleton.lean:653` axiom therefore cannot be removed by a constructive
  leaf on the current additive carrier. It is a structural placeholder whose removal needs
  the documented source-convolution-carrier redefinition, not a leaf lemma.

## 1. What the probe proves (already axiom-clean)

`Dev/L657DiagnosticProbe.lean` / `L657DiagProbe.lean`, WSL green on the isolated
`cwr-l657-iso` mirror, `.olean` present. Axiom set `[propext, Classical.choice, Quot.sound]`,
zero sorry:

```lean
theorem probe_balance_false :
    SourceScopedArchimedeanContributionBalance W0 f0 0 gd rd -> False
```

`W0 = concreteWeilForm.toWeilFormSymbols`, `f0 = commonBump` (the fixed common test),
`gd` the global-`{2}` data (inhabited, `globalSum_positive`), `rd` the draining-window
empty restricted data (inhabited, `restrictedSumZero`). `nlinarith` closes.

This is a failure **of the concrete fixed test `f0`**. It does not show `Common` is empty.

## 2. Why "`Common concreteW -> False`" is an over-claim (the existential escape)

From `FinitePrimeSourceData.lean:626-641` the common test field is existential:

```lean
structure CommonFinitePrimeArithmeticSourceData (W: WeilFormSymbols) where
  commonTestFunction : TestFunction
  finitePrimeData :
    FinitePrimeArithmeticSourceData W (concreteCommonSourceTest W commonTest)
  scopedArchimedeanContributionBalance :
    ∀ λ : ℝ, ∀ globalData, ∀ restrictedData, SourceScopedArchimedeanContributionBalance ...
```

The draining contradiction holds only for `f0 = commonBump`, whose squared convolution
evaluates `2` at the prime `2`, giving `Σ₂ ≠ 0` and hence `R(0) = P ≠ P − Σ₂ = G`.

But `commonTestFunction` can be chosen with its squared convolution vanishing at `t = 2`
(finite prime term zero), which makes both `Σ_r` and `Σ_g` zero on `{2}`, so the balance
holds trivially. The existential escapes the contradiction.

=> `Common Wconcrete` is NOT structurally empty. 923's "empty" is overturned.
The correct provable statement is the probe (`probe_balance_false`), which the
dated proof records preserve.

## 3. Why the `:653` axiom is still an honesty barrier (cannot be removed by a leaf)

`Common Wconcrete` is not provably empty, but it is **also not axiom-free constructible**
on the current additive carrier. The bottom is the certificate PAIR family:

    finitePrimeData : FinitePrimeArithmeticSourceData W (concreteCommonSourceTest W common)

Building it requires the Mellin convolution law for the square, which the concrete carrier
(`convolutionStar := fun f g => f + g`) breaks: `CC20YoshidaConstruction:2727` derives `2 = 1`.
So no honest `def : Common` exists on the additive carrier. The `:653` axiom is a placeholder
for a type that is (i) unsatisfiable for the standard test but (ii) not refuted across all
existential choices — the two structural seams every L653 verdict (920/921/923) names:
- the `∀ n` index fault (normalization requires `IsPrimePow n` at composites),
- the `∀ λ` balance fault (draining lambda obligation).

## 4. How to actually remove the `:653` axiom (ordered)

1. **Re-scope the balance** to a cover / `hsum`-conditional (923 §3b):
   `scopedArchimedeanContributionBalance : ∀ λ, (restrictedSumAtλ = Σ_g) -> …`, so the
   draining-λ case is no longer an obligation. This alone lets a `Common` for the STANDARD
   `f0` be built — as long as the finite-family is constructible.
2. **Re-type / rebuild the certificate family on the Mellin-correct carrier**
   (CompactLog / `cc20GlobalLogCrossingL2`). This is the ~31-file shared-type source-model
   refactor (915 §9; `docs/proofs/831/833/834`). Until this, `F`-653 cannot be honestly
   closed — `:653` removal is a route-milestone, not a per-helper leaf.
3. After (1)+(2), replace `UnconditionalSkeleton.lean:653` with a `def`/theorem and audit
   `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

## 5. Route-judgment impact

- `L657` (probe failure for `f0`) = **CLOSED**, axiom-clean. Do not re-open.
- `L653` / `Common Wconcrete` (route `ModelConstructorCore`) = **NOT closable on the additive
  carrier**; it funnels into the source-model redefinition. Honesty-blocker, not a leaf.
- L653 should not be force-removed by a leaf; that would require a cold route rebuild with
  the architected carrier seam.

RH not claimed. No new axiom, no sorry. The `:653` axiom stays flagged until the re-scope +
Mellin carrier work lands.

## 6. Next steps

1. Implement step-1 re-scope (cover/hsum balance) in a `Dev` probe; prove a `[global=cover]`
   `Common`-term-bearing `f0`.
2. Open the CompactLog carrier redefinition (the ~31-file shared-type refactor).
3. Axiom-audit `UnconditionalSkeleton` at the new seam; prune the trailing `:653` axiom.
4. (Deferred) A-lane generic-λ prolate hfactor — still open (611/911).
