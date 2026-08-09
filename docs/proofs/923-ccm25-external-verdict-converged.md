# Door L657 (CCM25 finite-prime arithmetic) — converged external-consult verdict + exact repair

Status: external-consult resolution, repo-premises verified by me. NO code change in this
round; this is the decision record. RH NOT claimed. Zero sorry. Do not instantiate the
current axiom.

## 1. The wall (unchanged)

`Dev/UnconditionalSkeleton.lean:657`:

```lean
axiom normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot :
  Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
    normalizedCoreSourceAnalyticCoreFromTheorems.toWeilFormSymbols
```

`CommonFinitePrimeArithmeticSourceData W` has a `scopedArchimedeanContributionBalance` field
that quantifies:

```lean
∀ λ : ℝ, ∀ globalData, ∀ restrictedData,
  SourceScopedArchimedeanContributionBalance W common λ globalData restrictedData
```

On the concrete `{2}` carrier this is **an empty (uninhabited) type** for a structural
(draining-window) reason, not a missing lemma.

## 2. The algebra that makes it empty (all premises now verified in-repo)

Let `A := archimedeanTerm(f⋆f)` and `P := poleFunctional(f⋆f)`.

- Restricted: `R(λ) = A + P − Σ_r(λ)`
- Global:     `G = P − A − Σ_g`
- `polePairing(g)` reduces to `poleFunctional(g⋆g)` (rfl-level), so the pole term is the same object on both sides. (`AnalyticCoreBase`)
- Concrete carrier: `archimedeanTerm := fun _ => 0` (`Dev/ConcreteP1SupportProbe.lean:169`), so `A = 0` definitionally.
- `R(λ)=G ⇔ Σ_r(λ)=Σ_g`.

| regime | Σ_r(λ) | balance |
|---|---|---|
| window-hit (`λ² ≥ 4`, contains 2) | = Σ_g | holds |
| draining (`λ² < 4`, set empty) | = 0 | fails because Σ_g ≠ 0 |

Verified premises that make draining fail irrecoverably:
- `restrictedIndexSet λ = if 2 ≤ λ^2 then {2} else ∅` (`ConcreteP1SupportProbe.lean:130-131`).
- draining `restrictedData` is **inhabited**: it is `onIndexSet ∅` = empty dependent product.
- `SourceGlobalFinitePrimeArithmeticData = onIndexSet globalIndexSet`, `globalIndexSet = {2}` (`:129`), and the on-index construction is available at `n=2` via `PrimePowerArithmeticBridge.lean:24` (needs `IsPrimePow 2`, visible via `term_two_pos`, and two rfl read-offs), so `globalData` is inhabited.
- `term_two_pos : 0 < sourceFinitePrimeTerm 2 commonBump` (`ConcreteP1SupportProbe.lean:59`) → `Σ_g ≠ 0`.

Therefore `Common concreteW` is empty; the `axiom` asserts an uninhabited type.

## 3. External-consult verdict (converged)

- **(a)** The `∀ λ` scoped balance is a type-scope fault, not a missing analytic lemma.
- **(b)** Option A — re-scope the balance to the covering / sum-equality regime — is **sufficient** on the concrete `{2}` carrier (because `A=0`). **No sign flip.**
- **(c)** The `∀ n` atom field is a second, separate index-scoping fault (uninhabited at composites/1).
- **(d)** The deeper carrier wall — concrete `convolutionStar = pointwise +`, not Mellin — is unaffected by this repair and remains open (the L657 fix is a finite/truncated consistency object, not a proof on a Mellin carrier).

## 3b. Exact structural repair (recommended, minimal)

Change the balance field to be conditional on the sum equality (more robust than an index-containment hypothesis, because it states exactly the algebra that is required):

```lean
scopedArchimedeanContributionBalance :
  ∀ λ : ℝ,
    (hsum : restrictedFinitePrimeSumAtλ λ = Σ_g) →
    ∀ globalData restrictedData,
      SourceScopedArchimedeanContributionBalance ... 
```

with `hsum` bought from the concrete `CoversGlobal` relation when desired:

```lean
def CoversGlobal (λ : ℝ) : Prop :=
  ∀ n ∈ globalPrimeIndexSet, n ∈ restrictedPrimeIndexSet λ   -- on {2}: (2 : ℝ) ≤ λ^2
```

Under the repaired field, the `{2}` certificate goes through by `simp [archimedeanTerm=0, pole_rfl, hsum]`, and the draining case is no longer an obligation.

Alternative that keeps the field formally `∀ λ` but removes draining (non-cover) data from the type: put `coversGlobal` as a field of `SourceRestrictedArithmeticData`, so a draining (non-cover) restrictedData does not exist at the type level.

## 4. Ordered next steps (formal)

1. Prove the diagnostic contradiction:
   `theorem concrete_common_empty : Common concreteWeil → False` using a draining λ (e.g. `λ=0`), `restricted_sum_empty`, `globalData` inhabit, and `globalSum≠0`. Do **not** instantiate the axiom afterwards.
2. Re-scope the balance field to the sum-equality conditional (or cover).
3. Rebuild the `{2}` Common term under the new type.
4. Keep the Mellin-carrier carrier wall separate (`docs/proofs/918`, `920`, `921`, `922`).

RH not claimed; no sorry/axiom introduced; the current `axiom` is a known-unsound placeholder to be removed in the next editing round.



