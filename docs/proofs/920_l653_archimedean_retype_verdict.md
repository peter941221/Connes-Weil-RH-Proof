# L653 closing verdict — archimedean λ-independence makes the scoped balance unsatisfiable on the concrete `{2}` model

Date: 2026-08-09. Type: root-cause verdict (source-verified, no code change).

## Bottom line

`CommonFinitePrimeArithmeticSourceData.scopedArchimedeanContributionBalance` is
**not merely unproved — it is structurally UNSATISFIABLE** on the concrete
`{2}` carrier, for a reason that has nothing to do with choosing the value of
`archimedeanTerm`:

> the field is quantified `∀ λ`, but `archimedeanTerm : Test → ℝ` takes no `λ`.
> The balance equation forces `A := archimedean(f⋆f)` to adopt a DIFFERENT
> value at each λ, impossible for a single λ-independent scalar when the probe
> window changes.

## The reduction (exact, `rfl`-level)

Let `R` be the "scoped restricted archimedean formula" and `G` the "scoped
global archimedean formula" (FinitePrimeSourceData.lean:25-43). Set `A :=
W.archimedeanTerm (convolutionStar f f)`, `P := W.evaluation.poleFunctional
(convolutionStar f f)`. On any `W` where `polePairing = poleFunctional∘(⋆)`
(refl, `polePairing_eq_poleFunctional_convolutionSquare`):

```
R(λ) = A + P − Σᵣ(λ)        Σᵣ(λ) := restricted finite-prime eval sum at λ
G    = P − A − Σ_g            Σ_g   := global finite-prime eval sum

scoped balance:  ∀ λ, R(λ) = G(λ)
instantaneous:   A = (Σᵣ(λ) − Σ_g)/2      (for EVERY λ)
```

On the concrete `{2}` model (`ConcreteP1SupportProbe`): `globalIndexSet = {2}`,
`restrictedIndexSet = if 2 ≤ λ² then {2} else ∅`, `Σ_g = Σ₂ ≠ 0`:

```
λ with 2 ≤ λ²  (window contains 2):   Σᵣ = Σ_g          ⇒ require A = 0
λ with 2 > λ²  (draining window):     Σᵣ = 0  ≠ Σ_g     ⇒ require A = −Σ₂/2
```

One λ-independent real `A` cannot satisfy both. Hence `scopedArchimedean…`
(unified `∀ λ`,map), the second leaf of L653, is **not provable** while
`archimedeanTerm` is `fun _ => 0` (or, in fact, any single λ-independent
value).

## Load-bearing consequence

`UnconditionalSkeleton.lean:653` `normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot`
reduces on two INDEPENDENT definitional seams:

- **A-lift `atoms`**: normalization `atIndex : ℕ → …` demands `IsPrimePow n`
  at every `n` (false at composites/1). Fix: re-scope normalization to
  `n ∈ globalPrimeIndexSet` (finite `{2}`).
- **B-lift `scoped balance`**: the `∀ λ` quantifier over a `λ`-independent
  `archimedeanTerm`. Fix: re-type to truncated semantics (require equality only
  when `restrictedPrimeIndexSet λ` covers `globalPrimeIndexSet`; vacuous when the
  window drains on a probe-zero family).

Neither is fixable by *supplying a value*; both are *structural (type-scope)*
faults. Both A and B are the same L653 wall (see route-state 916c).

## What did NOT change

- `positiveTraceNonnegative` is axiom-clean on concrete `g` (L5544).
- `ConcreteP1SupportProbe` carrier/dev works. RH NOT claimed. No new axiom, no
  sorry. Zero code changes; this is the ledger entry CW-Gate-any λ.