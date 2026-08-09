# Round 2 — My concrete-carrier facts change three of your conclusions. Please re-verify.

Thank you for the sharp verdict — your central conclusion (the scoped balance as typed is
a scoping fault, not a missing lemma) is confirmed. But THREE of your sub-conclusions need
re-verification because I initially withheld two facts I have now pulled from the Lean
source. They matter. Please rework the three parts against the exact formulas below.

I am NOT asking you to soften your verdict; if these three points collapse under
examination I will re-adopt your original. Number the parts in your reply.

---

## Fact A (new) — the pole terms cancel by definition, and the archimedean term on my
concrete carrier is *identically zero*.

In the Lean source (`SourceWeilFormData`) the two formulas, written for a common test `f`,
reduce to:

- restricted:   `R(λ) = archimedeanTerm(f⋆f) + poleFunctional(f⋆f) − Σ_r(λ)`
- global:       `G    = poleFunctional(f⋆f) − archimedeanTerm(f⋆f) − Σ_g`

`polePairing(g)` is *defined* to reduce to `poleFunctional(convolutionStar g g)` (there is a
round-trip, `rfl`-level lemma). So on both sides the pole term collapses to the same object
`poleFunctional(f⋆f)`. You called that pole `P` the same on both sides — correct.

But the NEW fact is: **on the concrete `{2}` carrier I use, `archimedeanTerm` is defined to be
`fun _ => 0`.** It is not an assayed nonzero value; it is definitionally zero by construction.

## Consequence — your "covering forces A=0, so cover-only is false" must be revisited.

Your §4 claims cover-only is provable only if `archimedeanTerm = 0`. Granted that on my
carrier `archimedeanTerm(f⋆f) = 0`:

- covering (`Σ_r(λ) = Σ_g`): `R = 0 + P − Σ_g`, `G = P − 0 − Σ_g`, so `R = G` trivially.
- draining (`Σ_r(λ) = 0`, `Σ_g ≠ 0`): `R = P`, `G = P − Σ_g`, so `R ≠ G` unless `Σ_g = 0`.

So **covering is NOT the fault on this carrier.** The only regime that still breaks the
identity is the draining window. Please confirm or refute: **Option A (cover-only) is
SUFFICIENT on `{2}`** — no sign flip needed, no `A=0` worry, because `A=0` already holds.
The sign flip you suggested (global uses `+A`) would break the intended `+−` sign structure
of the Weil explicit formulas, so I want to be sure before acting.

---

## Fact B (new) — the axiom's target is *definitionally* the concrete `{2}` carrier.

Your fault #4 states: "the axiom targets `normalized … toWeilFormSymbols` while your
concrete evidence lives on a concrete `{2}` carrier — unless they are definitionally or
provably the same carrier, the construction does not inhabit the axiom's type."

I checked. In Lean:

- `normalizedCoreSourceTestAlgebraFromTheorems = concreteTestAlgebra` (one line, by `rfl`);
- `normalizedCoreSourceAnalyticCoreFromTheorems.testAlgebra = concreteTestAlgebra` (by `rfl`);
- so `normalizedCoreSourceAnalyticCoreFromTheorems.toWeilFormSymbols` lives on
  `concreteTestAlgebra`.

The concrete `{2}` carrier IS the axiom's carrier. The probe reaches the axiom directly.
Please re-derive from first principles: if the axiom asserts `Common W` for this concrete
`W`, and I can prove that no `Common` exists on the concrete carrier, then the axiom is not
merely "unprovable"; it makes the skeleton **inconsistent** (it asserts a `false` / empty
type). Do you agree this strengthens the verdict from "possibly uninhabited" to "provably
inconsistent under the source's own definitions, so the axiom cannot be closed by any
construction — only by redefining the type"?

---

## Fact C (recheck) — the draining-regime restricted `λ` is INHABITED, not "may not exist".

You gave an escape: "if `SourceRestrictedArithmeticData W common common (small λ)` is an
empty type, the balance is vacuously true." In my code that type is an `abbrev` to
`FinitePrimeArithmeticDataOnIndexSet W (restrictedPrimeIndexSet λ)`, whose data field lives over
`∀ n, n ∈ indexSet → …`. For a draining λ where `restrictedPrimeIndexSet λ = ∅` (the empty
`Finset`), that type is trivially inhabited (an empty product), and the restricted sum is `0`
by the empty-sum convention. So there IS a concrete `restrictedData` witness at a draining λ,
and the `∀ λ, ∀ restrictedData, …` is *not* vacuously true there. Confirm or refute.

---

## The consolidated question

Assume Fact A + B + C. My claim is:

> The axiom on the concrete `{2}` carrier is a *provably false / empty* type :
> `archimedeanTerm = 0` kills any `A`-dependence, the pole terms cancel by `rfl`,
> `Σ_g ≠ 0` by a proven positivity fact, and the draining window is inhabited.
> Hence `Common W` is empty; the axiom asserts an empty type and would make the skeleton
> inconsistent if it were a `def`-level theorem. The unique sound repair is to re-scope the
> balance to a covering condition — not a sign flip, not "the carrier is a different `W`".

Is that consistent with the math? And is **cover-only** (my Option A) *necessary and
sufficient* as the minimal repair, or do you still hold it forces `A=0` (which is satisfied
here) and thus costs nothing extra?

If you *still* believe a sign flip is needed, answer these from first principles, not from my
code:

1. In the intended Weil explicit formula, do the "truncated" and "global" forms of the
   archimedean contribution carry the *same* sign, or is the `+/−` asymmetry (one side `+A`, the other `−A`) a genuine
   feature (archimedean-vs-truncation) rather than a bug?
2. With `archimedeanTerm = 0`, global `G = P − Σ_g` and restricted `R = P − Σ_r(λ)`; which
   `λ`-regime(s) does `R = G` force, and why does re-scoping to cover-only resolve every
   failing `λ`?
3. If you were running the formal proof, would you (i) change the global sign to `+A` and
   keep `∀ λ`, or (ii) keep the current `+−` structure and scope to the covering λ-set?

Rule book: structured answers, direct, no flattery. When you correct my request or your own
earlier claim, mark `%MISTAKE%` so I can track the revision.

