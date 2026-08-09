# External Consultation Prompt — Request for Independent Expert Input

You are being consulted as an external research mathematician / proof-engineering expert.
I am working on a formal proof project in Lean 4 / mathlib [search: this is a Connes–Weil
route toward the Riemann Hypotheses; nothing is yet claimed proved unconditionally].
I will give you, in self-contained form, the **single most current open bottom** in the
repository (the one that currently stands on an `axiom`), an exact transcript of the type it
requires, the concrete carrier facts I already proved, and my working hypothesis for a fix.
I want your independent first-principles judgment on whether my hypothesis is right and, if so,
a concrete plan.

Please be direct and critique the plan as hard as it needs. No flattery.

---

## 1. Context in one paragraph

The repo defines an analytic "Carrier" / "WeilFormSymbols" (archimedean test space, a
finite-prime arithmetic layer, and a Hilbert-operator carrier) and a chain of bridge
theorems that would, if all sound, eventually assemble to `_root_.RiemannHypothesis`.
Some obligations still sit on "bottom axioms". I have design‑time docs (`docs/proofs/9xx`)
that store judgments, rejected routes, and probe results. This prompt is about the single
most current open obstacle, which I index as **L657**.

---

## 2. The wall: `normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot`

In `Dev/UnconditionalSkeleton.lean:657` there is, verbatim:

```lean
axiom normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot :
  Source.CCM25Concrete.FinitePrimeSourceData.CommonFinitePrimeArithmeticSourceData
    normalizedCoreSourceAnalyticCoreFromTheorems.toWeilFormSymbols
```

I want to replace this axiom by a real axiom-free construction (a `def`/`theorem` depending
only on mathlib's `[Classical.choice, propext, Quot.sound]`). I have traced the type it
requires all the way down. The obstacle is, I believe, a **type scope‑‑fault** (wrong
quantifier width / wrong index key), not a missing analytic lemma. Below I lay out the
type, the concrete-carrier facts, and the two structural faults.

---

## 3. The type I must inhabit

```lean
structure Common (W : WeilFormSymbols) where
  commonTestFunction : TestFunction
  finitePrimeData :
    FinitePrimeArithmeticData W (commonTestOfCommon W common)
  scopedArchimedeanContributionBalance :
    ∀ λ : ℝ,
      ∀ globalData :    SourceGlobalArithmeticData    W common common,
      ∀ restrictedData : SourceRestrictedArithmeticData W common common λ,
        SourceScopedArchimedeanContributionBalance W common λ globalData restrictedData
```

where the "scoped balance" is a scalar equality of two real formulae, for the common
test `g`:

```text
R(λ) = A + P − Σ_r(λ)        restricted formula evaluated at λ
G    = P − A − Σ_g            global formula (λ‑independent)
require : ∀ λ, R(λ) = G
```

Concretely, I define (this is exact in source, `FinitePrimeSourceData.lean:25-60`):

- `A := W.archimedeanTerm (W.convolutionStar f f)` — one real, independent of λ,
- `P := W.polePairing (W.convolutionStar f f)` — one real, independent of λ,
- `Σ_r(λ) :=` restricted finite‑prime sum over `restrictedPrimeIndexSet λ` (a shrinking window,
  `n : ℝ ≤ λ²`),
- `Σ_g :=` global finite‑prime sum over `globalPrimeIndexSet`.

---

## 4. Facts I have already established (with evidence)

**(4a) The concrete carrier can be `{2}`-only.**
`ConcreteP1SupportProbe` constructs a `concreteTestAlgebra` with a compact‑support test
(`Icc 3/2 5/2`, value `1` at `t=2`), proof that the prime‑`2` term `> 0`, exact index set
`{2}`, and a real `SourceWeilFormData concreteTestAlgebra`. It is axiom‑free (given
`[Classical.choice, propext, Quot.sound]`).

**(4b) The `∀λ` scoped balance is structurally unsatisfiable on `{2}`.**

Write `λ` such that the window either contains `2` or not:

- If `λ² ≥ 4` (window contains the measurable prime `2`): `Σ_r(λ) = Σ_g ≠ 0`, so the equality
  forces `A = 0`.
- If `λ² < 4` (window drains): `Σ_r(λ) = 0` while `Σ_g ≠ 0`, so the equality forces `A = −Σ_g/2`.

A single λ‑independent real `A` cannot hold both. So `scopedArchimedeanContributionBalance`
as currently typed is **not provable** on a concrete carrier whose window actually drains.
Fix I contemplate: re‑scope to "truncated" meaning (require the equality only on the set of λ
where the restricted window covers the global index set; when the window drains and the family
is probe‑zero, the requirement is vacuously true). See docs `920`.

**(4c) The `∀n` "atoms" demand is a type‑scope‑fault.**

The certificate carries `atoms : ∀ n : ℕ, DataForSourceTest`, and `Data`
requires `IsPrimePow n`. This is **false at every composite** and at `n=1`, and `Data`
is a structure that needs `sourcePrimePowerIndex : IsPrimePow n`. So An object inhabiting the field type `atoms` (= `∀ n : ℕ, DataForSourceTest`) is **not just impossible to construct — it is _uninhabited_ for any
`W` whose arithmetic is honest. Fix candidate: use the already‑existing
`SourceFinitePrimeArithmeticDataOnIndexSet` / `SourceVisibleFinitePrimeArithmeticData`
keyed on the *global index set* `{2}`, which is feature‑complete at `n=2` on the concrete
carrier. Docs `docs/proofs/921`, `docs/proofs/922` (the on‑index primitive already exists
and is axiom‑clean, and the read‑offs are all `rfl`).

**(4d) The deepest wall — the concrete convolution is pointwise addition (non‑Mellin).**

- `SourceWeilFormData concreteTestAlgebra` has `convolutionStar f g := f + g` (pointwise `ℝ`),
  and there is an in‑repo theorem `not_normalizedCC20MellinConvolutionLaw`
  (`CC20YoshidaConstruction:2727`) proving the Mellin‑convolution law **fails** on that model
  (it doubles `M(f⋆g) = 2·Mf` instead of the true `Mf · Mg`, i.e. `M(f⋆g)= …`). So a sound
  *all‑pair* finite‑prime family cannot be built on that concrete carrier as‑is.
- The *genuine* Mellin carrier (`MellinConvolutionIdentity.mellin_log_convolution_product`,
  on `MellinProductCarrier.Test = ℝ → ℂ`, log‑coordinate) has the correct law and is
  axiom‑clean, but `WeilFormSymbols` pins every arithmetic field to `TestFunction`,
  i.e. to Schwartz. There is no total `decode : logCarrier → TestFunction`. Hence a
  *carrier‑retype* is needed to reuse the Mellin law.

**In short**: the `Common` record is typed against a `WeilFormSymbols` whose archimedean
test is Schwartz with a *non‑Mellin* convolution; both fields of the record are
uninhabitable "by construction", one for a `∀n` width, the other for a `∀λ` width over a
λ‑independent archimedean term.

---

## 5. The questions on which I want your independent judgment

1. **Is the `∀λ` balance really unprovable as stated on `{2}`, or is there a mathematical
   (non‑typing) way to make a λ‑independent `A` satisfy a `∀λ` equality while the sums
   dip in and out?** Should I fight the quantifier with a sharper lemma, or is the honest
   conclusion that the "scoped" definition itself is mis‑scoped and needs replacement with a
   truncated/conditional semantics?

2. **Is replacing `∀n`‑normalization by an on‑index `{2}`‑set normalization sound for what
   the route actually consumes?** The route consumers only view `globalPrimeIndexSet` (a
   `Finset`). But I must preserve the *content* of `DirectAtomVisibleReadOff` / the
   function‑read‑off (the visible slice of the atom normalization equals the visible
   arithmetic function) after re‑typing. Any Lean/mathlib pitfalls with a
   dependent‑index`∀ n ∈ globalSet → P n` structure (e.g. `Finset.filter IsPrimePow`,
   universe issues, `rfl` vs `simp` friction), and which key is more robust:
   ` ∈ largerGlobalSet` or the existing `sourceAtomVisible`‑keyed form?

3. **The deeper carrier wall.** If concrete has `f+g` non‑Mellin convolution, is the right
   end‑game
   (a) re‑type `WeilFormSymbols.Test` to the Mellin/log carrier and rebuild the arithmetic
   layer there (the "archimedean‑biased" big change), or
   (b) define the finite‑prime layer as a *parallel free‑standing certificate lattice* on a
   Mellin carrier that does **not** claim the skeleton's `atoms` slot, leaving that slot an
   open axiom while demonstrating the parallel lattice sound?
   Which is more advisable for a route that is an explicit formal experiment (consistency
   check) rather than a full closed proof?

4. **Is "one object keyed by the finite global index set, archimedean equality only when
   the window ≥ global" provably provable (not invented worse bounds), or is the scoped
   balance a genuine `archimedean‑bridge` analytic identity needing a real asymptotic
   lemma?**

5. Any suggestion to **shorten the route**, e.g. choosing the window = global by
   construction, or moving the equality to a pre‑λ‑stripped form.

---

## 6. Answer ground rules

- Direct critique welcome: if the hypothesis is wrong (fix is not a re‑type but a missing
  lemma, or the whole lane is dead), say so and why.
- First‑principles, not a re‑derivation of the whole field; question the ruling step.
- If the re‑type is right, give a concrete ordered plan (which structs/fields to re‑key,
  which bridges to add, in what order), even if it is a large mechanical job.
- Keep it scannable: short sections, tables for comparisons, a final line "recommended next
  action".

---

Thank you. For any referenced definition, the source is in the Windows repo:
`Source/CCM25Concrete/FinitePrimeSourceData.lean`, `Source/CCM25Concrete/PrimePowerArithmetic.lean`,
`Dev/UnconditionalSkeleton.lean`, `Dev/ConcreteP1SupportProbe.lean`. I can paste any full
definition on request.





