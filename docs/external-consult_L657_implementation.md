# External Consult — L657 implementation: prove `Common Wconcrete` is empty
# Lean 4 / mathlib v4.30.0

Self-contained request. You do NOT need my repository — every type, signature,
and fact you need is quoted inline below.

Deliverable: a new Lean leaf module (mathlib `v4.30.0`) that builds with axioms
only `[Classical.choice, propext, Quot.sound]` (zero `sorry`, zero new `axiom`).
**RH is not claimed.**

Your three jobs, in order:

1. Build the on-{2} finite-prime atom `atom2`.
2. Build the draining-window contradiction
   `concrete_common_empty : CommonFinitePrimeArithmeticSourceData Wconcrete -> False`
   (equivalently close the on-index statement).
3. (Second part, lower priority) State the re-scoped balance-field conjunction
   that turns the current impossible `forall lambda` statement into a
   cover-conditional one, without touching the (>= 25) consumer call-sites.

Read sections 0-4 first; they contain everything. If any step is genuinely
impossible, say which and why. Never fake a `rfl` or a `sorry`.

---

## 0. Goal

Show that the concrete W-symbol type is provably empty:

    theorem concrete_common_empty :
        CommonFinitePrimeArithmeticSourceData Wconcrete -> False

`Wconcrete` is the concrete `{2}` Weil-form symbol (a concrete carrier, not an
abstraction). This proves the current axiom is inconsistent with the repo's own
definitions, not merely unproved.

---

## 1. Verified facts (reuse; these already compile with library-trio only)

Leaf module `ConnesWeilRH/Dev/L657DiagnosticProbe.lean`, namespaces
`namespace ConnesWeilRH / namespace Source / namespace Dev / namespace L657DiagnosticProbe`.

    noncomputable def Wconcrete : WeilFormSymbols :=
      ConcreteP1SupportProbe.concreteWeilForm.toWeilFormSymbols

    lemma archimedeanTerm_zero (F : TestFunction) :
        Wconcrete.archimedeanTerm F = 0 := by rfl

    lemma global_index_set :
        Wconcrete.globalPrimeIndexSet = ({2} : Finset Nat) := by rfl

    lemma restricted_index_set_zero :
        Wconcrete.restrictedPrimeIndexSet 0 = (empty : Finset Nat) := by
      unfold Wconcrete; simp [concreteWeilForm, perCommonSupport]

    lemma two_is_prime_pow : IsPrimePow 2 := Nat.prime_two.isPrimePow

Context:

- `Wconcrete` is `concreteTestAlgebra.toWeilFormSymbols`. The algebra carries
  `convolutionStar f g = f + g` (pointwise), `archimedeanTerm := fun _ => 0`,
  `poleFunctional` agreeing with `polePairing`, and finite-prime support
  `perCommonSupport`.
- `perCommonSupport.globalIndexSet = {2}`; `restrictedIndexSet lambda =
  if 2 <= lambda^2 then {2} else empty`, so it is empty at `lambda = 0`.
- The common test is a bump nonzero at `t = 2` (`valueAt 2 = 1`), inside
  `Icc (3/2) (5/2)`; at `1/2` its value is `0`.

**The five facts (1)-(5) are all I assume. Everything else is proven in the leaf.**

---

## 2. The field that kills it

From `ConnesWeilRH/Source/CCM25Concrete/FinitePrimeSourceData.lean:626`:

    structure CommonFinitePrimeArithmeticSourceData (W : WeilFormSymbols) where
      commonTestFunction : TestFunction
      finitePrimeData :
        FinitePrimeArithmeticSourceData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
      scopedArchimedeanContributionBalance :
        forall lambda : Real,
          forall globalData :
            SourceGlobalFinitePrimeArithmeticData W commonTestFunction commonTestFunction,
          forall restrictedData :
            SourceRestrictedFinitePrimeArithmeticData
              W commonTestFunction commonTestFunction lambda,
            SourceScopedArchimedeanContributionBalance
              W commonTestFunction lambda globalData restrictedData

The balance definitions (lines 45-66):

    SourceScopedRestrictedArchimedeanFormula W f lambda restrictedData :=
        W.archimedeanTerm (W.convolutionStar f f) + W.polePairing f
          - MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet W f f lambda restrictedData

    SourceScopedGlobalArchimedeanFormula W f globalData :=
        W.poleFunctional (W.convolutionStar f f)
          - W.archimedeanTerm (W.convolutionStar f f)
          - MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f f globalData

    SourceScopedArchimedeanContributionBalance W f lambda globalData restrictedData :=
      SourceScopedRestrictedArchimedeanFormula W f lambda restrictedData =
        SourceScopedGlobalArchimedeanFormula W f globalData

On the concrete carrier `archimedeanTerm = 0` (fact (2)); the restricted formula uses
`W.polePairing f` while the global formula uses `W.poleFunctional (W.convolutionStar f f)`,
which agree on the concrete carrier (a definitional round-trip), so the pole terms cancel and
so the equality is exactly: `Sigma_restricted(lambda) = Sigma_global`.

At `lambda = 0`: `restrictedPrimeIndexSet 0 = empty` => `Sigma_restricted(0) = 0`.
`Sigma_global` over `{2}` is strictly positive (`term_2_positive`) => `!= 0`.

---

## 2b. The on-{2} atom (hard piece)

`SourceGlobalFinitePrimeArithmeticData Wconcrete f f` abbreviates
`SourceFinitePrimeArithmeticDataOnIndexSet Wconcrete f f Wconcrete.globalPrimeIndexSet`
with field

    atIndex : forall n, n in globalPrimeIndexSet -> SourceFinitePrimeArithmeticData ... n

Reduce to `SourceFinitePrimeArithmeticData Wconcrete f f 2`.

Standard bridge (`PrimePowerArithmeticBridge.lean:24-62`):

    noncomputable def SourceFinitePrimeArithmeticData.ofSourceEvaluationData
        {A : SourceTestAlgebra}
        (E : SourceEvaluationData A)
        {W : WeilFormSymbols}
        (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : Nat)
        (sourcePrimePowerIndex : IsPrimePow n)
        (visible : W.finitePrimeAtomVisible n
            (W.convolutionStar common.sourceTest common.sourceTest))
        (pairingReadOff : W.primePowerPairing n common.sourceTest common.sourceTest =
            (1 / Real.sqrt (n : Real)) *
              (E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceForwardPoint n) +
                E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceInversePoint n)))
        (weightReadOff : W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
        (termReadOff : W.finitePrimeTerm n (W.convolutionStar common.sourceTest common.sourceTest) =
            ArithmeticFunction.vonMangoldt n * ...) :
        SourceFinitePrimeArithmeticData W common.sourceTest common.sourceTest n

Notes at `n = 2`:

- `sourcePrimePowerIndex : IsPrimePow 2` via `Nat.prime_two.isPrimePow`.
- `visible` is the boolean `W.finitePrimeTerm 2 (convolutionStar f f) != 0`.
  On concrete `convolutionStar f f = f + f`; use `valueAt (f+f) 2 = 2` and
  `valueAt (f+f) (1/2) = 0`; `linarith`/`norm_num`.
- `pairingReadOff`, `weightReadOff`, `termReadOff` are `simp`-closable with the
  `@[simp]` `finitePrimeTerm`/`primePowerPairing`/`legacyValueAt` lemmas.
- Use the same `f` and `E := ConcreteP1SupportProbe.concreteEvaluation` everywhere.

---

## 3. Contradiction

    3.1  globalData : SourceGlobalFinitePrimeArithmeticData Wconcrete f f
         atIndex only n in {2} -> n=2 -> atom2
    3.2  restricted : SourceRestrictedFinitePrimeArithmeticData Wconcrete f f (0)
         atIndex empty -> False.elim (notMemEmpty n hn)
    3.3  sumRestrictedZero = 0 (unfold;simp);  globalSumNonZero (prime-2 positive)
    3.4  theorem concrete_common_empty :
           CommonFinitePrimeArithmeticSourceData Wconcrete -> False := by
           intro c; let g:=globalData; let r := ... 0
           have hb := c.scopedArchimedeanContributionBalance 0 g r
           -- unwind; archimedean+pole give `-Sigma_g = 0`; linarith.

---

## 4. Environment (exact)

- imports: `ConnesWeilRH.Dev.ConcreteP1SupportProbe`,
  `ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData`.
- evaluation data `E := ConcreteP1SupportProbe.concreteEvaluation`
- leaf namespace `ConnesWeilRH.Source.Dev`; mathlib `v4.30.0`; `#print axioms` = only `[Classical.choice, propext, Quot.sound]`; no axiom/sorry.

---

## 5. Second — re-scope

Give a corrected statement + a `{2}` proof in the covering window; do not expand
consumer sites.

    Repair A: isSubset globalIndexSet (restrictedIndexSet lambda) ->
        forall globalData restrictedData, ...Balance

    Repair B: Sigma_restricted = Sigma_global ->
        forall globalData restrictedData, ...Balance

---
## 6. What I need

1. `atom2`, `globalData`, `restrictedData 0`.
2. `concrete_common_empty`, no `sorry`.
3. Repair A/B.






---


---

## 7. UPDATE (2026-08-09) - verified sub-progress and the exact remaining 2 read-offs

I ran the leaf locally again. Below is the state: some fields already compile
axiom-free, and the two that remain are cut down to a single named reduction.

### 7.1 Already verified compiling (this session, `lake build` green)

- Visibility core is proven: `commonBump (2:Real) = 1` and `f = commonBump`;
  `(2:Real)⁻¹` is outside the bump support, so
  `AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm concreteEval 2 (f+f)`
  is strictly positive (via `sourceFinitePrimeTerm_eq_valueAt`).
- `atom2`'s `visible` field and its `weightReadOff` compile. `visible` reduces
  `Wconcrete.finitePrimeAtomVisible` to the nonzero-prime-term form via
  `Wconcrete.finitePrimeTerm 2 (Wconcrete.convolutionStar f f) =
   concreteEval.sourceFinitePrimeTerm 2 (f+f)`.

### 7.2 Remaining: `pairingReadOff` and `termReadOff`

After `simp`, both are down to a single function-normalization: normalize
`Wconcrete.convolutionStar f f` to `f + f` on the concrete carrier (encode/decode
are identity there). Add once:

```
private lemma conv_add : Wconcrete.convolutionStar f f = f + f
```

provable by `rfl`/`simp` from `concreteTestAlgebra`
(which defines `convolutionStar := fun f g => f + g`) plus
`concreteLegacyTestEquiv` (encode = decode = id). Put `conv_add` in the `simp`
list of both `pairingReadOff` and `termReadOff`.

Then each side becomes the same real number:
`(Real.sqrt 2)⁻¹ * ( norm (f+f) (2:Real) + norm (f+f) ((2:Real)⁻¹) )`,
with `norm (f+f) (2:Real) = norm 2 = 2` and the `(2:Real)⁻¹` term equal to `0`.
For `termReadOff` the leading factor `ArithmeticFunction.vonMangoldt 2` is
nonzero (already proven). Then `norm_num` closes both. No new axioms.

### 7.3 Final deliverable recap

Return the corrected leaf with `conv_add` defined, both `pairingReadOff` and
`termReadOff` closed by `simp [conv_add, ...], norm_num`, and
`concrete_common_empty` built on top as in section 3 of this prompt.
Axiom set stays `[Classical.choice, propext, Quot.sound]`, zero `sorry`,
RH not-claimed.

