# 850 — the "endpoint / half-density sign" is an ARTIFACT of the additive model; the positive claim's real home is the CompactLog convolution carrier

Date: 2026-08-07 · Status: source-verified structural verdict (no new build; every
claim is a named repo theorem/def). This answers Peter's "按你的想法开干" on 方向 2:
it pins what the endpoint/half-density sign really is, why 847/848's "canonical ≤0
is refuted on the concrete space" does NOT transfer to the faithful carrier, and
where the positive sign must be re-proved.

## 0. 先讲结论

**The "canonical Weil ≤ 0 refuted" conclusion (847/848) holds only on the current
ADDITIVE `convolutionSquare` model, and that model is a BAD carrier** — it fails the
structural Mellin-convolution law (`2 = 1`, Yoshida:2727). The `−8 < 0` counterexample
is an artifact of that additive freedom: vanishing on `{0, 1/2, 1}` does not constrain
g at `±i/2`, so the probe force-sets `mellinAt g (±i/2) = −1` and manufactures a
negative pole pairing.

**The real positive claim has a home that already proves nonnegativity:** the
`CompactLogTest` carrier (`CCM25Concrete/CompactLogConvolution.lean`) uses the GENUINE
log-coordinate convolution, where `convolutionSquare(0) = ∫‖g‖² ≥ 0`
(`convolutionSquare_zero_re_nonnegative`) and the windowed HS detector is `F†F`, whose
quadratic form `⟨u, F†F u⟩ = ‖F u‖² ≥ 0` (`Dev/A3NonzeroCompactLogGateProbe.lean`). On
that carrier the endpoint sign is a NATURAL nonnegative object, not a refuted universal.

So the honest next move is NOT "decide the sign on the additive test space" (that
decision is already NO, and it is a fake problem on a fake model). It is to
**re-type the Weil positivity / endpoint-quadratic-form onto the CompactLog carrier**
— the exact "re-type onto the CompactLog HS carrier" conclusion the closure audit
(AGENTS §2, A0/A1/A2/A3) already reached.

## 1. Why the additive refutation is a model artifact, not a sign fact

### 1a. The concrete arithmetic (`CC20ConcreteTestSpace.lean`)

```text
weilLocalSum(g) = -polePairing(g)                     (NormalizedCC20TestSpace 36-63)
polePairing(g)   = poleFunctional (convolutionSquare g)
poleFunctional(F)= Mellin(F)(+i/2).re + Mellin(F)(-i/2).re     (rfl)
convolutionSquare g  = g + g   (additive: encode(conv²g) = 2*encode g)
  =>  polePairing(g) = 2*[ Mellin(g)(+i/2) + Mellin(g)(-i/2) ]       // LINEAR in g
```

So in this model `polePairing` is a **linear functional** of `g`: the additive
convolution doubles the Mellin value (`M(conv²g) = 2·M g`) instead of a genuine
convolution whose Mellin is the product. Vanishing on `{0, 1/2, 1}` restricts
`Mellin g` only on those
three points; `±i/2` is outside that set, so an interpolation can force arbitrary
values there. The Yoshida counterexample sets `Mellin g(±i/2) = −1`, giving
`polePairing = 2(−1)+2(−1) = −4 < 0` and `weilLocalSum = +4 > 0` — hence the same test
is both detector-positive (weil > 0) and canonical-negative (weil ≤ 0 fails). One number,
two sign targets, mutually incompatible — but the incompatibility is a model design,
not RH.

### 1b. Why that freedom is illegitimate

The true Mellin convolution law for a convolution-pairing source is:

```text
NormalizedCC20MellinConvolutionLaw = ∀ f g s, Mellin(convolutionStar f g)(s) = Mellin f (s) * Mellin g (s)
```

The additive model fails this structurally: on a test with Mellin value `1`,
`convolutionStar` multiples the value to `2` (additive doubling) instead of squaring
to `1`, so the law forces `2 = 1`
(`not_normalizedCC20MellinConvolutionLaw`, `CC20YoshidaConstruction.lean:2727`; also
`normalizedCC20TestSpace_is_additive_pole_model`). A carrier that cannot satisfy its
own convolution contract is not a valid source on which to decide a sign.

## 2. The CompactLog carrier already proves the POSITIVE endpoint

`CCM25Concrete/CompactLogConvolution.lean` defines the faithful carrier:

```text
CompactLogTest (test : TestFunction) (compactSupport)
convolution (f g)  = MeasureTheory.convolution f g (mul) volume   // genuine additive convolution in log coord
convolutionSquare g = star(g) ⋆ g  (genuine Hermitian square)
```

Repo-proved nonnegative content on this carrier:

| proposition | fact | meaning |
|---|---|---|
| `convolutionSquare_zero_eq_integral_normSq` | `(g*⋆g)(0) = ∫ ‖g‖²` | the endpoint value is a real norm-square |
| `convolutionSquare_zero_re_nonnegative` | `0 ≤ (g*⋆g)(0).re` | endpoint ≥ 0 for every g |
| `convolutionSquare_add_neg_eq_two_re` | real symmetry | endpoint trace is real |
| `detector_diagonal_re_nonneg` (A3) | `0 ≤ ⟨u, F†F u⟩ = ‖F u‖²` | the HS gate's quadratic form is ≥ 0 |
| `nonzero_hsGate_witness` (A3) | nonzero test satisfies HS gate | the positive content is not empty |

So on the CompactLog carrier, the endpoint / half-density object IS a natural nonnegative
quantity — not "still open on which sign", but already `≥ 0` by construction
(`∫‖g‖²≥0`, `F†F≥0`). The `−8 < 0` refutation only exists because the ADDITIVE model's
`polePairing` is a free-scalar functional; the CompactLog `polePairing` — built from the
genuine convolution — does not have that freedom.

## 3. Honest state after 850

```text
the ADDITIVE carrier (CC20ConcreteTest):
   "canonical ≤0" on every compact-smooth vanishing on {0,½,1}
   ->   REFUTED (847/848, -8<0)
   verdict: THIS CARRIER does not decide RH; its sign is a dead sign.

the positive carrier (CompactLogTest): endpoint ≥ 0
   convolutionSquare(0) = ∫‖g‖² ≥ 0  (repo)
   detector = F†F ≥ 0               (repo, A3)
   verdict: the positive sign is already PROVED here, as a real
   compact-log object — the open work is the carrier re-type & federation.
```

## 4. What remains actually open

Keeping the full objective (not shrinking it):

1. **Re-type the CC20 endpoint / `weilSum` predicate onto `CompactLogTest`**
   (or feed the A3 windowed-HS detector as the `fullWeilPositivity` witness). This is
   the concrete "move onto the CompactLog HS carrier" step AGENTS/A3 already endorses.
   It replaces the refuted additive `canonical ≤ 0` with the proved `F†F ≥ 0`.
2. **Carry the finite-vanishing / moment-data machinery over.** In 845/846/848 the
   vanishing triple and detector already exist; the question is whether the 
   `fullWeilPositivity` slot can be filled by the CompactLog `F†F ≥ 0` witness instead
   of the refuted additive `≤ 0`. (No sign decision to hunt: it is nonnegative by
   construction on this carrier.)
3. **The genuine RH-scale analytic pieces remain unchanged**: generic-λ HS (839/844/845)
   and the cross-branch cancellation (815/842) still need real λ-analysis; 845 killed the
   transport bridge. ## 850 does not claim RH or "3U done".

## 5. Evidence / read at

```
ConnesWeilRH/Source/CC20ConcreteTestSpace.lean:36-63,101-105   additive pole model
ConnesWeilRH/Source/AnalyticCoreBase.lean:274-282,459-500      poleFunctional/polePairing core
ConnesWeilRH/Source/CC20YoshidaConstruction.lean:2218,2227,2293-2474,2724-2727 counterexample + ¬law
ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean   genuine convolution + ≥0 facts
ConnesWeilRH/Dev/A3NonzeroCompactLogGateProbe.lean             F†F ≥ 0 / nonzero HS witness
ConnesWeilRH/Source/CC20TestSpace.lean:25-48   CC20WeilNonpositive / FiniteVanishingCriterion
```

No RH claim is made; nothing here closes the skeleton.
