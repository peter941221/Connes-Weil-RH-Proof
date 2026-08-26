# 1043 — First-cut window architecture: root support, translation, and the two remaining gates

Date: 2026-08-26 (session 14)
Status: architecture landed in Lean (translation layer + root-support ledger);
endpoint sign theorem and Titchmarsh bridge remain open. RH is NOT claimed.

## 1. What the first cut is

The first cut is the unconditional positivity rung on the full prime-free
window, in either of two forms:

```
(SQUARE form)  support (g□) ⊆ (− log 2, log 2)  + triple vanishing  →  0 ≤ qw g
(ROOT form)    support g  ⊆ [− log 2 / 2, log 2 / 2] + triple vanishing → 0 ≤ qw g
```

Both dominate every current budget rung: the third boundary rung covers
`support (g□) ⊆ (−exp(−13/2), exp(−13/2))` with `exp(−13/2) ≈ 1.5e−3`, while
`log 2 ≈ 0.693` — a factor of about 377. The ROOT form is exactly the
published Yoshida (1992) / Connes–Consani (2020) window; the SQUARE form is
strictly stronger and needs the Titchmarsh bridge (§5).

## 2. Published-theorem hypothesis is ROOT support (verified in source)

From the arXiv source `weil-compo.tex` of Connes–Consani 2006.13771:

```
line 125  (mainthmintro): Let g ∈ C_c^∞(ℝ_+^*) have support in the interval
          [2^(−1/2), 2^(1/2)] and Fourier transform vanishing at i/2 and 0 ...
line 1958 (mainthmfine):  ... support in the interval [2^(−1/2), 2^(1/2)] and
          whose Fourier transform vanishes at −i/2 ... then W∞(g*g*) ≥
          Tr(θ(g) S θ(g)*) − c |ĝ(0)|²,  13 < c < 17.
```

`[2^(−1/2), 2^(1/2)]` in the multiplicative coordinate is
`[− log 2 / 2, log 2 / 2]` in the additive log coordinate — the ROOT support,
not the square support. The bad direction is the rank-one term `c |ĝ(0)|²`,
which the triple vanishing (which includes `laplaceAt g 0 = 0`) kills.

## 3. Layer architecture (what landed this session)

```
            triple vanishing on g
                        |
        +---------------+----------------+
        |                                |
   pole kill (existing)          support g ⊆ Icc (−log2/2) (log2/2)
        |                                |
        |                    convolutionSquare_support_subset_two_mul_Ioo
        |                    (NEW: doubled interval, OPEN, endpoints free)
        |                                |
        +---------------→ qw g = − archimedeanTerm (g□)
                                         |
                 +-----------------------+------------------------+
                 |                                (GATE 1)           |
       (this is where the first cut stops today)                     |
                 |                                                   |
   [GATE 1] endpoint sign:  archimedeanTerm (g□) ≤ 0   ... OPEN      |
                 |                                                   |
                 v                                                   |
          0 ≤ qw g   on the ROOT-support class                        |
                                                                     |
   [GATE 2] Titchmarsh:  support (g□) ⊆ (−log2, log2) →              |
            ∃ translation centering g into [−log2/2, log2/2]  ... OPEN
                 |
                 v
          0 ≤ qw g   on the SQUARE-support class  = the first cut, full
```

Landed this session (all axiom-clean, `[propext, Classical.choice,
Quot.sound]`):

+---------------------------------------------------------------+--------------------------------------------------------------+
| Layer                                                         | Declarations                                                 |
+---------------------------------------------------------------+--------------------------------------------------------------+
| Source: structure extensionality                              | CompactLogTest.ext (test field determines the structure)     |
| Source: translation of the square                             | translate_convolutionSquare_apply / translate_convolutionSquare |
| Source: support propagation of the square                     | convolutionSquare_support_subset_two_mul                     |
| Source: endpoint vanishing at ±2a                             | convolutionSquare_two_mul_eq_zero                            |
| Source: open doubled window                                   | convolutionSquare_support_subset_two_mul_Ioo                 |
| Dev: translation invariance leaf                              | qw_translate, vanishesOn_translate_iff,                      |
|                                                               | translate_support_subset_Icc                                 |
| Dev: root-support ledger                                      | qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_      |
|                                                               | rootSupport_logTwoHalf                                       |
| Dev: endpoint interface                                       | qw_nonneg_of_archimedeanTerm_nonpos_of_vanishesOn_cc20Triple|
|                                                               | _of_rootSupport_logTwoHalf                                   |
+---------------------------------------------------------------+--------------------------------------------------------------+

The key new support fact: the doubled endpoints carry NO mass. If
`support g ⊆ [−a, a]`, the autocorrelation integrand at `x = 2a` can only be
nonzero where the two support windows overlap, which is the single point
`t = a`; the continuous integrand supported in a singleton is identically
zero. Hence the square sits in the OPEN window `Ioo (−2a) (2a)` and the
existing prime-kill (`finitePrimeSum_eq_zero_of_support_subset_open_log_two`)
applies verbatim with `a = log 2 / 2`.

## 4. Why the budget ladder cannot reach this window (recap)

`B(R) = log(4π) + γ + R − (1/2) log(1/R)` is strictly increasing on `R > 0`
(proven in Lean, `budgetExpression_strictMonoOn_pos`) with true zero
`R* ≈ 1.98e−3`. At `R = log 2` one has `B(log 2) ≈ +3.9 > 0`. Pointwise
bounds die long before the window; the endpoint theorem needs the vanishing
orthogonality (Hilbert-space mechanism), which is exactly what
Yoshida/CC20 supply.

## 5. GATE 2 — Titchmarsh autocorrelation bridge (status: open, deliberate deferral)

Needed only for the SQUARE form. The required statement:

```
support (g□) ⊆ (−L, L)  →  diameter (support g) ≤ L
                         →  ∃ a, support (translate g a) ⊆ [−L/2, L/2]
```

The forward inclusion (root → square) is the easy direction and is now in
Lean. The reverse direction is the Titchmarsh convolution theorem; the
classical proofs go through Paley–Wiener / Cartwright-class entire-function
theory (indicator diagrams), none of which is in Mathlib today. The
autocorrelation identity `F̂ = |ĝ|²` (F = g□) gives the positivity that makes
the endpoint identity true, but the formalization cost is a separate
multi-session project (est. 2000+ lines of harmonic analysis infrastructure).

Decision: the ROOT form is the landing target for the first cut; the SQUARE
form becomes the Titchmarsh upgrade. The route consumer chain is unchanged:
any unconditional positivity rung extends the same ladder, and the ROOT-form
class is already 377× wider than every existing rung.

## 6. GATE 1 — endpoint sign theorem (the mathematical core, open)

Target statement in our owner (the Dev interface is already in place):

```
archimedeanTerm (g□) ≤ 0
  for all g with support g ⊆ [−log 2/2, log 2/2] and triple vanishing.
```

Two published proof mechanisms, both heavy:

+---------------------+-------------------------------------------------------------+
| Mechanism           | Formalization shape                                         |
+---------------------+-------------------------------------------------------------+
| Yoshida 1992 §6     | high-frequency coercivity + odd 10×10 + even 200×200 exact   |
|                     | rational LDLᵀ certificates; floats only generate, Lean      |
|                     | verifies exact identities.                                  |
| Connes–Consani 2020 | W∞(g□) ≥ Tr(θ(g) S θ(g)*) − c|ĝ(0)|²; positive Sonin-trace  |
|                     | operator + rank-one compression; needs trace-class API and  |
|                     | the numerically-certified constant band 13 < c < 17.        |
+---------------------+-------------------------------------------------------------+

Dictionary obligations before either can be assembled (the four same-owner
readbacks):

```
1. log coordinate:        their ρ = e^t  ↔  our test t
2. window:                [2^(−1/2), 2^(1/2)]  ↔  Icc (−log2/2) (log2/2)
3. vanishing points:      ĝ(0), ĝ(±i/2)  ↔  laplaceAt g (0), (±1/2)
4. archimedean sign:      their W∞(g□)  ↔  −archimedeanTerm (g□)
```

Readback 4 is now VERIFIED ON PAPER (2026-08-26, session 14), from the CC20
source (weil-compo.tex):

* (tex:2048, eq. bombieriexplicit2)
  `W_ℝ(f) = (log 4π + γ) f(1) + ∫₁^∞ (f(x) + f♯(x) − (2/x) f(1)) dx/(x − x⁻¹)`
  with the half-density involution `f♯(x) = x⁻¹ f(1/x)` (pinned by matching
  the prime term `W_p(f) = log p · Σ_m (f(p^m) + f♯(p^m))` against our
  `finitePrimeTermComplex F n = Λ(n) · n^(−1/2) · (F(log n) + F(−log n))`).
* Substituting `x = e^y` and our half-density test `F(y) = e^(y/2) f(e^y)`
  gives literally our numerator:
  `W_ℝ(f) = (log 4π + γ) F(0) + ∫₀^∞ (e^(y/2)(F(y)+F(−y)) − 2F(0)) dy/(e^y − e^(−y))
   = archimedeanTerm F`.
* (tex:~2055) CC20 define `W∞ := −W_ℝ`; hence `W∞ = −archimedeanTerm`, which
  is exactly the sign needed by `qw = pole − arch − primeSum` on the
  prime-free window (`qw = −arch = W∞` there).
* Their bad direction `c |ĝ(0)|²` with `ĝ(0) = ∫ g = laplaceAt g 0` is killed
  by the triple vanishing (which contains `laplaceAt g 0 = 0`).
* The CC20 operator route reduces to Lemma `second` (tex:1932): the operator
  `nf_I = −2ε'(1₊)(id − kf_I)` on `L²(I)`, `I = [−½ log 2, ½ log 2]`,
  satisfies `⟨ξ, nf_I ξ⟩ ≤ γ |⟨ξ₀, ξ⟩|²` with `γ ≈ 2.94355`, i.e. a
  RANK-ONE upper bound; `c = 4γ/log 2 ∈ (13, 17)`.

## 6a. Lean readback and endpoint certificate (landed)

`Dev/C1CC20ArchimedeanReadback.lean` now formalizes the log-coordinate
dictionary without adding an analytic axiom:

* `cc20WRLog_eq_archimedeanTerm` proves the displayed CC20 `W_R` expression is
  exactly the existing same-owner `archimedeanTerm`.
* `cc20WInfinityLog_eq_neg_archimedeanTerm` records the paper's sign convention
  `W∞ = −W_R`.
* `laplaceAt_zero_eq_zero_of_vanishesOn_cc20Triple` and
  `cc20RankOneBadDirection_eq_zero_of_vanishesOn_cc20Triple` kill the CC20
  rank-one error `c |ĝ(0)|²` from the explicit zero node.
* `CC20EndpointTraceCertificate` isolates the remaining analytic payload as
  two fields: a nonnegative trace and the endpoint lower bound
  `trace − c|ĝ(0)|² ≤ W∞(g□)`.
* `qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf`
  consumes that certificate and the existing support ledger to derive
  `0 ≤ qw g` on the ROOT window.

The probe build is axiom-clean (`3606/3606`, zero `sorryAx`).  The certificate
is an interface, not a proof of the CC20 trace estimate; GATE 1 remains open.

The formal content of readback 4 is now present as the checked log-coordinate
theorems above.  The positive-coordinate change-of-variables proof is still
outside this leaf, but no sign surprise remains: our `archimedeanTerm` is
CC20's `W_ℝ` verbatim, and the first cut
needs precisely `W_ℝ ≤ 0` on the window class, i.e. `W∞ ≥ 0` there.

## 6b. Finite-dimensional algebraic brick (landed 2026-08-26)

`Dev/C1CC20FiniteDimensional.lean` now formalizes the real two-dimensional
algebra used by CC20 Lemma `first`:

```text
trace(M - εI) ≥ 0 ∧ det(M - εI) ≥ 0
  ->  ε (x² + y²) ≤ (x,y) M (x,y)ᵀ
```

The leaf also records the exact CC20 coordinate trace and determinant formulas
under `α² + β² = 1`, and packages the hypotheses as
`CC20LemmaFirstCertificate`.  The converse is included: nonnegativity on every
coordinate pair forces the same trace and determinant conditions.  The WSL2
owning build is `960/960`; the import-facing probe is `961/961` and reports
nine declarations using only
`[propext, Classical.choice, Quot.sound]`
with no `sorryAx`.  This closes the finite algebraic substep only; CC20's
numerical spectral bounds, positive Sonin trace, endpoint inequality, and
Archimedean sign theorem remain explicit open premises.

## 6c. Endpoint coefficient arithmetic adapter (landed 2026-08-26)

`Dev/C1CC20EndpointCoefficient.lean` isolates the finite numerical implication
in CC20 Lemma `second`.  With the explicit caller premise

```text
294/100 < gamma < 2944/1000
```

the theorem `cc20EndpointCoefficient_band` proves

```text
13 < 4 * gamma / log 2 < 17.
```

The proof uses Mathlib's certified decimal bounds for `log 2`, so the result is
exact rational arithmetic.  The gamma enclosure remains an open input from
CC20's operator/numerical argument; this leaf does not prove the endpoint trace
estimate or the Archimedean sign.

The owning build is `2123/2123` and the import-facing probe is `2124/2124`,
with only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

## 6d. Endpoint certificate data layer (landed 2026-08-26)

`Dev/C1CC20EndpointCertificateData.lean` joins the three already-landed
layers (gamma enclosure, coefficient band, positive-trace readback) into the
data interface consumed by the same-owner certificate
`CC20EndpointTraceCertificate`:

```text
CC20GammaSpectralData            gamma : ℝ with 294/100 < gamma < 2944/1000
    coefficient = 4 * gamma / log 2, band 13 < c < 17, c > 0
CC20EndpointOperatorTraceData    positive HS trace + explicit endpoint_bound
    toCertificate                 ⟶ CC20EndpointTraceCertificate g
    realTrace_eq_hsNormSq         ordinary trace readback (Source/PositiveTrace)
qw_nonneg_of_cc20EndpointOperatorTraceData
                                 certificate consumer assembly into qw ≥ 0
cc20ScaledNegativeForm_le_rankOne
cc20EndpointResidual_nonpositive_of_shifted_form
                                 the scalar rank-one transfer of Lemma second
zeroTraceCertificate_of_nonnegative_wInfinity
                                 caller-supplied zero-trace regression witness
                                 (a definition: the certificate is data)
```

Evidence boundary: `endpoint_bound` remains an explicit analytic field of
`CC20EndpointOperatorTraceData`; nothing in this leaf proves the CC20 trace
estimate or the Archimedean sign.  The zero-trace witness is deliberately
support-free — the support/prime-free hypotheses belong to the downstream
`qw` consumer.

The six-target batch build (finite-dimensional brick, coefficient adapter,
certificate data, and all three probes) completes `3613 jobs`, `0 error`;
all eighteen audited declarations depend only on
`[propext, Classical.choice, Quot.sound]` with no `sorryAx`.

## 6e. Yoshida LDLᵀ engine and the CC20 operator-gap skeleton (2026-08-26)

Two further leaves land the remaining algebraic layers of Gate 1:

**`Dev/C1YoshidaLdlCertificate.lean` — the exact elimination engine.**
Yoshida §6 tracks, in strict rational interval arithmetic, the classical
identity

```text
x ⬝ᵥ ((L * D * Lᵀ) *ᵥ x) = ∑ i, d i * (Lᵀ *ᵥ x) i ^ 2
```

The leaf proves this reading identity (`ldlt_dotProduct_eq`), the forward
substitution injectivity of a unit lower triangular transpose
(`unitLowerTriangular_transpose_mulVec_injective`, largest-nonzero-index
argument), and assembles them into `posDef_of_ldlt : U = L * D * Lᵀ ⟹
U.PosDef`.  A synthetic 3x3 rational witness (`witnessL`, `witnessD`) makes
the pipeline non-vacuous: `witness_matrix_eq` evaluates the exact Gram
matrix, and `witness_posDef` certifies it.  This is the first structurally
nonzero Yoshida-shape certificate; transcribing the actual 10x10 odd /
200x200 even digamma interval data remains future work.

**`Dev/C1CC20OperatorGap.lean` — the abstract skeleton of Lemma `second`.**
With caller premises

```text
(H1)  qT ξ + a·(ell ξ)² ≥ ε₂·‖ξ‖²            (Lemma `first` on T)
(H2)  −ε₁·‖ξ‖² ≤ qKf ξ − qT ξ                (‖kf_I − T‖ ≤ ε₁)
```

the leaf proves the two displayed algebra steps of the paper:
`cc20GapCoercivity_transfer` (shifted coercivity `ε₂ − ε₁` for `qKf`) and
`cc20NegativeForm_le_rankOne` (the sign flip by `−2ε'(1₊) ≤ 0` giving
`⟨ξ|nf_I ξ⟩ ≤ γ·(ell ξ)²` with `γ := 2ε'(1₊)·a`), plus the factory
`CC20OperatorGapData.toGammaSpectralData` feeding the coefficient band.
The spectral estimates themselves remain caller premises.

Both probes are green (3621 jobs, 0 error; all audited declarations only
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`), and the full root
build after the complete source sync passes: `4147 jobs`, `0 error`.

## 7. Session boundary

* Translation invariance layer: LANDED, axiom-clean
  (`C1YoshidaTranslationProbe` green, 3505 jobs, 0 sorryAx).
* Root-support ledger + endpoint interface: LANDED, axiom-clean
  (`C1HealthyYoshidaDetectorProbe` green, 3605 jobs, 0 sorryAx; all five new
  declarations `[propext, Classical.choice, Quot.sound]`).
* CC20 log-coordinate readback + endpoint certificate consumer: LANDED,
  axiom-clean (`C1CC20ArchimedeanReadbackProbe` green, 3606 jobs, 0 sorryAx).
* CC20 finite-dimensional trace/determinant + shifted-coercivity brick: LANDED,
  axiom-clean (`C1CC20FiniteDimensionalProbe` green, 961 jobs, 0 sorryAx).
* CC20 endpoint coefficient arithmetic band: LANDED, axiom-clean
  (`C1CC20EndpointCoefficientProbe` green, 2124 jobs, 0 sorryAx); the gamma
  enclosure remains an explicit caller premise.
* CC20 endpoint certificate data layer: LANDED, axiom-clean (six-target batch
  `3613 jobs`, 0 error; 18 declarations `[propext, Classical.choice,
  Quot.sound]`, 0 sorryAx); `endpoint_bound` remains an explicit analytic
  field.
* Yoshida LDLᵀ engine + synthetic 3x3 witness: LANDED, axiom-clean
  (`C1YoshidaLdlCertificateProbe` green); actual 10x10 digamma interval
  transcription still future work.
* CC20 operator-gap skeleton of Lemma `second` (coercivity transfer + sign
  flip + gamma factory): LANDED, axiom-clean (`C1CC20OperatorGapProbe`
  green); spectral estimates remain caller premises.
* Full root build after complete source sync: GREEN (`4147 jobs`, 0 error).
* Endpoint sign / trace theorem: NOT attempted; the certificate remains the
  explicit open analytic obligation (§6a).
* Titchmarsh bridge: NOT attempted; deferral decision recorded in §5.
* RH remains unclaimed; the universal W4b over all vanishing tests is open.
