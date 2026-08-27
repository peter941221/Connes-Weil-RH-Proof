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

## 6f. Hilbert Lemma `first` and operator spectral decomposition (landed 2026-08-26)

The next layer replaces both scalar shadows in §6e by their genuine Hilbert
space and bounded-operator statements.  The source is Connes--Consani,
arXiv:2006.13771, Lemmas `first` and `second`:
<https://arxiv.org/abs/2006.13771>.

`Dev/C1CC20HilbertLemmaFirst.lean` first proves the complex Hermitian 2x2
criterion and then performs the full orthogonal decomposition

```text
xi = x phi + u,       u perpendicular to phi
u  = y chi + z,       z perpendicular to chi

||xi||^2 = |x|^2 + |y|^2 + ||z||^2.
```

This gives `cc20LemmaFirstHilbertForm_ge_epsilon`: the shifted determinant
certificate controls every vector of the ambient complex Hilbert space, not
only a real coordinate pair.

`Dev/C1CC20OperatorGap.lean` then proves the missing spectral-decomposition
algebra.  With

```text
T xi = lambdaMax * <phi,xi> phi + R(xi_perp)
R(phi_perp) is contained in phi_perp
Re <u,Ru> <= lambda2 * ||u||^2       for u in phi_perp,
```

the theorem `cc20DefectQuadraticForm_ge_of_spectralDecomposition` derives

```text
-(lambdaMax - 1) |<phi,xi>|^2
  + (1 - lambda2) ||xi_perp||^2
    <= Re <xi,(id - T)xi>.
```

The end-to-end checked chain is now

```text
Hermitian 2x2 determinant certificate
  -> cc20LemmaFirstHilbertForm_ge_epsilon
  -> cc20TCoercivity_of_spectralDecomposition
  -> ||kf_I - T|| <= epsilon1
  -> cc20NegativeForm_le_rankOne_of_spectralDecomposition_and_opNorm
  -> gamma * |<psi,xi>|^2 rank-one upper bound.
```

The last theorem no longer accepts a caller-supplied pointwise `hspectral`
inequality.  It accepts the actual decomposition, invariant-complement bound,
and operator norm estimate.  All new declarations are axiom-clean:
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`; the focused
operator owner/probe build completes `3613/3613`, and the synchronized root
build completes `4147/4147`.

The remaining boundary is concrete and analytic, not scalar algebra:

```text
paper's concrete L2(I) operators T, R, kf_I                  OPEN
certified lambdaMax / lambda2 and residual Rayleigh bound   OPEN
certified ||kf_I - T|| <= epsilon1                          OPEN
certified alpha, beta, a, epsilon2 determinant inequalities OPEN
positive Sonin trace endpoint / W_infinity lower bound      OPEN
RH-level universal coverage root                            OPEN
```

In particular, the paper's numerical statements (`lambda2 <= 0.772216`, the
`epsilon1` enclosure, and the reported overlaps) have not been imported as
floating-point evidence.  They still require exact interval certificates and
the concrete operator construction before Gate 1 closes.

## 6g. Raw L² integral-operator bounds for `kf_I` (landed 2026-08-27)

The first analytic brick toward the paper's concrete windowed operator
`kf_I` on `L²(I)` is now in Lean.  The source is the Hilbert--Schmidt
estimate behind Connes--Consani, arXiv:2006.13771: an `L²` kernel applied to
an `L²` input gives a bounded output, controlled pointwise by the kernel's
row mass and the input norm.

`Dev/C1CC20LpOperator.lean` supplies this in its raw integral form (not via
the abstract `Lp` type), matching the owner-preserving idiom on this branch:

```text
applyKernel k f x  =  ∫_y k(x, y) f(y) dy        -- definition
‖(Af)(x)‖ ≤ ‖k(·,x)‖₂ · ‖f‖₂                    -- theorem
```

The theorem `applyKernel_pointwise_l2_bound` is exactly Cauchy--Schwarz for
the pairing `(u, v) ↦ ∫ u(y) v(y) dy`, with the kernel's `x`-row as one
factor and `f` the other; the two `MemLp (· 2)` hypotheses say both factors
lie in `L²`.  The proof is three steps: norm-of-integral ≤ integral-of-norm,
the pointwise `‖k f‖ = ‖k‖ · ‖f‖` rewrite a.e., then the Lp/Lq product bound.

The integrated square-mass brick is now also formalized in
`Dev/C1CC20LpOperatorNorm.lean`.  Its theorem
`rows_l2_ae_of_kernel_l2` derives `MemLp (fun y => k (x, y)) 2` for almost
every row of a two-variable `L²` kernel.  Its endpoint
`applyKernel_l2_sq_bound` proves

```text
∫⁻ x, ‖(Af)(x)‖ₑ²
  ≤ (∫⁻ p : ℝ×ℝ, ‖k(p)‖ₑ²) * (∫⁻ y, ‖f(y)‖ₑ²).
```

The proof keeps the global calculation in `ENNReal` lintegrals, so a
non-integrable Bochner integral cannot collapse to `0`.  It combines the
pointwise Cauchy--Schwarz bound with a.e. row `L²` membership, lintegral
monotonicity, constant-factor extraction, and `lintegral_prod`.

This remains boundedness infrastructure only: it carries no RH sign or
coverage claim and does not construct the concrete kernel of `kf_I`.  The
still-open item

```text
paper's concrete L2(I) operators T, R, kf_I                  OPEN
```

above is unchanged: the estimate bounds an arbitrary `L²` kernel, but the
paper's specific `kf_I`, `T`, and `R` kernels are not yet written down.

Verification (per-brick protocol): native WSL ext4 builds are green for
`ConnesWeilRH.Dev.C1CC20LpOperator` (`2677 jobs`) and
`ConnesWeilRH.Dev.C1CC20LpOperatorNorm` (`2683 jobs`).  The focused audit for
the two integrated declarations reports exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.  The aggregate
root build is not evidence for these standalone `Dev/` leaves; they are
verified by explicit targeting.

## 6h. `Q(delta)` / `Qepsilon` pointwise-diagonal owner guard (landed 2026-08-27)

Primary-source check: Connes--Consani, Proposition 5 and Remark 6,
[arXiv:2006.13771](https://arxiv.org/html/2006.13771), define the compact
operator `K_I` through the additive kernel
`Qepsilon(exp(|v|)) / (2 * epsilon'(1+))` and state that
`Qepsilon(1) = 0`.  Thus a formal transcription of that raw paper kernel has
a zero pointwise diagonal.

The existing repository object is not that kernel.  It is explicitly the
ordinary `Q(delta)` regular profile, with diagonal value

```text
cc20QDeltaDiagonalValue
  = 8 * pi^2 / 9 + sineIntegralQuotient (4 * pi) - 1 / 2.
```

The new source facts prove it is strictly positive without numerical
evaluation:

```text
Real.neg_one_le_sinc
  -> -1 <= sineIntegralQuotient(x)
  -> pi > 3
  -> 0 < cc20QDeltaDiagonalValue.
```

Consequently `cc20RegularKernel_diagonal_pos` holds at every positive
coordinate, and
`cc20RegularKernel_ne_of_pointwise_zero_diagonal` rejects a literal equality
between the current regular kernel and any candidate whose pointwise diagonal
is identically zero.

This is a strict owner guard, not an operator theorem.  A diagonal is a
measure-zero set, so this result alone does not rule out almost-everywhere
kernel equality or equality of induced integral operators.  Any future bridge
to the paper's `K_I` must first formalize its own kernel/action and then prove
the required off-diagonal or operator-level relation; it may not instantiate a
same-kernel premise with the current `Q(delta)` regular profile.

## 6i. Formal `Qepsilon` series and raw endpoint kernel (landed 2026-08-27)

The first owner guard only used the paper's stated diagonal value.  The new
source module `CC20Concrete/EndpointKernelFormula.lean` now transcribes the
formula that gives that value.  Its primary source is Connes--Consani,
equations (84), (97)--(99), and (104):
<https://arxiv.org/html/2006.13771>.

`CC20EndpointSpectralData` deliberately records exactly the ingredients which
the future concrete prolate construction must supply:

```text
lambda(n), xi_n^an, (xi_n^an)', epsilon'(1+)
  -> lambda(n)^2 / (1 - lambda(n)^2)
  -> epsilonUpper(rho)                 [Lemma 4 rewrite]
  -> qEpsilon(rho)                     [equation (99)]
  -> qEpsilon(exp(|x - y|)) /
       (2 * epsilon'(1+))              [equation (104), raw K_I kernel]
```

The normalizing slope is not an arbitrary positive field: the contract also
requires the summable equation-(100) identity
`epsilon'(1+) = sum_n lambda(n)^2/(1-lambda(n)^2) * xi_n^an(1)^2`.
The actual prolate construction still has to prove that identity.

The exact endpoint calculation is now checked rather than cited:

```text
C_n(1) = 0                         -- integral endpoints coincide
qEpsilon(1) = tsum_n weight(n)*0 = 0
K_raw(x, x) = qEpsilon(exp(0)) / (2*epsilon'(1+)) = 0.
```

The corresponding raw diagonal integral is also formalized as
`integral_endpointWindowKernel_diagonal_zero` for every measure.  This is the
precise kernel-level content of Remark 6; it is not yet an equality with the
trace of a Hilbert-space operator.

`C1CC20EndpointKernelOwnerGuard.lean` also log-lifts this raw kernel to the
positive-coordinate domain and proves the specific theorem
`cc20RegularKernel_ne_endpointKernelOnPositiveCoordinates`.  Thus the
existing positive-diagonal `Q(delta)` owner cannot be substituted for the
paper formula even as a literal kernel function.

This progress has an important precise limit.  Lean's `tsum` is totalized, so
the `rho = 1` result is sound with no convergence premise because every
summand is zero.  It does **not** show that the series converges to the
analytic `Qepsilon` for other `rho`, construct the prolate modes, prove the
kernel has finite `L2` mass, or construct the interval-restricted bounded
operator `K_I`.  Those four analytic steps remain the required route into the
already-proved `C1CC20LpOperator` and `C1CC20OperatorGap` foundations.

Focused native WSL ext4 builds are green for the formula, owner guard, and
audit; every new theorem audits to `[propext, Classical.choice, Quot.sound]`
with no `sorryAx`.

## 6j. Windowed raw-kernel L2 brick (landed 2026-08-27)

`Dev/C1CC20RawKernelMass.lean` connects the §6i formula layer to the `L2`
boundedness foundation of `C1CC20LpOperator` / `C1CC20LpOperatorNorm`.  The
raw kernel depends on its arguments only through the displacement
`p.2 - p.1`, so restricting both coordinates to the symmetric window
`[-a, a]` and carrying an explicit uniform profile bound `B` yields:

```text
endpointKernelOnSquare data a        =  ([-a,a]^2).indicator K_raw     -- definition
measurable_endpointKernelOnSquare    measurable from continuous profile
exists_norm_bound_on_window          compactness packages B >= 0       (∀ p in window, ‖K_raw p‖ ≤ B)
enorm_sq_endpointKernelOnSquare_le   pointwise: ‖kernel‖ₑ² ≤ B²
endpointKernelOnSquare_diagonal_zero Remark 6 survives the restriction
memLp_..._of_mass_lt_top             MemLp 2 from total-mass premise
applyKernel_l2_sq_le_of_kernelMassTopLt   explicit operator bound via applyKernel_l2_sq_bound
```

The boundedness certificate itself stays caller-supplied on purpose: it is
exactly the slot where a prolate/uniform-convergence realization (or a
Yoshida-style numerical certificate) plugs in.  Verification is per-brick:
native WSL ext4 explicit targets green (`C1CC20RawKernelMass` 2685 jobs,
`C1CC20RawKernelMassAudit` 2686 jobs); all seven audited declarations report
only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

### 6j' Explicit certified window mass (landed 2026-08-27)

The caller-supplied total-mass and profile-bound premises are now eliminated
into theorems inside the same leaf, under one hypothesis pair — continuity of
the real displacement profile plus `0 ≤ a`.  The ladder:

```text
lintegral_indicator_one              ∫⁻ membership weight = volume(windowPair)
volume_cc20Window_of_nonneg          volume [-a,a] = ofReal (2a)
volume_cc20WindowPair_of_nonneg      volume windowPair = ofReal ((2a)^2)
enorm_sq_le_weighted_bound           ‖kernel‖ₑ² ≤ Bc² · weight(pointwise)
lintegral_enorm_sq_le_of_profileBound    master mass ≤ Bc² · volume(windowPair)
lintegral_enorm_sq_le_closed_of_profileBound   ≤ ofReal (Bc²·(2a)²)
memLp_endpointKernelOnSquare_of_profileBound   MemLp 2, no mass premise left
applyKernel_l2_sq_le_explicit        FLAGSHIP: from continuity alone,
    ∃ Bc ≥ 0, ∫⁻ ‖A f‖ₑ² ≤ ofReal(Bc²(2a)²) · ∫⁻ ‖f‖ₑ²
```

The flagship packages compactness (`exists_norm_bound_on_window`) with the
mass chain, so any continuous displacement profile on the square window now
carries an explicit square-mass operator bound with zero caller-supplied
analysis.  What remains open above this brick is unchanged and concrete:
writing down the paper's actual `kf_I / T / R` kernels via the prolate data
(`CC20EndpointSpectralData`) and proving the equation-(100) slope identity.
Verification unchanged: both targets green (`2685`/`2686` jobs), all thirteen
audited declarations `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

### 6k. Yoshida finite-matrix data: provenance check and certificate engine scaffold (2026-08-27)

The GATE 1 numerical route needs finite Hermitian-form certificates. The
primary source check today settled what is and is not available:

* The cited chapter `[Yos92]` — H. Yoshida, *On Hermitian forms attached to
  zeta functions*, Adv. Stud. Pure Math. 21 (1992), 281–325 — exists on
  Project Euclid, DOI `10.2969/aspm/02110281`, but only page 1 previews; the
  full text (with the matrix entries) is access-restricted.
* From the previewable introduction (OCR quoted verbatim): Yoshida's test
  class is `C(a) = { φ | supp φ ⊆ [−a, a] }` — the SQUARE support form in our
  additive log coordinate — and R.H. reduces to positive definiteness of the
  hermitian form restricted to every `C(a)`. This confirms the target shape
  of our SQUARE-first-cut bridge but supplies NO entry formulas.
* CC20 itself does not quote Yoshida's matrices; its own §6 controls the gap
  with Hermitian Toeplitz matrices around equation (114)'s trigonometric
  approximation.

Route consequence: the "odd 10×10 / even 200×200 digamma LDLᵀ" description of
the Yoshida route stays UNCONFIRMED until either full-text access or a
paper-supplied table appears; the CC20 §6 Toeplitz route is the currently
accessible alternative. Nothing consumes fabricated data.

What landed anyway is the certified-numerics ENGINE,
`scripts/yoshida_intervals/` (README + generator, stdlib-only Python):

```text
Interval / const_interval / add / scale / mul / join   exact Fraction algebra
psi_bracket(x, width_target)   rigorous digamma bracket at rational x > 0
                               psi(x) = -gamma + S_N(x) ± |x-1|/N
                               tail bound |x-1|/N by telescoping k(k+1)
                               (direct-series cost model documented:
                                N ~ |x-1|/width; deep targets future work)
ldlt_positive_definite(A)      exact symmetric rational PD inspection,
                               mirror of Dev/C1YoshidaLdlCertificate
emit_*                         Lean-ready transcription snippets
source field                   mandatory per value node - anti-fabrication
```

Self-tests green on WSL (stdlib and `--mpmath` variants): T1 reproduces the
landed Lean witness exactly (`d = (4,9,1)`, subdiagonals `1/2, 1/3, 1/4`);
T2/T3 verify `psi(1) = −gamma` and `psi(1/2) = −gamma − 2·log 2` against
published digit expansions; T5 cross-checks brackets against high-dps
mpmath floats modulo explicit parsing slack; T6 rejects negative-definite
input. This closes nothing in GATE 1 by itself; it pins the honest boundary
where real matrix data must enter from a primary source.

### 6l. Accessible-source breakthrough: Bombieri 2000 memoir (2026-08-27)

With email ruled out, the paywall problem was routed around instead: E.
Bombieri, *Remarks on Weil's quadratic functional in the theory of prime
numbers, I*, Atti Accad. Naz. Lincei (9) 11 (2000), 183–233 is FREE in full
at <http://www.bdim.eu/item?fmt=pdf&id=RLIN_2000_9_11_3_183_0> (EUDML entry
<https://eudml.org/doc/252338>). Verbatim findings relevant to GATE 1:

* On Yoshida (memoir p. 184): "he shows how the positivity of this
  functional for functions supported in a fixed interval [−t, t] can be
  reduced to a finite calculation (depending on t), **and verifies this
  positivity for t = (log 2)/2**." The target window of the first cut has
  EXACTLY this half-width — Yoshida's published verification covers the
  first-cut window scope.
* The abstract re-proves the same positivity theorem independently.
* Full explicit machinery (§§6–7): `K(x) = sin x / x`, `M = e^t`, and the
  finite-matrix resolvent built solely from elementary trigonometric/
  hyperbolic data:

```text
(7.1)  K*(x,y;t) = [ (1/4+xy)·K(t(x−y)) − cosh(t)·cos(t(x−y))
                     − cos(t(x+y)) ] / (2t·sinh(t))
(7.3)  H(x;y;t)   = 2t · K*(x;y;t)        (up to the printed 1/(1/4+y²)
                                           normalization; verify against PDF
                                           when transcribing)
(7.4)  w_gamma = Λ Σ_gamma' H(γ,γ';t) w_gamma'
```

Usability analysis (read against §8): `H(Γ;t)` is indexed by a multiset Γ
of zero ordinates (ρ = 1/2 + iγ), and Lemma 10 shows every γ real implies
all eigenvalues non-negative while non-real conjugate pairs create negative
eigenvalues — i.e. Bombieri's matrices are a CONDITIONAL off-line-zero
detector, not directly an unconditional positivity certificate. Direct
reuse inside GATE 1 therefore does not follow mechanically.

Strategic consequences:

1. The mathematically required endpoint fact — positivity of the Weil
   functional on root-support tests — exists in the published record as a
   verified finite calculation at our exact window (source: Bombieri's
   description of [Yos92]).
2. Since both Bombieri's and (described) Yoshida's finite methods reduce
   window-class positivity to spectra of explicit kernels over [−t, t]
   bands, the unconditional formalizable route remains the prolate /
   Hermitian-Toeplitz program of CC20 §6 — consistent with §6k's verdict;
   no dependency on inaccessible pages is created.
3. The elementary kernel toolbox above (sinc-based entries) is the shared
   substrate both routes reduce to; it is what a future Lean interval-
   certificate leaf will consume.

### 6m. Paper-window operator brick: `kf_I` boundedness on `I` (landed 2026-08-27)

`Dev/C1CC20RootWindowOperator.lean` instantiates the explicit certified
window-mass flagship at the paper's OWN working interval. New objects:

```text
cc20RootHalfWidth                    log 2 / 2, positive by log_pos/norm_num
cc20RootWindow_eq_cc20Window         I = cc20Window (log 2 / 2)   [rfl]
two_mul_cc20RootHalfWidth_sq_eq_logTwo_sq   (2a)^2 = (log 2)^2 at a = root radius
volume_cc20RootSquarePair            area(I × I) = ofReal ((log 2)^2)
applyKernel_l2_sq_le_explicit_rootWindow    FLAGSHIP at the paper window:
    ∃ Bc ≥ 0, ∫⁻ ‖A f‖ₑ² ≤ ofReal (Bc²·(log 2)²) · ∫⁻ ‖f‖ₑ²
      from Continuous data.endpointWindowKernel alone
```

This is the boundedness half of the paper's `nf_I`/`kf_I` on `L²(I)`
(arXiv:2006.13771, Lemma `second`'s window), with the doubled half-width
collapsing exactly to `(log 2)^2` in the closed form.  The spectral half —
the prolate data of `CC20EndpointSpectralData`, the equation-(100) slope
identity, and every sign estimate — remains the explicit caller obligation;
no RH claim.  Proof note for the record: `ring` treats a plain noncomputable
def as an opaque atom (`4·X^2 = (log 2)^2` refuses to close), so the
doubling identity needs `unfold cc20RootHalfWidth` before the ring pass —
the same hazard class as the §7 nlinarith-atom gotcha, now confirmed for
`ring`.  Verification per-brick: `RawKernelMass → RootWindowOperator →
Audit` chain green on ext4 explicit targeting (`2687` jobs); all five new
declarations report exactly `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`.

### 6n. CC20 §5–6 extraction: the numerical bridge into GATE 1 (2026-08-27)

Primary-source quotes pulled from <https://arxiv.org/html/2006.13771>
(all equation numbers theirs):

* Proposition 5, eqs (103)/(104): for an interval `I ⊆ [−log 2, log 2]`
  of length ≤ log 2 the correlation form defines
  `N_I = −2ε′(1₊)(Id − K_I)` with

```text
⟨η|K_I ξ⟩ = (2ε′(1₊))⁻¹ ∫∫ η̄(x) ξ(x+v) (Qε)(exp|v|) dx dv
```

  i.e. a DISPLACEMENT-type operator: only `v` enters the raw profile, `x`
  runs along the interval.
* Lemma 3, eqs (119)/(120)/(121): if `τ(λ,α,d,m)` approximates
  `χ := (Qε)(exp|x|)/(2ε′(1₊))` in `L¹([0, log 2])` to distance ≤ ε,
  then on `I = [−(log 2)/2, (log 2)/2]` the compact `K_I` is within OPERATOR
  NORM ε of the finite rank
  `T = λ Σ_n (e_n − d(|n|) e_{α_n})`, where `e_α` are rank-one projections
  onto `exp(±2πiαx/log 2)`, with conventions `α_{−n} = −α_n`, `d(0) = 0`,
  and `α_n = n`, `d(n) = 1` for `n > m`.  The proof is one inequality,
  eq (121): `|∫∫ η̄ξ(x+v)a(v)| ≤ ‖ξ‖‖η‖ ∫|a(v)|dv` via pointwise
  Cauchy–Schwarz in `x`.
* Eq (114)/(115) (Fact 1): with `m = 1732` and the paper's downloaded
  angles/coefficients, `2∫₀^{log 2}|τ − χ| dx ∼ 0.00122`.
* §6.2 eq (105): discretized Toeplitz form on lattice `ωZ`, `ω = 1/5000`;
  precise numeric tables are published as a DOWNLOAD, not in text — any
  transcription must flag them as externally-sourced certificate inputs.
* Appendix F: the first 11 prolate terms already give uniform 1e−11
  approximation of `Qε`.

Contract for the next Lean leaves (above the landed
`C1CC20RootWindowOperator` boundedness brick):

```text
L1  corrKernel/composition: displacement-form kernel equals
    profile∘(p.2 − p.1) on the pair window        [definition-level]
L2  opNorm-distance bridge, paper (121):
    ‖A_a − A_b‖ ≤ L¹-window-mass of (a − b)
    via pointwise Cauchy–Schwarz                  [the reusable engine]
L3  finite-rank slot: T = λ Σ (e_n − d e_{αn})    [spectral consumer]
```

Evidence boundary: the numeric certificates (λ, angles α_j, d(j), Fact 1's
0.00122) originate in a computer calculation whose precise values are a
downloadable artifact; they enter Lean ONLY through explicit rational-
interval certificate nodes (per §6k anti-fabrication mechanics), never as
bare literals.

### 6o. Translate-invariance pack: the L2 shift slot discharged (landed 2026-08-27)

New leaf `Dev/C1CC20TranslateInvariance.lean` (+ audit).  This removes the
last caller premise of the L2a slice brick:

```
abs_corrInnerSlice_le  η ξ v            (Dev/C1CC20CorrBridge.lean)
   requires  hxiShiftedMemLp : ∀ w, MemLp (fun x => ξ (x + w)) p2
        └────────── now supplied by memLp_shift hξ w ──────────┘
```

Landed content, all mathlib-native (signatures confirmed against v4.30 by
compiler probes):

* `lintegral_enorm_sq_shift` : `∫⁻ ‖ξ(·+w)‖ₑ² = ∫⁻ ‖ξ‖ₑ²`, directly
  `lintegral_add_right_eq_self`.  Pitfall recorded: the lemma reads
  `∫⁻ f(x+g) = ∫⁻ f x`; one must feed the UNSHIFTED base
  `(fun x => ‖ξ x‖ₑ ^ 2)` so that the lemma's own shift produces the
  desired left-hand side — feeding an already-shifted body double-shifts.
* `ltTop_of_memLp` : plain-mass finiteness recovered from a `MemLp`
  hypothesis (converse direction of the RawKernelMass expansion).
  The reverse rewrite `rw [← eLpNorm_lt_top_iff…]` misses because the iff's
  RHS pattern carries the exponent as `(ENNReal.ofReal 2).toReal`, while
  the goal shows a literal `2`; fix is to read the biconditional FORWARDS
  (`.mp`) into a local hypothesis, normalize with
  `rw [ENNReal.toReal_ofReal …] at`, then `exact`.
* `memLp_shift` : strong measurability of `ξ ∘ (+w)` via
  `hξ.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_right
  volume w)`, finiteness via the two items above and the same
  iff-expansion closer used in
  `C1CC20RawKernelMass.memLp_endpointKernelOnSquare_of_mass_lt_top`.

Verified per-brick on ext4: explicit target
`ConnesWeilRH.Dev.C1CC20TranslateInvarianceAudit`, 2686 jobs, exit clean;
all three declarations `[propext, Classical.choice, Quot.sound]`;
`sorryAx` count in log = 0.

Next bricks up the same ladder (paper eqs above):

```text
L2b  pairing fold over L¹ weight -> paper (121):
     needs real-integral shift twin + weight integrability bookkeeping;
     consumes abs_corrInnerSlice_le
L1   displacement-composition identity (definition-level tie to
     endpointKernelOnSquare / endpointWindowKernelComplex)
L3   finite-rank spectral-control slot T = λ Σ (e_n − d(|n|) e_{αn})
```

### 6p. Uniform displacement bound: eq-(121) constant made displacement-free (landed 2026-08-27)

New leaf `Dev/C1CC20UniformSlice.lean` (+ audit), same ladder as §6o:

```
abs_corrInnerSlice_le  :  ‖slice v‖ ≤ m(η)^½ · m(ξ∘(+v))^½   (v-dependent)
       │  mass_shift_real                          [this leaf]
       ▼
abs_corrInnerSlice_uniform :
       ‖corrInnerSlice η ξ v‖ ≤ (∫‖η x‖²)^½ · (∫‖ξ x‖²)^½   ∀ v
```

Landed content:

* `integral_shift` — REAL Bochner shift twin, generic normed-space:
  built from root-namespace `map_add_right_eq_self` (`IsAddRightInvariant`
  instance) fed through `integral_map`, pushing the measurability premise
  across the measure equality first.
* `measure_preimage_add_right_null` — preimage of a null set under
  right-addition is null; the combinational core of transporting
  a.e.-statements along shifts. Uses `← Measure.map_apply` to enter map
  form.
* `aestronglyMeasurable_norm_sq_shift` — `.norm.pow 2` closes pointwise,
  composition rides `quasiMeasurePreserving_add_right`; `simpa` normalizes
  the function-FPow/∘ shapes onto plain lambdas (both compile checks fail
  otherwise).
* `mass_shift_real` — `∫ ‖ξ(x+w)‖² = ∫ ‖ξ x‖²` for REAL integrals, the twin
  actually consumed by folding.
* `abs_corrInnerSlice_uniform` — the displacement-free slice Cauchy–Schwarz
  constant, exactly what equation (121) multiplies by the `L¹` mass of the
  window profile.

Verified per-brick on ext4: explicit target
`ConnesWeilRH.Dev.C1CC20UniformSliceAudit`, 2687 jobs, exit clean;
all five declarations `[propext, Classical.choice, Quot.sound]`;
`sorryAx` count 0.

Remaining half of L2b (recorded, not landed): strong measurability of the
slice map `v ↦ corrInnerSlice η ξ v`. Route mapped out by probes this
session: MemLp's definitional form is an existential
(`∃ rep, StronglyMeasurable rep ∧ f =ᵐ rep`) so Borel representatives come
free via `obtain`; the joint function assembles through
`StronglyMeasurable.comp_measurable` + `.mul`; partial integration uses
`StronglyMeasurable.integral_prod_right` (joint form on `uncurry f`);
pointwise slice equality per fixed `v` rides
`QuasiMeasurePreserving.preimage_ae_eq` (QuasiMeasurePreserving.lean:126)
through the null-preimage lemma above; domination/integrability closes with
`Integrable.mono` against `(fun v => K * ‖a v‖)` from
`Integrable.const_mul`.

### 6q. L2b pairing fold: the full equation-(121) analytic engine (landed 2026-08-27)

`Dev/C1CC20PairingFold.lean` closes the remaining L2b half as two
axiom-clean declarations:

```text
aestronglyMeasurable_corrInnerSlice
  MemLp eta 2, MemLp xi 2
    -> AEStronglyMeasurable (fun v => corrInnerSlice eta xi v)

abs_corrWeightedFold_le
  || integral_v a(v) * corrInnerSlice eta xi v ||
    <= (integral ||eta||^2)^(1/2)
       * (integral ||xi||^2)^(1/2)
       * integral ||a||.
```

The first declaration chooses the Borel representatives contained in the
definition of `MemLp`; the joint map `(v,x) -> eta(x) * xi(x+v)` is strongly
measurable by coordinate composition and multiplication, and
`StronglyMeasurable.integral_prod_right` integrates out `x`.  The old and
representative slices agree for each `v` through
`eventuallyEq_comp_add_right`.

The second declaration consumes the displacement-free bound
`abs_corrInnerSlice_uniform`, bounds each folded integrand by
`K * ||a v||`, proves it integrable with `Integrable.mono`, and applies
`norm_integral_le_integral_norm` followed by `integral_mono`.  This is the
formal analytic content of the Cauchy--Schwarz step in paper equation (121);
the concrete profile `a = K_I - T` and its numerical L1 certificate remain
separate next obligations.

Native WSL2 ext4 audit evidence:
`lake build ConnesWeilRH.Dev.C1CC20PairingFoldAudit` completed successfully
at `2688/2688` jobs.  Both declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.

### 6r. L1 displacement-kernel owner bridge (landed 2026-08-27)

`Dev/C1CC20DisplacementKernel.lean` fixes the exact orientation needed to
connect the paper's two-variable kernel to the L2b weight:

```text
displacementKernel a (x, y) = a(y - x)

applyKernel(displacementKernel a, f)(x)
  = integral_v a(v) * f(x + v).
```

The proof is the translation `y = v + x`, using the Bochner integral's
`integral_add_right_eq_self` invariance.  The profile orientation is therefore
the same as `corrInnerSlice eta xi v = integral_x eta(x) * xi(x+v)` and the
same `a(v)` that `abs_corrWeightedFold_le` controls.

The leaf also proves, by definition rather than an analytic approximation,
that `endpointWindowKernelComplex` is `displacementKernel` of
`endpointDisplacementProfile`, and `endpointKernelOnSquare` is the matching
square-window indicator.  This is the owner-preserving handoff from the
equation-(104) formula layer to the equation-(121) engine.

Native WSL2 ext4 audit evidence:
`lake build ConnesWeilRH.Dev.C1CC20DisplacementKernelAudit` completed
successfully at `2692/2692` jobs.  The four declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.

Boundary: this does NOT yet exchange a windowed double integral for the
correlation fold.  That Fubini/readback theorem must state and prove the
necessary integrability hypotheses; no implicit interchange is licensed by
this definition-level bridge.

### 6s. L1 Fubini/readback: bilinear displacement operator bound (landed 2026-08-27)

`Dev/C1CC20DisplacementReadback.lean` closes the interchange deliberately
left open in §6r.  Define the product integrand in displacement-first
coordinates by

```text
D(v, x) = a(v) * eta(x) * xi(x + v).
```

Given the explicit premise `Integrable (uncurry D) (volume.prod volume)`, the
leaf proves the two exact readbacks

```text
integral_v a(v) * corrInnerSlice(eta, xi, v)
  = integral_x integral_v D(v, x)

integral_x eta(x) * applyKernel(displacementKernel a, xi)(x)
  = integral_v a(v) * corrInnerSlice(eta, xi, v).
```

Consequently `norm_pairing_applyKernel_displacementKernel_le` applies the
landed equation-(121) engine and gives the scalar operator estimate

```text
|| integral_x eta(x) * A_a(x) ||
  <= ||eta||_2 * ||xi||_2 * ||a||_1.
```

This is the exact analytic bridge intended by Lemma 3.  It uses
`integral_integral_swap` only with the named product-integrability premise;
there is no unlicensed Fubini exchange.  The concrete next obligation is to
provide this premise and the L1 profile certificate for the actual windowed
kernel difference `K_I - T`, then promote the scalar bound to the target
operator-norm statement.

Native WSL2 ext4 audit evidence:
`lake build ConnesWeilRH.Dev.C1CC20DisplacementReadbackAudit` completed
successfully at `2693/2693` jobs.  The four declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.

### 6t. Product integrability: discharge the Fubini premise from L1 x L2 x L2 (landed 2026-08-27)

`Dev/C1CC20ProductIntegrability.lean` removes the explicit Fubini premise in
§6s for the raw translation-invariant displacement kernel.  For

```text
D(v, x) = a(v) * eta(x) * xi(x + v),
```

the new theorem `integrable_displacementCorrelationIntegrand` derives
`Integrable (Function.uncurry D) (volume.prod volume)` from an a.e.-strongly
measurable profile with `integrable ||a||`, plus `MemLp eta 2` and
`MemLp xi 2`.  It uses `integrable_prod_iff` in the displacement-first
coordinate order, Holder on each fixed slice, and `mass_shift_real` to make
the slice bound uniform in `v`:

```text
integral_x ||D(v, x)||
  <= (L2mass eta)^(1/2) * (L2mass xi)^(1/2) * ||a(v)||.
```

`aestronglyMeasurable_displacementCorrelationIntegrand` separately records
the product-space measurability proof, so the Fubini and domination evidence
remain independently inspectable.  The wrapper
`norm_pairing_applyKernel_displacementKernel_le_of_l1Weight` feeds the
automatic premise into §6s and leaves the equation-(121) scalar pairing bound
with only the natural L1/L2 assumptions.

Native WSL2 ext4 audit evidence: the joint explicit audit batch for this leaf
and §6u completed successfully at `3626/3626` jobs.  The three declarations
here audit to exactly `[propext, Classical.choice, Quot.sound]`, with zero
`sorryAx`.

Boundary: this proves product integrability for the raw displacement form.
It does not identify that raw form with a square-window `L2` operator; that
step still needs explicit zero-extension and support hypotheses for the
concrete `K_I - T` owner.

### 6u. Pairing bound to operator-norm gap: CC20 Lemma-second adapter (landed 2026-08-27)

`Dev/C1CC20PairingOperatorNorm.lean` records the Hilbert-space conversion
needed after the concrete operator representation is available:

```text
forall eta xi, ||<eta, A xi>|| <= B * ||eta|| * ||xi||
  -> ||A|| <= B.
```

`opNorm_le_of_norm_inner_le` proves this by testing the pairing estimate at
`eta = A xi`; the zero-output case is separated and the nonzero case cancels
`||A xi||`.  `cc20GapNorm_le_of_pairingBound` specializes the result to
`kf - T`, and `cc20NegativeForm_le_rankOne_of_pairingBound` immediately
feeds the resulting norm-gap premise into `C1CC20OperatorGap`'s existing
Lemma-second consumer.

Native WSL2 ext4 audit evidence: the joint explicit audit batch with §6t
completed successfully at `3626/3626` jobs.  The three declarations here audit
to exactly `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.

Boundary: no bounded operator on the `L2` quotient is constructed here, and
no numerical L1 enclosure for the concrete profile is supplied.  This is the
ready consumer between a future concrete `K_I - T` pairing theorem and the
already-landed CC20 endpoint-gap machinery.

### 6v. L2-kernel quotient lift: raw Hilbert--Schmidt control becomes a bounded operator (landed 2026-08-27)

`Dev/C1CC20KernelLpLift.lean` closes the representation gap that remained
open after §6t--§6u.  For every `MemLp k 2` kernel, it builds the actual
bounded operator on the a.e.-quotient:

```text
raw L2 kernel k
  -> applyKernelLpLinear k : Lp(C,2) ->L Lp(C,2)
  -> applyKernelLp k       : Lp(C,2) ->L Lp(C,2)
  -> ||applyKernelLp k|| <= ||k.toLp k||.
```

The construction proves output `MemLp` membership, preserves a.e. equality of
inputs, and proves additivity only on the a.e. set of L2 kernel rows, where
Holder supplies the two integrability premises required by `integral_add`.
It therefore does not mistake the Bochner integral's zero-on-nonintegrable
convention for a linearity theorem.  The real squared-mass identity then
converts the landed extended-real Hilbert--Schmidt estimate into the norm
bound used by `LinearMap.mkContinuous`.

This gives a direct typed consumer for the existing
`memLp_endpointKernelOnSquare_of_profileBound`: once a concrete endpoint
kernel has that certificate, `applyKernelLp` is the corresponding bounded
windowed L2 operator.  It also supplies the operator-side input needed by the
§6u CC20-gap adapter.

Native WSL2 ext4 audit evidence:
`lake build ConnesWeilRH.Dev.C1CC20KernelLpLiftAudit` completed successfully
at `2686/2686` jobs.  All nine declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.

Boundary: this is Hilbert--Schmidt boundedness of one L2 kernel.  It neither
identifies the raw displacement form with the windowed quotient operator nor
constructs the finite-rank `T` or a certified norm/L1 estimate for `K_I - T`.

### 6w. Square-window displacement action readback (landed 2026-08-27)

`Dev/C1CC20WindowedDisplacementReadback.lean` closes the exact missing
ownership bridge between the square-window CC20 kernel and the already-landed
translation form.  With `E_I f = 1_I * f`, it proves pointwise that

```text
applyKernel(windowedDisplacementKernel a I, f)
  = E_I (applyKernel(displacementKernel a, E_I f)).
```

Thus the two indicators in the square kernel have distinct, explicit jobs:
the first restricts and zero-extends the input, while the second restricts and
zero-extends the output.  The specialization
`applyKernel_endpointKernelOnSquare_eq_windowedTranslateFold` applies this
identity directly to the concrete CC20 endpoint profile and rewrites the
inner raw action into

```text
integral_v a(v) * E_I(f)(x + v).
```

The quotient theorem
`coeFn_applyKernelLp_endpointKernelOnSquare_eq_zeroExtend_ae` transports the
same identity to the representative of the already-constructed bounded
`Lp(C, 2)` operator.  Its conclusion is deliberately an a.e. equality: an
`Lp` value is an almost-everywhere equivalence class, and
`MemLp.coeFn_toLp` is the required bridge from its chosen representative to
the raw integral.

Boundary: the bare translation-invariant kernel is not asserted to be a
global `L2(R x R)` kernel.  The result therefore does not construct
`applyKernelLp` for the raw kernel, does not construct `T`, and does not
provide the certified L1/norm enclosure for `K_I - T`.  It gives the lawful
windowed owner relation needed before those later certificates can feed the
equation-(121) and operator-gap adapters.

Native WSL2 ext4 audit evidence:
`lake build ConnesWeilRH.Dev.C1CC20WindowedDisplacementReadbackAudit`
completed successfully at `2695/2695` jobs.  All seven declarations audit to
exactly `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.

### 6x. Square-window pairing readback: equation-(121) now consumes K_I (landed 2026-08-27)

`Dev/C1CC20WindowedPairingReadback.lean` carries the newly explicit window
ownership through the scalar pairing layer.  It first proves

```text
integral_x eta(x) * K_I(xi)(x)
  = integral_x E_I(eta)(x) * K(E_I(xi))(x),
```

then combines this with the existing displacement Fubini readback.  The exact
theorem `pairing_applyKernel_windowedDisplacementKernel_eq_weightedCorrFold`
keeps its product-integrability premise visible.  The wrapper
`norm_pairing_applyKernel_windowedDisplacementKernel_le_of_l1Weight` discharges
that premise from an L1 profile and the two zero-extended L2 factors, and the
endpoint specialization applies it directly to `endpointKernelOnSquare`.

```text
profile a in L1, eta and xi in L2
  -> |<eta, K_I xi>|
       <= ||E_I eta||_2 * ||E_I xi||_2 * integral |a(v)| dv.
```

This is the first equation-(121) estimate whose left side is the concrete
square-window endpoint owner.  It does not yet bound `K_I - T`: the finite-rank
approximant and certified difference profile remain absent.

Native WSL2 ext4 audit evidence:
`lake build ConnesWeilRH.Dev.C1CC20WindowedPairingReadbackAudit` completed
successfully at `2698/2698` jobs.  All five declarations audit to exactly
`[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.

### 6y. Scope-check of the finite-certificate route against Bombieri 2000 (landed 2026-08-27)

Source: E. Bombieri, "Remarks on Weil's quadratic functional in the theory of
prime numbers, I".  Primary artifact now on hand: the 53-page scan
`~/bombieri_weil_qf.pdf` (stays out of the repository; book page p = pdf index
p - 181).  Secondary: extracted text `~/blogs/bombieri.txt` (lossy on display
math -- see the sign erratum below).  Purpose: verify the Yoshida-scope
precedent and certify exact normalizations before any table transcription.
Verdict first, then evidence.

* GO for a finite-certificate GATE 1 attack, anchored twice.  (Intro, l.90:)
  Yoshida reduces positivity of the Weil functional on a fixed support
  `[-t, t]` to a finite calculation depending on t, and verifies that
  positivity at `t = (log 2)/2` -- exactly our ROOT half-width.  The
  reduction is unconditional.
* Section-7 normalizations, now CERTIFIED by visual read of book p.203 plus a
  numerical triangle closure (definition vs (7.1) vs the Lemma-10 form;
  worst deviation 8.9e-16 over a grid containing `t = log 2/2`, the diagonal
  `x = y`, `x = 0`, and off-window points; floats stay out of Lean):
  `K(x) = sin x / x`;
  `K*(x,y,t) = K(t(x-y))
     - (t/sinh t) (1/2+iy) K(t(i/2-y)) K(t(i/2+x))
     - (t/sinh t) (1/2-iy) K(t(i/2+y)) K(t(i/2-x))`;
  `(1/4+x^2) K*(x,y,t) = (1/4+y^2) K*(y,x,t)
     = (1/4+xy) K(t(x-y))
       - [cosh(t) cos(t(x-y)) - cos(t(x+y))] / (2 t sinh t)`   (7.1);
  `z_gamma = X_rho`, `w_gamma = (1/4+gamma^2) z_gamma`, `Lambda = 1/lambda`
  (7.2);
  `H(x,y,t) = 2t K*(x,y,t) / (1/4+y^2)`   (7.3);
  `w = Lambda H w` over Gamma, `D(Lambda;t) = det[I - Lambda H(Gamma;t)]`
  (7.4)/(7.5); Theorem 6: `D` is entire of order 1, finite exponential type,
  with `D = 1 + sum (-1)^n Delta_n Lambda^n / n!`.
  ERRATUM against the text layer: the sign inside (7.1)'s fraction is MINUS
  (`cosh cos(t(x-y)) - cos(t(x+y))`); the lossy extraction had suggested a
  plus.  An earlier draft of this section carried the wrong sign; corrected
  in place after the visual read.
* Section-6 coefficients `X_rho`, CERTIFIED by visual read of book p.202
  (2026-08-28).  `phi` is the characteristic function of `(1/M, M)` with
  `M = e^t`; the test functions are `f in W_0` of the form
  (6.1) `f(x) = sum_rho X_rho phi(x) x^{-rho} + X_0 phi(x)
         + X_1 phi(x) x^{-1}`  if `x in (M^{-1}, M)`,
  and `f(x) = 0` if `x not in (M^{-1}, M)`; the sum runs over ALL complex
  zeros `rho` of zeta, repeated according to their multiplicity `m(rho)`.
  The two end coefficients are fixed by `f(M) = f(1/M) = 0` (6.2):
  `X_0 = - sum_rho (M^{1-rho} - M^{rho-1})/(M - M^{-1}) X_rho`,
  `X_1 = - sum_rho (M^rho - M^{-rho})/(M - M^{-1}) X_rho`.
  The Mellin transform factors term by term (6.3):
  `f~(s) = sum_rho X_rho phi~(s-rho) + X_0 phi~(s) + X_1 phi~(s-1)`.
  By Lemma 7, for `f` to be a formal solution of the dual eigenvalue
  problem it is SUFFICIENT (footnote 5: only sufficient -- the expansion
  (6.1) may lack uniqueness) that `X_rho = f~(rho)/(lambda rho (1-rho))`;
  in view of (6.3) this yields the eigenvalue equation (6.4):
  `lambda rho (1-rho) X_rho =
     sum_{rho'} [ phi~(rho-rho')
       - (M^{1-rho'} - M^{rho'-1})/(M - M^{-1}) phi~(rho)
       - (M^{rho'} - M^{-rho'})/(M - M^{-1}) phi~(rho-1) ] X_{rho'}`.
  CLARIFICATION for (7.2)/(7.4) inherited from the same read: on book
  p.203 `Lambda = 1/lambda` is a SCALAR -- (7.4) is
  `w = Lambda * (H(Gamma;t) w)` with the scalar multiple of the vector,
  not a diagonal matrix acting on the left; the landed
  `bombieriEigenvec_iff` states exactly this shape.
* Section-8 Lemma-10 chain, CERTIFIED by visual read of book pp.209-212
  (2026-08-28).  Lemma 9: `F in V°`, `F not identically 0`, satisfying the
  eigenvalue equation (8.3) `lambda (1/4 + Delta) F = L[F]` on `(-t, t)`
  forces `lambda` REAL (proof: `((1/4+Delta)F, F) = 1/4 int|F|^2 +
  int|F'|^2 > 0` by (8.2), and `(L[F], F)` is real by `Gamma = -conj
  Gamma` plus Fubini).  Corollary (8.4): the resolvent
  `D_N(Lambda,t) = det[I - Lambda H(Gamma_N;t)]` has only REAL roots.
  Lemma 10 (full statement): `H(Gamma;t)` has eigenvalue 0 iff some
  `gamma in Gamma` has multiplicity > 1, in which case the multiplicity of
  0 is `sum'[m(gamma) - 1]` over distinct gamma; and if every gamma is
  real, ALL eigenvalues are non-negative.  Proof chain (8.5)-(8.15):
  `Z(u) = sum_gamma e^{-i gamma u} z_gamma` (8.5) reduces the system;
  multiplying (8.6) by `(1/4+gamma^2) conj(z_gamma)` and summing gives
  (8.10); integration by parts turns it into (8.11)
  `lambda sum w conj(w) = 1/4 int|Z|^2 + int|Z'|^2 - C/(2S)(|Z(t)|^2 +
  |Z(-t)|^2) + 1/S [conj Z(t) Z(-t) ...]` with `C = e^t + e^{-t}`,
  `S = e^t - e^{-t}`; the even/odd decomposition
  `Z^+- (u) = [Z(u) +- Z(-u)]/2` recombines the boundary correction into
  `tanh(t/2) |Z^+(t)|^2 + coth(t/2) |Z^-(t)|^2`; the Wirtinger-type
  inequality (8.13) `(e^{t/2} -+ e^{-t/2})/(e^{t/2} +- e^{-t/2})
  |Z^-(t)|^2 <= 1/4 int|Z^-|^2 + int|(Z^-)'|^2` holds with equality iff
  `Z^-(u) = Z^-(t) (e^{u/2} -+ e^{-u/2})/(e^{t/2} +- e^{-t/2})` (proof:
  integration by parts on `F^+- = Z^+- - Z^+-(t)(e^{u/2} -+
  e^{-u/2})/(e^{t/2} +- e^{-t/2})`); assembling gives (8.14)
  `lambda sum w conj(w) = 1/4 int|F|^2 + int|F'|^2 >= 0` with (8.15)
  `F(u) = Z(u) - A e^{u/2} - B e^{-u/2}`, `F(+-t) = 0`; `lambda = 0` then
  forces `F` to vanish identically, and linear independence of
  `e^{u/2}, e^{-u/2}, e^{-i gamma u}` on finite intervals (Gamma finite)
  forces all `z_gamma = 0`, a contradiction.
  ERRATUM 2 against the printed page: the p.211 recombination bracket is
  the REAL-symmetric combination `a conj(b) + conj(a) b` (twice the real
  part of `a conj b`), NOT the printed anti-symmetric-looking difference
  -- with the printed minus the identity fails already at `a = b = 1`
  (LHS `cosh t / sinh t`, RHS `tanh(t/2)`), while the symmetric bracket
  closes it on generic complex probes (and the Lean proof needs nothing
  beyond `Real.exp_neg` and `ring`).
  FORMALIZATION STATUS: the pure-algebra core of this chain is LANDED
  (see section 7: the even/odd boundary recombination identity and its
  nonnegativity for `t > 0`); the analytic steps ((8.2), (8.13), (8.14)
  with integrals and integration by parts) stay open and are the natural
  next slice if the detector route is pursued -- as a DETECTOR only,
  never an unconditional GATE 1.
* Lemma-10 identity COMPLETED (display in its proof, book p.210, same
  triangle-verified status):
  `2t K*(x,y,t) = 2 sin(t(x-y))/(x-y)
     - [e^{(1/2-iy)t} - e^{-(1/2-iy)t}]/(e^t - e^{-t})
       * [e^{(1/2+ix)t} - e^{-(1/2+ix)t}]/(1/2+ix)
     - [e^{(1/2+iy)t} - e^{-(1/2+iy)t}]/(e^t - e^{-t})
       * [e^{(1/2-ix)t} - e^{-(1/2-ix)t}]/(1/2-ix)`.
  Entries are elementary (`sinc`, `cosh`, `cos`, complex exponentials) with
  NO digamma.  Bombieri's section-7 system is therefore the accessible
  primary-source entry-formula set for the finite-certificate lane, with
  `scripts/yoshida_intervals/` kept as the verifying engine; Yoshida's own
  digamma tables remain unconfirmed behind the access wall.
* Sign-count framework recorded: Theorem 8 states `#negative eigenvalues of
  H(Gamma;t) = #distinct complex-conjugate pairs in Gamma`; Lemma 10 adds
  that all-real Gamma forces a nonnegative spectrum.  CAUTION: both are
  conditional on all-real ordinates (RH-equivalent input); they may feed
  detector/coverage arguments only, never the unconditional GATE 1 sign.
* Bombieri Theorem 12 is NOT a formalizable producer here.  Its displayed
  optimization gives `T[G] >= [log K - O(1) - 4(a+2/K) a K^2 log K] ||F||^2`
  with `K = (1/a)(1+log(1/a))^-1`, which evaluates to `-1.29 - O(1)` at
  `a = log 2 / 2` (out-of-tree float check only; nothing transported into
  Lean).  Its structural value stands: the prime sum vanishes because
  `supp(F * F(-.))` misses every `+- log n` -- the same mechanism as our ROOT
  ledger -- and the explicit formula's last two terms are literally our
  `archimedeanTerm`.
* Section 13 fake-zero experiments (unique negative eigenvalue tending to 0,
  fictitious zero off the critical line, N up to 160) independently
  anticipate our strict-detector design.

Decision consequence: brick 2 proceeds as planned.  Inside the
finite-certificate lane, transcribe the certified elementary system above;
the CC20 gamma lane stays the fallback consumer behind the already-landed
adapters.  Yoshida 1992 remains paywalled; the scope precedent above is
sufficient for the route decision.

## 7. Session boundary

* Translation invariance layer: LANDED, axiom-clean
  (`C1YoshidaTranslationProbe` green, 3505 jobs, 0 sorryAx).
* Root-support ledger + endpoint interface: LANDED, axiom-clean
  (`C1HealthyYoshidaDetectorProbe` green, 3605 jobs, 0 sorryAx; all five new
  declarations `[propext, Classical.choice, Quot.sound]`).
* Four-node interpolator root support: LANDED, axiom-clean
  (`exists_healthyMinimalLaplaceRealizes_rootSupport_logTwoHalf`).  The
  constructed test lies in `Icc(-log 2 / 2, log 2 / 2)` and its prime-free
  square theorem is now a corollary of that stronger statement.  This gives
  triple vanishing and nonzero detection only, not the strict detector sign.
* CC20 log-coordinate readback + endpoint certificate consumer: LANDED,
  axiom-clean (`C1CC20ArchimedeanReadbackProbe` green, 3606 jobs, 0 sorryAx).
* Endpoint/detector incompatibility guard: LANDED, axiom-clean.  An endpoint
  certificate on a root-supported triple-vanishing test forces
  `archimedeanTerm(g square) <= 0` and `qw g >= 0`, while strict healthy
  detector data on the same test forces `qw g < 0`.  The capstone
  `sourceRH_of_rootSupportedHealthyDetectorData_and_endpointCertificates`
  confirms that supplying both universally is already an RH proof; the
  current four-node interpolation does not supply the strict-sign premise.
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
  green).
* Complex Hilbert-space Lemma `first` and the genuine spectral-decomposition
  adapter: LANDED, axiom-clean.  The direct Lemma `second` endpoint now consumes
  `T = lambdaMax |phi><phi| + R`, complement invariance, the residual Rayleigh
  bound, and `||kf_I - T|| <= epsilon1`; it no longer consumes a pointwise
  `hspectral` shadow.  The concrete operators and exact numerical certificates
  remain caller premises.
* Translate-invariance pack for the L2 slice brick (`memLp_shift`,
  `lintegral_enorm_sq_shift`, `ltTop_of_memLp`): LANDED, axiom-clean
  (2686 jobs, 0 sorryAx); `abs_corrInnerSlice_le`'s shift slot is now a
  one-line corollary for every MemLp consumer.
* Uniform displacement bound (`integral_shift`, `mass_shift_real`,
  `abs_corrInnerSlice_uniform`): LANDED, axiom-clean (2687 jobs,
  0 sorryAx); the eq-(121) slice constant no longer depends on the
  displacement parameter.
* L1-weighted correlation fold (`aestronglyMeasurable_corrInnerSlice`,
  `abs_corrWeightedFold_le`): LANDED, axiom-clean (2688 jobs,
  0 sorryAx); this is the generic equation-(121) engine, while the concrete
  `K_I - T` L1 certificate remains open.
* Displacement-kernel owner bridge (`displacementKernel`,
  `applyKernel_displacementKernel_eq_translateFold`): LANDED, axiom-clean
  (2692 jobs, 0 sorryAx); it fixes the equation-(104) to equation-(121)
  orientation, while the windowed Fubini/readback layer remains open.
* Displacement Fubini/readback (`pairing_applyKernel_displacementKernel_eq_weightedCorrFold`,
  `norm_pairing_applyKernel_displacementKernel_le`): LANDED, axiom-clean
  (2693 jobs, 0 sorryAx); product integrability is an explicit caller premise
  and the concrete `K_I - T` L1/operator-norm enclosure remains open.
* Product-integrability discharge (`integrable_displacementCorrelationIntegrand`,
  `norm_pairing_applyKernel_displacementKernel_le_of_l1Weight`): LANDED,
  axiom-clean (joint audit 3626 jobs, 0 sorryAx); the raw equation-(121) Fubini premise
  now follows from L1 x L2 x L2, while square-window quotient ownership remains
  an explicit separate obligation.
* Pairing-to-operator-norm adapter (`opNorm_le_of_norm_inner_le`,
  `cc20NegativeForm_le_rankOne_of_pairingBound`): LANDED, axiom-clean
  (joint audit 3626 jobs, 0 sorryAx); the concrete `K_I - T` operator and certified L1
  profile enclosure are still missing.
* L2-kernel quotient lift (`applyKernelLp`, `opNorm_applyKernelLp_le`):
  LANDED, axiom-clean (2686 jobs, 0 sorryAx); any certified windowed L2 kernel
  now yields an actual bounded `Lp ℂ 2` operator, but the concrete difference
  kernel `K_I - T` and its numerical enclosure remain open.
* Square-window displacement action readback (`cc20WindowZeroExtend`,
  `applyKernel_endpointKernelOnSquare_eq_windowedTranslateFold`,
  `coeFn_applyKernelLp_endpointKernelOnSquare_eq_zeroExtend_ae`): LANDED,
  axiom-clean (2695 jobs, 0 sorryAx).  It proves the concrete owner is
  `1_I K 1_I` at both raw and a.e.-quotient levels, without asserting that the
  bare whole-plane translation kernel is itself an L2 operator.
* Square-window equation-(121) pairing (`pairing_applyKernel_windowedDisplacementKernel_eq_weightedCorrFold`,
  `norm_pairing_applyKernel_endpointKernelOnSquare_le_of_l1Weight`): LANDED,
  axiom-clean (2698 jobs, 0 sorryAx).  The concrete endpoint owner now has an
  L1 x L2 x L2 scalar bound with both factors explicitly zero-extended; the
  finite-rank difference profile for `K_I - T` remains open.
* Equation-(119) rank-one approximant (`C1CC20FiniteRankApproximation`):
  LANDED, axiom-clean (2700 jobs, 0 sorryAx); eq-(120) discharged by Fubini.
  Strict lambda data (11-term chi formula, remainder, certified absolute-value
  integration) and any `C(R)` producer remain open.
* Certificate honesty guards: LANDED, axiom-clean
  (`C1CC20NegativeIndex` finrank <= 1 for strictly negative subspaces under a
  one-functional kernel, specialized to the Riesz bad direction;
  `C1CC20EndpointSpectralOwnerGuard` blocks positivity smuggling through the
  spectral owner; `C1CC20EndpointAnalyticModeData` supplies the minimal
  genuine derivative owner with uniqueness).
* Finite-certificate scope-check against Bombieri 2000: LANDED as section 6y
  -- GO verdict at `t = log 2 / 2`; K*, (7.1)-(7.5), and the completed
  Lemma-10 Gram identity certified by visual read plus numerical triangle
  closure (worst 8.9e-16); a sign erratum in (7.1) from the lossy text layer
  was corrected in place; Theorem 12 excluded as a producer by an
  out-of-tree constant check.
* Bombieri section-7 readback slice one (`C1BombieriSection7Readback`):
  LANDED, axiom-clean (1507 jobs, 0 sorryAx) -- sinc kernel `bombieriK`,
  corrected kernel `bombieriKstar` verbatim from book p.203, and the master
  real/imaginary split lemma `bombieriK_re_add_mulI`.  The (7.1) closed
  form, the Lemma-10 Gram identity, and the ownership chain (7.2)-(7.5)
  remain open slices.
* Engine elementary-bracket module (commit `13a4105`): `scripts/yoshida_intervals/
  yoshida_interval_gen.py` gains `elementary_bracket(kind, theta_iv)` --
  rigorous sin/cos/sinh/cosh brackets on whole INTERVAL arguments from the
  defining Taylor series in exact Fraction arithmetic plus an in-file
  Lagrange remainder bound (M = 1 or exp(sup) via a proven rational exp
  upper bound; the geometric-tail ratio is gated on N + 1 > a after the
  self-tests caught the negative-ratio fake convergence).  NO stored
  digits, unlike `psi_bracket`.  Self-tests T1-T11 green stdlib-only and
  with mpmath (a rational mpmath argument must be built from integer
  numerator/denominator, not an int/int float quotient).  `Interval` grew
  value `__eq__`; README public surface updated.
* Bombieri (7.1) diagonal slice (`C1BombieriSection7DiagSymmetry`, commits
  `2688aad` + `01a7591`, 1508 jobs, 0 sorryAx): on the diagonal x = y = r
  the two rank-correction terms collapse (coefficients (1/2 +- ir) add to
  one, products coincide), the kernel pair `K(-u + vi) K(u + vi)` collapses
  to the real `(sin^2 u + sinh^2 v) / (u^2 + v^2)` via the master split and
  the two Pythagorean identities, giving the book identity
  `K*(r,r;t) = 1 - (cosh t - cos(2tr)) / (2 t sinh t (1/4 + r^2))`
  (`bombieriKstar_diagonalClosedForm`); plus `bombieriK_genPair`, the same
  product with INDEPENDENT real parts as an explicit re/im pair -- the
  off-diagonal building block.  Derivation note for the remaining general
  (7.1) slice: with AB and CD the two correction products
  (Re shared, Im opposite), `(1/2+iy)AB + (1/2-iy)CD = (u - 2 y v)` exactly
  (imaginary parts cancel), so the general law reduces to the real identity
  `(1/4+x^2)(t/sinh t)(u - 2 y v) = x(x-y) K(t(x-y))
     + [cosh t cos(t(x-y)) - cos(t(x+y))] / (2 t sinh t)`
  with `u`, `v` the shared real / opposite imaginary parts of the pair
  products; product-to-sum angle identities (cos_sub/cos_add) are the
  expected core haves.  The Lemma-10 Gram identity and (7.2)-(7.5)
  ownership chain remain open slices.
* Bombieri (7.1) general slice (`C1BombieriSection7Symmetry`, commit
  `ce15ee3`, 1509 jobs, 0 sorryAx): the full off-diagonal law
  `(1/4+x^2) K*(x,y;t) = (1/4+xy) K(t(x-y))
     - [cosh t cos(t(x-y)) - cos(t(x+y))] / (2 t sinh t)` for `t != 0`,
  `x != y` (`bombieriKstar_symmetryLaw`); its scalar engine
  `bombieri7_core` (the law as an explicit real identity in the six
  frozen atoms, after `bombieriK_genPair` consumes both correction
  products and the fold `(1/2+iy)AB + (1/2-iy)CD = (u - 2 y v)` kills
  the imaginary parts); `wCollapse` (the cosine pair equals twice
  `sin(ty) sin(tx) cosh^2(t/2) + cos(ty) cos(tx) sinh^2(t/2)` via
  cos_sub/cos_add and `cosh^2 = sinh^2 + 1`); and the punchline
  corollary `bombieriKstar_symmetric`
  (`(1/4+x^2) K*(x,y;t) = (1/4+y^2) K*(y,x;t)`, sinc odd + cosine pair
  even under `x <-> y`).  Proof mechanics worth recording: inside a
  complex ambient `binop%` re-elaborates the definition's real scalars
  as complex numeral divisions (`1/4` -> `(1:Complex)/(4:Complex)`), a
  complex power of a cast (`x^2` -> `↑x ^ 2`), a cast-level complex
  division (`t / Real.sinh t` -> `↑t / ↑(Real.sinh t)`), and an
  atom-split leading argument (`t * (x-y)` -> `↑t * (↑x - ↑y)`); a
  normalization block right after `unfold` pulls each back into a
  single `Complex.ofReal` block, without which `div_re`/`div_im`
  explode the projections into unmatchable `Complex.re 1` /
  `Complex.normSq` fragments.  The six trig atoms are frozen with
  `set` before `field_simp` (which otherwise reorders products inside
  `Real.sin`/`Real.cosh` arguments and splits each atom in two).  The
  Lemma-10 Gram identity and (7.2)-(7.5) ownership chain remain open
  slices.
* Bombieri Lemma-10 Gram identity (`C1BombieriSection7Lemma10`): LANDED,
  axiom-clean (leaf 1509 jobs, audit 1510 jobs, 0 sorryAx) -- the book
  p.210 display verbatim (`bombieriKstar_lemma10`, `t != 0`, `x != y`):
  `2t K*(x,y;t) = 2 sin(t(x-y))/(x-y) - [e^{(1/2-iy)t} - e^{-(1/2-iy)t}]
  /(e^t - e^{-t}) * [e^{(1/2+ix)t} - e^{-(1/2+ix)t}]/(1/2+ix) - (y-term
  mirrored)`, plus the reusable quarter-turn kernel identity
  `bombieriK_I_mul` (`K(I*u) = sinh u / u`) and the `Complex.sinh`
  defining-equation bridges `expBracket` / `sinhBracket`.  Proof mechanics
  worth recording: each of the four correction arguments is a quarter-turn
  `t(i/2 -+ c) = I * ((1/2 +- i c) t)`, so the kernel identity turns them
  into `sinh` quotients; the matching coefficient then cancels its `u` and
  every `t` disappears.  The correction brackets are discharged as
  standalone `have`s whose compound denominators are FIRST frozen with
  `set` as opaque atoms (nonvanishing facts transported through the
  defining equations) -- `field_simp`'s inner `ring_nf` otherwise
  distributes the products inside the inverse arguments (leaving
  `Complex.I ^ 2` unnormalized) and orphans the factored facts, while
  bare `ring` treats `x ^ (-1)` as an atom so the `u`-denominators can
  never cancel the display's coefficient denominator.  The (7.2)-(7.5)
  ownership chain remains the next slice.
* Bombieri (7.3) normalized kernel (`C1BombieriSection7H`): LANDED,
  axiom-clean (leaf 1510 jobs, audit 1511 jobs, 0 sorryAx) --
  `bombieriH` (`H(x,y;t) = 2 t K*(x,y;t)/(1/4 + y^2)`, the (7.3)
  definition), the (7.3) readback `bombieriH_mul_weight_eq`, and the
  flagship `bombieriH_symmetric` (`H(x,y;t) = H(y,x;t)` for `t != 0`,
  `x != y`): multiplying the (7.1) symmetry law by `2 t` and reading
  both sides through the (7.3) readbacks shows the normalization
  symmetrizes the kernel, which is the entrance for the
  symmetric-matrix eigenvalue sign count of (7.4).  Mechanics: the
  symmetry law's `binop%` weight form (`1/4 + (x:Complex) ^ 2`) is
  restated into single real casts via `Complex.ofReal_pow` (backward)
  plus `push_cast`; `mul_assoc` is stated LEFT-associated
  (`(a*b)*c = a*(b*c)`), so flattening a nested product needs the
  backward rewrite; `mul_left_comm` rewrites must be explicitly
  instantiated or the second call reverts the first.  The (7.4)/(7.5)
  matrix layer over a finite zero set and the `z_gamma = X_rho`
  transcription remain open (`X_rho`'s definition needs a fresh book
  p.204 read; the scan stays out of the repository).
* Bombieri (7.2)/(7.4)/(7.5) finite-Gamma matrix layer
  (`C1BombieriSection7Gamma`): LANDED, axiom-clean (leaf + audit
  `1706 jobs`, 0 sorryAx).  Gamma is modeled as `gamma : Fin n -> Real`
  (repetitions carry the multiplicity `m(gamma)`): `bombieriWOfZ` is the
  (7.2) coordinate change `w_gamma = (1/4 + gamma^2) z_gamma`
  (`noncomputable` -- the real division `1/4` pulls in
  `Real.instDivInvMonoid`); `bombieriHMatrix` is (7.4)'s `H(Gamma;t)`
  with `bombieriHMatrix_transpose` proving it symmetric (flagship
  `bombieriH_symmetric` off the diagonal, `by_cases` trivial on it);
  `bombieriHMatrix_mulVec_weight` is the ownership identity -- the
  H-matrix acting on the weighted vector equals `2 t` times the raw
  `K*`-matrix acting on `z`, per entry through the private `entry_eq`
  -- which is why (7.4) is equivalent to the original system (6.4);
  `bombieriEigenvec_iff` is the (7.4) readback in scalar-Lambda shape:
  `w = Lam * (H(Gamma;t) *v w)` componentwise (for every index `i`,
  `w i = Lam * (H(Gamma;t) *v w) i`) iff `w = Lam smul (H(Gamma;t) *v w)`
  as vectors; `bombieriD` is the
  (7.5) resolvent determinant `det[I - Lam smul H(Gamma;t)]` with
  `bombieriD_zero : D(0,t) = 1` (Theorem 6's constant term).  The
  section-6 `X_rho` definition (6.1)-(6.4) is transcribed into section
  6y from the book p.202 visual read; in the finite-certificate lane
  `z` enters as explicit data indexed by Gamma, so no function-space
  infrastructure is needed.  Mechanics: the `ᵀ` transpose notation is
  namespace-scoped in v4.30 -- write `Matrix.transpose`; v4.30 has root
  `dotProduct`, no `Matrix.dotProduct`, but `M.mulVec v i = sum j,
  M i j * v j` holds by `rfl`, so a private elementwise helper replaces
  unfolding; a hypothesis `h : w = ... w` must be transported via
  `congrArg (fun v => v i) h`, NOT `rw [h]` (`rw` would also rewrite
  the `w` inside `mulVec w`); `simp only` on the mulVec sums keeps the
  summands LEFT-associated (`(2t) bullet K* bullet z`), so per-entry
  helpers must be stated in the same association.
* Lemma-10 detector skeleton (`C1BombieriSection8Boundary`): LANDED,
  axiom-clean (leaf + audit `1707 jobs`, 0 sorryAx).  From the book
  pp.209-212 visual read (recorded in section 6y): the even/odd boundary
  recombination `bombieriEvenOddBoundary` -- the raw two-point boundary
  correction `C/(2S)(a conj a + b conj b) - (a conj b + conj a b)/S`
  equals the `tanh(t/2)`-weighted square of the even part plus the
  `coth(t/2)`-weighted square of the odd part -- and
  `bombieriEvenOddBoundary_nonneg` (`t > 0` makes both weights strictly
  positive, `Complex.normSq` squares).  v4.30 mechanics: `Complex.conj`
  and `Complex.abs` NO LONGER EXIST -- use `star`/`(starRingEnd ℂ)`
  (statement and proof in ONE syntactic form; `map_add`/`map_sub` of
  `starRingEnd ℂ` for conj of sums) and `Complex.normSq` (with
  `Complex.normSq_nonneg`, `Complex.mul_conj` for the bridge); `set`
  NORMALIZES later atom definitions against earlier ones (`dB` came out
  as `2 * dC`), so transport nonzero facts through the shown equation;
  `field_simp` on frozen atoms may leave the atoms intact -- then
  `rw [hdA, ..., hdE]` unfolds them, `push_cast` expands the ofReal
  sums to a single cast atom, and a SECOND `field_simp` with
  `Complex.ofReal_ne_zero.mpr hX` clears residual inverse powers before
  `ring` closes.
* Wirtinger (8.13) slice 7a, the IBP core (`C1BombieriSection8Wirtinger`):
  LANDED, axiom-clean (leaf `2654 jobs`, audit `2655 jobs`, 0 sorryAx).
  The even envelope `phiEven u = exp (u/2) + exp (-u/2)` with its
  derivative (`hasDerivAt_phiEven`, purely in `R`) and the envelope ODE
  `phi'' = (1/4) phi` (`phiEven_ode`); derivative transport through the
  `Real -> Complex` cast (`hasDerivAt_cast`, via
  `Complex.ofRealCLM.hasDerivAt` + `HasDerivAt.scomp` + `congr_deriv`);
  the product-rule derivative `hasDerivAt_g_mul_phiEven'` of
  `g * phi'`; and the IBP core identity `ibpCoreEven`:
  `integral over [-t,t] of (g' phi' + g (1/4) phi) = [g phi']` at the two
  endpoints, proved with `intervalIntegral.integral_eq_sub_of_hasDerivAt`
  (product rule + fundamental theorem; no abstract IBP).
  Mechanics worth recording (v4.30): a compound cast
  `((1/2 * ...) : Complex)` with a SINGLE type ascription is elaborated by
  binop% in the COMPLEX ambient and splits into
  `up (1/2) * (up e1 - up e2)`, which is not definitionally equal to the
  single cast `up (1/2 * ...)` produced by a transport lemma -- write the
  inner `: Real` ascription (or explicit `Complex.ofReal`) to force the
  single-cast form everywhere; a NEGATIVE literal passed where the
  implicit type is not yet known falls through to `Z` (DivInvMonoid Z
  failure) -- ascribe `(-2 : Real)`; `-x / 2` elaborates as `(-x) / 2`,
  NOT `x / (-2)` as produced by `div_const (-2)` -- bridge with
  `funext` + `neg_div`/`div_neg`; specialization at `x := -t` leaves
  `- -t` unreduced in exponentials -- `rw [neg_neg] at` the FTA result
  before `exact`; `HasDerivAt.comp`'s `h2 o h` output unifies with a
  lambda goal only when asserted through an explicit-type `have`
  (elaboration-order workaround); `simpa only [id_eq]` on
  `HasDerivAt.const_mul` leaves `(c * 1)` -- add `mul_one`.  Remaining
  (8.13) steps open: envelope integral evaluation (`R = 2 sinh t`), the
  Q-shift identity `Q(g) = Q(F) + tanh(t/2)|g(t)|^2` with vanishing
  cross terms `X(F) = 0`, `Q(F) >= 0` through the real channel, and the
  odd-case mirror with `coth(t/2)`.  DETECTOR only; never an
  unconditional GATE 1.
* Wirtinger (8.13) slice 7b, envelope integral + X(F) = 0
  (`C1BombieriSection8WirtingerSlice2`): LANDED, axiom-clean (leaf + audit
  `2655`/`2656 jobs`, 0 sorryAx).  Pointwise square expansions
  `phiEven_sq` (`phi^2 = e^u + 2 + e^{-u}`) and `phiEvenDeriv_sq`
  (`phi'^2 = (1/4)(e^u - 2 + e^{-u})`); `ibpCoreEven_zero` (the IBP core
  vanishes on C^1 functions with zero endpoints -- the cross-term killer
  of the Q-shift identity); flagship `envelopeIntegralEven`: the envelope
  quadratic integral `(1/4) int phi^2 + int phi'^2` over `[-t, t]` equals
  `e^t - e^{-t}` (= `2 sinh t`), the `R` constant of
  `Q(g) = Q(F) + |c|^2 R` -- the `t`-terms of the two expansions cancel.
  Support: private real exponential integrals `integral_exp_real` /
  `integral_expNeg_real` via the fundamental theorem (Mathlib has NO
  `intervalIntegral.integral_exp`) and premise-free
  `integral_comp_neg` for the reflected exponential.
  Mechanics worth recording: the interval-integral NOTATION has a binder
  AMBIGUITY -- `(1/4) * int x in a..b, f x + int x in a..b, g x` parses
  with the SECOND integral SUCKED INTO the first integrand
  (`fun x => f x + int g`, so the first integral is of a real-valued
  integrand containing another integral); the plain display cannot show
  this -- PARENTHESIZE every integral that participates in an arithmetic
  expression: `((int ...) + (int ...))`.  Diagnostic that found it:
  `pp.explicit` on the rw-failure dump (the goal's first intervalIntegral
  node carried the second one inside its integrand lambda).  Also:
  `intervalIntegral.integral_congr` takes `Set.EqOn f g (uIcc a b)`.
  Remaining (8.13) steps open: the Q-shift assembly
  `Q(g) = Q(F) + tanh(t/2)|g(t)|^2` (consumes `ibpCoreEven_zero` +
  `envelopeIntegralEven` + conj-linearity of the interval integral),
  `Q(F) >= 0` through the real channel, the odd-case mirror with
  `coth(t/2)`, and the (8.14) assembly.  DETECTOR only.
* Wirtinger (8.13) slice 7c, the Q-shift identity
  (`C1BombieriSection8WirtingerSlice3`): LANDED, axiom-clean (leaf + audit
  `2656`/`2657 jobs`, 0 sorryAx).  `integral_star_interval` (conj passes
  through the interval integral: the root-level Bochner `integral_conj`
  applied to each `Ioc` piece behind a def-unfolding `show` bridge);
  `xIntegrand_conj` (the IBP-core integrand of `conj F` is `conj` of the
  integrand, since the envelope weights are real); `xIntegral_zero` /
  `xIntegral_conj_zero` (both cross integrals vanish at `F(±t) = 0` — no
  `HasDerivAt` through `conj` exists or is needed); `rIntegral` (the
  envelope quadratic density integrates to `e^t − e^{−t}` through the real
  channel); `qIntegrand_expansion` + flagship `qShiftEven`:
  `Q(F + c·φ₊) = Q(F) + c·conj(c)·(e^t − e^{−t})`.
  Mechanics worth recording (v4.30): `Complex.ofReal_mul`/`ofReal_add`
  are stated with the CAST on the LEFT (`↑(a*b) = ↑a * ↑b`) — merging a
  cast-product into a cast-of-product therefore needs `←` (backward), and
  splitting needs the forward direction; a probe written as
  `(↑a * ↑b : ℂ) = ↑(a*b) := Complex.ofReal_mul a b` compiles VACUOUSLY
  because binop% re-elaborates `↑a * ↑b` into `↑(a*b)`, making the expected
  type trivially reflexive — probes of cast-lemma orientation must pin the
  form so binop% cannot normalize it.  Second reappearance of the binop%
  ambient hazard: a `show … from by simp` whose cast argument contains
  real ARITHMETIC (`(1/2)*(exp − exp)`) gets lifted into the complex
  ambient (`Complex.exp`, complex numeral divisions) and can never match
  the goal's single-cast form — fix by proving a bare-variable helper
  (`star_ofReal (r : Real) : (starRingEnd ℂ) ↑r = ↑r`) and rewriting with
  explicit instantiations.  `rw [theorem-with-function-variables]` can
  fail to fire a higher-order pattern (`xIntegrand (fun y ↦ ?F y) …` even
  when the goal matches visibly) — the robust route is a funext'd
  lambda-equality `have` between fully instantiated lambdas (same trick as
  slice 7b's `hf`/`hg`).  `Continuous.intervalIntegrable h (-t) t` without
  an ascribed expected type leaves the measure as an unassigned
  metavariable (`IsLocallyFiniteMeasure ?m` stuck) — ascribe the full
  `IntervalIntegrable … volume …` type on every such `have`.  And
  `noncomputable` is needed on every def whose body contains a real
  numeral division (`1/4 : Real`), even when the codomain is `ℂ`.
  Remaining (8.13) steps open: `Q(F) ≥ 0` through the real channel
  (`Complex.mul_conj` + `integral_ofReal` + `integral_nonneg`), the
  odd-case mirror with `coth(t/2)`, and the (8.14) assembly.
  DETECTOR only.
* Wirtinger (8.13) slice 7d, the real channel
  (`C1BombieriSection8WirtingerSlice4`): LANDED, axiom-clean (leaf + audit
  `2658 jobs`, 0 sorryAx).  Since `ℂ` carries no order, `Q(F) ≥ 0` is
  stated as the pair `qF_real` (the Q-form integral equals the
  `Complex.ofReal` cast of `¼∫normSq F + ∫normSq F'`, via pointwise
  `Complex.mul_conj` + `integral_ofReal`) and `sqMass_nonneg` (the real
  expression is nonnegative for `t ≥ 0`, via
  `intervalIntegral.integral_nonneg` — whose signature needs the explicit
  `a ≤ b` first argument — plus `Complex.normSq_nonneg`).
  `Complex.continuous_normSq` exists under that name.  Supporting change:
  `qIntegrand` in the slice-3 leaf is now public.  Remaining (8.13)
  steps open: the even-case corollary `tanh(t/2)|Z⁺(t)|² ≤ Q(Z⁺)` (via
  `c := Z⁺(t)/φ₊(t)`, `F = Z⁺ − cφ₊`, φ₊ evenness, and the
  `(a²−b²)/(a+b)² = (a−b)/(a+b)` exp algebra), the odd-case mirror with
  `coth(t/2)`, and the (8.14) assembly.  DETECTOR only.
* Wirtinger (8.13) slice 7e, the even-case inequality
  (`C1BombieriSection8WirtingerSlice5`): LANDED, axiom-clean (leaf + audit
  `2659 jobs`, 0 sorryAx).  `phiEven_even` / `phiEven_ne_zero`;
  `tanhHalf_eq_ratio` (`(e^t − e^{−t})/(e^{t/2} + e^{−t/2})² = tanh(t/2)`,
  the (8.13) weight — v4.30 defines `Real.tanh x` as
  `(Complex.tanh x).re`, so `unfold` DESTROYS the goal; the bridge is
  `Real.tanh_eq_sinh_div_cosh`, and the old import
  `Mathlib.Analysis.SpecialFunctions.Trigonometric` is GONE — hyperbolic
  functions live in `Mathlib.Analysis.Complex.Trigonometric`);
  flagship `wirtingerEven`: for even `Z` (`t ≥ 0`), `Q(Z)` is the cast of
  a real expression dominating `normSq(Z t)·(e^t − e^{−t})/φ₊(t)²` with
  explicit slack `S ≥ 0` — the even case of (8.13) in the real-channel
  shape.  Mechanism: subtract `c := Z(t)/φ₊(t)` times the envelope; the
  remainder is C¹, even, and vanishes at both endpoints, so `qShiftEven`
  applies and `qF_real` + `sqMass_nonneg` push `Q(F)` through the real
  channel; `field_simp` leaves a `Z t * (1 − 1) = 0` residue — close with
  `ring`.  Remaining (8.13) steps open: the odd-case mirror with the
  `coth(t/2)` weight (`φ₋ = e^{u/2} − e^{−u/2}`, odd, `φ₋(t) ≠ 0` for
  `t ≠ 0`), and the (8.14) assembly over the eigenvalue equation.
  DETECTOR only.
* Wirtinger (8.13) slice 7f, the odd envelope core
  (`C1BombieriSection8WirtingerSlice6`): LANDED, axiom-clean (leaf + audit
  `2658`/`2659 jobs`, 0 sorryAx).  The mirror of slices 7a/7b for the odd
  envelope `phiOdd u = e^{u/2} − e^{−u/2}` with derivative
  `½(e^{u/2} + e^{−u/2})`: `hasDerivAt_phiOdd`, the ODE `phiOdd_ode`
  (`(φ₋')' = ¼φ₋`, derivative target reusing the raw lambda so `ring`
  needs no def unfolding), square expansions `phiOdd_sq`
  (`φ₋² = e^u − 2 + e^{−u}`) and `phiOddDeriv_sq`
  (`φ₋'² = ¼(e^u + 2 + e^{−u})`), the product-rule transport
  `hasDerivAt_g_mul_phiOdd'`, the IBP core `ibpCoreOdd` /
  `ibpCoreOdd_zero`, and flagship `envelopeIntegralOdd`:
  `¼∫φ₋² + ∫φ₋'² = e^t − e^{−t}` — the SAME constant `R` as the even
  case, the `±2` terms of the two expansions canceling through the
  interval integrals.  The Q-form integrand is parity-independent, so
  the real channel of slice 7d is reused verbatim; only the IBP weights
  are mirrored.  Cosmetic note: the log carries an INFO-level
  `ring`/`ring_nf` suggestion block with zero `error:` lines — the
  acceptance signal stays the log text plus the axiom audit.
  Remaining (8.13) steps open: the odd Q-shift + odd-case inequality,
  and the (8.14) assembly.  DETECTOR only.
* Wirtinger (8.13) slice 7g, the odd-case inequality
  (`C1BombieriSection8WirtingerSlice7`): LANDED, axiom-clean (leaf + audit
  `2660 jobs`, 0 sorryAx).  Completes the even/odd pair behind (8.13):
  `xIntegrandOdd`/`rIntegralOdd`/`xIntegralOdd_zero`/
  `xIntegralOdd_conj_zero` (the odd IBP cross integrals, vanishing at
  zero endpoints through the integral-level conj transport of slice 7c),
  `qIntegrandOdd_expansion` + flagship `qShiftOdd`
  (`Q(F + c·φ₋) = Q(F) + c·conj(c)·(e^t − e^{−t})` — the same constant
  `R` as the even case), `phiOdd_odd`/`phiOdd_pos` (`t > 0` makes
  `φ₋(t) > 0`), the weight identification
  `coshHalf_div_sinhHalf_eq_ratio`
  (`(e^t − e^{−t})/(e^{t/2} − e^{−t/2})² = cosh(t/2)/sinh(t/2)` — the
  `coth(t/2)` of the book's (8.13); Mathlib v4.30 has NO `Real.coth`
  anywhere, so the weight is stated through `cosh`/`sinh`), and flagship
  `wirtingerOdd`: for odd `Z` with `t > 0`, `Q(Z)` is the cast of a real
  expression dominating `normSq(Z t)·(e^t − e^{−t})/φ₋(t)²` with slack
  `S ≥ 0`.  Odd-mirror mechanics worth recording (both NEW vs the even
  case): (1) the weight identity needs an explicit difference-of-squares
  factorization BEFORE `field_simp` — the residual otherwise carries
  `(a−b)²`-inverse and `(a−b)`-inverse as distinct `ring` atoms that
  never cancel (and `field_simp` alone then closes the goal, so the
  trailing `ring` must go); (2) in the odd-endpoint hypothesis the
  `rw [phiOdd_odd]` puts the negation INSIDE the cast
  (`Complex.ofReal (-phiOdd t)`) — `Complex.ofReal_neg` must pull it out
  before `field_simp`, since `ring` treats `↑(−φ₋t)` and `↑(φ₋t)` as
  different atoms.  Remaining (8.13) steps open: the (8.14) assembly
  over the eigenvalue equation, then the Theorem-8 sign count.
  DETECTOR only.
* Wirtinger (8.14) slice 8a, the even/odd parity split
  (`C1BombieriSection8ParitySplit`): LANDED, axiom-clean (leaf + audit
  `2661 jobs` after the pairing fix, 0 sorryAx; commits `8f87a7d` +
  `617e707`).  `qSplit`: `Q(Z) = Q(Z⁺) + Q(Z⁻)` over the symmetric
  window at the `qIntegrand` integral level (values only — no
  differentiability enters), where `Z^± = (Z ± Z∘neg)/2`; the engine
  is `integral_symmetry_half` (`∫_{−t}^{t} f = ∫_0^t (f x + f (−x))`,
  via premise-free `integral_comp_neg` and the ROOT-NAMESPACE
  `neg_zero` — `Real.neg_zero` does NOT exist in v4.30) plus the
  parallelogram law through `Complex.normSq_add`/`normSq_sub` (whose
  `±2·Re(z·conj w)` cross terms cancel pairwise as ring atoms).
  Mechanics worth recording: `normSq_half` needs the numeral evaluated
  separately (`Complex.normSq 2` is an OfNat node; `normSq_ofReal`'s
  `↑?r` pattern cannot fire — `simp; norm_num` gives `normSq 2 = 4`);
  `unfold` does NOT beta-reduce (`simp only []` forces it); after
  `simp only []` with `u := −x` the substitution leaves `- -x` — a
  GLOBAL `rw [neg_neg]` first, then each ±x evaluation is a distinct
  atom and the 12 `mul_conj` + 8 `normSq_half` + 4 `normSq_add` +
  4 `normSq_sub` chain closes under `push_cast; ring`.
  PAIRING FIX (`617e707`): the first cut paired the even part with the
  even half-sum of `Zp`; swapped to the TRUE derivatives — the even
  part paired with the odd half-difference `(Zp − Zp∘neg)/2`, the odd
  part with the even half-sum `(Zp + Zp∘neg)/2`.  The parallelogram
  algebra is symmetric in the second-slot pairing, so both statements
  are true, but only the true-derivative pairing is consumed by the
  Wirtinger corollaries downstream.  DETECTOR only.
* Wirtinger (8.13) slice 9, the full inequality (`C1BombieriSection8WirtingerFull`):
  LANDED, axiom-clean (leaf + audit `2663 jobs`, 0 sorryAx; commit
  `3e769f6`).  Flagship `wirtingerFull`: for every C¹ `Z` with `t > 0`,
  `Q(Z) = ↑((e^t−e^{−t})/φ₊(t)²·|Z⁺(t)|² + (e^t−e^{−t})/φ₋(t)²·|Z⁻(t)|² + S)`
  with `S ≥ 0`, assembled from `qSplit` + `wirtingerEven` on `Z⁺` +
  `wirtingerOdd` on `Z⁻` (the split parts carry their TRUE derivatives:
  `d/du Z⁺ = (Zp − Zp∘neg)/2`, `d/du Z⁻ = (Zp + Zp∘neg)/2`, the exact
  pairing `qSplit` supplies); corollary `wirtingerFull_weights`
  identifies the weights as `tanh(t/2)` and `coth(t/2)` (stated
  through `cosh`/`sinh`) — the book's (8.13) verbatim.  Mechanics
  worth recording (v4.30): the outer function is ℂ-valued, so the
  reflection chain rule `d/du Z(−u) = −(Zp (−u))` goes through
  `HasDerivAt.scomp` — plain `HasDerivAt.comp` requires the outer
  function on the algebra `𝕜'` and does NOT apply; `scomp`'s
  derivative is the SMUL `h' • g₁'`, i.e. `(-1 : ℝ) • Zp (−u)`,
  bridged to the negation by `neg_one_smul`; `HasDerivAt.div_const`'s
  constant lives in the TARGET space (`d : 𝕜'`, so `(2 : ℂ)`);
  `rw`-instantiated theorem right-hand sides arrive ALREADY
  beta-reduced (`simp only []` then errors "made no progress" — drop
  it); the v4.30 `linter.style.show` flags `show`-as-defeq-change as
  an ERROR (use `simp only []` to force beta instead); and the import
  closure of the Slice6/7 chain does NOT include Slice5, so
  `wirtingerEven`/`tanhHalf_eq_ratio` need an explicit
  `import ...WirtingerSlice5`.  Remaining (8.13)/(8.14) steps open:
  the (8.11) transport onto the (8.5) exponential-sum `Z(u) =
  Σ e^{−iγu} z_γ` (λ Σ w conj(w) = Q(Z) − boundary correction), the
  λ ≥ 0 assembly with the landed boundary lemma, the
  exponential-independence contradiction, and the Theorem-8 sign
  count.  DETECTOR only.
* Wirtinger slice 10, the finite-window exponential integral
  (`C1BombieriSection8ExpSum`): LANDED, axiom-clean (leaf + audit
  `2665 jobs`, 0 sorryAx; commit `5465468`).  First brick of the
  (8.11) transport: flagship `integral_exp_i_window` —
  `∫_{−t}^{t} e^{iθu} du = ↑(2 sin(θt)/θ)` for `θ ≠ 0` — the integral
  readback of the sinc term `2 sin(t(γ−γ'))/(γ−γ')` in the Lemma-10
  Gram identity, plus the `θ = 0` diagonal `2t`.  Route: real
  channel, NO complex division — `exp_mul_I` splits the integrand
  pointwise into `↑(cos θu) + I·↑(sin θu)`; the cosine half
  integrates by the real fundamental theorem with `sin(θu)/θ` as
  antiderivative (θ divided INSIDE, so no integral-linearity
  node-mismatch is ever exercised); the sine half is odd and vanishes
  through `integral_symmetry_half_real`, a real-valued mirror of the
  parity-split halving identity (the landed `integral_symmetry_half`
  is ℂ-valued — binop% silently lifts a real-valued argument through
  a cast, so the mirror is stated locally rather than reusing it).
  Mechanics worth recording (v4.30): the real `sin`/`cos` derivative
  lemmas live in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv`
  (`Real.hasDerivAt_sin`/`Real.hasDerivAt_cos`), which is NOT in the
  closure of `Analysis.Complex.Trigonometric` — explicit import
  needed; `integral_eq_sub_of_hasDerivAt`'s second argument is
  `IntervalIntegrable f' volume a b` (integrability of the DERIVATIVE,
  not continuity); `mul_neg` is now stated `a * -b = -(a * b)` (use
  the FORWARD direction to fold `θ * -t`); `integral_const_mul` takes
  NO integrability premise (`(r) (f)` only); the ℂ-valued
  `integral_symmetry_half` silently binop%-lifts real-valued inputs
  (cast appears in the expected type of the continuity argument);
  `Complex.real_smul` bridges the ℝ•ℂ algebra smul in
  `integral_const`'s `(b − a) • c` (root `smul_eq_mul` does NOT apply
  — that is `Mul.toSMul`-only); a bare `mul_comm` rewrite hits the
  FIRST multiplication in traversal order, possibly INSIDE a cast —
  close Euler-split tails with `ring` instead.  Remaining (8.11) steps
  open: the (8.5) exponential sum `Z(u) = Σ e^{−iγu} z_γ` with
  term-by-term derivative and mass expansion over `Fin n` (the
  diagonal `2t` vs off-diagonal sinc split), then the Gram-quadratic
  readback `λ Σ w conj(w) = Q(Z) − boundary`, then the ≥ 0 assembly.
  DETECTOR only.
* Full root build after complete source sync: GREEN (`4147 jobs`, 0 error).
* Endpoint sign / trace theorem: OPEN; the certificate remains the explicit
  analytic obligation (§6a).  Its scalar and finite-dimensional algebra are
  landed, but the infinite-dimensional operator/spectral estimate is absent.
* Titchmarsh bridge: NOT attempted; deferral decision recorded in §5.
* RH remains unclaimed; the universal W4b over all vanishing tests is open.
