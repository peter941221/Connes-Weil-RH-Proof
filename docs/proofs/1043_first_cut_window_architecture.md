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
* Full root build after complete source sync: GREEN (`4147 jobs`, 0 error).
* Endpoint sign / trace theorem: OPEN; the certificate remains the explicit
  analytic obligation (§6a).  Its scalar and finite-dimensional algebra are
  landed, but the infinite-dimensional operator/spectral estimate is absent.
* Titchmarsh bridge: NOT attempted; deferral decision recorded in §5.
* RH remains unclaimed; the universal W4b over all vanishing tests is open.
