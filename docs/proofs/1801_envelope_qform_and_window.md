# Record 1801 — Producer anatomy, gate indefiniteness, and the empty tailStart window

Date: 2026-09-21.

Status: TWO rigs, no Lean brick. The producer behind
`sourceRH_of_right_orbitGeometry_spanGateCertificate` is anatomized exactly,
its gate quadratic form is measured INDEFINITE on the geometry-preserving
family, and the committed `OrbitG8Geometry` tailStart parameter window is
measured EMPTY at every tested zero for the 1799-style owners — with the
escape route quantified (wider owners close it). RH not claimed.

## 1. Producer anatomy (theorem-grounded, k = 1 collapse)

Two committed facts collapse the producer to a single sentence:

- `C1GateMatrixRepresentation.lean:396`:
  `ICgate ((spanObj w y).convolutionSquare) = y ⬝ᵥ (gateMatrix w *ᵥ y)`.
  With `k = 1`, `w = fun _ => g`, `y = 1`, the producer's q-form condition
  IS `ICgate (g*⋆g) ≤ 0` for the geometry test itself. The span/matrix
  format is a free re-parameterization; it adds no freedom.
- `C1HealthyYoshidaMinimalInterpolation.lean:39`:
  `HealthyMinimalLaplaceRealizes ρ g = (L[g](0) = 0 ∧ L[g](½) = 0 ∧
  L[g](1) = 0 ∧ L[g](ρ) ≠ 0)` — finite conditions, no uniqueness clause.

**PRODUCER(ρ) ⟺ ∃ g: OrbitG8Geometry ρ g ∧ ICgate(g*⋆g) ≤ 0.**

The geometry's linear conditions pull back through the owner map
`g = halfDensityShift((base^⋆k) ⋆ c)` with the +s convention
(`L[u ⋆ v](s) = L[u](s)·L[v](s)`, plain product — no conjugate):

- target/orbit conditions ⟹ `L[δc](s) = 0` at the SAME nodes (dedup: the
  centered orbit nodes `v + ½` land exactly on the target nodes);
- the minimal/healthy zeros `{0, ½, 1}` (g level) hit the base zeros
  `{½, 1, 3/2}` where `L[base^⋆k] = 0` — structurally preserved, vacuous
  for the perturbation;
- `square_zero_control` and the fourth-order tail are conditions on the
  SQUARE and on free parameters (see §3).

So the solution space is an affine space `A + N` (A = the 1799 pinned
head, N = the node-orthogonal nullspace through the correction slot, real
dimension ≥ 13 in the rig family), and the gate restricted to it is the
quadratic form `q(λ) = G_AA − 2λG_AB + λ²G_BB` on each direction.

## 2. Rig 1801: the gate quadratic form is INDEFINITE

`scripts/envelope_qform_1801.py` (WSL, log `build-logs/1801_envelope_qform.log`):
8 owner cases (β ∈ {0.55, 0.6} × γ ∈ {14.1347, 40} × (cb, k) ∈
{(0.6, 1), (1.2, 2)}), all 1799-admissible (resid ≤ 3.1e-8, orbit sum
−2.000000); per case two node families (minimal: 5 conditions, null dim 13;
strengthened: +6 off-line-zero conditions, null dim 7) and 19 probes each
(3 axis directions + 16 random complex nullspace combinations).

Instrument notes: dcnull lives in COEFFICIENT space and numpy's SVD returns
`Vh` rows — the nullspace vectors are the CONJUGATES of the trailing rows
(two instrument errata, both caught by the in-rig preservation check, the
F71 three-way discipline). G_BB's sign is carried ENTIRELY by the prime
face (arch_BB ∈ [−2e-5, 5e-12] vs pr_BB ∈ [−7e-3, 1e-2]): no cancellation
risk; the indefiniteness is a clean measurement.

Readout (best probe per family-case):

| case (β, γ, cb, k) | family | G_AA | G_BB range | feasible | q_min best |
|---|---|---|---|---|---|
| 0.55, 14.13, 0.6, 1 | min | +7.38e4 | [−2.9e-4, +5.7e-3] | 2/19 | −3.65e4 |
| 0.55, 14.13, 1.2, 2 | min | +5.04e5 | [+2.3e-4, +3.0e-3] | 0/19 | +1.22e5 |
| 0.55, 40, 0.6, 1 | min | −5.08e8 | [−3.5e-3, +1.2e-3] | 19/19 | −1.40e9 |
| 0.55, 40, 1.2, 2 | min | −6.92e11 | [−6.4e-4, +2.6e-4] | 19/19 | −5.26e12 |
| 0.60, 14.13, 0.6, 1 | min | +1.86e4 | [−2.9e-4, +5.7e-3] | 2/19 | −8.86e3 |
| 0.60, 14.13, 1.2, 2 | min | +1.26e5 | [+2.3e-3, +3.0e-3] | 0/19 | +3.10e4 |
| 0.60, 40, 0.6, 1 | min | −1.22e8 | [−3.4e-3, +1.2e-3] | 19/19 | −3.58e8 |
| 0.60, 40, 1.2, 2 | min | −1.45e11 | [−6.3e-4, +2.6e-4] | 19/19 | −1.09e12 |

Findings:

- **F-A (indefiniteness)**: G_BB straddles zero in every family where the
  search found both signs (109/304 probes negative). Along any G_BB < 0
  direction, `q(λ) → −∞`: the gate condition is satisfiable at arbitrarily
  large span coefficients. The q-form on the geometry solution family is
  NOT positive definite.
- **F-B (the γ = 40 trough)**: at γ = 40 the pinned head's OWN gate is
  already ≤ 0 (−5.1e8 … −1.5e11) — the W2 quasiperiodic trough. Subject to
  the boundary items (§3), those zeros have a gate-satisfying head.
- **F-C (the λ ceiling)**: the huge-λ route is closed by the geometry's
  own consistency (§3). At the feasible-λ scale (O(1)–O(10), from the
  C₄/tail budget) the correction |2λG_AB| ≤ O(40) cannot dent G_AA ~ 1e4
  at γ = 14.13. The gate problem is the HEAD's prime book, not the span.

## 3. Rig 1801b: the committed tailStart window is EMPTY (measured)

The geometry couples three conditions on ONE integer parameter tailStart:

- floor: `zero_height_le_dyadic` ⟹ tS ≥ log₂(2γ) − 1;
- cap: `square_zero_control` demands `L[g²] = 0` at all zeros in the ball
  `|z − ρ| ≤ 2^{tS+1} + 2 + dist(2, ρ)`. L[g²] is Cartwright class (type
  a = supp radius, bounded on iR), zero budget `n(r) ≤ (2a/π)r`
  (Levin, Lectures on Entire Functions, Lect. 9 — paper-grade); demanded
  zeros ~ (2R/π)·log by RVM. Satisfiable only while
  `2^{tS+1} ≲ 2πe^a − γ − 2 − dist(2, ρ)`.
- budget: `tail_budget_below_multiplicity` with the committed
  `spectralMultiplicityConstant = (… + 192)/log 2 ≈ 279.8`
  (C1SpectralSummability.lean:303) ⟹ `ε²(tS) ≤ (4/3)^{tS}/(4·C_mult)`.

`scripts/tail_window_1801b.py` measures, on the constructed owner square
F = g*⋆g: the support radius a, and `S(T) = sup_{σ∈{−½,0,½}, τ≥max(T,2γ)}
τ⁴|L[F](σ+iτ)|` (direct +s quadrature to the grid Nyquist τ = π/DU ≈ 6283;
rows with T beyond Nyquist are marked unmeasurable, not filled).

Verdict — **all 8 cases EMPTY**:

| case | a | floor | cap | window | tail at best tS |
|---|---|---|---|---|---|
| γ=14.13, cb0.6 k1 (both β) | 2.03 | 4 | 3 | cap < floor | — |
| γ=14.13, cb1.2 k2 (both β) | 3.10 | 4 | 5 | {4,5} | S=1e11 vs ε²=2.8e-3; S=1e8 vs 3.8e-3 |
| γ=40, cb0.6 k1 (both β) | 1.99 | 6 | −99 | cap < 0 | — |
| γ=40, cb1.2 k2 (both β) | 2.93 | 6 | 4 | cap < floor | — |

Mechanism readings:

- **F-D (the γ-hostile ball)**: the ball formula's `+2 + dist(2, ρ)` term
  grows with γ; at γ = 40 with a narrow owner the ball budget is exceeded
  ALREADY at tS = 0 (the ball must contain the zero's height region, and
  the demanded zero count (2R/π)log R outgrows the Cartwright budget
  (2a/π)R for a ≈ 2).
- **F-E (the exponential race)**: S(T) falls ~10³ per doubling of T while
  ε²(tS) grows only 4/3 per level — the race is won by support, not by
  tailStart: closing the window needs `a ≳ 5` (support(g²) ≥ 5.12 at
  tS = 9, γ = 14.13), i.e. support(g) ≥ 2.56 — ALLOWED by the committed
  structure (`base_support`/`correction_support` only demand ⊆ (−1,1);
  orbitIndex is free) but NOT realized by the 1799-style narrow owners
  (a ≈ 2–3.1).

**The tension, now exact**: the GATE wants narrow tests (small prime book:
cells only at log n inside the support), the WINDOW wants wide tests
(large a raises the Cartwright cap and pushes T above the square's spectral
knee). The 1799 owners sit at the narrow end. The producer's satisfiability
is the question whether some width in between hosts a test whose gate,
under the full geometry, is ≤ 0.

## Boundary

No Lean brick (the wave is measurement + anatomy; the two instrument
errata are recorded in §2). The Cartwright cap and the RVM counting are
paper-grade; everything else is measured on the committed definitions.
The ball-zero interpolation system itself was NOT instantiated (as in
1799) — §3 caps what tailStart could even be. The γ = 40 negative gates
are gate-readouts, not certificates, until the ball/tail side is built.

## How to take it down (the decision tree this wave produces)

1. **Wide-owner route (no committed-definition change)**: rebuild the
   owner with orbitIndex k = 2–3 and full-width (−1,1) corrections
   (a ≈ 6) — the window closes by the §3 numbers; then measure the gate
   of that owner's head and minimize it over the (now larger) solution
   family. The producer reduces to `min ICgate(g²) ≤ 0` over the
   window-feasible class — a Weil-energy minimization with a concrete
   finite-dimensional proxy per zero.
2. **Cross-domination route**: |G_AB| reaches 8e3 at γ = 40 — if a
   direction with |G_AB| ~ G_AA/(2λ_max) exists at γ = 14.13, the
   feasible-λ window opens at modest λ. Same rig, maximize |G_AB| instead
   of probing randomly.
3. **Geometry revision (committed-definition change — needs approval)**:
   decouple the ball radius from tailStart (e.g. radius ~ 2γ + 2 + 2), so
   tailStart is free and the budget's (4/3)^{tS} relaxation makes the
   window nonempty for every C₄. This is the cleanest single edit but it
   touches `C1G8R0OrbitGeometry` certificates.
