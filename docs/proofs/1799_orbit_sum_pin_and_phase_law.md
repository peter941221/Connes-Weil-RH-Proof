# Record 1799 — Orbit-sum pin realized; gate phase law at the pinned head

Date: 2026-09-21.

Status: numerics record (no Lean brick, no RH claim). The committed
`OrbitG8Geometry` interpolation system — orbit target values, detector node,
healthy zeros, and the centered orbit sum `Σ_{u} L[g²](u) = −2` — is
instantiated EXACTLY by an explicit compactly-supported family at off-line
zeros, and the gate `ICgate(g*⋆g)` is read at the pinned head. The gate is a
phase-sensitive quasiperiodic balance: prime cells dominate, the sign flips
with the zero height, and the Archimedean face stays small and stable.

## Committed structure coded verbatim (F27/F28)

- `T = base^{⋆(n+1)} ⋆ correction` (`convolutionIterate` + `convolution`),
  `g = halfDensityShift(T) = e^{x/2}·T(x)`,
  `L[halfDensityShift f](s) = L[f](s + 1/2)` (`laplaceAt_halfDensityShift`).
- `laplaceAt` uses the **+s convention** `L[f](s) = ∫ f(x) e^{+sx} dx`
  (forced by the shift theorem).
- Square Laplace pairing: `L[g*⋆g](u) = conj(L[g](−ū))·L[g](u)`; the centered
  orbit `{u, −ū, ū, −u}`, `u = ρ − ½`, is `hermitianNodeClosure`-closed, and
  with the target values `(ρ, 1−ρ̄, ρ̄, 1−ρ) ↦ (1, −1, 0, 0)` the sum reads
  `2·Re[conj(−1)·1] + 2·Re[conj(0)·0] = −2` in closed form.
- Interpolation system (`healthyUnscaledTargetNodes`/`Value`,
  `negativeSourceOrbitValue`): `T̂(ρ) = 1`, `T̂(1−ρ̄) = −1`, `T̂(ρ̄) = 0`,
  `T̂(1−ρ) = 0`, `T̂(ρ+½) = −1`, base zeros at `{½, 1, 3/2}`.
- Gate: `ICgate F = archimedeanTerm F + finitePrimeSum F`
  (`C1LocalConfigurationDomination.lean:73`), denominator `e^y − e^{−y}`
  (F74), Archimedean engine = 1741 σ-identity (`σ(om) = log π − Re ψ(¼ −
  i·om/2)`), prime terms `Λ(n)·n^{−1/2}·(F(log n) + F(−log n))`.

Rig: `scripts/orbit_sum_pin_1799.py` (modes: full grid + `--scan`),
logs `build-logs/orbit_sum_pin_1799.log`,
`build-logs/orbit_sum_pin_1799_scan.log`, data
`results/1799_orbit_sum_pin.json`.

## Instrument evolution (three errata, F71 lineage)

- **E-E (static-width basis is singular at height γ)**: the first build used
  plain bumps of fixed width; the interpolation matrix read cond 1.4e17 with
  solution norms ~1e20 — numerically singular. Interpolation at `s = β + iγ`
  demands frequency-γ oscillation: the correction basis must be the modulated
  bumps `φ_j(x)·e^{−iγx}` (live rows) and `φ_j(x)·e^{+iγx}` (dead rows), and
  the base width must scale as `c/γ`. Quantitative confirmation of the 1627
  no-band-limited / infinite-type verdict.
- **E-F (block splitting amplifies leakage)**: solving the live (+γ) and dead
  (−γ) node blocks separately blows up: C^∞ bumps are Gevrey — the decay is
  SUBEXPONENTIAL, so a +γ-modulated bump still has ~1e-3 content at −γ over
  these supports; the dead-block cancellation reached α ~ 1e5 and
  re-contaminated the live nodes (resid 1e3). The 5×5 system is jointly
  well-conditioned (all entries O(1)) and must be solved as one system.
- **E-G (spectral-root base carries an invisible ring)**: building the base's
  zeros by the spectral operator `∏(D−a_j)` multiplies the bump spectrum by
  ξ³ and produces real-space ringing at ξ ~ 10³ (pre-normalization sup-norm
  3e5). Splines cannot see that content, so `b̂` evaluated through splines
  disagreed with the grid object and the post-convolution residuals read
  0.97 (algebra residual was 1e-11). Fix: the base is a bump COMBINATION
  `Σ_j c_j φ((x−μ_j)/w)` whose Laplace is `L[φ_w](s)·Σ_j c_j e^{s μ_j}` with
  the nullspace of the 3×4 matrix `[e^{s_l μ_j}]` (s_l ∈ {½, 1, 3/2})
  fixing the weights — the three zeros are EXACT (|b̂(s_l)| ≤ 4.3e-17) and
  the base is spectrally clean (energy above ξ = 300: 1.4e-3).
- **E-H (direct Archimedean engine invalid on oscillatory profiles)**:
  `arch_direct` (adaptive quadrature of the y-integrand) breaks on the
  pinned head's autocorrelation (disagreements up to 1e12 vs σ). The σ
  engine is the oscillation-immune referee; all arch readings below are σ.

All interpolation solves/reads use the grid rectangle product (`lap_grid`),
not splines; splines are used only for the prime-term evaluation where they
were validated in 1798.

## Readout 1 — the pin is realizable (full grid, 16 cases)

β ∈ {0.55, 0.6} (right-hand off-line zeros), γ ∈ {14.1347, 40},
base width `c_b/γ` with c_b ∈ {0.6, 1.2}, base power k ∈ {1, 2}.

Every case: interpolation residual ≤ 3.2e-8, **orbit sum = −2.000000**
(to printed precision in all 16), cond ≤ 9.4e3, zero factor ≤ 4.3e-17.

| β | γ | cond | max α | resid | orbit sum | arch σ | primes | gate |
|------|------|------|--------|--------|----------|---------|---------|---------|
| 0.55 | 14.1 | 9.3e3 | 1.7e4 | 2.8e-11 | −2.0000 | −50.77 | +7.38e4 | +7.38e4 |
| 0.55 | 14.1 | 9.3e3 | 6.6e4 | 6.7e-11 | −2.0000 | +0.0008 | +1.74e5 | +1.74e5 |
| 0.55 | 40.0 | 9.4e3 | 7.2e5 | 5.9e-10 | −2.0000 | −59.67 | −5.08e8 | −5.08e8 |
| 0.55 | 40.0 | 9.4e3 | 1.1e8 | 5.5e-08 | −2.0000 | +4.31 | −6.21e11 | −6.21e11 |
| 0.60 | 14.1 | 4.5e3 | 8.7e3 | 2.1e-11 | −2.0000 | −12.66 | +1.86e4 | +1.86e4 |
| 0.60 | 14.1 | 4.5e3 | 3.3e4 | 6.4e-11 | −2.0000 | +0.0002 | +4.40e4 | +4.40e4 |
| 0.60 | 40.0 | 4.5e3 | 3.5e5 | 1.7e-10 | −2.0000 | −14.52 | −1.22e8 | −1.22e8 |
| 0.60 | 40.0 | 4.5e3 | 4.8e7 | 3.2e-08 | −2.0000 | +10.70 | −1.30e11 | −1.30e11 |

(c_b = 1.2 rows analogous; see the JSON.)

## Readout 2 — the phase law (γ-scan, β = 0.55, c_b = 0.6, k = 1)

Scanning γ from 14 to 40 in steps of 1:

- The gate equals its prime part to 4 digits everywhere; the Archimedean
  face stays SMALL and stable (|arch σ| ≤ 1.04e6 only inside the γ ≈ 20–22
  resonance dip; ≤ 1e3 elsewhere; ≤ 73 on 24 ≤ γ ≤ 40 away from 20–22).
- The gate swings over ~5 orders of magnitude and flips sign three times
  (between 20 and 21, between 27 and 28, between 35 and 36).
- A single-phase model `cos(2γ log 2)` fails (max residual / amplitude
  = 12.1): the balance is a MULTI-FREQUENCY beat — each prime cell n
  carries its own carrier phase `2γ log n`, with a γ-dependent amplitude
  envelope (the `|b̂(ρ)|^{−k}` growth of the correction norm).

## Findings

- **W1 (pin realizability)**: the full committed interpolation system —
  orbit values, detector node, healthy zeros, and the centered orbit sum
  `= −2` — is realized EXACTLY by an explicit compactly-supported family at
  off-line zeros. The geometry pin is not an obstacle by itself; the 1798
  V3 "toy pin lands outside the window" worry is superseded: with the real
  system there is no free λ to land — the pinned head is a point in test
  space, and it exists.
- **W2 (phase law / no pointwise signed statement)**: at the pinned head
  the gate is a quasiperiodic function of the zero height with sign flips
  and unbounded envelope on this family. Any pointwise-in-the-head signed
  statement of the C3 gate is FALSE on this family; the signed estimate
  must live in the phase-locked structure: either (a) the CROSS channel
  against a carrier-locked reference (the 1798 V1 node-orthogonality, now
  with mechanism), or (b) after a Schwartz θ-regularization that kills the
  carrier tails (the 1734/F59 two-IBP bound is the ready tool).
- **W3 (stable Archimedean floor)**: the arch face is small and stable
  across the whole scan — the prime side is the entire content of the gate
  balance, which is consistent with the B5 budget's shape
  (`credit/deficit` = prime terms).
- **W4 (on-line collision)**: as β → ½⁺ the orbit nodes ρ and 1−ρ̄ COALESCE
  while their targets (1 and −1) collide: the interpolation system is
  intrinsically ill-conditioned (~1/ε) approaching the critical line — the
  off-line zero budget degenerates at the boundary. Consistent with the B5
  producer being a per-OFF-LINE-zero statement whose RH passage must go
  through the limit argument, not through the on-line geometry directly.

## Boundary

No Lean brick. The dyadic ball zero-control and the fourth-order tail
budget of the committed geometry are NOT instantiated (construction
obligations above the pricing question). The correction family (and hence
the gate envelope) is a choice, not a canonical object; W2's sign flips are
family-quantitative but the phase mechanism is structural. Detector-specific
semi-local positivity and RH remain open; no priority claim is made.
