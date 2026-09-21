# Record 1798 — First cross-gate pricing (two-span C3 producer)

Date: 2026-09-21.

Status: numerics record (no Lean brick, no RH claim). First instrument-valid
readouts of the three gate entries `G_AA = IC(A*⋆A)`, `G_BB = IC(B*⋆B)`,
`G_AB = IC(A*⋆B)` on L²-normalized admissible families, with the q-form
face (discriminant, roots, free minimum) and a first toy interpolation pin.

## Committed definitions coded verbatim (F27/F28)

- pair test `(A*⋆B)(x) = ∫ conj(A(−t))·B(x−t) dt`
  (`CCM25Concrete.CompactLogConvolution.convolution_apply`).
- `archimedeanTerm F = Re[(log 4π + γ)·F(0)
  + ∫_0^∞ (e^{y/2}(F(y)+F(−y)) − 2F(0))/(e^y − e^{−y}) dy]`
  (`C1SameOwnerWeil`, denominator per law F74).
- `finitePrimeTerm F n = Re[Λ(n)·n^{−1/2}·(F(log n)+F(−log n))]`
  (`C1SameOwnerWeil.finitePrimeTermComplex`).
- `ICgate = archimedeanTerm + finitePrimeSum`
  (`C1LocalConfigurationDomination.lean:73`).
- q-form `= G_AA + λ²G_BB − λ(G_AB + G_BA)`
  (`C1P2SpanProfileMatrix.twoSpan_gate_qform_expand`).

Rig: `scripts/twospan_cross_gate_1798.py`, log
`build-logs/twospan_cross_gate_1798.log`, data
`results/1798_twospan_cross_gate.json`.

## Instrument validation (F71/F77)

Four engines: (E1) direct convolution + y-quadrature; (E2) padded-FFT
convolution; (E3) σ-identity `arch = ∫σ(2πξ)F̂ dξ` (1741 engine verbatim,
oversample dξ ≈ 0.031 ≤ 0.05); (E4) mpmath/Gaussian referees.

- V0 Gaussian exact-answer: E1 = 1.7928047946, E3(exact F̂) = 1.7928047996,
  diff 5.0e-9.
- Every gate entry: E1 vs E3 arch agree ≤ 4.7e-7; conv E1 vs E2 ≤ 7.9e-16.
- Swap symmetry `ICgate(A*⋆B) = ICgate(B*⋆A)` (committed theorem 1762-1764
  lineage) confirmed numerically to machine precision on all 8 pairs.
- F0 = 1.000000 on every square entry (L² normalization check).
- Family anchors: D3 window root square reads −2.526 (1699/1700 anchors
  −2.7043/−2.705: same sign and scale); plain window bump square +0.861
  (1699 plain-seed sanity +0.823).

### Instrument errata caught in-build (F71 lineage)

- **E-A (slice-offset law)**: for `np.convolve(c, B, 'full')`, the value
  `F(x_j) = du·full[j + (N−1)/2]`, NOT `full[N−1 : 2N−1]`; the wrong slice
  shifts the whole pair test by LX and silently produces garbage gates
  (first run: −3e11 readings, swap split ±11). The FFT path must use the
  identical index convention.
- **E-B**: unnormalized derivative-structured families (D3 roots) have huge
  L² mass; every family must be L²-normalized before gate reads (F52
  recurrence). After normalization D3 anchors land on the committed scale.
- **E-C**: the σ engine's digamma argument is `¼ − i·om/2` (1741 verbatim);
  omitting the shift divides by zero at ξ = 0 and voids the engine.
- **E-D**: Taylor witness of the arch integrand at 0 is
  `F(0)/2 + (F''(0)/2 + F(0)/8)·y` (second-order coefficient F''/2, not
  F''/4). The value path integrates the exact formula from 1e-8 (numerator
  ~F(0)·y cancels the 2y denominator stably); the series is a witness only.

## Readouts (L²-normalized families)

Grid N = 24001, du = 5e-4, LX = 6, NF = 65536. Heads: plain bumps at
radius 0.9 / 1.8, mass-zero projection, D3 root at 0.9. References:
D3 window root at w = log2/2 (prime-free), plain window bump at 0.3
(prime-free: square support 0.6 < log 2).

| pair | G_AA | G_BB | G_AB | det | q_min |
|------|------|------|------|-----|-------|
| bump0.9 × D3root | +2.7526 | −2.5263 | −0.0000 | +6.954 | +2.753 |
| bump0.9 × win0.3 | +2.7526 | +0.8609 | +1.5679 | +0.0886 | −0.1030 |
| bump1.8 × D3root | +6.0538 | −2.5263 | −0.0002 | +15.294 | +6.054 |
| bump1.8 × win0.3 | +6.0538 | +0.8609 | +2.3230 | +0.1844 | −0.2142 |
| mz1.8 × D3root | +0.0723 | −2.5263 | +0.0002 | +0.1827 | +0.072 |
| mz1.8 × win0.3 | +0.0723 | +0.8609 | −0.2860 | +0.0195 | −0.0227 |
| D3head0.9 × D3root | −1.0960 | −2.5263 | +0.2709 | −2.696 | −1.067 |
| D3head0.9 × win0.3 | −1.0960 | +0.8609 | −0.0004 | +0.944 | −1.096 |

## Findings

- **V1 (node-orthogonality of the cross gate)**: against the triple-vanishing
  window reference, the cross gate VANISHES (|G_AB| ≤ 2.4e-4 on pairs of
  scale 1). Mechanism: the D3 moments make the pair correlation with any
  smooth head tiny (F0 ~ 1e-4..3e-4). The C3 signed estimate is therefore
  VACUOUS on D3 references — the cross-gate obstruction lives entirely in
  the non-vanishing (interpolation-compatible) reference direction.
- **V2 (razor-thin indefiniteness)**: on positive-reference pairs (both
  gates > 0), det = G_AB² − G_AA·G_BB reads SMALL POSITIVE
  (+0.0195 .. +0.1844): the 2×2 gate Gram is barely indefinite and the
  feasible λ-window is narrow — e.g. bump1.8 × win0.3: roots
  [1.476, 2.166] around λ* = 1.821, q_min = −0.214.
- **V3 (pin lands outside)**: the single-node real-λ least-squares pin
  (span realizes −1 at z = ρ+½, synthetic γ = 14.13 / 40) lands at
  λ ≈ 9.4–90.8 — a factor 5–40 outside the feasible window — and
  q(λ_pin) > 0 on every positive-reference pair. The geometry pin, not the
  free-λ face, is the binding constraint. (Toy pin caveat: the real
  geometry pins through the full orbit-sum system
  `Σ_{u ∈ orbit} ĝ²(u) = −2` plus target values; that system is NOT
  instantiated here.)
- **V4 (binding primes of the cross gate)**: for bump1.8 × win0.3 the AB
  entry decomposes as arch +1.448 + primes +0.875, with n = 2 (+0.409) and
  n = 3 (+0.345) binding; the tail is dead past n = 5. The AA entry's prime
  terms decay past n = 13. Any signed estimate for C3 must therefore
  control the prime-2/prime-3 pair-profile cells first (F71 kink-cell
  discipline applies).
- **V5 (gate negativity is a balance)**: the D3 head at radius 0.9 SEES
  primes (support past log 2) and still reads G_AA = −1.096 < 0 — with
  positive individual prime cells in its profile. Consistent with the 1744
  pointwise no-go: the gate is a global balance, never a pointwise sign.

## Boundary

No Lean brick; the full `OrbitG8Geometry` interpolation system (centered
orbit sum = −2, ball zero control, dyadic tail budget) is not instantiated;
the pin is a single-node toy. This record prices the gate entries and the
q-form face only. Detector-specific semi-local positivity and RH remain
open; no priority claim is made.
