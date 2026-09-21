# Record 1800 — C3' opens: carrier transport is a theorem; the arch floor has a symbol

Date: 2026-09-21.

Status: ONE formal brick (standard axioms, zero errors/warnings) plus a
paper page. The measured phase law of record 1799 (finding W2) becomes an
exact theorem: same-carrier pair profiles transport the carrier, and every
prime cell of a carrier square reads through ONE real phase factor
`exp(-iγ log n)`. The Archimedean face of a carrier square decomposes as
`σ(-γ)·‖u‖² + O(1/γ)` (paper-only, σ identity not yet formalized), and
`σ(-γ) < 0` for `γ > ξ* = 6.2898` is theorem-grade from the 1741 digamma
leaf. The C3' signed estimate is now stated precisely, in envelope
variables, with the phase dimension eliminated.

## Formal brick: `ConnesWeilRH/Dev/C1C3CarrierTransport.lean`

Coded on the committed definitions (`CompactLogTest`, involution
`f*(x) = conj(f(-x))`, convolution, `finitePrimeTermComplex`,
`C1SameOwnerWeil`), all standard axioms, zero errors and warnings
(log `build-logs/1800_carrier_transport.log`, mirror).

- `carrierExp γ x = exp(i·(-γ·x))` (canonical single-cast form),
  `carrierModulate γ f = carrierExp γ x · f.test x` — a well-formed
  `CompactLogTest` (compact support via `HasCompactSupport.mul_left`,
  smoothness via the ofReal∘linear composition).
- **Theorem (carrierPair_transport)** — C3' Lemma 1:
  `(Uᵧ)* ⋆ (Vᵧ) = carrierExp γ x · (u* ⋆ v)` pointwise. Same-carrier pair
  tests transport the carrier EXACTLY. Proof: pointwise integrand algebra
  (conjugate flips the carrier sign, `carrierExp γ (x-t) = carrierExp γ x ·
  carrierExp γ (-t)`, `carrierExp γ t · carrierExp γ (-t) = 1`), then
  `integral_congr_ae` + `integral_const_mul`.
- **Theorem (convolutionSquare_carrier_apply)**: the square channel
  `g* ⋆ g` of a carrier-modulated test carries the same carrier.
- **Theorem (square_pair_sum_carrier)** — C3' Lemma 2:
  `F(y) + F(-y) = 2 · Re[carrierExp γ y · G(y)]` with `G = u* ⋆ u`
  (Hermitian symmetry `convolutionSquare_neg` + `Complex.add_conj`).
- **Theorem (finitePrimeTerm_carrierSquare)** — C3' Lemma 3, the
  prime-cell phase law:
  `finitePrimeTerm F n = Λ(n) · (2/√n) · Re[carrierExp γ (log n) · G(log n)]`.
  This is the exact form of the quasiperiodic prime balance MEASURED in
  record 1799 (γ-scan: sign flips at γ ≈ 20.5, 28, 36; multi-frequency
  beats in `2γ log n`). The law is structural algebra, not a family
  artifact.

## Paper page: the σ-shift arch floor (C3' Lemma 3', paper-only)

With `F = carrier square`, the Fourier shift theorem gives
`F̂(ξ) = Ĝ(ξ + γ/(2π))`, so the σ-identity (1741, validated 7/7 at
3.3e-15) re-centers:

  arch(F) = ∫ σ(2πη − γ) · Ĝ(η) dη
          = σ(−γ) · G(0) + 2π·σ′(−γ)·(first moment) + remainder,

where `G(0) = ‖u‖² ≥ 0` (the envelope square at 0), and the remainder is
controlled by the σ-derivative: `σ(ξ) = log π − Re ψ(¼ − iξ/2)` has
`σ′(ξ) = O(1/ξ)` (the 1735 digamma vertical-line bound is the tool), while
`Ĝ` concentrates in `|η| ≲ W` for envelope support width W.

  **arch(carrier square) = σ(−γ)·‖u‖² + O(W·‖Ĝ‖₁/γ).**

Sign: `σ(−γ) < 0` for `γ > ξ* = 6.2898` is theorem-grade (1741 digamma
leaf), and `|σ(−γ)| ~ log(γ/2π)` grows. The Archimedean face of a carrier
square therefore supplies a NEGATIVE, symbol-controlled floor — the deficit
side of the B5 budget now has a symbol. Boundary honesty: the σ identity
itself is not yet in Lean (1741 is a validated numerics engine; the Lean
σ-identity brick is a listed next step), so this subsection is paper.

## The C3' estimate, now precisely stated

Combining the three formal lemmas with the σ floor, the two-span q-form on
a carrier-locked pair (A = carrierModulate γ a the pinned head, B =
carrierModulate γ b the reference, same γ) reduces EXACTLY to the
envelope-level form

  q(λ; γ) = [σ(−γ)·(‖a‖² + λ²‖b‖²) + O(1/γ)]
          + Σ_n (2Λ(n)/√n) · Re[e^{-iγ log n} · H_n(λ)],

where `H_n(λ)` is the envelope-level quadratic cell (`a*⋆a + λ²(b*⋆b) −
λ(a*⋆b + b*⋆a)` cells at log n). The remaining open inequality — the whole
content of C3' — is:

  **Envelope budget**: for each right-hand off-line zero ρ = β + iγ, the
  envelope pair (a, b) solving the committed interpolation system admits a
  coefficient λ with `q(λ; γ) ≤ 0`.

Two structural notes sharpen it:

- **Per-zero locality kills the phase obstruction.** B5 is a per-zero
  ∃-statement: γ is FIXED by the zero, not quantified. The 1799 W2 sign
  flips across γ are therefore NOT an obstruction to the producer — for
  each fixed γ the envelope freedom (the correction interpolation) is the
  object that must make the balance nonpositive. Uniformity in γ is needed
  only for the W4 limit passage (β → ½⁺), which is a separate page.
- **The cross channel is phase-locked, not dead.** 1798's V1 (cross gate
  vanishes against triple-vanishing references) plus Lemma 1 say: the AB
  cells carry the SAME carrier phase as the AA/BA cells. The cancellation
  the producer needs is an envelope-level cancellation between
  phase-coherent cells — measurable, and now amenable to the two-IBP bound
  (`|∫θe| ≤ ‖θ''‖₁/(4π²s²)`, brick 1735) for the pairing estimates.

## Boundary

One formal brick, no RH claim. The σ identity, the σ-derivative bound as a
Lean artifact, the envelope-level inequality, the W4 limit page, and the
Core B W^{2,1} assembly are all open. The 1799 correction family's huge
prime book (‖cells‖ ~ |α|²·phase, 7 orders above the σ floor at γ = 40)
remains the quantified gap the envelope inequality must close.
