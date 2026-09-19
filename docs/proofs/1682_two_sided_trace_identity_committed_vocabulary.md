# 1682 — The trace identity in committed vocabulary: the gate content is the TRACE-CLASS embeddability of the carrier, free on the inner side, conditional on the committed (anti-inner) side

Date: 2026-09-19.

Status: analysis record (paper level; hand-derived from committed
definitions per the read-source-first law).  One normalization constant is
left to the 1683 rig calibration.  No estimate is proved and RH is not
claimed.

## 1. The exact formal-side identity (already committed)

With the committed objects

```text
C = rootConvolution owner
  = cc20GlobalLogConvolution owner.sourceTest.involution.test   (CCM25)
J = sourceInclusion lambda
P₀ = carrier projection (range E ⊓ range Q, 1589 pin)
φ(ξ) = |𝓕h(ξ)|²,   h = the involution test ∈ C^∞_c  (CompactLogTest)
```

the survivor-core square-sum over a carrier ONB `{e_i}` is the diagonal
trace of a positive compression (1669-style column-energy identity, made
an iff with the gate in 1680):

```text
core  =  ∑_i ‖C J e_i‖²  =  tr( P₀ M_φ P₀ ).
```

Two immediate structural readings:

* The summands are `⟨M_φ e_i, e_i⟩`.  For `φ ≡ 1` the sum is the
  dimension — INFINITE.  So the core is never a boundedness statement;
  it is a TRACE-CLASS statement: `P₀ M_φ P₀` must be trace class on the
  carrier, equivalently the carrier embedding into the `φ`-weighted
  space must be Hilbert–Schmidt type.  This is the precise sense in
  which the gate is analytic content, not bookkeeping.
* `|𝓕h|² ≤ C_N(1+|ξ|)^{−N}` (h ∈ C^∞_c ⇒ 𝓕h Schwartz): the weight is
  as nice as it can be.  All the content sits in the carrier's measure
  structure, none in the weight.

## 2. The paper-side model formula (what ∫|ĝ|²dμ means)

For a MODEL space (Θ inner, K_Θ = H² ⊖ ΘH²) the compressed
multiplication trace is the Clark trace formula: with μ = the Clark
measure (pure point at the phase-hitting set {x : Θ(x) = e^{iα}}, atom
masses ∝ 1/|γ′(x_k)|, γ the boundary phase),

```text
tr( P_Θ M_φ P_Θ )  =  ∫ φ dμ   (φ continuous; rank-one defect terms
                                from the compressed-shift correction are
                                flagged and calibrated in 1683)
```

For OUR symbol the carrier is the two-sided intersection space (1629
normalization), Θ = e^{4πi(logλ)ξ}m(−ξ) is NOT inner — it is unimodular
on ℝ for every λ (m is a quotient of conjugates, |m(ξ)| = 1 on ℝ) but
GROWS in ℂ₊ (anti-inner exponential, 1681).  The object that plays μ is
the spectral measure of the associated canonical system (the de Branges
W-space of the 1590/1626 retype); the Clark pure-point formula is its
monotone-phase surrogate, valid per monotone branch of γ.

## 3. The structural split (the finding)

On the INNER side of the family (singular-inner twin Θ = e^{iτξ}, τ>0,
m ≡ 1): the phase is linear, the atoms sit on a uniform lattice
(spacing ∝ 1/τ) with EQUAL masses, and the atom measure has the same
total mass as normalized Lebesgue.  Then

```text
tr( P₀ M_φ P₀ ) = ∫ |𝓕h|² dμ ≈ (1/2π)∫ |𝓕h|² dξ < ∞
```

is FREE — the core square-sum holds for every Schwartz test, no
analysis needed.  By 1680's no-slack iff this is consistent: the gate on
the inner side is genuinely trivial (the corresponding face carries no
RH content).

The committed family lives on the ANTI-INNER side (logλ < 0).  There:

1. The exact phase derivative (hand-derived from the committed symbol
   via digamma; cross-checked by finite differences and by bisection in
   the 1683 rig) is

   ```text
   γ′(ξ) = 4π logλ − 2π logπ + 2π Re ψ(¼ + πiξ)
          ~ 4π logλ + 2π log ξ   (large ξ),
   ```

   so the phase folds at **ξ = λ⁻²** (asymptotically exactly; the rig's
   bisection reads ratio fold/λ⁻² = 1.0000017 at λ = 0.2).  NOTE: an
   earlier draft of this section transferred the 1631 kernel-side budget
   `γ′ = −2π log|ξ|` to the symbol side and placed the fold at λ² — the
   transfer was wrong (the rig's FD check caught it before commit; the
   F27/F28 lesson again).  The fold λ⁻² is 1633's ξ_c: the same
   degeneration seen from the symbol side and the kernel side.  At the
   fold the surrogate atom mass π/|γ′| blows up and the smooth-branch
   reading ends.
2. The measure is the two-sided canonical-system measure, whose
   finite-mass property is exactly what is NOT free — consistent with
   the tower (off-line zero ⇒ qw < 0 [formal] ⇒ 0 ≤ qw(g) [open gate]).

## 4. Trap flag (routes)

Any route that internally replaces the committed symbol by an inner
model (or approximates in a class where the anti-inner growth is not
tracked) silently falls into §3's free case and proves the free
inner-side bound — nothing.  This is the mechanism behind 1630's
Toeplitz-probe readout "approximable but not attained" (F43) and the
1632 ε-gap: the approximation sequence lives toward the inner side
while attainment is the anti-inner point itself.  Route-1 work must
price the two-sided measure, not a model-space surrogate of it.

## 5. Calibration duties (discharged by 1683's rig)

(a) the Clark atom-mass normalization constant under the committed
Fourier convention; (b) the atom-density × atom-mass cancellation on a
monotone branch; (c) the m ≡ 1 uniform-lattice row; (d) the degeneration
at |ξ| = λ²; (e) the smooth-branch integrability surrogate for a
concrete C^∞_c representative of the committed test class.

## 6. Boundary

The uniform annular bound, the survivor core, and RH remain open.  This
record names the object, splits the trivial from the contentful side,
and flags the surrogate trap.
