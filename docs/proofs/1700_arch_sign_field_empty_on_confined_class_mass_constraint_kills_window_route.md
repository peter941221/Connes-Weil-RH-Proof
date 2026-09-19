# 1700 — the archimedean sign field is EMPTY on the window-confined class: arch(g⋆g) ≤ 0 with sup = 0 already under ∫g = 0 alone (machine-zero, N-stable, ablation-isolated); the confined route to premise 1 is dead and P1 is forced into the full-book construction

Date: 2026-09-19.

Status: two decisive rigs on the committed vocabulary
(`scripts/arch_eigen_1700.py` + `arch_eigen_1700b.py`, run in WSL2; results
`results/1700_arch_sign_field.json` + `1700b_lambda_nstability.json`).
Companion to records 1698/1699.  RH is not claimed; the measurement is
numerical — the paper-level statement it points at is named in §4.

## 1. The question, made exact

After 1698, premise 1 of the two-premise exit is exactly
{window-confined seed with nonvanishing Laplace value} + {arch sign on the
D3 square}.  1699 showed the NAIVE seeds fail the sign.  The open question
was whether ANY seed in the class works.  The class is linear:

```text
  C_w = { g : supp g ⊆ [−w, w], w < 3/10,
          ∫g = 0,  ∫e^{x/2}g = 0,  ∫e^{x}g = 0 }        (ĝ vanishes at
                                                           0, 1/2, 1)
```

and the WHY of the three moments is structural: g = tripleVanishingRoot h
= D(D+1/2)(D+1)h has ker L* = span{1, e^{x/2}, e^x} (adjoint of D+a is
−D+a, order reversed), and ⟨g, φ⟩ on that span is exactly ĝ(1), ĝ(1/2),
ĝ(0) — the adjoint conditions ARE the node moments, so C_w is EXACTLY the
frame theorem's root class.  The sign field is the quadratic form

```text
  Q[g] = archimedeanTerm(g ⋆ g̃)
       = (log 4π + γ_E)F(0)
         + ∫₀^∞ [e^{y/2}(F(y)+F(−y)) − 2F(0)]/(eʸ − e^{−y}) dy,
  F = starConvolution g                                        (:61)
```

and the question is the sign of λ_max(w) = max Q[g]/mass(g) over C_w.

## 2. Instrument and its certification

Q is built as a symmetric matrix on a padded periodic grid (support class
enforced by coordinate masking, moments by projection), and independently
re-read as a direct discrete sum (no circulant, no adaptive quadrature).
Certifications, both against INDEPENDENT answers:

```text
  plain bump (unconstrained), w = 0.29:   Q_form = +0.823196
     vs 1699's quad readout  +0.823434                      ✓
  D3 root of the even bump, w = 0.29, L²=1: Q_form = −2.7043
     vs 1699's −2.705187                                    ✓
  validator A (random admissible g, form vs direct sum):
     relerr 3e−5 … 9e−5 at every width                      ✓
```

Two instrument bugs were caught and fixed in-wave (never recorded as
results): the circulant part of M was missing the correlation's internal
`dx` factor, and the −2F(0) term was missing the integration step — each
off by a factor visible against the known answers.  Adaptive quadrature
(`quad`) on the padded grid proved unreliable (spurious ~0 totals with
roundoff warnings); the certified readouts are the matrix form and the
direct discrete sum, which agree to 1e−4.

## 3. Verdict

```text
  λ_max(w), 3 moments:  +1e−15-scale at every w ∈ {0.10,…,0.29}
     N-stability (w=0.29):  −3.8e−15 (N=2400) / +5.3e−15 (N=4800)
     random admissible unit-mass g:  arch ≤ −4.99 across 20 draws
                                       (strictly negative, O(1) scale)

  constraint ablation (w=0.29):
     0 moments removed:   λ_max = +1.083332   (unconstrained scale)
     1 moment  (∫g = 0):  λ_max ≈ 0 to machine precision   ← THE KILLER
     2, 3 moments:        λ_max ≈ 0
```

**The archimedean sign field is EMPTY on the confined class**: no admissible
g has arch > 0; the spectrum tops out at 0 (machine zero, sign-flipping
under refinement = numerical zero, not a small positive).  The collapse is
caused by the MASS CONSTRAINT ALONE — ∫g = 0 suffices; the other two node
moments remove nothing further.

## 4. What this means

1. **The window-confined route to premise 1 is dead.**  The frame theorem's
   sign hypothesis `0 < arch((root h)²)` is unsatisfiable inside the class
   where the window readback `qw = −arch` is valid.  P1 is therefore forced
   into the FULL-book construction: drop confinement, restore the prime and
   spectral terms, and run the classical Weil/Yoshida negative test — where
   the sign comes from the true-zero spectral book, not from the arch side.
   The (a)-route of 1699 is not optional; it is the only remaining P1 route
   short of premise 2 itself.
2. **Paper-level statement this points at** (new-law candidate, F70):
   arch(g ⋆ g̃) ≤ 0 for every compactly supported smooth g with ∫g = 0 on
   [−w, w], w < 3/10 — with equality only in a degenerate limit (the top
   eigenvector approaches a one-sided trend shape, profile recorded in
   `1700b`).  If proved, this is the confined-class shadow of map 046's "no
   positive trace carries the sign": the arch book structurally CANNOT be
   the detector's positive side.  A candidate proof shape: with ∫g = 0,
   g = G′ for confined G, and the arch kernel (eʸ − e^{−y})⁻¹ integrates
   the square against a totally-monotone tail — a Krein/total-positivity
   argument is the natural first attempt.
3. Consistency: 1695/1696 (no positive trace carries the sign), 1699 (naive
   seeds fail; synthetic pair never dominates), 1700 (no confined seed can
   work AT ALL) — the sign keeps refusing every carrier; F67/F69/F70 now
   bracket it from the formal, domination, and sign-field sides.

## 5. Next

1. **F70 paper step**: prove (or refute) arch(g ⋆ g̃) ≤ 0 under ∫g = 0 on
   the confined class; identify whether w < 3/10 matters at all (the
   collapse was read at five widths uniformly).
2. **Unconfined P1**: price the classical full-book negative test — the
   test must now concentrate at a true off-line zero; the true-zero rig
   (mpmath `zetazero`, truncated explicit formula with smoothing
   discipline) becomes the required instrument.
3. Premise 2 remains the RH core; stop word unchanged: gate certificate.
