# Proof Record 1905: Two-Point Differential Annihilation & Spectral Orbit Decomposition

Date: 2026-09-23.

Status: FORMAL milestone; Stages 1 and 2 of the Two-Span Spectral Contradiction route closed without gaps.
Evidence: `ConnesWeilRH/Dev/C1TwoPointDifferentialAnnihilator.lean`,
`ConnesWeilRH/Dev/C1TwoPointSpectralDecomposition.lean`, and paired audits.
Build logs: `build-logs/1905_spectral_annihilator.log` (3619 jobs) and `build-logs/1905_spectral_decomposition.log` (3807 jobs),
both exit=0, zero error lines, zero `sorryAx`, standard axioms `[propext, Classical.choice, Quot.sound]`.

---

## 1. Mathematical Objective & First-Principles Architecture

Following the formal scoped no-go for scalar $L^\infty$ convolution contraction in Proof Record 1904,
the project pivoted to the two-span spectral contradiction route.

To create a direct spectral mismatch against the hypothetical off-line zero $\rho$ ($\mathrm{Re}(\rho) > 1/2$):
1. **Differential Annihilation**: Construct an operator that algebraically vanishes at the off-line zero
   $\rho - 1/2$ and its functional-equation companion $1 - \bar{\rho} - 1/2$, while preserving the triple vanishing
   on $\{0, 1/2, 1\}$ and strictly preserving the compact support radius (so the test remains completely prime-free).
2. **Spectral Orbit Pairing**: In the span $v(\lambda) = u_a - \lambda g$, where $u_a$ is the annihilated narrow test
   and $g$ is the pinned Yoshida detector:
   - At $\rho - 1/2$: $\text{laplaceAt}(v(\lambda), \rho - 1/2) = -\lambda$;
   - At $1 - \bar{\rho} - 1/2$: $\text{laplaceAt}(v(\lambda), 1 - \bar{\rho} - 1/2) = +\lambda$;
   - The paired Hermitian product is identically $- \lambda^2 \le 0$.

---

## 2. Formal Declarations & Theorems

### 2.1 Two-Point Differential Annihilator (`C1TwoPointDifferentialAnnihilator.lean`)

```lean
/-- The two-point differential annihilator: composing two Laplace-side derivative shifts
    at nodes `z1` and `z2`. -/
def twoPointDerivativeAnnihilator (f : CompactLogTest) (z1 z2 : ℂ) : CompactLogTest :=
  derivativeShift (derivativeShift f z1) z2

theorem laplaceAt_twoPointDerivativeAnnihilator (f : CompactLogTest) (z1 z2 s : ℂ) :
    laplaceAt (twoPointDerivativeAnnihilator f z1 z2) s =
      (z2 - s) * (z1 - s) * laplaceAt f s

@[simp] theorem twoPointDerivativeAnnihilator_laplaceAt_z1 (f : CompactLogTest) (z1 z2 : ℂ) :
    laplaceAt (twoPointDerivativeAnnihilator f z1 z2) z1 = 0

@[simp] theorem twoPointDerivativeAnnihilator_laplaceAt_z2 (f : CompactLogTest) (z1 z2 : ℂ) :
    laplaceAt (twoPointDerivativeAnnihilator f z1 z2) z2 = 0

theorem twoPointDerivativeAnnihilator_vanishesOn_cc20Triple (f : CompactLogTest) (z1 z2 : ℂ)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet f) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (twoPointDerivativeAnnihilator f z1 z2)

theorem twoPointDerivativeAnnihilator_support_subset_Icc (f : CompactLogTest) (z1 z2 : ℂ) {w : ℝ}
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w) :
    Function.support ((twoPointDerivativeAnnihilator f z1 z2).test : ℝ → ℂ) ⊆ Set.Icc (-w) w

theorem twoPointDerivativeAnnihilator_finitePrimeSum_eq_zero (f : CompactLogTest) (z1 z2 : ℂ) {w : ℝ}
    (hsupport : Function.support (f.test : ℝ → ℂ) ⊆ Set.Icc (-w) w) (hw : w < (3 / 10 : ℝ)) :
    finitePrimeSum (twoPointDerivativeAnnihilator f z1 z2).convolutionSquare = 0
```

### 2.2 Spectral Decomposition on the Span (`C1TwoPointSpectralDecomposition.lean`)

```lean
def annihilatorDetectorSpanVector (u_a g : CompactLogTest) (lambda : Real) : CompactLogTest :=
  spanObj ![u_a, g] ![(1 : Real), -lambda]

theorem laplaceAt_annihilatorDetectorSpanVector_at_rho_sub_half
    (u_a g : CompactLogTest) (lambda : Real) (rho : ℂ)
    (hu : laplaceAt u_a (rho - 1 / 2) = 0)
    (hg : laplaceAt g (rho - 1 / 2) = 1) :
    laplaceAt (annihilatorDetectorSpanVector u_a g lambda) (rho - 1 / 2) = -(lambda : ℂ)

theorem laplaceAt_annihilatorDetectorSpanVector_at_one_sub_star_rho_sub_half
    (u_a g : CompactLogTest) (lambda : Real) (rho : ℂ)
    (hu : laplaceAt u_a (1 - star rho - 1 / 2) = 0)
    (hg : laplaceAt g (1 - star rho - 1 / 2) = -1) :
    laplaceAt (annihilatorDetectorSpanVector u_a g lambda) (1 - star rho - 1 / 2) = (lambda : ℂ)

theorem pairedProduct_annihilatorDetectorSpanVector_eq_neg_sq
    (u_a g : CompactLogTest) (lambda : Real) (rho : ℂ)
    (hu1 : laplaceAt u_a (rho - 1 / 2) = 0)
    (hg1 : laplaceAt g (rho - 1 / 2) = 1)
    (hu2 : laplaceAt u_a (1 - star rho - 1 / 2) = 0)
    (hg2 : laplaceAt g (1 - star rho - 1 / 2) = -1) :
    star (laplaceAt (annihilatorDetectorSpanVector u_a g lambda) (1 - star rho - 1 / 2)) *
        laplaceAt (annihilatorDetectorSpanVector u_a g lambda) (rho - 1 / 2) =
      -((lambda : ℂ) ^ 2)
```

Both modules audited clean under standard axioms `[propext, Classical.choice, Quot.sound]`.
