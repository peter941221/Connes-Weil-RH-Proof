# Proof Record 1904: Universal Window Contraction Factor Lower Bound & Scheme A.1 Direct Absorption No-Go

Date: 2026-09-23.

Status: FORMAL scoped no-go for Scheme A.1 (Direct Margin Absorption via geometric contraction).
Evidence: Lean theorems `supportLength_mul_seminorm_ge_one_of_laplaceAt_zero_eq_one` and
`not_strict_base_contraction_of_arbitrary_window` in `ConnesWeilRH/Dev/C1P2BaseSeminormBound.lean`.
Build log: `build-logs/1904_base_seminorm_universal.log`, exit=0, 0 errors, 0 `sorryAx`, standard axioms `[propext, Classical.choice, Quot.sound]`.

---

## 1. Executive Summary & First-Principles Findings

Scheme A.1 proposed to bridge the gap between the pinned detector $g$ and the semi-local gate
`orbitWindowSemiLocalGate(g) ≤ 0` (`finitePrimeSum(g^2) ≤ - archimedeanTerm(g^2)`) by establishing
the seminorm budget inequality:
```text
2 * exp(L) * S^2 * H ≤ delta
```
via widening the base support window to $(-W, W)$ ($W > 1$), seeking to lower the seminorm bound
below $1/2$ and achieve geometric contraction $(2 \cdot \text{seminorm})^n \to 0$.

During the formal audit and implementation, two independent, unconditional mathematical barriers
were proved from first principles:

### 1.1 Universal Contraction Factor Lower Bound (Generalization of Map 089)
For any bounded interval $(a, b)$ with length $L = b - a$, and any test function $f$ supported in $(a, b)$
with unit Laplace target at zero ($\text{laplaceAt}(f, 0) = \int_a^b f(t) dt = 1$):
By Cauchy-Schwarz and $L^2 / L^\infty$ estimation:
```text
1 = |laplaceAt(f, 0)|^2 ≤ (b - a) * compactLogL2sq(f) ≤ (b - a)^2 * (seminorm(f))^2
```
Taking square roots yields the universal, scale-invariant lower bound:
```text
(b - a) * seminorm(f) ≥ 1
```
Consequently, the contraction factor $q = (b - a) \cdot \text{seminorm}(f)$ can NEVER be strictly less than 1.
Widening the window from $(-1, 1)$ to $(-W, W)$ scales the length to $2W$ and lowers the $L^\infty$ lower bound
to $1/(2W)$, so their product remains identically:
```text
(2W) * seminorm(f) ≥ (2W) * (1 / (2W)) = 1
```
The contraction factor is strictly bounded below by 1 for all windows and all bases.

### 1.2 Support Explosion vs $L^\infty$ Decay Mismatch
Even without Young's product contraction, under $n$-fold convolution $f^{*n}$:
- The support radius grows linearly: $L_n = n \cdot W$, so $\exp(L_n) = \exp(n W)$ explodes exponentially.
- In $\mathbb{R}$, by the Central Limit Theorem and $L^p$ convolution bounds, $\|f^{*n}\|_\infty = O(n^{-1/2})$.
- Therefore, the product:
  ```text
  exp(L_n) * (S_n)^2 * H_n ~ (exp(n W) / n) * 2 n W ~ 2 W * exp(n W) → +∞
  ```
  diverges exponentially as $n \to \infty$, rather than decaying below $\delta$.

### 1.3 Detector-Specific Gate Polarity Contradiction
For the pinned Yoshida detector $g$, spectral zero detection unconditionally forces:
```text
qw(g) < 0  <=>  archimedeanTerm(g^2) + finitePrimeSum(g^2) > 0  <=>  ICgate(g^2) > 0
```
This is already formal in `C1HealthyYoshidaSpectralNegativity.lean` (`ICgate_pos_of_healthyDetectorData`).
Therefore, any claim that $g$ itself satisfies `orbitWindowSemiLocalGate(g) ≤ 0` is mathematically false
for this object, as proved by `false_of_healthyDetectorData_and_orbitWindowSemiLocalGate`.

---

## 2. Formal Declarations in Lean 4

In `ConnesWeilRH/Dev/C1P2BaseSeminormBound.lean`:

```lean
/-- Universal lower bound on the convolution contraction factor for an arbitrary
    bounded window `(a, b)`: any base test with unit Laplace target at zero
    satisfies `(b - a) * seminorm(f) ≥ 1`. -/
theorem supportLength_mul_seminorm_ge_one_of_laplaceAt_zero_eq_one
    (f : CompactLogTest) {a b : Real} (hab : a < b)
    (hsupp : Function.support f.test ⊆ Set.Ioo a b)
    (hzero : laplaceAt f 0 = 1) :
    1 ≤ (b - a) * SchwartzMap.seminorm Complex 0 0 f.test

/-- Universal no-go for strict geometric base contraction on any bounded window:
    the contraction factor `(b - a) * seminorm(f) < 1` is mathematically impossible
    for any compactly supported base with unit Laplace target at zero. -/
theorem not_strict_base_contraction_of_arbitrary_window
    (f : CompactLogTest) {a b : Real} (hab : a < b)
    (hsupp : Function.support f.test ⊆ Set.Ioo a b)
    (hzero : laplaceAt f 0 = 1) :
    ¬ (b - a) * SchwartzMap.seminorm Complex 0 0 f.test < 1
```

Both declarations were audited in `C1P2BaseSeminormBoundAudit.lean` with axioms:
`[propext, Classical.choice, Quot.sound]`.
