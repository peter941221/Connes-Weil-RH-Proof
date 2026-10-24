import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1C3SigmaKernel
import ConnesWeilRH.Dev.C1P2OrbitPhysicalProfileReadback
import ConnesWeilRH.Dev.C1P2SignedBudget

/-!
# Route A same-owner joint-symbol data

This module defines the frequency symbol from an actual `OrbitG8Geometry`.
It proves a uniform pointwise bound for the finite prime part. It does not
identify `qw` with a frequency integral or assert a sign for that integral.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAJointSymbolData3080

open C1G8R0OrbitGeometry
open C1P2SignedBudget
open C1P2OrbitPhysicalProfileReadback
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open scoped BigOperators

noncomputable section

/-- Primes are derived from this geometry's support-owned prime-power range. -/
def routeAVisiblePrimes {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Finset Nat :=
  (orbitVisiblePrimeRange geometry).filter Nat.Prime

/-- The unscaled orbit transform on the critical line, owned by `geometry`. -/
def routeAOrbitTransform {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Complex :=
  CompactLogTest.laplaceAt (orbitRawFactor geometry)
    (((1 / 2 : Real) : Complex) + (xi : Complex) * Complex.I)

theorem routeAOrbitTransform_eq_selectedSourceLaplace
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    routeAOrbitTransform geometry xi =
      CompactLogTest.laplaceAt g ((xi : Complex) * Complex.I) := by
  change CompactLogTest.laplaceAt
      ((convolutionIterate geometry.base geometry.orbitIndex).convolution
        geometry.correction)
      (((1 / 2 : Real) : Complex) + (xi : Complex) * Complex.I) = _
  have h := selectedOwner_laplaceAt_sourceTest_centered
    geometry.base geometry.correction geometry.orbitIndex
    (((1 / 2 : Real) : Complex) + (xi : Complex) * Complex.I)
  have hsource :
      CompactLogTest.laplaceAt g
          ((((1 / 2 : Real) : Complex) + (xi : Complex) * Complex.I) - 1 / 2) =
        CompactLogTest.laplaceAt
          ((convolutionIterate geometry.base geometry.orbitIndex).convolution
            geometry.correction)
          (((1 / 2 : Real) : Complex) + (xi : Complex) * Complex.I) := by
    simpa only [geometry.selected_owner_test] using h
  have hcenter :
      (((1 / 2 : Real) : Complex) + (xi : Complex) * Complex.I) - 1 / 2 =
        (xi : Complex) * Complex.I := by
    norm_num
  rw [hcenter] at hsource
  simpa [orbitRawFactor] using hsource.symm

/-- The prime Poisson multiplier appearing in the joint-symbol formula. -/
def routeAPrimePoissonSymbol (p : Nat) (xi : Real) : Real :=
  let r : Real := 1 / Real.sqrt (p : Real)
  (1 - r ^ 2) /
      (1 - 2 * r * Real.cos (Real.log (p : Real) * xi) + r ^ 2) - 1

/-- The joint symbol keeps the archimedean term and all visible primes in one
scalar expression. -/
def routeAJointSymbol {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  -Dev.c3Sigma xi -
    ∑ p ∈ routeAVisiblePrimes geometry,
      Real.log (p : Real) * routeAPrimePoissonSymbol p xi

/-- The frequency-side quadratic density for this geometry. -/
def routeAFrequencyEnergyDensity
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  routeAJointSymbol geometry xi *
    ‖routeAOrbitTransform geometry xi‖ ^ 2

/-- The nonnegative part of the same owner's frequency density. -/
def routeAFrequencyCreditDensity
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  max 0 (routeAJointSymbol geometry xi) *
    ‖routeAOrbitTransform geometry xi‖ ^ 2

/-- The magnitude of the negative part of the same owner's frequency density. -/
def routeAFrequencyDeficitDensity
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) : Real :=
  max 0 (-routeAJointSymbol geometry xi) *
    ‖routeAOrbitTransform geometry xi‖ ^ 2

/-- The negative-sign frequency band of the actual geometry's joint symbol. -/
def routeANegativeSymbolBand
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Set Real :=
  {xi | routeAJointSymbol geometry xi < 0}

theorem routeAJointSymbol_eq_posPart_sub_negPart (x : Real) :
    x = max 0 x - max 0 (-x) := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx, max_eq_left (neg_nonpos.mpr hx)]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_left hx', max_eq_right (neg_nonneg.mpr hx')]
    ring

theorem routeAFrequencyEnergyDensity_eq_credit_sub_deficit
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    routeAFrequencyEnergyDensity geometry xi =
      routeAFrequencyCreditDensity geometry xi -
        routeAFrequencyDeficitDensity geometry xi := by
  unfold routeAFrequencyEnergyDensity routeAFrequencyCreditDensity
    routeAFrequencyDeficitDensity
  calc
    routeAJointSymbol geometry xi * ‖routeAOrbitTransform geometry xi‖ ^ 2 =
        (max 0 (routeAJointSymbol geometry xi) -
          max 0 (-routeAJointSymbol geometry xi)) *
            ‖routeAOrbitTransform geometry xi‖ ^ 2 := by
      exact congrArg (fun z : Real => z * ‖routeAOrbitTransform geometry xi‖ ^ 2)
        (routeAJointSymbol_eq_posPart_sub_negPart
          (routeAJointSymbol geometry xi))
    _ = max 0 (routeAJointSymbol geometry xi) *
          ‖routeAOrbitTransform geometry xi‖ ^ 2 -
        max 0 (-routeAJointSymbol geometry xi) *
          ‖routeAOrbitTransform geometry xi‖ ^ 2 := by ring

theorem routeAFrequencyCreditDensity_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    0 ≤ routeAFrequencyCreditDensity geometry xi := by
  unfold routeAFrequencyCreditDensity
  positivity

theorem routeAFrequencyDeficitDensity_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    0 ≤ routeAFrequencyDeficitDensity geometry xi := by
  unfold routeAFrequencyDeficitDensity
  positivity

theorem routeAFrequencyEnergyDensity_nonneg_of_jointSymbol_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real)
    (hsymbol : 0 ≤ routeAJointSymbol geometry xi) :
    0 ≤ routeAFrequencyEnergyDensity geometry xi := by
  unfold routeAFrequencyEnergyDensity
  positivity

/-- The elementary absolute envelope for one prime's Poisson multiplier. -/
def routeAPrimePoissonAllowance (p : Nat) : Real :=
  let r : Real := 1 / Real.sqrt (p : Real)
  2 * r / (1 - r)

/-- The total prime-symbol allowance belongs to the same geometry as the
joint symbol. -/
def routeAJointSymbolPrimeAllowance
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) : Real :=
  ∑ p ∈ routeAVisiblePrimes geometry,
    Real.log (p : Real) * routeAPrimePoissonAllowance p

theorem routeAPrimePoissonSymbol_abs_le (p : Nat) (hp : Nat.Prime p)
    (xi : Real) :
    |routeAPrimePoissonSymbol p xi| ≤ routeAPrimePoissonAllowance p := by
  let r : Real := 1 / Real.sqrt (p : Real)
  let c : Real := Real.cos (Real.log (p : Real) * xi)
  let d : Real := 1 - 2 * r * c + r ^ 2
  have hpcast : (1 : Real) < (p : Real) := by
    exact_mod_cast hp.one_lt
  have hsqrt : 1 < Real.sqrt (p : Real) := by
    have hsquare := Real.sq_sqrt (show 0 ≤ (p : Real) by positivity)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (p : Real) := Real.sqrt_nonneg _
    by_contra h
    have hle : Real.sqrt (p : Real) ≤ 1 := le_of_not_gt h
    nlinarith [sq_nonneg (1 - Real.sqrt (p : Real)), hsqrt_nonneg]
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hrlt : r < 1 := by
    dsimp [r]
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr (show 0 < (p : Real) by positivity))]
    simpa using hsqrt
  have hcosUpper : r * c ≤ r := by
    nlinarith [Real.cos_le_one (Real.log (p : Real) * xi)]
  have hcosLower : -r ≤ r * c := by
    nlinarith [Real.neg_one_le_cos (Real.log (p : Real) * xi)]
  have hdLower : (1 - r) ^ 2 ≤ d := by
    dsimp [d]
    nlinarith [hcosUpper]
  have hdUpper : d ≤ (1 + r) ^ 2 := by
    dsimp [d]
    nlinarith [hcosLower]
  have hdpos : 0 < d := by
    have hpos : 0 < (1 - r) ^ 2 := sq_pos_of_pos (by linarith)
    exact lt_of_lt_of_le hpos hdLower
  have hdenLower : 0 < 1 - r := by linarith
  have hdenUpper : 0 < 1 + r := by linarith
  have hquotUpper : (1 - r ^ 2) / d ≤ (1 + r) / (1 - r) := by
    apply (div_le_div_iff₀ hdpos hdenLower).2
    nlinarith [mul_le_mul_of_nonneg_left hdLower (le_of_lt hdenUpper)]
  have hquotLower : (1 - r) / (1 + r) ≤ (1 - r ^ 2) / d := by
    apply (div_le_div_iff₀ hdenUpper hdpos).2
    nlinarith [mul_le_mul_of_nonneg_left hdUpper (le_of_lt hdenLower)]
  have hupperRewrite : (1 + r) / (1 - r) - 1 = 2 * r / (1 - r) := by
    field_simp
    ring
  have hlowerRewrite : 1 - (1 - r) / (1 + r) = 2 * r / (1 + r) := by
    field_simp
    ring
  have hbound :
      -(2 * r / (1 + r)) ≤ routeAPrimePoissonSymbol p xi ∧
        routeAPrimePoissonSymbol p xi ≤ 2 * r / (1 - r) := by
    have hsymbol :
        routeAPrimePoissonSymbol p xi = (1 - r ^ 2) / d - 1 := by
      simp [routeAPrimePoissonSymbol, r, c, d]
    constructor
    · rw [hsymbol]
      calc
        -(2 * r / (1 + r)) = (1 - r) / (1 + r) - 1 := by linarith [hlowerRewrite]
        _ ≤ (1 - r ^ 2) / d - 1 := sub_le_sub_right hquotLower 1
    · rw [hsymbol]
      calc
        (1 - r ^ 2) / d - 1 ≤ (1 + r) / (1 - r) - 1 := sub_le_sub_right hquotUpper 1
        _ = 2 * r / (1 - r) := hupperRewrite
  have hsymm : 2 * r / (1 + r) ≤ 2 * r / (1 - r) := by
    apply (div_le_div_iff₀ hdenUpper hdenLower).2
    nlinarith [hrpos]
  change |routeAPrimePoissonSymbol p xi| ≤ 2 * r / (1 - r)
  rw [abs_le]
  constructor
  · calc
      -(2 * r / (1 - r)) ≤ -(2 * r / (1 + r)) := neg_le_neg hsymm
      _ ≤ routeAPrimePoissonSymbol p xi := by
        exact hbound.1
  · exact hbound.2

theorem routeAPrimePoissonAllowance_pos (p : Nat) (hp : Nat.Prime p) :
    0 < routeAPrimePoissonAllowance p := by
  let r : Real := 1 / Real.sqrt (p : Real)
  have hpcast : (1 : Real) < (p : Real) := by exact_mod_cast hp.one_lt
  have hsqrt : 1 < Real.sqrt (p : Real) := by
    have hsquare := Real.sq_sqrt (show 0 ≤ (p : Real) by positivity)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (p : Real) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (1 - Real.sqrt (p : Real)), hsqrt_nonneg]
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr (show 0 < (p : Real) by positivity))]
    simpa using hsqrt
  unfold routeAPrimePoissonAllowance
  dsimp [r]
  exact div_pos (by positivity) (by linarith)

theorem routeAJointSymbolPrimeAllowance_nonneg
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    0 ≤ routeAJointSymbolPrimeAllowance geometry := by
  unfold routeAJointSymbolPrimeAllowance
  apply Finset.sum_nonneg
  intro p hp
  apply mul_nonneg
  · apply Real.log_nonneg
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact_mod_cast hprime.one_le
  · exact (routeAPrimePoissonAllowance_pos p
      (Finset.mem_filter.mp hp).2).le

theorem routeAJointSymbol_primePart_abs_le
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    |∑ p ∈ routeAVisiblePrimes geometry,
        Real.log (p : Real) * routeAPrimePoissonSymbol p xi| ≤
      routeAJointSymbolPrimeAllowance geometry := by
  unfold routeAJointSymbolPrimeAllowance
  calc
    |∑ p ∈ routeAVisiblePrimes geometry,
        Real.log (p : Real) * routeAPrimePoissonSymbol p xi| ≤
      ∑ p ∈ routeAVisiblePrimes geometry,
        |Real.log (p : Real) * routeAPrimePoissonSymbol p xi| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ routeAVisiblePrimes geometry,
        Real.log (p : Real) * routeAPrimePoissonAllowance p := by
          apply Finset.sum_le_sum
          intro p hp
          have hlog : 0 ≤ Real.log (p : Real) := by
            apply Real.log_nonneg
            have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
            exact_mod_cast hprime.one_le
          calc
            |Real.log (p : Real) * routeAPrimePoissonSymbol p xi| =
                Real.log (p : Real) *
                  |routeAPrimePoissonSymbol p xi| := by
                    rw [abs_mul, abs_of_nonneg hlog]
            _ ≤ Real.log (p : Real) * routeAPrimePoissonAllowance p :=
              mul_le_mul_of_nonneg_left
                (routeAPrimePoissonSymbol_abs_le p
                  (Finset.mem_filter.mp hp).2 xi) hlog

theorem routeAJointSymbol_lower_bound
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real) :
    -Dev.c3Sigma xi - routeAJointSymbolPrimeAllowance geometry ≤
      routeAJointSymbol geometry xi := by
  unfold routeAJointSymbol
  have h := routeAJointSymbol_primePart_abs_le geometry xi
  have hupper :
      ∑ p ∈ routeAVisiblePrimes geometry,
        Real.log (p : Real) * routeAPrimePoissonSymbol p xi ≤
        routeAJointSymbolPrimeAllowance geometry := (abs_le.mp h).2
  linarith

theorem routeAJointSymbol_nonneg_of_archimedean_margin
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (xi : Real)
    (harch : routeAJointSymbolPrimeAllowance geometry ≤ -Dev.c3Sigma xi) :
    0 ≤ routeAJointSymbol geometry xi := by
  have h := routeAJointSymbol_lower_bound geometry xi
  linarith

private theorem exists_c3Sigma_below_neg (B : Real) :
    ∃ xi : Real, 0 ≤ xi ∧ Dev.c3Sigma xi < -B := by
  have hdiv :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
      (Filter.eventually_gt_atTop (2 * (B + 13)))
  obtain ⟨K, hK⟩ := hdiv.exists
  let xi : Real := 2 * ((K : Real) + 1)
  have hterm : ∀ n ∈ Finset.range K,
      (1 / 2 : Real) * (1 / ((n : Real) + 1)) ≤
        (xi / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2)) := by
    intro n hn
    have hnK : n < K := Finset.mem_range.mp hn
    let a : Real := (n : Real) + 1 / 4
    let b : Real := (n : Real) + 1
    let x : Real := xi / 2
    have ha : 0 < a := by dsimp [a]; positivity
    have hb : 0 < b := by dsimp [b]; positivity
    have hxab : a ≤ b := by dsimp [a, b]; norm_num
    have hnb : b ≤ x := by
      dsimp [b, x, xi]
      have hcast : (n : Real) + 1 ≤ (K : Real) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hnK)
      linarith
    have hax : a ≤ x := hxab.trans hnb
    have hsq : a ^ 2 ≤ x ^ 2 := by
      nlinarith [sq_nonneg (x - a)]
    have hden₁ : 0 < 2 * b := by positivity
    have hden₂ : 0 < a * (a ^ 2 + x ^ 2) := by positivity
    have hrewrite : (1 / 2 : Real) * (1 / b) = 1 / (2 * b) := by
      field_simp
    rw [hrewrite]
    change 1 / (2 * b) ≤ x ^ 2 / (a * (a ^ 2 + x ^ 2))
    apply (div_le_div_iff₀ hden₁ hden₂).2
    calc
      1 * (a * (a ^ 2 + x ^ 2)) ≤
          1 * (b * (a ^ 2 + x ^ 2)) := by gcongr
      _ ≤ 1 * (b * (2 * x ^ 2)) := by
        gcongr
        nlinarith
      _ = x ^ 2 * (2 * b) := by ring
  have hK' : 2 * (B + 13) <
      ∑ n ∈ Finset.range K, (1 / ((n : Real) + 1) : Real) := by
    simpa using hK
  have hhalf : B + 13 <
      ∑ n ∈ Finset.range K, (1 / 2 : Real) * (1 / ((n : Real) + 1)) := by
    have heq :
        (∑ n ∈ Finset.range K,
            (1 / 2 : Real) * (1 / ((n : Real) + 1))) =
          (1 / 2 : Real) *
            (∑ n ∈ Finset.range K, (1 / ((n : Real) + 1) : Real)) := by
      rw [Finset.mul_sum]
    rw [heq]
    nlinarith [hK']
  have hsum :
      (∑ n ∈ Finset.range K,
          (1 / 2 : Real) * (1 / ((n : Real) + 1))) ≤
        ∑ n ∈ Finset.range K,
          (xi / 2) ^ 2 /
            (((n : Real) + 1 / 4) *
              (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2)) := by
    exact Finset.sum_le_sum (fun n hn => hterm n hn)
  have hsum' : B + 13 <
      ∑ n ∈ Finset.range K,
        (xi / 2) ^ 2 /
          (((n : Real) + 1 / 4) *
            (((n : Real) + 1 / 4) ^ 2 + (xi / 2) ^ 2)) :=
    lt_of_lt_of_le hhalf hsum
  have hfinite := Dev.c3Sigma_le_at_zero_sub_finite_sum xi K
  dsimp [xi] at hfinite hsum'
  refine ⟨2 * ((K : Real) + 1), ?_, ?_⟩
  · positivity
  · calc
      Dev.c3Sigma (2 * ((K : Real) + 1)) ≤
          Dev.c3Sigma 0 -
            ∑ n ∈ Finset.range K,
              ((2 * ((K : Real) + 1) / 2) ^ 2 /
                (((n : Real) + 1 / 4) *
                  (((n : Real) + 1 / 4) ^ 2 +
                    (2 * ((K : Real) + 1) / 2) ^ 2))) := hfinite
      _ < -B := by
        have hsum'' : B + 13 <
            ∑ n ∈ Finset.range K,
              ((2 * ((K : Real) + 1) / 2) ^ 2 /
                (((n : Real) + 1 / 4) *
                  (((n : Real) + 1 / 4) ^ 2 +
                    (2 * ((K : Real) + 1) / 2) ^ 2))) := by
          exact hsum'
        linarith [Dev.c3Sigma_zero_lt_twelve]

theorem exists_routeAJointSymbol_nonneg_tail
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    ∃ T : Real, 0 ≤ T ∧ ∀ xi : Real, T ≤ |xi| →
      0 ≤ routeAJointSymbol geometry xi := by
  let C := routeAJointSymbolPrimeAllowance geometry
  have hC : 0 ≤ C := routeAJointSymbolPrimeAllowance_nonneg geometry
  obtain ⟨T, hT, hbelow⟩ := exists_c3Sigma_below_neg C
  refine ⟨T, hT, ?_⟩
  intro xi hxi
  have hEven : Dev.c3Sigma xi = Dev.c3Sigma |xi| := by
    by_cases hnonneg : 0 ≤ xi
    · rw [abs_of_nonneg hnonneg]
    · have hneg : xi < 0 := lt_of_not_ge hnonneg
      rw [abs_of_neg hneg]
      exact (Dev.c3Sigma_neg_eq xi).symm
  have hmono : Dev.c3Sigma |xi| ≤ Dev.c3Sigma T :=
    Dev.c3Sigma_antitone_of_nonneg hT hxi
  have hxiBound : Dev.c3Sigma xi < -C := by
    rw [hEven]
    exact lt_of_le_of_lt hmono hbelow
  have hmargin : C ≤ -Dev.c3Sigma xi := by linarith
  simpa [C] using
    routeAJointSymbol_nonneg_of_archimedean_margin geometry xi hmargin

theorem routeAFrequencyEnergyDensity_nonneg_on_jointSymbol_tail
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) {T xi : Real}
    (hT : T ≤ |xi|)
    (hTtail : ∀ eta : Real, T ≤ |eta| →
      0 ≤ routeAJointSymbol geometry eta) :
    0 ≤ routeAFrequencyEnergyDensity geometry xi := by
  exact routeAFrequencyEnergyDensity_nonneg_of_jointSymbol_nonneg
    geometry xi (hTtail xi hT)

theorem routeANegativeSymbolBand_subset_Icc_of_nonneg_tail
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) (T : Real)
    (hT : 0 ≤ T)
    (hTail : ∀ xi : Real, T ≤ |xi| →
      0 ≤ routeAJointSymbol geometry xi) :
    routeANegativeSymbolBand geometry ⊆ Set.Icc (-T) T := by
  intro xi hxi
  change routeAJointSymbol geometry xi < 0 at hxi
  have habs : |xi| < T := by
    by_contra hnot
    have hle : T ≤ |xi| := le_of_not_gt hnot
    exact (not_lt_of_ge (hTail xi hle)) hxi
  have hcoords := abs_lt.mp habs
  exact ⟨le_of_lt hcoords.1, le_of_lt hcoords.2⟩

theorem routeANegativeSymbolBand_is_bounded
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    ∃ T : Real, 0 ≤ T ∧
      routeANegativeSymbolBand geometry ⊆ Set.Icc (-T) T := by
  obtain ⟨T, hT, hTail⟩ := exists_routeAJointSymbol_nonneg_tail geometry
  exact ⟨T, hT,
    routeANegativeSymbolBand_subset_Icc_of_nonneg_tail geometry T hT hTail⟩

end
end C1RouteAJointSymbolData3080
end Source
end ConnesWeilRH
