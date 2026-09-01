import ConnesWeilRH.Dev.C1HealthyDetectorPinning
import ConnesWeilRH.Dev.C1CC20ArchimedeanReadback
import ConnesWeilRH.Dev.C1HealthyYoshidaUnscaledOrbit
import ConnesWeilRH.Dev.C1SpectralTailBound

/-!
# C1HealthyDetectorRootSupportExit - consumer #3 in its capstone-consumable form

This module advances consumer 3 of `RH_MAINLINE_FREEZE.md`: *detector-specific
semi-local positivity on the same healthy owner*.

The unconditional spectral-negativity construction
(`C1HealthyYoshidaSpectralNegativity`) already produces
`HealthyYoshidaDetectorData` for every off-line source zero oriented to the
right of the critical line, but its owner is an n-fold convolution orbit whose
support leaves the ROOT window.  The capstone
`sourceRH_of_rootSupportedHealthyDetectorData_and_endpointCertificates`
consumes the detector data only together with ROOT support, because the CC20
endpoint certificate is proved exactly on root-supported tests.  Consumer 3 is
therefore precisely the root-support transport of the strict spectral sign:

    rootSupportedHealthyDetectorGate rho :=
      exists g, HealthyYoshidaDetectorData rho g /\
                support g.test ⊆ [-log 2 / 2, log 2 / 2]

What lands here:

1. the gate as a named proposition, in the exact shape the capstone consumes;
2. the C2 -> C3 glue: the pinned-detector archimedean gate of record 1080
   implies the root-supported gate;
3. the RH exit composition: right-representative root-supported gates plus the
   CC20 endpoint certificates imply `SourceRH` (the two signs meet on one
   root-supported test, mirroring the existing route guard);
4. a damper-free fourth-order tail: for EVERY compact-log test the
   half-density square satisfies `FourthOrderSpectralTail` with an explicit
   threshold and size, derived from the proved uniform quadratic vertical
   decay alone - no n-fold base damping.  The library's selected-owner tail
   needs the n-fold orbit to regulate its tail size; this theorem shows the
   TAIL side is root-support-compatible in principle.  The remaining
   root-support obstruction is isolated on the prefix side: the ball-radius
   interpolation constants versus the geometric shell budget.

RH is NOT claimed; the root-supported gate stays open.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyDetectorRootSupportExit

open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open C1HealthyYoshidaDetector
open C1HealthyYoshidaMinimalInterpolation
open C1SameOwnerWeil
open C1HealthyDetectorPinning
open C1CC20ArchimedeanReadback
open C1HealthyYoshidaUnscaledOrbit
open C1SpectralTailBound
open C1SpectralWeil

/-! ### Small complex-algebra helpers -/

private theorem re_add_im_I (z : Complex) :
    z = (z.re : Complex) + (z.im : Real) * Complex.I := by
  apply Complex.ext
  · simp
  · simp

/-! ### The consumer-3 gate in capstone form -/

/-- The root-support transport of the strict detector sign, stated exactly as
the healthy-owner RH capstone consumes it.  This is consumer 3's remaining
obligation: the unconditional spectral-negativity construction supplies the
data package away from the ROOT window, and the CC20 endpoint certificate
route needs it on the ROOT window. -/
def rootSupportedHealthyDetectorGate (rho : Complex) : Prop :=
  ∃ g : CompactLogTest,
    HealthyYoshidaDetectorData rho g /\
      Function.support g.test ⊆
        Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)

/-- The 1080 handoff glue: on a pinned detector the archimedean gate implies
the root-supported gate, since pinning already carries the explicit support
radius. -/
theorem rootSupportedGate_of_selectedDetectorArchimedeanGate
    {rho : Complex} {g : CompactLogTest}
    (hpinned : HealthyMinimalLaplaceRealizes rho g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hgate : selectedDetectorArchimedeanGate rho g) :
    rootSupportedHealthyDetectorGate rho :=
  ⟨g, (healthyDetectorData_iff_selectedDetectorArchimedeanGate hpinned
    hsupport).mpr hgate, hsupport⟩

/-! ### The RH exit composition -/

/-- Right-representative root-supported detector gates plus the CC20 endpoint
certificates imply `SourceRH`.  For an off-line zero take its functional-
equation representative strictly right of the critical line, its root-
supported detector, and the endpoint certificate for that same test: the
certificate forces `0 <= qw g` while the detector data forces
`qw g = spectralWeilValue g.convolutionSquare < 0`.  The detection field is
not consumed; only the two signs meet on one root-supported test. -/
theorem sourceRH_of_rootSupportedGate_rightRep_and_endpointCertificates
    (hgate : forall sigma : sourceNontrivialZeroSet,
      (1 / 2 : Real) < sigma.1.re ->
        rootSupportedHealthyDetectorGate sigma.1)
    (hendpoint : forall g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace
          cc20TripleFiniteVanishingSet g ->
        Function.support g.test ⊆
            Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2) ->
          Nonempty (CC20EndpointTraceCertificate g)) :
    RHDefinitionBridge.standard.SourceRH := by
  intro rho hrho
  by_cases hline : rho.re = 1 / 2
  · simpa [RHDefinitionBridge.standard] using hline
  · obtain ⟨sigma, hright, _, _⟩ :=
      exists_rightOfCriticalXiZero_of_re_ne_half ⟨rho, hrho⟩ hline
    obtain ⟨g, hdetector, hsupport⟩ := hgate sigma hright
    obtain ⟨hcertificate⟩ := hendpoint g hdetector.vanishesOnF hsupport
    have hqwNonnegative : 0 ≤ C1SameOwnerWeil.qw g :=
      qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
        g hdetector.vanishesOnF hsupport hcertificate
    have hspectralNegative :
        C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0 :=
      (C1HealthyYoshidaDetector.weilSquareSumPositive_iff_spectralWeilValue_neg g).mp
        hdetector.weilSquareSumPositive
    have hqwNegative : C1SameOwnerWeil.qw g < 0 := by
      rw [C1CenterTwoCriterionBridge.qw_eq_spectralWeilValue_centerTwo]
      exact hspectralNegative
    exact False.elim ((not_lt_of_ge hqwNonnegative) hqwNegative)

/-! ### The damper-free fourth-order tail -/

/-- DAMPER-FREE TAIL.  For every compact-log test `h` and every strip anchor
`rho` there are an explicit threshold `T` and size `epsilon > 0` such that the
half-density square satisfies the fourth-order spectral tail condition.  Only
the proved uniform quadratic vertical decay is used: the Hermitian product
turns two quadratic factors into the fourth-order decay, so no n-fold base
damping is needed.  This removes the selected-owner orbit from the TAIL side
of the spectral-sign construction; the remaining root-support obstruction
sits on the prefix side. -/
theorem exists_fourthOrderTail_halfDensityShift_convolutionSquare
    (h : CompactLogTest) (rho : Complex)
    (hrhoRe : rho.re ∈ Set.Icc (0 : Real) 1) :
    ∃ T : Real, ∃ epsilon : Real, 0 ≤ T ∧ 0 < epsilon ∧
      FourthOrderSpectralTail
        (halfDensityShift h).convolutionSquare rho T epsilon := by
  obtain ⟨C, hC0, hdecay⟩ :=
    exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay h
  refine ⟨max 1 (|rho.im| + 1), 1 + 81 * C * (2 * Real.pi) ^ 2,
    by positivity, by positivity, ?_⟩
  intro z hz hT hone hrhoHeight
  have ht1 : (1 : Real) ≤ |z.im| := le_trans (le_max_left _ _) hT
  have hrhoIm : |rho.im| + 1 ≤ |z.im| := le_trans (le_max_right _ _) hT
  have htwopi : 0 < (2 : Real) * Real.pi := by positivity
  have hrhoLe : |rho.im| ≤ |z.im| := by linarith
  -- distance weights: both are at most 9 |Im z|^2
  have hsub1 : |z.re - rho.re| ≤ 1 := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [hz.1, hz.2, hrhoRe.1, hrhoRe.2]
    · linarith [hz.1, hz.2, hrhoRe.1, hrhoRe.2]
  have hsub2 : |z.im - rho.im| ≤ 2 * |z.im| := by
    have htri : |z.im - rho.im| ≤ |z.im| + |rho.im| := by
      have h := abs_sub_le (z.im) 0 (rho.im)
      simpa using h
    linarith
  have hW1 : ‖z - rho‖ ^ 2 ≤ 9 * |z.im| ^ 2 := by
    have hab : |z.re - rho.re| + |z.im - rho.im| ≤ 1 + 2 * |z.im| := by
      linarith
    have hsq : ‖z - rho‖ ^ 2 ≤ (|z.re - rho.re| + |z.im - rho.im|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (Complex.norm_le_abs_re_add_abs_im (z - rho)) 2
    have hmono : (|z.re - rho.re| + |z.im - rho.im|) ^ 2 ≤
        (1 + 2 * |z.im|) ^ 2 := pow_le_pow_left₀ (by positivity) hab 2
    have hfin : (1 + 2 * |z.im|) ^ 2 ≤ 9 * |z.im| ^ 2 := by
      have hprod2 : (0 : Real) ≤ (|z.im| - 1) * (5 * |z.im| + 1) :=
        mul_nonneg (by nlinarith) (by nlinarith)
      nlinarith [hprod2]
    linarith [hsq, hmono, hfin]
  have hcompRe : (1 - star z).re ∈ Set.Icc (0 : Real) 1 := by
    have hstarRe : (star z).re = z.re := by simp
    rw [Complex.sub_re, Complex.one_re, hstarRe]
    exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hcompIm : (1 - star z).im = z.im := by simp
  have hcompReSub : |(1 - star z).re - rho.re| ≤ 1 := by
    have h1 : (1 - star z).re = 1 - z.re := by
      rw [Complex.sub_re, Complex.one_re]
      simp
    rw [h1]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [hz.1, hz.2, hrhoRe.1, hrhoRe.2]
    · linarith [hz.1, hz.2, hrhoRe.1, hrhoRe.2]
  have hW2 : ‖(1 - star z) - rho‖ ^ 2 ≤ 9 * |z.im| ^ 2 := by
    have hcompSub : |(1 - star z).im - rho.im| ≤ 2 * |z.im| := by
      rw [hcompIm]; exact hsub2
    have hab : |(1 - star z).re - rho.re| + |(1 - star z).im - rho.im| ≤
        1 + 2 * |z.im| := by linarith
    have hsq : ‖(1 - star z) - rho‖ ^ 2 ≤
        (|(1 - star z).re - rho.re| + |(1 - star z).im - rho.im|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        (Complex.norm_le_abs_re_add_abs_im ((1 - star z) - rho)) 2
    have hmono : (|(1 - star z).re - rho.re| + |(1 - star z).im - rho.im|) ^ 2 ≤
        (1 + 2 * |z.im|) ^ 2 := pow_le_pow_left₀ (by positivity) hab 2
    have hfin : (1 + 2 * |z.im|) ^ 2 ≤ 9 * |z.im| ^ 2 := by
      have hprod2 : (0 : Real) ≤ (|z.im| - 1) * (5 * |z.im| + 1) :=
        mul_nonneg (by nlinarith) (by nlinarith)
      nlinarith [hprod2]
    linarith [hsq, hmono, hfin]
  -- the two vertical decay instances
  have hpt : ((z.re : Complex) + (z.im : Real) * Complex.I) = z :=
    (re_add_im_I z).symm
  have hdecayZ := hdecay z.re hz z.im
  rw [hpt] at hdecayZ
  have hptComp : (((1 - star z).re : Complex) +
      ((1 - star z).im : Real) * Complex.I) = 1 - star z :=
    (re_add_im_I (1 - star z)).symm
  have hdecayComp := hdecay (1 - star z).re hcompRe (1 - star z).im
  rw [hptComp, hcompIm] at hdecayComp
  have hnormZ : ‖((z.im : Real) / (2 * Real.pi))‖ = |z.im| / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos htwopi]
  rw [hnormZ] at hdecayZ hdecayComp
  have hpos1 : 0 < ((|z.im| : Real) / (2 * Real.pi)) ^ 2 := by positivity
  have hdenomEq : C / ((|z.im| / (2 * Real.pi)) ^ 2) * |z.im| ^ 2
      = C * (2 * Real.pi) ^ 2 := by
    field_simp [hpos1.ne]
  have hmulZ : ‖CompactLogTest.laplaceAt h z‖ *
      ((|z.im| / (2 * Real.pi)) ^ 2) ≤ C := by
    rw [mul_comm]; exact hdecayZ
  have hmulComp : ‖CompactLogTest.laplaceAt h (1 - star z)‖ *
      ((|z.im| / (2 * Real.pi)) ^ 2) ≤ C := by
    rw [mul_comm]; exact hdecayComp
  have keyZ : ‖CompactLogTest.laplaceAt h z‖ * |z.im| ^ 2 ≤
      C * (2 * Real.pi) ^ 2 := by
    have h2 : ‖CompactLogTest.laplaceAt h z‖ ≤
        C / ((|z.im| / (2 * Real.pi)) ^ 2) := (le_div_iff₀ hpos1).mpr hmulZ
    calc ‖CompactLogTest.laplaceAt h z‖ * |z.im| ^ 2
        ≤ C / ((|z.im| / (2 * Real.pi)) ^ 2) * |z.im| ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = C * (2 * Real.pi) ^ 2 := hdenomEq
  have keyComp : ‖CompactLogTest.laplaceAt h (1 - star z)‖ * |z.im| ^ 2 ≤
      C * (2 * Real.pi) ^ 2 := by
    have h2 : ‖CompactLogTest.laplaceAt h (1 - star z)‖ ≤
        C / ((|z.im| / (2 * Real.pi)) ^ 2) := (le_div_iff₀ hpos1).mpr hmulComp
    calc ‖CompactLogTest.laplaceAt h (1 - star z)‖ * |z.im| ^ 2
        ≤ C / ((|z.im| / (2 * Real.pi)) ^ 2) * |z.im| ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ = C * (2 * Real.pi) ^ 2 := hdenomEq
  -- assemble: the Hermitian product squares the decay order
  have hsquareValue :
      ‖CompactLogTest.laplaceAt
          (halfDensityShift h).convolutionSquare (z - 1 / 2)‖ =
        ‖CompactLogTest.laplaceAt h (1 - star z)‖ *
          ‖CompactLogTest.laplaceAt h z‖ := by
    rw [laplaceAt_halfDensityShift_convolutionSquare_centered h z, norm_mul]
    congr 1
    simp
  have hnonnegC : 0 ≤ C := hC0
  have hprod : ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
      ‖CompactLogTest.laplaceAt
          (halfDensityShift h).convolutionSquare (z - 1 / 2)‖ ≤
      81 * C ^ 2 * (2 * Real.pi) ^ 4 := by
    rw [hsquareValue]
    have hP1 : ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 ≤
        (9 * |z.im| ^ 2) * (9 * |z.im| ^ 2) :=
      mul_le_mul hW1 hW2 (by positivity) (by positivity)
    have hP2 : (‖CompactLogTest.laplaceAt h z‖ * |z.im| ^ 2) *
        (‖CompactLogTest.laplaceAt h (1 - star z)‖ * |z.im| ^ 2) ≤
        (C * (2 * Real.pi) ^ 2) * (C * (2 * Real.pi) ^ 2) :=
      mul_le_mul keyZ keyComp (by positivity) (by positivity)
    calc ‖z - rho‖ ^ 2 * ‖(1 - star z) - rho‖ ^ 2 *
        (‖CompactLogTest.laplaceAt h (1 - star z)‖ *
          ‖CompactLogTest.laplaceAt h z‖)
        ≤ (9 * |z.im| ^ 2) * (9 * |z.im| ^ 2) *
          (‖CompactLogTest.laplaceAt h (1 - star z)‖ *
            ‖CompactLogTest.laplaceAt h z‖) :=
          mul_le_mul_of_nonneg_right hP1 (by positivity)
      _ = 81 * ((‖CompactLogTest.laplaceAt h z‖ * |z.im| ^ 2) *
            (‖CompactLogTest.laplaceAt h (1 - star z)‖ * |z.im| ^ 2)) := by
          ring
      _ ≤ 81 * ((C * (2 * Real.pi) ^ 2) * (C * (2 * Real.pi) ^ 2)) :=
          mul_le_mul_of_nonneg_left hP2 (by positivity)
      _ = 81 * C ^ 2 * (2 * Real.pi) ^ 4 := by
          ring
  have hCp : 0 ≤ C * (2 * Real.pi) ^ 2 :=
    mul_nonneg hnonnegC (sq_nonneg (2 * Real.pi))
  exact lt_of_le_of_lt hprod (by
    nlinarith [hnonnegC, hCp, sq_nonneg (C * (2 * Real.pi) ^ 2)])

end C1HealthyDetectorRootSupportExit
end Source
end ConnesWeilRH
