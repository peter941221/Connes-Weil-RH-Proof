import ConnesWeilRH.Dev.MellinBandGamma
import ConnesWeilRH.Basic

/-!
# Arch sign slot: the ONE phase obligation is named, axiom-clean

859 / 862 / 873 reduce route-1's arch sign, for the faithful band test
`f_a(t) = t^a e^{-t}` (a > 0), to the single real statement `Re[(M f_a (i/2))^4] >= 0`,
with `M(f_a)(i/2) = Gamma(a + i/2)` (proven in `MellinBandGamma`).

This module does two honest, verifiable things:
1. names the phase obligation `Re[(Gamma (a+i/2))^4] >= 0` as an exact predicate
   (`archPhaseGate`), and proves it equals the band-test Mellin sign slot;
2. records that a controlled phase/arg bound is the ONLY content left (mathlib
   v4.30.0 has no Stirling/arg-Gamma estimate).  No Stirling is assumed; the
   4th-power object is nonzero (so the slot is non-vacuous, AGENTS 6/11).

No RH is claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace Dev
namespace ArchPhaseSignSlot

open MeasureTheory

noncomputable section

/-- The critical-line Mellin of the band test, as a point. -/
noncomputable def bandMellin (a : Real) : Complex :=
  mellin (fun t : Real => (Real.exp (-t) : Complex) * (t : Complex) ^ (a : Complex)) (Complex.I / 2)

/-- The arch-phase gate: `Re[(M f_a (i/2))^4] >= 0`. -/
noncomputable def archPhaseGate (a : Real) : Prop :=
  0 <= ((bandMellin a) ^ 4).re

/-- The band test's critical Mellin is `Gamma(a+i/2)` (nonzero producer). -/
theorem bandMellin_eq_Gamma (a : Real) (ha : 0 < a) :
    bandMellin a = Complex.Gamma ((a : Complex) + Complex.I / 2) := by
  unfold bandMellin
  exact MellinBandGamma.mellin_band_eq_Gamma a ha

/-- The arch-phase slot is EXACTLY `Re[(Gamma(a+i/2))^4] >= 0`. -/
theorem archPhaseGate_eq_Gamma_phase (a : Real) (ha : 0 < a) :
    archPhaseGate a <-> 0 <= ((Complex.Gamma ((a : Complex) + Complex.I / 2)) ^ 4).re := by
  unfold archPhaseGate
  rw [bandMellin_eq_Gamma a ha]

/-- Non-vacuous: the band-test Mellin is nonzero for every a>0. -/
theorem bandMellin_ne_zero (a : Real) (ha : 0 < a) :
    bandMellin a ≠ 0 := by
  unfold bandMellin
  exact MellinBandGamma.mellin_band_ne_zero a ha

end
end ArchPhaseSignSlot
end Dev
end Source
end ConnesWeilRH

