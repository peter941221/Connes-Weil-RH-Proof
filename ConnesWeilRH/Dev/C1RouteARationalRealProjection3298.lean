import ConnesWeilRH.Dev.C1RouteARationalTightTail3298

namespace ConnesWeilRH.Dev

def ratRectRealPartInterval3298 (rect : RatRect3276) : RatInterval3276 :=
  { lo := rect.reLo
    hi := rect.reHi }

def ratCoefficientPhaseRealInterval3298
    (coefficient phase : RatRect3276) : RatInterval3276 :=
  RatInterval3276.sub
    (RatInterval3276.mul
      { lo := coefficient.reLo, hi := coefficient.reHi }
      { lo := phase.reLo, hi := phase.reHi })
    (RatInterval3276.mul
      { lo := coefficient.imLo, hi := coefficient.imHi }
      { lo := phase.imLo, hi := phase.imHi })

def ratRealFamilyInterval3298
    (coefficient phase : RatRect3276) (bump : RatInterval3276) : RatInterval3276 :=
  RatInterval3276.mul bump (ratCoefficientPhaseRealInterval3298 coefficient phase)

theorem ratIntervalMemSub3298
    {a b : RatInterval3276} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (RatInterval3276.sub a b).Mem (x - y) := by
  unfold RatInterval3276.Mem RatInterval3276.toReal
    RatInterval3276.sub RealInterval2429.Mem
  simp only [Rat.cast_sub]
  change (a.lo : ℝ) ≤ x ∧ x ≤ a.hi at ha
  change (b.lo : ℝ) ≤ y ∧ y ≤ b.hi at hb
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem ratCoefficientPhaseRealInterval_mem3298
    {coefficient phase : RatRect3276} {c z : ℂ}
    (hcoefficient : coefficient.Mem c)
    (hphase : phase.Mem z) :
    (ratCoefficientPhaseRealInterval3298 coefficient phase).Mem (c * z).re := by
  have hcr : (⟨coefficient.reLo, coefficient.reHi⟩ : RatInterval3276).Mem c.re := by
    change (coefficient.reLo : ℝ) ≤ c.re ∧ c.re ≤ coefficient.reHi
    exact ⟨hcoefficient.1, hcoefficient.2.1⟩
  have hci : (⟨coefficient.imLo, coefficient.imHi⟩ : RatInterval3276).Mem c.im := by
    change (coefficient.imLo : ℝ) ≤ c.im ∧ c.im ≤ coefficient.imHi
    exact ⟨hcoefficient.2.2.1, hcoefficient.2.2.2⟩
  have hzr : (⟨phase.reLo, phase.reHi⟩ : RatInterval3276).Mem z.re := by
    change (phase.reLo : ℝ) ≤ z.re ∧ z.re ≤ phase.reHi
    exact ⟨hphase.1, hphase.2.1⟩
  have hzi : (⟨phase.imLo, phase.imHi⟩ : RatInterval3276).Mem z.im := by
    change (phase.imLo : ℝ) ≤ z.im ∧ z.im ≤ phase.imHi
    exact ⟨hphase.2.2.1, hphase.2.2.2⟩
  have hreal := ratIntervalMemSub3298
    (RatInterval3276.mem_mul hcr hzr)
    (RatInterval3276.mem_mul hci hzi)
  simpa [ratCoefficientPhaseRealInterval3298, Complex.mul_re] using hreal

theorem ratRealFamilyInterval_mem3298
    {coefficient phase : RatRect3276} {bump : RatInterval3276}
    {c z : ℂ} {b : ℝ} (hcoefficient : coefficient.Mem c)
    (hphase : phase.Mem z) (hbump : bump.Mem b) :
    (ratRealFamilyInterval3298 coefficient phase bump).Mem
      (b * (c * z).re) := by
  exact RatInterval3276.mem_mul hbump
    (ratCoefficientPhaseRealInterval_mem3298 hcoefficient hphase)

theorem ratRealFamilyInterval_external_mem3298
    {coefficient : ℂ} {modulation radius position : ℝ}
    {coefficientRect phaseRect : RatRect3276} {bumpInterval : RatInterval3276}
    (hcoefficient : coefficientRect.Mem coefficient)
    (hphase : phaseRect.Mem
      (Complex.exp ((modulation * position : ℝ) * Complex.I)))
    (hbump : bumpInterval.Mem
      (C1RouteAOwnerScaleAudit.widthBump radius position)) :
    (ratRealFamilyInterval3298 coefficientRect phaseRect bumpInterval).Mem
      (externalFamilyValue2344 coefficient modulation radius position).re := by
  have hreal := ratRealFamilyInterval_mem3298 hcoefficient hphase
    hbump
  rw [externalFamilyValue2344_eq_familyTerm]
  convert hreal using 1 <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
  <;> ring_nf

end ConnesWeilRH.Dev
