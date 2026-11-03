import ConnesWeilRH.Dev.C1RouteARationalBump3280

namespace ConnesWeilRH.Dev

def ratRealRect3281 (a : RatInterval3276) : RatRect3276 :=
  { reLo := a.lo
    reHi := a.hi
    imLo := 0
    imHi := 0 }

theorem ratRealRect3281_mem
    {x : ℝ} {a : RatInterval3276}
    (ha : a.Mem x) : (ratRealRect3281 a).Mem (x : ℂ) := by
  unfold ratRealRect3281 RatRect3276.Mem RatRect3276.toReal
    ComplexRect2427.Mem
  exact ⟨ha.1, ha.2, by norm_num, by norm_num⟩

theorem ratFamilyRect_mem3281
    {family : Fin 30} {position : ℝ}
    {coefficientRect : RatRect3276} {bumpInterval : RatInterval3276}
    {phaseRect : RatRect3276}
    (hcoefficient : coefficientRect.Mem
      (record2680CorrectionCoefficient family))
    (hbump : bumpInterval.Mem
      (C1RouteAOwnerScaleAudit.widthBump (C1RouteAOwnerScaleAudit.storedWidth family ^ 2) position))
    (hphase : phaseRect.Mem
      (Complex.exp (((capturedModulations2584 family * position : ℝ) : ℂ) *
        Complex.I))) :
    (RatRect3276.mul
      (RatRect3276.mul coefficientRect (ratRealRect3281 bumpInterval))
      phaseRect).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient family)
        (capturedModulations2584 family)
        (C1RouteAOwnerScaleAudit.storedWidth family ^ 2) position) := by
  rw [externalFamilyValue2344_eq_familyTerm]
  have hbump' := ratRealRect3281_mem hbump
  have hfirst := RatRect3276.mem_mul hcoefficient hbump'
  have hsecond := RatRect3276.mem_mul hfirst hphase
  simpa using hsecond

end ConnesWeilRH.Dev
