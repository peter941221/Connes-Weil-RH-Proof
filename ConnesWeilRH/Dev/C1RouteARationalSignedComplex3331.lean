import ConnesWeilRH.Dev.C1RouteARationalSignedInterval3329

namespace ConnesWeilRH.Dev

theorem ratRect_mul_singleton_reHi_formula3331
    (cRe cIm : ℚ) (b : RatRect3276) :
    (RatRect3276.mul
      ({ reLo := cRe, reHi := cRe, imLo := cIm, imHi := cIm } : RatRect3276)
      b).reHi =
      max (cRe * b.reLo) (cRe * b.reHi) -
        min (cIm * b.imLo) (cIm * b.imHi) := by
  unfold RatRect3276.mul
  simp only [RatInterval3276.mul, RatInterval3276.sub, max_self, min_self]

end ConnesWeilRH.Dev
