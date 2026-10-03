import ConnesWeilRH.Dev.C1RouteASignedCenterError2531

namespace ConnesWeilRH.Dev

/-!
Record 2534: whole-cell Lipschitz inflation interface.

If a cell function is L-Lipschitz on [a,b], then every point is controlled by
one of the two endpoints, with a half-cell allowance.  In the Route A use,
f is the third-derivative magnitude channel and L is supplied by a certified
fourth-derivative enclosure.  This theorem is only the generic transport
interface; it does not instantiate the owner data or certify a numerical L.
-/

theorem norm_le_endpoint_max_add_half_lipschitz2534
    {E : Type*} [SeminormedAddCommGroup E]
    (f : ℝ → E) (a b L : ℝ)
    (hab : a ≤ b) (hL : 0 ≤ L)
    (hLip : ∀ ⦃x y : ℝ⦄,
      x ∈ Set.Icc a b → y ∈ Set.Icc a b →
        ‖f x - f y‖ ≤ L * |x - y|) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Icc a b →
      ‖f x‖ ≤ max ‖f a‖ ‖f b‖ + L * ((b - a) / 2) := by
  intro x hx
  have hmid : a ≤ (a + b) / 2 := by linarith
  have hmid' : (a + b) / 2 ≤ b := by linarith
  rcases le_total x ((a + b) / 2) with hleft | hright
  · have hxa : 0 ≤ x - a := by linarith [hx.1]
    have hdist : x - a ≤ (b - a) / 2 := by linarith
    have hxa_mem : x ∈ Set.Icc a b := hx
    have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    have hdiff := hLip hxa_mem ha_mem
    rw [abs_of_nonneg hxa] at hdiff
    calc
      ‖f x‖ = ‖f a + (f x - f a)‖ := by congr 1 <;> abel
      _ ≤ ‖f a‖ + ‖f x - f a‖ := norm_add_le _ _
      _ ≤ ‖f a‖ + L * (x - a) := by linarith
      _ ≤ ‖f a‖ + L * ((b - a) / 2) := by
        have hmul : L * (x - a) ≤ L * ((b - a) / 2) :=
          mul_le_mul_of_nonneg_left hdist hL
        linarith
      _ ≤ max ‖f a‖ ‖f b‖ + L * ((b - a) / 2) := by
        have hmax : ‖f a‖ ≤ max ‖f a‖ ‖f b‖ := le_max_left _ _
        linarith
  · have hxb : 0 ≤ b - x := by linarith [hx.2]
    have hdist : b - x ≤ (b - a) / 2 := by linarith
    have hxb_mem : x ∈ Set.Icc a b := hx
    have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
    have hdiff := hLip hxb_mem hb_mem
    have hdiff' : ‖f x - f b‖ ≤ L * (b - x) := by
      simpa [abs_of_nonpos (by linarith : x - b ≤ 0)] using hdiff
    calc
      ‖f x‖ = ‖f b + (f x - f b)‖ := by congr 1 <;> abel
      _ ≤ ‖f b‖ + ‖f x - f b‖ := norm_add_le _ _
      _ ≤ ‖f b‖ + L * (b - x) := by linarith
      _ ≤ ‖f b‖ + L * ((b - a) / 2) := by
        have hmul : L * (b - x) ≤ L * ((b - a) / 2) :=
          mul_le_mul_of_nonneg_left hdist hL
        linarith
      _ ≤ max ‖f a‖ ‖f b‖ + L * ((b - a) / 2) := by
        have hmax : ‖f b‖ ≤ max ‖f a‖ ‖f b‖ := le_max_right _ _
        linarith

end ConnesWeilRH.Dev



