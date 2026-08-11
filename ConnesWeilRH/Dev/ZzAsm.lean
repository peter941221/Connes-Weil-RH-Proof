/-! ### Near-band integral on (0,1] -/

/- `|g|` integrable on (0,1]. -/
lemma bump_integrableOn_Ioc01_abs :
    IntegrableOn (fun y : Real => |bumpArchG y|) (Ioc (0 : Real) 1) := by
  exact bump_integrable_Ioi_abs.mono_set (by
    intro y hy
    simp at hy
    exact hy.1)

/- `|g|` integrable on (1,inf). -/
lemma bump_integrableOn_Ioi1_abs :
    IntegrableOn (fun y : Real => |bumpArchG y|) (Ioi (1 : Real)) := by
  exact bump_integrable_Ioi_abs.mono_set (by
    intro y hy
    simpa [Set.mem_Ioi] using (lt_trans (by norm_num : (0 : Real) < (1 : Real)) hy))

/- `e^{1/2} + 1 < 11/4`. -/
lemma bump_ehalf_add_one_lt_quarter : Real.exp (1 / 2 : Real) + 1 < (11 / 4 : Real) := by
  have he := ConnesWeilRH.Source.Dev.Wall14Coeff.expHalf_lt
  linarith


/- Near integral on (0,1] is <= 11/4. -/
lemma bump_near_integral_le :
    (∫ y in Ioc (0 : Real) 1, |bumpArchG y|) <= (11 / 4 : Real) := by
  let mu : Measure Real := volume.restrict (Ioc (0 : Real) 1)
  let K : Real := Real.exp (1 / 2 : Real) + 1
  have hmeas : MeasurableSet (Ioc (0 : Real) 1) := measurableSet_Ioc
  have hbnd : (fun y : Real => |bumpArchG y|) <=ᵐ[mu] (fun _ : Real => K) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact bumpG_abs_le_near y hy.1 (by simpa using hy.2)
  have hnon : (fun _ : Real => (0 : Real)) <=ᵐ[mu] (fun y : Real => |bumpArchG y|) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict hmeas] with y hy
    exact abs_nonneg (bumpArchG y)
  have hfin : (volume : Measure Real) (Ioc (0 : Real) 1) != ⊤ := by
    simp [Real.volume_Ioc]
  haveI : IsFiniteMeasure mu := MeasureTheory.isFiniteMeasure_restrict.mpr
    (by simpa [mu] using hfin)
  have hKint : Integrable (fun _ : Real => K) mu := MeasureTheory.integrable_const K
  have hsum_eq : (∫ y : Real, K ∂mu) = K := by
    calc
      (∫ y : Real, K ∂mu) = mu.real Set.univ * K := by simp [MeasureTheory.integral_const]
      _ = K := by
        have hvol : mu Set.univ = (1 : ENNReal) := by simp [mu, Real.volume_Ioc]
        simp [hvol]
  have hmm : (∫ y : Real, |bumpArchG y| ∂mu) <= (∫ y : Real, K ∂mu) :=
    MeasureTheory.integral_mono_of_nonneg hnon hKint hbnd
  calc
    (∫ y in Ioc (0 : Real) 1, |bumpArchG y|) <= (∫ y : Real, K ∂mu) := by
      simpa [mu] using hmm
    _ = K := hsum_eq
    _ <= (11 / 4 : Real) := by nlinarith [ConnesWeilRH.Source.Dev.Wall14Coeff.expHalf_lt]

/- Tail constant `(2 e^{-1})/(1-e^{-2}) <= 4/3`. -/
lemma bump_tail_const_le : (2 * Real.exp (-1 : Real)) / (1 - Real.exp (-2 : Real)) <= (4 / 3 : Real) := by
  let t : Real := Real.exp (-1 : Real)
  have ht_le : t <= (1 / 2 : Real) := by
    have he : (2 : Real) <= Real.exp 1 := Real.add_one_le_exp 1
    have hispos : (0 : Real) < Real.exp 1 := Real.exp_pos 1
    have hstep : (1 / Real.exp 1 : Real) <= (1 / 2 : Real) := by
      rw [div_le_iff₀ hispos]
      nlinarith [he]
    unfold t
    rw [Real.exp_neg]
    exact hstep
  have ht_sq : t^2 = Real.exp (-2 : Real) := by
    unfold t
    rw [pow_two, Real.exp_add]
    norm_num
  have hden : (0 : Real) < 1 - t^2 := by
    have hlt1 : t < (1 : Real) := by nlinarith [ht_le]
    nlinarith
  have hqt : 2 * t / (1 - t^2) <= (4 / 3 : Real) := by
    rw [div_le_iff₀ hden]
    nlinarith
  calc
    (2 * Real.exp (-1 : Real)) / (1 - Real.exp (-2 : Real))
        = 2 * t / (1 - t^2) := by
          simp [t, ht_sq]
    _ <= (4 / 3 : Real) := hqt