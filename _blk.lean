/-! ### Integral assembly on (0,inf): |Re(Int)| <= Int |g| <= 11/4 + (4/3) A -/

/-- `|g|` integrable on `(0,inf)`. -/
lemma bump_integrableOn_Ioi_abs :
    IntegrableOn (fun y : Real => |bumpArchG y|) (Ioi (0 : Real)) := by
  have hh : IntegrableOn (fun y : Real => ‖bumpPlateauOwner.archimedeanIntegrand y‖) (Ioi (0 : Real)) :=
    bumpPlateauOwner.archimedeanIntegrand_integrable_on_Ioi.norm
  apply hh.ae_eq ?_
  filter_upwards [self_mem_ae_restrict (s := Ioi (0:Real))] with y hy
  exact bump_norm_integrand_eq_abs y (by simpa using hy)