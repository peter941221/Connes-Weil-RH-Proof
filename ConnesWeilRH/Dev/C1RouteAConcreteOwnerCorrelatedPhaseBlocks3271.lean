import ConnesWeilRH.Dev.C1RouteAConcreteOwnerCell16923CoeffPhaseBlocks3270

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def record2680Cell16923Block0Group0to4Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (((record2680CorrectionCoefficient 0 + record2680CorrectionCoefficient 1) + record2680CorrectionCoefficient 4))).mul
    (record2680Cell16923Family0TightStageBox3269 9)

theorem record2680_cell16923_block0_group0to4_mem3271 :
    record2680Cell16923Block0Group0to4Rect3271.Mem
      (((record2680CorrectionCoefficient 0 + record2680CorrectionCoefficient 1) + record2680CorrectionCoefficient 4) *
        (Complex.exp (((capturedModulations2584 0 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family0_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block0Group2to3Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point ((record2680CorrectionCoefficient 2 + record2680CorrectionCoefficient 3))).mul
    (record2680Cell16923Family2TightStageBox3269 9)

theorem record2680_cell16923_block0_group2to3_mem3271 :
    record2680Cell16923Block0Group2to3Rect3271.Mem
      ((record2680CorrectionCoefficient 2 + record2680CorrectionCoefficient 3) *
        (Complex.exp (((capturedModulations2584 2 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family2_tight_phase_box_mem3269

noncomputable def record2680Cell16923CorrelatedPhaseBlock0to4Rect3271 : ComplexRect2427 :=
  (record2680Cell16923Block0Group0to4Rect3271.add
      record2680Cell16923Block0Group2to3Rect3271)

theorem record2680_cell16923_correlated_phase_block0to4_mem3271 :
    record2680Cell16923CorrelatedPhaseBlock0to4Rect3271.Mem
      ((((record2680CorrectionCoefficient 0 + record2680CorrectionCoefficient 1) + record2680CorrectionCoefficient 4) *
        (Complex.exp (((capturedModulations2584 0 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + ((record2680CorrectionCoefficient 2 + record2680CorrectionCoefficient 3) *
        (Complex.exp (((capturedModulations2584 2 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)))) := by
  apply ComplexRect2427.mem_add
  · exact record2680_cell16923_block0_group0to4_mem3271
  · exact record2680_cell16923_block0_group2to3_mem3271

noncomputable def record2680Cell16923Block5Group5to7Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (((record2680CorrectionCoefficient 5 + record2680CorrectionCoefficient 6) + record2680CorrectionCoefficient 7))).mul
    (ComplexRect2427.point 1)

theorem record2680_cell16923_block5_group5to7_mem3271 :
    record2680Cell16923Block5Group5to7Rect3271.Mem
      (((record2680CorrectionCoefficient 5 + record2680CorrectionCoefficient 6) + record2680CorrectionCoefficient 7) *
        (Complex.exp (((capturedModulations2584 5 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  have hphase : (ComplexRect2427.point (1 : ℂ)).Mem
      (Complex.exp (((capturedModulations2584 5 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)) := by
    simpa [capturedModulations2584, Matrix.cons_val_zero,
      Matrix.cons_val_four, Matrix.cons_val_5, Fin.ext_iff]
      using (ComplexRect2427.point_mem (1 : ℂ))
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _) hphase

noncomputable def record2680Cell16923Block5Group8to8Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 8)).mul
    (record2680Cell16923Family8TightStageBox3269 9)

theorem record2680_cell16923_block5_group8to8_mem3271 :
    record2680Cell16923Block5Group8to8Rect3271.Mem
      (record2680CorrectionCoefficient 8 *
        (Complex.exp (((capturedModulations2584 8 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family8_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block5Group9to9Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 9)).mul
    (record2680Cell16923Family9TightStageBox3269 9)

theorem record2680_cell16923_block5_group9to9_mem3271 :
    record2680Cell16923Block5Group9to9Rect3271.Mem
      (record2680CorrectionCoefficient 9 *
        (Complex.exp (((capturedModulations2584 9 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family9_tight_phase_box_mem3269

noncomputable def record2680Cell16923CorrelatedPhaseBlock5to9Rect3271 : ComplexRect2427 :=
  ((record2680Cell16923Block5Group5to7Rect3271.add
      record2680Cell16923Block5Group8to8Rect3271).add
      record2680Cell16923Block5Group9to9Rect3271)

theorem record2680_cell16923_correlated_phase_block5to9_mem3271 :
    record2680Cell16923CorrelatedPhaseBlock5to9Rect3271.Mem
      ((((record2680CorrectionCoefficient 5 + record2680CorrectionCoefficient 6) + record2680CorrectionCoefficient 7) *
        (Complex.exp (((capturedModulations2584 5 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 8 *
        (Complex.exp (((capturedModulations2584 8 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 9 *
        (Complex.exp (((capturedModulations2584 9 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)))) := by
  apply ComplexRect2427.mem_add
  · apply ComplexRect2427.mem_add
    · exact record2680_cell16923_block5_group5to7_mem3271
    · exact record2680_cell16923_block5_group8to8_mem3271
  · exact record2680_cell16923_block5_group9to9_mem3271

noncomputable def record2680Cell16923Block10Group10to10Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 10)).mul
    (record2680Cell16923Family10TightStageBox3268 9)

theorem record2680_cell16923_block10_group10to10_mem3271 :
    record2680Cell16923Block10Group10to10Rect3271.Mem
      (record2680CorrectionCoefficient 10 *
        (Complex.exp (((capturedModulations2584 10 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family10_tight_phase_box_mem3268

noncomputable def record2680Cell16923Block10Group11to11Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 11)).mul
    (record2680Cell16923Family11TightStageBox3268 9)

theorem record2680_cell16923_block10_group11to11_mem3271 :
    record2680Cell16923Block10Group11to11Rect3271.Mem
      (record2680CorrectionCoefficient 11 *
        (Complex.exp (((capturedModulations2584 11 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family11_tight_phase_box_mem3268

noncomputable def record2680Cell16923Block10Group12to12Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 12)).mul
    (record2680Cell16923Family12TightStageBox3268 9)

theorem record2680_cell16923_block10_group12to12_mem3271 :
    record2680Cell16923Block10Group12to12Rect3271.Mem
      (record2680CorrectionCoefficient 12 *
        (Complex.exp (((capturedModulations2584 12 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family12_tight_phase_box_mem3268

noncomputable def record2680Cell16923Block10Group13to13Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 13)).mul
    (record2680Cell16923Family13TightStageBox3268 9)

theorem record2680_cell16923_block10_group13to13_mem3271 :
    record2680Cell16923Block10Group13to13Rect3271.Mem
      (record2680CorrectionCoefficient 13 *
        (Complex.exp (((capturedModulations2584 13 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family13_tight_phase_box_mem3268

noncomputable def record2680Cell16923Block10Group14to14Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 14)).mul
    (record2680Cell16923Family14TightStageBox3268 9)

theorem record2680_cell16923_block10_group14to14_mem3271 :
    record2680Cell16923Block10Group14to14Rect3271.Mem
      (record2680CorrectionCoefficient 14 *
        (Complex.exp (((capturedModulations2584 14 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family14_tight_phase_box_mem3268

noncomputable def record2680Cell16923CorrelatedPhaseBlock10to14Rect3271 : ComplexRect2427 :=
  ((((record2680Cell16923Block10Group10to10Rect3271.add
      record2680Cell16923Block10Group11to11Rect3271).add
      record2680Cell16923Block10Group12to12Rect3271).add
      record2680Cell16923Block10Group13to13Rect3271).add
      record2680Cell16923Block10Group14to14Rect3271)

theorem record2680_cell16923_correlated_phase_block10to14_mem3271 :
    record2680Cell16923CorrelatedPhaseBlock10to14Rect3271.Mem
      ((record2680CorrectionCoefficient 10 *
        (Complex.exp (((capturedModulations2584 10 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 11 *
        (Complex.exp (((capturedModulations2584 11 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 12 *
        (Complex.exp (((capturedModulations2584 12 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 13 *
        (Complex.exp (((capturedModulations2584 13 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 14 *
        (Complex.exp (((capturedModulations2584 14 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)))) := by
  apply ComplexRect2427.mem_add
  · apply ComplexRect2427.mem_add
    · apply ComplexRect2427.mem_add
      · apply ComplexRect2427.mem_add
        · exact record2680_cell16923_block10_group10to10_mem3271
        · exact record2680_cell16923_block10_group11to11_mem3271
      · exact record2680_cell16923_block10_group12to12_mem3271
    · exact record2680_cell16923_block10_group13to13_mem3271
  · exact record2680_cell16923_block10_group14to14_mem3271

noncomputable def record2680Cell16923Block15Group15to15Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 15)).mul
    (record2680Cell16923Family15TightStageBox3269 9)

theorem record2680_cell16923_block15_group15to15_mem3271 :
    record2680Cell16923Block15Group15to15Rect3271.Mem
      (record2680CorrectionCoefficient 15 *
        (Complex.exp (((capturedModulations2584 15 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family15_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block15Group16to16Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 16)).mul
    (record2680Cell16923Family16TightStageBox3269 9)

theorem record2680_cell16923_block15_group16to16_mem3271 :
    record2680Cell16923Block15Group16to16Rect3271.Mem
      (record2680CorrectionCoefficient 16 *
        (Complex.exp (((capturedModulations2584 16 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family16_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block15Group17to17Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 17)).mul
    (record2680Cell16923Family17TightStageBox3269 9)

theorem record2680_cell16923_block15_group17to17_mem3271 :
    record2680Cell16923Block15Group17to17Rect3271.Mem
      (record2680CorrectionCoefficient 17 *
        (Complex.exp (((capturedModulations2584 17 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family17_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block15Group18to18Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 18)).mul
    (record2680Cell16923Family18TightStageBox3269 9)

theorem record2680_cell16923_block15_group18to18_mem3271 :
    record2680Cell16923Block15Group18to18Rect3271.Mem
      (record2680CorrectionCoefficient 18 *
        (Complex.exp (((capturedModulations2584 18 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family18_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block15Group19to19Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 19)).mul
    (record2680Cell16923Family19TightStageBox3269 9)

theorem record2680_cell16923_block15_group19to19_mem3271 :
    record2680Cell16923Block15Group19to19Rect3271.Mem
      (record2680CorrectionCoefficient 19 *
        (Complex.exp (((capturedModulations2584 19 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family19_tight_phase_box_mem3269

noncomputable def record2680Cell16923CorrelatedPhaseBlock15to19Rect3271 : ComplexRect2427 :=
  ((((record2680Cell16923Block15Group15to15Rect3271.add
      record2680Cell16923Block15Group16to16Rect3271).add
      record2680Cell16923Block15Group17to17Rect3271).add
      record2680Cell16923Block15Group18to18Rect3271).add
      record2680Cell16923Block15Group19to19Rect3271)

theorem record2680_cell16923_correlated_phase_block15to19_mem3271 :
    record2680Cell16923CorrelatedPhaseBlock15to19Rect3271.Mem
      ((record2680CorrectionCoefficient 15 *
        (Complex.exp (((capturedModulations2584 15 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 16 *
        (Complex.exp (((capturedModulations2584 16 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 17 *
        (Complex.exp (((capturedModulations2584 17 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 18 *
        (Complex.exp (((capturedModulations2584 18 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 19 *
        (Complex.exp (((capturedModulations2584 19 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)))) := by
  apply ComplexRect2427.mem_add
  · apply ComplexRect2427.mem_add
    · apply ComplexRect2427.mem_add
      · apply ComplexRect2427.mem_add
        · exact record2680_cell16923_block15_group15to15_mem3271
        · exact record2680_cell16923_block15_group16to16_mem3271
      · exact record2680_cell16923_block15_group17to17_mem3271
    · exact record2680_cell16923_block15_group18to18_mem3271
  · exact record2680_cell16923_block15_group19to19_mem3271

noncomputable def record2680Cell16923Block20Group20to20Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 20)).mul
    (record2680Cell16923Family20TightStageBox3269 9)

theorem record2680_cell16923_block20_group20to20_mem3271 :
    record2680Cell16923Block20Group20to20Rect3271.Mem
      (record2680CorrectionCoefficient 20 *
        (Complex.exp (((capturedModulations2584 20 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family20_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block20Group21to21Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 21)).mul
    (record2680Cell16923Family21TightStageBox3269 9)

theorem record2680_cell16923_block20_group21to21_mem3271 :
    record2680Cell16923Block20Group21to21Rect3271.Mem
      (record2680CorrectionCoefficient 21 *
        (Complex.exp (((capturedModulations2584 21 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family21_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block20Group22to22Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 22)).mul
    (record2680Cell16923Family22TightStageBox3269 9)

theorem record2680_cell16923_block20_group22to22_mem3271 :
    record2680Cell16923Block20Group22to22Rect3271.Mem
      (record2680CorrectionCoefficient 22 *
        (Complex.exp (((capturedModulations2584 22 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family22_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block20Group23to23Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 23)).mul
    (record2680Cell16923Family23TightStageBox3269 9)

theorem record2680_cell16923_block20_group23to23_mem3271 :
    record2680Cell16923Block20Group23to23Rect3271.Mem
      (record2680CorrectionCoefficient 23 *
        (Complex.exp (((capturedModulations2584 23 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family23_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block20Group24to24Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 24)).mul
    (record2680Cell16923Family24TightStageBox3269 9)

theorem record2680_cell16923_block20_group24to24_mem3271 :
    record2680Cell16923Block20Group24to24Rect3271.Mem
      (record2680CorrectionCoefficient 24 *
        (Complex.exp (((capturedModulations2584 24 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family24_tight_phase_box_mem3269

noncomputable def record2680Cell16923CorrelatedPhaseBlock20to24Rect3271 : ComplexRect2427 :=
  ((((record2680Cell16923Block20Group20to20Rect3271.add
      record2680Cell16923Block20Group21to21Rect3271).add
      record2680Cell16923Block20Group22to22Rect3271).add
      record2680Cell16923Block20Group23to23Rect3271).add
      record2680Cell16923Block20Group24to24Rect3271)

theorem record2680_cell16923_correlated_phase_block20to24_mem3271 :
    record2680Cell16923CorrelatedPhaseBlock20to24Rect3271.Mem
      ((record2680CorrectionCoefficient 20 *
        (Complex.exp (((capturedModulations2584 20 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 21 *
        (Complex.exp (((capturedModulations2584 21 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 22 *
        (Complex.exp (((capturedModulations2584 22 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 23 *
        (Complex.exp (((capturedModulations2584 23 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 24 *
        (Complex.exp (((capturedModulations2584 24 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)))) := by
  apply ComplexRect2427.mem_add
  · apply ComplexRect2427.mem_add
    · apply ComplexRect2427.mem_add
      · apply ComplexRect2427.mem_add
        · exact record2680_cell16923_block20_group20to20_mem3271
        · exact record2680_cell16923_block20_group21to21_mem3271
      · exact record2680_cell16923_block20_group22to22_mem3271
    · exact record2680_cell16923_block20_group23to23_mem3271
  · exact record2680_cell16923_block20_group24to24_mem3271

noncomputable def record2680Cell16923Block25Group25to25Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 25)).mul
    (record2680Cell16923Family25TightStageBox3269 9)

theorem record2680_cell16923_block25_group25to25_mem3271 :
    record2680Cell16923Block25Group25to25Rect3271.Mem
      (record2680CorrectionCoefficient 25 *
        (Complex.exp (((capturedModulations2584 25 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family25_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block25Group26to26Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 26)).mul
    (record2680Cell16923Family26TightStageBox3269 9)

theorem record2680_cell16923_block25_group26to26_mem3271 :
    record2680Cell16923Block25Group26to26Rect3271.Mem
      (record2680CorrectionCoefficient 26 *
        (Complex.exp (((capturedModulations2584 26 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family26_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block25Group27to27Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 27)).mul
    (record2680Cell16923Family27TightStageBox3269 9)

theorem record2680_cell16923_block25_group27to27_mem3271 :
    record2680Cell16923Block25Group27to27Rect3271.Mem
      (record2680CorrectionCoefficient 27 *
        (Complex.exp (((capturedModulations2584 27 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family27_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block25Group28to28Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 28)).mul
    (record2680Cell16923Family28TightStageBox3269 9)

theorem record2680_cell16923_block25_group28to28_mem3271 :
    record2680Cell16923Block25Group28to28Rect3271.Mem
      (record2680CorrectionCoefficient 28 *
        (Complex.exp (((capturedModulations2584 28 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family28_tight_phase_box_mem3269

noncomputable def record2680Cell16923Block25Group29to29Rect3271 : ComplexRect2427 :=
  (ComplexRect2427.point (record2680CorrectionCoefficient 29)).mul
    (record2680Cell16923Family29TightStageBox3269 9)

theorem record2680_cell16923_block25_group29to29_mem3271 :
    record2680Cell16923Block25Group29to29Rect3271.Mem
      (record2680CorrectionCoefficient 29 *
        (Complex.exp (((capturedModulations2584 29 *
        record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) := by
  exact ComplexRect2427.mem_mul
    (ComplexRect2427.point_mem _)
    record2680_cell16923_family29_tight_phase_box_mem3269

noncomputable def record2680Cell16923CorrelatedPhaseBlock25to29Rect3271 : ComplexRect2427 :=
  ((((record2680Cell16923Block25Group25to25Rect3271.add
      record2680Cell16923Block25Group26to26Rect3271).add
      record2680Cell16923Block25Group27to27Rect3271).add
      record2680Cell16923Block25Group28to28Rect3271).add
      record2680Cell16923Block25Group29to29Rect3271)

theorem record2680_cell16923_correlated_phase_block25to29_mem3271 :
    record2680Cell16923CorrelatedPhaseBlock25to29Rect3271.Mem
      ((record2680CorrectionCoefficient 25 *
        (Complex.exp (((capturedModulations2584 25 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 26 *
        (Complex.exp (((capturedModulations2584 26 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 27 *
        (Complex.exp (((capturedModulations2584 27 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 28 *
        (Complex.exp (((capturedModulations2584 28 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I))) + (record2680CorrectionCoefficient 29 *
        (Complex.exp (((capturedModulations2584 29 *
          record2680Center3212 16923 : ℝ) : ℂ) * Complex.I)))) := by
  apply ComplexRect2427.mem_add
  · apply ComplexRect2427.mem_add
    · apply ComplexRect2427.mem_add
      · apply ComplexRect2427.mem_add
        · exact record2680_cell16923_block25_group25to25_mem3271
        · exact record2680_cell16923_block25_group26to26_mem3271
      · exact record2680_cell16923_block25_group27to27_mem3271
    · exact record2680_cell16923_block25_group28to28_mem3271
  · exact record2680_cell16923_block25_group29to29_mem3271

end ConnesWeilRH.Dev
