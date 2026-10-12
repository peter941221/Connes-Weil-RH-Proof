import ConnesWeilRH.Dev.C1RouteARepairedOwnerCell2678
import ConnesWeilRH.Dev.C1RouteACellContainment2676Aggregates
import ConnesWeilRH.Dev.MatrixConsValFamily2637

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/- Record 2680: actual repaired correction owner, cell 4096, correction-M0. -/

noncomputable def record2680CorrectionCoefficient : Fin 30 → ℂ :=
  ![
    ⟨binary64Value2674 0x43812e3841ffb1e3, binary64Value2674 0x439e61841fe52416⟩,
    ⟨binary64Value2674 0xc34e0239d34fb3e1, binary64Value2674 0xc36b197776eb9db7⟩,
    ⟨binary64Value2674 0xbebafb010274fb17, binary64Value2674 0xbeb1b1e0470d24cf⟩,
    ⟨binary64Value2674 0x3eb5688ce4de2eac, binary64Value2674 0x3eadea9bcd4cb814⟩,
    ⟨binary64Value2674 0xc2e5528b272524e3, binary64Value2674 0xc2c7f19cf32e1ffb⟩,
    ⟨binary64Value2674 0xc1bc8c89c0cfa09f, binary64Value2674 0xc19a5605776dde56⟩,
    ⟨binary64Value2674 0x41bec3a10fd22b9f, binary64Value2674 0x41a2ef17cd93dce1⟩,
    ⟨binary64Value2674 0xc19f435e0cadfe6d, binary64Value2674 0xc18ca44fedd6cd1a⟩,
    ⟨binary64Value2674 0x429d205a14149eed, binary64Value2674 0xc26d181697f5db0e⟩,
    ⟨binary64Value2674 0xc2f3023e90541fa6, binary64Value2674 0xc2e6bf30f1686fc9⟩,
    ⟨binary64Value2674 0x430fb42039920a98, binary64Value2674 0x4310ce5c21397338⟩,
    ⟨binary64Value2674 0xc31d86944e2b8a51, binary64Value2674 0xc325bcec60096b80⟩,
    ⟨binary64Value2674 0x432625a50950540f, binary64Value2674 0x4336dbe1146e84d2⟩,
    ⟨binary64Value2674 0xc32b901e66b09ee7, binary64Value2674 0xc342ea176a22c67b⟩,
    ⟨binary64Value2674 0xc36de6e1c3a5635b, binary64Value2674 0xc38a72bccfff76d0⟩,
    ⟨binary64Value2674 0xc36ccf2be916189d, binary64Value2674 0xc38981552367d382⟩,
    ⟨binary64Value2674 0xc329d940d59a5727, binary64Value2674 0xc344b00d7c9a6bc8⟩,
    ⟨binary64Value2674 0x42fa8818cd8610e6, binary64Value2674 0xc2f48cf0322191d0⟩,
    ⟨binary64Value2674 0xc2f90cf62e2d7ced, binary64Value2674 0x4300d6a8a46d7d87⟩,
    ⟨binary64Value2674 0x42e946611f3a4b74, binary64Value2674 0xc2ed199b66e4102f⟩,
    ⟨binary64Value2674 0xc2e2d91fcf675977, binary64Value2674 0x42dca1074a1e43f9⟩,
    ⟨binary64Value2674 0x42e848a28187940b, binary64Value2674 0xc2d8e7b4f9a6b6cc⟩,
    ⟨binary64Value2674 0xc2e20eb85545e6f2, binary64Value2674 0x42cd3b94b79a01dc⟩,
    ⟨binary64Value2674 0x42ce79797065c05f, binary64Value2674 0xc29cf31f09183e15⟩,
    ⟨binary64Value2674 0xc2cebd8466fde1b1, binary64Value2674 0x42366b3044c4448e⟩,
    ⟨binary64Value2674 0x42c273d86472ed2d, binary64Value2674 0x42957729f9cdbf6e⟩,
    ⟨binary64Value2674 0xc2b30ea50e416898, binary64Value2674 0xc297238d3172e241⟩,
    ⟨binary64Value2674 0x42afca7fd367c6ad, binary64Value2674 0x42a1e5bd71f0f839⟩,
    ⟨binary64Value2674 0xc2ac16e10349f945, binary64Value2674 0xc2a31f6f9ae9ceeb⟩,
    ⟨binary64Value2674 0x4290004c85a0ed39, binary64Value2674 0x428cb984de3817ee⟩]

set_option maxRecDepth 10000 in theorem record2680Family0CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 0).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 0)
        (capturedModulations2584 0) (storedWidth 0 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family0PhiMem hx)
    (record2677Family0TrigMem hx).1 (record2677Family0TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 0)
    (theta := capturedModulations2584 0) (radius := storedWidth 0 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 0).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 0))
        record2677Family0MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 0))
      record2677Family0MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 0).reHi ∧
    (record2676CorrectionM0FamilyRects 0).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 0))
        record2677Family0MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 0))
      record2677Family0MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 0).imHi := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family0MidRect,
      record2677Family0PhiRect, record2677Family0CosRect,
      record2677Family0SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family1CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 1).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 1)
        (capturedModulations2584 1) (storedWidth 1 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family1PhiMem hx)
    (record2677Family1TrigMem hx).1 (record2677Family1TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 1)
    (theta := capturedModulations2584 1) (radius := storedWidth 1 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 1).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 1))
        record2677Family1MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 1))
      record2677Family1MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 1).reHi ∧
    (record2676CorrectionM0FamilyRects 1).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 1))
        record2677Family1MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 1))
      record2677Family1MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 1).imHi := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family1MidRect,
      record2677Family1PhiRect, record2677Family1CosRect,
      record2677Family1SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family2CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 2).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 2)
        (capturedModulations2584 2) (storedWidth 2 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family2PhiMem hx)
    (record2677Family2TrigMem hx).1 (record2677Family2TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 2)
    (theta := capturedModulations2584 2) (radius := storedWidth 2 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 2).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 2))
        record2677Family2MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 2))
      record2677Family2MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 2).reHi ∧
    (record2676CorrectionM0FamilyRects 2).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 2))
        record2677Family2MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 2))
      record2677Family2MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 2).imHi := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family2MidRect,
      record2677Family2PhiRect, record2677Family2CosRect,
      record2677Family2SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family3CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 3).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 3)
        (capturedModulations2584 3) (storedWidth 3 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family3PhiMem hx)
    (record2677Family3TrigMem hx).1 (record2677Family3TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 3)
    (theta := capturedModulations2584 3) (radius := storedWidth 3 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 3).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 3))
        record2677Family3MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 3))
      record2677Family3MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 3).reHi ∧
    (record2676CorrectionM0FamilyRects 3).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 3))
        record2677Family3MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 3))
      record2677Family3MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 3).imHi := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family3MidRect,
      record2677Family3PhiRect, record2677Family3CosRect,
      record2677Family3SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family4CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 4).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 4)
        (capturedModulations2584 4) (storedWidth 4 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family4PhiMem hx)
    (record2677Family4TrigMem hx).1 (record2677Family4TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 4)
    (theta := capturedModulations2584 4) (radius := storedWidth 4 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 4).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 4))
        record2677Family4MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 4))
      record2677Family4MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 4).reHi ∧
    (record2676CorrectionM0FamilyRects 4).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 4))
        record2677Family4MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 4))
      record2677Family4MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 4).imHi := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family4MidRect,
      record2677Family4PhiRect, record2677Family4CosRect,
      record2677Family4SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family5CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 5).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 5)
        (capturedModulations2584 5) (storedWidth 5 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family5PhiMem hx)
    (record2677Family5TrigMem hx).1 (record2677Family5TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 5)
    (theta := capturedModulations2584 5) (radius := storedWidth 5 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 5).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 5))
        record2677Family5MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 5))
      record2677Family5MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 5).reHi ∧
    (record2676CorrectionM0FamilyRects 5).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 5))
        record2677Family5MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 5))
      record2677Family5MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 5).imHi := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family5MidRect,
      record2677Family5PhiRect, record2677Family5CosRect,
      record2677Family5SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family6CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 6).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 6)
        (capturedModulations2584 6) (storedWidth 6 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family6PhiMem hx)
    (record2677Family6TrigMem hx).1 (record2677Family6TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 6)
    (theta := capturedModulations2584 6) (radius := storedWidth 6 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 6).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 6))
        record2677Family6MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 6))
      record2677Family6MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 6).reHi ∧
    (record2676CorrectionM0FamilyRects 6).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 6))
        record2677Family6MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 6))
      record2677Family6MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 6).imHi := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family6MidRect,
      record2677Family6PhiRect, record2677Family6CosRect,
      record2677Family6SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family7CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 7).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 7)
        (capturedModulations2584 7) (storedWidth 7 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family7PhiMem hx)
    (record2677Family7TrigMem hx).1 (record2677Family7TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 7)
    (theta := capturedModulations2584 7) (radius := storedWidth 7 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 7).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 7))
        record2677Family7MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 7))
      record2677Family7MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 7).reHi ∧
    (record2676CorrectionM0FamilyRects 7).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 7))
        record2677Family7MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 7))
      record2677Family7MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 7).imHi := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family7MidRect,
      record2677Family7PhiRect, record2677Family7CosRect,
      record2677Family7SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family8CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 8).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 8)
        (capturedModulations2584 8) (storedWidth 8 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family8PhiMem hx)
    (record2677Family8TrigMem hx).1 (record2677Family8TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 8)
    (theta := capturedModulations2584 8) (radius := storedWidth 8 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 8).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 8))
        record2677Family8MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 8))
      record2677Family8MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 8).reHi ∧
    (record2676CorrectionM0FamilyRects 8).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 8))
        record2677Family8MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 8))
      record2677Family8MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 8).imHi := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family8MidRect,
      record2677Family8PhiRect, record2677Family8CosRect,
      record2677Family8SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family9CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 9).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 9)
        (capturedModulations2584 9) (storedWidth 9 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family9PhiMem hx)
    (record2677Family9TrigMem hx).1 (record2677Family9TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 9)
    (theta := capturedModulations2584 9) (radius := storedWidth 9 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 9).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 9))
        record2677Family9MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 9))
      record2677Family9MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 9).reHi ∧
    (record2676CorrectionM0FamilyRects 9).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 9))
        record2677Family9MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 9))
      record2677Family9MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 9).imHi := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family9MidRect,
      record2677Family9PhiRect, record2677Family9CosRect,
      record2677Family9SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family10CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 10).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 10)
        (capturedModulations2584 10) (storedWidth 10 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family10PhiMem hx)
    (record2677Family10TrigMem hx).1 (record2677Family10TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 10)
    (theta := capturedModulations2584 10) (radius := storedWidth 10 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 10).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 10))
        record2677Family10MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 10))
      record2677Family10MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 10).reHi ∧
    (record2676CorrectionM0FamilyRects 10).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 10))
        record2677Family10MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 10))
      record2677Family10MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 10).imHi := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family10MidRect,
      record2677Family10PhiRect, record2677Family10CosRect,
      record2677Family10SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family11CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 11).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 11)
        (capturedModulations2584 11) (storedWidth 11 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family11PhiMem hx)
    (record2677Family11TrigMem hx).1 (record2677Family11TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 11)
    (theta := capturedModulations2584 11) (radius := storedWidth 11 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 11).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 11))
        record2677Family11MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 11))
      record2677Family11MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 11).reHi ∧
    (record2676CorrectionM0FamilyRects 11).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 11))
        record2677Family11MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 11))
      record2677Family11MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 11).imHi := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family11MidRect,
      record2677Family11PhiRect, record2677Family11CosRect,
      record2677Family11SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family12CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 12).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 12)
        (capturedModulations2584 12) (storedWidth 12 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family12PhiMem hx)
    (record2677Family12TrigMem hx).1 (record2677Family12TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 12)
    (theta := capturedModulations2584 12) (radius := storedWidth 12 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 12).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 12))
        record2677Family12MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 12))
      record2677Family12MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 12).reHi ∧
    (record2676CorrectionM0FamilyRects 12).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 12))
        record2677Family12MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 12))
      record2677Family12MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 12).imHi := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family12MidRect,
      record2677Family12PhiRect, record2677Family12CosRect,
      record2677Family12SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family13CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 13).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 13)
        (capturedModulations2584 13) (storedWidth 13 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family13PhiMem hx)
    (record2677Family13TrigMem hx).1 (record2677Family13TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 13)
    (theta := capturedModulations2584 13) (radius := storedWidth 13 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 13).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 13))
        record2677Family13MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 13))
      record2677Family13MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 13).reHi ∧
    (record2676CorrectionM0FamilyRects 13).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 13))
        record2677Family13MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 13))
      record2677Family13MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 13).imHi := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family13MidRect,
      record2677Family13PhiRect, record2677Family13CosRect,
      record2677Family13SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family14CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 14).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 14)
        (capturedModulations2584 14) (storedWidth 14 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family14PhiMem hx)
    (record2677Family14TrigMem hx).1 (record2677Family14TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 14)
    (theta := capturedModulations2584 14) (radius := storedWidth 14 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 14).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 14))
        record2677Family14MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 14))
      record2677Family14MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 14).reHi ∧
    (record2676CorrectionM0FamilyRects 14).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 14))
        record2677Family14MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 14))
      record2677Family14MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 14).imHi := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family14MidRect,
      record2677Family14PhiRect, record2677Family14CosRect,
      record2677Family14SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family15CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 15).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 15)
        (capturedModulations2584 15) (storedWidth 15 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family15PhiMem hx)
    (record2677Family15TrigMem hx).1 (record2677Family15TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 15)
    (theta := capturedModulations2584 15) (radius := storedWidth 15 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 15).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 15))
        record2677Family15MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 15))
      record2677Family15MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 15).reHi ∧
    (record2676CorrectionM0FamilyRects 15).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 15))
        record2677Family15MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 15))
      record2677Family15MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 15).imHi := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family15MidRect,
      record2677Family15PhiRect, record2677Family15CosRect,
      record2677Family15SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family16CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 16).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 16)
        (capturedModulations2584 16) (storedWidth 16 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family16PhiMem hx)
    (record2677Family16TrigMem hx).1 (record2677Family16TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 16)
    (theta := capturedModulations2584 16) (radius := storedWidth 16 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 16).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 16))
        record2677Family16MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 16))
      record2677Family16MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 16).reHi ∧
    (record2676CorrectionM0FamilyRects 16).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 16))
        record2677Family16MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 16))
      record2677Family16MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 16).imHi := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family16MidRect,
      record2677Family16PhiRect, record2677Family16CosRect,
      record2677Family16SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family17CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 17).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 17)
        (capturedModulations2584 17) (storedWidth 17 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family17PhiMem hx)
    (record2677Family17TrigMem hx).1 (record2677Family17TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 17)
    (theta := capturedModulations2584 17) (radius := storedWidth 17 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 17).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 17))
        record2677Family17MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 17))
      record2677Family17MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 17).reHi ∧
    (record2676CorrectionM0FamilyRects 17).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 17))
        record2677Family17MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 17))
      record2677Family17MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 17).imHi := by
    norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family17MidRect,
      record2677Family17PhiRect, record2677Family17CosRect,
      record2677Family17SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family18CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 18).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 18)
        (capturedModulations2584 18) (storedWidth 18 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family18PhiMem hx)
    (record2677Family18TrigMem hx).1 (record2677Family18TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 18)
    (theta := capturedModulations2584 18) (radius := storedWidth 18 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 18).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 18))
        record2677Family18MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 18))
      record2677Family18MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 18).reHi ∧
    (record2676CorrectionM0FamilyRects 18).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 18))
        record2677Family18MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 18))
      record2677Family18MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 18).imHi := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family18MidRect,
      record2677Family18PhiRect, record2677Family18CosRect,
      record2677Family18SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family19CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 19).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 19)
        (capturedModulations2584 19) (storedWidth 19 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family19PhiMem hx)
    (record2677Family19TrigMem hx).1 (record2677Family19TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 19)
    (theta := capturedModulations2584 19) (radius := storedWidth 19 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 19).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 19))
        record2677Family19MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 19))
      record2677Family19MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 19).reHi ∧
    (record2676CorrectionM0FamilyRects 19).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 19))
        record2677Family19MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 19))
      record2677Family19MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 19).imHi := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family19MidRect,
      record2677Family19PhiRect, record2677Family19CosRect,
      record2677Family19SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family20CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 20).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 20)
        (capturedModulations2584 20) (storedWidth 20 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family20PhiMem hx)
    (record2677Family20TrigMem hx).1 (record2677Family20TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 20)
    (theta := capturedModulations2584 20) (radius := storedWidth 20 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 20).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 20))
        record2677Family20MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 20))
      record2677Family20MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 20).reHi ∧
    (record2676CorrectionM0FamilyRects 20).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 20))
        record2677Family20MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 20))
      record2677Family20MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 20).imHi := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family20MidRect,
      record2677Family20PhiRect, record2677Family20CosRect,
      record2677Family20SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family21CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 21).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 21)
        (capturedModulations2584 21) (storedWidth 21 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family21PhiMem hx)
    (record2677Family21TrigMem hx).1 (record2677Family21TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 21)
    (theta := capturedModulations2584 21) (radius := storedWidth 21 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 21).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 21))
        record2677Family21MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 21))
      record2677Family21MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 21).reHi ∧
    (record2676CorrectionM0FamilyRects 21).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 21))
        record2677Family21MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 21))
      record2677Family21MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 21).imHi := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family21MidRect,
      record2677Family21PhiRect, record2677Family21CosRect,
      record2677Family21SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family22CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 22).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 22)
        (capturedModulations2584 22) (storedWidth 22 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family22PhiMem hx)
    (record2677Family22TrigMem hx).1 (record2677Family22TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 22)
    (theta := capturedModulations2584 22) (radius := storedWidth 22 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 22).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 22))
        record2677Family22MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 22))
      record2677Family22MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 22).reHi ∧
    (record2676CorrectionM0FamilyRects 22).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 22))
        record2677Family22MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 22))
      record2677Family22MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 22).imHi := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family22MidRect,
      record2677Family22PhiRect, record2677Family22CosRect,
      record2677Family22SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family23CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 23).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 23)
        (capturedModulations2584 23) (storedWidth 23 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family23PhiMem hx)
    (record2677Family23TrigMem hx).1 (record2677Family23TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 23)
    (theta := capturedModulations2584 23) (radius := storedWidth 23 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 23).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 23))
        record2677Family23MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 23))
      record2677Family23MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 23).reHi ∧
    (record2676CorrectionM0FamilyRects 23).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 23))
        record2677Family23MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 23))
      record2677Family23MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 23).imHi := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family23MidRect,
      record2677Family23PhiRect, record2677Family23CosRect,
      record2677Family23SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family24CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 24).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 24)
        (capturedModulations2584 24) (storedWidth 24 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family24PhiMem hx)
    (record2677Family24TrigMem hx).1 (record2677Family24TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 24)
    (theta := capturedModulations2584 24) (radius := storedWidth 24 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 24).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 24))
        record2677Family24MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 24))
      record2677Family24MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 24).reHi ∧
    (record2676CorrectionM0FamilyRects 24).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 24))
        record2677Family24MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 24))
      record2677Family24MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 24).imHi := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family24MidRect,
      record2677Family24PhiRect, record2677Family24CosRect,
      record2677Family24SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family25CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 25).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 25)
        (capturedModulations2584 25) (storedWidth 25 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family25PhiMem hx)
    (record2677Family25TrigMem hx).1 (record2677Family25TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 25)
    (theta := capturedModulations2584 25) (radius := storedWidth 25 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 25).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 25))
        record2677Family25MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 25))
      record2677Family25MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 25).reHi ∧
    (record2676CorrectionM0FamilyRects 25).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 25))
        record2677Family25MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 25))
      record2677Family25MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 25).imHi := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family25MidRect,
      record2677Family25PhiRect, record2677Family25CosRect,
      record2677Family25SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family26CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 26).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 26)
        (capturedModulations2584 26) (storedWidth 26 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family26PhiMem hx)
    (record2677Family26TrigMem hx).1 (record2677Family26TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 26)
    (theta := capturedModulations2584 26) (radius := storedWidth 26 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 26).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 26))
        record2677Family26MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 26))
      record2677Family26MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 26).reHi ∧
    (record2676CorrectionM0FamilyRects 26).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 26))
        record2677Family26MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 26))
      record2677Family26MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 26).imHi := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family26MidRect,
      record2677Family26PhiRect, record2677Family26CosRect,
      record2677Family26SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family27CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 27).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 27)
        (capturedModulations2584 27) (storedWidth 27 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family27PhiMem hx)
    (record2677Family27TrigMem hx).1 (record2677Family27TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 27)
    (theta := capturedModulations2584 27) (radius := storedWidth 27 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 27).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 27))
        record2677Family27MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 27))
      record2677Family27MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 27).reHi ∧
    (record2676CorrectionM0FamilyRects 27).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 27))
        record2677Family27MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 27))
      record2677Family27MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 27).imHi := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family27MidRect,
      record2677Family27PhiRect, record2677Family27CosRect,
      record2677Family27SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family28CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 28).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 28)
        (capturedModulations2584 28) (storedWidth 28 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family28PhiMem hx)
    (record2677Family28TrigMem hx).1 (record2677Family28TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 28)
    (theta := capturedModulations2584 28) (radius := storedWidth 28 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 28).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 28))
        record2677Family28MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 28))
      record2677Family28MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 28).reHi ∧
    (record2676CorrectionM0FamilyRects 28).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 28))
        record2677Family28MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 28))
      record2677Family28MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 28).imHi := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family28MidRect,
      record2677Family28PhiRect, record2677Family28CosRect,
      record2677Family28SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2680Family29CorrectionM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2676CorrectionM0FamilyRects 29).Mem
      (externalFamilyValue2344 (record2680CorrectionCoefficient 29)
        (capturedModulations2584 29) (storedWidth 29 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family29PhiMem hx)
    (record2677Family29TrigMem hx).1 (record2677Family29TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2680CorrectionCoefficient 29)
    (theta := capturedModulations2584 29) (radius := storedWidth 29 ^ 2)
    (x := x) hmid
  have hsub : (record2676CorrectionM0FamilyRects 29).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 29))
        record2677Family29MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 29))
      record2677Family29MidRect).reHi ≤ (record2676CorrectionM0FamilyRects 29).reHi ∧
    (record2676CorrectionM0FamilyRects 29).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 29))
        record2677Family29MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2680CorrectionCoefficient 29))
      record2677Family29MidRect).imHi ≤ (record2676CorrectionM0FamilyRects 29).imHi := by
    norm_num [Matrix.cons_val_29, Matrix.cons_val_zero, record2676CorrectionM0FamilyRects,
      record2680CorrectionCoefficient, record2677Family29MidRect,
      record2677Family29PhiRect, record2677Family29CosRect,
      record2677Family29SinRect, ComplexRect2427.mul, RealInterval2429.mul,
      RealInterval2429.add, RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674,
      binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

theorem record2680CorrectionM0CellContained {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    record2675CorrectionM0Rect.Mem
      (externalPhysical2344 record2680CorrectionCoefficient
        capturedModulations2584 x) := by
  have hfamily : ∀ index position, position ∈ Set.Icc 0 record2675CellRight →
      (record2676CorrectionM0FamilyRects index).Mem
        (externalFamilyValue2344 (record2680CorrectionCoefficient index)
          (capturedModulations2584 index) (storedWidth index ^ 2) position) := by
    intro index position hposition
    fin_cases index
    · exact record2680Family0CorrectionM0CellRectMem hposition
    · exact record2680Family1CorrectionM0CellRectMem hposition
    · exact record2680Family2CorrectionM0CellRectMem hposition
    · exact record2680Family3CorrectionM0CellRectMem hposition
    · exact record2680Family4CorrectionM0CellRectMem hposition
    · exact record2680Family5CorrectionM0CellRectMem hposition
    · exact record2680Family6CorrectionM0CellRectMem hposition
    · exact record2680Family7CorrectionM0CellRectMem hposition
    · exact record2680Family8CorrectionM0CellRectMem hposition
    · exact record2680Family9CorrectionM0CellRectMem hposition
    · exact record2680Family10CorrectionM0CellRectMem hposition
    · exact record2680Family11CorrectionM0CellRectMem hposition
    · exact record2680Family12CorrectionM0CellRectMem hposition
    · exact record2680Family13CorrectionM0CellRectMem hposition
    · exact record2680Family14CorrectionM0CellRectMem hposition
    · exact record2680Family15CorrectionM0CellRectMem hposition
    · exact record2680Family16CorrectionM0CellRectMem hposition
    · exact record2680Family17CorrectionM0CellRectMem hposition
    · exact record2680Family18CorrectionM0CellRectMem hposition
    · exact record2680Family19CorrectionM0CellRectMem hposition
    · exact record2680Family20CorrectionM0CellRectMem hposition
    · exact record2680Family21CorrectionM0CellRectMem hposition
    · exact record2680Family22CorrectionM0CellRectMem hposition
    · exact record2680Family23CorrectionM0CellRectMem hposition
    · exact record2680Family24CorrectionM0CellRectMem hposition
    · exact record2680Family25CorrectionM0CellRectMem hposition
    · exact record2680Family26CorrectionM0CellRectMem hposition
    · exact record2680Family27CorrectionM0CellRectMem hposition
    · exact record2680Family28CorrectionM0CellRectMem hposition
    · exact record2680Family29CorrectionM0CellRectMem hposition
  exact (correction_M0CellSumContained (coefficients := record2680CorrectionCoefficient)
    (modulations := capturedModulations2584) hfamily) x hx

end ConnesWeilRH.Dev
