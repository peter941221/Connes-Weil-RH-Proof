import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem firstJetMidpointMinus_triangle2565 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

theorem fjminZero2565 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def fjminP000Center2565 : RatPair2542 := (0, 0)

def fjminP000Factor2565 : RatPair2542 := (0, 0)

noncomputable def fjminP000Error2565 : ℝ := 0

theorem fjminP000Exterior2565 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n (-1/2)
    (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem fjminP000BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP000Center2565‖ ≤ fjminP000Error2565 := by
  rw [fjminP000Exterior2565]
  norm_num [fjminP000Center2565, fjminP000Error2565, fjminZero2565]

theorem fjminP000DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP000Factor2565 * embedPair2542 fjminP000Center2565‖ ≤
        (pairMagnitude2542 fjminP000Factor2565 : ℝ) * fjminP000Error2565 := by
  rw [fjminP000Exterior2565]
  norm_num [fjminP000Factor2565, fjminP000Center2565, fjminP000Error2565, pairMagnitude2542,
      fjminZero2565]

def fjminP000Rounded2565 : RatPair2542 := (0, 0)

noncomputable def fjminP000Radius2565 : ℝ := 0

theorem fjminP000RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP000Factor2565 fjminP000Center2565) = fjminP000Rounded2565 :=
        by
  cbv

theorem fjminP000RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP000Rounded2565‖ ≤ fjminP000Radius2565 := by
  rw [fjminP000Exterior2565]
  norm_num [fjminP000Rounded2565, fjminP000Radius2565, fjminZero2565]

theorem fjminP000DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [fjminP000Exterior2565]
  norm_num

noncomputable def fjminP001Input2565 : RatPair2542 := ((((-((74 * 10^40
        + 3163554082308786923030623187936917919547) * 10^40
        + 6189645194398852582143451811084217740401)) : ℚ) /
        ((208 * 10^40
        + 8043940912794372598641292711490528776820) * 10^40
        + 5100987153752063079186153183641600000000)),
    ((1751911280236833479653958331 : ℚ) /
        7378697629483820646400000000))

def fjminP001Center2565 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjminP001Factor2565 : RatPair2542 := ((((((48206378145472865255 * 10^40
        + 4558879378186968721762698369388365651076) * 10^40
        + 8183683534072696621069541849066993590601) * 10^40
        + 1799131963158929497400353332108237304719) : ℚ) /
        (((79306619212413954 * 10^40
        + 6135590275954697994891057369985995860880) * 10^40
        + 3799340399814374588299513654302616835559) * 10^40
        + 5354338069519581005199293335783525390562)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjminP001Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP001BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP001Center2565‖ ≤ fjminP001Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP001Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP001Input2565]
  have hc : (compactExp2547 fjminP001Input2565 9).1 = fjminP001Center2565 := by cbv
  have he : ((compactExp2547 fjminP001Input2565 9).2 : ℝ) = fjminP001Error2565 := by
    have hq : (compactExp2547 fjminP001Input2565 9).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP001Error2565]
  have h := compactExp_error2547 fjminP001Input2565 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^9 * embedPair2542 fjminP001Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP001Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP001DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP001Factor2565 * embedPair2542 fjminP001Center2565‖ ≤
        (pairMagnitude2542 fjminP001Factor2565 : ℝ) * fjminP001Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP001Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP001Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP001BaseError2565
    (embedPair_magnitude2542 fjminP001Factor2565)

def fjminP001Rounded2565 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fjminP001Radius2565 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP001RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP001Factor2565 fjminP001Center2565) = fjminP001Rounded2565 :=
        by
  cbv

theorem fjminP001RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP001Rounded2565‖ ≤ fjminP001Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP001Factor2565 fjminP001Center2565)
  rw [fjminP001RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP001Factor2565 * embedPair2542 fjminP001Center2565)
    (embedPair2542 fjminP001Rounded2565)).trans (add_le_add fjminP001DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP001Factor2565, fjminP001Error2565, rounding2542,
      fjminP001Radius2565]

theorem fjminP001DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP001Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP001RoundedError2565 (embedPair_magnitude2542
      fjminP001Rounded2565))
  apply h'.trans
  norm_num [fjminP001Radius2565, pairMagnitude2542, fjminP001Rounded2565]

noncomputable def fjminP002Input2565 : RatPair2542 := ((((-((1908 * 10^40
        + 9356477313226526661601126851044270189063) * 10^40
        + 5191776234307827898306730134726634237041)) : ℚ) /
        ((8147 * 10^40
        + 6895918656149932623563298325318453465194) * 10^40
        + 9452298146475584633489225469132800000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def fjminP002Center2565 : RatPair2542 := ((((-7510330962121851658113) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-167206057629782703065) : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)))

def fjminP002Factor2565 : RatPair2542 := ((((((19927458173227725776043 * 10^40
        + 2690117318636346021192956930819447261675) * 10^40
        + 7606482230257965636231267455327844182840) * 10^40
        + 2667446867398360400948527094263193367439) : ℚ) /
        (((483013323431043476903 * 10^40
        + 7511499335200218287611909907279225454881) * 10^40
        + 746082615335519961120361053248712426867) * 10^40
        + 9194345188221519198102945811473613265122)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjminP002Error2565 : ℝ := ((47917824040196111573 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP002BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP002Center2565‖ ≤ fjminP002Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP002Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP002Input2565]
  have hc : (compactExp2547 fjminP002Input2565 8).1 = fjminP002Center2565 := by cbv
  have he : ((compactExp2547 fjminP002Input2565 8).2 : ℝ) = fjminP002Error2565 := by
    have hq : (compactExp2547 fjminP002Input2565 8).2 =
        ((47917824040196111573 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP002Error2565]
  have h := compactExp_error2547 fjminP002Input2565 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjminP002Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP002Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP002DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP002Factor2565 * embedPair2542 fjminP002Center2565‖ ≤
        (pairMagnitude2542 fjminP002Factor2565 : ℝ) * fjminP002Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP002Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP002Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP002BaseError2565
    (embedPair_magnitude2542 fjminP002Factor2565)

def fjminP002Rounded2565 : RatPair2542 :=
  (((95581 : ℚ) /
        1267650600228229401496703205376),
    (((-638633) : ℚ) /
        1267650600228229401496703205376))

noncomputable def fjminP002Radius2565 : ℝ := ((2199023258899 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP002RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP002Factor2565 fjminP002Center2565) = fjminP002Rounded2565 :=
        by
  cbv

theorem fjminP002RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP002Rounded2565‖ ≤ fjminP002Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP002Factor2565 fjminP002Center2565)
  rw [fjminP002RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP002Factor2565 * embedPair2542 fjminP002Center2565)
    (embedPair2542 fjminP002Rounded2565)).trans (add_le_add fjminP002DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP002Factor2565, fjminP002Error2565, rounding2542,
      fjminP002Radius2565]

theorem fjminP002DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP002Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP002RoundedError2565 (embedPair_magnitude2542
      fjminP002Rounded2565))
  apply h'.trans
  norm_num [fjminP002Radius2565, pairMagnitude2542, fjminP002Rounded2565]

noncomputable def fjminP003Input2565 : RatPair2542 := ((((-((6741898 * 10^40
        + 8650175576592174173380311150688129946428) * 10^40
        + 2573857778485855228570792044839354408089)) : ℚ) /
        ((39860431 * 10^40
        + 3525369205518296877772896888819194996209) * 10^40
        + 8027785848626107559175480881971200000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def fjminP003Center2565 : RatPair2542 := ((((-16457100312752944049586069821) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-187592818628376015785955978523) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def fjminP003Factor2565 : RatPair2542 := ((((((159929187887964078749905774346 * 10^40
        + 2911106577035738550624706132091463509159) * 10^40
        + 2192779424272312654623211523507388653835) * 10^40
        + 3667550152654527134075141835527094175999) : ℚ) /
        (((11560434268978921445520672852 * 10^40
        + 3151491610707945740034502288795420775469) * 10^40
        + 9342842308133684351566010846049001848136) * 10^40
        + 2052163694690945731849716328945811648002)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjminP003Error2565 : ℝ := ((787019084893669535021784089 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP003BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP003Center2565‖ ≤ fjminP003Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP003Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP003Input2565]
  have hc : (compactExp2547 fjminP003Input2565 8).1 = fjminP003Center2565 := by cbv
  have he : ((compactExp2547 fjminP003Input2565 8).2 : ℝ) = fjminP003Error2565 := by
    have hq : (compactExp2547 fjminP003Input2565 8).2 =
        ((787019084893669535021784089 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP003Error2565]
  have h := compactExp_error2547 fjminP003Input2565 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjminP003Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP003Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP003DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP003Factor2565 * embedPair2542 fjminP003Center2565‖ ≤
        (pairMagnitude2542 fjminP003Factor2565 : ℝ) * fjminP003Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP003Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP003Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP003BaseError2565
    (embedPair_magnitude2542 fjminP003Factor2565)

def fjminP003Rounded2565 : RatPair2542 :=
  (((2403508333533 : ℚ) /
        633825300114114700748351602688),
    (((-3366684385075) : ℚ) /
        633825300114114700748351602688))

noncomputable def fjminP003Radius2565 : ℝ := ((2235261797137 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP003RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP003Factor2565 fjminP003Center2565) = fjminP003Rounded2565 :=
        by
  cbv

theorem fjminP003RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP003Rounded2565‖ ≤ fjminP003Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP003Factor2565 fjminP003Center2565)
  rw [fjminP003RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP003Factor2565 * embedPair2542 fjminP003Center2565)
    (embedPair2542 fjminP003Rounded2565)).trans (add_le_add fjminP003DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP003Factor2565, fjminP003Error2565, rounding2542,
      fjminP003Radius2565]

theorem fjminP003DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP003Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP003RoundedError2565 (embedPair_magnitude2542
      fjminP003Rounded2565))
  apply h'.trans
  norm_num [fjminP003Radius2565, pairMagnitude2542, fjminP003Rounded2565]

noncomputable def fjminP004Input2565 : RatPair2542 := ((((-((4313 * 10^40
        + 1891010053817582509092773862775633242315) * 10^40
        + 9610172859229760383941744954062571737041)) : ℚ) /
        ((29780 * 10^40
        + 5895054484312759971766663273404887092534) * 10^40
        + 1331668037402944633489225469132800000000)),
    ((1751911280236833479653958331 : ℚ) /
        3689348814741910323200000000))

def fjminP004Center2565 : RatPair2542 := ((((-66328937998152592934425233428247) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((23627401317734783120891400711731 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def fjminP004Factor2565 : RatPair2542 := ((((((43053193436111892580981 * 10^40
        + 5268077254950526113516014890382988751958) * 10^40
        + 9368333013603576308597948378269469887780) * 10^40
        + 526438913939257057324931049341318367439) : ℚ) /
        (((6452926836878943435502 * 10^40
        + 5270363476754729271482605203204217239397) * 10^40
        + 2433289965035647104971396368485606800583) * 10^40
        + 9158788578070925885350137901317363265122)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjminP004Error2565 : ℝ := ((386980696826640705426490371081 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP004BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP004Center2565‖ ≤ fjminP004Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP004Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP004Input2565]
  have hc : (compactExp2547 fjminP004Input2565 8).1 = fjminP004Center2565 := by cbv
  have he : ((compactExp2547 fjminP004Input2565 8).2 : ℝ) = fjminP004Error2565 := by
    have hq : (compactExp2547 fjminP004Input2565 8).2 =
        ((386980696826640705426490371081 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP004Error2565]
  have h := compactExp_error2547 fjminP004Input2565 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjminP004Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP004Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP004DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP004Factor2565 * embedPair2542 fjminP004Center2565‖ ≤
        (pairMagnitude2542 fjminP004Factor2565 : ℝ) * fjminP004Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP004Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP004Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP004BaseError2565
    (embedPair_magnitude2542 fjminP004Factor2565)

def fjminP004Rounded2565 : RatPair2542 :=
  (((2833839323295303 : ℚ) /
        1267650600228229401496703205376),
    ((2805161102151451 : ℚ) /
        1267650600228229401496703205376))

noncomputable def fjminP004Radius2565 : ℝ := ((2201703692675 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem fjminP004RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP004Factor2565 fjminP004Center2565) = fjminP004Rounded2565 :=
        by
  cbv

theorem fjminP004RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP004Rounded2565‖ ≤ fjminP004Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP004Factor2565 fjminP004Center2565)
  rw [fjminP004RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP004Factor2565 * embedPair2542 fjminP004Center2565)
    (embedPair2542 fjminP004Rounded2565)).trans (add_le_add fjminP004DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP004Factor2565, fjminP004Error2565, rounding2542,
      fjminP004Radius2565]

theorem fjminP004DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP004Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP004RoundedError2565 (embedPair_magnitude2542
      fjminP004Rounded2565))
  apply h'.trans
  norm_num [fjminP004Radius2565, pairMagnitude2542, fjminP004Rounded2565]

def fjminP005Center2565 : RatPair2542 := (0, 0)

def fjminP005Factor2565 : RatPair2542 := (0, 0)

noncomputable def fjminP005Error2565 : ℝ := 0

theorem fjminP005Exterior2565 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n (-1/2)
    (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem fjminP005BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP005Center2565‖ ≤ fjminP005Error2565 := by
  rw [fjminP005Exterior2565]
  norm_num [fjminP005Center2565, fjminP005Error2565, fjminZero2565]

theorem fjminP005DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP005Factor2565 * embedPair2542 fjminP005Center2565‖ ≤
        (pairMagnitude2542 fjminP005Factor2565 : ℝ) * fjminP005Error2565 := by
  rw [fjminP005Exterior2565]
  norm_num [fjminP005Factor2565, fjminP005Center2565, fjminP005Error2565, pairMagnitude2542,
      fjminZero2565]

def fjminP005Rounded2565 : RatPair2542 := (0, 0)

noncomputable def fjminP005Radius2565 : ℝ := 0

theorem fjminP005RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP005Factor2565 fjminP005Center2565) = fjminP005Rounded2565 :=
        by
  cbv

theorem fjminP005RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP005Rounded2565‖ ≤ fjminP005Radius2565 := by
  rw [fjminP005Exterior2565]
  norm_num [fjminP005Rounded2565, fjminP005Radius2565, fjminZero2565]

theorem fjminP005DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [fjminP005Exterior2565]
  norm_num

noncomputable def fjminP006Input2565 : RatPair2542 := ((((-1009480612784001817040786481870793719)
    : ℚ) /
        1761648103394083163919587737600000000),
    ((0 : ℚ) /
        1))

def fjminP006Center2565 : RatPair2542 := (((2552935579348625 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def fjminP006Factor2565 : RatPair2542 := ((((64927152 * 10^40
        + 630156867445020113682589906669419017759) : ℚ) /
        (903209 * 10^40
        + 4502448949280199772634820186661161964482)),
    ((0 : ℚ) /
        1))

noncomputable def fjminP006Error2565 : ℝ := ((3648537530399 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem fjminP006BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP006Center2565‖ ≤ fjminP006Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP006Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP006Input2565]
  have hc : (compactExp2547 fjminP006Input2565 7).1 = fjminP006Center2565 := by cbv
  have he : ((compactExp2547 fjminP006Input2565 7).2 : ℝ) = fjminP006Error2565 := by
    have hq : (compactExp2547 fjminP006Input2565 7).2 =
        ((3648537530399 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [fjminP006Error2565]
  have h := compactExp_error2547 fjminP006Input2565 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^7 * embedPair2542 fjminP006Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP006Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP006DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP006Factor2565 * embedPair2542 fjminP006Center2565‖ ≤
        (pairMagnitude2542 fjminP006Factor2565 : ℝ) * fjminP006Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP006Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP006Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP006BaseError2565
    (embedPair_magnitude2542 fjminP006Factor2565)

def fjminP006Rounded2565 : RatPair2542 :=
  (((1 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fjminP006Radius2565 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP006RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP006Factor2565 fjminP006Center2565) = fjminP006Rounded2565 :=
        by
  cbv

theorem fjminP006RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP006Rounded2565‖ ≤ fjminP006Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP006Factor2565 fjminP006Center2565)
  rw [fjminP006RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP006Factor2565 * embedPair2542 fjminP006Center2565)
    (embedPair2542 fjminP006Rounded2565)).trans (add_le_add fjminP006DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP006Factor2565, fjminP006Error2565, rounding2542,
      fjminP006Radius2565]

theorem fjminP006DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP006Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP006RoundedError2565 (embedPair_magnitude2542
      fjminP006Rounded2565))
  apply h'.trans
  norm_num [fjminP006Radius2565, pairMagnitude2542, fjminP006Rounded2565]

noncomputable def fjminP007Input2565 : RatPair2542 := ((((-((6741898 * 10^40
        + 8650175576592174173380311150688129946428) * 10^40
        + 2573857778485855228570792044839354408089)) : ℚ) /
        ((9965107 * 10^40
        + 8381342301379574219443224222204798749052) * 10^40
        + 4506946462156526889793870220492800000000)),
    ((0 : ℚ) /
        1))

def fjminP007Center2565 : RatPair2542 := (((57295603695874659276408122021 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

def fjminP007Factor2565 : RatPair2542 := ((((((159929187887964078749905774346 * 10^40
        + 2911106577035738550624706132091463509159) * 10^40
        + 2192779424272312654623211523507388653835) * 10^40
        + 3667550152654527134075141835527094175999) : ℚ) /
        (((11560434268978921445520672852 * 10^40
        + 3151491610707945740034502288795420775469) * 10^40
        + 9342842308133684351566010846049001848136) * 10^40
        + 2052163694690945731849716328945811648002)),
    ((0 : ℚ) /
        1))

noncomputable def fjminP007Error2565 : ℝ := ((31723657183144844024517521 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP007BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP007Center2565‖ ≤ fjminP007Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP007Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP007Input2565]
  have hc : (compactExp2547 fjminP007Input2565 6).1 = fjminP007Center2565 := by cbv
  have he : ((compactExp2547 fjminP007Input2565 6).2 : ℝ) = fjminP007Error2565 := by
    have hq : (compactExp2547 fjminP007Input2565 6).2 =
        ((31723657183144844024517521 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP007Error2565]
  have h := compactExp_error2547 fjminP007Input2565 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^6 * embedPair2542 fjminP007Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP007Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP007DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP007Factor2565 * embedPair2542 fjminP007Center2565‖ ≤
        (pairMagnitude2542 fjminP007Factor2565 : ℝ) * fjminP007Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP007Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP007Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP007BaseError2565
    (embedPair_magnitude2542 fjminP007Factor2565)

def fjminP007Rounded2565 : RatPair2542 :=
  (((343751931781 : ℚ) /
        158456325028528675187087900672),
    ((0 : ℚ) /
        1))

noncomputable def fjminP007Radius2565 : ℝ := ((2199403915419 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP007RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP007Factor2565 fjminP007Center2565) = fjminP007Rounded2565 :=
        by
  cbv

theorem fjminP007RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP007Rounded2565‖ ≤ fjminP007Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP007Factor2565 fjminP007Center2565)
  rw [fjminP007RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP007Factor2565 * embedPair2542 fjminP007Center2565)
    (embedPair2542 fjminP007Rounded2565)).trans (add_le_add fjminP007DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP007Factor2565, fjminP007Error2565, rounding2542,
      fjminP007Radius2565]

theorem fjminP007DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP007Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP007RoundedError2565 (embedPair_magnitude2542
      fjminP007Rounded2565))
  apply h'.trans
  norm_num [fjminP007Radius2565, pairMagnitude2542, fjminP007Rounded2565]

noncomputable def fjminP008Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1261719220645415482412484183 : ℚ) /
        3777893186295716170956800000000))

def fjminP008Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP008Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3978571430081297) : ℚ) /
        281474976710656))

noncomputable def fjminP008Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP008BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP008Center2565‖ ≤ fjminP008Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP008Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP008Input2565]
  have hc : (compactExp2547 fjminP008Input2565 17).1 = fjminP008Center2565 := by cbv
  have he : ((compactExp2547 fjminP008Input2565 17).2 : ℝ) = fjminP008Error2565 := by
    have hq : (compactExp2547 fjminP008Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP008Error2565]
  have h := compactExp_error2547 fjminP008Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP008Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP008Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP008DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP008Factor2565 * embedPair2542 fjminP008Center2565‖ ≤
        (pairMagnitude2542 fjminP008Factor2565 : ℝ) * fjminP008Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP008Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP008Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP008BaseError2565
    (embedPair_magnitude2542 fjminP008Factor2565)

def fjminP008Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP008Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP008RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP008Factor2565 fjminP008Center2565) = fjminP008Rounded2565 :=
        by
  cbv

theorem fjminP008RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP008Rounded2565‖ ≤ fjminP008Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP008Factor2565 fjminP008Center2565)
  rw [fjminP008RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP008Factor2565 * embedPair2542 fjminP008Center2565)
    (embedPair2542 fjminP008Rounded2565)).trans (add_le_add fjminP008DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP008Factor2565, fjminP008Error2565, rounding2542,
      fjminP008Radius2565]

theorem fjminP008DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP008Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP008RoundedError2565 (embedPair_magnitude2542
      fjminP008Rounded2565))
  apply h'.trans
  norm_num [fjminP008Radius2565, pairMagnitude2542, fjminP008Rounded2565]

noncomputable def fjminP009Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1876507056447276098253971529 : ℚ) /
        3777893186295716170956800000000))

def fjminP009Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP009Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5917178117733711) : ℚ) /
        281474976710656))

noncomputable def fjminP009Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP009BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP009Center2565‖ ≤ fjminP009Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP009Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP009Input2565]
  have hc : (compactExp2547 fjminP009Input2565 17).1 = fjminP009Center2565 := by cbv
  have he : ((compactExp2547 fjminP009Input2565 17).2 : ℝ) = fjminP009Error2565 := by
    have hq : (compactExp2547 fjminP009Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP009Error2565]
  have h := compactExp_error2547 fjminP009Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP009Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP009Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP009DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP009Factor2565 * embedPair2542 fjminP009Center2565‖ ≤
        (pairMagnitude2542 fjminP009Factor2565 : ℝ) * fjminP009Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP009Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP009Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP009BaseError2565
    (embedPair_magnitude2542 fjminP009Factor2565)

def fjminP009Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP009Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP009RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP009Factor2565 fjminP009Center2565) = fjminP009Rounded2565 :=
        by
  cbv

theorem fjminP009RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP009Rounded2565‖ ≤ fjminP009Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP009Factor2565 fjminP009Center2565)
  rw [fjminP009RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP009Factor2565 * embedPair2542 fjminP009Center2565)
    (embedPair2542 fjminP009Rounded2565)).trans (add_le_add fjminP009DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP009Factor2565, fjminP009Error2565, rounding2542,
      fjminP009Radius2565]

theorem fjminP009DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP009Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP009RoundedError2565 (embedPair_magnitude2542
      fjminP009Rounded2565))
  apply h'.trans
  norm_num [fjminP009Radius2565, pairMagnitude2542, fjminP009Rounded2565]

noncomputable def fjminP010Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1116282043593459096767143119 : ℚ) /
        1888946593147858085478400000000))

def fjminP010Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP010Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3519965277442521) : ℚ) /
        140737488355328))

noncomputable def fjminP010Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP010BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP010Center2565‖ ≤ fjminP010Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP010Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP010Input2565]
  have hc : (compactExp2547 fjminP010Input2565 17).1 = fjminP010Center2565 := by cbv
  have he : ((compactExp2547 fjminP010Input2565 17).2 : ℝ) = fjminP010Error2565 := by
    have hq : (compactExp2547 fjminP010Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP010Error2565]
  have h := compactExp_error2547 fjminP010Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP010Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP010Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP010DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP010Factor2565 * embedPair2542 fjminP010Center2565‖ ≤
        (pairMagnitude2542 fjminP010Factor2565 : ℝ) * fjminP010Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP010Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP010Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP010BaseError2565
    (embedPair_magnitude2542 fjminP010Factor2565)

def fjminP010Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP010Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP010RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP010Factor2565 fjminP010Center2565) = fjminP010Rounded2565 :=
        by
  cbv

theorem fjminP010RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP010Rounded2565‖ ≤ fjminP010Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP010Factor2565 fjminP010Center2565)
  rw [fjminP010RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP010Factor2565 * embedPair2542 fjminP010Center2565)
    (embedPair2542 fjminP010Rounded2565)).trans (add_le_add fjminP010DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP010Factor2565, fjminP010Error2565, rounding2542,
      fjminP010Radius2565]

theorem fjminP010DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP010Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP010RoundedError2565 (embedPair_magnitude2542
      fjminP010Rounded2565))
  apply h'.trans
  norm_num [fjminP010Radius2565, pairMagnitude2542, fjminP010Rounded2565]

noncomputable def fjminP011Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1234978985119947335660559039 : ℚ) /
        1888946593147858085478400000000))

def fjminP011Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP011Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3894251610461801) : ℚ) /
        140737488355328))

noncomputable def fjminP011Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP011BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP011Center2565‖ ≤ fjminP011Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP011Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP011Input2565]
  have hc : (compactExp2547 fjminP011Input2565 17).1 = fjminP011Center2565 := by cbv
  have he : ((compactExp2547 fjminP011Input2565 17).2 : ℝ) = fjminP011Error2565 := by
    have hq : (compactExp2547 fjminP011Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP011Error2565]
  have h := compactExp_error2547 fjminP011Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP011Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP011Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP011DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP011Factor2565 * embedPair2542 fjminP011Center2565‖ ≤
        (pairMagnitude2542 fjminP011Factor2565 : ℝ) * fjminP011Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP011Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP011Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP011BaseError2565
    (embedPair_magnitude2542 fjminP011Factor2565)

def fjminP011Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP011Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP011RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP011Factor2565 fjminP011Center2565) = fjminP011Rounded2565 :=
        by
  cbv

theorem fjminP011RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP011Rounded2565‖ ≤ fjminP011Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP011Factor2565 fjminP011Center2565)
  rw [fjminP011RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP011Factor2565 * embedPair2542 fjminP011Center2565)
    (embedPair2542 fjminP011Rounded2565)).trans (add_le_add fjminP011DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP011Factor2565, fjminP011Error2565, rounding2542,
      fjminP011Radius2565]

theorem fjminP011DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP011Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP011RoundedError2565 (embedPair_magnitude2542
      fjminP011Rounded2565))
  apply h'.trans
  norm_num [fjminP011Radius2565, pairMagnitude2542, fjminP011Rounded2565]

noncomputable def fjminP012Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((27158399338384035222570051 : ℚ) /
        37778931862957161709568000000))

def fjminP012Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP012Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2140960324737725) : ℚ) /
        70368744177664))

noncomputable def fjminP012Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP012BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP012Center2565‖ ≤ fjminP012Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP012Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP012Input2565]
  have hc : (compactExp2547 fjminP012Input2565 17).1 = fjminP012Center2565 := by cbv
  have he : ((compactExp2547 fjminP012Input2565 17).2 : ℝ) = fjminP012Error2565 := by
    have hq : (compactExp2547 fjminP012Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP012Error2565]
  have h := compactExp_error2547 fjminP012Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP012Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP012Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP012DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP012Factor2565 * embedPair2542 fjminP012Center2565‖ ≤
        (pairMagnitude2542 fjminP012Factor2565 : ℝ) * fjminP012Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP012Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP012Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP012BaseError2565
    (embedPair_magnitude2542 fjminP012Factor2565)

def fjminP012Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP012Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP012RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP012Factor2565 fjminP012Center2565) = fjminP012Rounded2565 :=
        by
  cbv

theorem fjminP012RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP012Rounded2565‖ ≤ fjminP012Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP012Factor2565 fjminP012Center2565)
  rw [fjminP012RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP012Factor2565 * embedPair2542 fjminP012Center2565)
    (embedPair2542 fjminP012Rounded2565)).trans (add_le_add fjminP012DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP012Factor2565, fjminP012Error2565, rounding2542,
      fjminP012Radius2565]

theorem fjminP012DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP012Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP012RoundedError2565 (embedPair_magnitude2542
      fjminP012Rounded2565))
  apply h'.trans
  norm_num [fjminP012Radius2565, pairMagnitude2542, fjminP012Rounded2565]

noncomputable def fjminP013Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((293990861666597709724015149 : ℚ) /
        377789318629571617095680000000))

def fjminP013Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP013Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4635197846686455) : ℚ) /
        140737488355328))

noncomputable def fjminP013Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP013BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP013Center2565‖ ≤ fjminP013Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP013Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP013Input2565]
  have hc : (compactExp2547 fjminP013Input2565 17).1 = fjminP013Center2565 := by cbv
  have he : ((compactExp2547 fjminP013Input2565 17).2 : ℝ) = fjminP013Error2565 := by
    have hq : (compactExp2547 fjminP013Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP013Error2565]
  have h := compactExp_error2547 fjminP013Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP013Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP013Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP013DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP013Factor2565 * embedPair2542 fjminP013Center2565‖ ≤
        (pairMagnitude2542 fjminP013Factor2565 : ℝ) * fjminP013Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP013Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP013Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP013BaseError2565
    (embedPair_magnitude2542 fjminP013Factor2565)

def fjminP013Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP013Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP013RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP013Factor2565 fjminP013Center2565) = fjminP013Rounded2565 :=
        by
  cbv

theorem fjminP013RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP013Rounded2565‖ ≤ fjminP013Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP013Factor2565 fjminP013Center2565)
  rw [fjminP013RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP013Factor2565 * embedPair2542 fjminP013Center2565)
    (embedPair2542 fjminP013Rounded2565)).trans (add_le_add fjminP013DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP013Factor2565, fjminP013Error2565, rounding2542,
      fjminP013Radius2565]

theorem fjminP013DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP013Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP013RoundedError2565 (embedPair_magnitude2542
      fjminP013Rounded2565))
  apply h'.trans
  norm_num [fjminP013Radius2565, pairMagnitude2542, fjminP013Rounded2565]

noncomputable def fjminP014Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1677542468568059149194008229 : ℚ) /
        1888946593147858085478400000000))

def fjminP014Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP014Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5289784310949011) : ℚ) /
        140737488355328))

noncomputable def fjminP014Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP014BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP014Center2565‖ ≤ fjminP014Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP014Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP014Input2565]
  have hc : (compactExp2547 fjminP014Input2565 17).1 = fjminP014Center2565 := by cbv
  have he : ((compactExp2547 fjminP014Input2565 17).2 : ℝ) = fjminP014Error2565 := by
    have hq : (compactExp2547 fjminP014Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP014Error2565]
  have h := compactExp_error2547 fjminP014Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP014Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP014Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP014DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP014Factor2565 * embedPair2542 fjminP014Center2565‖ ≤
        (pairMagnitude2542 fjminP014Factor2565 : ℝ) * fjminP014Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP014Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP014Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP014BaseError2565
    (embedPair_magnitude2542 fjminP014Factor2565)

def fjminP014Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP014Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP014RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP014Factor2565 fjminP014Center2565) = fjminP014Rounded2565 :=
        by
  cbv

theorem fjminP014RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP014Rounded2565‖ ≤ fjminP014Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP014Factor2565 fjminP014Center2565)
  rw [fjminP014RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP014Factor2565 * embedPair2542 fjminP014Center2565)
    (embedPair2542 fjminP014Rounded2565)).trans (add_le_add fjminP014DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP014Factor2565, fjminP014Error2565, rounding2542,
      fjminP014Radius2565]

theorem fjminP014DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP014Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP014RoundedError2565 (embedPair_magnitude2542
      fjminP014Rounded2565))
  apply h'.trans
  norm_num [fjminP014Radius2565, pairMagnitude2542, fjminP014Rounded2565]

noncomputable def fjminP015Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1826280091905607810113908433 : ℚ) /
        1888946593147858085478400000000))

def fjminP015Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP015Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5758797740487047) : ℚ) /
        140737488355328))

noncomputable def fjminP015Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP015BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP015Center2565‖ ≤ fjminP015Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP015Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP015Input2565]
  have hc : (compactExp2547 fjminP015Input2565 17).1 = fjminP015Center2565 := by cbv
  have he : ((compactExp2547 fjminP015Input2565 17).2 : ℝ) = fjminP015Error2565 := by
    have hq : (compactExp2547 fjminP015Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP015Error2565]
  have h := compactExp_error2547 fjminP015Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP015Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP015Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP015DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP015Factor2565 * embedPair2542 fjminP015Center2565‖ ≤
        (pairMagnitude2542 fjminP015Factor2565 : ℝ) * fjminP015Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP015Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP015Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP015BaseError2565
    (embedPair_magnitude2542 fjminP015Factor2565)

def fjminP015Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP015Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP015RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP015Factor2565 fjminP015Center2565) = fjminP015Rounded2565 :=
        by
  cbv

theorem fjminP015RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP015Rounded2565‖ ≤ fjminP015Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP015Factor2565 fjminP015Center2565)
  rw [fjminP015RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP015Factor2565 * embedPair2542 fjminP015Center2565)
    (embedPair2542 fjminP015Rounded2565)).trans (add_le_add fjminP015DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP015Factor2565, fjminP015Error2565, rounding2542,
      fjminP015Radius2565]

theorem fjminP015DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP015Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP015RoundedError2565 (embedPair_magnitude2542
      fjminP015Rounded2565))
  apply h'.trans
  norm_num [fjminP015Radius2565, pairMagnitude2542, fjminP015Rounded2565]

noncomputable def fjminP016Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((966884756949258260679651951 : ℚ) /
        944473296573929042739200000000))

def fjminP016Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP016Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3048871735671609) : ℚ) /
        70368744177664))

noncomputable def fjminP016Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP016BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP016Center2565‖ ≤ fjminP016Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP016Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP016Input2565]
  have hc : (compactExp2547 fjminP016Input2565 17).1 = fjminP016Center2565 := by cbv
  have he : ((compactExp2547 fjminP016Input2565 17).2 : ℝ) = fjminP016Error2565 := by
    have hq : (compactExp2547 fjminP016Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP016Error2565]
  have h := compactExp_error2547 fjminP016Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP016Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP016Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP016DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP016Factor2565 * embedPair2542 fjminP016Center2565‖ ≤
        (pairMagnitude2542 fjminP016Factor2565 : ℝ) * fjminP016Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP016Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP016Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP016BaseError2565
    (embedPair_magnitude2542 fjminP016Factor2565)

def fjminP016Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP016Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP016RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP016Factor2565 fjminP016Center2565) = fjminP016Rounded2565 :=
        by
  cbv

theorem fjminP016RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP016Rounded2565‖ ≤ fjminP016Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP016Factor2565 fjminP016Center2565)
  rw [fjminP016RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP016Factor2565 * embedPair2542 fjminP016Center2565)
    (embedPair2542 fjminP016Rounded2565)).trans (add_le_add fjminP016DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP016Factor2565, fjminP016Error2565, rounding2542,
      fjminP016Radius2565]

theorem fjminP016DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP016Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP016RoundedError2565 (embedPair_magnitude2542
      fjminP016Rounded2565))
  apply h'.trans
  norm_num [fjminP016Radius2565, pairMagnitude2542, fjminP016Rounded2565]

noncomputable def fjminP017Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2142560996036405154016564653 : ℚ) /
        1888946593147858085478400000000))

def fjminP017Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP017Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-6756124363134027) : ℚ) /
        140737488355328))

noncomputable def fjminP017Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP017BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP017Center2565‖ ≤ fjminP017Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP017Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP017Input2565]
  have hc : (compactExp2547 fjminP017Input2565 17).1 = fjminP017Center2565 := by cbv
  have he : ((compactExp2547 fjminP017Input2565 17).2 : ℝ) = fjminP017Error2565 := by
    have hq : (compactExp2547 fjminP017Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP017Error2565]
  have h := compactExp_error2547 fjminP017Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP017Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP017Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP017DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP017Factor2565 * embedPair2542 fjminP017Center2565‖ ≤
        (pairMagnitude2542 fjminP017Factor2565 : ℝ) * fjminP017Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP017Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP017Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP017BaseError2565
    (embedPair_magnitude2542 fjminP017Factor2565)

def fjminP017Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP017Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP017RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP017Factor2565 fjminP017Center2565) = fjminP017Rounded2565 :=
        by
  cbv

theorem fjminP017RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP017Rounded2565‖ ≤ fjminP017Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP017Factor2565 fjminP017Center2565)
  rw [fjminP017RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP017Factor2565 * embedPair2542 fjminP017Center2565)
    (embedPair2542 fjminP017Rounded2565)).trans (add_le_add fjminP017DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP017Factor2565, fjminP017Error2565, rounding2542,
      fjminP017Radius2565]

theorem fjminP017DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP017Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP017RoundedError2565 (embedPair_magnitude2542
      fjminP017Rounded2565))
  apply h'.trans
  norm_num [fjminP017Radius2565, pairMagnitude2542, fjminP017Rounded2565]

noncomputable def fjminP018Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((555375153147096446436377307 : ℚ) /
        472236648286964521369600000000))

def fjminP018Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP018Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-1751261042181613) : ℚ) /
        35184372088832))

noncomputable def fjminP018Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP018BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP018Center2565‖ ≤ fjminP018Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP018Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP018Input2565]
  have hc : (compactExp2547 fjminP018Input2565 17).1 = fjminP018Center2565 := by cbv
  have he : ((compactExp2547 fjminP018Input2565 17).2 : ℝ) = fjminP018Error2565 := by
    have hq : (compactExp2547 fjminP018Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP018Error2565]
  have h := compactExp_error2547 fjminP018Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP018Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP018Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP018DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP018Factor2565 * embedPair2542 fjminP018Center2565‖ ≤
        (pairMagnitude2542 fjminP018Factor2565 : ℝ) * fjminP018Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP018Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP018Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP018BaseError2565
    (embedPair_magnitude2542 fjminP018Factor2565)

def fjminP018Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP018Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP018RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP018Factor2565 fjminP018Center2565) = fjminP018Rounded2565 :=
        by
  cbv

theorem fjminP018RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP018Rounded2565‖ ≤ fjminP018Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP018Factor2565 fjminP018Center2565)
  rw [fjminP018RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP018Factor2565 * embedPair2542 fjminP018Center2565)
    (embedPair2542 fjminP018Rounded2565)).trans (add_le_add fjminP018DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP018Factor2565, fjminP018Error2565, rounding2542,
      fjminP018Radius2565]

theorem fjminP018DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP018Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP018RoundedError2565 (embedPair_magnitude2542
      fjminP018Rounded2565))
  apply h'.trans
  norm_num [fjminP018Radius2565, pairMagnitude2542, fjminP018Rounded2565]

noncomputable def fjminP019Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((118208299174604243670929049 : ℚ) /
        94447329657392904273920000000))

def fjminP019Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP019Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-1863727500536955) : ℚ) /
        35184372088832))

noncomputable def fjminP019Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP019BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP019Center2565‖ ≤ fjminP019Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP019Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP019Input2565]
  have hc : (compactExp2547 fjminP019Input2565 17).1 = fjminP019Center2565 := by cbv
  have he : ((compactExp2547 fjminP019Input2565 17).2 : ℝ) = fjminP019Error2565 := by
    have hq : (compactExp2547 fjminP019Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP019Error2565]
  have h := compactExp_error2547 fjminP019Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP019Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP019Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP019DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP019Factor2565 * embedPair2542 fjminP019Center2565‖ ≤
        (pairMagnitude2542 fjminP019Factor2565 : ℝ) * fjminP019Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP019Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP019Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP019BaseError2565
    (embedPair_magnitude2542 fjminP019Factor2565)

def fjminP019Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP019Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP019RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP019Factor2565 fjminP019Center2565) = fjminP019Rounded2565 :=
        by
  cbv

theorem fjminP019RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP019Rounded2565‖ ≤ fjminP019Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP019Factor2565 fjminP019Center2565)
  rw [fjminP019RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP019Factor2565 * embedPair2542 fjminP019Center2565)
    (embedPair2542 fjminP019Rounded2565)).trans (add_le_add fjminP019DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP019Factor2565, fjminP019Error2565, rounding2542,
      fjminP019Radius2565]

theorem fjminP019DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP019Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP019RoundedError2565 (embedPair_magnitude2542
      fjminP019Rounded2565))
  apply h'.trans
  norm_num [fjminP019Radius2565, pairMagnitude2542, fjminP019Rounded2565]

noncomputable def fjminP020Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2519303167856168777929316541 : ℚ) /
        1888946593147858085478400000000))

def fjminP020Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP020Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-7944103127967419) : ℚ) /
        140737488355328))

noncomputable def fjminP020Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP020BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP020Center2565‖ ≤ fjminP020Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP020Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP020Input2565]
  have hc : (compactExp2547 fjminP020Input2565 17).1 = fjminP020Center2565 := by cbv
  have he : ((compactExp2547 fjminP020Input2565 17).2 : ℝ) = fjminP020Error2565 := by
    have hq : (compactExp2547 fjminP020Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP020Error2565]
  have h := compactExp_error2547 fjminP020Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP020Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP020Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP020DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP020Factor2565 * embedPair2542 fjminP020Center2565‖ ≤
        (pairMagnitude2542 fjminP020Factor2565 : ℝ) * fjminP020Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP020Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP020Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP020BaseError2565
    (embedPair_magnitude2542 fjminP020Factor2565)

def fjminP020Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP020Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP020RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP020Factor2565 fjminP020Center2565) = fjminP020Rounded2565 :=
        by
  cbv

theorem fjminP020RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP020Rounded2565‖ ≤ fjminP020Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP020Factor2565 fjminP020Center2565)
  rw [fjminP020RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP020Factor2565 * embedPair2542 fjminP020Center2565)
    (embedPair2542 fjminP020Rounded2565)).trans (add_le_add fjminP020DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP020Factor2565, fjminP020Error2565, rounding2542,
      fjminP020Radius2565]

theorem fjminP020DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP020Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP020RoundedError2565 (embedPair_magnitude2542
      fjminP020Rounded2565))
  apply h'.trans
  norm_num [fjminP020Radius2565, pairMagnitude2542, fjminP020Rounded2565]

noncomputable def fjminP021Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2648771212589104536068841693 : ℚ) /
        1888946593147858085478400000000))

def fjminP021Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP021Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-8352353914239387) : ℚ) /
        140737488355328))

noncomputable def fjminP021Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP021BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP021Center2565‖ ≤ fjminP021Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP021Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP021Input2565]
  have hc : (compactExp2547 fjminP021Input2565 17).1 = fjminP021Center2565 := by cbv
  have he : ((compactExp2547 fjminP021Input2565 17).2 : ℝ) = fjminP021Error2565 := by
    have hq : (compactExp2547 fjminP021Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP021Error2565]
  have h := compactExp_error2547 fjminP021Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP021Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP021Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP021DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP021Factor2565 * embedPair2542 fjminP021Center2565‖ ≤
        (pairMagnitude2542 fjminP021Factor2565 : ℝ) * fjminP021Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP021Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP021Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP021BaseError2565
    (embedPair_magnitude2542 fjminP021Factor2565)

def fjminP021Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP021Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP021RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP021Factor2565 fjminP021Center2565) = fjminP021Rounded2565 :=
        by
  cbv

theorem fjminP021RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP021Rounded2565‖ ≤ fjminP021Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP021Factor2565 fjminP021Center2565)
  rw [fjminP021RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP021Factor2565 * embedPair2542 fjminP021Center2565)
    (embedPair2542 fjminP021Rounded2565)).trans (add_le_add fjminP021DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP021Factor2565, fjminP021Error2565, rounding2542,
      fjminP021Radius2565]

theorem fjminP021DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP021Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP021RoundedError2565 (embedPair_magnitude2542
      fjminP021Rounded2565))
  apply h'.trans
  norm_num [fjminP021Radius2565, pairMagnitude2542, fjminP021Rounded2565]

noncomputable def fjminP022Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((543007546456794340281131487 : ℚ) /
        377789318629571617095680000000))

def fjminP022Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP022Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-8561311721741165) : ℚ) /
        140737488355328))

noncomputable def fjminP022Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP022BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP022Center2565‖ ≤ fjminP022Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP022Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP022Input2565]
  have hc : (compactExp2547 fjminP022Input2565 17).1 = fjminP022Center2565 := by cbv
  have he : ((compactExp2547 fjminP022Input2565 17).2 : ℝ) = fjminP022Error2565 := by
    have hq : (compactExp2547 fjminP022Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP022Error2565]
  have h := compactExp_error2547 fjminP022Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP022Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP022Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP022DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP022Factor2565 * embedPair2542 fjminP022Center2565‖ ≤
        (pairMagnitude2542 fjminP022Factor2565 : ℝ) * fjminP022Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP022Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP022Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP022BaseError2565
    (embedPair_magnitude2542 fjminP022Factor2565)

def fjminP022Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP022Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP022RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP022Factor2565 fjminP022Center2565) = fjminP022Rounded2565 :=
        by
  cbv

theorem fjminP022RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP022Rounded2565‖ ≤ fjminP022Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP022Factor2565 fjminP022Center2565)
  rw [fjminP022RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP022Factor2565 * embedPair2542 fjminP022Center2565)
    (embedPair2542 fjminP022Rounded2565)).trans (add_le_add fjminP022DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP022Factor2565, fjminP022Error2565, rounding2542,
      fjminP022Radius2565]

theorem fjminP022DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP022Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP022RoundedError2565 (embedPair_magnitude2542
      fjminP022Rounded2565))
  apply h'.trans
  norm_num [fjminP022Radius2565, pairMagnitude2542, fjminP022Rounded2565]

noncomputable def fjminP023Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1453048211174897778209007387 : ℚ) /
        944473296573929042739200000000))

def fjminP023Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP023Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4581887954876333) : ℚ) /
        70368744177664))

noncomputable def fjminP023Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP023BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP023Center2565‖ ≤ fjminP023Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP023Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP023Input2565]
  have hc : (compactExp2547 fjminP023Input2565 17).1 = fjminP023Center2565 := by cbv
  have he : ((compactExp2547 fjminP023Input2565 17).2 : ℝ) = fjminP023Error2565 := by
    have hq : (compactExp2547 fjminP023Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP023Error2565]
  have h := compactExp_error2547 fjminP023Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP023Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP023Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP023DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP023Factor2565 * embedPair2542 fjminP023Center2565‖ ≤
        (pairMagnitude2542 fjminP023Factor2565 : ℝ) * fjminP023Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP023Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP023Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP023BaseError2565
    (embedPair_magnitude2542 fjminP023Factor2565)

def fjminP023Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP023Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP023RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP023Factor2565 fjminP023Center2565) = fjminP023Rounded2565 :=
        by
  cbv

theorem fjminP023RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP023Rounded2565‖ ≤ fjminP023Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP023Factor2565 fjminP023Center2565)
  rw [fjminP023RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP023Factor2565 * embedPair2542 fjminP023Center2565)
    (embedPair2542 fjminP023Rounded2565)).trans (add_le_add fjminP023DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP023Factor2565, fjminP023Error2565, rounding2542,
      fjminP023Radius2565]

theorem fjminP023DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP023Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP023RoundedError2565 (embedPair_magnitude2542
      fjminP023Rounded2565))
  apply h'.trans
  norm_num [fjminP023Radius2565, pairMagnitude2542, fjminP023Rounded2565]

noncomputable def fjminP024Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1496949629611413064555803333 : ℚ) /
        944473296573929042739200000000))

def fjminP024Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP024Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4720322026636147) : ℚ) /
        70368744177664))

noncomputable def fjminP024Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP024BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP024Center2565‖ ≤ fjminP024Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP024Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP024Input2565]
  have hc : (compactExp2547 fjminP024Input2565 17).1 = fjminP024Center2565 := by cbv
  have he : ((compactExp2547 fjminP024Input2565 17).2 : ℝ) = fjminP024Error2565 := by
    have hq : (compactExp2547 fjminP024Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP024Error2565]
  have h := compactExp_error2547 fjminP024Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP024Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP024Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP024DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP024Factor2565 * embedPair2542 fjminP024Center2565‖ ≤
        (pairMagnitude2542 fjminP024Factor2565 : ℝ) * fjminP024Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP024Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP024Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP024BaseError2565
    (embedPair_magnitude2542 fjminP024Factor2565)

def fjminP024Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP024Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP024RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP024Factor2565 fjminP024Center2565) = fjminP024Rounded2565 :=
        by
  cbv

theorem fjminP024RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP024Rounded2565‖ ≤ fjminP024Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP024Factor2565 fjminP024Center2565)
  rw [fjminP024RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP024Factor2565 * embedPair2542 fjminP024Center2565)
    (embedPair2542 fjminP024Rounded2565)).trans (add_le_add fjminP024DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP024Factor2565, fjminP024Error2565, rounding2542,
      fjminP024Radius2565]

theorem fjminP024DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP024Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP024RoundedError2565 (embedPair_magnitude2542
      fjminP024Rounded2565))
  apply h'.trans
  norm_num [fjminP024Radius2565, pairMagnitude2542, fjminP024Rounded2565]

noncomputable def fjminP025Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((48499811018293309025440887 : ℚ) /
        29514790517935282585600000000))

def fjminP025Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP025Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-152934154702833) : ℚ) /
        2199023255552))

noncomputable def fjminP025Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP025BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP025Center2565‖ ≤ fjminP025Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP025Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP025Input2565]
  have hc : (compactExp2547 fjminP025Input2565 17).1 = fjminP025Center2565 := by cbv
  have he : ((compactExp2547 fjminP025Input2565 17).2 : ℝ) = fjminP025Error2565 := by
    have hq : (compactExp2547 fjminP025Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP025Error2565]
  have h := compactExp_error2547 fjminP025Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP025Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP025Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP025DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP025Factor2565 * embedPair2542 fjminP025Center2565‖ ≤
        (pairMagnitude2542 fjminP025Factor2565 : ℝ) * fjminP025Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP025Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP025Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP025BaseError2565
    (embedPair_magnitude2542 fjminP025Factor2565)

def fjminP025Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP025Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP025RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP025Factor2565 fjminP025Center2565) = fjminP025Rounded2565 :=
        by
  cbv

theorem fjminP025RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP025Rounded2565‖ ≤ fjminP025Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP025Factor2565 fjminP025Center2565)
  rw [fjminP025RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP025Factor2565 * embedPair2542 fjminP025Center2565)
    (embedPair2542 fjminP025Rounded2565)).trans (add_le_add fjminP025DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP025Factor2565, fjminP025Error2565, rounding2542,
      fjminP025Radius2565]

theorem fjminP025DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP025Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP025RoundedError2565 (embedPair_magnitude2542
      fjminP025Rounded2565))
  apply h'.trans
  norm_num [fjminP025Radius2565, pairMagnitude2542, fjminP025Rounded2565]

noncomputable def fjminP026Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((100515438378930241589387643 : ℚ) /
        59029581035870565171200000000))

def fjminP026Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP026Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-316954711375437) : ℚ) /
        4398046511104))

noncomputable def fjminP026Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP026BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP026Center2565‖ ≤ fjminP026Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP026Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP026Input2565]
  have hc : (compactExp2547 fjminP026Input2565 17).1 = fjminP026Center2565 := by cbv
  have he : ((compactExp2547 fjminP026Input2565 17).2 : ℝ) = fjminP026Error2565 := by
    have hq : (compactExp2547 fjminP026Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP026Error2565]
  have h := compactExp_error2547 fjminP026Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP026Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP026Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP026DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP026Factor2565 * embedPair2542 fjminP026Center2565‖ ≤
        (pairMagnitude2542 fjminP026Factor2565 : ℝ) * fjminP026Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP026Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP026Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP026BaseError2565
    (embedPair_magnitude2542 fjminP026Factor2565)

def fjminP026Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP026Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP026RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP026Factor2565 fjminP026Center2565) = fjminP026Rounded2565 :=
        by
  cbv

theorem fjminP026RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP026Rounded2565‖ ≤ fjminP026Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP026Factor2565 fjminP026Center2565)
  rw [fjminP026RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP026Factor2565 * embedPair2542 fjminP026Center2565)
    (embedPair2542 fjminP026Rounded2565)).trans (add_le_add fjminP026DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP026Factor2565, fjminP026Error2565, rounding2542,
      fjminP026Radius2565]

theorem fjminP026DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP026Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP026RoundedError2565 (embedPair_magnitude2542
      fjminP026Rounded2565))
  apply h'.trans
  norm_num [fjminP026Radius2565, pairMagnitude2542, fjminP026Rounded2565]

noncomputable def fjminP027Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((211177751933296260595876053 : ℚ) /
        118059162071741130342400000000))

def fjminP027Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP027Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-665905501606627) : ℚ) /
        8796093022208))

noncomputable def fjminP027Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP027BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP027Center2565‖ ≤ fjminP027Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP027Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP027Input2565]
  have hc : (compactExp2547 fjminP027Input2565 17).1 = fjminP027Center2565 := by cbv
  have he : ((compactExp2547 fjminP027Input2565 17).2 : ℝ) = fjminP027Error2565 := by
    have hq : (compactExp2547 fjminP027Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP027Error2565]
  have h := compactExp_error2547 fjminP027Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP027Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP027Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP027DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP027Factor2565 * embedPair2542 fjminP027Center2565‖ ≤
        (pairMagnitude2542 fjminP027Factor2565 : ℝ) * fjminP027Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP027Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP027Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP027BaseError2565
    (embedPair_magnitude2542 fjminP027Factor2565)

def fjminP027Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP027Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP027RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP027Factor2565 fjminP027Center2565) = fjminP027Rounded2565 :=
        by
  cbv

theorem fjminP027RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP027Rounded2565‖ ≤ fjminP027Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP027Factor2565 fjminP027Center2565)
  rw [fjminP027RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP027Factor2565 * embedPair2542 fjminP027Center2565)
    (embedPair2542 fjminP027Rounded2565)).trans (add_le_add fjminP027DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP027Factor2565, fjminP027Error2565, rounding2542,
      fjminP027Radius2565]

theorem fjminP027DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP027Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP027RoundedError2565 (embedPair_magnitude2542
      fjminP027Rounded2565))
  apply h'.trans
  norm_num [fjminP027Radius2565, pairMagnitude2542, fjminP027Rounded2565]

noncomputable def fjminP028Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((860780157665754287223049953 : ℚ) /
        472236648286964521369600000000))

def fjminP028Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP028Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2714292757716727) : ℚ) /
        35184372088832))

noncomputable def fjminP028Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP028BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP028Center2565‖ ≤ fjminP028Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP028Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP028Input2565]
  have hc : (compactExp2547 fjminP028Input2565 17).1 = fjminP028Center2565 := by cbv
  have he : ((compactExp2547 fjminP028Input2565 17).2 : ℝ) = fjminP028Error2565 := by
    have hq : (compactExp2547 fjminP028Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP028Error2565]
  have h := compactExp_error2547 fjminP028Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP028Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP028Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP028DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP028Factor2565 * embedPair2542 fjminP028Center2565‖ ≤
        (pairMagnitude2542 fjminP028Factor2565 : ℝ) * fjminP028Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP028Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP028Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP028BaseError2565
    (embedPair_magnitude2542 fjminP028Factor2565)

def fjminP028Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP028Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP028RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP028Factor2565 fjminP028Center2565) = fjminP028Rounded2565 :=
        by
  cbv

theorem fjminP028RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP028Rounded2565‖ ≤ fjminP028Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP028Factor2565 fjminP028Center2565)
  rw [fjminP028RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP028Factor2565 * embedPair2542 fjminP028Center2565)
    (embedPair2542 fjminP028Rounded2565)).trans (add_le_add fjminP028DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP028Factor2565, fjminP028Error2565, rounding2542,
      fjminP028Radius2565]

theorem fjminP028DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP028Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP028RoundedError2565 (embedPair_magnitude2542
      fjminP028Rounded2565))
  apply h'.trans
  norm_num [fjminP028Radius2565, pairMagnitude2542, fjminP028Rounded2565]

noncomputable def fjminP029Input2565 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((885244406725664293840781901 : ℚ) /
        472236648286964521369600000000))

def fjminP029Center2565 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjminP029Factor2565 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2791435723263659) : ℚ) /
        35184372088832))

noncomputable def fjminP029Error2565 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjminP029BaseError2565 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP029Center2565‖ ≤ fjminP029Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjminP029Input2565‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjminP029Input2565]
  have hc : (compactExp2547 fjminP029Input2565 17).1 = fjminP029Center2565 := by cbv
  have he : ((compactExp2547 fjminP029Input2565 17).2 : ℝ) = fjminP029Error2565 := by
    have hq : (compactExp2547 fjminP029Input2565 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjminP029Error2565]
  have h := compactExp_error2547 fjminP029Input2565 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjminP029Input2565) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjminP029Input2565, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjminP029DerivativeError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjminP029Factor2565 * embedPair2542 fjminP029Center2565‖ ≤
        (pairMagnitude2542 fjminP029Factor2565 : ℝ) * fjminP029Error2565 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjminP029Factor2565 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjminP029Factor2565, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjminP029BaseError2565
    (embedPair_magnitude2542 fjminP029Factor2565)

def fjminP029Rounded2565 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjminP029Radius2565 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjminP029RoundCompute2565 :
    pairRound2542 (pairMul2542 fjminP029Factor2565 fjminP029Center2565) = fjminP029Rounded2565 :=
        by
  cbv

theorem fjminP029RoundedError2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjminP029Rounded2565‖ ≤ fjminP029Radius2565 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjminP029Factor2565 fjminP029Center2565)
  rw [fjminP029RoundCompute2565, embedPair_mul2542] at hr
  have h := (firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP029Factor2565 * embedPair2542 fjminP029Center2565)
    (embedPair2542 fjminP029Rounded2565)).trans (add_le_add fjminP029DerivativeError2565 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjminP029Factor2565, fjminP029Error2565, rounding2542,
      fjminP029Radius2565]

theorem fjminP029DerivativeNorm2565 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetMidpointMinus_triangle2565
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjminP029Rounded2565) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjminP029RoundedError2565 (embedPair_magnitude2542
      fjminP029Rounded2565))
  apply h'.trans
  norm_num [fjminP029Radius2565, pairMagnitude2542, fjminP029Rounded2565]

noncomputable def fjminValue2565 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 fjminP000Rounded2565
  | 1 => embedPair2542 fjminP001Rounded2565
  | 2 => embedPair2542 fjminP002Rounded2565
  | 3 => embedPair2542 fjminP003Rounded2565
  | 4 => embedPair2542 fjminP004Rounded2565
  | 5 => embedPair2542 fjminP005Rounded2565
  | 6 => embedPair2542 fjminP006Rounded2565
  | 7 => embedPair2542 fjminP007Rounded2565
  | 8 => embedPair2542 fjminP008Rounded2565
  | 9 => embedPair2542 fjminP009Rounded2565
  | 10 => embedPair2542 fjminP010Rounded2565
  | 11 => embedPair2542 fjminP011Rounded2565
  | 12 => embedPair2542 fjminP012Rounded2565
  | 13 => embedPair2542 fjminP013Rounded2565
  | 14 => embedPair2542 fjminP014Rounded2565
  | 15 => embedPair2542 fjminP015Rounded2565
  | 16 => embedPair2542 fjminP016Rounded2565
  | 17 => embedPair2542 fjminP017Rounded2565
  | 18 => embedPair2542 fjminP018Rounded2565
  | 19 => embedPair2542 fjminP019Rounded2565
  | 20 => embedPair2542 fjminP020Rounded2565
  | 21 => embedPair2542 fjminP021Rounded2565
  | 22 => embedPair2542 fjminP022Rounded2565
  | 23 => embedPair2542 fjminP023Rounded2565
  | 24 => embedPair2542 fjminP024Rounded2565
  | 25 => embedPair2542 fjminP025Rounded2565
  | 26 => embedPair2542 fjminP026Rounded2565
  | 27 => embedPair2542 fjminP027Rounded2565
  | 28 => embedPair2542 fjminP028Rounded2565
  | 29 => embedPair2542 fjminP029Rounded2565
  | _ => 0

noncomputable def fjminError2565 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => fjminP000Radius2565
  | 1 => fjminP001Radius2565
  | 2 => fjminP002Radius2565
  | 3 => fjminP003Radius2565
  | 4 => fjminP004Radius2565
  | 5 => fjminP005Radius2565
  | 6 => fjminP006Radius2565
  | 7 => fjminP007Radius2565
  | 8 => fjminP008Radius2565
  | 9 => fjminP009Radius2565
  | 10 => fjminP010Radius2565
  | 11 => fjminP011Radius2565
  | 12 => fjminP012Radius2565
  | 13 => fjminP013Radius2565
  | 14 => fjminP014Radius2565
  | 15 => fjminP015Radius2565
  | 16 => fjminP016Radius2565
  | 17 => fjminP017Radius2565
  | 18 => fjminP018Radius2565
  | 19 => fjminP019Radius2565
  | 20 => fjminP020Radius2565
  | 21 => fjminP021Radius2565
  | 22 => fjminP022Radius2565
  | 23 => fjminP023Radius2565
  | 24 => fjminP024Radius2565
  | 25 => fjminP025Radius2565
  | 26 => fjminP026Radius2565
  | 27 => fjminP027Radius2565
  | 28 => fjminP028Radius2565
  | 29 => fjminP029Radius2565
  | _ => 0

theorem fjminExpError2565 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548 - fjminValue2565
        i‖ ≤ fjminError2565 i := by
  fin_cases i
  · simpa only [fjminValue2565, fjminError2565] using fjminP000RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP001RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP002RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP003RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP004RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP005RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP006RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP007RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP008RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP009RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP010RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP011RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP012RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP013RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP014RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP015RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP016RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP017RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP018RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP019RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP020RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP021RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP022RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP023RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP024RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP025RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP026RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP027RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP028RoundedError2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP029RoundedError2565

theorem fjminUnitNorm2565 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤ 1 := by
  fin_cases i
  · simpa only [fjminValue2565, fjminError2565] using fjminP000DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP001DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP002DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP003DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP004DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP005DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP006DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP007DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP008DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP009DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP010DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP011DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP012DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP013DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP014DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP015DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP016DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP017DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP018DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP019DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP020DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP021DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP022DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP023DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP024DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP025DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP026DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP027DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP028DerivativeNorm2565
  · simpa only [fjminValue2565, fjminError2565] using fjminP029DerivativeNorm2565

noncomputable def fjminSum2565 : ℂ := ⟨(((-(((2419 * 10^40
        + 7672734528378904643553182292392075734997) * 10^40
        + 8408618543870665580438268702748510888989) * 10^40
        + 5166516871026312354076667460126464905109)) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((((1357 * 10^40
        + 6444388160937687715332125730917765305744) * 10^40
        + 9832761636063459458726070811843459884967) * 10^40
        + 8195338626302065696351882260942691548503) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216))⟩

noncomputable def fjminUpper2565 : ℝ := ((1283 : ℝ) /
        20000000)

theorem fjminSum_eq2565 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * fjminValue2565 i) =
      fjminSum2565 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, fjminValue2565,
      fjminSum2565, embedPair2542, fjminP000Rounded2565,
      fjminP001Rounded2565,
      fjminP002Rounded2565,
      fjminP003Rounded2565,
      fjminP004Rounded2565,
      fjminP005Rounded2565,
      fjminP006Rounded2565,
      fjminP007Rounded2565,
      fjminP008Rounded2565,
      fjminP009Rounded2565,
      fjminP010Rounded2565,
      fjminP011Rounded2565,
      fjminP012Rounded2565,
      fjminP013Rounded2565,
      fjminP014Rounded2565,
      fjminP015Rounded2565,
      fjminP016Rounded2565,
      fjminP017Rounded2565,
      fjminP018Rounded2565,
      fjminP019Rounded2565,
      fjminP020Rounded2565,
      fjminP021Rounded2565,
      fjminP022Rounded2565,
      fjminP023Rounded2565,
      fjminP024Rounded2565,
      fjminP025Rounded2565,
      fjminP026Rounded2565,
      fjminP027Rounded2565,
      fjminP028Rounded2565,
      fjminP029Rounded2565, Complex.mul_re, Complex.mul_im]

theorem fjminSum_norm2565 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * fjminValue2565 i‖ ≤ ((1281 : ℝ) /
        20000000) := by
  rw [fjminSum_eq2565]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [fjminSum2565]

theorem fjminCharge2565 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * fjminError2565 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, fjminError2565,
      fjminP000Radius2565,
      fjminP001Radius2565,
      fjminP002Radius2565,
      fjminP003Radius2565,
      fjminP004Radius2565,
      fjminP005Radius2565,
      fjminP006Radius2565,
      fjminP007Radius2565,
      fjminP008Radius2565,
      fjminP009Radius2565,
      fjminP010Radius2565,
      fjminP011Radius2565,
      fjminP012Radius2565,
      fjminP013Radius2565,
      fjminP014Radius2565,
      fjminP015Radius2565,
      fjminP016Radius2565,
      fjminP017Radius2565,
      fjminP018Radius2565,
      fjminP019Radius2565,
      fjminP020Radius2565,
      fjminP021Radius2565,
      fjminP022Radius2565,
      fjminP023Radius2565,
      fjminP024Radius2565,
      fjminP025Radius2565,
      fjminP026Radius2565,
      fjminP027Radius2565,
      fjminP028Radius2565,
      fjminP029Radius2565]

theorem firstJetMidpointMinusUpper_le2565 :
    signedJetUpper2539 1 (-1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 edgeMidpointPosition2548 ≤ fjminUpper2565 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * fjminValue2565 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * fjminError2565 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (fjminExpError2565 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (fjminUnitNorm2565 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 fjminUpper2565
  linarith [fjminSum_norm2565, fjminCharge2565]

theorem weightedPhysicalFirstJetMidpointMinus_le2565 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖iteratedDeriv 1 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        edgeMidpointPosition2548‖ ≤
      fjminUpper2565 := by
  have h := weightedPhysical2539_jet_le_center_error 1 (-1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i))
        edgeMidpointPosition2548
  exact h.trans firstJetMidpointMinusUpper_le2565

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.fjminExpError2565
#print axioms ConnesWeilRH.Dev.fjminSum_eq2565
#print axioms ConnesWeilRH.Dev.fjminSum_norm2565
#print axioms ConnesWeilRH.Dev.fjminCharge2565
#print axioms ConnesWeilRH.Dev.firstJetMidpointMinusUpper_le2565
#print axioms ConnesWeilRH.Dev.weightedPhysicalFirstJetMidpointMinus_le2565
