import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541
import ConnesWeilRH.Dev.C1RouteABoundaryMidpoint2548
import ConnesWeilRH.Dev.C1RouteACorrectionCoefficientBoxes2570
import ConnesWeilRH.Dev.C1RouteACorrectionCenterNode2570

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem firstJetCorrMinus_triangle2570 (a b c : ℂ) : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  calc
    ‖a - c‖ = ‖(a - b) + (b - c)‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _

theorem fjcmZero2570 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def fjcmP000Center2570 : RatPair2542 := (0, 0)

def fjcmP000Factor2570 : RatPair2542 := (0, 0)

noncomputable def fjcmP000Error2570 : ℝ := 0

theorem fjcmP000Exterior2570 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n (-1/2)
    (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem fjcmP000BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP000Center2570‖ ≤ fjcmP000Error2570 := by
  rw [fjcmP000Exterior2570]
  norm_num [fjcmP000Center2570, fjcmP000Error2570, fjcmZero2570]

theorem fjcmP000DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP000Factor2570 * embedPair2542 fjcmP000Center2570‖ ≤
        (pairMagnitude2542 fjcmP000Factor2570 : ℝ) * fjcmP000Error2570 := by
  rw [fjcmP000Exterior2570]
  norm_num [fjcmP000Factor2570, fjcmP000Center2570, fjcmP000Error2570, pairMagnitude2542,
      fjcmZero2570]

def fjcmP000Rounded2570 : RatPair2542 := (0, 0)

noncomputable def fjcmP000Radius2570 : ℝ := 0

theorem fjcmP000RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP000Factor2570 fjcmP000Center2570) = fjcmP000Rounded2570 := by
  cbv

theorem fjcmP000RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP000Rounded2570‖ ≤ fjcmP000Radius2570 := by
  rw [fjcmP000Exterior2570]
  norm_num [fjcmP000Rounded2570, fjcmP000Radius2570, fjcmZero2570]

theorem fjcmP000DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨0, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [fjcmP000Exterior2570]
  norm_num

noncomputable def fjcmP001Input2570 : RatPair2542 := ((((-((74 * 10^40
        + 3163554082308786923030623187936917919547) * 10^40
        + 6189645194398852582143451811084217740401)) : ℚ) /
        ((208 * 10^40
        + 8043940912794372598641292711490528776820) * 10^40
        + 5100987153752063079186153183641600000000)),
    ((1751911280236833479653958331 : ℚ) /
        7378697629483820646400000000))

def fjcmP001Center2570 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def fjcmP001Factor2570 : RatPair2542 := ((((((48206378145472865255 * 10^40
        + 4558879378186968721762698369388365651076) * 10^40
        + 8183683534072696621069541849066993590601) * 10^40
        + 1799131963158929497400353332108237304719) : ℚ) /
        (((79306619212413954 * 10^40
        + 6135590275954697994891057369985995860880) * 10^40
        + 3799340399814374588299513654302616835559) * 10^40
        + 5354338069519581005199293335783525390562)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjcmP001Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP001BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP001Center2570‖ ≤ fjcmP001Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP001Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP001Input2570]
  have hc : (compactExp2547 fjcmP001Input2570 9).1 = fjcmP001Center2570 := by cbv
  have he : ((compactExp2547 fjcmP001Input2570 9).2 : ℝ) = fjcmP001Error2570 := by
    have hq : (compactExp2547 fjcmP001Input2570 9).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP001Error2570]
  have h := compactExp_error2547 fjcmP001Input2570 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^9 * embedPair2542 fjcmP001Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP001Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP001DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP001Factor2570 * embedPair2542 fjcmP001Center2570‖ ≤
        (pairMagnitude2542 fjcmP001Factor2570 : ℝ) * fjcmP001Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP001Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP001Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP001BaseError2570
    (embedPair_magnitude2542 fjcmP001Factor2570)

def fjcmP001Rounded2570 : RatPair2542 :=
  ((((-1) : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP001Radius2570 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP001RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP001Factor2570 fjcmP001Center2570) = fjcmP001Rounded2570 := by
  cbv

theorem fjcmP001RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP001Rounded2570‖ ≤ fjcmP001Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP001Factor2570 fjcmP001Center2570)
  rw [fjcmP001RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP001Factor2570 * embedPair2542 fjcmP001Center2570)
    (embedPair2542 fjcmP001Rounded2570)).trans (add_le_add fjcmP001DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP001Factor2570, fjcmP001Error2570, rounding2542,
      fjcmP001Radius2570]

theorem fjcmP001DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP001Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP001RoundedError2570 (embedPair_magnitude2542
      fjcmP001Rounded2570))
  apply h'.trans
  norm_num [fjcmP001Radius2570, pairMagnitude2542, fjcmP001Rounded2570]

noncomputable def fjcmP002Input2570 : RatPair2542 := ((((-((1908 * 10^40
        + 9356477313226526661601126851044270189063) * 10^40
        + 5191776234307827898306730134726634237041)) : ℚ) /
        ((8147 * 10^40
        + 6895918656149932623563298325318453465194) * 10^40
        + 9452298146475584633489225469132800000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def fjcmP002Center2570 : RatPair2542 := ((((-7510330962121851658113) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-167206057629782703065) : ℚ) /
        (2283596 * 10^40
        + 3083295358096932575511191922182123945984)))

def fjcmP002Factor2570 : RatPair2542 := ((((((19927458173227725776043 * 10^40
        + 2690117318636346021192956930819447261675) * 10^40
        + 7606482230257965636231267455327844182840) * 10^40
        + 2667446867398360400948527094263193367439) : ℚ) /
        (((483013323431043476903 * 10^40
        + 7511499335200218287611909907279225454881) * 10^40
        + 746082615335519961120361053248712426867) * 10^40
        + 9194345188221519198102945811473613265122)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjcmP002Error2570 : ℝ := ((47917824040196111573 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP002BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP002Center2570‖ ≤ fjcmP002Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP002Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP002Input2570]
  have hc : (compactExp2547 fjcmP002Input2570 8).1 = fjcmP002Center2570 := by cbv
  have he : ((compactExp2547 fjcmP002Input2570 8).2 : ℝ) = fjcmP002Error2570 := by
    have hq : (compactExp2547 fjcmP002Input2570 8).2 =
        ((47917824040196111573 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP002Error2570]
  have h := compactExp_error2547 fjcmP002Input2570 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjcmP002Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP002Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP002DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP002Factor2570 * embedPair2542 fjcmP002Center2570‖ ≤
        (pairMagnitude2542 fjcmP002Factor2570 : ℝ) * fjcmP002Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP002Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP002Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP002BaseError2570
    (embedPair_magnitude2542 fjcmP002Factor2570)

def fjcmP002Rounded2570 : RatPair2542 :=
  (((95581 : ℚ) /
        1267650600228229401496703205376),
    (((-638633) : ℚ) /
        1267650600228229401496703205376))

noncomputable def fjcmP002Radius2570 : ℝ := ((2199023258899 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP002RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP002Factor2570 fjcmP002Center2570) = fjcmP002Rounded2570 := by
  cbv

theorem fjcmP002RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP002Rounded2570‖ ≤ fjcmP002Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP002Factor2570 fjcmP002Center2570)
  rw [fjcmP002RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP002Factor2570 * embedPair2542 fjcmP002Center2570)
    (embedPair2542 fjcmP002Rounded2570)).trans (add_le_add fjcmP002DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP002Factor2570, fjcmP002Error2570, rounding2542,
      fjcmP002Radius2570]

theorem fjcmP002DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP002Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP002RoundedError2570 (embedPair_magnitude2542
      fjcmP002Rounded2570))
  apply h'.trans
  norm_num [fjcmP002Radius2570, pairMagnitude2542, fjcmP002Rounded2570]

noncomputable def fjcmP003Input2570 : RatPair2542 := ((((-((6741898 * 10^40
        + 8650175576592174173380311150688129946428) * 10^40
        + 2573857778485855228570792044839354408089)) : ℚ) /
        ((39860431 * 10^40
        + 3525369205518296877772896888819194996209) * 10^40
        + 8027785848626107559175480881971200000000)),
    (((-1751911280236833479653958331) : ℚ) /
        3689348814741910323200000000))

def fjcmP003Center2570 : RatPair2542 := ((((-16457100312752944049586069821) : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    (((-187592818628376015785955978523) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def fjcmP003Factor2570 : RatPair2542 := ((((((159929187887964078749905774346 * 10^40
        + 2911106577035738550624706132091463509159) * 10^40
        + 2192779424272312654623211523507388653835) * 10^40
        + 3667550152654527134075141835527094175999) : ℚ) /
        (((11560434268978921445520672852 * 10^40
        + 3151491610707945740034502288795420775469) * 10^40
        + 9342842308133684351566010846049001848136) * 10^40
        + 2052163694690945731849716328945811648002)),
    ((5524291025718029 : ℚ) /
        140737488355328))

noncomputable def fjcmP003Error2570 : ℝ := ((787019084893669535021784089 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP003BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP003Center2570‖ ≤ fjcmP003Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP003Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP003Input2570]
  have hc : (compactExp2547 fjcmP003Input2570 8).1 = fjcmP003Center2570 := by cbv
  have he : ((compactExp2547 fjcmP003Input2570 8).2 : ℝ) = fjcmP003Error2570 := by
    have hq : (compactExp2547 fjcmP003Input2570 8).2 =
        ((787019084893669535021784089 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP003Error2570]
  have h := compactExp_error2547 fjcmP003Input2570 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjcmP003Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP003Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP003DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP003Factor2570 * embedPair2542 fjcmP003Center2570‖ ≤
        (pairMagnitude2542 fjcmP003Factor2570 : ℝ) * fjcmP003Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP003Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP003Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP003BaseError2570
    (embedPair_magnitude2542 fjcmP003Factor2570)

def fjcmP003Rounded2570 : RatPair2542 :=
  (((2403508333533 : ℚ) /
        633825300114114700748351602688),
    (((-3366684385075) : ℚ) /
        633825300114114700748351602688))

noncomputable def fjcmP003Radius2570 : ℝ := ((2235261797137 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP003RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP003Factor2570 fjcmP003Center2570) = fjcmP003Rounded2570 := by
  cbv

theorem fjcmP003RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP003Rounded2570‖ ≤ fjcmP003Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP003Factor2570 fjcmP003Center2570)
  rw [fjcmP003RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP003Factor2570 * embedPair2542 fjcmP003Center2570)
    (embedPair2542 fjcmP003Rounded2570)).trans (add_le_add fjcmP003DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP003Factor2570, fjcmP003Error2570, rounding2542,
      fjcmP003Radius2570]

theorem fjcmP003DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP003Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP003RoundedError2570 (embedPair_magnitude2542
      fjcmP003Rounded2570))
  apply h'.trans
  norm_num [fjcmP003Radius2570, pairMagnitude2542, fjcmP003Rounded2570]

noncomputable def fjcmP004Input2570 : RatPair2542 := ((((-((4313 * 10^40
        + 1891010053817582509092773862775633242315) * 10^40
        + 9610172859229760383941744954062571737041)) : ℚ) /
        ((29780 * 10^40
        + 5895054484312759971766663273404887092534) * 10^40
        + 1331668037402944633489225469132800000000)),
    ((1751911280236833479653958331 : ℚ) /
        3689348814741910323200000000))

def fjcmP004Center2570 : RatPair2542 := ((((-66328937998152592934425233428247) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((23627401317734783120891400711731 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def fjcmP004Factor2570 : RatPair2542 := ((((((43053193436111892580981 * 10^40
        + 5268077254950526113516014890382988751958) * 10^40
        + 9368333013603576308597948378269469887780) * 10^40
        + 526438913939257057324931049341318367439) : ℚ) /
        (((6452926836878943435502 * 10^40
        + 5270363476754729271482605203204217239397) * 10^40
        + 2433289965035647104971396368485606800583) * 10^40
        + 9158788578070925885350137901317363265122)),
    (((-5524291025718029) : ℚ) /
        140737488355328))

noncomputable def fjcmP004Error2570 : ℝ := ((386980696826640705426490371081 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP004BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP004Center2570‖ ≤ fjcmP004Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP004Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP004Input2570]
  have hc : (compactExp2547 fjcmP004Input2570 8).1 = fjcmP004Center2570 := by cbv
  have he : ((compactExp2547 fjcmP004Input2570 8).2 : ℝ) = fjcmP004Error2570 := by
    have hq : (compactExp2547 fjcmP004Input2570 8).2 =
        ((386980696826640705426490371081 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP004Error2570]
  have h := compactExp_error2547 fjcmP004Input2570 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^8 * embedPair2542 fjcmP004Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP004Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP004DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP004Factor2570 * embedPair2542 fjcmP004Center2570‖ ≤
        (pairMagnitude2542 fjcmP004Factor2570 : ℝ) * fjcmP004Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP004Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP004Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP004BaseError2570
    (embedPair_magnitude2542 fjcmP004Factor2570)

def fjcmP004Rounded2570 : RatPair2542 :=
  (((2833839323295303 : ℚ) /
        1267650600228229401496703205376),
    ((2805161102151451 : ℚ) /
        1267650600228229401496703205376))

noncomputable def fjcmP004Radius2570 : ℝ := ((2201703692675 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

theorem fjcmP004RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP004Factor2570 fjcmP004Center2570) = fjcmP004Rounded2570 := by
  cbv

theorem fjcmP004RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP004Rounded2570‖ ≤ fjcmP004Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP004Factor2570 fjcmP004Center2570)
  rw [fjcmP004RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP004Factor2570 * embedPair2542 fjcmP004Center2570)
    (embedPair2542 fjcmP004Rounded2570)).trans (add_le_add fjcmP004DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP004Factor2570, fjcmP004Error2570, rounding2542,
      fjcmP004Radius2570]

theorem fjcmP004DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP004Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP004RoundedError2570 (embedPair_magnitude2542
      fjcmP004Rounded2570))
  apply h'.trans
  norm_num [fjcmP004Radius2570, pairMagnitude2542, fjcmP004Rounded2570]

def fjcmP005Center2570 : RatPair2542 := (0, 0)

def fjcmP005Factor2570 : RatPair2542 := (0, 0)

noncomputable def fjcmP005Error2570 : ℝ := 0

theorem fjcmP005Exterior2570 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 = 0 := by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |edgeMidpointPosition2548| := by
    norm_num [storedWidth, edgeMidpointPosition2548]
  exact weightedFamily_outside_zero2543 n (-1/2)
    (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem fjcmP005BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP005Center2570‖ ≤ fjcmP005Error2570 := by
  rw [fjcmP005Exterior2570]
  norm_num [fjcmP005Center2570, fjcmP005Error2570, fjcmZero2570]

theorem fjcmP005DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP005Factor2570 * embedPair2542 fjcmP005Center2570‖ ≤
        (pairMagnitude2542 fjcmP005Factor2570 : ℝ) * fjcmP005Error2570 := by
  rw [fjcmP005Exterior2570]
  norm_num [fjcmP005Factor2570, fjcmP005Center2570, fjcmP005Error2570, pairMagnitude2542,
      fjcmZero2570]

def fjcmP005Rounded2570 : RatPair2542 := (0, 0)

noncomputable def fjcmP005Radius2570 : ℝ := 0

theorem fjcmP005RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP005Factor2570 fjcmP005Center2570) = fjcmP005Rounded2570 := by
  cbv

theorem fjcmP005RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP005Rounded2570‖ ≤ fjcmP005Radius2570 := by
  rw [fjcmP005Exterior2570]
  norm_num [fjcmP005Rounded2570, fjcmP005Radius2570, fjcmZero2570]

theorem fjcmP005DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨5, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  rw [fjcmP005Exterior2570]
  norm_num

noncomputable def fjcmP006Input2570 : RatPair2542 := ((((-1009480612784001817040786481870793719) :
    ℚ) /
        1761648103394083163919587737600000000),
    ((0 : ℚ) /
        1))

def fjcmP006Center2570 : RatPair2542 := (((2552935579348625 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((0 : ℚ) /
        1))

def fjcmP006Factor2570 : RatPair2542 := ((((64927152 * 10^40
        + 630156867445020113682589906669419017759) : ℚ) /
        (903209 * 10^40
        + 4502448949280199772634820186661161964482)),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP006Error2570 : ℝ := ((3648537530399 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem fjcmP006BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP006Center2570‖ ≤ fjcmP006Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP006Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP006Input2570]
  have hc : (compactExp2547 fjcmP006Input2570 7).1 = fjcmP006Center2570 := by cbv
  have he : ((compactExp2547 fjcmP006Input2570 7).2 : ℝ) = fjcmP006Error2570 := by
    have hq : (compactExp2547 fjcmP006Input2570 7).2 =
        ((3648537530399 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688)) := by cbv
    rw [hq]
    norm_num [fjcmP006Error2570]
  have h := compactExp_error2547 fjcmP006Input2570 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^7 * embedPair2542 fjcmP006Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP006Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP006DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP006Factor2570 * embedPair2542 fjcmP006Center2570‖ ≤
        (pairMagnitude2542 fjcmP006Factor2570 : ℝ) * fjcmP006Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP006Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP006Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP006BaseError2570
    (embedPair_magnitude2542 fjcmP006Factor2570)

def fjcmP006Rounded2570 : RatPair2542 :=
  (((1 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP006Radius2570 : ℝ := ((2199023255553 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP006RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP006Factor2570 fjcmP006Center2570) = fjcmP006Rounded2570 := by
  cbv

theorem fjcmP006RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP006Rounded2570‖ ≤ fjcmP006Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP006Factor2570 fjcmP006Center2570)
  rw [fjcmP006RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP006Factor2570 * embedPair2542 fjcmP006Center2570)
    (embedPair2542 fjcmP006Rounded2570)).trans (add_le_add fjcmP006DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP006Factor2570, fjcmP006Error2570, rounding2542,
      fjcmP006Radius2570]

theorem fjcmP006DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP006Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP006RoundedError2570 (embedPair_magnitude2542
      fjcmP006Rounded2570))
  apply h'.trans
  norm_num [fjcmP006Radius2570, pairMagnitude2542, fjcmP006Rounded2570]

noncomputable def fjcmP007Input2570 : RatPair2542 := ((((-((6741898 * 10^40
        + 8650175576592174173380311150688129946428) * 10^40
        + 2573857778485855228570792044839354408089)) : ℚ) /
        ((9965107 * 10^40
        + 8381342301379574219443224222204798749052) * 10^40
        + 4506946462156526889793870220492800000000)),
    ((0 : ℚ) /
        1))

def fjcmP007Center2570 : RatPair2542 := (((57295603695874659276408122021 : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((0 : ℚ) /
        1))

def fjcmP007Factor2570 : RatPair2542 := ((((((159929187887964078749905774346 * 10^40
        + 2911106577035738550624706132091463509159) * 10^40
        + 2192779424272312654623211523507388653835) * 10^40
        + 3667550152654527134075141835527094175999) : ℚ) /
        (((11560434268978921445520672852 * 10^40
        + 3151491610707945740034502288795420775469) * 10^40
        + 9342842308133684351566010846049001848136) * 10^40
        + 2052163694690945731849716328945811648002)),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP007Error2570 : ℝ := ((31723657183144844024517521 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP007BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP007Center2570‖ ≤ fjcmP007Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP007Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP007Input2570]
  have hc : (compactExp2547 fjcmP007Input2570 6).1 = fjcmP007Center2570 := by cbv
  have he : ((compactExp2547 fjcmP007Input2570 6).2 : ℝ) = fjcmP007Error2570 := by
    have hq : (compactExp2547 fjcmP007Input2570 6).2 =
        ((31723657183144844024517521 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP007Error2570]
  have h := compactExp_error2547 fjcmP007Input2570 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^6 * embedPair2542 fjcmP007Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP007Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP007DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP007Factor2570 * embedPair2542 fjcmP007Center2570‖ ≤
        (pairMagnitude2542 fjcmP007Factor2570 : ℝ) * fjcmP007Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP007Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP007Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP007BaseError2570
    (embedPair_magnitude2542 fjcmP007Factor2570)

def fjcmP007Rounded2570 : RatPair2542 :=
  (((343751931781 : ℚ) /
        158456325028528675187087900672),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP007Radius2570 : ℝ := ((2199403915419 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP007RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP007Factor2570 fjcmP007Center2570) = fjcmP007Rounded2570 := by
  cbv

theorem fjcmP007RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP007Rounded2570‖ ≤ fjcmP007Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP007Factor2570 fjcmP007Center2570)
  rw [fjcmP007RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP007Factor2570 * embedPair2542 fjcmP007Center2570)
    (embedPair2542 fjcmP007Rounded2570)).trans (add_le_add fjcmP007DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP007Factor2570, fjcmP007Error2570, rounding2542,
      fjcmP007Radius2570]

theorem fjcmP007DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP007Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP007RoundedError2570 (embedPair_magnitude2542
      fjcmP007Rounded2570))
  apply h'.trans
  norm_num [fjcmP007Radius2570, pairMagnitude2542, fjcmP007Rounded2570]

noncomputable def fjcmP008Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1261719220645415482412484183 : ℚ) /
        3777893186295716170956800000000))

def fjcmP008Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP008Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3978571430081297) : ℚ) /
        281474976710656))

noncomputable def fjcmP008Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP008BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP008Center2570‖ ≤ fjcmP008Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP008Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP008Input2570]
  have hc : (compactExp2547 fjcmP008Input2570 17).1 = fjcmP008Center2570 := by cbv
  have he : ((compactExp2547 fjcmP008Input2570 17).2 : ℝ) = fjcmP008Error2570 := by
    have hq : (compactExp2547 fjcmP008Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP008Error2570]
  have h := compactExp_error2547 fjcmP008Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP008Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP008Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP008DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP008Factor2570 * embedPair2542 fjcmP008Center2570‖ ≤
        (pairMagnitude2542 fjcmP008Factor2570 : ℝ) * fjcmP008Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP008Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP008Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP008BaseError2570
    (embedPair_magnitude2542 fjcmP008Factor2570)

def fjcmP008Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP008Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP008RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP008Factor2570 fjcmP008Center2570) = fjcmP008Rounded2570 := by
  cbv

theorem fjcmP008RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP008Rounded2570‖ ≤ fjcmP008Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP008Factor2570 fjcmP008Center2570)
  rw [fjcmP008RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP008Factor2570 * embedPair2542 fjcmP008Center2570)
    (embedPair2542 fjcmP008Rounded2570)).trans (add_le_add fjcmP008DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP008Factor2570, fjcmP008Error2570, rounding2542,
      fjcmP008Radius2570]

theorem fjcmP008DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP008Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP008RoundedError2570 (embedPair_magnitude2542
      fjcmP008Rounded2570))
  apply h'.trans
  norm_num [fjcmP008Radius2570, pairMagnitude2542, fjcmP008Rounded2570]

noncomputable def fjcmP009Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1876507056447276098253971529 : ℚ) /
        3777893186295716170956800000000))

def fjcmP009Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP009Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5917178117733711) : ℚ) /
        281474976710656))

noncomputable def fjcmP009Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP009BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP009Center2570‖ ≤ fjcmP009Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP009Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP009Input2570]
  have hc : (compactExp2547 fjcmP009Input2570 17).1 = fjcmP009Center2570 := by cbv
  have he : ((compactExp2547 fjcmP009Input2570 17).2 : ℝ) = fjcmP009Error2570 := by
    have hq : (compactExp2547 fjcmP009Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP009Error2570]
  have h := compactExp_error2547 fjcmP009Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP009Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP009Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP009DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP009Factor2570 * embedPair2542 fjcmP009Center2570‖ ≤
        (pairMagnitude2542 fjcmP009Factor2570 : ℝ) * fjcmP009Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP009Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP009Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP009BaseError2570
    (embedPair_magnitude2542 fjcmP009Factor2570)

def fjcmP009Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP009Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP009RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP009Factor2570 fjcmP009Center2570) = fjcmP009Rounded2570 := by
  cbv

theorem fjcmP009RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP009Rounded2570‖ ≤ fjcmP009Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP009Factor2570 fjcmP009Center2570)
  rw [fjcmP009RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP009Factor2570 * embedPair2542 fjcmP009Center2570)
    (embedPair2542 fjcmP009Rounded2570)).trans (add_le_add fjcmP009DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP009Factor2570, fjcmP009Error2570, rounding2542,
      fjcmP009Radius2570]

theorem fjcmP009DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP009Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP009RoundedError2570 (embedPair_magnitude2542
      fjcmP009Rounded2570))
  apply h'.trans
  norm_num [fjcmP009Radius2570, pairMagnitude2542, fjcmP009Rounded2570]

noncomputable def fjcmP010Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1116282043593459096767143119 : ℚ) /
        1888946593147858085478400000000))

def fjcmP010Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP010Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3519965277442521) : ℚ) /
        140737488355328))

noncomputable def fjcmP010Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP010BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP010Center2570‖ ≤ fjcmP010Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP010Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP010Input2570]
  have hc : (compactExp2547 fjcmP010Input2570 17).1 = fjcmP010Center2570 := by cbv
  have he : ((compactExp2547 fjcmP010Input2570 17).2 : ℝ) = fjcmP010Error2570 := by
    have hq : (compactExp2547 fjcmP010Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP010Error2570]
  have h := compactExp_error2547 fjcmP010Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP010Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP010Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP010DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP010Factor2570 * embedPair2542 fjcmP010Center2570‖ ≤
        (pairMagnitude2542 fjcmP010Factor2570 : ℝ) * fjcmP010Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP010Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP010Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP010BaseError2570
    (embedPair_magnitude2542 fjcmP010Factor2570)

def fjcmP010Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP010Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP010RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP010Factor2570 fjcmP010Center2570) = fjcmP010Rounded2570 := by
  cbv

theorem fjcmP010RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP010Rounded2570‖ ≤ fjcmP010Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP010Factor2570 fjcmP010Center2570)
  rw [fjcmP010RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP010Factor2570 * embedPair2542 fjcmP010Center2570)
    (embedPair2542 fjcmP010Rounded2570)).trans (add_le_add fjcmP010DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP010Factor2570, fjcmP010Error2570, rounding2542,
      fjcmP010Radius2570]

theorem fjcmP010DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP010Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP010RoundedError2570 (embedPair_magnitude2542
      fjcmP010Rounded2570))
  apply h'.trans
  norm_num [fjcmP010Radius2570, pairMagnitude2542, fjcmP010Rounded2570]

noncomputable def fjcmP011Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1234978985119947335660559039 : ℚ) /
        1888946593147858085478400000000))

def fjcmP011Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP011Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3894251610461801) : ℚ) /
        140737488355328))

noncomputable def fjcmP011Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP011BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP011Center2570‖ ≤ fjcmP011Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP011Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP011Input2570]
  have hc : (compactExp2547 fjcmP011Input2570 17).1 = fjcmP011Center2570 := by cbv
  have he : ((compactExp2547 fjcmP011Input2570 17).2 : ℝ) = fjcmP011Error2570 := by
    have hq : (compactExp2547 fjcmP011Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP011Error2570]
  have h := compactExp_error2547 fjcmP011Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP011Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP011Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP011DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP011Factor2570 * embedPair2542 fjcmP011Center2570‖ ≤
        (pairMagnitude2542 fjcmP011Factor2570 : ℝ) * fjcmP011Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP011Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP011Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP011BaseError2570
    (embedPair_magnitude2542 fjcmP011Factor2570)

def fjcmP011Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP011Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP011RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP011Factor2570 fjcmP011Center2570) = fjcmP011Rounded2570 := by
  cbv

theorem fjcmP011RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP011Rounded2570‖ ≤ fjcmP011Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP011Factor2570 fjcmP011Center2570)
  rw [fjcmP011RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP011Factor2570 * embedPair2542 fjcmP011Center2570)
    (embedPair2542 fjcmP011Rounded2570)).trans (add_le_add fjcmP011DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP011Factor2570, fjcmP011Error2570, rounding2542,
      fjcmP011Radius2570]

theorem fjcmP011DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP011Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP011RoundedError2570 (embedPair_magnitude2542
      fjcmP011Rounded2570))
  apply h'.trans
  norm_num [fjcmP011Radius2570, pairMagnitude2542, fjcmP011Rounded2570]

noncomputable def fjcmP012Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((27158399338384035222570051 : ℚ) /
        37778931862957161709568000000))

def fjcmP012Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP012Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2140960324737725) : ℚ) /
        70368744177664))

noncomputable def fjcmP012Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP012BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP012Center2570‖ ≤ fjcmP012Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP012Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP012Input2570]
  have hc : (compactExp2547 fjcmP012Input2570 17).1 = fjcmP012Center2570 := by cbv
  have he : ((compactExp2547 fjcmP012Input2570 17).2 : ℝ) = fjcmP012Error2570 := by
    have hq : (compactExp2547 fjcmP012Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP012Error2570]
  have h := compactExp_error2547 fjcmP012Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP012Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP012Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP012DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP012Factor2570 * embedPair2542 fjcmP012Center2570‖ ≤
        (pairMagnitude2542 fjcmP012Factor2570 : ℝ) * fjcmP012Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP012Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP012Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP012BaseError2570
    (embedPair_magnitude2542 fjcmP012Factor2570)

def fjcmP012Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP012Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP012RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP012Factor2570 fjcmP012Center2570) = fjcmP012Rounded2570 := by
  cbv

theorem fjcmP012RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP012Rounded2570‖ ≤ fjcmP012Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP012Factor2570 fjcmP012Center2570)
  rw [fjcmP012RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP012Factor2570 * embedPair2542 fjcmP012Center2570)
    (embedPair2542 fjcmP012Rounded2570)).trans (add_le_add fjcmP012DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP012Factor2570, fjcmP012Error2570, rounding2542,
      fjcmP012Radius2570]

theorem fjcmP012DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP012Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP012RoundedError2570 (embedPair_magnitude2542
      fjcmP012Rounded2570))
  apply h'.trans
  norm_num [fjcmP012Radius2570, pairMagnitude2542, fjcmP012Rounded2570]

noncomputable def fjcmP013Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((293990861666597709724015149 : ℚ) /
        377789318629571617095680000000))

def fjcmP013Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP013Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4635197846686455) : ℚ) /
        140737488355328))

noncomputable def fjcmP013Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP013BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP013Center2570‖ ≤ fjcmP013Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP013Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP013Input2570]
  have hc : (compactExp2547 fjcmP013Input2570 17).1 = fjcmP013Center2570 := by cbv
  have he : ((compactExp2547 fjcmP013Input2570 17).2 : ℝ) = fjcmP013Error2570 := by
    have hq : (compactExp2547 fjcmP013Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP013Error2570]
  have h := compactExp_error2547 fjcmP013Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP013Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP013Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP013DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP013Factor2570 * embedPair2542 fjcmP013Center2570‖ ≤
        (pairMagnitude2542 fjcmP013Factor2570 : ℝ) * fjcmP013Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP013Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP013Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP013BaseError2570
    (embedPair_magnitude2542 fjcmP013Factor2570)

def fjcmP013Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP013Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP013RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP013Factor2570 fjcmP013Center2570) = fjcmP013Rounded2570 := by
  cbv

theorem fjcmP013RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP013Rounded2570‖ ≤ fjcmP013Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP013Factor2570 fjcmP013Center2570)
  rw [fjcmP013RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP013Factor2570 * embedPair2542 fjcmP013Center2570)
    (embedPair2542 fjcmP013Rounded2570)).trans (add_le_add fjcmP013DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP013Factor2570, fjcmP013Error2570, rounding2542,
      fjcmP013Radius2570]

theorem fjcmP013DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP013Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP013RoundedError2570 (embedPair_magnitude2542
      fjcmP013Rounded2570))
  apply h'.trans
  norm_num [fjcmP013Radius2570, pairMagnitude2542, fjcmP013Rounded2570]

noncomputable def fjcmP014Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1677542468568059149194008229 : ℚ) /
        1888946593147858085478400000000))

def fjcmP014Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP014Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5289784310949011) : ℚ) /
        140737488355328))

noncomputable def fjcmP014Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP014BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP014Center2570‖ ≤ fjcmP014Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP014Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP014Input2570]
  have hc : (compactExp2547 fjcmP014Input2570 17).1 = fjcmP014Center2570 := by cbv
  have he : ((compactExp2547 fjcmP014Input2570 17).2 : ℝ) = fjcmP014Error2570 := by
    have hq : (compactExp2547 fjcmP014Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP014Error2570]
  have h := compactExp_error2547 fjcmP014Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP014Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP014Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP014DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP014Factor2570 * embedPair2542 fjcmP014Center2570‖ ≤
        (pairMagnitude2542 fjcmP014Factor2570 : ℝ) * fjcmP014Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP014Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP014Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP014BaseError2570
    (embedPair_magnitude2542 fjcmP014Factor2570)

def fjcmP014Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP014Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP014RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP014Factor2570 fjcmP014Center2570) = fjcmP014Rounded2570 := by
  cbv

theorem fjcmP014RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP014Rounded2570‖ ≤ fjcmP014Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP014Factor2570 fjcmP014Center2570)
  rw [fjcmP014RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP014Factor2570 * embedPair2542 fjcmP014Center2570)
    (embedPair2542 fjcmP014Rounded2570)).trans (add_le_add fjcmP014DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP014Factor2570, fjcmP014Error2570, rounding2542,
      fjcmP014Radius2570]

theorem fjcmP014DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP014Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP014RoundedError2570 (embedPair_magnitude2542
      fjcmP014Rounded2570))
  apply h'.trans
  norm_num [fjcmP014Radius2570, pairMagnitude2542, fjcmP014Rounded2570]

noncomputable def fjcmP015Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1826280091905607810113908433 : ℚ) /
        1888946593147858085478400000000))

def fjcmP015Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP015Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-5758797740487047) : ℚ) /
        140737488355328))

noncomputable def fjcmP015Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP015BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP015Center2570‖ ≤ fjcmP015Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP015Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP015Input2570]
  have hc : (compactExp2547 fjcmP015Input2570 17).1 = fjcmP015Center2570 := by cbv
  have he : ((compactExp2547 fjcmP015Input2570 17).2 : ℝ) = fjcmP015Error2570 := by
    have hq : (compactExp2547 fjcmP015Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP015Error2570]
  have h := compactExp_error2547 fjcmP015Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP015Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP015Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP015DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP015Factor2570 * embedPair2542 fjcmP015Center2570‖ ≤
        (pairMagnitude2542 fjcmP015Factor2570 : ℝ) * fjcmP015Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP015Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP015Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP015BaseError2570
    (embedPair_magnitude2542 fjcmP015Factor2570)

def fjcmP015Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP015Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP015RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP015Factor2570 fjcmP015Center2570) = fjcmP015Rounded2570 := by
  cbv

theorem fjcmP015RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP015Rounded2570‖ ≤ fjcmP015Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP015Factor2570 fjcmP015Center2570)
  rw [fjcmP015RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP015Factor2570 * embedPair2542 fjcmP015Center2570)
    (embedPair2542 fjcmP015Rounded2570)).trans (add_le_add fjcmP015DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP015Factor2570, fjcmP015Error2570, rounding2542,
      fjcmP015Radius2570]

theorem fjcmP015DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP015Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP015RoundedError2570 (embedPair_magnitude2542
      fjcmP015Rounded2570))
  apply h'.trans
  norm_num [fjcmP015Radius2570, pairMagnitude2542, fjcmP015Rounded2570]

noncomputable def fjcmP016Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((966884756949258260679651951 : ℚ) /
        944473296573929042739200000000))

def fjcmP016Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP016Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-3048871735671609) : ℚ) /
        70368744177664))

noncomputable def fjcmP016Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP016BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP016Center2570‖ ≤ fjcmP016Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP016Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP016Input2570]
  have hc : (compactExp2547 fjcmP016Input2570 17).1 = fjcmP016Center2570 := by cbv
  have he : ((compactExp2547 fjcmP016Input2570 17).2 : ℝ) = fjcmP016Error2570 := by
    have hq : (compactExp2547 fjcmP016Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP016Error2570]
  have h := compactExp_error2547 fjcmP016Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP016Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP016Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP016DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP016Factor2570 * embedPair2542 fjcmP016Center2570‖ ≤
        (pairMagnitude2542 fjcmP016Factor2570 : ℝ) * fjcmP016Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP016Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP016Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP016BaseError2570
    (embedPair_magnitude2542 fjcmP016Factor2570)

def fjcmP016Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP016Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP016RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP016Factor2570 fjcmP016Center2570) = fjcmP016Rounded2570 := by
  cbv

theorem fjcmP016RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP016Rounded2570‖ ≤ fjcmP016Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP016Factor2570 fjcmP016Center2570)
  rw [fjcmP016RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP016Factor2570 * embedPair2542 fjcmP016Center2570)
    (embedPair2542 fjcmP016Rounded2570)).trans (add_le_add fjcmP016DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP016Factor2570, fjcmP016Error2570, rounding2542,
      fjcmP016Radius2570]

theorem fjcmP016DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP016Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP016RoundedError2570 (embedPair_magnitude2542
      fjcmP016Rounded2570))
  apply h'.trans
  norm_num [fjcmP016Radius2570, pairMagnitude2542, fjcmP016Rounded2570]

noncomputable def fjcmP017Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2142560996036405154016564653 : ℚ) /
        1888946593147858085478400000000))

def fjcmP017Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP017Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-6756124363134027) : ℚ) /
        140737488355328))

noncomputable def fjcmP017Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP017BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP017Center2570‖ ≤ fjcmP017Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP017Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP017Input2570]
  have hc : (compactExp2547 fjcmP017Input2570 17).1 = fjcmP017Center2570 := by cbv
  have he : ((compactExp2547 fjcmP017Input2570 17).2 : ℝ) = fjcmP017Error2570 := by
    have hq : (compactExp2547 fjcmP017Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP017Error2570]
  have h := compactExp_error2547 fjcmP017Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP017Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP017Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP017DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP017Factor2570 * embedPair2542 fjcmP017Center2570‖ ≤
        (pairMagnitude2542 fjcmP017Factor2570 : ℝ) * fjcmP017Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP017Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP017Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP017BaseError2570
    (embedPair_magnitude2542 fjcmP017Factor2570)

def fjcmP017Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP017Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP017RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP017Factor2570 fjcmP017Center2570) = fjcmP017Rounded2570 := by
  cbv

theorem fjcmP017RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP017Rounded2570‖ ≤ fjcmP017Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP017Factor2570 fjcmP017Center2570)
  rw [fjcmP017RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP017Factor2570 * embedPair2542 fjcmP017Center2570)
    (embedPair2542 fjcmP017Rounded2570)).trans (add_le_add fjcmP017DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP017Factor2570, fjcmP017Error2570, rounding2542,
      fjcmP017Radius2570]

theorem fjcmP017DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP017Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP017RoundedError2570 (embedPair_magnitude2542
      fjcmP017Rounded2570))
  apply h'.trans
  norm_num [fjcmP017Radius2570, pairMagnitude2542, fjcmP017Rounded2570]

noncomputable def fjcmP018Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((555375153147096446436377307 : ℚ) /
        472236648286964521369600000000))

def fjcmP018Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP018Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-1751261042181613) : ℚ) /
        35184372088832))

noncomputable def fjcmP018Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP018BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP018Center2570‖ ≤ fjcmP018Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP018Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP018Input2570]
  have hc : (compactExp2547 fjcmP018Input2570 17).1 = fjcmP018Center2570 := by cbv
  have he : ((compactExp2547 fjcmP018Input2570 17).2 : ℝ) = fjcmP018Error2570 := by
    have hq : (compactExp2547 fjcmP018Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP018Error2570]
  have h := compactExp_error2547 fjcmP018Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP018Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP018Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP018DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP018Factor2570 * embedPair2542 fjcmP018Center2570‖ ≤
        (pairMagnitude2542 fjcmP018Factor2570 : ℝ) * fjcmP018Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP018Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP018Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP018BaseError2570
    (embedPair_magnitude2542 fjcmP018Factor2570)

def fjcmP018Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP018Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP018RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP018Factor2570 fjcmP018Center2570) = fjcmP018Rounded2570 := by
  cbv

theorem fjcmP018RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP018Rounded2570‖ ≤ fjcmP018Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP018Factor2570 fjcmP018Center2570)
  rw [fjcmP018RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP018Factor2570 * embedPair2542 fjcmP018Center2570)
    (embedPair2542 fjcmP018Rounded2570)).trans (add_le_add fjcmP018DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP018Factor2570, fjcmP018Error2570, rounding2542,
      fjcmP018Radius2570]

theorem fjcmP018DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP018Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP018RoundedError2570 (embedPair_magnitude2542
      fjcmP018Rounded2570))
  apply h'.trans
  norm_num [fjcmP018Radius2570, pairMagnitude2542, fjcmP018Rounded2570]

noncomputable def fjcmP019Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((118208299174604243670929049 : ℚ) /
        94447329657392904273920000000))

def fjcmP019Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP019Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-1863727500536955) : ℚ) /
        35184372088832))

noncomputable def fjcmP019Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP019BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP019Center2570‖ ≤ fjcmP019Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP019Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP019Input2570]
  have hc : (compactExp2547 fjcmP019Input2570 17).1 = fjcmP019Center2570 := by cbv
  have he : ((compactExp2547 fjcmP019Input2570 17).2 : ℝ) = fjcmP019Error2570 := by
    have hq : (compactExp2547 fjcmP019Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP019Error2570]
  have h := compactExp_error2547 fjcmP019Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP019Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP019Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP019DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP019Factor2570 * embedPair2542 fjcmP019Center2570‖ ≤
        (pairMagnitude2542 fjcmP019Factor2570 : ℝ) * fjcmP019Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP019Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP019Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP019BaseError2570
    (embedPair_magnitude2542 fjcmP019Factor2570)

def fjcmP019Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP019Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP019RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP019Factor2570 fjcmP019Center2570) = fjcmP019Rounded2570 := by
  cbv

theorem fjcmP019RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP019Rounded2570‖ ≤ fjcmP019Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP019Factor2570 fjcmP019Center2570)
  rw [fjcmP019RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP019Factor2570 * embedPair2542 fjcmP019Center2570)
    (embedPair2542 fjcmP019Rounded2570)).trans (add_le_add fjcmP019DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP019Factor2570, fjcmP019Error2570, rounding2542,
      fjcmP019Radius2570]

theorem fjcmP019DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP019Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP019RoundedError2570 (embedPair_magnitude2542
      fjcmP019Rounded2570))
  apply h'.trans
  norm_num [fjcmP019Radius2570, pairMagnitude2542, fjcmP019Rounded2570]

noncomputable def fjcmP020Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2519303167856168777929316541 : ℚ) /
        1888946593147858085478400000000))

def fjcmP020Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP020Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-7944103127967419) : ℚ) /
        140737488355328))

noncomputable def fjcmP020Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP020BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP020Center2570‖ ≤ fjcmP020Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP020Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP020Input2570]
  have hc : (compactExp2547 fjcmP020Input2570 17).1 = fjcmP020Center2570 := by cbv
  have he : ((compactExp2547 fjcmP020Input2570 17).2 : ℝ) = fjcmP020Error2570 := by
    have hq : (compactExp2547 fjcmP020Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP020Error2570]
  have h := compactExp_error2547 fjcmP020Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP020Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP020Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP020DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP020Factor2570 * embedPair2542 fjcmP020Center2570‖ ≤
        (pairMagnitude2542 fjcmP020Factor2570 : ℝ) * fjcmP020Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP020Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP020Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP020BaseError2570
    (embedPair_magnitude2542 fjcmP020Factor2570)

def fjcmP020Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP020Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP020RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP020Factor2570 fjcmP020Center2570) = fjcmP020Rounded2570 := by
  cbv

theorem fjcmP020RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP020Rounded2570‖ ≤ fjcmP020Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP020Factor2570 fjcmP020Center2570)
  rw [fjcmP020RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP020Factor2570 * embedPair2542 fjcmP020Center2570)
    (embedPair2542 fjcmP020Rounded2570)).trans (add_le_add fjcmP020DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP020Factor2570, fjcmP020Error2570, rounding2542,
      fjcmP020Radius2570]

theorem fjcmP020DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP020Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP020RoundedError2570 (embedPair_magnitude2542
      fjcmP020Rounded2570))
  apply h'.trans
  norm_num [fjcmP020Radius2570, pairMagnitude2542, fjcmP020Rounded2570]

noncomputable def fjcmP021Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((2648771212589104536068841693 : ℚ) /
        1888946593147858085478400000000))

def fjcmP021Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP021Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-8352353914239387) : ℚ) /
        140737488355328))

noncomputable def fjcmP021Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP021BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP021Center2570‖ ≤ fjcmP021Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP021Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP021Input2570]
  have hc : (compactExp2547 fjcmP021Input2570 17).1 = fjcmP021Center2570 := by cbv
  have he : ((compactExp2547 fjcmP021Input2570 17).2 : ℝ) = fjcmP021Error2570 := by
    have hq : (compactExp2547 fjcmP021Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP021Error2570]
  have h := compactExp_error2547 fjcmP021Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP021Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP021Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP021DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP021Factor2570 * embedPair2542 fjcmP021Center2570‖ ≤
        (pairMagnitude2542 fjcmP021Factor2570 : ℝ) * fjcmP021Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP021Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP021Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP021BaseError2570
    (embedPair_magnitude2542 fjcmP021Factor2570)

def fjcmP021Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP021Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP021RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP021Factor2570 fjcmP021Center2570) = fjcmP021Rounded2570 := by
  cbv

theorem fjcmP021RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP021Rounded2570‖ ≤ fjcmP021Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP021Factor2570 fjcmP021Center2570)
  rw [fjcmP021RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP021Factor2570 * embedPair2542 fjcmP021Center2570)
    (embedPair2542 fjcmP021Rounded2570)).trans (add_le_add fjcmP021DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP021Factor2570, fjcmP021Error2570, rounding2542,
      fjcmP021Radius2570]

theorem fjcmP021DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP021Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP021RoundedError2570 (embedPair_magnitude2542
      fjcmP021Rounded2570))
  apply h'.trans
  norm_num [fjcmP021Radius2570, pairMagnitude2542, fjcmP021Rounded2570]

noncomputable def fjcmP022Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((543007546456794340281131487 : ℚ) /
        377789318629571617095680000000))

def fjcmP022Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP022Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-8561311721741165) : ℚ) /
        140737488355328))

noncomputable def fjcmP022Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP022BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP022Center2570‖ ≤ fjcmP022Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP022Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP022Input2570]
  have hc : (compactExp2547 fjcmP022Input2570 17).1 = fjcmP022Center2570 := by cbv
  have he : ((compactExp2547 fjcmP022Input2570 17).2 : ℝ) = fjcmP022Error2570 := by
    have hq : (compactExp2547 fjcmP022Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP022Error2570]
  have h := compactExp_error2547 fjcmP022Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP022Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP022Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP022DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP022Factor2570 * embedPair2542 fjcmP022Center2570‖ ≤
        (pairMagnitude2542 fjcmP022Factor2570 : ℝ) * fjcmP022Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP022Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP022Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP022BaseError2570
    (embedPair_magnitude2542 fjcmP022Factor2570)

def fjcmP022Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP022Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP022RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP022Factor2570 fjcmP022Center2570) = fjcmP022Rounded2570 := by
  cbv

theorem fjcmP022RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP022Rounded2570‖ ≤ fjcmP022Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP022Factor2570 fjcmP022Center2570)
  rw [fjcmP022RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP022Factor2570 * embedPair2542 fjcmP022Center2570)
    (embedPair2542 fjcmP022Rounded2570)).trans (add_le_add fjcmP022DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP022Factor2570, fjcmP022Error2570, rounding2542,
      fjcmP022Radius2570]

theorem fjcmP022DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP022Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP022RoundedError2570 (embedPair_magnitude2542
      fjcmP022Rounded2570))
  apply h'.trans
  norm_num [fjcmP022Radius2570, pairMagnitude2542, fjcmP022Rounded2570]

noncomputable def fjcmP023Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1453048211174897778209007387 : ℚ) /
        944473296573929042739200000000))

def fjcmP023Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP023Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4581887954876333) : ℚ) /
        70368744177664))

noncomputable def fjcmP023Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP023BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP023Center2570‖ ≤ fjcmP023Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP023Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP023Input2570]
  have hc : (compactExp2547 fjcmP023Input2570 17).1 = fjcmP023Center2570 := by cbv
  have he : ((compactExp2547 fjcmP023Input2570 17).2 : ℝ) = fjcmP023Error2570 := by
    have hq : (compactExp2547 fjcmP023Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP023Error2570]
  have h := compactExp_error2547 fjcmP023Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP023Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP023Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP023DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP023Factor2570 * embedPair2542 fjcmP023Center2570‖ ≤
        (pairMagnitude2542 fjcmP023Factor2570 : ℝ) * fjcmP023Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP023Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP023Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP023BaseError2570
    (embedPair_magnitude2542 fjcmP023Factor2570)

def fjcmP023Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP023Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP023RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP023Factor2570 fjcmP023Center2570) = fjcmP023Rounded2570 := by
  cbv

theorem fjcmP023RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP023Rounded2570‖ ≤ fjcmP023Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP023Factor2570 fjcmP023Center2570)
  rw [fjcmP023RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP023Factor2570 * embedPair2542 fjcmP023Center2570)
    (embedPair2542 fjcmP023Rounded2570)).trans (add_le_add fjcmP023DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP023Factor2570, fjcmP023Error2570, rounding2542,
      fjcmP023Radius2570]

theorem fjcmP023DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP023Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP023RoundedError2570 (embedPair_magnitude2542
      fjcmP023Rounded2570))
  apply h'.trans
  norm_num [fjcmP023Radius2570, pairMagnitude2542, fjcmP023Rounded2570]

noncomputable def fjcmP024Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((1496949629611413064555803333 : ℚ) /
        944473296573929042739200000000))

def fjcmP024Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP024Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-4720322026636147) : ℚ) /
        70368744177664))

noncomputable def fjcmP024Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP024BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP024Center2570‖ ≤ fjcmP024Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP024Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP024Input2570]
  have hc : (compactExp2547 fjcmP024Input2570 17).1 = fjcmP024Center2570 := by cbv
  have he : ((compactExp2547 fjcmP024Input2570 17).2 : ℝ) = fjcmP024Error2570 := by
    have hq : (compactExp2547 fjcmP024Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP024Error2570]
  have h := compactExp_error2547 fjcmP024Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP024Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP024Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP024DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP024Factor2570 * embedPair2542 fjcmP024Center2570‖ ≤
        (pairMagnitude2542 fjcmP024Factor2570 : ℝ) * fjcmP024Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP024Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP024Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP024BaseError2570
    (embedPair_magnitude2542 fjcmP024Factor2570)

def fjcmP024Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP024Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP024RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP024Factor2570 fjcmP024Center2570) = fjcmP024Rounded2570 := by
  cbv

theorem fjcmP024RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP024Rounded2570‖ ≤ fjcmP024Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP024Factor2570 fjcmP024Center2570)
  rw [fjcmP024RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP024Factor2570 * embedPair2542 fjcmP024Center2570)
    (embedPair2542 fjcmP024Rounded2570)).trans (add_le_add fjcmP024DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP024Factor2570, fjcmP024Error2570, rounding2542,
      fjcmP024Radius2570]

theorem fjcmP024DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP024Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP024RoundedError2570 (embedPair_magnitude2542
      fjcmP024Rounded2570))
  apply h'.trans
  norm_num [fjcmP024Radius2570, pairMagnitude2542, fjcmP024Rounded2570]

noncomputable def fjcmP025Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((48499811018293309025440887 : ℚ) /
        29514790517935282585600000000))

def fjcmP025Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP025Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-152934154702833) : ℚ) /
        2199023255552))

noncomputable def fjcmP025Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP025BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP025Center2570‖ ≤ fjcmP025Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP025Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP025Input2570]
  have hc : (compactExp2547 fjcmP025Input2570 17).1 = fjcmP025Center2570 := by cbv
  have he : ((compactExp2547 fjcmP025Input2570 17).2 : ℝ) = fjcmP025Error2570 := by
    have hq : (compactExp2547 fjcmP025Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP025Error2570]
  have h := compactExp_error2547 fjcmP025Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP025Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP025Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP025DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP025Factor2570 * embedPair2542 fjcmP025Center2570‖ ≤
        (pairMagnitude2542 fjcmP025Factor2570 : ℝ) * fjcmP025Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP025Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP025Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP025BaseError2570
    (embedPair_magnitude2542 fjcmP025Factor2570)

def fjcmP025Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP025Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP025RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP025Factor2570 fjcmP025Center2570) = fjcmP025Rounded2570 := by
  cbv

theorem fjcmP025RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP025Rounded2570‖ ≤ fjcmP025Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP025Factor2570 fjcmP025Center2570)
  rw [fjcmP025RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP025Factor2570 * embedPair2542 fjcmP025Center2570)
    (embedPair2542 fjcmP025Rounded2570)).trans (add_le_add fjcmP025DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP025Factor2570, fjcmP025Error2570, rounding2542,
      fjcmP025Radius2570]

theorem fjcmP025DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP025Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP025RoundedError2570 (embedPair_magnitude2542
      fjcmP025Rounded2570))
  apply h'.trans
  norm_num [fjcmP025Radius2570, pairMagnitude2542, fjcmP025Rounded2570]

noncomputable def fjcmP026Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((100515438378930241589387643 : ℚ) /
        59029581035870565171200000000))

def fjcmP026Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP026Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-316954711375437) : ℚ) /
        4398046511104))

noncomputable def fjcmP026Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP026BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP026Center2570‖ ≤ fjcmP026Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP026Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP026Input2570]
  have hc : (compactExp2547 fjcmP026Input2570 17).1 = fjcmP026Center2570 := by cbv
  have he : ((compactExp2547 fjcmP026Input2570 17).2 : ℝ) = fjcmP026Error2570 := by
    have hq : (compactExp2547 fjcmP026Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP026Error2570]
  have h := compactExp_error2547 fjcmP026Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP026Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP026Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP026DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP026Factor2570 * embedPair2542 fjcmP026Center2570‖ ≤
        (pairMagnitude2542 fjcmP026Factor2570 : ℝ) * fjcmP026Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP026Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP026Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP026BaseError2570
    (embedPair_magnitude2542 fjcmP026Factor2570)

def fjcmP026Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP026Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP026RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP026Factor2570 fjcmP026Center2570) = fjcmP026Rounded2570 := by
  cbv

theorem fjcmP026RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP026Rounded2570‖ ≤ fjcmP026Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP026Factor2570 fjcmP026Center2570)
  rw [fjcmP026RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP026Factor2570 * embedPair2542 fjcmP026Center2570)
    (embedPair2542 fjcmP026Rounded2570)).trans (add_le_add fjcmP026DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP026Factor2570, fjcmP026Error2570, rounding2542,
      fjcmP026Radius2570]

theorem fjcmP026DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP026Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP026RoundedError2570 (embedPair_magnitude2542
      fjcmP026Rounded2570))
  apply h'.trans
  norm_num [fjcmP026Radius2570, pairMagnitude2542, fjcmP026Rounded2570]

noncomputable def fjcmP027Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((211177751933296260595876053 : ℚ) /
        118059162071741130342400000000))

def fjcmP027Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP027Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-665905501606627) : ℚ) /
        8796093022208))

noncomputable def fjcmP027Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP027BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP027Center2570‖ ≤ fjcmP027Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP027Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP027Input2570]
  have hc : (compactExp2547 fjcmP027Input2570 17).1 = fjcmP027Center2570 := by cbv
  have he : ((compactExp2547 fjcmP027Input2570 17).2 : ℝ) = fjcmP027Error2570 := by
    have hq : (compactExp2547 fjcmP027Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP027Error2570]
  have h := compactExp_error2547 fjcmP027Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP027Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP027Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP027DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP027Factor2570 * embedPair2542 fjcmP027Center2570‖ ≤
        (pairMagnitude2542 fjcmP027Factor2570 : ℝ) * fjcmP027Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP027Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP027Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP027BaseError2570
    (embedPair_magnitude2542 fjcmP027Factor2570)

def fjcmP027Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP027Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP027RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP027Factor2570 fjcmP027Center2570) = fjcmP027Rounded2570 := by
  cbv

theorem fjcmP027RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP027Rounded2570‖ ≤ fjcmP027Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP027Factor2570 fjcmP027Center2570)
  rw [fjcmP027RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP027Factor2570 * embedPair2542 fjcmP027Center2570)
    (embedPair2542 fjcmP027Rounded2570)).trans (add_le_add fjcmP027DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP027Factor2570, fjcmP027Error2570, rounding2542,
      fjcmP027Radius2570]

theorem fjcmP027DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP027Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP027RoundedError2570 (embedPair_magnitude2542
      fjcmP027Rounded2570))
  apply h'.trans
  norm_num [fjcmP027Radius2570, pairMagnitude2542, fjcmP027Rounded2570]

noncomputable def fjcmP028Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((860780157665754287223049953 : ℚ) /
        472236648286964521369600000000))

def fjcmP028Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP028Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2714292757716727) : ℚ) /
        35184372088832))

noncomputable def fjcmP028Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP028BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP028Center2570‖ ≤ fjcmP028Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP028Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP028Input2570]
  have hc : (compactExp2547 fjcmP028Input2570 17).1 = fjcmP028Center2570 := by cbv
  have he : ((compactExp2547 fjcmP028Input2570 17).2 : ℝ) = fjcmP028Error2570 := by
    have hq : (compactExp2547 fjcmP028Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP028Error2570]
  have h := compactExp_error2547 fjcmP028Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP028Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP028Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP028DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP028Factor2570 * embedPair2542 fjcmP028Center2570‖ ≤
        (pairMagnitude2542 fjcmP028Factor2570 : ℝ) * fjcmP028Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP028Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP028Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP028BaseError2570
    (embedPair_magnitude2542 fjcmP028Factor2570)

def fjcmP028Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP028Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP028RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP028Factor2570 fjcmP028Center2570) = fjcmP028Rounded2570 := by
  cbv

theorem fjcmP028RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP028Rounded2570‖ ≤ fjcmP028Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP028Factor2570 fjcmP028Center2570)
  rw [fjcmP028RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP028Factor2570 * embedPair2542 fjcmP028Center2570)
    (embedPair2542 fjcmP028Rounded2570)).trans (add_le_add fjcmP028DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP028Factor2570, fjcmP028Error2570, rounding2542,
      fjcmP028Radius2570]

theorem fjcmP028DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP028Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP028RoundedError2570 (embedPair_magnitude2542
      fjcmP028Rounded2570))
  apply h'.trans
  norm_num [fjcmP028Radius2570, pairMagnitude2542, fjcmP028Rounded2570]

noncomputable def fjcmP029Input2570 : RatPair2542 := ((((-((2312766 * 10^40
        + 5723377961432442750676809523978604904753) * 10^40
        + 220031083640126007330874640054198158089)) : ℚ) /
        ((4174816 * 10^40
        + 9326268133026780540942986273425263844336) * 10^40
        + 8843172633802526297846211569254400000000)),
    ((885244406725664293840781901 : ℚ) /
        472236648286964521369600000000))

def fjcmP029Center2570 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def fjcmP029Factor2570 : RatPair2542 := ((((((54884016694729092840146371801 * 10^40
        + 6502325117949998187793905437630785390186) * 10^40
        + 7585738327713173722577909715215709633189) * 10^40
        + 4416348539866922371824759613847406675999) : ℚ) /
        (((483754603623697104842 * 10^40
        + 7395822809037885219937162061104553505735) * 10^40
        + 1630027390710280251512396664011296520761) * 10^40
        + 1798592002285995256350480772305186648002)),
    (((-2791435723263659) : ℚ) /
        35184372088832))

noncomputable def fjcmP029Error2570 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem fjcmP029BaseError2570 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP029Center2570‖ ≤ fjcmP029Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hz : ‖embedPair2542 fjcmP029Input2570‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, fjcmP029Input2570]
  have hc : (compactExp2547 fjcmP029Input2570 17).1 = fjcmP029Center2570 := by cbv
  have he : ((compactExp2547 fjcmP029Input2570 17).2 : ℝ) = fjcmP029Error2570 := by
    have hq : (compactExp2547 fjcmP029Input2570 17).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [fjcmP029Error2570]
  have h := compactExp_error2547 fjcmP029Input2570 hz 17
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 = Complex.exp ((2 : ℂ)^17 * embedPair2542 fjcmP029Input2570) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [edgeMidpointPosition2548, storedWidth,
      nodeModulation2541, embedPair2542, fjcmP029Input2570, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem fjcmP029DerivativeError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 -
      embedPair2542 fjcmP029Factor2570 * embedPair2542 fjcmP029Center2570‖ ≤
        (pairMagnitude2542 fjcmP029Factor2570 : ℝ) * fjcmP029Error2570 := by
  have hx : |edgeMidpointPosition2548| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [edgeMidpointPosition2548, storedWidth]
  have hf : weightedMultiplier2543 1 (-1/2)
      (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) edgeMidpointPosition2548 =
      embedPair2542 fjcmP029Factor2570 := by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      edgeMidpointPosition2548, storedWidth, nodeModulation2541, embedPair2542,
      fjcmP029Factor2570, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 1 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 1 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ fjcmP029BaseError2570
    (embedPair_magnitude2542 fjcmP029Factor2570)

def fjcmP029Rounded2570 : RatPair2542 :=
  (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

noncomputable def fjcmP029Radius2570 : ℝ := ((2199023255769 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

theorem fjcmP029RoundCompute2570 :
    pairRound2542 (pairMul2542 fjcmP029Factor2570 fjcmP029Center2570) = fjcmP029Rounded2570 := by
  cbv

theorem fjcmP029RoundedError2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548 - embedPair2542 fjcmP029Rounded2570‖ ≤ fjcmP029Radius2570 := by
  have hr := embedPair_round_error2542 (pairMul2542 fjcmP029Factor2570 fjcmP029Center2570)
  rw [fjcmP029RoundCompute2570, embedPair_mul2542] at hr
  have h := (firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP029Factor2570 * embedPair2542 fjcmP029Center2570)
    (embedPair2542 fjcmP029Rounded2570)).trans (add_le_add fjcmP029DerivativeError2570 hr)
  apply h.trans
  norm_num [pairMagnitude2542, fjcmP029Factor2570, fjcmP029Error2570, rounding2542,
      fjcmP029Radius2570]

theorem fjcmP029DerivativeNorm2570 :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548‖ ≤ 1 := by
  have h := firstJetCorrMinus_triangle2570
    (weightedUnitJet2539 1 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      edgeMidpointPosition2548)
    (embedPair2542 fjcmP029Rounded2570) 0
  simp only [sub_zero] at h
  have h' := h.trans (add_le_add fjcmP029RoundedError2570 (embedPair_magnitude2542
      fjcmP029Rounded2570))
  apply h'.trans
  norm_num [fjcmP029Radius2570, pairMagnitude2542, fjcmP029Rounded2570]

noncomputable def fjcmValue2570 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => embedPair2542 fjcmP000Rounded2570
  | 1 => embedPair2542 fjcmP001Rounded2570
  | 2 => embedPair2542 fjcmP002Rounded2570
  | 3 => embedPair2542 fjcmP003Rounded2570
  | 4 => embedPair2542 fjcmP004Rounded2570
  | 5 => embedPair2542 fjcmP005Rounded2570
  | 6 => embedPair2542 fjcmP006Rounded2570
  | 7 => embedPair2542 fjcmP007Rounded2570
  | 8 => embedPair2542 fjcmP008Rounded2570
  | 9 => embedPair2542 fjcmP009Rounded2570
  | 10 => embedPair2542 fjcmP010Rounded2570
  | 11 => embedPair2542 fjcmP011Rounded2570
  | 12 => embedPair2542 fjcmP012Rounded2570
  | 13 => embedPair2542 fjcmP013Rounded2570
  | 14 => embedPair2542 fjcmP014Rounded2570
  | 15 => embedPair2542 fjcmP015Rounded2570
  | 16 => embedPair2542 fjcmP016Rounded2570
  | 17 => embedPair2542 fjcmP017Rounded2570
  | 18 => embedPair2542 fjcmP018Rounded2570
  | 19 => embedPair2542 fjcmP019Rounded2570
  | 20 => embedPair2542 fjcmP020Rounded2570
  | 21 => embedPair2542 fjcmP021Rounded2570
  | 22 => embedPair2542 fjcmP022Rounded2570
  | 23 => embedPair2542 fjcmP023Rounded2570
  | 24 => embedPair2542 fjcmP024Rounded2570
  | 25 => embedPair2542 fjcmP025Rounded2570
  | 26 => embedPair2542 fjcmP026Rounded2570
  | 27 => embedPair2542 fjcmP027Rounded2570
  | 28 => embedPair2542 fjcmP028Rounded2570
  | 29 => embedPair2542 fjcmP029Rounded2570
  | _ => 0

noncomputable def fjcmError2570 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => fjcmP000Radius2570
  | 1 => fjcmP001Radius2570
  | 2 => fjcmP002Radius2570
  | 3 => fjcmP003Radius2570
  | 4 => fjcmP004Radius2570
  | 5 => fjcmP005Radius2570
  | 6 => fjcmP006Radius2570
  | 7 => fjcmP007Radius2570
  | 8 => fjcmP008Radius2570
  | 9 => fjcmP009Radius2570
  | 10 => fjcmP010Radius2570
  | 11 => fjcmP011Radius2570
  | 12 => fjcmP012Radius2570
  | 13 => fjcmP013Radius2570
  | 14 => fjcmP014Radius2570
  | 15 => fjcmP015Radius2570
  | 16 => fjcmP016Radius2570
  | 17 => fjcmP017Radius2570
  | 18 => fjcmP018Radius2570
  | 19 => fjcmP019Radius2570
  | 20 => fjcmP020Radius2570
  | 21 => fjcmP021Radius2570
  | 22 => fjcmP022Radius2570
  | 23 => fjcmP023Radius2570
  | 24 => fjcmP024Radius2570
  | 25 => fjcmP025Radius2570
  | 26 => fjcmP026Radius2570
  | 27 => fjcmP027Radius2570
  | 28 => fjcmP028Radius2570
  | 29 => fjcmP029Radius2570
  | _ => 0

theorem fjcmExpError2570 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548 - fjcmValue2570 i‖
        ≤ fjcmError2570 i := by
  fin_cases i
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP000RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP001RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP002RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP003RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP004RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP005RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP006RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP007RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP008RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP009RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP010RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP011RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP012RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP013RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP014RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP015RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP016RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP017RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP018RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP019RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP020RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP021RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP022RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP023RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP024RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP025RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP026RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP027RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP028RoundedError2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP029RoundedError2570

theorem fjcmUnitNorm2570 (i : Fin 30) :
    ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤ 1 := by
  fin_cases i
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP000DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP001DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP002DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP003DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP004DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP005DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP006DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP007DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP008DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP009DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP010DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP011DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP012DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP013DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP014DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP015DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP016DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP017DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP018DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP019DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP020DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP021DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP022DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP023DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP024DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP025DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP026DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP027DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP028DerivativeNorm2570
  · simpa only [fjcmValue2570, fjcmError2570] using fjcmP029DerivativeNorm2570

noncomputable def fjcmSum2570 : ℂ := ⟨(((-(((429804985775 * 10^40
        + 7822497338081328645299613810230836440224) * 10^40
        + 9333894238232540250048190400089205265870) * 10^40
        + 6053715535570663465118110050444024211907)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888)),
    (((-(((756282981949 * 10^40
        + 4767539950125315149175117012740676343197) * 10^40
        + 1606354447962956256765385070094931734666) * 10^40
        + 3563805821346662272576945514910798216635)) : ℝ) /
        (((1419606883389 * 10^40
        + 8572081041480622812588561594557825924180) * 10^40
        + 8648728554527468610959648031899646689592) * 10^40
        + 5319463985864300012238628776434768805888))⟩

noncomputable def fjcmUpper2570 : ℝ := ((30638167 : ℝ) /
        50000000)

theorem fjcmSum_eq2570 :
    (∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcmValue2570 i) =
      fjcmSum2570 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570, fjcmValue2570,
      fjcmSum2570, embedPair2542, fjcmP000Rounded2570,
      fjcmP001Rounded2570,
      fjcmP002Rounded2570,
      fjcmP003Rounded2570,
      fjcmP004Rounded2570,
      fjcmP005Rounded2570,
      fjcmP006Rounded2570,
      fjcmP007Rounded2570,
      fjcmP008Rounded2570,
      fjcmP009Rounded2570,
      fjcmP010Rounded2570,
      fjcmP011Rounded2570,
      fjcmP012Rounded2570,
      fjcmP013Rounded2570,
      fjcmP014Rounded2570,
      fjcmP015Rounded2570,
      fjcmP016Rounded2570,
      fjcmP017Rounded2570,
      fjcmP018Rounded2570,
      fjcmP019Rounded2570,
      fjcmP020Rounded2570,
      fjcmP021Rounded2570,
      fjcmP022Rounded2570,
      fjcmP023Rounded2570,
      fjcmP024Rounded2570,
      fjcmP025Rounded2570,
      fjcmP026Rounded2570,
      fjcmP027Rounded2570,
      fjcmP028Rounded2570,
      fjcmP029Rounded2570, Complex.mul_re, Complex.mul_im]

theorem fjcmSum_norm2570 :
    ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcmValue2570 i‖ ≤ ((15319081 : ℝ) /
        25000000) := by
  rw [fjcmSum_eq2570]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [fjcmSum2570]

theorem fjcmCharge2570 :
    (∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
      |(correctionCoefficientCenter2570 i).im|) * fjcmError2570 i) ≤ (1 : ℝ)/10^8 := by
  rw [sum30_chain2541]
  norm_num [correctionCoefficientCenter2570, correctionCoefficientBox2570, fjcmError2570,
      fjcmP000Radius2570,
      fjcmP001Radius2570,
      fjcmP002Radius2570,
      fjcmP003Radius2570,
      fjcmP004Radius2570,
      fjcmP005Radius2570,
      fjcmP006Radius2570,
      fjcmP007Radius2570,
      fjcmP008Radius2570,
      fjcmP009Radius2570,
      fjcmP010Radius2570,
      fjcmP011Radius2570,
      fjcmP012Radius2570,
      fjcmP013Radius2570,
      fjcmP014Radius2570,
      fjcmP015Radius2570,
      fjcmP016Radius2570,
      fjcmP017Radius2570,
      fjcmP018Radius2570,
      fjcmP019Radius2570,
      fjcmP020Radius2570,
      fjcmP021Radius2570,
      fjcmP022Radius2570,
      fjcmP023Radius2570,
      fjcmP024Radius2570,
      fjcmP025Radius2570,
      fjcmP026Radius2570,
      fjcmP027Radius2570,
      fjcmP028Radius2570,
      fjcmP029Radius2570]

theorem firstJetCorrMinusUpper_le2570 :
    signedJetUpper2539 1 (-1/2) correctionCoefficientCenter2570 correctionCoefficientError2570
      nodeModulation2541 edgeMidpointPosition2548 ≤ fjcmUpper2570 := by
  have hsum :
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i *
        weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
      ‖∑ i : Fin 30, correctionCoefficientCenter2570 i * fjcmValue2570 i‖ +
        ∑ i : Fin 30, (|(correctionCoefficientCenter2570 i).re| +
          |(correctionCoefficientCenter2570 i).im|) * fjcmError2570 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (fjcmExpError2570 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548‖ ≤
        (1 : ℝ)/10^28 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (fjcmUnitNorm2570 i)
      (by norm_num [correctionCoefficientError2570] : 0 ≤ correctionCoefficientError2570 i)
    simpa [correctionCoefficientError2570] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, correctionCoefficientError2570 i *
      ‖weightedUnitJet2539 1 (-1/2) nodeModulation2541 i edgeMidpointPosition2548‖) ≤
        (30 : ℝ)/10^28 := by simpa using he
  unfold signedJetUpper2539 fjcmUpper2570
  linarith [fjcmSum_norm2570, fjcmCharge2570]

theorem weightedPhysicalFirstJetMidpointMinus_le2570 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (correctionCoefficientBox2570 i).Mem (coefficients i)) :
    ‖iteratedDeriv 1 (weightedPhysical2539 (-1/2) coefficients nodeModulation2541)
        edgeMidpointPosition2548‖ ≤
      fjcmUpper2570 := by
  have h := weightedPhysical2539_jet_le_center_error 1 (-1/2) coefficients
    correctionCoefficientCenter2570 correctionCoefficientError2570 nodeModulation2541
    (fun i => corrError_of_box2570 i (coefficients i) (hbox i))
        edgeMidpointPosition2548
  exact h.trans firstJetCorrMinusUpper_le2570

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.fjcmExpError2570
#print axioms ConnesWeilRH.Dev.fjcmSum_eq2570
#print axioms ConnesWeilRH.Dev.fjcmSum_norm2570
#print axioms ConnesWeilRH.Dev.fjcmCharge2570
#print axioms ConnesWeilRH.Dev.firstJetCorrMinusUpper_le2570
#print axioms ConnesWeilRH.Dev.weightedPhysicalFirstJetMidpointMinus_le2570
