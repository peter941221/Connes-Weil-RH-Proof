import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC02702MinusMidpointPosition2558 : ℝ := (((-63373312967) : ℝ) /
        20480000000)

theorem batchC02702MinusMidpointZero2558 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC02702MinusMidpointP000Center2558 : RatPair2542 := (0, 0)

def batchC02702MinusMidpointP000Factor2558 : RatPair2542 := (0, 0)

noncomputable def batchC02702MinusMidpointP000Error2558 : ℝ := 0

theorem batchC02702MinusMidpointP000Exterior2558 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702MinusMidpointPosition2558 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchC02702MinusMidpointPosition2558| := by
    norm_num [storedWidth, batchC02702MinusMidpointPosition2558]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchC02702MinusMidpointP000BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP000Center2558‖ ≤
          batchC02702MinusMidpointP000Error2558 := by
  rw [batchC02702MinusMidpointP000Exterior2558]
  norm_num [batchC02702MinusMidpointP000Center2558, batchC02702MinusMidpointP000Error2558,
      batchC02702MinusMidpointZero2558]

theorem batchC02702MinusMidpointP000DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP000Factor2558 * embedPair2542
          batchC02702MinusMidpointP000Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP000Factor2558 : ℝ) *
            batchC02702MinusMidpointP000Error2558 := by
  rw [batchC02702MinusMidpointP000Exterior2558]
  norm_num [batchC02702MinusMidpointP000Factor2558, batchC02702MinusMidpointP000Center2558,
      batchC02702MinusMidpointP000Error2558,
      batchC02702MinusMidpointZero2558, pairMagnitude2542]

def batchC02702MinusMidpointP001Input2558 : RatPair2542 := ((((-((5 * 10^40
        + 3504303417434760386999929017667363840150) * 10^40
        + 7065197578866620046686850042385705038593)) : ℚ) /
        ((15 * 10^40
        + 1612652671587019504157663885706632293191) * 10^40
        + 3160232799473938874157180041297920000000)),
    ((350092624093618097711382043 : ℚ) /
        1475739525896764129280000000))

def batchC02702MinusMidpointP001Center2558 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP001Factor2558 : RatPair2542 := ((((((((((18989191560062493993795951 *
    10^40
        + 4110023446308113681406228186210089285650) * 10^40
        + 5145546104278186007948796853889036633024) * 10^40
        + 9994318262738831071905717261550927769034) * 10^40
        + 3264590124986083882860973420331962011067) * 10^40
        + 5237788887152971469072715027918005559957) * 10^40
        + 5593291296174480068491109044834925948274) * 10^40
        + 6997574668016065997376552390862307574455) : ℚ) /
        (((((((54105540788415740489 * 10^40
        + 2931356199167944642473351615169585001077) * 10^40
        + 4020531209492111696220637897379014226619) * 10^40
        + 8585987951334465895033401841877465163177) * 10^40
        + 6896538155263082326530881375021604697491) * 10^40
        + 1324707366372248378856264640668371194827) * 10^40
        + 3601680893010927936822967907978763939041) * 10^40
        + 3203509111834793963542907295176226504704)),
    (((-(((34484229932780166952418172510926885 * 10^40
        + 1281196893040766413904005054393076042164) * 10^40
        + 7458699320790844460018335191266168851674) * 10^40
        + 4324708838486109656860722031105549827811)) : ℚ) /
        (((735564686403689043284200373188 * 10^40
        + 8339608353744565324561421019557184918550) * 10^40
        + 7653492327867554597914600290570847865539) * 10^40
        + 8850399349938203191061304267749822824448)))

noncomputable def batchC02702MinusMidpointP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP001BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP001Center2558‖ ≤
          batchC02702MinusMidpointP001Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP001Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP001Input2558 9 =
      (batchC02702MinusMidpointP001Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP001Input2558 9).2 : ℝ) =
      batchC02702MinusMidpointP001Error2558 := by
    rw [hs]
    norm_num [batchC02702MinusMidpointP001Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP001Input2558 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchC02702MinusMidpointP001Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP001Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP001DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP001Factor2558 * embedPair2542
          batchC02702MinusMidpointP001Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP001Factor2558 : ℝ) *
            batchC02702MinusMidpointP001Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP001Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP001Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP001BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP001Factor2558)

def batchC02702MinusMidpointP002Input2558 : RatPair2542 := ((((-((137 * 10^40
        + 4401424859025447155572798501466478300192) * 10^40
        + 8350590344327610056263434896585587258113)) : ℚ) /
        ((587 * 10^40
        + 6524417550169392565340483963257442419575) * 10^40
        + 9504259261776564753257440330383360000000)),
    (((-350092624093618097711382043) : ℚ) /
        737869762948382064640000000))

def batchC02702MinusMidpointP002Center2558 : RatPair2542 := ((((-7110114361857534115379) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-6333848226778538616101) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def batchC02702MinusMidpointP002Factor2558 : RatPair2542 :=
    ((((((((((150212571334196503579247139667 * 10^40
        + 9163209187502141494710650831796431192536) * 10^40
        + 507281275353351890716371351784708371145) * 10^40
        + 8480797422461879094128014907314443959100) * 10^40
        + 8233542199750861861870781059284504784593) * 10^40
        + 9550249057257351331680471688591620119386) * 10^40
        + 1168047590767020253673727573219690147058) * 10^40
        + 8153234743307686278754595695347158467255) : ℚ) /
        (((((((1953899039546285947456112296 * 10^40
        + 7673736773822626414817620259283524897141) * 10^40
        + 5406164084000020068852107286177159711960) * 10^40
        + 5774149937269982249539177239118060566908) * 10^40
        + 338486896549685979230661870731014688685) * 10^40
        + 2634991169007257980604500840879144170550) * 10^40
        + 2409031153406469105552544536822337101999) * 10^40
        + 7461875231166155716250512669180212281344)),
    (((((14254488774908057854183236164098686845 * 10^40
        + 7686454202669610032154208799384379479906) * 10^40
        + 1812283933368878824080216950354793361405) * 10^40
        + 5898123693701625564178366519142582091491) : ℚ) /
        (((4420293021448109776268191949359753 * 10^40
        + 5113549992090376434982646198381435684752) * 10^40
        + 5951274819406525227415980298653775511236) * 10^40
        + 5879919491600614695843908543954643058688)))

noncomputable def batchC02702MinusMidpointP002Error2558 : ℝ := ((26983739625775590139 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC02702MinusMidpointP002BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP002Center2558‖ ≤
          batchC02702MinusMidpointP002Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP002Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP002Input2558 8 =
      (batchC02702MinusMidpointP002Center2558, ((26983739625775590139 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP002Input2558 8).2 : ℝ) =
      batchC02702MinusMidpointP002Error2558 := by
    rw [hs]
    norm_num [batchC02702MinusMidpointP002Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP002Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02702MinusMidpointP002Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP002Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP002DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP002Factor2558 * embedPair2542
          batchC02702MinusMidpointP002Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP002Factor2558 : ℝ) *
            batchC02702MinusMidpointP002Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP002Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP002Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP002BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP002Factor2558)

def batchC02702MinusMidpointP003Input2558 : RatPair2542 := ((((-((17978 * 10^40
        + 4030212473199722643390514466080803922501) * 10^40
        + 3401130615601267743870503284143371155851)) : ℚ) /
        ((106381 * 10^40
        + 4204507708951028328222454345582026233646) * 10^40
        + 5856611288583869909968241526046720000000)),
    (((-350092624093618097711382043) : ℚ) /
        737869762948382064640000000))

def batchC02702MinusMidpointP003Center2558 : RatPair2542 := ((((-58106249730148233646939962825) :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-207049365502413670126209538747) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC02702MinusMidpointP003Factor2558 : RatPair2542 :=
    ((((-(((((((8587118944655113435641778166071224278805 *
    10^40
        + 1956247831922779801564644081824049360849) * 10^40
        + 3279775206554071554392450597187222205851) * 10^40
        + 1322051819989443530439002334349178225209) * 10^40
        + 9776962249626166654534514418493964732625) * 10^40
        + 7805153701622941450781962493736782262885) * 10^40
        + 9703477961807649639373732825955100562472) * 10^40
        + 7673846094652338694673136827633651078635)) : ℚ) /
        (((((((6295124644922401867701737793286554565 * 10^40
        + 1885132289075211727192079263323616092341) * 10^40
        + 6778707324660183439209865917275146357167) * 10^40
        + 5665363653661441373801092879922095985706) * 10^40
        + 7828938869410890849439849316752321410286) * 10^40
        + 7710801438557010217757118791471979314382) * 10^40
        + 8305941636898111078398656661462376403609) * 10^40
        + 2027102401832096725071479128841112256512)),
    ((((((47 * 10^40
        + 766088324452062752386245071770028169937) * 10^40
        + 4775928125255567376609439561142139949469) * 10^40
        + 3390744022638410271737584635820783002905) * 10^40
        + 905299886267082376939049562892883042017) : ℚ) /
        (((434573054097549927729223802033777098975 * 10^40
        + 1394345955410396784976174923282890881413) * 10^40
        + 99727730632957233443891185163181434929) * 10^40
        + 8559443968361154784223646070495831392256)))

noncomputable def batchC02702MinusMidpointP003Error2558 : ℝ := ((826667988108485078980432455 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP003BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP003Center2558‖ ≤
          batchC02702MinusMidpointP003Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP003Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP003Input2558 8 =
      (batchC02702MinusMidpointP003Center2558, ((826667988108485078980432455 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP003Input2558 8).2 : ℝ) =
      batchC02702MinusMidpointP003Error2558 := by
    rw [hs]
    norm_num [batchC02702MinusMidpointP003Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP003Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02702MinusMidpointP003Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP003Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP003DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP003Factor2558 * embedPair2542
          batchC02702MinusMidpointP003Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP003Factor2558 : ℝ) *
            batchC02702MinusMidpointP003Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP003Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP003Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP003BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP003Factor2558)

def batchC02702MinusMidpointP004Input2558 : RatPair2542 := ((((-((310 * 10^40
        + 5541789657225231998939567259741105294041) * 10^40
        + 3911141731350061375812775950296524758113)) : ℚ) /
        ((2145 * 10^40
        + 2212355329797116134411126239519665640744) * 10^40
        + 3719573893923334673257440330383360000000)),
    ((350092624093618097711382043 : ℚ) /
        737869762948382064640000000))

def batchC02702MinusMidpointP004Center2558 : RatPair2542 := ((((-14371500528035275052607237674543)
    : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((12802452745902397208933690968501 : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)))

def batchC02702MinusMidpointP004Factor2558 : RatPair2542 :=
    ((((-(((((((520953137459391319316568270609668 *
    10^40
        + 8177766096435312342608677990151162372185) * 10^40
        + 5223839380695291050922388836783682811955) * 10^40
        + 8868982267677706476106710379620778744536) * 10^40
        + 322045669563515536820014419078237390539) * 10^40
        + 4332890314498254274849593903886182351359) * 10^40
        + 122436744204620425304394920624164683196) * 10^40
        + 2385790354566109375043750925746591532745)) : ℚ) /
        (((((((346983072916716027729110664619 * 10^40
        + 5814609820823304438878745152390944551467) * 10^40
        + 8412411646822488785787991599803744814168) * 10^40
        + 8530139197747216560438490319076908092229) * 10^40
        + 2637877857882345536289986430818365586179) * 10^40
        + 8233292386238434563323792431491390375825) * 10^40
        + 7899042971785880835675068377876178830775) * 10^40
        + 8685471467824486253546384669180212281344)),
    (((-(((30794268138000640896528291175086887664 * 10^40
        + 1862599272687028699021452156072555110383) * 10^40
        + 6670961177670294107701664920621838220720) * 10^40
        + 645983890529858508719364122658207091491)) : ℚ) /
        (((58905269112085043400175710021598764 * 10^40
        + 9511231959280340772064546122596922387632) * 10^40
        + 8998030819665788276266920027812002454870) * 10^40
        + 1484422618688382546163780543954643058688)))

noncomputable def batchC02702MinusMidpointP004Error2558 : ℝ := ((99782814131998056663875442399 :
    ℝ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC02702MinusMidpointP004BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP004Center2558‖ ≤
          batchC02702MinusMidpointP004Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP004Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP004Input2558 8 =
      (batchC02702MinusMidpointP004Center2558, ((99782814131998056663875442399 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP004Input2558 8).2 : ℝ) =
      batchC02702MinusMidpointP004Error2558 := by
    rw [hs]
    norm_num [batchC02702MinusMidpointP004Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP004Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02702MinusMidpointP004Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP004Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP004DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP004Factor2558 * embedPair2542
          batchC02702MinusMidpointP004Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP004Factor2558 : ℝ) *
            batchC02702MinusMidpointP004Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP004Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP004Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP004BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP004Factor2558)

def batchC02702MinusMidpointP005Center2558 : RatPair2542 := (0, 0)

def batchC02702MinusMidpointP005Factor2558 : RatPair2542 := (0, 0)

noncomputable def batchC02702MinusMidpointP005Error2558 : ℝ := 0

theorem batchC02702MinusMidpointP005Exterior2558 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702MinusMidpointPosition2558 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchC02702MinusMidpointPosition2558| := by
    norm_num [storedWidth, batchC02702MinusMidpointPosition2558]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchC02702MinusMidpointP005BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP005Center2558‖ ≤
          batchC02702MinusMidpointP005Error2558 := by
  rw [batchC02702MinusMidpointP005Exterior2558]
  norm_num [batchC02702MinusMidpointP005Center2558, batchC02702MinusMidpointP005Error2558,
      batchC02702MinusMidpointZero2558]

theorem batchC02702MinusMidpointP005DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP005Factor2558 * embedPair2542
          batchC02702MinusMidpointP005Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP005Factor2558 : ℝ) *
            batchC02702MinusMidpointP005Error2558 := by
  rw [batchC02702MinusMidpointP005Exterior2558]
  norm_num [batchC02702MinusMidpointP005Factor2558, batchC02702MinusMidpointP005Center2558,
      batchC02702MinusMidpointP005Error2558,
      batchC02702MinusMidpointZero2558, pairMagnitude2542]

def batchC02702MinusMidpointP006Input2558 : RatPair2542 :=
    ((((-2691854844418907159374445560845021) : ℚ) /
        4709346362150826203608514560000000),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP006Center2558 : RatPair2542 := (((24536880891660385 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP006Factor2558 : RatPair2542 := (((((386354651 * 10^40
        + 3627162444806068151617718400366460101867) * 10^40
        + 2630864115832552443132576010247138304083) : ℚ) /
        ((78116 * 10^40
        + 7394358677380139464566897660207834597863) * 10^40
        + 4679529841955827692530304040988553216332)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP006Error2558 : ℝ := ((8315075432921 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP006BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP006Center2558‖ ≤
          batchC02702MinusMidpointP006Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP006Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP006Input2558 7 =
      (batchC02702MinusMidpointP006Center2558, ((8315075432921 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP006Input2558 7).2 : ℝ) =
      batchC02702MinusMidpointP006Error2558 := by
    rw [hs]
    norm_num [batchC02702MinusMidpointP006Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP006Input2558 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchC02702MinusMidpointP006Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP006Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP006DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP006Factor2558 * embedPair2542
          batchC02702MinusMidpointP006Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP006Factor2558 : ℝ) *
            batchC02702MinusMidpointP006Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP006Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP006Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP006BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP006Factor2558)

def batchC02702MinusMidpointP007Input2558 : RatPair2542 := ((((-((17978 * 10^40
        + 4030212473199722643390514466080803922501) * 10^40
        + 3401130615601267743870503284143371155851)) : ℚ) /
        ((26595 * 10^40
        + 3551126927237757082055613586395506558411) * 10^40
        + 6464152822145967477492060381511680000000)),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP007Center2558 : RatPair2542 := (((237433748203075576781347204881 : ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP007Factor2558 : RatPair2542 := ((((((((((224591666282 * 10^40
        + 1753516019302676239161188145284295846232) * 10^40
        + 4107340819809505051998843562854630482077) * 10^40
        + 3385414374033169861147424703366092250407) * 10^40
        + 9561063286668591847773932751751009790671) * 10^40
        + 7738697803807255000259536785663690943301) * 10^40
        + 3771705693717138557555585061249495274633) * 10^40
        + 3658513775578184065784552981392057110643) : ℚ) /
        (((((((1271290297 * 10^40
        + 8233821325299327758671555202457894759027) * 10^40
        + 1955891722775494276858055602086357307357) * 10^40
        + 4089628360086498584692754802645933911167) * 10^40
        + 7898953101226941157736021740894338014802) * 10^40
        + 863715018560209640238217085794558788292) * 10^40
        + 9875469667596925425241584238111755641665) * 10^40
        + 5364851134312736263138211925568228442572)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702MinusMidpointP007Error2558 : ℝ := ((16423828134423182786722323 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC02702MinusMidpointP007BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP007Center2558‖ ≤
          batchC02702MinusMidpointP007Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP007Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP007Input2558 6 =
      (batchC02702MinusMidpointP007Center2558, ((16423828134423182786722323 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP007Input2558 6).2 : ℝ) =
      batchC02702MinusMidpointP007Error2558 := by
    rw [hs]
    norm_num [batchC02702MinusMidpointP007Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP007Input2558 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchC02702MinusMidpointP007Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP007Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP007DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP007Factor2558 * embedPair2542
          batchC02702MinusMidpointP007Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP007Factor2558 : ℝ) *
            batchC02702MinusMidpointP007Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP007Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP007Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP007BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP007Factor2558)

def batchC02702MinusMidpointP008Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((252135252400106793034278199 : ℚ) /
        94447329657392904273920000000))

def batchC02702MinusMidpointP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP008Factor2558 : RatPair2542 :=
    ((((((((((564689050064879604274400868986616615916
    * 10^40
        + 5340472421250797764956913862411760615341) * 10^40
        + 2224111105085960174073787200026790789804) * 10^40
        + 3377842183251860869608154554595855843266) * 10^40
        + 4701807794334409816599543638573464390937) * 10^40
        + 6887952501867086864496980955224858024833) * 10^40
        + 5545964217840853096092162346977092582955) * 10^40
        + 8225385456562411369035488777850054246125) : ℚ) /
        (((((((27429040058720438583967452 * 10^40
        + 357122126223786108137892205857761989583) * 10^40
        + 2368286863856365580257718692218957798589) * 10^40
        + 8521163476404502517122319210974143343289) * 10^40
        + 1839050384787997900261372206006490668502) * 10^40
        + 8157487672622911730249642091624930859963) * 10^40
        + 6314841665335889959297733003330078242090) * 10^40
        + 6233657145111234763597481315364449026048)),
    (((-((((1 * 10^40
        + 6623196771255164637072026425755768695513) * 10^40
        + 4669932270289216502431407499019823203341) * 10^40
        + 1303712992513035018081063369044093097585) * 10^40
        + 6536939261621165895042954432607843900483)) : ℚ) /
        (((129588926347391489899444003291257 * 10^40
        + 7538181907809913744878732678738385858823) * 10^40
        + 6106345723266917970420106624842646598815) * 10^40
        + 3122567841486982709738233962998808969216)))

noncomputable def batchC02702MinusMidpointP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP008BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP008Center2558‖ ≤
          batchC02702MinusMidpointP008Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP008Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP008Input2558 14 =
      (batchC02702MinusMidpointP008Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP008Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP008Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP008Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP008Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP008Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP008Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP008DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP008Factor2558 * embedPair2542
          batchC02702MinusMidpointP008Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP008Factor2558 : ℝ) *
            batchC02702MinusMidpointP008Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP008Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP008Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP008BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP008Factor2558)

def batchC02702MinusMidpointP009Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((374991180736622439969330537 : ℚ) /
        94447329657392904273920000000))

def batchC02702MinusMidpointP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP009Factor2558 : RatPair2542 :=
    ((((((((((564689050058238054576255755083463000174
    * 10^40
        + 5947972927175974268141767868320620398587) * 10^40
        + 4082179457602926964697935173896255009571) * 10^40
        + 9818013618890133242580698060927089998763) * 10^40
        + 4123889980619720932878221590326129345970) * 10^40
        + 9430147804610201929478417084387146511597) * 10^40
        + 2671427223987045071012491629425628066594) * 10^40
        + 6046350524778584921205724530632973278509) : ℚ) /
        (((((((27429040058720438583967452 * 10^40
        + 357122126223786108137892205857761989583) * 10^40
        + 2368286863856365580257718692218957798589) * 10^40
        + 8521163476404502517122319210974143343289) * 10^40
        + 1839050384787997900261372206006490668502) * 10^40
        + 8157487672622911730249642091624930859963) * 10^40
        + 6314841665335889959297733003330078242090) * 10^40
        + 6233657145111234763597481315364449026048)),
    (((-((((5 * 10^40
        + 7687114195953143245964835396802044545048) * 10^40
        + 6607608981268587857136904905790246908997) * 10^40
        + 3576136276798308148441049553324513247740) * 10^40
        + 8802209553072264890415633784354238663001)) : ℚ) /
        (((302374161477246809765369341012934 * 10^40
        + 7589091118223132071383709583722900337255) * 10^40
        + 914806687622808597646915457966175397235) * 10^40
        + 7285991630136292989389212580330554261504)))

noncomputable def batchC02702MinusMidpointP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP009BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP009Center2558‖ ≤
          batchC02702MinusMidpointP009Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP009Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP009Input2558 14 =
      (batchC02702MinusMidpointP009Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP009Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP009Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP009Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP009Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP009Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP009Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP009DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP009Factor2558 * embedPair2542
          batchC02702MinusMidpointP009Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP009Factor2558 : ℝ) *
            batchC02702MinusMidpointP009Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP009Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP009Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP009BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP009Factor2558)

def batchC02702MinusMidpointP010Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((223071861160337868686469807 : ℚ) /
        47223664828696452136960000000))

def batchC02702MinusMidpointP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP010Factor2558 : RatPair2542 :=
    ((((((((((141172262513300405185770435721240847150
    * 10^40
        + 3412916766768250283657069008972514150820) * 10^40
        + 4878372497174891742297325131068733554503) * 10^40
        + 1266256539400802572032784813558020271002) * 10^40
        + 6355309986451440291883417492930901876845) * 10^40
        + 6421159073878073623470644702458918109294) * 10^40
        + 1958260558953489554373160683041517443023) * 10^40
        + 6439909063749030036842300011997086365565) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-((((3 * 10^40
        + 4316465532287817281493918760243588918536) * 10^40
        + 8089940877342736206649444408780459084857) * 10^40
        + 3511212976154441698760251914190577177473) * 10^40
        + 9414062192456795478674056091962868027711)) : ℚ) /
        (((151187080738623404882684670506467 * 10^40
        + 3794545559111566035691854791861450168627) * 10^40
        + 5457403343811404298823457728983087698617) * 10^40
        + 8642995815068146494694606290165277130752)))

noncomputable def batchC02702MinusMidpointP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP010BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP010Center2558‖ ≤
          batchC02702MinusMidpointP010Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP010Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP010Input2558 14 =
      (batchC02702MinusMidpointP010Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP010Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP010Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP010Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP010Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP010Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP010Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP010DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP010Factor2558 * embedPair2542
          batchC02702MinusMidpointP010Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP010Factor2558 : ℝ) *
            batchC02702MinusMidpointP010Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP010Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP010Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP010BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP010Factor2558)

def batchC02702MinusMidpointP011Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((246791626082039486171473567 : ℚ) /
        47223664828696452136960000000))

def batchC02702MinusMidpointP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP011Factor2558 : RatPair2542 :=
    ((((((((((141172262512339677556693376855652826380
    * 10^40
        + 2629085159886692745816841088531488488537) * 10^40
        + 7435136587039361804998719343746859202962) * 10^40
        + 8479648082013613866938797828476367334360) * 10^40
        + 3260381138164977402244601940417104694291) * 10^40
        + 9078050523384428278519946885305324602985) * 10^40
        + 434203752815370442004893673325763086767) * 10^40
        + 4410391301220642182479488108022154758685) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-((((11 * 10^40
        + 3896252347322421927507332755803899808849) * 10^40
        + 4590225645849072988431117391526370024551) * 10^40
        + 9871476986423717981874518346351621300425) * 10^40
        + 3901185751018665610743518054845789778573)) : ℚ) /
        (((453561242215870214648054011519402 * 10^40
        + 1383636677334698107075564375584350505882) * 10^40
        + 6372210031434212896470373186949263095853) * 10^40
        + 5928987445204439484083818870495831392256)))

noncomputable def batchC02702MinusMidpointP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP011BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP011Center2558‖ ≤
          batchC02702MinusMidpointP011Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP011Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP011Input2558 14 =
      (batchC02702MinusMidpointP011Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP011Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP011Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP011Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP011Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP011Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP011Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP011DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP011Factor2558 * embedPair2542
          batchC02702MinusMidpointP011Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP011Factor2558 : ℝ) *
            batchC02702MinusMidpointP011Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP011Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP011Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP011BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP011Factor2558)

def batchC02702MinusMidpointP012Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((5427189948381351944663203 : ℚ) /
        944473296573929042739200000))

def batchC02702MinusMidpointP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP012Factor2558 : RatPair2542 :=
    ((((((((((35293065627810583779452079224984170131 *
    10^40
        + 9948553584791663839600814610065254967945) * 10^40
        + 3350858601520067256486501962895732752599) * 10^40
        + 9516648926018156222320348989342638312141) * 10^40
        + 398113300560728432592757284208227110653) * 10^40
        + 2375490559259616845818496301019533123463) * 10^40
        + 8819034336606617776692061758345284883624) * 10^40
        + 1847478971235718252607499172244953839157) : ℚ) /
        (((((((1714315003670027411497965 * 10^40
        + 7522320132888986631758618262866110124348) * 10^40
        + 9523017928991022848766107418263684862411) * 10^40
        + 8657572717275281407320144950685883958955) * 10^40
        + 5739940649049249868766335762875405666781) * 10^40
        + 4259842979538931983140602630726558178747) * 10^40
        + 7269677604083493122456108312708129890130) * 10^40
        + 6639603571569452172724842582210278064128)),
    (((-((((6 * 10^40
        + 2617257897985840065111118600218977014634) * 10^40
        + 5484950118092246054309270322805003027431) * 10^40
        + 7145321466125663516947184297764869832962) * 10^40
        + 3800903340730332766182701014928081701425)) : ℚ) /
        (((226780621107935107324027005759701 * 10^40
        + 691818338667349053537782187792175252941) * 10^40
        + 3186105015717106448235186593474631547926) * 10^40
        + 7964493722602219742041909435247915696128)))

noncomputable def batchC02702MinusMidpointP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP012BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP012Center2558‖ ≤
          batchC02702MinusMidpointP012Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP012Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP012Input2558 14 =
      (batchC02702MinusMidpointP012Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP012Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP012Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP012Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP012Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP012Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP012Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP012DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP012Factor2558 * embedPair2542
          batchC02702MinusMidpointP012Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP012Factor2558 : ℝ) *
            batchC02702MinusMidpointP012Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP012Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP012Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP012BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP012Factor2558)

def batchC02702MinusMidpointP013Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((58749568760405039326952397 : ℚ) /
        9444732965739290427392000000))

def batchC02702MinusMidpointP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP013Factor2558 : RatPair2542 :=
    ((((((((((141172262510151720864938541658582862806
    * 10^40
        + 4469177612259363553160481417180851880871) * 10^40
        + 7271731112967336490186455740068721846050) * 10^40
        + 2257863420297916222450617346466222053488) * 10^40
        + 3182373946446238202076946200600948199028) * 10^40
        + 1821501251655341131464838812047029504716) * 10^40
        + 5367598245071066403140479662029381746906) * 10^40
        + 1373447012697905650212852540169615017053) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-((((4 * 10^40
        + 5188970516413811499168054217463417117880) * 10^40
        + 8962284434789832832602795010041586369890) * 10^40
        + 9727437659668840474297065875252268008692) * 10^40
        + 9609482411139289811544264164390018113905)) : ℚ) /
        (((151187080738623404882684670506467 * 10^40
        + 3794545559111566035691854791861450168627) * 10^40
        + 5457403343811404298823457728983087698617) * 10^40
        + 8642995815068146494694606290165277130752)))

noncomputable def batchC02702MinusMidpointP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP013BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP013Center2558‖ ≤
          batchC02702MinusMidpointP013Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP013Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP013Input2558 14 =
      (batchC02702MinusMidpointP013Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP013Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP013Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP013Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP013Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP013Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP013Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP013DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP013Factor2558 * embedPair2542
          batchC02702MinusMidpointP013Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP013Factor2558 : ℝ) *
            batchC02702MinusMidpointP013Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP013Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP013Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP013BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP013Factor2558)

def batchC02702MinusMidpointP014Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((335231156665698118882125637 : ℚ) /
        47223664828696452136960000000))

def batchC02702MinusMidpointP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP014Factor2558 : RatPair2542 :=
    ((((((((((141172262507902522390352220718441790171
    * 10^40
        + 300772766458692448789497184742656435929) * 10^40
        + 3302913877813862812471974464285947874871) * 10^40
        + 2180721818250352348225771625514696112241) * 10^40
        + 1007881281444997375847164985783515701369) * 10^40
        + 5538628374328275285950128880701659037972) * 10^40
        + 7564258037981695336458816889131181117013) * 10^40
        + 16108380794084960532899416626535122325) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-((((15 * 10^40
        + 4711782650148165033458629658711231392816) * 10^40
        + 8541946399542162136612852522500047280261) * 10^40
        + 9458896534397344387376762881430687564903) * 10^40
        + 8893274401014671223040112686804833335903)) : ℚ) /
        (((453561242215870214648054011519402 * 10^40
        + 1383636677334698107075564375584350505882) * 10^40
        + 6372210031434212896470373186949263095853) * 10^40
        + 5928987445204439484083818870495831392256)))

noncomputable def batchC02702MinusMidpointP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP014BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP014Center2558‖ ≤
          batchC02702MinusMidpointP014Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP014Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP014Input2558 14 =
      (batchC02702MinusMidpointP014Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP014Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP014Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP014Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP014Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP014Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP014Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP014DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP014Factor2558 * embedPair2542
          batchC02702MinusMidpointP014Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP014Factor2558 : ℝ) *
            batchC02702MinusMidpointP014Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP014Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP014Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP014BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP014Factor2558)

def batchC02702MinusMidpointP015Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((364954091521538076540638449 : ℚ) /
        47223664828696452136960000000))

def batchC02702MinusMidpointP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP015Factor2558 : RatPair2542 :=
    ((((((((((141172262506108520697165052390514272539
    * 10^40
        + 1163102540087384318158014502517793973537) * 10^40
        + 6662224904472506820313811240169159223300) * 10^40
        + 4861262892371750939254932188424858176503) * 10^40
        + 5706901344285919705342862431068193151275) * 10^40
        + 2403892158619337215584504306530228580644) * 10^40
        + 3329034766166150680143028163120570792655) * 10^40
        + 1617906534666763649264561316546233399741) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-((((16 * 10^40
        + 8429147953776447821834526495710206005117) * 10^40
        + 1808506228296334337850486999795956310329) * 10^40
        + 8555534159031782956121834507646585586131) * 10^40
        + 5070195774529210133540527894840307748131)) : ℚ) /
        (((453561242215870214648054011519402 * 10^40
        + 1383636677334698107075564375584350505882) * 10^40
        + 6372210031434212896470373186949263095853) * 10^40
        + 5928987445204439484083818870495831392256)))

noncomputable def batchC02702MinusMidpointP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP015BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP015Center2558‖ ≤
          batchC02702MinusMidpointP015Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP015Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP015Input2558 14 =
      (batchC02702MinusMidpointP015Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP015Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP015Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP015Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP015Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP015Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP015Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP015DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP015Factor2558 * embedPair2542
          batchC02702MinusMidpointP015Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP015Factor2558 : ℝ) *
            batchC02702MinusMidpointP015Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP015Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP015Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP015BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP015Factor2558)

def batchC02702MinusMidpointP016Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((193217102700957375093453903 : ℚ) /
        23611832414348226068480000000))

def batchC02702MinusMidpointP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP016Factor2558 : RatPair2542 :=
    ((((((((((35293065626179306437096975233205686756 *
    10^40
        + 2700839732396542441885020968926760874161) * 10^40
        + 3477430990202891823469053126213710843596) * 10^40
        + 3371315263949693831336656699065440678215) * 10^40
        + 4460259549562234521487210626985346644585) * 10^40
        + 8329821746612140821520784292295179516138) * 10^40
        + 6559386244290296414826231126222506891305) * 10^40
        + 6159370302844511078658184950507249375549) : ℚ) /
        (((((((1714315003670027411497965 * 10^40
        + 7522320132888986631758618262866110124348) * 10^40
        + 9523017928991022848766107418263684862411) * 10^40
        + 8657572717275281407320144950685883958955) * 10^40
        + 5739940649049249868766335762875405666781) * 10^40
        + 4259842979538931983140602630726558178747) * 10^40
        + 7269677604083493122456108312708129890130) * 10^40
        + 6639603571569452172724842582210278064128)),
    (((-((((2 * 10^40
        + 9723731225428201242014104992343776889483) * 10^40
        + 6659254483496882937409261181769001457869) * 10^40
        + 9434687857438561039645180445253905069064) * 10^40
        + 647120755130957024760882213007336657119)) : ℚ) /
        (((75593540369311702441342335253233 * 10^40
        + 6897272779555783017845927395930725084313) * 10^40
        + 7728701671905702149411728864491543849308) * 10^40
        + 9321497907534073247347303145082638565376)))

noncomputable def batchC02702MinusMidpointP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP016BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP016Center2558‖ ≤
          batchC02702MinusMidpointP016Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP016Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP016Input2558 14 =
      (batchC02702MinusMidpointP016Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP016Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP016Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP016Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP016Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP016Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP016Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP016DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP016Factor2558 * embedPair2542
          batchC02702MinusMidpointP016Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP016Factor2558 : ℝ) *
            batchC02702MinusMidpointP016Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP016Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP016Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP016BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP016Factor2558)

def batchC02702MinusMidpointP017Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((428157983708866250038028109 : ℚ) /
        47223664828696452136960000000))

def batchC02702MinusMidpointP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP017Factor2558 : RatPair2542 :=
    ((((((((((141172262501787398100659280551205193950
    * 10^40
        + 234216386844654792361770481291474022653) * 10^40
        + 9875230616211065560064086745238705784830) * 10^40
        + 3533661041231121287064274890838782037616) * 10^40
        + 2847017146010904001130669895228794161922) * 10^40
        + 4670053364511725118531902370906897295898) * 10^40
        + 9258680386302920494957032942010364530533) * 10^40
        + 7546485279519889734310892612025112657381) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-(((9409439767777235845124810611073857807011 * 10^40
        + 1141462386095610979796776712490031021656) * 10^40
        + 6802211939877106169382728662832049492841) * 10^40
        + 4269778526185666227425401706158183282651)) : ℚ) /
        (((21598154391231914983240667215209 * 10^40
        + 6256363651301652290813122113123064309803) * 10^40
        + 9351057620544486328403351104140441099802) * 10^40
        + 5520427973581163784956372327166468161536)))

noncomputable def batchC02702MinusMidpointP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP017BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP017Center2558‖ ≤
          batchC02702MinusMidpointP017Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP017Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP017Input2558 14 =
      (batchC02702MinusMidpointP017Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP017Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP017Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP017Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP017Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP017Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP017Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP017DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP017Factor2558 * embedPair2542
          batchC02702MinusMidpointP017Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP017Factor2558 : ℝ) *
            batchC02702MinusMidpointP017Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP017Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP017Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP017BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP017Factor2558)

def batchC02702MinusMidpointP018Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((110983214113089949101875771 : ℚ) /
        11805916207174113034240000000))

def batchC02702MinusMidpointP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP018Factor2558 : RatPair2542 :=
    ((((((((((8823266406287594019940450787081566670 *
    10^40
        + 6119858448081203048066066796214576633087) * 10^40
        + 8702399186164431314360816594986702664747) * 10^40
        + 6431950539828166390973819716219340093791) * 10^40
        + 7474704053355262156724715757079902383058) * 10^40
        + 5143587368483703849954517183479341522702) * 10^40
        + 4940334469406162336933220769920918858290) * 10^40
        + 4846350364159473144912671974907583611541) : ℚ) /
        (((((((428578750917506852874491 * 10^40
        + 4380580033222246657939654565716527531087) * 10^40
        + 2380754482247755712191526854565921215602) * 10^40
        + 9664393179318820351830036237671470989738) * 10^40
        + 8934985162262312467191583940718851416695) * 10^40
        + 3564960744884732995785150657681639544686) * 10^40
        + 9317419401020873280614027078177032472532) * 10^40
        + 6659900892892363043181210645552569516032)),
    (((-((((5 * 10^40
        + 1219615355747026582441362697489455391308) * 10^40
        + 3674877945901046408344033822852306684691) * 10^40
        + 7832192719931112598584807178697673203883) * 10^40
        + 8539655427465254493574217396459379350049)) : ℚ) /
        (((113390310553967553662013502879850 * 10^40
        + 5345909169333674526768891093896087626470) * 10^40
        + 6593052507858553224117593296737315773963) * 10^40
        + 3982246861301109871020954717623957848064)))

noncomputable def batchC02702MinusMidpointP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP018BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP018Center2558‖ ≤
          batchC02702MinusMidpointP018Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP018Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP018Input2558 14 =
      (batchC02702MinusMidpointP018Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP018Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP018Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP018Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP018Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP018Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP018Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP018DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP018Factor2558 * embedPair2542
          batchC02702MinusMidpointP018Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP018Factor2558 : ℝ) *
            batchC02702MinusMidpointP018Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP018Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP018Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP018BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP018Factor2558)

def batchC02702MinusMidpointP019Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((23622117235346621952839097 : ℚ) /
        2361183241434822606848000000))

def batchC02702MinusMidpointP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP019Factor2558 : RatPair2542 :=
    ((((((((((8823266406146839947444166786326714084 *
    10^40
        + 8416027449914414243722269174068522717297) * 10^40
        + 8557307600137263570780211189758945884418) * 10^40
        + 3559171872453683808379790171102630970566) * 10^40
        + 4296377141099947865981809541344202699960) * 10^40
        + 5811124601314758524101779666302538425547) * 10^40
        + 2243711936717553107545135608090345418452) * 10^40
        + 4868326606464400365678336902090477516933) : ℚ) /
        (((((((428578750917506852874491 * 10^40
        + 4380580033222246657939654565716527531087) * 10^40
        + 2380754482247755712191526854565921215602) * 10^40
        + 9664393179318820351830036237671470989738) * 10^40
        + 8934985162262312467191583940718851416695) * 10^40
        + 3564960744884732995785150657681639544686) * 10^40
        + 9317419401020873280614027078177032472532) * 10^40
        + 6659900892892363043181210645552569516032)),
    (((-((((1 * 10^40
        + 8169650974574908743756110413591660204819) * 10^40
        + 920000330533490410650948763377578904415) * 10^40
        + 8746329209210834569476356205897647941066) * 10^40
        + 5315594138165692486862540174542254659405)) : ℚ) /
        (((37796770184655851220671167626616 * 10^40
        + 8448636389777891508922963697965362542156) * 10^40
        + 8864350835952851074705864432245771924654) * 10^40
        + 4660748953767036623673651572541319282688)))

noncomputable def batchC02702MinusMidpointP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP019BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP019Center2558‖ ≤
          batchC02702MinusMidpointP019Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP019Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP019Input2558 14 =
      (batchC02702MinusMidpointP019Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP019Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP019Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP019Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP019Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP019Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP019Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP019DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP019Factor2558 * embedPair2542
          batchC02702MinusMidpointP019Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP019Factor2558 : ℝ) *
            batchC02702MinusMidpointP019Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP019Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP019Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP019BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP019Factor2558)

def batchC02702MinusMidpointP020Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((503444133770802894866222173 : ℚ) /
        47223664828696452136960000000))

def batchC02702MinusMidpointP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP020Factor2558 : RatPair2542 :=
    ((((((((((141172262495741459138715628556800242424
    * 10^40
        + 3473562192753135210506069214129647612598) * 10^40
        + 8583331574209320619776636950077007495373) * 10^40
        + 5818585169243074079269743062092395394776) * 10^40
        + 1745426132839943505377912570440924930206) * 10^40
        + 9168167463852151468082584674179378543119) * 10^40
        + 4948818170840034628190740220679298958757) * 10^40
        + 5506677170605261875965907900317493990405) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-((((3 * 10^40
        + 3191911164115419866573946136795074725103) * 10^40
        + 6372161412521397815391872674595263879205) * 10^40
        + 2849498088247934296562812385941662548531) * 10^40
        + 630254094020520464214259072441943516641)) : ℚ) /
        (((64794463173695744949722001645628 * 10^40
        + 8769090953904956872439366339369192929411) * 10^40
        + 8053172861633458985210053312421323299407) * 10^40
        + 6561283920743491354869116981499404484608)))

noncomputable def batchC02702MinusMidpointP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP020BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP020Center2558‖ ≤
          batchC02702MinusMidpointP020Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP020Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP020Input2558 14 =
      (batchC02702MinusMidpointP020Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP020Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP020Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP020Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP020Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP020Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP020Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP020DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP020Factor2558 * embedPair2542
          batchC02702MinusMidpointP020Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP020Factor2558 : ℝ) *
            batchC02702MinusMidpointP020Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP020Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP020Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP020BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP020Factor2558)

def batchC02702MinusMidpointP021Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((529316338618240150109231229 : ℚ) /
        47223664828696452136960000000))

def batchC02702MinusMidpointP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP021Factor2558 : RatPair2542 :=
    ((((((((((141172262493438155195934774671438554528
    * 10^40
        + 3630110172757526514502642527362126234671) * 10^40
        + 6921859969226717262192725329121026812682) * 10^40
        + 410681744036281565177105912257153811000) * 10^40
        + 988603210629249299927135301338022899246) * 10^40
        + 8907511190505583040581905106924361209081) * 10^40
        + 4308596311869889575993794687526695770300) * 10^40
        + 6524874204836026235452165307404192174661) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-((((8 * 10^40
        + 1427867214563894845012792587605302743657) * 10^40
        + 3459130332406809005592202578406402523047) * 10^40
        + 768867439195241397771198792275379367163) * 10^40
        + 9658288280238858080703399822907969494317)) : ℚ) /
        (((151187080738623404882684670506467 * 10^40
        + 3794545559111566035691854791861450168627) * 10^40
        + 5457403343811404298823457728983087698617) * 10^40
        + 8642995815068146494694606290165277130752)))

noncomputable def batchC02702MinusMidpointP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP021BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP021Center2558‖ ≤
          batchC02702MinusMidpointP021Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP021Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP021Input2558 14 =
      (batchC02702MinusMidpointP021Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP021Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP021Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP021Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP021Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP021Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP021Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP021DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP021Factor2558 * embedPair2542
          batchC02702MinusMidpointP021Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP021Factor2558 : ℝ) *
            batchC02702MinusMidpointP021Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP021Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP021Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP021BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP021Factor2558)

def batchC02702MinusMidpointP022Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((108511737429989693542437311 : ℚ) /
        9444732965739290427392000000))

def batchC02702MinusMidpointP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP022Factor2558 : RatPair2542 :=
    ((((((((((141172262492214589285691423570548654659
    * 10^40
        + 6873210118695204191564358047237886866636) * 10^40
        + 1530855584427543335338062897736094244495) * 10^40
        + 8664627486402214714269555428386931338690) * 10^40
        + 3609200326752752870803587255269921943412) * 10^40
        + 8619176055269618580579074446218644581271) * 10^40
        + 4052736068463099517600765203826701685814) * 10^40
        + 2130027227279118471847568360992710018453) : ℚ) /
        (((((((6857260014680109645991863 * 10^40
        + 89280531555946527034473051464440497395) * 10^40
        + 8092071715964091395064429673054739449647) * 10^40
        + 4630290869101125629280579802743535835822) * 10^40
        + 2959762596196999475065343051501622667125) * 10^40
        + 7039371918155727932562410522906232714990) * 10^40
        + 9078710416333972489824433250832519560522) * 10^40
        + 6558414286277808690899370328841112256512)),
    (((-((((25 * 10^40
        + 395048348683470394099365287839387836493) * 10^40
        + 2905077329750383167380778000010275718185) * 10^40
        + 5237247361696863188145293285437459402462) * 10^40
        + 8393027146086339703946873680175670576545)) : ℚ) /
        (((453561242215870214648054011519402 * 10^40
        + 1383636677334698107075564375584350505882) * 10^40
        + 6372210031434212896470373186949263095853) * 10^40
        + 5928987445204439484083818870495831392256)))

noncomputable def batchC02702MinusMidpointP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP022BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP022Center2558‖ ≤
          batchC02702MinusMidpointP022Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP022Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP022Input2558 14 =
      (batchC02702MinusMidpointP022Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP022Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP022Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP022Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP022Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP022Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP022Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP022DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP022Factor2558 * embedPair2542
          batchC02702MinusMidpointP022Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP022Factor2558 : ℝ) *
            batchC02702MinusMidpointP022Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP022Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP022Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP022BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP022Factor2558)

def batchC02702MinusMidpointP023Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((290369419344105424990310011 : ℚ) /
        23611832414348226068480000000))

def batchC02702MinusMidpointP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP023Factor2558 : RatPair2542 :=
    ((((((((((35293065622129394763634545512326829608 *
    10^40
        + 5396691596542352082167899814560747932755) * 10^40
        + 9953263836143960639312887423843964026597) * 10^40
        + 7349307845293333221803065392312591098342) * 10^40
        + 9370853840712363839306044629361882978370) * 10^40
        + 593452275499475902172887584398153428263) * 10^40
        + 9045456458264255064019418411861114687190) * 10^40
        + 1280275009625478319513080193453785936405) : ℚ) /
        (((((((1714315003670027411497965 * 10^40
        + 7522320132888986631758618262866110124348) * 10^40
        + 9523017928991022848766107418263684862411) * 10^40
        + 8657572717275281407320144950685883958955) * 10^40
        + 5739940649049249868766335762875405666781) * 10^40
        + 4259842979538931983140602630726558178747) * 10^40
        + 7269677604083493122456108312708129890130) * 10^40
        + 6639603571569452172724842582210278064128)),
    (((-((((13 * 10^40
        + 4007742420594894286880519874500375335973) * 10^40
        + 2166858026904195498292620447516063932660) * 10^40
        + 6189016539530657593030026324824881200722) * 10^40
        + 3668954818213532946260087935515620176609)) : ℚ) /
        (((226780621107935107324027005759701 * 10^40
        + 691818338667349053537782187792175252941) * 10^40
        + 3186105015717106448235186593474631547926) * 10^40
        + 7964493722602219742041909435247915696128)))

noncomputable def batchC02702MinusMidpointP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP023BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP023Center2558‖ ≤
          batchC02702MinusMidpointP023Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP023Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP023Input2558 14 =
      (batchC02702MinusMidpointP023Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP023Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP023Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP023Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP023Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP023Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP023Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP023DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP023Factor2558 * embedPair2542
          batchC02702MinusMidpointP023Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP023Factor2558 : ℝ) *
            batchC02702MinusMidpointP023Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP023Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP023Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP023BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP023Factor2558)

def batchC02702MinusMidpointP024Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((299142445099036254066018149 : ℚ) /
        23611832414348226068480000000))

def batchC02702MinusMidpointP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP024Factor2558 : RatPair2542 :=
    ((((((((((35293065621683574138263094220739902841 *
    10^40
        + 2774198920355947622962186374334749617416) * 10^40
        + 4020843086077867696197258748562519781505) * 10^40
        + 8117965650466387642742483539744430368658) * 10^40
        + 3546201715856651106138139746279722170169) * 10^40
        + 9483280541200900778910191621633303751502) * 10^40
        + 8785333637078923815616548652465912363791) * 10^40
        + 8834666554411430465763112692384849919445) : ℚ) /
        (((((((1714315003670027411497965 * 10^40
        + 7522320132888986631758618262866110124348) * 10^40
        + 9523017928991022848766107418263684862411) * 10^40
        + 8657572717275281407320144950685883958955) * 10^40
        + 5739940649049249868766335762875405666781) * 10^40
        + 4259842979538931983140602630726558178747) * 10^40
        + 7269677604083493122456108312708129890130) * 10^40
        + 6639603571569452172724842582210278064128)),
    (((-((((13 * 10^40
        + 8056561949426871065802313770011347703778) * 10^40
        + 8691350488810374691177152007038595086562) * 10^40
        + 4219842820779449275147959991914230964511) * 10^40
        + 1228979147330077891977417525597903242431)) : ℚ) /
        (((226780621107935107324027005759701 * 10^40
        + 691818338667349053537782187792175252941) * 10^40
        + 3186105015717106448235186593474631547926) * 10^40
        + 7964493722602219742041909435247915696128)))

noncomputable def batchC02702MinusMidpointP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP024BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP024Center2558‖ ≤
          batchC02702MinusMidpointP024Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP024Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP024Input2558 14 =
      (batchC02702MinusMidpointP024Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP024Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP024Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP024Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP024Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP024Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP024Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP024DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP024Factor2558 * embedPair2542
          batchC02702MinusMidpointP024Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP024Factor2558 : ℝ) *
            batchC02702MinusMidpointP024Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP024Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP024Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP024BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP024Factor2558)

def batchC02702MinusMidpointP025Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((9691944049326230590535511 : ℚ) /
        737869762948382064640000000))

def batchC02702MinusMidpointP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP025Factor2558 : RatPair2542 :=
    ((((((((((34465884395611179931694637511665877 *
    10^40
        + 9935709142959548606820984503458716729512) * 10^40
        + 2245712753480854761049279469834375368001) * 10^40
        + 2954899450912989362332887738785682290221) * 10^40
        + 5224236290409548615738595426970839067688) * 10^40
        + 2933133202031462664314126593172938562176) * 10^40
        + 8890875380634418124412287898752998014950) * 10^40
        + 1842041356865386894212673405098322394541) : ℚ) /
        (((((((1674135745771511144040 * 10^40
        + 9821799140754774401007576775647330185668) * 10^40
        + 3095237322196280295750748151775648129748) * 10^40
        + 4490876535856714141999336079053404183553) * 10^40
        + 6675527285790087158074967124768433013346) * 10^40
        + 4662363127909705988264785744756568904471) * 10^40
        + 4333271169535237786252398543274129033095) * 10^40
        + 8307265237862860793137426604084189724672)),
    (((-(((30427941899533039054484551373130439996 * 10^40
        + 8248660310749332205422186036168656950457) * 10^40
        + 2228276285791861610569087101293984040491) * 10^40
        + 4483522225378923668603926850436720378647)) : ℚ) /
        (((48210166051856953087590775033 * 10^40
        + 9500572240293084045291993576145363982834) * 10^40
        + 3837837182188715371268757480143170627454) * 10^40
        + 9164108098155315097734277616801710866432)))

noncomputable def batchC02702MinusMidpointP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP025BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP025Center2558‖ ≤
          batchC02702MinusMidpointP025Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP025Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP025Input2558 14 =
      (batchC02702MinusMidpointP025Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP025Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP025Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP025Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP025Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP025Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP025Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP025DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP025Factor2558 * embedPair2542
          batchC02702MinusMidpointP025Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP025Factor2558 : ℝ) *
            batchC02702MinusMidpointP025Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP025Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP025Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP025BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP025Factor2558)

def batchC02702MinusMidpointP026Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((20086470120360724037391579 : ℚ) /
        1475739525896764129280000000))

def batchC02702MinusMidpointP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP026Factor2558 : RatPair2542 :=
    ((((((((((137863537580054233186398236656168141 *
    10^40
        + 7186220248410619001222411553709170736073) * 10^40
        + 7327604927025658414583539962513598150930) * 10^40
        + 7976793462233144964290610579857005345304) * 10^40
        + 895369515805090793483768946827723677010) * 10^40
        + 6111314581587791561971934624210068220700) * 10^40
        + 5002717494297129692297877833097729349145) * 10^40
        + 1938830151270487061095746145254382091605) : ℚ) /
        (((((((6696542983086044576163 * 10^40
        + 9287196563019097604030307102589320742673) * 10^40
        + 2380949288785121183002992607102592518993) * 10^40
        + 7963506143426856567997344316213616734214) * 10^40
        + 6702109143160348632299868499073732053385) * 10^40
        + 8649452511638823953059142979026275617885) * 10^40
        + 7333084678140951145009594173096516132383) * 10^40
        + 3229060951451443172549706416336758898688)),
    (((-(((134348724328450837937251035938972359040 * 10^40
        + 3172854763231164516249325172305281637373) * 10^40
        + 5318933957574046494948026768931407688606) * 10^40
        + 4669590614324682570104233549048550860429)) : ℚ) /
        (((205417229264433974025386780579 * 10^40
        + 4393742589074879845157190020097637839903) * 10^40
        + 265567124108439408014705784957857456112) * 10^40
        + 2525330157357429546867791584633376735232)))

noncomputable def batchC02702MinusMidpointP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP026BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP026Center2558‖ ≤
          batchC02702MinusMidpointP026Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP026Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP026Input2558 14 =
      (batchC02702MinusMidpointP026Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP026Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP026Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP026Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP026Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP026Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP026Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP026DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP026Factor2558 * embedPair2542
          batchC02702MinusMidpointP026Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP026Factor2558 : ℝ) *
            batchC02702MinusMidpointP026Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP026Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP026Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP026BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP026Factor2558)

def batchC02702MinusMidpointP027Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((42200637759763894192232309 : ℚ) /
        2951479051793528258560000000))

def batchC02702MinusMidpointP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP027Factor2558 : RatPair2542 :=
    ((((((((((551454150305818696251812446688544872 *
    10^40
        + 37160370140526062182201825860642905916) * 10^40
        + 7431252051164900264114833471770513463219) * 10^40
        + 2814420835557186323310356363302660153575) * 10^40
        + 64492150574892768329989094102740827476) * 10^40
        + 3807697432257986236466892742972857104476) * 10^40
        + 4297999053971307108490599340327109084098) * 10^40
        + 2770114716802032596492143704139442794741) : ℚ) /
        (((((((26786171932344178304655 * 10^40
        + 7148786252076390416121228410357282970692) * 10^40
        + 9523797155140484732011970428410370075975) * 10^40
        + 1854024573707426271989377264854466936858) * 10^40
        + 6808436572641394529199473996294928213543) * 10^40
        + 4597810046555295812236571916105102471542) * 10^40
        + 9332338712563804580038376692386064529533) * 10^40
        + 2916243805805772690198825665347035594752)),
    (((-(((290685404658916770286867690431323115301 * 10^40
        + 4601632329711889844249909164510735035192) * 10^40
        + 2113400567234308063601722261151029375973) * 10^40
        + 6253431071254203013890353677899137923813)) : ℚ) /
        (((423098173708834155455274264477 * 10^40
        + 542335481975125651219286907066776446367) * 10^40
        + 4278332285477084153821334303346034760350) * 10^40
        + 6096948682318287723399331920588149096448)))

noncomputable def batchC02702MinusMidpointP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP027BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP027Center2558‖ ≤
          batchC02702MinusMidpointP027Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP027Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP027Input2558 14 =
      (batchC02702MinusMidpointP027Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP027Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP027Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP027Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP027Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP027Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP027Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP027DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP027Factor2558 * embedPair2542
          batchC02702MinusMidpointP027Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP027Factor2558 : ℝ) *
            batchC02702MinusMidpointP027Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP027Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP027Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP027BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP027Factor2558)

def batchC02702MinusMidpointP028Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((172013724418843644501899009 : ℚ) /
        11805916207174113034240000000))

def batchC02702MinusMidpointP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP028Factor2558 : RatPair2542 :=
    ((((((((((8823266404798757747299834164813174479 *
    10^40
        + 9105463070324798272919135165445600109782) * 10^40
        + 3554643796700374401403782245759017976283) * 10^40
        + 3969336644924616314433122835530817371386) * 10^40
        + 960179327508665985350737460719926183704) * 10^40
        + 336055537307806081168503747610772136843) * 10^40
        + 2273272432805915072783148631074476847765) * 10^40
        + 8329441831540297640581318299903180192861) : ℚ) /
        (((((((428578750917506852874491 * 10^40
        + 4380580033222246657939654565716527531087) * 10^40
        + 2380754482247755712191526854565921215602) * 10^40
        + 9664393179318820351830036237671470989738) * 10^40
        + 8934985162262312467191583940718851416695) * 10^40
        + 3564960744884732995785150657681639544686) * 10^40
        + 9317419401020873280614027078177032472532) * 10^40
        + 6659900892892363043181210645552569516032)),
    (((-((((7 * 10^40
        + 9385669905585180123890697472912150908475) * 10^40
        + 7182972385298468363124635718249522379345) * 10^40
        + 3201677532433766202155008901040016702019) * 10^40
        + 9126641763810048808234869867195446642771)) : ℚ) /
        (((113390310553967553662013502879850 * 10^40
        + 5345909169333674526768891093896087626470) * 10^40
        + 6593052507858553224117593296737315773963) * 10^40
        + 3982246861301109871020954717623957848064)))

noncomputable def batchC02702MinusMidpointP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP028BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP028Center2558‖ ≤
          batchC02702MinusMidpointP028Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP028Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP028Input2558 14 =
      (batchC02702MinusMidpointP028Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP028Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP028Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP028Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP028Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP028Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP028Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP028DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP028Factor2558 * embedPair2542
          batchC02702MinusMidpointP028Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP028Factor2558 : ℝ) *
            batchC02702MinusMidpointP028Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP028Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP028Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP028BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP028Factor2558)

def batchC02702MinusMidpointP029Input2558 : RatPair2542 := ((((-((6166 * 10^40
        + 8522103943384246224185360315693348197780) * 10^40
        + 278778219936927016433873126037902405851)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((176902529717651864464566253 : ℚ) /
        11805916207174113034240000000))

def batchC02702MinusMidpointP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702MinusMidpointP029Factor2558 : RatPair2542 :=
    ((((((((((8823266404651715495405550974754003594 *
    10^40
        + 3102374005381494855827322269852277818721) * 10^40
        + 5589805508195443202103797558441013109999) * 10^40
        + 2010768298193942389752785616217914490892) * 10^40
        + 41134154679457473627209051144239816080) * 10^40
        + 2355147844994628599516587415380925864224) * 10^40
        + 1690449680277217575844315836725152032340) * 10^40
        + 9558901323611030120341151582356955564325) : ℚ) /
        (((((((428578750917506852874491 * 10^40
        + 4380580033222246657939654565716527531087) * 10^40
        + 2380754482247755712191526854565921215602) * 10^40
        + 9664393179318820351830036237671470989738) * 10^40
        + 8934985162262312467191583940718851416695) * 10^40
        + 3564960744884732995785150657681639544686) * 10^40
        + 9317419401020873280614027078177032472532) * 10^40
        + 6659900892892363043181210645552569516032)),
    (((-((((8 * 10^40
        + 1641891523918732312555421384627299725339) * 10^40
        + 3907498574363852304027193093647584051597) * 10^40
        + 4537213876799831697142303806413741974302) * 10^40
        + 145367997828283230210643790748931746007)) : ℚ) /
        (((113390310553967553662013502879850 * 10^40
        + 5345909169333674526768891093896087626470) * 10^40
        + 6593052507858553224117593296737315773963) * 10^40
        + 3982246861301109871020954717623957848064)))

noncomputable def batchC02702MinusMidpointP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702MinusMidpointP029BaseError2558 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP029Center2558‖ ≤
          batchC02702MinusMidpointP029Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702MinusMidpointP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702MinusMidpointP029Input2558]
  have hs : compactExp2547 batchC02702MinusMidpointP029Input2558 14 =
      (batchC02702MinusMidpointP029Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702MinusMidpointP029Input2558 14).2 : ℝ) =
      batchC02702MinusMidpointP029Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702MinusMidpointP029Error2558]
  have h := compactExp_error2547 batchC02702MinusMidpointP029Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC02702MinusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702MinusMidpointP029Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702MinusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702MinusMidpointP029Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702MinusMidpointP029DerivativeError2558 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702MinusMidpointPosition2558 -
      embedPair2542 batchC02702MinusMidpointP029Factor2558 * embedPair2542
          batchC02702MinusMidpointP029Center2558‖ ≤
        (pairMagnitude2542 batchC02702MinusMidpointP029Factor2558 : ℝ) *
            batchC02702MinusMidpointP029Error2558 := by
  have hx : |batchC02702MinusMidpointPosition2558| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02702MinusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC02702MinusMidpointPosition2558 = embedPair2542
          batchC02702MinusMidpointP029Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702MinusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702MinusMidpointP029Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702MinusMidpointP029BaseError2558
    (embedPair_magnitude2542 batchC02702MinusMidpointP029Factor2558)

theorem batchC02702MinusMidpointGrid2558 :
    -stripRadius2303 + ((5405 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC02702MinusMidpointPosition2558 := by
  norm_num [stripRadius2303, batchC02702MinusMidpointPosition2558]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP000DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP001DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP002DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP003DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP004DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP005DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP006DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP007DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP008DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP009DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP010DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP011DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP012DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP013DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP014DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP015DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP016DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP017DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP018DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP019DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP020DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP021DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP022DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP023DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP024DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP025DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP026DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP027DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP028DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointP029DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702MinusMidpointGrid2558
