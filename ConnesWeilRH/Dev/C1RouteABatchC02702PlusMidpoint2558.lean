import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC02702PlusMidpointPosition2558 : ℝ := (((-63373312967) : ℝ) /
        20480000000)

theorem batchC02702PlusMidpointZero2558 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC02702PlusMidpointP000Center2558 : RatPair2542 := (0, 0)

def batchC02702PlusMidpointP000Factor2558 : RatPair2542 := (0, 0)

noncomputable def batchC02702PlusMidpointP000Error2558 : ℝ := 0

theorem batchC02702PlusMidpointP000Exterior2558 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702PlusMidpointPosition2558 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchC02702PlusMidpointPosition2558| := by
    norm_num [storedWidth, batchC02702PlusMidpointPosition2558]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchC02702PlusMidpointP000BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP000Center2558‖ ≤ batchC02702PlusMidpointP000Error2558
          := by
  rw [batchC02702PlusMidpointP000Exterior2558]
  norm_num [batchC02702PlusMidpointP000Center2558, batchC02702PlusMidpointP000Error2558,
      batchC02702PlusMidpointZero2558]

theorem batchC02702PlusMidpointP000DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP000Factor2558 * embedPair2542
          batchC02702PlusMidpointP000Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP000Factor2558 : ℝ) *
            batchC02702PlusMidpointP000Error2558 := by
  rw [batchC02702PlusMidpointP000Exterior2558]
  norm_num [batchC02702PlusMidpointP000Factor2558, batchC02702PlusMidpointP000Center2558,
      batchC02702PlusMidpointP000Error2558,
      batchC02702PlusMidpointZero2558, pairMagnitude2542]

def batchC02702PlusMidpointP001Input2558 : RatPair2542 := ((((-((5 * 10^40
        + 4420612401000429719085702179664251021076) * 10^40
        + 4574594656352623968313149957614294961407)) : ℚ) /
        ((15 * 10^40
        + 1612652671587019504157663885706632293191) * 10^40
        + 3160232799473938874157180041297920000000)),
    ((350092624093618097711382043 : ℚ) /
        1475739525896764129280000000))

def batchC02702PlusMidpointP001Center2558 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP001Factor2558 : RatPair2542 := ((((((((((19053866810755885415984310 *
    10^40
        + 785337640602963520848400915192169788811) * 10^40
        + 7882951559571991561670750321852583857891) * 10^40
        + 4654158297560429888690271483463610950246) * 10^40
        + 6118694835003359148767205292906172793821) * 10^40
        + 605034558301707622586471966863449147592) * 10^40
        + 5766087646153371020618904722282391829322) * 10^40
        + 5762437322576403917376552390862307574455) : ℚ) /
        (((((((54105540788415740489 * 10^40
        + 2931356199167944642473351615169585001077) * 10^40
        + 4020531209492111696220637897379014226619) * 10^40
        + 8585987951334465895033401841877465163177) * 10^40
        + 6896538155263082326530881375021604697491) * 10^40
        + 1324707366372248378856264640668371194827) * 10^40
        + 3601680893010927936822967907978763939041) * 10^40
        + 3203509111834793963542907295176226504704)),
    (((-(((34541975362848887684412341668713145 * 10^40
        + 5726841153829293059810799937604774220777) * 10^40
        + 2817185859137024751296330529357406611070) * 10^40
        + 1005590497974751783139277968894450172189)) : ℚ) /
        (((735564686403689043284200373188 * 10^40
        + 8339608353744565324561421019557184918550) * 10^40
        + 7653492327867554597914600290570847865539) * 10^40
        + 8850399349938203191061304267749822824448)))

noncomputable def batchC02702PlusMidpointP001Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP001BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP001Center2558‖ ≤ batchC02702PlusMidpointP001Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP001Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP001Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP001Input2558 9 =
      (batchC02702PlusMidpointP001Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP001Input2558 9).2 : ℝ) =
      batchC02702PlusMidpointP001Error2558 := by
    rw [hs]
    norm_num [batchC02702PlusMidpointP001Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP001Input2558 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchC02702PlusMidpointP001Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP001Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP001DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP001Factor2558 * embedPair2542
          batchC02702PlusMidpointP001Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP001Factor2558 : ℝ) *
            batchC02702PlusMidpointP001Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP001Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP001Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP001BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP001Factor2558)

def batchC02702PlusMidpointP002Input2558 : RatPair2542 := ((((-((144 * 10^40
        + 5433914840032884354003356799027886996796) * 10^40
        + 1844459684645541158736565103414412741887)) : ℚ) /
        ((587 * 10^40
        + 6524417550169392565340483963257442419575) * 10^40
        + 9504259261776564753257440330383360000000)),
    (((-350092624093618097711382043) : ℚ) /
        737869762948382064640000000))

def batchC02702PlusMidpointP002Center2558 : RatPair2542 := ((((-10065740793234723969) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-573874309005953449777) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC02702PlusMidpointP002Factor2558 : RatPair2542 :=
    ((((((((((312688984322933224629405852785 * 10^40
        + 6488925374669797599156690527831613558736) * 10^40
        + 3274728455474499996339243054366921972533) * 10^40
        + 8892497720497172138628099205126781061637) * 10^40
        + 3944178966048175939934796411030627160842) * 10^40
        + 4392378792839155532366178083442760712700) * 10^40
        + 8123464410166531976654827003989598174990) * 10^40
        + 3437546309150200198754595695347158467255) : ℚ) /
        (((((((1953899039546285947456112296 * 10^40
        + 7673736773822626414817620259283524897141) * 10^40
        + 5406164084000020068852107286177159711960) * 10^40
        + 5774149937269982249539177239118060566908) * 10^40
        + 338486896549685979230661870731014688685) * 10^40
        + 2634991169007257980604500840879144170550) * 10^40
        + 2409031153406469105552544536822337101999) * 10^40
        + 7461875231166155716250512669180212281344)),
    (((((14601503424022411995531813899475286712 * 10^40
        + 8665895499118545619586117964873910415595) * 10^40
        + 2204890085221170918296737076382006882235) * 10^40
        + 8409412004814096675821633480857417908509) : ℚ) /
        (((4420293021448109776268191949359753 * 10^40
        + 5113549992090376434982646198381435684752) * 10^40
        + 5951274819406525227415980298653775511236) * 10^40
        + 5879919491600614695843908543954643058688)))

noncomputable def batchC02702PlusMidpointP002Error2558 : ℝ := ((77330566637103985 : ℝ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))

theorem batchC02702PlusMidpointP002BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP002Center2558‖ ≤ batchC02702PlusMidpointP002Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP002Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP002Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP002Input2558 8 =
      (batchC02702PlusMidpointP002Center2558, ((77330566637103985 : ℚ) /
        (5021681388309344611 * 10^40
        + 686315385661331328818843555712276103168))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP002Input2558 8).2 : ℝ) =
      batchC02702PlusMidpointP002Error2558 := by
    rw [hs]
    norm_num [batchC02702PlusMidpointP002Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP002Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02702PlusMidpointP002Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP002Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP002DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP002Factor2558 * embedPair2542
          batchC02702PlusMidpointP002Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP002Factor2558 : ℝ) *
            batchC02702PlusMidpointP002Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP002Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP002Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP002BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP002Factor2558)

def batchC02702PlusMidpointP003Input2558 : RatPair2542 := ((((-((19264 * 10^40
        + 2884605670675445464725529648201973760886) * 10^40
        + 9009763225338185381129496715856628844149)) : ℚ) /
        ((106381 * 10^40
        + 4204507708951028328222454345582026233646) * 10^40
        + 5856611288583869909968241526046720000000)),
    (((-350092624093618097711382043) : ℚ) /
        737869762948382064640000000))

def batchC02702PlusMidpointP003Center2558 : RatPair2542 := ((((-164521249162533956881112449) : ℚ)
    /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    (((-2344947086343668055140351859) : ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)))

def batchC02702PlusMidpointP003Factor2558 : RatPair2542 :=
    ((((-(((((((2802363921649523910028082497927345292670 *
    10^40
        + 4175839571149808878556603671592136069538) * 10^40
        + 5153097297533142238235527484860063439846) * 10^40
        + 9293297317411747824146702335760402181961) * 10^40
        + 618190433964549956160900096093281407384) * 10^40
        + 3480832224883382753096614750348115535114) * 10^40
        + 6345126000080654688133491426846751411047) * 10^40
        + 9268429252884112898224378942544550359545)) : ℚ) /
        (((((((2098374881640800622567245931095518188 * 10^40
        + 3961710763025070575730693087774538697447) * 10^40
        + 2259569108220061146403288639091715452389) * 10^40
        + 1888454551220480457933697626640698661902) * 10^40
        + 2609646289803630283146616438917440470095) * 10^40
        + 5903600479519003405919039597157326438127) * 10^40
        + 6101980545632703692799552220487458801203) * 10^40
        + 675700800610698908357159709613704085504)),
    ((((((50 * 10^40
        + 4882201249655978697811259824357747954529) * 10^40
        + 1389908054943240254813419532820526571601) * 10^40
        + 6352921849457207196656904323794666580775) * 10^40
        + 4962990161732917623060950437107116957983) : ℚ) /
        (((434573054097549927729223802033777098975 * 10^40
        + 1394345955410396784976174923282890881413) * 10^40
        + 99727730632957233443891185163181434929) * 10^40
        + 8559443968361154784223646070495831392256)))

noncomputable def batchC02702PlusMidpointP003Error2558 : ℝ := ((37905287035463621532289067 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP003BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP003Center2558‖ ≤ batchC02702PlusMidpointP003Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP003Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP003Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP003Input2558 8 =
      (batchC02702PlusMidpointP003Center2558, ((37905287035463621532289067 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP003Input2558 8).2 : ℝ) =
      batchC02702PlusMidpointP003Error2558 := by
    rw [hs]
    norm_num [batchC02702PlusMidpointP003Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP003Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02702PlusMidpointP003Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP003Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP003DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP003Factor2558 * embedPair2542
          batchC02702PlusMidpointP003Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP003Factor2558 : ℝ) *
            batchC02702PlusMidpointP003Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP003Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP003Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP003BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP003Factor2558)

def batchC02702PlusMidpointP004Input2558 : RatPair2542 := ((((-((336 * 10^40
        + 4845410458933347222137519824252218570408) * 10^40
        + 9771872664532489039187224049703475241887)) : ℚ) /
        ((2145 * 10^40
        + 2212355329797116134411126239519665640744) * 10^40
        + 3719573893923334673257440330383360000000)),
    ((350092624093618097711382043 : ℚ) /
        737869762948382064640000000))

def batchC02702PlusMidpointP004Center2558 : RatPair2542 := ((((-651060353801662704330308043849) :
    ℚ) /
        (36537540 * 10^40
        + 9332725729550921208179070754913983135744)),
    ((4639832506294752093136623076087 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC02702PlusMidpointP004Factor2558 : RatPair2542 :=
    ((((-(((((((515984927642293014416340964519131 *
    10^40
        + 346488680287937856846496256804894315517) * 10^40
        + 6604463801549896582752766768709442528041) * 10^40
        + 594202172230487208346942316686156427571) * 10^40
        + 5947364983206930907370898305880247254444) * 10^40
        + 5497062889934961240475354311000597392928) * 10^40
        + 102635895462784432871730913404561187987) * 10^40
        + 6632153119480305855043750925746591532745)) : ℚ) /
        (((((((346983072916716027729110664619 * 10^40
        + 5814609820823304438878745152390944551467) * 10^40
        + 8412411646822488785787991599803744814168) * 10^40
        + 8530139197747216560438490319076908092229) * 10^40
        + 2637877857882345536289986430818365586179) * 10^40
        + 8233292386238434563323792431491390375825) * 10^40
        + 7899042971785880835675068377876178830775) * 10^40
        + 8685471467824486253546384669180212281344)),
    (((-(((35418620232473379037984999863238841689 * 10^40
        + 2551770962862589589869465869005111050130) * 10^40
        + 883691836971875015429917592910881586299) * 10^40
        + 9915354186296314931280635877341792908509)) : ℚ) /
        (((58905269112085043400175710021598764 * 10^40
        + 9511231959280340772064546122596922387632) * 10^40
        + 8998030819665788276266920027812002454870) * 10^40
        + 1484422618688382546163780543954643058688)))

noncomputable def batchC02702PlusMidpointP004Error2558 : ℝ := ((4575351005829847050178480723 : ℝ)
    /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))

theorem batchC02702PlusMidpointP004BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP004Center2558‖ ≤ batchC02702PlusMidpointP004Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP004Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP004Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP004Input2558 8 =
      (batchC02702PlusMidpointP004Center2558, ((4575351005829847050178480723 : ℚ) /
        (40173451106474756888 * 10^40
        + 5490523085290650630550748445698208825344))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP004Input2558 8).2 : ℝ) =
      batchC02702PlusMidpointP004Error2558 := by
    rw [hs]
    norm_num [batchC02702PlusMidpointP004Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP004Input2558 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02702PlusMidpointP004Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP004Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP004DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP004Factor2558 * embedPair2542
          batchC02702PlusMidpointP004Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP004Factor2558 : ℝ) *
            batchC02702PlusMidpointP004Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP004Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP004Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP004BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP004Factor2558)

def batchC02702PlusMidpointP005Center2558 : RatPair2542 := (0, 0)

def batchC02702PlusMidpointP005Factor2558 : RatPair2542 := (0, 0)

noncomputable def batchC02702PlusMidpointP005Error2558 : ℝ := 0

theorem batchC02702PlusMidpointP005Exterior2558 (n : ℕ) :
    weightedUnitJet2539 n (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702PlusMidpointPosition2558 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchC02702PlusMidpointPosition2558| := by
    norm_num [storedWidth, batchC02702PlusMidpointPosition2558]
  exact weightedFamily_outside_zero2543 n (1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchC02702PlusMidpointP005BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP005Center2558‖ ≤ batchC02702PlusMidpointP005Error2558
          := by
  rw [batchC02702PlusMidpointP005Exterior2558]
  norm_num [batchC02702PlusMidpointP005Center2558, batchC02702PlusMidpointP005Error2558,
      batchC02702PlusMidpointZero2558]

theorem batchC02702PlusMidpointP005DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP005Factor2558 * embedPair2542
          batchC02702PlusMidpointP005Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP005Factor2558 : ℝ) *
            batchC02702PlusMidpointP005Error2558 := by
  rw [batchC02702PlusMidpointP005Exterior2558]
  norm_num [batchC02702PlusMidpointP005Factor2558, batchC02702PlusMidpointP005Center2558,
      batchC02702PlusMidpointP005Error2558,
      batchC02702PlusMidpointZero2558, pairMagnitude2542]

def batchC02702PlusMidpointP006Input2558 : RatPair2542 := ((((-2805703294461092840625554439154979)
    : ℚ) /
        4709346362150826203608514560000000),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP006Center2558 : RatPair2542 := (((1111574280176963 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP006Factor2558 : RatPair2542 := (((((397598569 * 10^40
        + 2248029305282856306998763834324638808464) * 10^40
        + 3695850232345361403132576010247138304083) : ℚ) /
        ((78116 * 10^40
        + 7394358677380139464566897660207834597863) * 10^40
        + 4679529841955827692530304040988553216332)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP006Error2558 : ℝ := ((1241436786993 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem batchC02702PlusMidpointP006BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP006Center2558‖ ≤ batchC02702PlusMidpointP006Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP006Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP006Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP006Input2558 7 =
      (batchC02702PlusMidpointP006Center2558, ((1241436786993 : ℚ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP006Input2558 7).2 : ℝ) =
      batchC02702PlusMidpointP006Error2558 := by
    rw [hs]
    norm_num [batchC02702PlusMidpointP006Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP006Input2558 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchC02702PlusMidpointP006Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP006Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP006DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP006Factor2558 * embedPair2542
          batchC02702PlusMidpointP006Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP006Factor2558 : ℝ) *
            batchC02702PlusMidpointP006Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP006Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP006Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP006BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP006Factor2558)

def batchC02702PlusMidpointP007Input2558 : RatPair2542 := ((((-((19264 * 10^40
        + 2884605670675445464725529648201973760886) * 10^40
        + 9009763225338185381129496715856628844149)) : ℚ) /
        ((26595 * 10^40
        + 3551126927237757082055613586395506558411) * 10^40
        + 6464152822145967477492060381511680000000)),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP007Center2558 : RatPair2542 := (((10756267225401715789905685133 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP007Factor2558 : RatPair2542 := ((((((((((86982621897 * 10^40
        + 5945150695698575939207725090414525283784) * 10^40
        + 3588292073946746347004769277655491555176) * 10^40
        + 388467253707938523074570237926180279829) * 10^40
        + 4445070996155514496646057221165654261762) * 10^40
        + 6081163799203706267814012387096758834358) * 10^40
        + 5031132011717089356537153351535306443557) * 10^40
        + 8381303930526061355261517660464019036881) : ℚ) /
        (((((((423763432 * 10^40
        + 6077940441766442586223851734152631586342) * 10^40
        + 3985297240925164758952685200695452435785) * 10^40
        + 8029876120028832861564251600881977970389) * 10^40
        + 2632984367075647052578673913631446004934) * 10^40
        + 287905006186736546746072361931519596097) * 10^40
        + 6625156555865641808413861412703918547221) * 10^40
        + 8454950378104245421046070641856076147524)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02702PlusMidpointP007Error2558 : ℝ := ((1561786486120041945683413 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP007BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP007Center2558‖ ≤ batchC02702PlusMidpointP007Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP007Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP007Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP007Input2558 6 =
      (batchC02702PlusMidpointP007Center2558, ((1561786486120041945683413 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP007Input2558 6).2 : ℝ) =
      batchC02702PlusMidpointP007Error2558 := by
    rw [hs]
    norm_num [batchC02702PlusMidpointP007Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP007Input2558 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchC02702PlusMidpointP007Input2558)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP007Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP007DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP007Factor2558 * embedPair2542
          batchC02702PlusMidpointP007Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP007Factor2558 : ℝ) *
            batchC02702PlusMidpointP007Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP007Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP007Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP007BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP007Factor2558)

def batchC02702PlusMidpointP008Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((252135252400106793034278199 : ℚ) /
        94447329657392904273920000000))

def batchC02702PlusMidpointP008Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP008Factor2558 : RatPair2542 :=
    ((((((((((188229766330232509669972094849773495575
    * 10^40
        + 4579415654554187927166683941347648962376) * 10^40
        + 7034106440534994748507728456716029306276) * 10^40
        + 3075699827239486494717538337460387020376) * 10^40
        + 1769803937212570181561605855048386052131) * 10^40
        + 704069962974981874828027513628736539600) * 10^40
        + 6070586947559459338282776409772025071117) * 10^40
        + 6177554252118558669678496259283351415375) : ℚ) /
        (((((((9143013352906812861322484 * 10^40
        + 119040708741262036045964068619253996527) * 10^40
        + 7456095621285455193419239564072985932863) * 10^40
        + 2840387825468167505707439736991381114429) * 10^40
        + 7279683461595999300087124068668830222834) * 10^40
        + 2719162557540970576749880697208310286654) * 10^40
        + 5438280555111963319765911001110026080696) * 10^40
        + 8744552381703744921199160438454816342016)),
    (((-((((1 * 10^40
        + 6623200434662875302832187420544476646751) * 10^40
        + 6276722003810400909712016307975633086393) * 10^40
        + 5777845510231690976154703003165850251584) * 10^40
        + 9499290406057943224957045567392156099517)) : ℚ) /
        (((129588926347391489899444003291257 * 10^40
        + 7538181907809913744878732678738385858823) * 10^40
        + 6106345723266917970420106624842646598815) * 10^40
        + 3122567841486982709738233962998808969216)))

noncomputable def batchC02702PlusMidpointP008Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP008BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP008Center2558‖ ≤ batchC02702PlusMidpointP008Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP008Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP008Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP008Input2558 14 =
      (batchC02702PlusMidpointP008Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP008Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP008Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP008Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP008Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP008Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP008Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP008DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP008Factor2558 * embedPair2542
          batchC02702PlusMidpointP008Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP008Factor2558 : ℝ) *
            batchC02702PlusMidpointP008Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP008Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP008Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP008BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP008Factor2558)

def batchC02702PlusMidpointP009Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((374991180736622439969330537 : ℚ) /
        94447329657392904273920000000))

def batchC02702PlusMidpointP009Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP009Factor2558 : RatPair2542 :=
    ((((((((((188229766328018659770590390215388956994
    * 10^40
        + 8115249156529246761561635276650602223458) * 10^40
        + 7653462558040650345382444448005850712865) * 10^40
        + 5222423639118910619041719506237465072208) * 10^40
        + 4910497999307673886987831838965941037142) * 10^40
        + 1551468397222686896488506223349499368521) * 10^40
        + 8445741282941523329922886170588203565663) * 10^40
        + 8784542608190616520401908176877657759503) : ℚ) /
        (((((((9143013352906812861322484 * 10^40
        + 119040708741262036045964068619253996527) * 10^40
        + 7456095621285455193419239564072985932863) * 10^40
        + 2840387825468167505707439736991381114429) * 10^40
        + 7279683461595999300087124068668830222834) * 10^40
        + 2719162557540970576749880697208310286654) * 10^40
        + 5438280555111963319765911001110026080696) * 10^40
        + 8744552381703744921199160438454816342016)),
    (((-((((5 * 10^40
        + 7687126908996359875952180805705887100147) * 10^40
        + 3375412492097817404983120816210916082392) * 10^40
        + 7542228797906314497949992609465238567738) * 10^40
        + 6652311261543655749584366215645761336999)) : ℚ) /
        (((302374161477246809765369341012934 * 10^40
        + 7589091118223132071383709583722900337255) * 10^40
        + 914806687622808597646915457966175397235) * 10^40
        + 7285991630136292989389212580330554261504)))

noncomputable def batchC02702PlusMidpointP009Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP009BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP009Center2558‖ ≤ batchC02702PlusMidpointP009Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP009Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP009Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP009Input2558 14 =
      (batchC02702PlusMidpointP009Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP009Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP009Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP009Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP009Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP009Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP009Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP009DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP009Factor2558 * embedPair2542
          batchC02702PlusMidpointP009Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP009Factor2558 : ℝ) *
            batchC02702PlusMidpointP009Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP009Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP009Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP009BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP009Factor2558)

def batchC02702PlusMidpointP010Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((223071861160337868686469807 : ℚ) /
        47223664828696452136960000000))

def batchC02702PlusMidpointP010Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP010Factor2558 : RatPair2542 :=
    ((((((((((47057441581584962123216429870638938284 *
    10^40
        + 2670786800790397262597617833126770239589) * 10^40
        + 2365974850434882586719891557866352612253) * 10^40
        + 909523621339150741889633309334782191822) * 10^40
        + 7169070330259088491301578658191275106069) * 10^40
        + 8409074473547512771155806699624752002595) * 10^40
        + 4208236571720956928020734134542087700207) * 10^40
        + 6338909462899115398947433337332362121855) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-((((3 * 10^40
        + 4316473094924905904888993268207010258824) * 10^40
        + 8977144365720408394920278134359142992628) * 10^40
        + 4667175524337888363850732035745190924056) * 10^40
        + 7890584668188539561325943908037131972289)) : ℚ) /
        (((151187080738623404882684670506467 * 10^40
        + 3794545559111566035691854791861450168627) * 10^40
        + 5457403343811404298823457728983087698617) * 10^40
        + 8642995815068146494694606290165277130752)))

noncomputable def batchC02702PlusMidpointP010Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP010BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP010Center2558‖ ≤ batchC02702PlusMidpointP010Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP010Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP010Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP010Input2558 14 =
      (batchC02702PlusMidpointP010Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP010Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP010Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP010Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP010Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP010Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP010Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP010DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP010Factor2558 * embedPair2542
          batchC02702PlusMidpointP010Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP010Factor2558 : ℝ) *
            batchC02702PlusMidpointP010Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP010Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP010Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP010BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP010Factor2558)

def batchC02702PlusMidpointP011Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((246791626082039486171473567 : ℚ) /
        47223664828696452136960000000))

def batchC02702PlusMidpointP011Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP011Factor2558 : RatPair2542 :=
    ((((((((((47057441581264719580190743582109598027 *
    10^40
        + 5742842931829878083317541859646428352161) * 10^40
        + 6551562880389705940953689628759061161739) * 10^40
        + 6647320802210087840191637647640897879608) * 10^40
        + 6137427380830267528088640140686676045218) * 10^40
        + 5961371623382964322838907427240220833825) * 10^40
        + 7033550969674917223897978464636836248122) * 10^40
        + 2329070208722986114159829369340718252895) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-((((11 * 10^40
        + 3896277447693596419057754856476671927425) * 10^40
        + 974928581748448301555695346088687277615) * 10^40
        + 9836353460979343586239637937046447407973) * 10^40
        + 7859173863266421109256481945154210221427)) : ℚ) /
        (((453561242215870214648054011519402 * 10^40
        + 1383636677334698107075564375584350505882) * 10^40
        + 6372210031434212896470373186949263095853) * 10^40
        + 5928987445204439484083818870495831392256)))

noncomputable def batchC02702PlusMidpointP011Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP011BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP011Center2558‖ ≤ batchC02702PlusMidpointP011Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP011Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP011Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP011Input2558 14 =
      (batchC02702PlusMidpointP011Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP011Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP011Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP011Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP011Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP011Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP011Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP011DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP011Factor2558 * embedPair2542
          batchC02702PlusMidpointP011Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP011Factor2558 : ℝ) *
            batchC02702PlusMidpointP011Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP011Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP011Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP011BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP011Factor2558)

def batchC02702PlusMidpointP012Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((5427189948381351944663203 : ℚ) /
        944473296573929042739200000))

def batchC02702PlusMidpointP012Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP012Factor2558 : RatPair2542 :=
    ((((((((((11764360395224734691807264232551054019 *
    10^40
        + 2032804831230799738544920244222401369977) * 10^40
        + 3801915538350835420317363116176104607721) * 10^40
        + 3294075835724106211909792589318073296085) * 10^40
        + 8062029517214061576032695634872985990331) * 10^40
        + 4025668881983577672772563383374455866028) * 10^40
        + 9661882208552987694704774062830490432674) * 10^40
        + 6663894600824265764202499724081651279719) : ℚ) /
        (((((((571438334556675803832655 * 10^40
        + 2507440044296328877252872754288703374782) * 10^40
        + 9841005976330340949588702472754561620803) * 10^40
        + 9552524239091760469106714983561961319651) * 10^40
        + 8579980216349749956255445254291801888927) * 10^40
        + 1419947659846310661046867543575519392915) * 10^40
        + 9089892534694497707485369437569376630043) * 10^40
        + 5546534523856484057574947527403426021376)),
    (((-((((6 * 10^40
        + 2617271697530449973924419768571651243698) * 10^40
        + 1022126893024382245512059373614225421099) * 10^40
        + 1385273381264499246355218534539991951948) * 10^40
        + 6324284628588579233817298985071918298575)) : ℚ) /
        (((226780621107935107324027005759701 * 10^40
        + 691818338667349053537782187792175252941) * 10^40
        + 3186105015717106448235186593474631547926) * 10^40
        + 7964493722602219742041909435247915696128)))

noncomputable def batchC02702PlusMidpointP012Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP012BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP012Center2558‖ ≤ batchC02702PlusMidpointP012Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP012Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP012Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP012Input2558 14 =
      (batchC02702PlusMidpointP012Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP012Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP012Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP012Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP012Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP012Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP012Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP012DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP012Factor2558 * embedPair2542
          batchC02702PlusMidpointP012Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP012Factor2558 : ℝ) *
            batchC02702PlusMidpointP012Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP012Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP012Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP012BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP012Factor2558)

def batchC02702PlusMidpointP013Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((58749568760405039326952397 : ℚ) /
        9444732965739290427392000000))

def batchC02702PlusMidpointP013Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP013Factor2558 : RatPair2542 :=
    ((((((((((47057441580535400682939131849752943502 *
    10^40
        + 9689540415954101685765421969196216149606) * 10^40
        + 3163761055699030836016268427533015376102) * 10^40
        + 1240059248304855292028910820304182785984) * 10^40
        + 6111424983590687794699421560747957213464) * 10^40
        + 209188532806601940487204736154122467736) * 10^40
        + 2011349133760149210943173794204709134835) * 10^40
        + 1316755445882073936737617513389871672351) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-((((4 * 10^40
        + 5188980475125442293287097360129586442176) * 10^40
        + 2041382688647915363280508104956270564212) * 10^40
        + 6180849086181605301216888224126836931242) * 10^40
        + 6632939211051609388455735835609981886095)) : ℚ) /
        (((151187080738623404882684670506467 * 10^40
        + 3794545559111566035691854791861450168627) * 10^40
        + 5457403343811404298823457728983087698617) * 10^40
        + 8642995815068146494694606290165277130752)))

noncomputable def batchC02702PlusMidpointP013Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP013BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP013Center2558‖ ≤ batchC02702PlusMidpointP013Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP013Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP013Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP013Input2558 14 =
      (batchC02702PlusMidpointP013Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP013Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP013Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP013Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP013Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP013Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP013Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP013DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP013Factor2558 * embedPair2542
          batchC02702PlusMidpointP013Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP013Factor2558 : ℝ) *
            batchC02702PlusMidpointP013Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP013Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP013Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP013BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP013Factor2558)

def batchC02702PlusMidpointP014Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((335231156665698118882125637 : ℚ) /
        47223664828696452136960000000))

def batchC02702PlusMidpointP014Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP014Factor2558 : RatPair2542 :=
    ((((((((((47057441579785667858077024869705919291 *
    10^40
        + 1633405467353877984308427225050151001292) * 10^40
        + 1840821977314539610111441335605424052375) * 10^40
        + 7881012047622334000620628913320340805568) * 10^40
        + 8719927428590274185956161155808813047577) * 10^40
        + 8114897573697579991982301425705665645488) * 10^40
        + 2743569064730358855382619536571975591537) * 10^40
        + 4197642568580800373510966472208845040775) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-((((15 * 10^40
        + 4711816745415476761417434881913982746201) * 10^40
        + 5899825950098511127566228307155124480321) * 10^40
        + 9255782373617519545694709837166522370828) * 10^40
        + 7689558935975106696959887313195166664097)) : ℚ) /
        (((453561242215870214648054011519402 * 10^40
        + 1383636677334698107075564375584350505882) * 10^40
        + 6372210031434212896470373186949263095853) * 10^40
        + 5928987445204439484083818870495831392256)))

noncomputable def batchC02702PlusMidpointP014Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP014BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP014Center2558‖ ≤ batchC02702PlusMidpointP014Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP014Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP014Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP014Input2558 14 =
      (batchC02702PlusMidpointP014Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP014Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP014Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP014Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP014Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP014Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP014Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP014DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP014Factor2558 * embedPair2542
          batchC02702PlusMidpointP014Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP014Factor2558 : ℝ) *
            batchC02702PlusMidpointP014Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP014Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP014Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP014BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP014Factor2558)

def batchC02702PlusMidpointP015Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((364954091521538076540638449 : ℚ) /
        47223664828696452136960000000))

def batchC02702PlusMidpointP015Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP015Factor2558 : RatPair2542 :=
    ((((((((((47057441579187667293681302093730080080 *
    10^40
        + 5254182058563441940764599664308530180494) * 10^40
        + 9627258986200754279392053594233161168518) * 10^40
        + 8774525738996133530963682434290394826989) * 10^40
        + 6952934116203914962454726970903705530879) * 10^40
        + 7069985501794600635193759900981855493045) * 10^40
        + 4665161307458510636610689961235105483418) * 10^40
        + 1398241953205026603088187105515411133247) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-((((16 * 10^40
        + 8429185072066497885364765596670157342671) * 10^40
        + 4494604484266652848099301110953830107754) * 10^40
        + 2717693113040599109602644985878298061297) * 10^40
        + 9379285649609193706459472105159692251869)) : ℚ) /
        (((453561242215870214648054011519402 * 10^40
        + 1383636677334698107075564375584350505882) * 10^40
        + 6372210031434212896470373186949263095853) * 10^40
        + 5928987445204439484083818870495831392256)))

noncomputable def batchC02702PlusMidpointP015Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP015BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP015Center2558‖ ≤ batchC02702PlusMidpointP015Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP015Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP015Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP015Input2558 14 =
      (batchC02702PlusMidpointP015Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP015Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP015Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP015Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP015Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP015Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP015Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP015DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP015Factor2558 * embedPair2542
          batchC02702PlusMidpointP015Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP015Factor2558 : ℝ) *
            batchC02702PlusMidpointP015Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP015Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP015Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP015BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP015Factor2558)

def batchC02702PlusMidpointP016Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((193217102700957375093453903 : ℚ) /
        23611832414348226068480000000))

def batchC02702PlusMidpointP016Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP016Factor2558 : RatPair2542 :=
    ((((((((((11764360394680975577688896235291559560 *
    10^40
        + 6283566880432425939306322363842903338716) * 10^40
        + 510773001245110275978213503948763971386) * 10^40
        + 7912297948367952081581895159225674084777) * 10^40
        + 2749411600214563605664180082465359168308) * 10^40
        + 9343779277767752331339992713799671330253) * 10^40
        + 8908666177780880574082830518789564435235) * 10^40
        + 1434525044693863372886061650169083125183) : ℚ) /
        (((((((571438334556675803832655 * 10^40
        + 2507440044296328877252872754288703374782) * 10^40
        + 9841005976330340949588702472754561620803) * 10^40
        + 9552524239091760469106714983561961319651) * 10^40
        + 8579980216349749956255445254291801888927) * 10^40
        + 1419947659846310661046867543575519392915) * 10^40
        + 9089892534694497707485369437569376630043) * 10^40
        + 5546534523856484057574947527403426021376)),
    (((-((((2 * 10^40
        + 9723737775921927531963356843234639372048) * 10^40
        + 6894050610086715593535693810403212033137) * 10^40
        + 7960367175193083549875403786099772655087) * 10^40
        + 3047522479049999135239117786992663342881)) : ℚ) /
        (((75593540369311702441342335253233 * 10^40
        + 6897272779555783017845927395930725084313) * 10^40
        + 7728701671905702149411728864491543849308) * 10^40
        + 9321497907534073247347303145082638565376)))

noncomputable def batchC02702PlusMidpointP016Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP016BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP016Center2558‖ ≤ batchC02702PlusMidpointP016Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP016Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP016Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP016Input2558 14 =
      (batchC02702PlusMidpointP016Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP016Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP016Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP016Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP016Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP016Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP016Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP016DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP016Factor2558 * embedPair2542
          batchC02702PlusMidpointP016Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP016Factor2558 : ℝ) *
            batchC02702PlusMidpointP016Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP016Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP016Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP016BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP016Factor2558)

def batchC02702PlusMidpointP017Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((428157983708866250038028109 : ℚ) /
        47223664828696452136960000000))

def batchC02702PlusMidpointP017Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP017Factor2558 : RatPair2542 :=
    ((((((((((47057441577747293094846044813960387217 *
    10^40
        + 4944553340815865432165851657233090196867) * 10^40
        + 698260890113607192642145429256343355695) * 10^40
        + 4998658455282590313566796668428369447360) * 10^40
        + 5999639383445576394383996125623905867762) * 10^40
        + 1158705903758729936176225922440745064796) * 10^40
        + 9975043180837433908215358220865036729377) * 10^40
        + 6707768201489401964770297537341704219127) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-(((9409441841422556456787113392267124141194 * 10^40
        + 8299847978351939120990737162722073371420) * 10^40
        + 1645535519742527212876200571210519815503) * 10^40
        + 6403860729926830412574598293841816717349)) : ℚ) /
        (((21598154391231914983240667215209 * 10^40
        + 6256363651301652290813122113123064309803) * 10^40
        + 9351057620544486328403351104140441099802) * 10^40
        + 5520427973581163784956372327166468161536)))

noncomputable def batchC02702PlusMidpointP017Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP017BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP017Center2558‖ ≤ batchC02702PlusMidpointP017Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP017Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP017Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP017Input2558 14 =
      (batchC02702PlusMidpointP017Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP017Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP017Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP017Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP017Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP017Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP017Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP017DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP017Factor2558 * embedPair2542
          batchC02702PlusMidpointP017Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP017Factor2558 : ℝ) *
            batchC02702PlusMidpointP017Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP017Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP017Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP017BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP017Factor2558)

def batchC02702PlusMidpointP018Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((110983214113089949101875771 : ℚ) /
        11805916207174113034240000000))

def batchC02702PlusMidpointP018Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP018Factor2558 : RatPair2542 :=
    ((((((((((2941090098584499697977626385082938217 *
    10^40
        + 3385774558435462297358184442288354639528) * 10^40
        + 1905373729849180355159071147131615977462) * 10^40
        + 8841115061705568998108692303624078495940) * 10^40
        + 2807232622041875410200349387394195032714) * 10^40
        + 5856322130052160964359771881918433380452) * 10^40
        + 7493995847223082887929595292485821820630) * 10^40
        + 1460800523989580968304223991635861203847) : ℚ) /
        (((((((142859583639168950958163 * 10^40
        + 8126860011074082219313218188572175843695) * 10^40
        + 7460251494082585237397175618188640405200) * 10^40
        + 9888131059772940117276678745890490329912) * 10^40
        + 9644995054087437489063861313572950472231) * 10^40
        + 7854986914961577665261716885893879848228) * 10^40
        + 9772473133673624426871342359392344157510) * 10^40
        + 8886633630964121014393736881850856505344)),
    (((-((((5 * 10^40
        + 1219626643487670791278245037563237503411) * 10^40
        + 3889186366584705425776906758186345922127) * 10^40
        + 4874959752359920051961748635483376939049) * 10^40
        + 9986038757827176866425782603540620649951)) : ℚ) /
        (((113390310553967553662013502879850 * 10^40
        + 5345909169333674526768891093896087626470) * 10^40
        + 6593052507858553224117593296737315773963) * 10^40
        + 3982246861301109871020954717623957848064)))

noncomputable def batchC02702PlusMidpointP018Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP018BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP018Center2558‖ ≤ batchC02702PlusMidpointP018Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP018Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP018Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP018Input2558 14 =
      (batchC02702PlusMidpointP018Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP018Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP018Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP018Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP018Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP018Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP018Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP018DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP018Factor2558 * embedPair2542
          batchC02702PlusMidpointP018Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP018Factor2558 : ℝ) *
            batchC02702PlusMidpointP018Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP018Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP018Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP018BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP018Factor2558)

def batchC02702PlusMidpointP019Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((23622117235346621952839097 : ℚ) /
        2361183241434822606848000000))

def batchC02702PlusMidpointP019Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP019Factor2558 : RatPair2542 :=
    ((((((((((2941090098537581673812198384831320688 *
    10^40
        + 7484497559046532695910251901573003334264) * 10^40
        + 8523676534506791107298869345389030384019) * 10^40
        + 7883522172580741470577349121918508788198) * 10^40
        + 5081123651290103979952713982148961805015) * 10^40
        + 2745501207662512522408859376192832348067) * 10^40
        + 6595121669660213144800233571875630674017) * 10^40
        + 4801459271424556708559445634030159172311) : ℚ) /
        (((((((142859583639168950958163 * 10^40
        + 8126860011074082219313218188572175843695) * 10^40
        + 7460251494082585237397175618188640405200) * 10^40
        + 9888131059772940117276678745890490329912) * 10^40
        + 9644995054087437489063861313572950472231) * 10^40
        + 7854986914961577665261716885893879848228) * 10^40
        + 9772473133673624426871342359392344157510) * 10^40
        + 8886633630964121014393736881850856505344)),
    (((-((((1 * 10^40
        + 8169654978789043744783138559479253304578) * 10^40
        + 7928938750145688748248968657591779351550) * 10^40
        + 2944376109065935200459507068517660156083) * 10^40
        + 7228772073214326713137459825457745340595)) : ℚ) /
        (((37796770184655851220671167626616 * 10^40
        + 8448636389777891508922963697965362542156) * 10^40
        + 8864350835952851074705864432245771924654) * 10^40
        + 4660748953767036623673651572541319282688)))

noncomputable def batchC02702PlusMidpointP019Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP019BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP019Center2558‖ ≤ batchC02702PlusMidpointP019Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP019Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP019Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP019Input2558 14 =
      (batchC02702PlusMidpointP019Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP019Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP019Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP019Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP019Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP019Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP019Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP019DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP019Factor2558 * embedPair2542
          batchC02702PlusMidpointP019Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP019Factor2558 : ℝ) *
            batchC02702PlusMidpointP019Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP019Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP019Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP019BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP019Factor2558)

def batchC02702PlusMidpointP020Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((503444133770802894866222173 : ℚ) /
        47223664828696452136960000000))

def batchC02702PlusMidpointP020Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP020Factor2558 : RatPair2542 :=
    ((((((((((47057441575731980107531494149158736708 *
    10^40
        + 9357668609452025571547284568179148060182) * 10^40
        + 267627876113025545879662164202443925876) * 10^40
        + 5760299831286574577635286058846240566413) * 10^40
        + 8965775712388589562466410350694616123856) * 10^40
        + 9324743936872205386026453356864905480537) * 10^40
        + 1871755775683138619293260647088014872118) * 10^40
        + 9361165498517859345321969300105831330135) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-((((3 * 10^40
        + 3191918478924055267938292937792114365348) * 10^40
        + 9994811104379924064306256020312548529607) * 10^40
        + 7773719809224584967298314845532452186198) * 10^40
        + 9516565212325729775785740927558056483359)) : ℚ) /
        (((64794463173695744949722001645628 * 10^40
        + 8769090953904956872439366339369192929411) * 10^40
        + 8053172861633458985210053312421323299407) * 10^40
        + 6561283920743491354869116981499404484608)))

noncomputable def batchC02702PlusMidpointP020Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP020BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP020Center2558‖ ≤ batchC02702PlusMidpointP020Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP020Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP020Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP020Input2558 14 =
      (batchC02702PlusMidpointP020Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP020Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP020Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP020Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP020Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP020Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP020Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP020DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP020Factor2558 * embedPair2542
          batchC02702PlusMidpointP020Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP020Factor2558 : ℝ) *
            batchC02702PlusMidpointP020Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP020Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP020Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP020BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP020Factor2558)

def batchC02702PlusMidpointP021Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((529316338618240150109231229 : ℚ) /
        47223664828696452136960000000))

def batchC02702PlusMidpointP021Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP021Factor2558 : RatPair2542 :=
    ((((((((((47057441574964212126604542854038174076 *
    10^40
        + 9409851269453489339546142339256640934206) * 10^40
        + 3047137341118824426685024957217117031646) * 10^40
        + 624332022884310406271073675567826705155) * 10^40
        + 2046834738318358160649484594326982113536) * 10^40
        + 9237858512423349243526226834446566369191) * 10^40
        + 1658348489359756935227612136037147142633) * 10^40
        + 3033897843261447465150721769134730724887) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-((((8 * 10^40
        + 1427885159576561285168354696985310585541) * 10^40
        + 3023169515060919775173475643944099299273) * 10^40
        + 3128411852876203056931962360184975084762) * 10^40
        + 413930040334704799296600177092030505683)) : ℚ) /
        (((151187080738623404882684670506467 * 10^40
        + 3794545559111566035691854791861450168627) * 10^40
        + 5457403343811404298823457728983087698617) * 10^40
        + 8642995815068146494694606290165277130752)))

noncomputable def batchC02702PlusMidpointP021Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP021BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP021Center2558‖ ≤ batchC02702PlusMidpointP021Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP021Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP021Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP021Input2558 14 =
      (batchC02702PlusMidpointP021Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP021Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP021Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP021Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP021Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP021Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP021Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP021DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP021Factor2558 * embedPair2542
          batchC02702PlusMidpointP021Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP021Factor2558 : ℝ) *
            batchC02702PlusMidpointP021Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP021Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP021Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP021BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP021Factor2558)

def batchC02702PlusMidpointP022Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((108511737429989693542437311 : ℚ) /
        9444732965739290427392000000))

def batchC02702PlusMidpointP022Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP022Factor2558 : RatPair2542 :=
    ((((((((((47057441574556356823190092487074874120 *
    10^40
        + 7157551251432715231900047512548561144861) * 10^40
        + 1250135879519099784400137480088806175584) * 10^40
        + 42313937006288122635223514277752547718) * 10^40
        + 6253700443692859350941635245637615128258) * 10^40
        + 9141746800678027756858616614211327493254) * 10^40
        + 4906395074890826915763268974803815781137) * 10^40
        + 8235615517409144877282522786997570006151) : ℚ) /
        (((((((2285753338226703215330621 * 10^40
        + 29760177185315509011491017154813499131) * 10^40
        + 9364023905321363798354809891018246483215) * 10^40
        + 8210096956367041876426859934247845278607) * 10^40
        + 4319920865398999825021781017167207555708) * 10^40
        + 5679790639385242644187470174302077571663) * 10^40
        + 6359570138777990829941477750277506520174) * 10^40
        + 2186138095425936230299790109613704085504)),
    (((-((((25 * 10^40
        + 395103530557538039543265976702061437224) * 10^40
        + 3123732040528821269438893701875777432398) * 10^40
        + 9270036631587240740760128340295799104575) * 10^40
        + 6111547458704649096053126319824329423455)) : ℚ) /
        (((453561242215870214648054011519402 * 10^40
        + 1383636677334698107075564375584350505882) * 10^40
        + 6372210031434212896470373186949263095853) * 10^40
        + 5928987445204439484083818870495831392256)))

noncomputable def batchC02702PlusMidpointP022Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP022BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP022Center2558‖ ≤ batchC02702PlusMidpointP022Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP022Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP022Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP022Input2558 14 =
      (batchC02702PlusMidpointP022Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP022Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP022Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP022Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP022Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP022Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP022Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP022DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP022Factor2558 * embedPair2542
          batchC02702PlusMidpointP022Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP022Factor2558 : ℝ) *
            batchC02702PlusMidpointP022Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP022Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP022Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP022BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP022Factor2558)

def batchC02702PlusMidpointP023Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((290369419344105424990310011 : ℚ) /
        23611832414348226068480000000))

def batchC02702PlusMidpointP023Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP023Factor2558 : RatPair2542 :=
    ((((((((((11764360393331005019868086328331940511 *
    10^40
        + 3848850835147695819400615312387565691580) * 10^40
        + 9336050616558799881259491603158848365720) * 10^40
        + 5904962142149165211737364723641390891486) * 10^40
        + 4386276363931273378270458083257537946237) * 10^40
        + 98322787396864024890693811167329300962) * 10^40
        + 3070689582438866790480559614002433700529) * 10^40
        + 9808159946954185786504360064484595312135) : ℚ) /
        (((((((571438334556675803832655 * 10^40
        + 2507440044296328877252872754288703374782) * 10^40
        + 9841005976330340949588702472754561620803) * 10^40
        + 9552524239091760469106714983561961319651) * 10^40
        + 8579980216349749956255445254291801888927) * 10^40
        + 1419947659846310661046867543575519392915) * 10^40
        + 9089892534694497707485369437569376630043) * 10^40
        + 5546534523856484057574947527403426021376)),
    (((-((((13 * 10^40
        + 4007771953121256570338706499870617366856) * 10^40
        + 252092563713456363417597726743243068184) * 10^40
        + 2641525101407516815479695121992728575220) * 10^40
        + 1238969902903896813739912064484379823391)) : ℚ) /
        (((226780621107935107324027005759701 * 10^40
        + 691818338667349053537782187792175252941) * 10^40
        + 3186105015717106448235186593474631547926) * 10^40
        + 7964493722602219742041909435247915696128)))

noncomputable def batchC02702PlusMidpointP023Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP023BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP023Center2558‖ ≤ batchC02702PlusMidpointP023Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP023Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP023Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP023Input2558 14 =
      (batchC02702PlusMidpointP023Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP023Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP023Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP023Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP023Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP023Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP023Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP023DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP023Factor2558 * embedPair2542
          batchC02702PlusMidpointP023Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP023Factor2558 : ℝ) *
            batchC02702PlusMidpointP023Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP023Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP023Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP023BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP023Factor2558)

def batchC02702PlusMidpointP024Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((299142445099036254066018149 : ℚ) /
        23611832414348226068480000000))

def batchC02702PlusMidpointP024Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP024Factor2558 : RatPair2542 :=
    ((((((((((11764360393182398144744269231136298255 *
    10^40
        + 6308019943085560999665377498978899586467) * 10^40
        + 7358577033203435566887615378065033617356) * 10^40
        + 6161181410540183352050504106118670648258) * 10^40
        + 2444725655646035800547823122230151010170) * 10^40
        + 3061598875964005650469795156912379408708) * 10^40
        + 6317315308710423041012936360870699592730) * 10^40
        + 5659623795216169835254370897461616639815) : ℚ) /
        (((((((571438334556675803832655 * 10^40
        + 2507440044296328877252872754288703374782) * 10^40
        + 9841005976330340949588702472754561620803) * 10^40
        + 9552524239091760469106714983561961319651) * 10^40
        + 8579980216349749956255445254291801888927) * 10^40
        + 1419947659846310661046867543575519392915) * 10^40
        + 9089892534694497707485369437569376630043) * 10^40
        + 5546534523856484057574947527403426021376)),
    (((-((((13 * 10^40
        + 8056592374229062428387781917829837080159) * 10^40
        + 2581183774328209561549267086480028788761) * 10^40
        + 6539226376265942540498668862774459573286) * 10^40
        + 1359387829804677948022582474402096757569)) : ℚ) /
        (((226780621107935107324027005759701 * 10^40
        + 691818338667349053537782187792175252941) * 10^40
        + 3186105015717106448235186593474631547926) * 10^40
        + 7964493722602219742041909435247915696128)))

noncomputable def batchC02702PlusMidpointP024Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP024BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP024Center2558‖ ≤ batchC02702PlusMidpointP024Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP024Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP024Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP024Input2558 14 =
      (batchC02702PlusMidpointP024Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP024Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP024Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP024Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP024Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP024Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP024Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP024DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP024Factor2558 * embedPair2542
          batchC02702PlusMidpointP024Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP024Factor2558 : ℝ) *
            batchC02702PlusMidpointP024Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP024Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP024Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP024BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP024Factor2558)

def batchC02702PlusMidpointP025Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((9691944049326230590535511 : ℚ) /
        737869762948382064640000000))

def batchC02702PlusMidpointP025Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP025Factor2558 : RatPair2542 :=
    ((((((((((11488633196279123875659186941606396 *
    10^40
        + 8069764330501132327070547551323023398490) * 10^40
        + 3986870035018856677838192631671885728484) * 10^40
        + 3393939653748715908021577497817431720951) * 10^40
        + 4828582661663560950134058283476090474014) * 10^40
        + 6983473279611623985817110945722068008510) * 10^40
        + 3377090820982648601792189149984770883373) * 10^40
        + 4988409685631963951404224468366107464847) : ℚ) /
        (((((((558045248590503714680 * 10^40
        + 3273933046918258133669192258549110061889) * 10^40
        + 4365079107398760098583582717258549376582) * 10^40
        + 8163625511952238047333112026351134727851) * 10^40
        + 2225175761930029052691655708256144337782) * 10^40
        + 1554121042636568662754928581585522968157) * 10^40
        + 1444423723178412595417466181091376344365) * 10^40
        + 2769088412620953597712475534694729908224)),
    (((-(((30427948605220188664177271881341524442 * 10^40
        + 361650246847142737375713411771030272475) * 10^40
        + 9162450622897579761770306828341107227250) * 10^40
        + 8808116043788610411396073149563279621353)) : ℚ) /
        (((48210166051856953087590775033 * 10^40
        + 9500572240293084045291993576145363982834) * 10^40
        + 3837837182188715371268757480143170627454) * 10^40
        + 9164108098155315097734277616801710866432)))

noncomputable def batchC02702PlusMidpointP025Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP025BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP025Center2558‖ ≤ batchC02702PlusMidpointP025Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP025Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP025Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP025Input2558 14 =
      (batchC02702PlusMidpointP025Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP025Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP025Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP025Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP025Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP025Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP025Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP025DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP025Factor2558 * embedPair2542
          batchC02702PlusMidpointP025Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP025Factor2558 : ℝ) *
            batchC02702PlusMidpointP025Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP025Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP025Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP025BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP025Factor2558)

def batchC02702PlusMidpointP026Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((20086470120360724037391579 : ℚ) /
        1475739525896764129280000000))

def batchC02702PlusMidpointP026Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP026Factor2558 : RatPair2542 :=
    ((((((((((45954532784319666655843309969593797 *
    10^40
        + 1426851880862004166261681385250194866636) * 10^40
        + 5395731444442839834814911221079575140245) * 10^40
        + 8961490501188592803739329866174485611945) * 10^40
        + 2647138764709875910712695546885817698144) * 10^40
        + 6060153709600476244840253200061043358038) * 10^40
        + 9988101941183746805384998679300995963275) * 10^40
        + 4810526983797502300365248715084794030535) : ℚ) /
        (((((((2232180994362014858721 * 10^40
        + 3095732187673032534676769034196440247557) * 10^40
        + 7460316429595040394334330869034197506331) * 10^40
        + 2654502047808952189332448105404538911404) * 10^40
        + 8900703047720116210766622833024577351128) * 10^40
        + 6216484170546274651019714326342091872628) * 10^40
        + 5777694892713650381669864724365505377461) * 10^40
        + 1076353650483814390849902138778919632896)),
    (((-(((134348753936122538847574669713719758017 * 10^40
        + 7308219331306691236611309733842411642193) * 10^40
        + 635745736761160866824478214137771261475) * 10^40
        + 2778526563942391989895766450951449139571)) : ℚ) /
        (((205417229264433974025386780579 * 10^40
        + 4393742589074879845157190020097637839903) * 10^40
        + 265567124108439408014705784957857456112) * 10^40
        + 2525330157357429546867791584633376735232)))

noncomputable def batchC02702PlusMidpointP026Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP026BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP026Center2558‖ ≤ batchC02702PlusMidpointP026Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP026Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP026Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP026Input2558 14 =
      (batchC02702PlusMidpointP026Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP026Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP026Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP026Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP026Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP026Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP026Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP026DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP026Factor2558 * embedPair2542
          batchC02702PlusMidpointP026Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP026Factor2558 : ℝ) *
            batchC02702PlusMidpointP026Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP026Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP026Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP026BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP026Factor2558)

def batchC02702PlusMidpointP027Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((42200637759763894192232309 : ℚ) /
        2951479051793528258560000000))

def batchC02702PlusMidpointP027Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP027Factor2558 : RatPair2542 :=
    ((((((((((183818131132479254458779739899665956 *
    10^40
        + 9471500648947366684144244078008766120420) * 10^40
        + 956536558792114874519869424890340847482) * 10^40
        + 2815044333629240037006624145989488705233) * 10^40
        + 9416226421291013507649086623140552832389) * 10^40
        + 7361427873704178308887397548955034839380) * 10^40
        + 8048117456995916667973024053182714415607) * 10^40
        + 7580372639096703985497381234713147598247) : ℚ) /
        (((((((8928723977448059434885 * 10^40
        + 2382928750692130138707076136785760990230) * 10^40
        + 9841265718380161577337323476136790025325) * 10^40
        + 618008191235808757329792421618155645619) * 10^40
        + 5602812190880464843066491332098309404514) * 10^40
        + 4865936682185098604078857305368367490514) * 10^40
        + 3110779570854601526679458897462021509844) * 10^40
        + 4305414601935257563399608555115678531584)),
    (((-(((290685468719949522236012511701840674626 * 10^40
        + 5233823826433902300838040012442871180424) * 10^40
        + 1039408464645177893835102954918218664898) * 10^40
        + 1156184325027837306109646322100862076187)) : ℚ) /
        (((423098173708834155455274264477 * 10^40
        + 542335481975125651219286907066776446367) * 10^40
        + 4278332285477084153821334303346034760350) * 10^40
        + 6096948682318287723399331920588149096448)))

noncomputable def batchC02702PlusMidpointP027Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP027BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP027Center2558‖ ≤ batchC02702PlusMidpointP027Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP027Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP027Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP027Input2558 14 =
      (batchC02702PlusMidpointP027Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP027Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP027Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP027Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP027Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP027Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP027Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP027DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP027Factor2558 * embedPair2542
          batchC02702PlusMidpointP027Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP027Factor2558 : ℝ) *
            batchC02702PlusMidpointP027Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP027Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP027Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP027BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP027Factor2558)

def batchC02702PlusMidpointP028Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((172013724418843644501899009 : ℚ) /
        11805916207174113034240000000))

def batchC02702PlusMidpointP028Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP028Factor2558 : RatPair2542 :=
    ((((((((((2941090098088220940430754177660140820 *
    10^40
        + 4380976099183327372309207232032029131759) * 10^40
        + 6856121933361161384173393030722387747974) * 10^40
        + 8020243763404385639261793343394570921805) * 10^40
        + 635724380093010019742356621940869632929) * 10^40
        + 7587144852993528374764434069962243585166) * 10^40
        + 3271641835023000466546237912870341150455) * 10^40
        + 2621831013116522466860439433301060064287) : ℚ) /
        (((((((142859583639168950958163 * 10^40
        + 8126860011074082219313218188572175843695) * 10^40
        + 7460251494082585237397175618188640405200) * 10^40
        + 9888131059772940117276678745890490329912) * 10^40
        + 9644995054087437489063861313572950472231) * 10^40
        + 7854986914961577665261716885893879848228) * 10^40
        + 9772473133673624426871342359392344157510) * 10^40
        + 8886633630964121014393736881850856505344)),
    (((-((((7 * 10^40
        + 9385687400539926215637091457978697001734) * 10^40
        + 5918671427023693231481113070098989191584) * 10^40
        + 9874599168940500164280885844712353803912) * 10^40
        + 5701417645444924631765130132804553357229)) : ℚ) /
        (((113390310553967553662013502879850 * 10^40
        + 5345909169333674526768891093896087626470) * 10^40
        + 6593052507858553224117593296737315773963) * 10^40
        + 3982246861301109871020954717623957848064)))

noncomputable def batchC02702PlusMidpointP028Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP028BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP028Center2558‖ ≤ batchC02702PlusMidpointP028Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP028Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP028Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP028Input2558 14 =
      (batchC02702PlusMidpointP028Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP028Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP028Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP028Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP028Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP028Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP028Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP028DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP028Factor2558 * embedPair2542
          batchC02702PlusMidpointP028Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP028Factor2558 : ℝ) *
            batchC02702PlusMidpointP028Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP028Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP028Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP028BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP028Factor2558)

def batchC02702PlusMidpointP029Input2558 : RatPair2542 := ((((-((6168 * 10^40
        + 1658881604342127522088790756327708291059) * 10^40
        + 6108163737235603788566126873962097594149)) : ℚ) /
        ((6955 * 10^40
        + 5636605784501699265944151376982344761976) * 10^40
        + 4549328075413419389967457666990080000000)),
    ((176902529717651864464566253 : ℚ) /
        11805916207174113034240000000))

def batchC02702PlusMidpointP029Center2558 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02702PlusMidpointP029Factor2558 : RatPair2542 :=
    ((((((((((2941090098039206856465993114307083858 *
    10^40
        + 5713279744202226233278602933500921701406) * 10^40
        + 867842503859517651073398134949719459213) * 10^40
        + 4034054314494160997701680936956936628307) * 10^40
        + 329375989149940515834513818748974177055) * 10^40
        + 1593508955555802547547128625885628160959) * 10^40
        + 9744034250846767967566626981420566211980) * 10^40
        + 3031650843806766626780383860785651854775) : ℚ) /
        (((((((142859583639168950958163 * 10^40
        + 8126860011074082219313218188572175843695) * 10^40
        + 7460251494082585237397175618188640405200) * 10^40
        + 9888131059772940117276678745890490329912) * 10^40
        + 9644995054087437489063861313572950472231) * 10^40
        + 7854986914961577665261716885893879848228) * 10^40
        + 9772473133673624426871342359392344157510) * 10^40
        + 8886633630964121014393736881850856505344)),
    (((-((((8 * 10^40
        + 1641909516097916477882795795363442256103) * 10^40
        + 9476323729275658515863906958911731688193) * 10^40
        + 3254407971060683599086915336710844555391) * 10^40
        + 7625800149590361249789356209251068253993)) : ℚ) /
        (((113390310553967553662013502879850 * 10^40
        + 5345909169333674526768891093896087626470) * 10^40
        + 6593052507858553224117593296737315773963) * 10^40
        + 3982246861301109871020954717623957848064)))

noncomputable def batchC02702PlusMidpointP029Error2558 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02702PlusMidpointP029BaseError2558 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP029Center2558‖ ≤ batchC02702PlusMidpointP029Error2558
          := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hz : ‖embedPair2542 batchC02702PlusMidpointP029Input2558‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02702PlusMidpointP029Input2558]
  have hs : compactExp2547 batchC02702PlusMidpointP029Input2558 14 =
      (batchC02702PlusMidpointP029Center2558, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02702PlusMidpointP029Input2558 14).2 : ℝ) =
      batchC02702PlusMidpointP029Error2558 :=
      by
    rw [hs]
    norm_num [batchC02702PlusMidpointP029Error2558]
  have h := compactExp_error2547 batchC02702PlusMidpointP029Input2558 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC02702PlusMidpointPosition2558 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02702PlusMidpointP029Input2558) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02702PlusMidpointPosition2558, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02702PlusMidpointP029Input2558, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02702PlusMidpointP029DerivativeError2558 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02702PlusMidpointPosition2558 -
      embedPair2542 batchC02702PlusMidpointP029Factor2558 * embedPair2542
          batchC02702PlusMidpointP029Center2558‖ ≤
        (pairMagnitude2542 batchC02702PlusMidpointP029Factor2558 : ℝ) *
            batchC02702PlusMidpointP029Error2558 := by
  have hx : |batchC02702PlusMidpointPosition2558| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02702PlusMidpointPosition2558, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC02702PlusMidpointPosition2558 = embedPair2542
          batchC02702PlusMidpointP029Factor2558 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02702PlusMidpointPosition2558, storedWidth, nodeModulation2541, embedPair2542,
      batchC02702PlusMidpointP029Factor2558, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02702PlusMidpointP029BaseError2558
    (embedPair_magnitude2542 batchC02702PlusMidpointP029Factor2558)

theorem batchC02702PlusMidpointGrid2558 :
    -stripRadius2303 + ((5405 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC02702PlusMidpointPosition2558 := by
  norm_num [stripRadius2303, batchC02702PlusMidpointPosition2558]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP000DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP001DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP002DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP003DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP004DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP005DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP006DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP007DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP008DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP009DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP010DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP011DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP012DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP013DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP014DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP015DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP016DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP017DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP018DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP019DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP020DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP021DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP022DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP023DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP024DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP025DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP026DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP027DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP028DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointP029DerivativeError2558
#print axioms ConnesWeilRH.Dev.batchC02702PlusMidpointGrid2558
