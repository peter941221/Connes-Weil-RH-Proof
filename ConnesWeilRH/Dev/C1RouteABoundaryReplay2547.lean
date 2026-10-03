import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def boundaryPosition2547 : ℝ := (((-158531586419) : ℝ) /
        51200000000)

def boundaryInput2547 : RatPair2542 := ((((-((385485 * 10^40
        + 7514714974673144428189546195986214107469) * 10^40
        + 9933263207807163531825851601966592293953)) : ℚ) /
        ((695756 * 10^40
        + 6268652885787367200189259750885058137872) * 10^40
        + 2934332971511469361136514419916800000000)),
    ((912951341665564226630614693 : ℚ) /
        472236648286964521369600000000))

def boundaryCenter2547 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def boundaryFactor2547 : RatPair2542 := ((((((((((((((302965006690404118429569397219452 * 10^40
        + 7564029273269060297094803094618650646126) * 10^40
        + 6976014042493413734324646536657550366259) * 10^40
        + 8542012761723082797140732681300427869187) * 10^40
        + 9003832863128160797281142589005113084940) * 10^40
        + 5403857261296289190055981375421093964361) * 10^40
        + 1687388464958740255095830793390375388654) * 10^40
        + 7139155089816736325876310175091600730161) * 10^40
        + 5165576640165795906519767889776422449191) * 10^40
        + 3633631444022224386675356871545118625362) * 10^40
        + 7581088352030558511256347220219659639919) * 10^40
        + 6695110727042485762669615857190087253367) : ℚ) /
        (((((((((((13282448415 * 10^40
        + 3751862906737114075469030278080835751875) * 10^40
        + 2628107237486823411921077444762763908139) * 10^40
        + 5890379944666146121359885013759151515141) * 10^40
        + 9105505754700664169173964362303503055489) * 10^40
        + 5492971875787620267770212498653701654461) * 10^40
        + 9917397580919462582875861542047875023918) * 10^40
        + 8329582070970086591074054577383756385271) * 10^40
        + 9738501248109756999871127555411343358644) * 10^40
        + 8142452279729649629225556601960818840205) * 10^40
        + 7455672210938309794872243781464869251619) * 10^40
        + 6005055907615662265016388383497282125824)),
    (((-((((((((95397560234492498054 * 10^40
        + 559664516503103964465883624296579507786) * 10^40
        + 9576449776811227752067155597825690514103) * 10^40
        + 8634824245431275282617093544521628683647) * 10^40
        + 5826147713755339701220740176640148799364) * 10^40
        + 9209920101260276513417381362551295587948) * 10^40
        + 4384647982920097284998242820787631977912) * 10^40
        + 7568757345322560558519207297282781586301) * 10^40
        + 7292790321774993435831567198892251823179)) : ℚ) /
        ((((((((966 * 10^40
        + 1854664759073824730069108812637219606340) * 10^40
        + 5597687691702706787457206187151880564181) * 10^40
        + 1195422202881051970022012443698912848523) * 10^40
        + 3875083057406769970465767194818051714366) * 10^40
        + 1046594007454693856580563199902554159399) * 10^40
        + 417992587910568601181232896372719981817) * 10^40
        + 627191162563074044093713889668612473962) * 10^40
        + 4350923635082522974021415051787780489216)))

noncomputable def boundaryError2547 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem boundaryBaseError2547 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ boundaryPosition2547 -
      embedPair2542 boundaryCenter2547‖ ≤ boundaryError2547 := by
  have hx : |boundaryPosition2547| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [boundaryPosition2547, storedWidth]
  have hz : ‖embedPair2542 boundaryInput2547‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, boundaryInput2547]
  have hc : (compactExp2547 boundaryInput2547 16).1 = boundaryCenter2547 := by cbv
  have he : ((compactExp2547 boundaryInput2547 16).2 : ℝ) = boundaryError2547 := by
    have hq : (compactExp2547 boundaryInput2547 16).2 =
        ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376)) := by cbv
    rw [hq]
    norm_num [boundaryError2547]
  have h := compactExp_error2547 boundaryInput2547 hz 16
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      boundaryPosition2547 = Complex.exp ((2 : ℂ)^16 * embedPair2542 boundaryInput2547) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [boundaryPosition2547, storedWidth, nodeModulation2541,
      embedPair2542, boundaryInput2547, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem boundaryThirdError2547 :
    ‖weightedUnitJet2539 3 (1/2) nodeModulation2541 ⟨15, by omega⟩ boundaryPosition2547 -
      embedPair2542 boundaryFactor2547 * embedPair2542 boundaryCenter2547‖ ≤
        (pairMagnitude2542 boundaryFactor2547 : ℝ) * boundaryError2547 := by
  have hx : |boundaryPosition2547| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [boundaryPosition2547, storedWidth]
  have hf : weightedMultiplier2543 3 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) boundaryPosition2547 = embedPair2542 boundaryFactor2547 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      boundaryPosition2547, storedWidth, nodeModulation2541, embedPair2542,
      boundaryFactor2547, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 3 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 3 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ boundaryBaseError2547
    (embedPair_magnitude2542 boundaryFactor2547)

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.boundaryBaseError2547
#print axioms ConnesWeilRH.Dev.boundaryThirdError2547
