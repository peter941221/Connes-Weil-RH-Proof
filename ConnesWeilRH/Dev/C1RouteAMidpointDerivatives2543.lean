import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def midpointPosition2543 : ℝ := ((42008576641 : ℝ) /
        102400000000)

def midpointP000Input2543 : RatPair2542 :=
  ((((-((523053 * 10^40
        + 6373990269775483386616395927478469539740) * 10^40
        + 3467492791494473100437977675509109116517)) : ℚ) /
        ((1094483 * 10^40
        + 8971088841897882341136553470713470238364) * 10^40
        + 5086687848056831141691407243673600000000)),
    (((-232067602941064323301960589) : ℚ) /
        922337203685477580800000000))

def midpointP000Center2543 : RatPair2542 :=
  ((((-60961385640231681) : ℚ) /
        1267650600228229401496703205376),
    ((25412767027801613 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP000Error2543 : ℝ := ((39915271971413 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP000Factor2543 : RatPair2542 :=
  ((((-((((((((13342 * 10^40
        + 3015801245854766379814681928439070024363) * 10^40
        + 9481969453714121922486185124452480784473) * 10^40
        + 8126774117899837054232550509875771308316) * 10^40
        + 3869802274026886344162409715301787722651) * 10^40
        + 9980688219716912341212116298554365885440) * 10^40
        + 1012599672666388876349627969454794886688) * 10^40
        + 7683499685351538252911893761812780936222) * 10^40
        + 374817849284337460401540138477252270305)) : ℚ) /
        ((((((((8 * 10^40
        + 6668224935249533460919544345303138030674) * 10^40
        + 1040864574269495071556864116362895858024) * 10^40
        + 8344089389439559804986720050232518065929) * 10^40
        + 5264961046904416599202942648641385387732) * 10^40
        + 3800984390770155565746846183863319357540) * 10^40
        + 3971766905395597511637434602304662648526) * 10^40
        + 7033265009993750901655621536048315026019) * 10^40
        + 645853842836846640432971685570403106816)),
    ((((((798 * 10^40
        + 8357942859094132739276291010903405192330) * 10^40
        + 4235926070655591792666796670420683457276) * 10^40
        + 7088162744952566242753921231657127556569) * 10^40
        + 9373129204606370426780197109076891200497) : ℚ) /
        ((((2 * 10^40
        + 9439467545329268991608846459933422578249) * 10^40
        + 5881566353765362090670591612667141215125) * 10^40
        + 1803167123134690024236371132986406089075) * 10^40
        + 897276854462665725770608362840072912896)))

theorem midpointP000BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP000Center2543‖ ≤ midpointP000Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP000Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP000Input2543]
  have hc : (compactExp2542 midpointP000Input2543 6).1 = midpointP000Center2543 := by cbv
  have he : ((compactExp2542 midpointP000Input2543 6).2 : ℝ) = midpointP000Error2543 := by
    have hq : (compactExp2542 midpointP000Input2543 6).2 =
        ((39915271971413 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP000Error2543]
  have h := compactExp_error2542 midpointP000Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨0, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP000Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP000Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP000DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨0, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP000Factor2543 * embedPair2542 midpointP000Center2543‖ ≤
      (pairMagnitude2542 midpointP000Factor2543 : ℝ) * midpointP000Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨0, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨0, by omega⟩)
      (storedWidth ⟨0, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP000Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP000Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨0, by omega⟩) (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP000BaseError2543
    (embedPair_magnitude2542 midpointP000Factor2543)

def midpointP001Input2543 : RatPair2542 :=
  ((((-((669 * 10^40
        + 9864486927565694333713260186101151054464) * 10^40
        + 2408107246054573974877406189332442339231)) : ℚ) /
        ((1417 * 10^40
        + 8705469963287017585067741186120308289333) * 10^40
        + 9924713592444639678570574761164800000000)),
    (((-232067602941064323301960589) : ℚ) /
        922337203685477580800000000))

def midpointP001Center2543 : RatPair2542 :=
  ((((-42980958787528105) : ℚ) /
        633825300114114700748351602688),
    ((8958663593582673 : ℚ) /
        316912650057057350374175801344))

noncomputable def midpointP001Error2543 : ℝ := ((27549026282477 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def midpointP001Factor2543 : RatPair2542 :=
  ((((-(((((((41864250200061396719222641700632 * 10^40
        + 3972874017824764861808425356059465038508) * 10^40
        + 4599857468099679542935789166608372758196) * 10^40
        + 3641995040246581438005122922150385402450) * 10^40
        + 4074418964522998359108016190552146084166) * 10^40
        + 9408860701113652201494904180436455436619) * 10^40
        + 1817787621424004060277782482478407816725) * 10^40
        + 3862169444137706420636232327360107887145)) : ℚ) /
        (((((((27122281040468145655395181727 * 10^40
        + 4465675670570477380597075576515595385168) * 10^40
        + 6760620108220723950900319112239593202325) * 10^40
        + 2005501022054633232176888077346872743205) * 10^40
        + 6631671594556436470660296288914756404176) * 10^40
        + 8911902022939581525031971574093922515011) * 10^40
        + 4590040599026161349413345843802051545870) * 10^40
        + 7274278988292002465838403758956818202624)),
    (((((2213291119314198169219454192720586256 * 10^40
        + 2060949341139658521474348818648858466291) * 10^40
        + 437424717035797156905633434820709034447) * 10^40
        + 6614734654790194717369214569164834457651) : ℚ) /
        (((16468843626820963186346239605770663 * 10^40
        + 9959417166099062347511745396294917658616) * 10^40
        + 2571381445361360490102741222929985052940) * 10^40
        + 501233798682413229627038566197460205568)))

theorem midpointP001BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP001Center2543‖ ≤ midpointP001Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP001Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP001Input2543]
  have hc : (compactExp2542 midpointP001Input2543 6).1 = midpointP001Center2543 := by cbv
  have he : ((compactExp2542 midpointP001Input2543 6).2 : ℝ) = midpointP001Error2543 := by
    have hq : (compactExp2542 midpointP001Input2543 6).2 =
        ((27549026282477 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [midpointP001Error2543]
  have h := compactExp_error2542 midpointP001Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨1, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP001Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP001Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP001DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨1, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP001Factor2543 * embedPair2542 midpointP001Center2543‖ ≤
      (pairMagnitude2542 midpointP001Factor2543 : ℝ) * midpointP001Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP001Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP001Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP001BaseError2543
    (embedPair_magnitude2542 midpointP001Factor2543)

def midpointP002Input2543 : RatPair2542 :=
  ((((-((17504 * 10^40
        + 5533685727613462851485367902899472965795) * 10^40
        + 2076067450279743934634355647818833287071)) : ℚ) /
        ((37259 * 10^40
        + 7512399958630922988558011403061934943263) * 10^40
        + 3245319541147164857129196178636800000000)),
    ((232067602941064323301960589 : ℚ) /
        922337203685477580800000000))

def midpointP002Center2543 : RatPair2542 :=
  ((((-102387181446193135) : ℚ) /
        1267650600228229401496703205376),
    (((-42681798673030777) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP002Error2543 : ℝ := ((32516940792383 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def midpointP002Factor2543 : RatPair2542 :=
  ((((-(((((((19963079138162941481988693370456250544 * 10^40
        + 2791749517623246610107642711366680740414) * 10^40
        + 8157697118417550133124886213605354235460) * 10^40
        + 5095747763790514696896399068861568414051) * 10^40
        + 5785859122645493350942709043283643907139) * 10^40
        + 3160681799518925024241136357969511523714) * 10^40
        + 6463283541369029111207329104972548207973) * 10^40
        + 7007650812520590902941384794302220450345)) : ℚ) /
        (((((((12934203555623022802489371619775238 * 10^40
        + 5369406541151071830883757205280034038497) * 10^40
        + 5239347416869405872418377391211952970768) * 10^40
        + 6256121658307969231689166054734832200523) * 10^40
        + 4892178652454750943483273149762057891696) * 10^40
        + 3393138559547178245036975735142135566697) * 10^40
        + 3171694872646251788063092958998674069461) * 10^40
        + 2078416538416332669174346994037727166464)),
    (((-(((749081746754454866716173838399175548252 * 10^40
        + 7329165331616059462417302127822378877518) * 10^40
        + 5987407382140001584381127768293948460732) * 10^40
        + 5664477738272850871804227282338978580531)) : ℚ) /
        (((11372863999724529723771331140716484706 * 10^40
        + 3059657384216312359868101852254002691611) * 10^40
        + 5513986549700772477284468726247877327111) * 10^40
        + 2128040375699336320163472946549812625408)))

theorem midpointP002BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP002Center2543‖ ≤ midpointP002Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP002Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP002Input2543]
  have hc : (compactExp2542 midpointP002Input2543 6).1 = midpointP002Center2543 := by cbv
  have he : ((compactExp2542 midpointP002Input2543 6).2 : ℝ) = midpointP002Error2543 := by
    have hq : (compactExp2542 midpointP002Input2543 6).2 =
        ((32516940792383 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [midpointP002Error2543]
  have h := compactExp_error2542 midpointP002Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨2, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP002Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP002Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP002DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨2, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP002Factor2543 * embedPair2542 midpointP002Center2543‖ ≤
      (pairMagnitude2542 midpointP002Factor2543 : ℝ) * midpointP002Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP002Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP002Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP002BaseError2543
    (embedPair_magnitude2542 midpointP002Factor2543)

def midpointP003Input2543 : RatPair2542 :=
  ((((-((2311845 * 10^40
        + 6291996787715184886019299151454837578887) * 10^40
        + 7138254125466834346928002399630202866517)) : ℚ) /
        ((4936844 * 10^40
        + 9835528589511556039278102674210316090725) * 10^40
        + 261672208631327141691407243673600000000)),
    ((232067602941064323301960589 : ℚ) /
        922337203685477580800000000))

def midpointP003Center2543 : RatPair2542 :=
  ((((-56401925962504077) : ℚ) /
        633825300114114700748351602688),
    (((-47024160929127597) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP003Error2543 : ℝ := ((71321852804659 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP003Factor2543 : RatPair2542 :=
  ((((-((((((((615005 * 10^40
        + 4489955296946052072641394773339651525881) * 10^40
        + 4883376942278976503518548681940399327305) * 10^40
        + 571434976186337069251827051591651050236) * 10^40
        + 2298848378614165546880014524640237189209) * 10^40
        + 294305613577732397383336344284580324843) * 10^40
        + 8503938090781555962220383686533771591293) * 10^40
        + 8735419874177333201845446243363956961680) * 10^40
        + 232405645034873295799933447461014141145)) : ℚ) /
        ((((((((398 * 10^40
        + 6372239225929469748655229703529237503939) * 10^40
        + 799977628651599572544205741928229267546) * 10^40
        + 8074163384365080543125525280832019200187) * 10^40
        + 8783760858095326559356407291417140397976) * 10^40
        + 1202644505756096119848347178014857296159) * 10^40
        + 6634671206451512668072394385035667250674) * 10^40
        + 3655306539217751237311456414319608430951) * 10^40
        + 8342981345179815132303112409507822567424)),
    (((-((((1690 * 10^40
        + 9480166018474758933053915892815359367299) * 10^40
        + 5229197564789926158528054389477096640376) * 10^40
        + 4885709635916523216608836773640754358029) * 10^40
        + 1782610999484692326928715209662828700497)) : ℚ) /
        ((((59 * 10^40
        + 8977045912724148255392324646419666610799) * 10^40
        + 4963278804814690982954086293272215991213) * 10^40
        + 8079980077853176363345647266331259570704) * 10^40
        + 3499471875913971532495728362840072912896)))

theorem midpointP003BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP003Center2543‖ ≤ midpointP003Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP003Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP003Input2543]
  have hc : (compactExp2542 midpointP003Input2543 6).1 = midpointP003Center2543 := by cbv
  have he : ((compactExp2542 midpointP003Input2543 6).2 : ℝ) = midpointP003Error2543 := by
    have hq : (compactExp2542 midpointP003Input2543 6).2 =
        ((71321852804659 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP003Error2543]
  have h := compactExp_error2542 midpointP003Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨3, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP003Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP003Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP003DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨3, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP003Factor2543 * embedPair2542 midpointP003Center2543‖ ≤
      (pairMagnitude2542 midpointP003Factor2543 : ℝ) * midpointP003Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP003Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP003Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP003BaseError2543
    (embedPair_magnitude2542 midpointP003Factor2543)

def midpointP004Input2543 : RatPair2542 :=
  ((((-((40164 * 10^40
        + 5022442974389097174534817852520776456575) * 10^40
        + 2711401382296326618996496687857895787071)) : ℚ) /
        ((85933 * 10^40
        + 7760455571997284522015582536256410604776) * 10^40
        + 4973901795733724857129196178636800000000)),
    (((-232067602941064323301960589) : ℚ) /
        922337203685477580800000000))

def midpointP004Center2543 : RatPair2542 :=
  ((((-119454017871663921) : ℚ) /
        1267650600228229401496703205376),
    ((49796393156523871 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP004Error2543 : ℝ := ((37665695892389 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def midpointP004Factor2543 : RatPair2542 :=
  ((((-(((((((564378176724267563125294326482792286996 * 10^40
        + 7793861343471075362982889066048212520267) * 10^40
        + 7667065579426159097849321527398913429457) * 10^40
        + 7675611769591527863681838940015246206788) * 10^40
        + 8940034844557488900729219046152932970084) * 10^40
        + 4636260708540202849753410774984021334210) * 10^40
        + 436458769742663058601602148959316643627) * 10^40
        + 2723780419566804084586249540395970450345)) : ℚ) /
        (((((((365961559856702817619232579306699500 * 10^40
        + 6862221928175758903022166902333397953764) * 10^40
        + 3565446275448390073657647876318263415813) * 10^40
        + 443786034197786466539481759498176295069) * 10^40
        + 7587538321304029666896982313510841953357) * 10^40
        + 6606111637808476813357363589154438181955) * 10^40
        + 7072260956407791940695604017013672348849) * 10^40
        + 6072399290426652832809546994037727166464)),
    (((((368611408295709392399334776767573491440 * 10^40
        + 8038343857873021036125363811016247373236) * 10^40
        + 6135632365403370959160501821158961146048) * 10^40
        + 201308577402291439278129479604603580531) : ℚ) /
        (((60494756785749855398949708414367509556 * 10^40
        + 8469685393859698559239062009782750790208) * 10^40
        + 5624121067586997531350846526087951220080) * 10^40
        + 471203586473293187030672946549812625408)))

theorem midpointP004BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP004Center2543‖ ≤ midpointP004Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP004Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP004Input2543]
  have hc : (compactExp2542 midpointP004Input2543 6).1 = midpointP004Center2543 := by cbv
  have he : ((compactExp2542 midpointP004Input2543 6).2 : ℝ) = midpointP004Error2543 := by
    have hq : (compactExp2542 midpointP004Input2543 6).2 =
        ((37665695892389 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [midpointP004Error2543]
  have h := compactExp_error2542 midpointP004Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨4, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP004Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP004Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP004DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨4, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP004Factor2543 * embedPair2542 midpointP004Center2543‖ ≤
      (pairMagnitude2542 midpointP004Factor2543 : ℝ) * midpointP004Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP004Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP004Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP004BaseError2543
    (embedPair_magnitude2542 midpointP004Factor2543)

def midpointP005Input2543 : RatPair2542 :=
  ((((-((1907265 * 10^40
        + 1219318152063824565102509123924878687393) * 10^40
        + 719543833510121554458247198890608599551)) : ℚ) /
        ((2004853 * 10^40
        + 1585656787256051029723459526030936333635) * 10^40
        + 8987763861162286712537110865510400000000)),
    ((0 : ℚ) /
        1))

def midpointP005Center2543 : RatPair2542 :=
  (((76215933147918825 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def midpointP005Error2543 : ℝ := ((9142075765063 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP005Factor2543 : RatPair2542 :=
  ((((-(((((((390588975183437 * 10^40
        + 6595285136274578832698654063302023923750) * 10^40
        + 9262686129128118715912579288829282295054) * 10^40
        + 7007718742684940407130168637759701898505) * 10^40
        + 7458477752731381125697792724191127053571) * 10^40
        + 4904073158970027853342266917834596676787) * 10^40
        + 8054978070547616453931618479107984891994) * 10^40
        + 3027617334658936452006834539364295119359)) : ℚ) /
        (((((((350324527734794 * 10^40
        + 5077494899797170116444918479360072265102) * 10^40
        + 5125126627881435946977575762428922040794) * 10^40
        + 800688019471023688888142049757864098247) * 10^40
        + 4155740870070314522743882242943086043493) * 10^40
        + 892110770724758133063317963885677711327) * 10^40
        + 9753802393133669735751674835807564773841) * 10^40
        + 4757931552203294191972661842542819522564)),
    ((0 : ℚ) /
        1))

theorem midpointP005BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP005Center2543‖ ≤ midpointP005Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP005Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP005Input2543]
  have hc : (compactExp2542 midpointP005Input2543 5).1 = midpointP005Center2543 := by cbv
  have he : ((compactExp2542 midpointP005Input2543 5).2 : ℝ) = midpointP005Error2543 := by
    have hq : (compactExp2542 midpointP005Input2543 5).2 =
        ((9142075765063 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP005Error2543]
  have h := compactExp_error2542 midpointP005Input2543 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨5, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^5 * embedPair2542 midpointP005Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP005Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP005DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨5, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP005Factor2543 * embedPair2542 midpointP005Center2543‖ ≤
      (pairMagnitude2542 midpointP005Factor2543 : ℝ) * midpointP005Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨5, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨5, by omega⟩)
      (storedWidth ⟨5, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP005Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP005Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨5, by omega⟩) (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP005BaseError2543
    (embedPair_magnitude2542 midpointP005Factor2543)

def midpointP006Input2543 : RatPair2542 :=
  ((((-341272804931755697817790975552580907) : ℚ) /
        362648785144156933668031692800000000),
    ((0 : ℚ) /
        1))

def midpointP006Center2543 : RatPair2542 :=
  (((52931751828820959 : ℚ) /
        633825300114114700748351602688),
    ((0 : ℚ) /
        1))

noncomputable def midpointP006Error2543 : ℝ := ((2936091580181 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def midpointP006Factor2543 : RatPair2542 :=
  ((((-((3201440231239 * 10^40
        + 6608967083614380855716100921509856426832) * 10^40
        + 9367393745110086276487151843557516356077)) : ℚ) /
        ((1125139654581 * 10^40
        + 7592681536358322695098251662029717487854) * 10^40
        + 7500513901407974894051392625769934575692)),
    ((0 : ℚ) /
        1))

theorem midpointP006BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP006Center2543‖ ≤ midpointP006Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP006Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP006Input2543]
  have hc : (compactExp2542 midpointP006Input2543 5).1 = midpointP006Center2543 := by cbv
  have he : ((compactExp2542 midpointP006Input2543 5).2 : ℝ) = midpointP006Error2543 := by
    have hq : (compactExp2542 midpointP006Input2543 5).2 =
        ((2936091580181 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [midpointP006Error2543]
  have h := compactExp_error2542 midpointP006Input2543 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨6, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^5 * embedPair2542 midpointP006Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP006Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP006DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨6, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP006Factor2543 * embedPair2542 midpointP006Center2543‖ ≤
      (pairMagnitude2542 midpointP006Factor2543 : ℝ) * midpointP006Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP006Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP006Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP006BaseError2543
    (embedPair_magnitude2542 midpointP006Factor2543)

def midpointP007Input2543 : RatPair2542 :=
  ((((-((2311845 * 10^40
        + 6291996787715184886019299151454837578887) * 10^40
        + 7138254125466834346928002399630202866517)) : ℚ) /
        ((2468422 * 10^40
        + 4917764294755778019639051337105158045362) * 10^40
        + 5130836104315663570845703621836800000000)),
    ((0 : ℚ) /
        1))

def midpointP007Center2543 : RatPair2542 :=
  (((122212850061716733 : ℚ) /
        1267650600228229401496703205376),
    ((0 : ℚ) /
        1))

noncomputable def midpointP007Error2543 : ℝ := ((1646148233959 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

def midpointP007Factor2543 : RatPair2542 :=
  ((((-(((((((1622180115837306 * 10^40
        + 7500893616582762097249324847779076008090) * 10^40
        + 7892896625795004381465952916528460631708) * 10^40
        + 136230341594532776769798913637406872595) * 10^40
        + 2539625204588326250076991096191802039906) * 10^40
        + 2996035745261859322162207410278023205085) * 10^40
        + 8669578784040080395442137289137269148049) * 10^40
        + 283941358206281159383582648634127100239)) : ℚ) /
        (((((((805041462575021 * 10^40
        + 7079312926936802232247311991249217419670) * 10^40
        + 979742744862321305049150515046562815308) * 10^40
        + 5823069415768300550791984076254412420139) * 10^40
        + 1108424179451382096714663219362497219983) * 10^40
        + 3403655412067643210192511207855818793412) * 10^40
        + 2576003740463481318714632232700438990647) * 10^40
        + 5626858567174875362465669405463491599044)),
    ((0 : ℚ) /
        1))

theorem midpointP007BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP007Center2543‖ ≤ midpointP007Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP007Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP007Input2543]
  have hc : (compactExp2542 midpointP007Input2543 5).1 = midpointP007Center2543 := by cbv
  have he : ((compactExp2542 midpointP007Input2543 5).2 : ℝ) = midpointP007Error2543 := by
    have hq : (compactExp2542 midpointP007Input2543 5).2 =
        ((1646148233959 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)) := by cbv
    rw [hq]
    norm_num [midpointP007Error2543]
  have h := compactExp_error2542 midpointP007Input2543 hz 5
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨7, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^5 * embedPair2542 midpointP007Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP007Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP007DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨7, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP007Factor2543 * embedPair2542 midpointP007Center2543‖ ≤
      (pairMagnitude2542 midpointP007Factor2543 : ℝ) * midpointP007Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP007Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP007Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP007BaseError2543
    (embedPair_magnitude2542 midpointP007Factor2543)

def midpointP008Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-167134122842263137885183377) : ℚ) /
        1844674407370955161600000000))

def midpointP008Center2543 : RatPair2542 :=
  (((37713743166656081 : ℚ) /
        633825300114114700748351602688),
    ((19853078225315115 : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP008Error2543 : ℝ := ((32095378731397 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP008Factor2543 : RatPair2542 :=
  ((((-((((((((3697 * 10^40
        + 6695544845373007224977011139861869124047) * 10^40
        + 5751214489027335331702880674962105770002) * 10^40
        + 1687375741020180928339238449197641943931) * 10^40
        + 3379057925446582662067634828092277990120) * 10^40
        + 3671391649328794972466650579256772643768) * 10^40
        + 5397256916767634767867471143745825095655) * 10^40
        + 283115769815564769395674342853560936625) * 10^40
        + 8979512871905385810782305864793809204625)) : ℚ) /
        ((((((((18 * 10^40
        + 2984288604778480337311700118630858362060) * 10^40
        + 9056203459937844487150861487164860266824) * 10^40
        + 3561206765350349624704998165397574540535) * 10^40
        + 7952653318595315879921374007057196578094) * 10^40
        + 9585218808933562408282095673458040021310) * 10^40
        + 8214764246505575257497281678399261335674) * 10^40
        + 606956795371708452327948581224096572212) * 10^40
        + 6855565731403325368319009638031290269696)),
    ((((((782 * 10^40
        + 7803930662711799002237176280397422942957) * 10^40
        + 2961043133561303497950876517448929480432) * 10^40
        + 8688501477283953483890994467971185477446) * 10^40
        + 1692867309942801740675242549977663094021) : ℚ) /
        ((((12 * 10^40
        + 8329988601378996734190278649661899052629) * 10^40
        + 4565644144180008712481702843628126145477) * 10^40
        + 3880296661271743328473918521073442795679) * 10^40
        + 919260466983222442850016725680145825792)))

theorem midpointP008BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP008Center2543‖ ≤ midpointP008Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP008Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP008Input2543]
  have hc : (compactExp2542 midpointP008Input2543 6).1 = midpointP008Center2543 := by cbv
  have he : ((compactExp2542 midpointP008Input2543 6).2 : ℝ) = midpointP008Error2543 := by
    have hq : (compactExp2542 midpointP008Input2543 6).2 =
        ((32095378731397 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP008Error2543]
  have h := compactExp_error2542 midpointP008Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨8, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP008Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP008Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP008DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨8, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP008Factor2543 * embedPair2542 midpointP008Center2543‖ ≤
      (pairMagnitude2542 midpointP008Factor2543 : ℝ) * midpointP008Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP008Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP008Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP008BaseError2543
    (embedPair_magnitude2542 midpointP008Factor2543)

def midpointP009Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-248572230457264719772844751) : ℚ) /
        1844674407370955161600000000))

def midpointP009Center2543 : RatPair2542 :=
  ((((-59344799379932253) : ℚ) /
        1267650600228229401496703205376),
    (((-61188882496737185) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP009Error2543 : ℝ := ((47193201250081 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP009Factor2543 : RatPair2542 :=
  ((((-((((((((8128 * 10^40
        + 3723575962641545863319894641101428997722) * 10^40
        + 4400614045615760512915482836846891782182) * 10^40
        + 3581479132791261655890664936157316411252) * 10^40
        + 2765038607811724807840588179722550491949) * 10^40
        + 2550341874693127381241382657428396787020) * 10^40
        + 7784635350546405026798515991827438229671) * 10^40
        + 1157807472002488641607726013051655198558) * 10^40
        + 2554051683493137563730574894444539599057)) : ℚ) /
        ((((((((18 * 10^40
        + 2984288604778480337311700118630858362060) * 10^40
        + 9056203459937844487150861487164860266824) * 10^40
        + 3561206765350349624704998165397574540535) * 10^40
        + 7952653318595315879921374007057196578094) * 10^40
        + 9585218808933562408282095673458040021310) * 10^40
        + 8214764246505575257497281678399261335674) * 10^40
        + 606956795371708452327948581224096572212) * 10^40
        + 6855565731403325368319009638031290269696)),
    ((((((388 * 10^40
        + 665119999355322866265293389390708955810) * 10^40
        + 2547343139328823460723508348836631927495) * 10^40
        + 7617763330444532393469326570474625026332) * 10^40
        + 143234148664284492410266635094634746441) : ℚ) /
        ((((4 * 10^40
        + 2776662867126332244730092883220633017543) * 10^40
        + 1521881381393336237493900947876042048492) * 10^40
        + 4626765553757247776157972840357814265226) * 10^40
        + 3639753488994407480950005575226715275264)))

theorem midpointP009BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP009Center2543‖ ≤ midpointP009Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP009Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP009Input2543]
  have hc : (compactExp2542 midpointP009Input2543 6).1 = midpointP009Center2543 := by cbv
  have he : ((compactExp2542 midpointP009Input2543 6).2 : ℝ) = midpointP009Error2543 := by
    have hq : (compactExp2542 midpointP009Input2543 6).2 =
        ((47193201250081 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP009Error2543]
  have h := compactExp_error2542 midpointP009Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨9, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP009Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP009Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP009DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨9, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP009Factor2543 * embedPair2542 midpointP009Center2543‖ ≤
      (pairMagnitude2542 midpointP009Factor2543 : ℝ) * midpointP009Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP009Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP009Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP009BaseError2543
    (embedPair_magnitude2542 midpointP009Factor2543)

def midpointP010Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-147868731131102971900751961) : ℚ) /
        922337203685477580800000000))

def midpointP010Center2543 : RatPair2542 :=
  ((((-1786516799585073) : ℚ) /
        39614081257132168796771975168),
    ((1975841114612903 : ℚ) /
        39614081257132168796771975168))

noncomputable def midpointP010Error2543 : ℝ := ((46567664217959 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP010Factor2543 : RatPair2542 :=
  ((((-((((((((2872 * 10^40
        + 680393931565205447846392155648474071537) * 10^40
        + 1782637355566734238400227695136318256512) * 10^40
        + 4325760045685567782469878793729400928553) * 10^40
        + 3551851835409260918876345585641463912671) * 10^40
        + 9803488021220810437472877763980428445018) * 10^40
        + 8565056130553024051223351403755539761682) * 10^40
        + 9187540784660632500172330322488613733735) * 10^40
        + 9660454956788938732192077725246206587745)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((230 * 10^40
        + 8500133677194978185441068680873269656878) * 10^40
        + 1322068027756547022607629423111873003093) * 10^40
        + 7418816203934140282777743195476208212287) * 10^40
        + 898242252581902671943964407177224313551) : ℚ) /
        ((((2 * 10^40
        + 1388331433563166122365046441610316508771) * 10^40
        + 5760940690696668118746950473938021024246) * 10^40
        + 2313382776878623888078986420178907132613) * 10^40
        + 1819876744497203740475002787613357637632)))

theorem midpointP010BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP010Center2543‖ ≤ midpointP010Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP010Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP010Input2543]
  have hc : (compactExp2542 midpointP010Input2543 6).1 = midpointP010Center2543 := by cbv
  have he : ((compactExp2542 midpointP010Input2543 6).2 : ℝ) = midpointP010Error2543 := by
    have hq : (compactExp2542 midpointP010Input2543 6).2 =
        ((46567664217959 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP010Error2543]
  have h := compactExp_error2542 midpointP010Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨10, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP010Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP010Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP010DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨10, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP010Factor2543 * embedPair2542 midpointP010Center2543‖ ≤
      (pairMagnitude2542 midpointP010Factor2543 : ℝ) * midpointP010Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP010Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP010Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP010BaseError2543
    (embedPair_magnitude2542 midpointP010Factor2543)

def midpointP011Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-163591967237422244711390441) : ℚ) /
        922337203685477580800000000))

def midpointP011Center2543 : RatPair2542 :=
  (((29700478777308971 : ℚ) /
        1267650600228229401496703205376),
    ((4993654612293977 : ℚ) /
        79228162514264337593543950336))

noncomputable def midpointP011Error2543 : ℝ := ((21246915866791 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def midpointP011Factor2543 : RatPair2542 :=
  ((((-((((((((3512 * 10^40
        + 9875224420360211346880549317996207418684) * 10^40
        + 3568883867014093871128131137402436260518) * 10^40
        + 2806412593740939175106878121146441995124) * 10^40
        + 5365585872144082127854513629995548682941) * 10^40
        + 3119434389937971231317552711860239170185) * 10^40
        + 4100465346593858684098953445831694981027) * 10^40
        + 688014125117825212287658412026629352582) * 10^40
        + 5015513798208625115135757727121973157505)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((766 * 10^40
        + 1905434921295744355061864176205111292168) * 10^40
        + 8204791713865886004402696161004698477610) * 10^40
        + 4414763431112379432599423799582301896442) * 10^40
        + 8351260190222016474755056063097609349693) : ℚ) /
        ((((6 * 10^40
        + 4164994300689498367095139324830949526314) * 10^40
        + 7282822072090004356240851421814063072738) * 10^40
        + 6940148330635871664236959260536721397839) * 10^40
        + 5459630233491611221425008362840072912896)))

theorem midpointP011BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP011Center2543‖ ≤ midpointP011Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP011Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP011Input2543]
  have hc : (compactExp2542 midpointP011Input2543 6).1 = midpointP011Center2543 := by cbv
  have he : ((compactExp2542 midpointP011Input2543 6).2 : ℝ) = midpointP011Error2543 := by
    have hq : (compactExp2542 midpointP011Input2543 6).2 =
        ((21246915866791 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [midpointP011Error2543]
  have h := compactExp_error2542 midpointP011Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨11, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP011Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP011Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP011DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨11, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP011Factor2543 * embedPair2542 midpointP011Center2543‖ ≤
      (pairMagnitude2542 midpointP011Factor2543 : ℝ) * midpointP011Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP011Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP011Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP011BaseError2543
    (embedPair_magnitude2542 midpointP011Factor2543)

def midpointP012Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-3597547835483398755459269) : ℚ) /
        18446744073709551616000000))

def midpointP012Center2543 : RatPair2542 :=
  (((10616669865367347 : ℚ) /
        158456325028528675187087900672),
    ((112899785215701 : ℚ) /
        19807040628566084398385987584))

noncomputable def midpointP012Error2543 : ℝ := ((24649589418789 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP012Factor2543 : RatPair2542 :=
  ((((-((((((((1061 * 10^40
        + 2613290794927495019448150618954225895490) * 10^40
        + 3262893783976623784762776937112298098169) * 10^40
        + 7984632366204486836529895415756748205511) * 10^40
        + 8745980058517251720035911601644698347285) * 10^40
        + 8012538431693093737576162440282053942484) * 10^40
        + 6867465616614926649395261773105155928999) * 10^40
        + 5153752562064080988575789589037138701950) * 10^40
        + 129588267999495412379793808749074615161)) : ℚ) /
        ((((((((1 * 10^40
        + 1436518037798655021081981257414428647628) * 10^40
        + 8066012716246115280446928842947803766676) * 10^40
        + 5222575422834396851544062385337348408783) * 10^40
        + 4872040832412207242495085875441074786130) * 10^40
        + 9349076175558347650517630979591127501331) * 10^40
        + 9263422765406598453593580104899953833479) * 10^40
        + 6287934799710731778270496786326506035763) * 10^40
        + 2928472858212707835519938102376955641856)),
    ((((((421 * 10^40
        + 2320411960639507766092195939332476705312) * 10^40
        + 779755702604046839291547758390598289346) * 10^40
        + 7461473941926396680565492978919156390170) * 10^40
        + 4530759111509349638325585896335522603425) : ℚ) /
        ((((3 * 10^40
        + 2082497150344749183547569662415474763157) * 10^40
        + 3641411036045002178120425710907031536369) * 10^40
        + 3470074165317935832118479630268360698919) * 10^40
        + 7729815116745805610712504181420036456448)))

theorem midpointP012BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP012Center2543‖ ≤ midpointP012Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP012Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP012Input2543]
  have hc : (compactExp2542 midpointP012Input2543 6).1 = midpointP012Center2543 := by cbv
  have he : ((compactExp2542 midpointP012Input2543 6).2 : ℝ) = midpointP012Error2543 := by
    have hq : (compactExp2542 midpointP012Input2543 6).2 =
        ((24649589418789 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP012Error2543]
  have h := compactExp_error2542 midpointP012Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨12, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP012Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP012Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP012DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨12, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP012Factor2543 * embedPair2542 midpointP012Center2543‖ ≤
      (pairMagnitude2542 midpointP012Factor2543 : ℝ) * midpointP012Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP012Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP012Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP012BaseError2543
    (embedPair_magnitude2542 midpointP012Factor2543)

def midpointP013Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-38943612797745222552819531) : ℚ) /
        184467440737095516160000000))

def midpointP013Center2543 : RatPair2542 :=
  (((12483771131617153 : ℚ) /
        316912650057057350374175801344),
    (((-69082355836916511) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP013Error2543 : ℝ := ((20346739221721 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def midpointP013Factor2543 : RatPair2542 :=
  ((((-((((((((4972 * 10^40
        + 6146106730630066831269036077316794681320) * 10^40
        + 6500834745341126418598985136184110551830) * 10^40
        + 3469101854323237307665530312030979506551) * 10^40
        + 3689379094410989348065840806605768970720) * 10^40
        + 5357317379544343419996866394793901940253) * 10^40
        + 8729000180740400747431303822410342327418) * 10^40
        + 8523633380670169357790996925181316397188) * 10^40
        + 1161004091636492608684192973707310239169)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((303 * 10^40
        + 9903523272938960428355409357094213634129) * 10^40
        + 7918150455041837426076021133419240166165) * 10^40
        + 4541686360635601136888717545587748926564) * 10^40
        + 2587622863153817023305462620490410747105) : ℚ) /
        ((((2 * 10^40
        + 1388331433563166122365046441610316508771) * 10^40
        + 5760940690696668118746950473938021024246) * 10^40
        + 2313382776878623888078986420178907132613) * 10^40
        + 1819876744497203740475002787613357637632)))

theorem midpointP013BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP013Center2543‖ ≤ midpointP013Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP013Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP013Input2543]
  have hc : (compactExp2542 midpointP013Input2543 6).1 = midpointP013Center2543 := by cbv
  have he : ((compactExp2542 midpointP013Input2543 6).2 : ℝ) = midpointP013Error2543 := by
    have hq : (compactExp2542 midpointP013Input2543 6).2 =
        ((20346739221721 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [midpointP013Error2543]
  have h := compactExp_error2542 midpointP013Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨13, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP013Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP013Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP013DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨13, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP013Factor2543 * embedPair2542 midpointP013Center2543‖ ≤
      (pairMagnitude2542 midpointP013Factor2543 : ℝ) * midpointP013Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP013Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP013Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP013BaseError2543
    (embedPair_magnitude2542 midpointP013Factor2543)

def midpointP014Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-222216309640860904036652051) : ℚ) /
        922337203685477580800000000))

def midpointP014Center2543 : RatPair2542 :=
  ((((-40857339058233125) : ℚ) /
        633825300114114700748351602688),
    (((-24260996165990991) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP014Error2543 : ℝ := ((47215369270231 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP014Factor2543 : RatPair2542 :=
  ((((-((((((((6473 * 10^40
        + 972448521698348560418982286013865395250) * 10^40
        + 3120211606753311512739415361840082208486) * 10^40
        + 5409824973323471748560508638475064408579) * 10^40
        + 6010941128309371357830454209504249147999) * 10^40
        + 8265039809023363939292864215185543088532) * 10^40
        + 9323938752640448123087787817908026864075) * 10^40
        + 4694055378914175175366446021199542966938) * 10^40
        + 1926108761149239620746865766463631387225)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((1040 * 10^40
        + 7603620870143799552237416181683159606814) * 10^40
        + 8191700518335951931066285282831468950641) * 10^40
        + 640805496372756204323451421740282137275) * 10^40
        + 8885333814538010785650320322688078922223) : ℚ) /
        ((((6 * 10^40
        + 4164994300689498367095139324830949526314) * 10^40
        + 7282822072090004356240851421814063072738) * 10^40
        + 6940148330635871664236959260536721397839) * 10^40
        + 5459630233491611221425008362840072912896)))

theorem midpointP014BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP014Center2543‖ ≤ midpointP014Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP014Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP014Input2543]
  have hc : (compactExp2542 midpointP014Input2543 6).1 = midpointP014Center2543 := by cbv
  have he : ((compactExp2542 midpointP014Input2543 6).2 : ℝ) = midpointP014Error2543 := by
    have hq : (compactExp2542 midpointP014Input2543 6).2 =
        ((47215369270231 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP014Error2543]
  have h := compactExp_error2542 midpointP014Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨14, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP014Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP014Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP014DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨14, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP014Factor2543 * embedPair2542 midpointP014Center2543‖ ≤
      (pairMagnitude2542 midpointP014Factor2543 : ℝ) * midpointP014Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP014Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP014Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP014BaseError2543
    (embedPair_magnitude2542 midpointP014Factor2543)

def midpointP015Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-241918896241267742567269127) : ℚ) /
        922337203685477580800000000))

def midpointP015Center2543 : RatPair2542 :=
  ((((-40286401872268933) : ℚ) /
        1267650600228229401496703205376),
    ((75119174508443341 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP015Error2543 : ℝ := ((58495575838589 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP015Factor2543 : RatPair2542 :=
  ((((-((((((((7669 * 10^40
        + 9095389785724971891054355243111952249124) * 10^40
        + 5757381305298547462840072318235856960784) * 10^40
        + 5442308229246207460408767334439828788037) * 10^40
        + 9091402998437521496779249245098628531427) * 10^40
        + 2198175006097532779816664978302280159434) * 10^40
        + 1192672020706450612438935213908674541448) * 10^40
        + 4606023942099329524780534536829608737179) * 10^40
        + 7689332900762541899554688540300682988193)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((1133 * 10^40
        + 383375309897013491682063823180778935752) * 10^40
        + 8819305348451890643474545121043081566044) * 10^40
        + 5962410504709434148201768033363488803686) * 10^40
        + 3601275205196559526849440008746953478771) : ℚ) /
        ((((6 * 10^40
        + 4164994300689498367095139324830949526314) * 10^40
        + 7282822072090004356240851421814063072738) * 10^40
        + 6940148330635871664236959260536721397839) * 10^40
        + 5459630233491611221425008362840072912896)))

theorem midpointP015BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP015Center2543‖ ≤ midpointP015Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP015Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP015Input2543]
  have hc : (compactExp2542 midpointP015Input2543 6).1 = midpointP015Center2543 := by cbv
  have he : ((compactExp2542 midpointP015Input2543 6).2 : ℝ) = midpointP015Error2543 := by
    have hq : (compactExp2542 midpointP015Input2543 6).2 =
        ((58495575838589 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP015Error2543]
  have h := compactExp_error2542 midpointP015Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨15, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP015Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP015Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP015DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨15, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP015Factor2543 * embedPair2542 midpointP015Center2543‖ ≤
      (pairMagnitude2542 midpointP015Factor2543 : ℝ) * midpointP015Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP015Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP015Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP015BaseError2543
    (embedPair_magnitude2542 midpointP015Factor2543)

def midpointP016Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-128078761976539480284285369) : ℚ) /
        461168601842738790400000000))

def midpointP016Center2543 : RatPair2542 :=
  (((40547209846529425 : ℚ) /
        1267650600228229401496703205376),
    ((74978719169544533 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP016Error2543 : ℝ := ((54105609013039 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP016Factor2543 : RatPair2542 :=
  ((((-((((((((2149 * 10^40
        + 5171461584491785838601599623965825842195) * 10^40
        + 1159746974460170526888909211810052585679) * 10^40
        + 6539920816986468135654698651855121366029) * 10^40
        + 3768176938125462569857550835833180719186) * 10^40
        + 7171793877650484969363212382449846833832) * 10^40
        + 4059426714036992223270748684541543326710) * 10^40
        + 8523461248730548073826385994579998771250) * 10^40
        + 6136740670939087131228838187653373906977)) : ℚ) /
        ((((((((1 * 10^40
        + 1436518037798655021081981257414428647628) * 10^40
        + 8066012716246115280446928842947803766676) * 10^40
        + 5222575422834396851544062385337348408783) * 10^40
        + 4872040832412207242495085875441074786130) * 10^40
        + 9349076175558347650517630979591127501331) * 10^40
        + 9263422765406598453593580104899953833479) * 10^40
        + 6287934799710731778270496786326506035763) * 10^40
        + 2928472858212707835519938102376955641856)),
    ((((((199 * 10^40
        + 9542681419948342981254682481643791034226) * 10^40
        + 7303376138889027782907599025519188126609) * 10^40
        + 7621351670622804180280639344582403847895) * 10^40
        + 5764592781889787956448230270487084986479) : ℚ) /
        ((((1 * 10^40
        + 694165716781583061182523220805158254385) * 10^40
        + 7880470345348334059373475236969010512123) * 10^40
        + 1156691388439311944039493210089453566306) * 10^40
        + 5909938372248601870237501393806678818816)))

theorem midpointP016BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP016Center2543‖ ≤ midpointP016Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP016Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP016Input2543]
  have hc : (compactExp2542 midpointP016Input2543 6).1 = midpointP016Center2543 := by cbv
  have he : ((compactExp2542 midpointP016Input2543 6).2 : ℝ) = midpointP016Error2543 := by
    have hq : (compactExp2542 midpointP016Input2543 6).2 =
        ((54105609013039 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP016Error2543]
  have h := compactExp_error2542 midpointP016Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨16, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP016Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP016Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP016DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨16, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP016Factor2543 * embedPair2542 midpointP016Center2543‖ ≤
      (pairMagnitude2542 midpointP016Factor2543 : ℝ) * midpointP016Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP016Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP016Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP016BaseError2543
    (embedPair_magnitude2542 midpointP016Factor2543)

def midpointP017Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-283815168104843088184463307) : ℚ) /
        922337203685477580800000000))

def midpointP017Center2543 : RatPair2542 :=
  (((14158838218709175 : ℚ) /
        316912650057057350374175801344),
    (((-31852477766206211) : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP017Error2543 : ℝ := ((49707156234579 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP017Factor2543 : RatPair2542 :=
  ((((-((((((((10552 * 10^40
        + 6117502222271189345237124340864688817201) * 10^40
        + 1787296751344994946386601051777409767196) * 10^40
        + 790999840104712143920557484438775131136) * 10^40
        + 115533356533361244926101406571757714252) * 10^40
        + 7014267087473276566690964719836557114773) * 10^40
        + 5946192316855069994868769794587964295082) * 10^40
        + 4379200214514680730930309078473304538190) * 10^40
        + 717212324944206024986015926635071879913)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((443 * 10^40
        + 871547337113521485768490072369688708460) * 10^40
        + 3176384290861686142415387084948506925637) * 10^40
        + 737400870114596849432250698985098331010) * 10^40
        + 6068899578839440778572941871316264734637) : ℚ) /
        ((((2 * 10^40
        + 1388331433563166122365046441610316508771) * 10^40
        + 5760940690696668118746950473938021024246) * 10^40
        + 2313382776878623888078986420178907132613) * 10^40
        + 1819876744497203740475002787613357637632)))

theorem midpointP017BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP017Center2543‖ ≤ midpointP017Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP017Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP017Input2543]
  have hc : (compactExp2542 midpointP017Input2543 6).1 = midpointP017Center2543 := by cbv
  have he : ((compactExp2542 midpointP017Input2543 6).2 : ℝ) = midpointP017Error2543 := by
    have hq : (compactExp2542 midpointP017Input2543 6).2 =
        ((49707156234579 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP017Error2543]
  have h := compactExp_error2542 midpointP017Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨17, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP017Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP017Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP017DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨17, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP017Factor2543 * embedPair2542 midpointP017Center2543‖ ≤
      (pairMagnitude2542 midpointP017Factor2543 : ℝ) * midpointP017Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP017Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP017Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP017BaseError2543
    (embedPair_magnitude2542 midpointP017Factor2543)

def midpointP018Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-73567983708883823551501933) : ℚ) /
        230584300921369395200000000))

def midpointP018Center2543 : RatPair2542 :=
  (((96739130213619 : ℚ) /
        1267650600228229401496703205376),
    (((-42620051607736831) : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP018Error2543 : ℝ := ((56618823860459 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP018Factor2543 : RatPair2542 :=
  ((((-((((((((708 * 10^40
        + 9839882150709010837730854078871216979685) * 10^40
        + 6710639948449430710413019173443634290220) * 10^40
        + 8919427662264496313258097881950316606776) * 10^40
        + 5003829803181946965119335233753065452702) * 10^40
        + 1207038114031771194435370587368164434336) * 10^40
        + 9968362209029540805562365600350181326368) * 10^40
        + 9655704556253586059087857877769776353711) * 10^40
        + 221498902477557740663451908377383029593)) : ℚ) /
        (((((((2859129509449663755270495314353607161907 * 10^40
        + 2016503179061528820111732210736950941669) * 10^40
        + 1305643855708599212886015596334337102195) * 10^40
        + 8718010208103051810623771468860268696532) * 10^40
        + 7337269043889586912629407744897781875332) * 10^40
        + 9815855691351649613398395026224988458369) * 10^40
        + 9071983699927682944567624196581626508940) * 10^40
        + 8232118214553176958879984525594238910464)),
    ((((((344 * 10^40
        + 5590536833868330737200443308918445366035) * 10^40
        + 5107051977858431828298533012536389254253) * 10^40
        + 1694865375050899376834094157215336895640) * 10^40
        + 4941530732963882722984620721130396158609) : ℚ) /
        ((((1 * 10^40
        + 6041248575172374591773784831207737381578) * 10^40
        + 6820705518022501089060212855453515768184) * 10^40
        + 6735037082658967916059239815134180349459) * 10^40
        + 8864907558372902805356252090710018228224)))

theorem midpointP018BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP018Center2543‖ ≤ midpointP018Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP018Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP018Input2543]
  have hc : (compactExp2542 midpointP018Input2543 6).1 = midpointP018Center2543 := by cbv
  have he : ((compactExp2542 midpointP018Input2543 6).2 : ℝ) = midpointP018Error2543 := by
    have hq : (compactExp2542 midpointP018Input2543 6).2 =
        ((56618823860459 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP018Error2543]
  have h := compactExp_error2542 midpointP018Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨18, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP018Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP018Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP018DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨18, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP018Factor2543 * embedPair2542 midpointP018Center2543‖ ≤
      (pairMagnitude2542 midpointP018Factor2543 : ℝ) * midpointP018Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP018Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP018Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP018BaseError2543
    (embedPair_magnitude2542 midpointP018Factor2543)

def midpointP019Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-15658507908849208554053631) : ℚ) /
        46116860184273879040000000))

def midpointP019Center2543 : RatPair2542 :=
  ((((-10295249169114155) : ℚ) /
        158456325028528675187087900672),
    (((-10981650668030205) : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP019Error2543 : ℝ := ((45235645573715 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP019Factor2543 : RatPair2542 :=
  ((((-((((((((802 * 10^40
        + 8836790858401087600288971507166632717553) * 10^40
        + 7846503116737835856726871881127105355828) * 10^40
        + 6231530398078433475852947742255468800235) * 10^40
        + 7417947525386236267566091920499085763813) * 10^40
        + 3642958749477157102808257660706818043526) * 10^40
        + 8363755979597038230962006785409959062334) * 10^40
        + 8759466539106649194022734034221630510058) * 10^40
        + 264296230792735541408149963437797158409)) : ℚ) /
        (((((((2859129509449663755270495314353607161907 * 10^40
        + 2016503179061528820111732210736950941669) * 10^40
        + 1305643855708599212886015596334337102195) * 10^40
        + 8718010208103051810623771468860268696532) * 10^40
        + 7337269043889586912629407744897781875332) * 10^40
        + 9815855691351649613398395026224988458369) * 10^40
        + 9071983699927682944567624196581626508940) * 10^40
        + 8232118214553176958879984525594238910464)),
    ((((((122 * 10^40
        + 2289098048547738281340851746560712068137) * 10^40
        + 2144075155515479463358101723848999893506) * 10^40
        + 9166334788528321681992481551927767215202) * 10^40
        + 4433464798618149097330217362025243812605) : ℚ) /
        (((5347082858390791530591261610402579127192 * 10^40
        + 8940235172674167029686737618484505256061) * 10^40
        + 5578345694219655972019746605044726783153) * 10^40
        + 2954969186124300935118750696903339409408)))

theorem midpointP019BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP019Center2543‖ ≤ midpointP019Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP019Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP019Input2543]
  have hc : (compactExp2542 midpointP019Input2543 6).1 = midpointP019Center2543 := by cbv
  have he : ((compactExp2542 midpointP019Input2543 6).2 : ℝ) = midpointP019Error2543 := by
    have hq : (compactExp2542 midpointP019Input2543 6).2 =
        ((45235645573715 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP019Error2543]
  have h := compactExp_error2542 midpointP019Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨19, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP019Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP019Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP019DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨19, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP019Factor2543 * embedPair2542 midpointP019Center2543‖ ≤
      (pairMagnitude2542 midpointP019Factor2543 : ℝ) * midpointP019Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP019Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP019Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP019BaseError2543
    (embedPair_magnitude2542 midpointP019Factor2543)

def midpointP020Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-333720465095227151612459579) : ℚ) /
        922337203685477580800000000))

def midpointP020Center2543 : RatPair2542 :=
  ((((-16810184028697807) : ℚ) /
        633825300114114700748351602688),
    ((19582446550305535 : ℚ) /
        316912650057057350374175801344))

noncomputable def midpointP020Error2543 : ℝ := ((46763222162401 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP020Factor2543 : RatPair2542 :=
  ((((-((((((((14585 * 10^40
        + 9714213254284901517763305136952932746758) * 10^40
        + 4828941874181754519333025893952785542501) * 10^40
        + 9247732805566522922166864341431150023346) * 10^40
        + 4726980914969959438309362456531349026094) * 10^40
        + 523539890363251198712447518185402070016) * 10^40
        + 7729404754778499674779463856037628345714) * 10^40
        + 1233800442352770662732513031570587659353) * 10^40
        + 2762520141736303382207357049779216605065)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((1562 * 10^40
        + 9952304117017701271598542068509132326763) * 10^40
        + 5303421018534626870567591981789432452793) * 10^40
        + 6473833663416107749413668052172650046614) * 10^40
        + 8066009353771944000744808801508625651767) : ℚ) /
        ((((6 * 10^40
        + 4164994300689498367095139324830949526314) * 10^40
        + 7282822072090004356240851421814063072738) * 10^40
        + 6940148330635871664236959260536721397839) * 10^40
        + 5459630233491611221425008362840072912896)))

theorem midpointP020BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP020Center2543‖ ≤ midpointP020Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP020Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP020Input2543]
  have hc : (compactExp2542 midpointP020Input2543 6).1 = midpointP020Center2543 := by cbv
  have he : ((compactExp2542 midpointP020Input2543 6).2 : ℝ) = midpointP020Error2543 := by
    have hq : (compactExp2542 midpointP020Input2543 6).2 =
        ((46763222162401 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP020Error2543]
  have h := compactExp_error2542 midpointP020Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨20, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP020Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP020Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP020DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨20, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP020Factor2543 * embedPair2542 midpointP020Center2543‖ ≤
      (pairMagnitude2542 midpointP020Factor2543 : ℝ) * midpointP020Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP020Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP020Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP020BaseError2543
    (embedPair_magnitude2542 midpointP020Factor2543)

def midpointP021Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-350870499539081630010359067) : ℚ) /
        922337203685477580800000000))

def midpointP021Center2543 : RatPair2542 :=
  (((30112485018138119 : ℚ) /
        633825300114114700748351602688),
    ((60322777943108247 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP021Error2543 : ℝ := ((16686510927065 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def midpointP021Factor2543 : RatPair2542 :=
  ((((-((((((((16122 * 10^40
        + 5488316469379268361288846029774656498206) * 10^40
        + 6722320866219536573225950828014567859408) * 10^40
        + 4518607025198675592682711163316733405746) * 10^40
        + 5946014968692359977192716420840639018190) * 10^40
        + 6758216425301303134745666499682202964911) * 10^40
        + 6226443544155951756441221885707810669287) * 10^40
        + 6401144692297345365675651648301363343089) * 10^40
        + 4547266933146093218252662237085809009353)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((547 * 10^40
        + 7727365978462241054868483204662986170900) * 10^40
        + 5275106628938958309450886054986067856609) * 10^40
        + 9790882893174135039890798558780321257436) * 10^40
        + 2147883171421496240173405864592639064797) : ℚ) /
        ((((2 * 10^40
        + 1388331433563166122365046441610316508771) * 10^40
        + 5760940690696668118746950473938021024246) * 10^40
        + 2313382776878623888078986420178907132613) * 10^40
        + 1819876744497203740475002787613357637632)))

theorem midpointP021BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP021Center2543‖ ≤ midpointP021Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP021Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP021Input2543]
  have hc : (compactExp2542 midpointP021Input2543 6).1 = midpointP021Center2543 := by cbv
  have he : ((compactExp2542 midpointP021Input2543 6).2 : ℝ) = midpointP021Error2543 := by
    have hq : (compactExp2542 midpointP021Input2543 6).2 =
        ((16686510927065 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [midpointP021Error2543]
  have h := compactExp_error2542 midpointP021Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨21, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP021Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP021Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP021DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨21, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP021Factor2543 * embedPair2542 midpointP021Center2543‖ ≤
      (pairMagnitude2542 midpointP021Factor2543 : ℝ) * midpointP021Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP021Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP021Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP021BaseError2543
    (embedPair_magnitude2542 midpointP021Factor2543)

def midpointP022Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-71929703922051079173425353) : ℚ) /
        184467440737095516160000000))

def midpointP022Center2543 : RatPair2542 :=
  (((41953357048259425 : ℚ) /
        633825300114114700748351602688),
    ((15018251701478521 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP022Error2543 : ℝ := ((22985519218845 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP022Factor2543 : RatPair2542 :=
  ((((-((((((((16938 * 10^40
        + 8126788965103822066150939705292360732978) * 10^40
        + 8486588577318514057705862615326079509985) * 10^40
        + 4346738312587779001400388594235394525426) * 10^40
        + 9688223780542484420937881058773118143384) * 10^40
        + 4826047013613862042758971656634427605780) * 10^40
        + 2138353543073850442680372209961383202857) * 10^40
        + 6328878134055950421975498896274085813984) * 10^40
        + 1565163488632481666640181435402043681369)) : ℚ) /
        ((((((((4 * 10^40
        + 5746072151194620084327925029657714590515) * 10^40
        + 2264050864984461121787715371791215066706) * 10^40
        + 890301691337587406176249541349393635133) * 10^40
        + 9488163329648828969980343501764299144523) * 10^40
        + 7396304702233390602070523918364510005327) * 10^40
        + 7053691061626393814374320419599815333918) * 10^40
        + 5151739198842927113081987145306024143053) * 10^40
        + 1713891432850831342079752409507822567424)),
    ((((((1684 * 10^40
        + 4304727163048240485732261997375822063346) * 10^40
        + 6689599082112536887782507201775157744448) * 10^40
        + 1576291920854272961985309179150622552186) * 10^40
        + 1061028648132871133543693879394685091345) : ℚ) /
        ((((6 * 10^40
        + 4164994300689498367095139324830949526314) * 10^40
        + 7282822072090004356240851421814063072738) * 10^40
        + 6940148330635871664236959260536721397839) * 10^40
        + 5459630233491611221425008362840072912896)))

theorem midpointP022BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP022Center2543‖ ≤ midpointP022Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP022Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP022Input2543]
  have hc : (compactExp2542 midpointP022Input2543 6).1 = midpointP022Center2543 := by cbv
  have he : ((compactExp2542 midpointP022Input2543 6).2 : ℝ) = midpointP022Error2543 := by
    have hq : (compactExp2542 midpointP022Input2543 6).2 =
        ((22985519218845 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP022Error2543]
  have h := compactExp_error2542 midpointP022Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨22, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP022Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP022Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP022DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨22, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP022Factor2543 * embedPair2542 midpointP022Center2543‖ ≤
      (pairMagnitude2542 midpointP022Factor2543 : ℝ) * midpointP022Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP022Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP022Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP022BaseError2543
    (embedPair_magnitude2542 midpointP022Factor2543)

def midpointP023Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-192478591312897184507537453) : ℚ) /
        461168601842738790400000000))

def midpointP023Center2543 : RatPair2542 :=
  ((((-701767675945475) : ℚ) /
        1267650600228229401496703205376),
    (((-42618634647220093) : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP023Error2543 : ℝ := ((5616918763789 : ℝ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472))

def midpointP023Factor2543 : RatPair2542 :=
  ((((-((((((((4851 * 10^40
        + 2894462251597906311135853252488947405841) * 10^40
        + 9195885381490715095944306130086364288807) * 10^40
        + 7649077024405533607040957241386902954802) * 10^40
        + 1379678561815762678933701734940555760991) * 10^40
        + 9923644352722711216213576001884796461478) * 10^40
        + 5283313746620747593043419372137645583993) * 10^40
        + 5291283646981190463899086623577657792036) * 10^40
        + 5608781920727853426094458881502221263065)) : ℚ) /
        ((((((((1 * 10^40
        + 1436518037798655021081981257414428647628) * 10^40
        + 8066012716246115280446928842947803766676) * 10^40
        + 5222575422834396851544062385337348408783) * 10^40
        + 4872040832412207242495085875441074786130) * 10^40
        + 9349076175558347650517630979591127501331) * 10^40
        + 9263422765406598453593580104899953833479) * 10^40
        + 6287934799710731778270496786326506035763) * 10^40
        + 2928472858212707835519938102376955641856)),
    ((((((901 * 10^40
        + 4823831453546429796231405578160190361850) * 10^40
        + 8339815800926343409899380300208890895164) * 10^40
        + 9338630639243003113645397334526787808911) * 10^40
        + 769975099591899635006102750543041951569) : ℚ) /
        ((((3 * 10^40
        + 2082497150344749183547569662415474763157) * 10^40
        + 3641411036045002178120425710907031536369) * 10^40
        + 3470074165317935832118479630268360698919) * 10^40
        + 7729815116745805610712504181420036456448)))

theorem midpointP023BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP023Center2543‖ ≤ midpointP023Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP023Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP023Input2543]
  have hc : (compactExp2542 midpointP023Input2543 6).1 = midpointP023Center2543 := by cbv
  have he : ((compactExp2542 midpointP023Input2543 6).2 : ℝ) = midpointP023Error2543 := by
    have hq : (compactExp2542 midpointP023Input2543 6).2 =
        ((5616918763789 : ℚ) /
        (17 * 10^40
        + 4224571863520493293247799005065324265472)) := by cbv
    rw [hq]
    norm_num [midpointP023Error2543]
  have h := compactExp_error2542 midpointP023Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨23, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP023Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP023Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP023DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨23, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP023Factor2543 * embedPair2542 midpointP023Center2543‖ ≤
      (pairMagnitude2542 midpointP023Factor2543 : ℝ) * midpointP023Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP023Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP023Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP023BaseError2543
    (embedPair_magnitude2542 midpointP023Factor2543)

def midpointP024Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-198294009626145024670442227) : ℚ) /
        461168601842738790400000000))

def midpointP024Center2543 : RatPair2542 :=
  ((((-62048065864636513) : ℚ) /
        1267650600228229401496703205376),
    (((-58445890164336165) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP024Error2543 : ℝ := ((12095821322917 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def midpointP024Factor2543 : RatPair2542 :=
  ((((-((((((((5148 * 10^40
        + 7047761247438967460230898515811956982904) * 10^40
        + 4632640162116879412239451589356596490390) * 10^40
        + 5681829791478160898056213924024433019246) * 10^40
        + 8944230810568607389477207902755359242115) * 10^40
        + 1368488764580467611573446611566953922667) * 10^40
        + 6160820328809124677920322705910345558030) * 10^40
        + 936391178131659407584777942027885738322) * 10^40
        + 1257395436927830080397541850715077848985)) : ℚ) /
        ((((((((1 * 10^40
        + 1436518037798655021081981257414428647628) * 10^40
        + 8066012716246115280446928842947803766676) * 10^40
        + 5222575422834396851544062385337348408783) * 10^40
        + 4872040832412207242495085875441074786130) * 10^40
        + 9349076175558347650517630979591127501331) * 10^40
        + 9263422765406598453593580104899953833479) * 10^40
        + 6287934799710731778270496786326506035763) * 10^40
        + 2928472858212707835519938102376955641856)),
    ((((((928 * 10^40
        + 7191637361450728121541663367392126455737) * 10^40
        + 9501634373460170616887680042730863745261) * 10^40
        + 3738695680600127793330608604383142698188) * 10^40
        + 6331218809684118005569597446935497365071) : ℚ) /
        ((((3 * 10^40
        + 2082497150344749183547569662415474763157) * 10^40
        + 3641411036045002178120425710907031536369) * 10^40
        + 3470074165317935832118479630268360698919) * 10^40
        + 7729815116745805610712504181420036456448)))

theorem midpointP024BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP024Center2543‖ ≤ midpointP024Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP024Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP024Input2543]
  have hc : (compactExp2542 midpointP024Input2543 6).1 = midpointP024Center2543 := by cbv
  have he : ((compactExp2542 midpointP024Input2543 6).2 : ℝ) = midpointP024Error2543 := by
    have hq : (compactExp2542 midpointP024Input2543 6).2 =
        ((12095821322917 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [midpointP024Error2543]
  have h := compactExp_error2542 midpointP024Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨24, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP024Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP024Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP024DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨24, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP024Factor2543 * embedPair2542 midpointP024Center2543‖ ≤
      (pairMagnitude2542 midpointP024Factor2543 : ℝ) * midpointP024Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP024Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP024Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP024BaseError2543
    (embedPair_magnitude2542 midpointP024Factor2543)

def midpointP025Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-6424546158860510660323953) : ℚ) /
        14411518807585587200000000))

def midpointP025Center2543 : RatPair2542 :=
  ((((-41226985061112047) : ℚ) /
        633825300114114700748351602688),
    ((10807721380190347 : ℚ) /
        633825300114114700748351602688))

noncomputable def midpointP025Error2543 : ℝ := ((47088513695723 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP025Factor2543 : RatPair2542 :=
  ((((-((((((((5 * 10^40
        + 4044107318642583765126701222608283941038) * 10^40
        + 7448820071240418172294534739631770513781) * 10^40
        + 2839201669928187131261744777874523908109) * 10^40
        + 469225468836679461552111301487252821316) * 10^40
        + 8387803145946612042119482142165710503241) * 10^40
        + 9872169202616820846955848540540876480264) * 10^40
        + 7567947684450847484170504704316656953840) * 10^40
        + 185547962953003605537520888815971488593)) : ℚ) /
        (((((((11168474646287749044025372321693777976 * 10^40
        + 2000064465543209096953561453948191214615) * 10^40
        + 8950412671311361715675335998423181004305) * 10^40
        + 4526242227375402546135249107300235424595) * 10^40
        + 8309911207202693698877458624003506960450) * 10^40
        + 5194593186294342381302337480571191361165) * 10^40
        + 5074499936327842511502217282017896978550) * 10^40
        + 5500906711775598347495624939553102495744)),
    ((((((10 * 10^40
        + 298863411462693300562061355957895191212) * 10^40
        + 3894581786427200272721435371541180135728) * 10^40
        + 8767541727340265672796645839527494748018) * 10^40
        + 9480944326309158342794167021448301372023) : ℚ) /
        (((334192678649424470661953850650161195449 * 10^40
        + 5558764698292135439355421101155281578503) * 10^40
        + 8473646605888728498251234162815295423947) * 10^40
        + 809685574132768808444921918556458713088)))

theorem midpointP025BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP025Center2543‖ ≤ midpointP025Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP025Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP025Input2543]
  have hc : (compactExp2542 midpointP025Input2543 6).1 = midpointP025Center2543 := by cbv
  have he : ((compactExp2542 midpointP025Input2543 6).2 : ℝ) = midpointP025Error2543 := by
    have hq : (compactExp2542 midpointP025Input2543 6).2 =
        ((47088513695723 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP025Error2543]
  have h := compactExp_error2542 midpointP025Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨25, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP025Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP025Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP025DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨25, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP025Factor2543 * embedPair2542 midpointP025Center2543‖ ≤
      (pairMagnitude2542 midpointP025Factor2543 : ℝ) * midpointP025Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP025Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP025Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP025BaseError2543
    (embedPair_magnitude2542 midpointP025Factor2543)

def midpointP026Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-13314816284541079739367117) : ℚ) /
        28823037615171174400000000))

def midpointP026Center2543 : RatPair2542 :=
  ((((-5895272958844489) : ℚ) /
        316912650057057350374175801344),
    ((81913470580212805 : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP026Error2543 : ℝ := ((14998463592469 : ℝ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944))

def midpointP026Factor2543 : RatPair2542 :=
  ((((-((((((((23 * 10^40
        + 2123814894860080317489741628008595591898) * 10^40
        + 575138019529688900726895147472033021016) * 10^40
        + 8133133017896856926949359177468625748122) * 10^40
        + 2882891924551078175727861107403936938755) * 10^40
        + 713147463120540283160753959953650017775) * 10^40
        + 5515025884591468230370575930291637192870) * 10^40
        + 7940912739265531041756209761819717388148) * 10^40
        + 6616531568768038431276546099938413712665)) : ℚ) /
        (((((((44673898585150996176101489286775111904 * 10^40
        + 8000257862172836387814245815792764858463) * 10^40
        + 5801650685245446862701343993692724017221) * 10^40
        + 8104968909501610184540996429200941698383) * 10^40
        + 3239644828810774795509834496014027841802) * 10^40
        + 778372745177369525209349922284765444662) * 10^40
        + 297999745311370046008869128071587914202) * 10^40
        + 2003626847102393389982499758212409982976)),
    ((((((20 * 10^40
        + 7868525939390077205457044910857715811230) * 10^40
        + 2106204824694010675837961709655174630397) * 10^40
        + 5866737056800587935573901606774715675824) * 10^40
        + 4716148895308115397780975413405004052347) : ℚ) /
        (((668385357298848941323907701300322390899 * 10^40
        + 1117529396584270878710842202310563157007) * 10^40
        + 6947293211777456996502468325630590847894) * 10^40
        + 1619371148265537616889843837112917426176)))

theorem midpointP026BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP026Center2543‖ ≤ midpointP026Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP026Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP026Input2543]
  have hc : (compactExp2542 midpointP026Input2543 6).1 = midpointP026Center2543 := by cbv
  have he : ((compactExp2542 midpointP026Input2543 6).2 : ℝ) = midpointP026Error2543 := by
    have hq : (compactExp2542 midpointP026Input2543 6).2 =
        ((14998463592469 : ℚ) /
        (34 * 10^40
        + 8449143727040986586495598010130648530944)) := by cbv
    rw [hq]
    norm_num [midpointP026Error2543]
  have h := compactExp_error2542 midpointP026Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨26, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP026Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP026Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP026DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨26, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP026Factor2543 * embedPair2542 midpointP026Center2543‖ ≤
      (pairMagnitude2542 midpointP026Factor2543 : ℝ) * midpointP026Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP026Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP026Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP026BaseError2543
    (embedPair_magnitude2542 midpointP026Factor2543)

def midpointP027Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-27973742299905538962999907) : ℚ) /
        57646075230342348800000000))

def midpointP027Center2543 : RatPair2542 :=
  (((79810959027156749 : ℚ) /
        1267650600228229401496703205376),
    ((7483713039867911 : ℚ) /
        316912650057057350374175801344))

noncomputable def midpointP027Error2543 : ℝ := ((21971025144965 : ℝ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888))

def midpointP027Factor2543 : RatPair2542 :=
  ((((-((((((((102 * 10^40
        + 4548605097092058957034101061145639101697) * 10^40
        + 9648756261447178545879448343974095593942) * 10^40
        + 7819173008141746583395456225398668399862) * 10^40
        + 20238464899871453478890609197636559120) * 10^40
        + 5358972911497091803705104468486399760968) * 10^40
        + 5239664687086667000141883538620627512036) * 10^40
        + 2696507601662964517030364412523864675683) * 10^40
        + 6076443959743699815349325162727043323193)) : ℚ) /
        (((((((178695594340603984704405957147100447619 * 10^40
        + 2001031448691345551256983263171059433854) * 10^40
        + 3206602740981787450805375974770896068887) * 10^40
        + 2419875638006440738163985716803766793533) * 10^40
        + 2958579315243099182039337984056111367208) * 10^40
        + 3113490980709478100837399689139061778648) * 10^40
        + 1191998981245480184035476512286351656808) * 10^40
        + 8014507388409573559929999032849639931904)),
    ((((((131 * 10^40
        + 163156432198891915045105566732547514455) * 10^40
        + 1732369633054747487326241608112902357195) * 10^40
        + 3454533097466428439211592266883678447247) * 10^40
        + 384892178020406212161475883380055875711) : ℚ) /
        (((4010312143793093647943446207801934345394 * 10^40
        + 6705176379505625272265053213863378942046) * 10^40
        + 1683759270664741979014809953783545087364) * 10^40
        + 9716226889593225701339063022677504557056)))

theorem midpointP027BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP027Center2543‖ ≤ midpointP027Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP027Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP027Input2543]
  have hc : (compactExp2542 midpointP027Input2543 6).1 = midpointP027Center2543 := by cbv
  have he : ((compactExp2542 midpointP027Input2543 6).2 : ℝ) = midpointP027Error2543 := by
    have hq : (compactExp2542 midpointP027Input2543 6).2 =
        ((21971025144965 : ℚ) /
        (69 * 10^40
        + 6898287454081973172991196020261297061888)) := by cbv
    rw [hq]
    norm_num [midpointP027Error2543]
  have h := compactExp_error2542 midpointP027Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨27, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP027Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP027Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP027DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨27, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP027Factor2543 * embedPair2542 midpointP027Center2543‖ ≤
      (pairMagnitude2542 midpointP027Factor2543 : ℝ) * midpointP027Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP027Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP027Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP027BaseError2543
    (embedPair_magnitude2542 midpointP027Factor2543)

def midpointP028Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-114023575338654370347174007) : ℚ) /
        230584300921369395200000000))

def midpointP028Center2543 : RatPair2542 :=
  (((2592405383329941 : ℚ) /
        39614081257132168796771975168),
    (((-19596563653085349) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP028Error2543 : ℝ := ((41544814960909 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP028Factor2543 : RatPair2542 :=
  ((((-((((((((1702 * 10^40
        + 2146868283064666344100662495077167214652) * 10^40
        + 2948683871936019018012923560576738990741) * 10^40
        + 2039168930268808416952351094758587275788) * 10^40
        + 7105691447279951230335994052148945761934) * 10^40
        + 5233981447275754057066275596084170962825) * 10^40
        + 5768686651487098381888038954197906009452) * 10^40
        + 8272090917236963504650721468401484699808) * 10^40
        + 7504162634620559379732599324690612757953)) : ℚ) /
        (((((((2859129509449663755270495314353607161907 * 10^40
        + 2016503179061528820111732210736950941669) * 10^40
        + 1305643855708599212886015596334337102195) * 10^40
        + 8718010208103051810623771468860268696532) * 10^40
        + 7337269043889586912629407744897781875332) * 10^40
        + 9815855691351649613398395026224988458369) * 10^40
        + 9071983699927682944567624196581626508940) * 10^40
        + 8232118214553176958879984525594238910464)),
    ((((((534 * 10^40
        + 346878575502436972647997002010846543273) * 10^40
        + 5842418821422014318096502127466028666075) * 10^40
        + 1802291867341008792701333151324056468423) * 10^40
        + 9227514258541057620468200377249560335011) : ℚ) /
        ((((1 * 10^40
        + 6041248575172374591773784831207737381578) * 10^40
        + 6820705518022501089060212855453515768184) * 10^40
        + 6735037082658967916059239815134180349459) * 10^40
        + 8864907558372902805356252090710018228224)))

theorem midpointP028BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP028Center2543‖ ≤ midpointP028Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP028Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP028Input2543]
  have hc : (compactExp2542 midpointP028Input2543 6).1 = midpointP028Center2543 := by cbv
  have he : ((compactExp2542 midpointP028Input2543 6).2 : ℝ) = midpointP028Error2543 := by
    have hq : (compactExp2542 midpointP028Input2543 6).2 =
        ((41544814960909 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP028Error2543]
  have h := compactExp_error2542 midpointP028Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨28, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP028Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP028Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP028DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨28, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP028Factor2543 * embedPair2542 midpointP028Center2543‖ ≤
      (pairMagnitude2542 midpointP028Factor2543 : ℝ) * midpointP028Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP028Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP028Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP028BaseError2543
    (embedPair_magnitude2542 midpointP028Factor2543)

def midpointP029Input2543 : RatPair2542 :=
  ((((-((765759 * 10^40
        + 9220008118228572644733013732085952767233) * 10^40
        + 6195777758350016577360268910860671616517)) : ℚ) /
        ((1615821 * 10^40
        + 8657849103005641127025697039314156817578) * 10^40
        + 401421039708351141691407243673600000000)),
    (((-117264241519146685751589419) : ℚ) /
        230584300921369395200000000))

def midpointP029Center2543 : RatPair2542 :=
  (((36257600129090953 : ℚ) /
        1267650600228229401496703205376),
    (((-77144481251239621) : ℚ) /
        1267650600228229401496703205376))

noncomputable def midpointP029Error2543 : ℝ := ((60162805064471 : ℝ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776))

def midpointP029Factor2543 : RatPair2542 :=
  ((((-((((((((1800 * 10^40
        + 3093405242376387486073568065075745335914) * 10^40
        + 3603161286382229636111128960158816823746) * 10^40
        + 9296243871408586470228236272318893154789) * 10^40
        + 3969838891921220779895777197169487792553) * 10^40
        + 975051323370047103109052880760037431297) * 10^40
        + 4576637045621912508552459440068271415908) * 10^40
        + 4452052651715037134961402297900282505435) * 10^40
        + 5051274568647383280250832723300513853225)) : ℚ) /
        (((((((2859129509449663755270495314353607161907 * 10^40
        + 2016503179061528820111732210736950941669) * 10^40
        + 1305643855708599212886015596334337102195) * 10^40
        + 8718010208103051810623771468860268696532) * 10^40
        + 7337269043889586912629407744897781875332) * 10^40
        + 9815855691351649613398395026224988458369) * 10^40
        + 9071983699927682944567624196581626508940) * 10^40
        + 8232118214553176958879984525594238910464)),
    ((((((549 * 10^40
        + 2124977710677033648254903945856340645098) * 10^40
        + 7883405581128968505825602828580333091656) * 10^40
        + 2459631912087626307879521753753628273256) * 10^40
        + 3516725784624786870192505771262705530087) : ℚ) /
        ((((1 * 10^40
        + 6041248575172374591773784831207737381578) * 10^40
        + 6820705518022501089060212855453515768184) * 10^40
        + 6735037082658967916059239815134180349459) * 10^40
        + 8864907558372902805356252090710018228224)))

theorem midpointP029BaseError2543 :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP029Center2543‖ ≤ midpointP029Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hz : ‖embedPair2542 midpointP029Input2543‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, midpointP029Input2543]
  have hc : (compactExp2542 midpointP029Input2543 6).1 = midpointP029Center2543 := by cbv
  have he : ((compactExp2542 midpointP029Input2543 6).2 : ℝ) = midpointP029Error2543 := by
    have hq : (compactExp2542 midpointP029Input2543 6).2 =
        ((60162805064471 : ℚ) /
        (139 * 10^40
        + 3796574908163946345982392040522594123776)) := by cbv
    rw [hq]
    norm_num [midpointP029Error2543]
  have h := compactExp_error2542 midpointP029Input2543 hz 6
  rw [hc, he] at h
  have howner : weightedUnitJet2539 0 (1/2) nodeModulation2541 ⟨29, by omega⟩
      midpointPosition2543 = Complex.exp ((2 : ℂ)^6 * embedPair2542 midpointP029Input2543) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;>
      norm_num [midpointPosition2543, storedWidth, nodeModulation2541,
        embedPair2542, midpointP029Input2543, Complex.mul_re, Complex.mul_im]
  rwa [howner]

theorem midpointP029DerivativeError2543 :
    ‖weightedUnitJet2539 2 (1/2) nodeModulation2541 ⟨29, by omega⟩ midpointPosition2543 -
      embedPair2542 midpointP029Factor2543 * embedPair2542 midpointP029Center2543‖ ≤
      (pairMagnitude2542 midpointP029Factor2543 : ℝ) * midpointP029Error2543 := by
  have hx : |midpointPosition2543| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [midpointPosition2543, storedWidth]
  have hf : weightedMultiplier2543 2 (1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) midpointPosition2543 = embedPair2542 midpointP029Factor2543
          := by
    apply Complex.ext <;>
      norm_num [weightedMultiplier2543, Finset.sum_range_succ, weightedLambda2537,
        bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
        midpointPosition2543, storedWidth, nodeModulation2541, embedPair2542,
            midpointP029Factor2543,
        Complex.mul_re, Complex.mul_im, pow_succ]
  have hfactor := weightedFamily_inside_factor2543 2 (by omega) (1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at hfactor
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [hfactor]
  exact complex_multiplier_error2543 _ _ _ _ _ midpointP029BaseError2543
    (embedPair_magnitude2542 midpointP029Factor2543)

theorem midpoint_grid2543 :
    (-stripRadius2303 + (5440 : ℝ)*(2*stripRadius2303/10240) +
      (-stripRadius2303 + (5441 : ℝ)*(2*stripRadius2303/10240)))/2 =
        midpointPosition2543 := by
  norm_num [stripRadius2303, midpointPosition2543]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.midpointP000DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP001DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP002DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP003DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP004DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP005DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP006DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP007DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP008DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP009DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP010DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP011DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP012DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP013DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP014DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP015DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP016DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP017DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP018DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP019DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP020DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP021DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP022DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP023DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP024DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP025DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP026DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP027DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP028DerivativeError2543
#print axioms ConnesWeilRH.Dev.midpointP029DerivativeError2543
