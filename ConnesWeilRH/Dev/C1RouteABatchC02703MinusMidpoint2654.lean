import ConnesWeilRH.Dev.C1RouteACompactExp1602547
import ConnesWeilRH.Dev.C1RouteADerivativeMultiplier2543
import ConnesWeilRH.Dev.C1RouteANonzeroNode2541

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def batchC02703MinusMidpointPosition2654 : ℝ := (((-316735492833) : ℝ) /
        102400000000)

theorem batchC02703MinusMidpointZero2654 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def batchC02703MinusMidpointP000Center2654 : RatPair2542 := (0, 0)

def batchC02703MinusMidpointP000Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchC02703MinusMidpointP000Error2654 : ℝ := 0

theorem batchC02703MinusMidpointP000Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703MinusMidpointPosition2654 = 0 :=
        by
  have hx : storedWidth ⟨0, by omega⟩ ^ 2 ≤ |batchC02703MinusMidpointPosition2654| := by
    norm_num [storedWidth, batchC02703MinusMidpointPosition2654]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨0, by omega⟩)
    (pow_pos (storedWidth_pos ⟨0, by omega⟩) 2) hx

theorem batchC02703MinusMidpointP000BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP000Center2654‖ ≤
          batchC02703MinusMidpointP000Error2654 := by
  rw [batchC02703MinusMidpointP000Exterior2654]
  norm_num [batchC02703MinusMidpointP000Center2654, batchC02703MinusMidpointP000Error2654,
      batchC02703MinusMidpointZero2654]

theorem batchC02703MinusMidpointP000DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP000Factor2654 * embedPair2542
          batchC02703MinusMidpointP000Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP000Factor2654 : ℝ) *
            batchC02703MinusMidpointP000Error2654 := by
  rw [batchC02703MinusMidpointP000Exterior2654]
  norm_num [batchC02703MinusMidpointP000Factor2654, batchC02703MinusMidpointP000Center2654,
      batchC02703MinusMidpointP000Error2654,
      batchC02703MinusMidpointZero2654, pairMagnitude2542]

def batchC02703MinusMidpointP001Input2654 : RatPair2542 :=
    ((((-(9173966179679248992031974566443778681947 *
    10^40
        + 7251325571877605797560529797558238234583)) : ℚ) /
        ((2 * 10^40
        + 6105795989954410616908676258371734840964) * 10^40
        + 7085517164747000628154230269542400000000)),
    ((1749739040583718993008386157 : ℚ) /
        7378697629483820646400000000))

def batchC02703MinusMidpointP001Center2654 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP001Factor2654 : RatPair2542 := ((((((((((236143840922145307119 *
    10^40
        + 6478068127392365490049450671635635745130) * 10^40
        + 2786376288855800575242323810724514048997) * 10^40
        + 2629450156546203961805702495213714299930) * 10^40
        + 2736212487786417339062292538248618516713) * 10^40
        + 8513276665543631003359189783446426942139) * 10^40
        + 7892029221523119761741502417453869478152) * 10^40
        + 1455790256752002883571880656162808048495) : ℚ) /
        (((((((684873256575724 * 10^40
        + 2370140998274624055002488004123915834298) * 10^40
        + 8089970320597692648080808394183498962723) * 10^40
        + 7079859102305490765553462129060756538270) * 10^40
        + 9395243675980792162292799876635620380601) * 10^40
        + 4969621022290337072789875449736420652707) * 10^40
        + 8152520742871246570624020783295022628009) * 10^40
        + 9291125434145921407965473005619963232256)),
    (((-(((40538026203407005755117918291668 * 10^40
        + 998732175264027605367373092066460726790) * 10^40
        + 9346247354401068033020624635511850811810) * 10^40
        + 1323177232878084045762408280199696783971)) : ℚ) /
        (((872336107864473325864215004 * 10^40
        + 3083119694800333575110962220020458067639) * 10^40
        + 4911086349577617206369127334737239996814) * 10^40
        + 6739671780504839054352608273370949091328)))

noncomputable def batchC02703MinusMidpointP001Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP001BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP001Center2654‖ ≤
          batchC02703MinusMidpointP001Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP001Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP001Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP001Input2654 9 =
      (batchC02703MinusMidpointP001Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP001Input2654 9).2 : ℝ) =
      batchC02703MinusMidpointP001Error2654 := by
    rw [hs]
    norm_num [batchC02703MinusMidpointP001Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP001Input2654 hz 9
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^9 * embedPair2542
          batchC02703MinusMidpointP001Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP001Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP001DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP001Factor2654 * embedPair2542
          batchC02703MinusMidpointP001Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP001Factor2654 : ℝ) *
            batchC02703MinusMidpointP001Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP001Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP001Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP001BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP001Factor2654)

def batchC02703MinusMidpointP002Input2654 : RatPair2542 := ((((-((212 * 10^40
        + 965063883437823607556343305245266437394) * 10^40
        + 3912294867707320106256934808194655389327)) : ℚ) /
        ((907 * 10^40
        + 6566688093805892399028352450919822243973) * 10^40
        + 5562169296946165227104579407052800000000)),
    (((-1749739040583718993008386157) : ℚ) /
        3689348814741910323200000000))

def batchC02703MinusMidpointP002Center2654 : RatPair2542 := ((((-3406786364882305976811) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-428447050640957123259) : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)))

def batchC02703MinusMidpointP002Factor2654 : RatPair2542 :=
    ((((((((((33521820560913021339830833421 * 10^40
        + 3935540130358090539257247628197981023572) * 10^40
        + 878618211656434017631787564249622037639) * 10^40
        + 1704106225874868911991799634871432165588) * 10^40
        + 9964077442092123025870711893366574672918) * 10^40
        + 8432404332400219525781185353702250849478) * 10^40
        + 5567810911721332605084516604201977273097) * 10^40
        + 4305256104343216289420440649965696120685) : ℚ) /
        (((((((480385729523523435726859879 * 10^40
        + 2775216011231556979761304011622474958341) * 10^40
        + 15830441943907989341034779726937110421) * 10^40
        + 5658583955982579854750334187300077732517) * 10^40
        + 9727265293890335306969300400259610548921) * 10^40
        + 2584695690484231275698265184139082278852) * 10^40
        + 4986820186651225289806278557987509658566) * 10^40
        + 4491828599305430759480867966189230358528)),
    (((((1357283558220629257977726460086461172 * 10^40
        + 3611981904065823113019703939813754567602) * 10^40
        + 8449809778675802385312750200829104204327) * 10^40
        + 5942645024162743523672658028499182344531) : ℚ) /
        (((421806401758280500327337297102314 * 10^40
        + 8140150076674282230220238386611892008295) * 10^40
        + 687681922515014871635317358694198419023) * 10^40
        + 9246120977791785609131556620000357777408)))

noncomputable def batchC02703MinusMidpointP002Error2654 : ℝ := ((57185464289322366127 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP002BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP002Center2654‖ ≤
          batchC02703MinusMidpointP002Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP002Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP002Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP002Input2654 8 =
      (batchC02703MinusMidpointP002Center2654, ((57185464289322366127 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP002Input2654 8).2 : ℝ) =
      batchC02703MinusMidpointP002Error2654 := by
    rw [hs]
    norm_num [batchC02703MinusMidpointP002Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP002Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02703MinusMidpointP002Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP002Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP002DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP002Factor2654 * embedPair2542
          batchC02703MinusMidpointP002Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP002Factor2654 : ℝ) *
            batchC02703MinusMidpointP002Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP002Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP002Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP002BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP002Factor2654)

def batchC02703MinusMidpointP003Input2654 : RatPair2542 := ((((-((6741902 * 10^40
        + 4502746968753472778979071172993835788977) * 10^40
        + 4785113362794939861150963129495002694047)) : ℚ) /
        ((39909323 * 10^40
        + 2173098595058318439849977628536462222717) * 10^40
        + 7075397844561261240558584646860800000000)),
    (((-1749739040583718993008386157) : ℚ) /
        3689348814741910323200000000))

def batchC02703MinusMidpointP003Center2654 : RatPair2542 := ((((-53774575216227850214818131579) :
    ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)),
    (((-216410946229993639686862587171) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC02703MinusMidpointP003Factor2654 : RatPair2542 := ((((-((((((((9074604 * 10^40
        + 6504401686453387674017898565265781521557) * 10^40
        + 8658041398003457245408305977578667002255) * 10^40
        + 6142385658818137701867039957573767884882) * 10^40
        + 3183684969225987363205450252644622612370) * 10^40
        + 7530194435616161628668360120942258076808) * 10^40
        + 3598008548691395456162455248249142913815) * 10^40
        + 833332689495853054274444669509629881611) * 10^40
        + 2787138718078089548020680386389719039145)) : ℚ) /
        ((((((((6650 * 10^40
        + 2408491116392305360750374304171148880015) * 10^40
        + 8888519693162406535793642164592918910006) * 10^40
        + 4530433710676354504923695640497324738458) * 10^40
        + 474708301784417656819782432434936751540) * 10^40
        + 6207645351261312099665966688738336505321) * 10^40
        + 2489225876476505527844576104121433734986) * 10^40
        + 7256772275000525081059431851505002049817) * 10^40
        + 156564114883576411595615598893307265024)),
    ((((((88228 * 10^40
        + 1934910164618315246450347528517042705909) * 10^40
        + 2407806690558347261915604839566167556505) * 10^40
        + 2213085211156861311559212780091659868303) * 10^40
        + 7399229151092479420049225020802928126451) : ℚ) /
        ((((81 * 10^40
        + 5490088787818391259802587653191878682990) * 10^40
        + 5592798717137792896144614007283126629840) * 10^40
        + 8169378537463451588299065414406849324310) * 10^40
        + 7748156047340878143410821357736682323968)))

noncomputable def batchC02703MinusMidpointP003Error2654 : ℝ := ((846057011154568664979607571 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP003BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP003Center2654‖ ≤
          batchC02703MinusMidpointP003Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP003Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP003Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP003Input2654 8 =
      (batchC02703MinusMidpointP003Center2654, ((846057011154568664979607571 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP003Input2654 8).2 : ℝ) =
      batchC02703MinusMidpointP003Error2654 := by
    rw [hs]
    norm_num [batchC02703MinusMidpointP003Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP003Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02703MinusMidpointP003Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP003Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP003DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP003Factor2654 * embedPair2542
          batchC02703MinusMidpointP003Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP003Factor2654 : ℝ) *
            batchC02703MinusMidpointP003Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP003Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP003Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP003BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP003Factor2654)

def batchC02703MinusMidpointP004Input2654 : RatPair2542 := ((((-((53 * 10^40
        + 2504229323577865046679863564264153647511) * 10^40
        + 5417855259998427784412833470984301987703)) : ℚ) /
        ((367 * 10^40
        + 9235794181140936530116772061806973257075) * 10^40
        + 3233813500783245025233842156339200000000)),
    ((1749739040583718993008386157 : ℚ) /
        3689348814741910323200000000))

def batchC02703MinusMidpointP004Center2654 : RatPair2542 := ((((-1647405103627431517954936411011)
    : ℚ) /
        (4567192 * 10^40
        + 6166590716193865151022383844364247891968)),
    ((106077341082942180312823656311507 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def batchC02703MinusMidpointP004Factor2654 : RatPair2542 :=
    ((((-(((((((6491219052692045656731689910 * 10^40
        + 3586199579524609628956978239765409418250) * 10^40
        + 4387114858229479484532761336252889943348) * 10^40
        + 4159451820231794125222818993056995318027) * 10^40
        + 8766284165004856550201053011981185714488) * 10^40
        + 7601356740524013718501447273003488876706) * 10^40
        + 7369288871893473623242730432174317215701) * 10^40
        + 1677920605357760098735043273446352972305)) : ℚ) /
        (((((((4323275564328024290765888 * 10^40
        + 577796549450561173324521435512667847094) * 10^40
        + 143690981248927661524289161612659297436) * 10^40
        + 3697326703760821531686382783935428510357) * 10^40
        + 9511936665947723534268286380581151786561) * 10^40
        + 2329944432892520785389832690094461582735) * 10^40
        + 5346428983474055333529662657433530506872) * 10^40
        + 872872799447661823459696309910389129216)),
    (((-(((36198134074178657526639131094704985 * 10^40
        + 7135426259651105208862413227909725862473) * 10^40
        + 7175816498313877468460011422751953908199) * 10^40
        + 7814483434628898130637278964978577868451)) : ℚ) /
        (((69308293269420702059076544575621 * 10^40
        + 5633177325419984539322170168813258063842) * 10^40
        + 7525751726261002576446366634684657373192) * 10^40
        + 2454077087469085869006917982962967379968)))

noncomputable def batchC02703MinusMidpointP004Error2654 : ℝ := ((404793822476982939150548061053 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP004BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP004Center2654‖ ≤
          batchC02703MinusMidpointP004Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP004Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP004Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP004Input2654 8 =
      (batchC02703MinusMidpointP004Center2654, ((404793822476982939150548061053 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP004Input2654 8).2 : ℝ) =
      batchC02703MinusMidpointP004Error2654 := by
    rw [hs]
    norm_num [batchC02703MinusMidpointP004Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP004Input2654 hz 8
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^8 * embedPair2542
          batchC02703MinusMidpointP004Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP004Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP004DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP004Factor2654 * embedPair2542
          batchC02703MinusMidpointP004Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP004Factor2654 : ℝ) *
            batchC02703MinusMidpointP004Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP004Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP004Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP004BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP004Factor2654)

def batchC02703MinusMidpointP005Center2654 : RatPair2542 := (0, 0)

def batchC02703MinusMidpointP005Factor2654 : RatPair2542 := (0, 0)

noncomputable def batchC02703MinusMidpointP005Error2654 : ℝ := 0

theorem batchC02703MinusMidpointP005Exterior2654 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703MinusMidpointPosition2654 = 0 :=
        by
  have hx : storedWidth ⟨5, by omega⟩ ^ 2 ≤ |batchC02703MinusMidpointPosition2654| := by
    norm_num [storedWidth, batchC02703MinusMidpointPosition2654]
  exact weightedFamily_outside_zero2543 n (-1/2) (nodeModulation2541 ⟨5, by omega⟩)
    (pow_pos (storedWidth_pos ⟨5, by omega⟩) 2) hx

theorem batchC02703MinusMidpointP005BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP005Center2654‖ ≤
          batchC02703MinusMidpointP005Error2654 := by
  rw [batchC02703MinusMidpointP005Exterior2654]
  norm_num [batchC02703MinusMidpointP005Center2654, batchC02703MinusMidpointP005Error2654,
      batchC02703MinusMidpointZero2654]

theorem batchC02703MinusMidpointP005DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP005Factor2654 * embedPair2542
          batchC02703MinusMidpointP005Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP005Factor2654 : ℝ) *
            batchC02703MinusMidpointP005Error2654 := by
  rw [batchC02703MinusMidpointP005Exterior2654]
  norm_num [batchC02703MinusMidpointP005Factor2654, batchC02703MinusMidpointP005Center2654,
      batchC02703MinusMidpointP005Error2654,
      batchC02703MinusMidpointZero2654, pairMagnitude2542]

def batchC02703MinusMidpointP006Input2654 : RatPair2542 :=
    ((((-1009428092593926457380865987939173537) : ℚ) /
        1768181925932868714734839398400000000),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP006Center2654 : RatPair2542 := (((26883824737354423 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP006Factor2654 : RatPair2542 := (((((4071090421578219 * 10^40
        + 3046410394279833499635372981911572273568) * 10^40
        + 2990094374375914774196473074014740023041) : ℚ) /
        ((827957589354 * 10^40
        + 2620074908263472570046885954478345606089) * 10^40
        + 602636945803179096785892296058960092164)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP006Error2654 : ℝ := ((8895293114767 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP006BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP006Center2654‖ ≤
          batchC02703MinusMidpointP006Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP006Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP006Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP006Input2654 7 =
      (batchC02703MinusMidpointP006Center2654, ((8895293114767 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP006Input2654 7).2 : ℝ) =
      batchC02703MinusMidpointP006Error2654 := by
    rw [hs]
    norm_num [batchC02703MinusMidpointP006Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP006Input2654 hz 7
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^7 * embedPair2542
          batchC02703MinusMidpointP006Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP006Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP006DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP006Factor2654 * embedPair2542
          batchC02703MinusMidpointP006Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP006Factor2654 : ℝ) *
            batchC02703MinusMidpointP006Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP006Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP006Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP006BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP006Factor2654)

def batchC02703MinusMidpointP007Input2654 : RatPair2542 := ((((-((6741902 * 10^40
        + 4502746968753472778979071172993835788977) * 10^40
        + 4785113362794939861150963129495002694047)) : ℚ) /
        ((9977330 * 10^40
        + 8043274648764579609962494407134115555679) * 10^40
        + 4268849461140315310139646161715200000000)),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP007Center2654 : RatPair2542 := (((241661989992022089411994152701 : ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP007Factor2654 : RatPair2542 := ((((((((((2366401621824506055 * 10^40
        + 7630479700911177936403721043330179031705) * 10^40
        + 9395478918911093528566332832112333032212) * 10^40
        + 1952656918616801753599209642164982178364) * 10^40
        + 8342330682176256869462465776247320677998) * 10^40
        + 2579841195589826359397471727743041157216) * 10^40
        + 8807591378861194303605951890678238886231) * 10^40
        + 1400069354830927378705834711869370396161) : ℚ) /
        (((((((13430054441389972 * 10^40
        + 2391531057807732993606177861224085965674) * 10^40
        + 4541038191545642410236064673779875047485) * 10^40
        + 2974384389092509867159402550158979206813) * 10^40
        + 9055339083166401027717051401113358631398) * 10^40
        + 6387680231754923059765005555281878603047) * 10^40
        + 8698142665837978369254917285640268386974) * 10^40
        + 4859669419323709514823338847477481584644)),
    ((0 : ℚ) /
        1))

noncomputable def batchC02703MinusMidpointP007Error2654 : ℝ := ((33423390781133109051567861 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP007BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP007Center2654‖ ≤
          batchC02703MinusMidpointP007Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP007Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP007Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP007Input2654 6 =
      (batchC02703MinusMidpointP007Center2654, ((33423390781133109051567861 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP007Input2654 6).2 : ℝ) =
      batchC02703MinusMidpointP007Error2654 := by
    rw [hs]
    norm_num [batchC02703MinusMidpointP007Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP007Input2654 hz 6
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^6 * embedPair2542
          batchC02703MinusMidpointP007Input2654)
          := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP007Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP007DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP007Factor2654 * embedPair2542
          batchC02703MinusMidpointP007Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP007Factor2654 : ℝ) *
            batchC02703MinusMidpointP007Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP007Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP007Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP007BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP007Factor2654)

def batchC02703MinusMidpointP008Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1260154782678093206550844401 : ℚ) /
        472236648286964521369600000000))

def batchC02703MinusMidpointP008Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP008Factor2654 : RatPair2542 := (((((((((((595044 * 10^40
        + 9511886320417698812235059176045659534856) * 10^40
        + 496613998233975091002150299283860339275) * 10^40
        + 1407313522331424690454978007275869332882) * 10^40
        + 4021075882592196281260004820541053255719) * 10^40
        + 9841542999298396506910497435347784798418) * 10^40
        + 9687623244240492974972358791156161974992) * 10^40
        + 8382084541453212213826522974782734373831) * 10^40
        + 9127808763599284465671455522320825945375) : ℚ) /
        (((((((1110439080628680299099986960941600 * 10^40
        + 2657103405942841666364752370186768464667) * 10^40
        + 9270380565708012113814295317813744068646) * 10^40
        + 698111232335582801608470202915489884157) * 10^40
        + 8865146144447876850326522351656108407076) * 10^40
        + 9011902430559518560961483140217351149084) * 10^40
        + 8268336972108683727698227758310661785228) * 10^40
        + 5006197847838498008632702395573229060096)),
    (((-((((21808 * 10^40
        + 9184518215723137210280023394080164975234) * 10^40
        + 1636950392389465614169495813688652371087) * 10^40
        + 8045965150054602203913089318521256379160) * 10^40
        + 7475216192493995457967920654843235907343)) : ℚ) /
        (((3332325135140147603871227328263866455 * 10^40
        + 5005702969657625053787045271971239654632) * 10^40
        + 2635559150742289720293477249947721890321) * 10^40
        + 8490702832146132629431562715473364647936)))

noncomputable def batchC02703MinusMidpointP008Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP008BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP008Center2654‖ ≤
          batchC02703MinusMidpointP008Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP008Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP008Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP008Input2654 14 =
      (batchC02703MinusMidpointP008Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP008Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP008Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP008Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP008Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP008Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP008Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP008DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP008Factor2654 * embedPair2542
          batchC02703MinusMidpointP008Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP008Factor2654 : ℝ) *
            batchC02703MinusMidpointP008Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP008Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP008Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP008BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP008Factor2654)

def batchC02703MinusMidpointP009Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1874180327301030250642993263 : ℚ) /
        472236648286964521369600000000))

def batchC02703MinusMidpointP009Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP009Factor2654 : RatPair2542 := (((((((((((595044 * 10^40
        + 9511617443478332017858183520943323718232) * 10^40
        + 1431691172605909024557198536034391626472) * 10^40
        + 2595539232799377357158074451913675741298) * 10^40
        + 3980383319084582681756644265614687561567) * 10^40
        + 6553862455404097915408693960225318469512) * 10^40
        + 7057476978616049209959388677469776968707) * 10^40
        + 8229024599315800386679477192495794002798) * 10^40
        + 6822839502587583725217309693687241074143) : ℚ) /
        (((((((1110439080628680299099986960941600 * 10^40
        + 2657103405942841666364752370186768464667) * 10^40
        + 9270380565708012113814295317813744068646) * 10^40
        + 698111232335582801608470202915489884157) * 10^40
        + 8865146144447876850326522351656108407076) * 10^40
        + 9011902430559518560961483140217351149084) * 10^40
        + 8268336972108683727698227758310661785228) * 10^40
        + 5006197847838498008632702395573229060096)),
    (((-((((1046 * 10^40
        + 3088954642831138413225650190697775071535) * 10^40
        + 9360636178488561456417504262737308367433) * 10^40
        + 5081134900766240001291366686229831043950) * 10^40
        + 9087472418211622533884036545288961967439)) : ℚ) /
        (((107494359198069277544233139621415046 * 10^40
        + 9516312999021213711412485331353910956601) * 10^40
        + 407598682282009345815918620966055544849) * 10^40
        + 919054930069230084820372990821721440256)))

noncomputable def batchC02703MinusMidpointP009Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP009BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP009Center2654‖ ≤
          batchC02703MinusMidpointP009Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP009Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP009Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP009Input2654 14 =
      (batchC02703MinusMidpointP009Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP009Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP009Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP009Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP009Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP009Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP009Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP009DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP009Factor2654 * embedPair2542
          batchC02703MinusMidpointP009Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP009Factor2654 : ℝ) *
            batchC02703MinusMidpointP009Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP009Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP009Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP009BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP009Factor2654)

def batchC02703MinusMidpointP010Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1114897936905804466764951993 : ℚ) /
        236118324143482260684800000000))

def batchC02703MinusMidpointP010Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP010Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2377853387039079055843118908210211705564) * 10^40
        + 6082366984191790438370599340089683043528) * 10^40
        + 8586107140082185855019535563771811264428) * 10^40
        + 1218514554574286258491711477825298509733) * 10^40
        + 6128854886574482946831571159882077008289) * 10^40
        + 8013574220984106616621570416111604745168) * 10^40
        + 1111579582945050508431753179923198143324) * 10^40
        + 4649300156884445394214248222747074674255) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((19295 * 10^40
        + 251209688118352575868517330095996654317) * 10^40
        + 3903995162642359760853997598919738296447) * 10^40
        + 4585465752645214754054638784004905919248) * 10^40
        + 1748995792288641673786849504129894428999)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703MinusMidpointP010Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP010BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP010Center2654‖ ≤
          batchC02703MinusMidpointP010Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP010Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP010Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP010Input2654 14 =
      (batchC02703MinusMidpointP010Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP010Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP010Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP010Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP010Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP010Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP010Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP010DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP010Factor2654 * embedPair2542
          batchC02703MinusMidpointP010Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP010Factor2654 : ℝ) *
            batchC02703MinusMidpointP010Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP010Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP010Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP010BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP010Factor2654)

def batchC02703MinusMidpointP011Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1233447703055322478455772233 : ℚ) /
        236118324143482260684800000000))

def batchC02703MinusMidpointP011Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP011Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2377814492877895032675485996926066253501) * 10^40
        + 3853831165340520691961981370385727740570) * 10^40
        + 5248023673148915517769539193374007687173) * 10^40
        + 504953040337304670815818106319988373149) * 10^40
        + 5185563186287662697296185165915317433540) * 10^40
        + 6807901200031395902421589118439424092383) * 10^40
        + 4272829271112226582075091167291241464144) * 10^40
        + 1965174367728967301769988133708489480495) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((21346 * 10^40
        + 7113248990535718065199967483939910122648) * 10^40
        + 9739029009273506923516046362167060011786) * 10^40
        + 9791210928274351705662990135250428298864) * 10^40
        + 6736782627735230538049480463370431643319)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703MinusMidpointP011Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP011BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP011Center2654‖ ≤
          batchC02703MinusMidpointP011Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP011Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP011Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP011Input2654 14 =
      (batchC02703MinusMidpointP011Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP011Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP011Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP011Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP011Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP011Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP011Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP011DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP011Factor2654 * embedPair2542
          batchC02703MinusMidpointP011Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP011Factor2654 : ℝ) *
            batchC02703MinusMidpointP011Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP011Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP011Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP011BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP011Factor2654)

def batchC02703MinusMidpointP012Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((27124724943668121973688997 : ℚ) /
        4722366482869645213696000000))

def batchC02703MinusMidpointP012Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP012Factor2654 : RatPair2542 := (((((((((((37190 * 10^40
        + 3094442516998417883527524063864680090250) * 10^40
        + 8965112239619440688947144559858733942114) * 10^40
        + 3907900013316356174460734997047860468999) * 10^40
        + 9817441275286604904587339890445509693353) * 10^40
        + 4561032091825323911468071671884784825984) * 10^40
        + 1820011823487711109105628850675306274841) * 10^40
        + 8327832917739614078746325426674904282567) * 10^40
        + 4344709867483473608836028814226512928439) : ℚ) /
        (((((((69402442539292518693749185058850 * 10^40
        + 166068962871427604147797023136673029041) * 10^40
        + 7454398785356750757113393457363359004290) * 10^40
        + 3793631952020973925100529387682218117759) * 10^40
        + 8679071634027992303145407646978506775442) * 10^40
        + 3063243901909969910060092696263584446817) * 10^40
        + 8016771060756792732981139234894416361576) * 10^40
        + 7812887365489906125539543899723326816256)),
    (((-((((11735 * 10^40
        + 8780535546108161048756128841499913183491) * 10^40
        + 8842577313058082170942704015283587130758) * 10^40
        + 2545147103095217412865346317557575689006) * 10^40
        + 2110795118663289511077394716687741314275)) : ℚ) /
        (((833081283785036900967806832065966613 * 10^40
        + 8751425742414406263446761317992809913658) * 10^40
        + 658889787685572430073369312486930472580) * 10^40
        + 4622675708036533157357890678868341161984)))

noncomputable def batchC02703MinusMidpointP012Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP012BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP012Center2654‖ ≤
          batchC02703MinusMidpointP012Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP012Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP012Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP012Input2654 14 =
      (batchC02703MinusMidpointP012Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP012Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP012Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP012Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP012Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP012Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP012Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP012DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP012Factor2654 * embedPair2542
          batchC02703MinusMidpointP012Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP012Factor2654 : ℝ) *
            batchC02703MinusMidpointP012Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP012Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP012Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP012BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP012Factor2654)

def batchC02703MinusMidpointP013Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((293626334869738940090135403 : ℚ) /
        47223664828696452136960000000))

def batchC02703MinusMidpointP013Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP013Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2377725915493777823133876332866325274788) * 10^40
        + 1082049087595250389813896780799330572800) * 10^40
        + 4775064279270027635407831741912429999300) * 10^40
        + 1225718528679948132873284709347936751248) * 10^40
        + 514383528246370895140191008615903385294) * 10^40
        + 8550823802232445761352437904741430369158) * 10^40
        + 5204149074141225292565832262635445899486) * 10^40
        + 7960391872920369675067821812058804725231) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((25408 * 10^40
        + 2787309359005387391591352845958219001033) * 10^40
        + 6130179280504842765768823331233158732941) * 10^40
        + 3277118210242114980931103482713577743207) * 10^40
        + 9432385424328117192628498834094962183145)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703MinusMidpointP013Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP013BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP013Center2654‖ ≤
          batchC02703MinusMidpointP013Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP013Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP013Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP013Input2654 14 =
      (batchC02703MinusMidpointP013Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP013Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP013Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP013Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP013Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP013Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP013Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP013DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP013Factor2654 * embedPair2542
          batchC02703MinusMidpointP013Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP013Factor2654 : ℝ) *
            batchC02703MinusMidpointP013Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP013Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP013Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP013BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP013Factor2654)

def batchC02703MinusMidpointP014Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1675462440708706317018938163 : ℚ) /
        236118324143482260684800000000))

def batchC02703MinusMidpointP014Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP014Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2377634858793254429862206944550752898678) * 10^40
        + 7904548014248852640892274587298680602632) * 10^40
        + 7174428409961677071624513751675129772117) * 10^40
        + 6629496854106486562553780288674968741393) * 10^40
        + 901744310430409648329455853807483258046) * 10^40
        + 5904542070058772552695703288360530056698) * 10^40
        + 8228864728925240276471761232088055261620) * 10^40
        + 6049810294842652054097480750495303522775) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((28996 * 10^40
        + 4568168768111582432741920460246365098386) * 10^40
        + 758256886812083334601100739562807910286) * 10^40
        + 7358768639185458585698809068821605427947) * 10^40
        + 657106942525932860709845172516895311309)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703MinusMidpointP014Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP014BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP014Center2654‖ ≤
          batchC02703MinusMidpointP014Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP014Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP014Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP014Input2654 14 =
      (batchC02703MinusMidpointP014Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP014Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP014Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP014Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP014Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP014Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP014Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP014DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP014Factor2654 * embedPair2542
          batchC02703MinusMidpointP014Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP014Factor2654 : ℝ) *
            batchC02703MinusMidpointP014Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP014Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP014Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP014BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP014Factor2654)

def batchC02703MinusMidpointP015Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1824015640458731668997834151 : ℚ) /
        236118324143482260684800000000))

def batchC02703MinusMidpointP015Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP015Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2377562230309480871671105255880787924799) * 10^40
        + 1397916138868459995050626882638660421641) * 10^40
        + 9437231465866694260135490720994097702350) * 10^40
        + 5847824068632704086340433563779782614887) * 10^40
        + 3966488555302207178522245624446680034891) * 10^40
        + 3811097983554526459003792468571635582378) * 10^40
        + 5955855329368680871075067256349499341716) * 10^40
        + 9837858725232953537302569695203919438607) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((31567 * 10^40
        + 3986278662849148489268210291526473938448) * 10^40
        + 8045289916586266146816522745918461470518) * 10^40
        + 5208554078123201476878644316073472292698) * 10^40
        + 1590482423880836589179274605417085941593)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703MinusMidpointP015Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP015BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP015Center2654‖ ≤
          batchC02703MinusMidpointP015Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP015Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP015Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP015Input2654 14 =
      (batchC02703MinusMidpointP015Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP015Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP015Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP015Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP015Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP015Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP015Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP015DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP015Factor2654 * embedPair2542
          batchC02703MinusMidpointP015Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP015Factor2654 : ℝ) *
            batchC02703MinusMidpointP015Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP015Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP015Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP015BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP015Factor2654)

def batchC02703MinusMidpointP016Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((965685891782551182861078297 : ℚ) /
        118059162071741130342400000000))

def batchC02703MinusMidpointP016Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP016Factor2654 : RatPair2542 := (((((((((((37190 * 10^40
        + 3094376476258077818494250455503617261641) * 10^40
        + 1324052242629519277945377323057321884796) * 10^40
        + 7491915307509330481924523228902856828331) * 10^40
        + 7820230374956359923668236152780002830249) * 10^40
        + 7223433867391847396940783888033427658632) * 10^40
        + 6459343317874285160354933938058441564720) * 10^40
        + 420759825459851725844842609354496204502) * 10^40
        + 5374027816447252732550797682411057358223) : ℚ) /
        (((((((69402442539292518693749185058850 * 10^40
        + 166068962871427604147797023136673029041) * 10^40
        + 7454398785356750757113393457363359004290) * 10^40
        + 3793631952020973925100529387682218117759) * 10^40
        + 8679071634027992303145407646978506775442) * 10^40
        + 3063243901909969910060092696263584446817) * 10^40
        + 8016771060756792732981139234894416361576) * 10^40
        + 7812887365489906125539543899723326816256)),
    (((-((((16712 * 10^40
        + 6809765401462649427020694764688499290439) * 10^40
        + 6142230894840230754338941617943359705287) * 10^40
        + 9906328213871565002878238918862076176384) * 10^40
        + 6623733424983427964894071506853055722471)) : ℚ) /
        (((833081283785036900967806832065966613 * 10^40
        + 8751425742414406263446761317992809913658) * 10^40
        + 658889787685572430073369312486930472580) * 10^40
        + 4622675708036533157357890678868341161984)))

noncomputable def batchC02703MinusMidpointP016Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP016BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP016Center2654‖ ≤
          batchC02703MinusMidpointP016Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP016Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP016Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP016Input2654 14 =
      (batchC02703MinusMidpointP016Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP016Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP016Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP016Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP016Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP016Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP016Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP016DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP016Factor2654 * embedPair2542
          batchC02703MinusMidpointP016Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP016Factor2654 : ℝ) *
            batchC02703MinusMidpointP016Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP016Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP016Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP016BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP016Factor2654)

def batchC02703MinusMidpointP017Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((2139904379798294298276928491 : ℚ) /
        236118324143482260684800000000))

def batchC02703MinusMidpointP017Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP017Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2377387293695108829105195894175524960173) * 10^40
        + 6167020039667569885075580000029206240028) * 10^40
        + 1598044302689345282551683841974033662123) * 10^40
        + 1415867198200163904919768456139441233797) * 10^40
        + 7827529576188783746378236772859669935451) * 10^40
        + 7236889287776580059200500267795817873547) * 10^40
        + 6516064285014102520397228664357671194792) * 10^40
        + 8386190828868678699810359395236474018887) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((37034 * 10^40
        + 3395551262402867619517360050759035998916) * 10^40
        + 4879443967906905171342655500958057282411) * 10^40
        + 123555454251075395052750170844308191312) * 10^40
        + 6316623161179664614513501582078234152213)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703MinusMidpointP017Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP017BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP017Center2654‖ ≤
          batchC02703MinusMidpointP017Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP017Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP017Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP017Input2654 14 =
      (batchC02703MinusMidpointP017Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP017Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP017Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP017Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP017Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP017Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP017Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP017DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP017Factor2654 * embedPair2542
          batchC02703MinusMidpointP017Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP017Factor2654 : ℝ) *
            batchC02703MinusMidpointP017Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP017Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP017Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP017BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP017Factor2654)

def batchC02703MinusMidpointP018Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((554686529274626395045879629 : ℚ) /
        59029581035870565171200000000))

def batchC02703MinusMidpointP018Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP018Factor2654 : RatPair2542 := (((((((((((9297 * 10^40
        + 5773583705243277586594424995420028804760) * 10^40
        + 5182966143699487480259692205001770883028) * 10^40
        + 4020507743990833377970961434985848605816) * 10^40
        + 7212931758580410267644422854180029196075) * 10^40
        + 4947067936821937130282568809007603684519) * 10^40
        + 4291328800715125488025049104190003698272) * 10^40
        + 3864123602854609007023542655551597067992) * 10^40
        + 4769507831844831046157632400830702037207) : ℚ) /
        (((((((17350610634823129673437296264712 * 10^40
        + 5041517240717856901036949255784168257260) * 10^40
        + 4363599696339187689278348364340839751072) * 10^40
        + 5948407988005243481275132346920554529439) * 10^40
        + 9669767908506998075786351911744626693860) * 10^40
        + 5765810975477492477515023174065896111704) * 10^40
        + 4504192765189198183245284808723604090394) * 10^40
        + 1953221841372476531384885974930831704064)),
    (((-((((9599 * 10^40
        + 7042978842356676479263066107961556128037) * 10^40
        + 2980710011135274027524850760129623729272) * 10^40
        + 1368971216360877961751389103951658989352) * 10^40
        + 752256899933076549950925626940586368947)) : ℚ) /
        (((416540641892518450483903416032983306 * 10^40
        + 9375712871207203131723380658996404956829) * 10^40
        + 329444893842786215036684656243465236290) * 10^40
        + 2311337854018266578678945339434170580992)))

noncomputable def batchC02703MinusMidpointP018Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP018BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP018Center2654‖ ≤
          batchC02703MinusMidpointP018Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP018Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP018Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP018Input2654 14 =
      (batchC02703MinusMidpointP018Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP018Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP018Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP018Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP018Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP018Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP018Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP018DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP018Factor2654 * embedPair2542
          batchC02703MinusMidpointP018Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP018Factor2654 : ℝ) *
            batchC02703MinusMidpointP018Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP018Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP018Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP018BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP018Factor2654)

def batchC02703MinusMidpointP019Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((118061729677797542810828703 : ℚ) /
        11805916207174113034240000000))

def batchC02703MinusMidpointP019Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP019Factor2654 : RatPair2542 := (((((((((((9297 * 10^40
        + 5773578006946052349775733355751781296382) * 10^40
        + 4335690715242413985762342147436647342615) * 10^40
        + 7866891664725674125548954447542319425644) * 10^40
        + 5016278387280527496951276313081069651106) * 10^40
        + 9939209228529898222698369418215897177978) * 10^40
        + 9930240751938682735899037462442455009110) * 10^40
        + 8029131745145320946462472848963970336234) * 10^40
        + 2964767659807654970696193945193332829991) : ℚ) /
        (((((((17350610634823129673437296264712 * 10^40
        + 5041517240717856901036949255784168257260) * 10^40
        + 4363599696339187689278348364340839751072) * 10^40
        + 5948407988005243481275132346920554529439) * 10^40
        + 9669767908506998075786351911744626693860) * 10^40
        + 5765810975477492477515023174065896111704) * 10^40
        + 4504192765189198183245284808723604090394) * 10^40
        + 1953221841372476531384885974930831704064)),
    (((-((((329 * 10^40
        + 5548357229606262235486591762063762100444) * 10^40
        + 9053902061844886540414312517847683074905) * 10^40
        + 3997947190610725960926402454294505660024) * 10^40
        + 43387742284535901619007048259344028795)) : ℚ) /
        (((13436794899758659693029142452676880 * 10^40
        + 8689539124877651713926560666419238869575) * 10^40
        + 1300949835285251168226989827620756943106) * 10^40
        + 1364881866258653760602546623852715180032)))

noncomputable def batchC02703MinusMidpointP019Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP019BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP019Center2654‖ ≤
          batchC02703MinusMidpointP019Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP019Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP019Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP019Input2654 14 =
      (batchC02703MinusMidpointP019Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP019Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP019Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP019Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP019Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP019Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP019Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP019DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP019Factor2654 * embedPair2542
          batchC02703MinusMidpointP019Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP019Factor2654 : ℝ) *
            batchC02703MinusMidpointP019Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP019Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP019Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP019BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP019Factor2654)

def batchC02703MinusMidpointP020Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((2516179419352937322532008027 : ℚ) /
        236118324143482260684800000000))

def batchC02703MinusMidpointP020Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP020Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2377142529500369780061455623986112251336) * 10^40
        + 5491772987561492212637254671877690818396) * 10^40
        + 6735780394712814145423998505010966236851) * 10^40
        + 9046469034032578568173005933195931697111) * 10^40
        + 6345901753474834920242052859621001496908) * 10^40
        + 4087321233906667133096588025920508199488) * 10^40
        + 5149089326935243139574210757680093126870) * 10^40
        + 4527174895459311752924793284229434688935) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((43546 * 10^40
        + 3583689289010067897170719033072882111124) * 10^40
        + 8743849193711718527857801978780211682334) * 10^40
        + 5711316753881642946952801542221899197148) * 10^40
        + 7850371945403749539328395445065850013861)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703MinusMidpointP020Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP020BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP020Center2654‖ ≤
          batchC02703MinusMidpointP020Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP020Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP020Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP020Input2654 14 =
      (batchC02703MinusMidpointP020Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP020Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP020Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP020Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP020Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP020Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP020Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP020DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP020Factor2654 * embedPair2542
          batchC02703MinusMidpointP020Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP020Factor2654 : ℝ) *
            batchC02703MinusMidpointP020Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP020Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP020Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP020BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP020Factor2654)

def batchC02703MinusMidpointP021Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((2645486933342248857784813371 : ℚ) /
        236118324143482260684800000000))

def batchC02703MinusMidpointP021Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP021Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2377049282390476233854512010180133038120) * 10^40
        + 8177973733738692728920866363304013151825) * 10^40
        + 3457372743305418114321872868813648816258) * 10^40
        + 9537236441669677099711849420989204613553) * 10^40
        + 4828580767303814637930836153198688216058) * 10^40
        + 4989292717412829185180881697982021580653) * 10^40
        + 2173805497611138141217553612422331268912) * 10^40
        + 2069662602534254607582133460630173433447) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((1476 * 10^40
        + 9104503282555516884048757732922569490915) * 10^40
        + 1612530228675795383528789742144036787156) * 10^40
        + 2356569624307757315178107653346719607625) * 10^40
        + 723200885078991896495442900542422475163)) : ℚ) /
        (((53747179599034638772116569810707523 * 10^40
        + 4758156499510606855706242665676955478300) * 10^40
        + 5203799341141004672907959310483027772424) * 10^40
        + 5459527465034615042410186495410860720128)))

noncomputable def batchC02703MinusMidpointP021Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP021BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP021Center2654‖ ≤
          batchC02703MinusMidpointP021Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP021Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP021Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP021Input2654 14 =
      (batchC02703MinusMidpointP021Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP021Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP021Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP021Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP021Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP021Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP021Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP021DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP021Factor2654 * embedPair2542
          batchC02703MinusMidpointP021Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP021Factor2654 : ℝ) *
            batchC02703MinusMidpointP021Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP021Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP021Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP021BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP021Factor2654)

def batchC02703MinusMidpointP022Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((542334257496525531427714089 : ℚ) /
        47223664828696452136960000000))

def batchC02703MinusMidpointP022Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP022Factor2654 : RatPair2542 := (((((((((((148761 * 10^40
        + 2376999747466849650178436100111046276792) * 10^40
        + 1871130793273425132723368088223066452117) * 10^40
        + 9760637334337296709630894199716586725179) * 10^40
        + 531806553278998710858432853900483571399) * 10^40
        + 3471043135983666704860859364433229362903) * 10^40
        + 6279537107042630266090350162734982924551) * 10^40
        + 4467221762923726819553174955202842005977) * 10^40
        + 7035698041870132542029236000619896003031) : ℚ) /
        (((((((277609770157170074774996740235400 * 10^40
        + 664275851485710416591188092546692116166) * 10^40
        + 9817595141427003028453573829453436017161) * 10^40
        + 5174527808083895700402117550728872471039) * 10^40
        + 4716286536111969212581630587914027101769) * 10^40
        + 2252975607639879640240370785054337787271) * 10^40
        + 2067084243027170931924556939577665446307) * 10^40
        + 1251549461959624502158175598893307265024)),
    (((-((((46929 * 10^40
        + 6460956745895236605579053262348026176292) * 10^40
        + 6896481000136505851604883453380929733346) * 10^40
        + 9022579260268753996625294722124803697766) * 10^40
        + 5007557760331598400506700499969706883635)) : ℚ) /
        (((1666162567570073801935613664131933227 * 10^40
        + 7502851484828812526893522635985619827316) * 10^40
        + 1317779575371144860146738624973860945160) * 10^40
        + 9245351416073066314715781357736682323968)))

noncomputable def batchC02703MinusMidpointP022Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP022BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP022Center2654‖ ≤
          batchC02703MinusMidpointP022Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP022Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP022Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP022Input2654 14 =
      (batchC02703MinusMidpointP022Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP022Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP022Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP022Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP022Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP022Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP022Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP022DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP022Factor2654 * embedPair2542
          batchC02703MinusMidpointP022Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP022Factor2654 : ℝ) *
            batchC02703MinusMidpointP022Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP022Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP022Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP022BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP022Factor2654)

def batchC02703MinusMidpointP023Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1451246539493341798322821389 : ℚ) /
        118059162071741130342400000000))

def batchC02703MinusMidpointP023Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP023Factor2654 : RatPair2542 := (((((((((((37190 * 10^40
        + 3094212519364738519712001063340731322742) * 10^40
        + 5518558373286992403044793349167470144861) * 10^40
        + 7074635616043786122776759919576846579737) * 10^40
        + 3812467483512099431146408044968296487732) * 10^40
        + 1686495112650737631222344619797952668163) * 10^40
        + 9055777341125812175965401445242076089734) * 10^40
        + 7910798968348548563622178669162847084384) * 10^40
        + 4694875937375457116935276221254790830935) : ℚ) /
        (((((((69402442539292518693749185058850 * 10^40
        + 166068962871427604147797023136673029041) * 10^40
        + 7454398785356750757113393457363359004290) * 10^40
        + 3793631952020973925100529387682218117759) * 10^40
        + 8679071634027992303145407646978506775442) * 10^40
        + 3063243901909969910060092696263584446817) * 10^40
        + 8016771060756792732981139234894416361576) * 10^40
        + 7812887365489906125539543899723326816256)),
    (((-((((25116 * 10^40
        + 554785463802802653353324791195406866381) * 10^40
        + 8769705461971328406521126370122884376608) * 10^40
        + 347649370516797836488543630573291948375) * 10^40
        + 3637043371109748034075049974054435120627)) : ℚ) /
        (((833081283785036900967806832065966613 * 10^40
        + 8751425742414406263446761317992809913658) * 10^40
        + 658889787685572430073369312486930472580) * 10^40
        + 4622675708036533157357890678868341161984)))

noncomputable def batchC02703MinusMidpointP023Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP023BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP023Center2654‖ ≤
          batchC02703MinusMidpointP023Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP023Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP023Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP023Input2654 14 =
      (batchC02703MinusMidpointP023Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP023Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP023Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP023Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP023Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP023Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP023Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP023DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP023Factor2654 * embedPair2542
          batchC02703MinusMidpointP023Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP023Factor2654 : ℝ) *
            batchC02703MinusMidpointP023Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP023Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP023Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP023BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP023Factor2654)

def batchC02703MinusMidpointP024Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((1495093523437065373217234451 : ℚ) /
        118059162071741130342400000000))

def batchC02703MinusMidpointP024Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP024Factor2654 : RatPair2542 := (((((((((((37190 * 10^40
        + 3094194470732912434872796708729358407574) * 10^40
        + 7482721431658378817644340163238115036843) * 10^40
        + 7164464244606204302048954699865104106495) * 10^40
        + 2505767197182772403116838942866703234455) * 10^40
        + 6864634929883573954810634100291142335221) * 10^40
        + 9948358751750161103714347335824558358015) * 10^40
        + 888985045977941093929876092473046861338) * 10^40
        + 8930326729541336038736196981631257637015) : ℚ) /
        (((((((69402442539292518693749185058850 * 10^40
        + 166068962871427604147797023136673029041) * 10^40
        + 7454398785356750757113393457363359004290) * 10^40
        + 3793631952020973925100529387682218117759) * 10^40
        + 8679071634027992303145407646978506775442) * 10^40
        + 3063243901909969910060092696263584446817) * 10^40
        + 8016771060756792732981139234894416361576) * 10^40
        + 7812887365489906125539543899723326816256)),
    (((-((((25874 * 10^40
        + 8950356639227962951813409799126394472687) * 10^40
        + 8772198988639777903653679568219562457129) * 10^40
        + 4774988486160249293086467003899906293359) * 10^40
        + 8693541181310099080156377554884647584493)) : ℚ) /
        (((833081283785036900967806832065966613 * 10^40
        + 8751425742414406263446761317992809913658) * 10^40
        + 658889787685572430073369312486930472580) * 10^40
        + 4622675708036533157357890678868341161984)))

noncomputable def batchC02703MinusMidpointP024Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP024BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP024Center2654‖ ≤
          batchC02703MinusMidpointP024Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP024Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP024Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP024Input2654 14 =
      (batchC02703MinusMidpointP024Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP024Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP024Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP024Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP024Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP024Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP024Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP024DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP024Factor2654 * embedPair2542
          batchC02703MinusMidpointP024Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP024Factor2654 : ℝ) *
            batchC02703MinusMidpointP024Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP024Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP024Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP024BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP024Factor2654)

def batchC02703MinusMidpointP025Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((48439674860800074916295889 : ℚ) /
        3689348814741910323200000000))

def batchC02703MinusMidpointP025Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP025Factor2654 : RatPair2542 := (((((((((((36 * 10^40
        + 3186615401447304354946079825189717217611) * 10^40
        + 1296129247081480309298662239859963460701) * 10^40
        + 846840250085691371562815628228308535279) * 10^40
        + 1154514048397490425751575542551098280589) * 10^40
        + 4921927485011852284470410235825963543848) * 10^40
        + 9068730701581774989105536657911172704575) * 10^40
        + 1132015136561504790364101665029083861964) * 10^40
        + 14751803847577919573279768646481978207) : ℚ) /
        (((((((67775822792277850286864438534 * 10^40
        + 332193426721554128519675583030406907254) * 10^40
        + 9235795311313824951911243548298206405277) * 10^40
        + 6273235968703145482348730985730158416130) * 10^40
        + 6248710030892605461233540437155252448022) * 10^40
        + 8928772699122958954990293059273694906686) * 10^40
        + 3455094502989020305403301893784076578478) * 10^40
        + 1023254772817861236450722210839573561344)),
    (((-((((838 * 10^40
        + 3231436275096225657995773955092347276412) * 10^40
        + 2950056238157398872025752591496774336552) * 10^40
        + 1857186752596858555017684632921133823344) * 10^40
        + 6553755916031980924609828322466372974127)) : ℚ) /
        (((26033790118282403155243963502061456 * 10^40
        + 6835982054450450195732711291187275309801) * 10^40
        + 8145590305865174138439792791015216577268) * 10^40
        + 1394458615876141661167434083714635661312)))

noncomputable def batchC02703MinusMidpointP025Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP025BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP025Center2654‖ ≤
          batchC02703MinusMidpointP025Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP025Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP025Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP025Input2654 14 =
      (batchC02703MinusMidpointP025Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP025Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP025Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP025Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP025Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP025Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP025Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP025DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP025Factor2654 * embedPair2542
          batchC02703MinusMidpointP025Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP025Factor2654 : ℝ) *
            batchC02703MinusMidpointP025Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP025Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP025Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP025BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP025Factor2654)

def batchC02703MinusMidpointP026Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((100390806713240309485743021 : ℚ) /
        7378697629483820646400000000))

def batchC02703MinusMidpointP026Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP026Factor2654 : RatPair2542 := (((((((((((145 * 10^40
        + 2746461509012601451001434070541953520866) * 10^40
        + 1058637561239913903770542715522189606924) * 10^40
        + 3884952249878445411270194242530262327176) * 10^40
        + 3954987040251388631082679928994537734504) * 10^40
        + 2466425719934866185824930887736425148526) * 10^40
        + 4307393920356045404969068897715770588826) * 10^40
        + 9996733788627807038398583608101490532038) * 10^40
        + 9256236649831396517988362179967341335) : ℚ) /
        (((((((271103291169111401147457754136 * 10^40
        + 1328773706886216514078702332121627629019) * 10^40
        + 6943181245255299807644974193192825621110) * 10^40
        + 5092943874812581929394923942920633664522) * 10^40
        + 4994840123570421844934161748621009792091) * 10^40
        + 5715090796491835819961172237094779626745) * 10^40
        + 3820378011956081221613207575136306313912) * 10^40
        + 4093019091271444945802888843358294245376)),
    (((-((((1737 * 10^40
        + 4174561863532926747034541029468497405232) * 10^40
        + 7724515785893850712592394368812105447371) * 10^40
        + 6232123051279249794970361211063616576092) * 10^40
        + 3958697645364395832602083965393784370003)) : ℚ) /
        (((52067580236564806310487927004122913 * 10^40
        + 3671964108900900391465422582374550619603) * 10^40
        + 6291180611730348276879585582030433154536) * 10^40
        + 2788917231752283322334868167429271322624)))

noncomputable def batchC02703MinusMidpointP026Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP026BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP026Center2654‖ ≤
          batchC02703MinusMidpointP026Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP026Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP026Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP026Input2654 14 =
      (batchC02703MinusMidpointP026Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP026Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP026Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP026Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP026Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP026Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP026Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP026DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP026Factor2654 * embedPair2542
          batchC02703MinusMidpointP026Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP026Factor2654 : ℝ) *
            batchC02703MinusMidpointP026Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP026Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP026Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP026BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP026Factor2654)

def batchC02703MinusMidpointP027Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((210915907231581076143804291 : ℚ) /
        14757395258967641292800000000))

def batchC02703MinusMidpointP027Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP027Factor2654 : RatPair2542 := (((((((((((581 * 10^40
        + 985845453151242705339607644245482601706) * 10^40
        + 5121456714711902305767143581576988973341) * 10^40
        + 1524561960389345473502856390938591470849) * 10^40
        + 6087239323408003271014853259691326532669) * 10^40
        + 7952874762489747666276822431998896768305) * 10^40
        + 4061330369395101923653349503713654935435) * 10^40
        + 8790395017337103585369011152828052862358) * 10^40
        + 933785121505565155946071896711305103607) : ℚ) /
        (((((((1084413164676445604589831016544 * 10^40
        + 5315094827544866056314809328486510516078) * 10^40
        + 7772724981021199230579896772771302484442) * 10^40
        + 371775499250327717579695771682534658089) * 10^40
        + 9979360494281687379736646994484039168366) * 10^40
        + 2860363185967343279844688948379118506981) * 10^40
        + 5281512047824324886452830300545225255649) * 10^40
        + 6372076365085779783211555373433176981504)),
    (((-((((3650 * 10^40
        + 2244678466197474521071068164496344813622) * 10^40
        + 6040465432623397759213756480985875548681) * 10^40
        + 5175346159734206315930517628885358016725) * 10^40
        + 5121471461899650798200159929598413791613)) : ℚ) /
        (((104135160473129612620975854008245826 * 10^40
        + 7343928217801800782930845164749101239207) * 10^40
        + 2582361223460696553759171164060866309072) * 10^40
        + 5577834463504566644669736334858542645248)))

noncomputable def batchC02703MinusMidpointP027Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP027BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP027Center2654‖ ≤
          batchC02703MinusMidpointP027Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP027Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP027Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP027Input2654 14 =
      (batchC02703MinusMidpointP027Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP027Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP027Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP027Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP027Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP027Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP027Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP027DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP027Factor2654 * embedPair2542
          batchC02703MinusMidpointP027Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP027Factor2654 : ℝ) *
            batchC02703MinusMidpointP027Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP027Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP027Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP027BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP027Factor2654)

def batchC02703MinusMidpointP028Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((859712854308450190152717591 : ℚ) /
        59029581035870565171200000000))

def batchC02703MinusMidpointP028Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP028Factor2654 : RatPair2542 := (((((((((((9297 * 10^40
        + 5773523431096670255342518177369224700095) * 10^40
        + 1922427213944740041582770883243640587612) * 10^40
        + 3460441696347192205781182978298516439058) * 10^40
        + 8787625173566134038124491879569407667023) * 10^40
        + 9070036617138252839841987274936207434365) * 10^40
        + 5528544323823169515946875207417793260773) * 10^40
        + 830215618080243746678817852400175733411) * 10^40
        + 7075766111534991410767432872475491044847) : ℚ) /
        (((((((17350610634823129673437296264712 * 10^40
        + 5041517240717856901036949255784168257260) * 10^40
        + 4363599696339187689278348364340839751072) * 10^40
        + 5948407988005243481275132346920554529439) * 10^40
        + 9669767908506998075786351911744626693860) * 10^40
        + 5765810975477492477515023174065896111704) * 10^40
        + 4504192765189198183245284808723604090394) * 10^40
        + 1953221841372476531384885974930831704064)),
    (((-((((14878 * 10^40
        + 6544235060768819816475062673195425229972) * 10^40
        + 3825276855604333702008431217662368670176) * 10^40
        + 1273617614368334739061205634626213076187) * 10^40
        + 9120046485444057113340233115596329793513)) : ℚ) /
        (((416540641892518450483903416032983306 * 10^40
        + 9375712871207203131723380658996404956829) * 10^40
        + 329444893842786215036684656243465236290) * 10^40
        + 2311337854018266578678945339434170580992)))

noncomputable def batchC02703MinusMidpointP028Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP028BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP028Center2654‖ ≤
          batchC02703MinusMidpointP028Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP028Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP028Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP028Input2654 14 =
      (batchC02703MinusMidpointP028Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP028Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP028Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP028Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP028Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP028Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP028Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP028DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP028Factor2654 * embedPair2542
          batchC02703MinusMidpointP028Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP028Factor2654 : ℝ) *
            batchC02703MinusMidpointP028Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP028Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP028Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP028BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP028Factor2654)

def batchC02703MinusMidpointP029Input2654 : RatPair2542 := ((((-((2312471 * 10^40
        + 2655097755127852687431612393404753154076) * 10^40
        + 9638804149026145288666457897561408944047)) : ℚ) /
        ((3650931 * 10^40
        + 4620464447189727540551040626083260477048) * 10^40
        + 152564319075151395749417399091200000000)),
    ((884146769519556836563855947 : ℚ) /
        59029581035870565171200000000))

def batchC02703MinusMidpointP029Center2654 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def batchC02703MinusMidpointP029Factor2654 : RatPair2542 := (((((((((((9297 * 10^40
        + 5773517478228372367278902191481958562833) * 10^40
        + 3920664632574876752363730030295614918426) * 10^40
        + 1764336587520520048470348664277300457660) * 10^40
        + 3066739846247819703937535527656305105347) * 10^40
        + 9323218988037218059066387176796617646443) * 10^40
        + 392874577874525545040251055905294259849) * 10^40
        + 6159854076674716099297095795310129556159) * 10^40
        + 3574052655646302183158618397519082656775) : ℚ) /
        (((((((17350610634823129673437296264712 * 10^40
        + 5041517240717856901036949255784168257260) * 10^40
        + 4363599696339187689278348364340839751072) * 10^40
        + 5948407988005243481275132346920554529439) * 10^40
        + 9669767908506998075786351911744626693860) * 10^40
        + 5765810975477492477515023174065896111704) * 10^40
        + 4504192765189198183245284808723604090394) * 10^40
        + 1953221841372476531384885974930831704064)),
    (((-((((15301 * 10^40
        + 5209408756904637771184993009501471624695) * 10^40
        + 2982083055425221796664582053059263836808) * 10^40
        + 1096746133418363924572610109331505033253) * 10^40
        + 7616302684805761763362765372880391626421)) : ℚ) /
        (((416540641892518450483903416032983306 * 10^40
        + 9375712871207203131723380658996404956829) * 10^40
        + 329444893842786215036684656243465236290) * 10^40
        + 2311337854018266578678945339434170580992)))

noncomputable def batchC02703MinusMidpointP029Error2654 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem batchC02703MinusMidpointP029BaseError2654 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP029Center2654‖ ≤
          batchC02703MinusMidpointP029Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hz : ‖embedPair2542 batchC02703MinusMidpointP029Input2654‖ ≤ 1 := by
    apply complex_norm_le_l1_2541
    norm_num [embedPair2542, batchC02703MinusMidpointP029Input2654]
  have hs : compactExp2547 batchC02703MinusMidpointP029Input2654 14 =
      (batchC02703MinusMidpointP029Center2654, ((2199023255553 : ℚ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))) := by decide +kernel
  have hc := congrArg Prod.fst hs
  have he : ((compactExp2547 batchC02703MinusMidpointP029Input2654 14).2 : ℝ) =
      batchC02703MinusMidpointP029Error2654 :=
      by
    rw [hs]
    norm_num [batchC02703MinusMidpointP029Error2654]
  have h := compactExp_error2547 batchC02703MinusMidpointP029Input2654 hz 14
  rw [hc, he] at h
  have ho : weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
      batchC02703MinusMidpointPosition2654 = Complex.exp ((2 : ℂ)^14 * embedPair2542
          batchC02703MinusMidpointP029Input2654) := by
    simp only [weightedUnitJet2539, iteratedDeriv_zero]
    rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
    congr 1
    apply Complex.ext <;> norm_num [batchC02703MinusMidpointPosition2654, storedWidth,
        nodeModulation2541,
      embedPair2542, batchC02703MinusMidpointP029Input2654, Complex.mul_re, Complex.mul_im]
  rwa [ho]

theorem batchC02703MinusMidpointP029DerivativeError2654 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        batchC02703MinusMidpointPosition2654 -
      embedPair2542 batchC02703MinusMidpointP029Factor2654 * embedPair2542
          batchC02703MinusMidpointP029Center2654‖ ≤
        (pairMagnitude2542 batchC02703MinusMidpointP029Factor2654 : ℝ) *
            batchC02703MinusMidpointP029Error2654 := by
  have hx : |batchC02703MinusMidpointPosition2654| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [batchC02703MinusMidpointPosition2654, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) batchC02703MinusMidpointPosition2654 = embedPair2542
          batchC02703MinusMidpointP029Factor2654 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      batchC02703MinusMidpointPosition2654, storedWidth, nodeModulation2541, embedPair2542,
      batchC02703MinusMidpointP029Factor2654, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ batchC02703MinusMidpointP029BaseError2654
    (embedPair_magnitude2542 batchC02703MinusMidpointP029Factor2654)

theorem batchC02703MinusMidpointGrid2654 :
    -stripRadius2303 + ((5407 : ℝ) /
        2) * (2 * stripRadius2303 / 10240) =
      batchC02703MinusMidpointPosition2654 := by
  norm_num [stripRadius2303, batchC02703MinusMidpointPosition2654]

end ConnesWeilRH.Dev

#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP000DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP001DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP002DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP003DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP004DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP005DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP006DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP007DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP008DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP009DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP010DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP011DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP012DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP013DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP014DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP015DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP016DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP017DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP018DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP019DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP020DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP021DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP022DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP023DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP024DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP025DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP026DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP027DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP028DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointP029DerivativeError2654
#print axioms ConnesWeilRH.Dev.batchC02703MinusMidpointGrid2654
