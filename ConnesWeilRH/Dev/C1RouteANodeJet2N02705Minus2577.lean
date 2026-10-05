import ConnesWeilRH.Dev.C1RouteANodeExpN02705Minus2577

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodeJet2N02705MinusPointPosition2577 : ℝ := (((-31653888483) : ℝ) /
        10240000000)

theorem nodeJet2N02705MinusPointZero2577 : embedPair2542 (0, 0) = 0 := by
  apply Complex.ext <;> norm_num [embedPair2542]

def nodeJet2N02705MinusPointP000Center2577 : RatPair2542 := (0, 0)

def nodeJet2N02705MinusPointP000Factor2577 : RatPair2542 := (0, 0)

noncomputable def nodeJet2N02705MinusPointP000Error2577 : ℝ := 0

theorem nodeJet2N02705MinusPointP000Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705MinusPointPosition2577 = 0 := by
  exact nodeExpN02705MinusPointP000Exterior2577 n

theorem nodeJet2N02705MinusPointP000BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP000Center2577‖ ≤
          nodeJet2N02705MinusPointP000Error2577 := by
  exact nodeExpN02705MinusPointP000BaseError2577

theorem nodeJet2N02705MinusPointP000DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨0, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP000Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP000Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP000Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP000Error2577 := by
  rw [nodeJet2N02705MinusPointP000Exterior2577]
  norm_num [nodeJet2N02705MinusPointP000Factor2577, nodeJet2N02705MinusPointP000Center2577,
      nodeJet2N02705MinusPointP000Error2577,
      nodeJet2N02705MinusPointZero2577, pairMagnitude2542]

def nodeJet2N02705MinusPointP001Input2577 : RatPair2542 :=
    ((((-(2972220902592775860753336338870765187961 *
    10^40
        + 1585476530521012854490327853635425132317)) : ℚ) /
        (8511279604154028674011082907130390598740 * 10^40
        + 8004112173150622382000883902709760000000)),
    ((174865292075716174968560007 : ℚ) /
        737869762948382064640000000))

def nodeJet2N02705MinusPointP001Center2577 : RatPair2542 := ((((-1) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP001Factor2577 : RatPair2542 := ((((((((((2887217692484891859274 *
    10^40
        + 886679836763604923085252168554646985739) * 10^40
        + 7486542552432697637594941029194865396741) * 10^40
        + 1518069733670358780561234122811908179648) * 10^40
        + 7040427930445822873422064821970815424657) * 10^40
        + 8469223515252558414094112152822875365471) * 10^40
        + 8020159321792564217647499596885429749896) * 10^40
        + 7410772325625147516484931190488312180055) : ℚ) /
        (((((((8598038200957472 * 10^40
        + 141790292102205354197806213013410962041) * 10^40
        + 1621595586686419268366832641327035700902) * 10^40
        + 8644107106818903029834864907366570427723) * 10^40
        + 2966182222028762433558068143872846920503) * 10^40
        + 9256141228727664788448559272500972010992) * 10^40
        + 8780447658410284346885802049043658572913) * 10^40
        + 8024020628939428337850636823283560873984)),
    (((-(((425283087872729633386251443747682 * 10^40
        + 5802925677923572007457013418443218329780) * 10^40
        + 9625961773053587482733519856452226096839) * 10^40
        + 76949047559627055388919828064618582771)) : ℚ) /
        (((9272560704011309957005710651 * 10^40
        + 8069058291469678712499426532598938186360) * 10^40
        + 2264379892714596108919112878838923781865) * 10^40
        + 733434366566606583015219610970623049728)))

noncomputable def nodeJet2N02705MinusPointP001Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP001BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP001Center2577‖ ≤
          nodeJet2N02705MinusPointP001Error2577 := by
  exact nodeExpN02705MinusPointP001BaseError2577

theorem nodeJet2N02705MinusPointP001DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨1, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP001Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP001Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP001Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP001Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨1, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨1, by omega⟩)
      (storedWidth ⟨1, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP001Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP001Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨1, by omega⟩) (pow_pos (storedWidth_pos ⟨1, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP001BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP001Factor2577)

def nodeJet2N02705MinusPointP002Input2577 : RatPair2542 :=
    ((((-(1558232809265543759449685049388990963208 *
    10^40
        + 5657148282816822161277233008769014177453)) : ℚ) /
        (6677151314258110391825028471093402075161 * 10^40
        + 8148315816099404395428715739217920000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def nodeJet2N02705MinusPointP002Center2577 : RatPair2542 := ((((-6232910466508290662095) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-7671910554999950297919) : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def nodeJet2N02705MinusPointP002Factor2577 : RatPair2542 := ((((((((((3085075762200203053 * 10^40
        + 6072814700135538495746018428650397893868) * 10^40
        + 1837280582076068071520959202602311038984) * 10^40
        + 3603306572017445509368637947760764186427) * 10^40
        + 774213985585593346879043058334044450152) * 10^40
        + 2908786441949417468639403671543982163485) * 10^40
        + 5118411737621580575601390200087670433103) * 10^40
        + 258285359105090417422433686570657464855) : ℚ) /
        (((((((52108046783186561 * 10^40
        + 2517301206754568672051708514103298778758) * 10^40
        + 307278298735271599409957052881096749749) * 10^40
        + 8912157885642591946906725677832695378712) * 10^40
        + 5349668788316479638210476901573947197792) * 10^40
        + 3477780095469449440409070908119974740958) * 10^40
        + 6649761686748851669514236472658946305194) * 10^40
        + 1263766961113092385263524678550866100224)),
    (((((73214433723593302981779069206957 * 10^40
        + 4213172027890799561825160837935364574275) * 10^40
        + 5526010610713136441679481822241752494779) * 10^40
        + 2080704016000371510865980803355104368851) : ℚ) /
        (((22827187032831391170524010701 * 10^40
        + 8575416780773630581938393274919168558414) * 10^40
        + 3060834003913784083951889723658255416479) * 10^40
        + 9528788458481189921638234054314235527168)))

noncomputable def nodeJet2N02705MinusPointP002Error2577 : ℝ := ((62258049251692668505 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP002BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP002Center2577‖ ≤
          nodeJet2N02705MinusPointP002Error2577 := by
  exact nodeExpN02705MinusPointP002BaseError2577

theorem nodeJet2N02705MinusPointP002DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨2, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP002Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP002Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP002Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP002Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨2, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨2, by omega⟩)
      (storedWidth ⟨2, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP002Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP002Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨2, by omega⟩) (pow_pos (storedWidth_pos ⟨2, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP002BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP002Factor2577)

def nodeJet2N02705MinusPointP003Input2577 : RatPair2542 := ((((-((550 * 10^40
        + 3595636945123166861610172112009740757253) * 10^40
        + 4707504622032470410174329256036448054837)) : ℚ) /
        ((3259 * 10^40
        + 8976654890313777338921755240451858920673) * 10^40
        + 3765349097629268219761063158087680000000)),
    (((-174865292075716174968560007) : ℚ) /
        368934881474191032320000000))

def nodeJet2N02705MinusPointP003Center2577 : RatPair2542 := ((((-93385857423547319201975676215) :
    ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    (((-229891941848088526221276769381) : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)))

def nodeJet2N02705MinusPointP003Factor2577 : RatPair2542 :=
    ((((-(((((((40417180757220899214476465196437426 *
    10^40
        + 5260398886056821874691347854016566072837) * 10^40
        + 9262499800574697601502313830260919918041) * 10^40
        + 1079891154693138483786585646739999299715) * 10^40
        + 4113925390295055702237308627344793203701) * 10^40
        + 6754505502487081875998817976005515175295) * 10^40
        + 1609250056949383749442148665187738628057) * 10^40
        + 2520920826868561463882080707237775188745)) : ℚ) /
        (((((((29604367698943771981708558977030 * 10^40
        + 9750626296738597542654141573367848536409) * 10^40
        + 6952446126917018946733924115648897938036) * 10^40
        + 2756621396728156120213212379139513240729) * 10^40
        + 8875828780001173777272969283944059597379) * 10^40
        + 1062944108982617242874876149987906172642) * 10^40
        + 1952814561977408250195797687281132808703) * 10^40
        + 8022754047778734387929287440564217708544)),
    (((((587538668319594083136248914325680752728 * 10^40
        + 6240467155573943299903033960617971971281) * 10^40
        + 1283029367673681608622119889702396815962) * 10^40
        + 1418252549417170678275388563999167221891) : ℚ) /
        (((544098958820394839962216851308212164 * 10^40
        + 4830094983735407052937641969332998957692) * 10^40
        + 6570814641536834032655487643959894692813) * 10^40
        + 1609016050185404464549032956900187045888)))

noncomputable def nodeJet2N02705MinusPointP003Error2577 : ℝ := ((874492453823048358099631199 : ℝ)
    /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP003BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP003Center2577‖ ≤
          nodeJet2N02705MinusPointP003Error2577 := by
  exact nodeExpN02705MinusPointP003BaseError2577

theorem nodeJet2N02705MinusPointP003DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨3, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP003Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP003Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP003Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP003Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨3, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨3, by omega⟩)
      (storedWidth ⟨3, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP003Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP003Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨3, by omega⟩) (pow_pos (storedWidth_pos ⟨3, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP003BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP003Factor2577)

def nodeJet2N02705MinusPointP004Input2577 : RatPair2542 := ((((-((17 * 10^40
        + 2533280590083662039217955279786228756184) * 10^40
        + 5273242798277482655099909987298882195197)) : ℚ) /
        ((119 * 10^40
        + 2496410941960060508819208543369047417438) * 10^40
        + 2834992468434524816007071221678080000000)),
    ((174865292075716174968560007 : ℚ) /
        368934881474191032320000000))

def nodeJet2N02705MinusPointP004Center2577 : RatPair2542 := ((((-5644135271377406361162294963633)
    : ℚ) /
        (18268770 * 10^40
        + 4666362864775460604089535377456991567872)),
    ((55577632561868580858707835001315 : ℚ) /
        (73075081 * 10^40
        + 8665451459101842416358141509827966271488)))

def nodeJet2N02705MinusPointP004Factor2577 : RatPair2542 :=
    ((((-(((((((79600531647045569356087922498 * 10^40
        + 6162727161199266101937409674067221066458) * 10^40
        + 541944693275417769918434658150788388675) * 10^40
        + 7395022921334885120502601610448638188207) * 10^40
        + 974290306752991828109989498943063201971) * 10^40
        + 2398160969064441365624746750483803333632) * 10^40
        + 176908762996339492406347975262579332657) * 10^40
        + 2427994833426599375623716033369696431145)) : ℚ) /
        (((((((53011274345890175698472415 * 10^40
        + 6654196183038584089428426414779223849907) * 10^40
        + 7432821288974638103849279611788523908928) * 10^40
        + 4001249450104118954482731842358523964473) * 10^40
        + 4525496761622166743752808507278718631827) * 10^40
        + 7860437450765645771850202732544696646713) * 10^40
        + 2817322538080545719004856834432560587189) * 10^40
        + 7397138783410592076845762711445437415424)),
    (((-(((379719610352929740038238693408526316 * 10^40
        + 9536459218950010532560042058684826215138) * 10^40
        + 5342082771585448413668125067813724359331) * 10^40
        + 2814572106273141101908312677871214611251)) : ℚ) /
        (((728088417336041513946925114699671 * 10^40
        + 6448650525065914750459888068963248539818) * 10^40
        + 4842754602194513589572666504736055075634) * 10^40
        + 8419119820800285945050012408479500730368)))

noncomputable def nodeJet2N02705MinusPointP004Error2577 : ℝ := ((412739842713913026403732476439 :
    ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP004BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP004Center2577‖ ≤
          nodeJet2N02705MinusPointP004Error2577 := by
  exact nodeExpN02705MinusPointP004BaseError2577

theorem nodeJet2N02705MinusPointP004DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨4, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP004Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP004Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP004Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP004Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨4, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨4, by omega⟩)
      (storedWidth ⟨4, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP004Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP004Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨4, by omega⟩) (pow_pos (storedWidth_pos ⟨4, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP004BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP004Factor2577)

def nodeJet2N02705MinusPointP005Center2577 : RatPair2542 := (0, 0)

def nodeJet2N02705MinusPointP005Factor2577 : RatPair2542 := (0, 0)

noncomputable def nodeJet2N02705MinusPointP005Error2577 : ℝ := 0

theorem nodeJet2N02705MinusPointP005Exterior2577 (n : ℕ) :
    weightedUnitJet2539 n (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705MinusPointPosition2577 = 0 := by
  exact nodeExpN02705MinusPointP005Exterior2577 n

theorem nodeJet2N02705MinusPointP005BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP005Center2577‖ ≤
          nodeJet2N02705MinusPointP005Error2577 := by
  exact nodeExpN02705MinusPointP005BaseError2577

theorem nodeJet2N02705MinusPointP005DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨5, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP005Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP005Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP005Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP005Error2577 := by
  rw [nodeJet2N02705MinusPointP005Exterior2577]
  norm_num [nodeJet2N02705MinusPointP005Factor2577, nodeJet2N02705MinusPointP005Center2577,
      nodeJet2N02705MinusPointP005Error2577,
      nodeJet2N02705MinusPointZero2577, pairMagnitude2542]

def nodeJet2N02705MinusPointP006Input2577 : RatPair2542 :=
    ((((-1009401942711546853650056001574587) : ℚ) /
        1771445797272420243763363840000000),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP006Center2577 : RatPair2542 := (((30816524370707993 : ℚ) /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP006Factor2577 : RatPair2542 := (((((40654778 * 10^40
        + 8079476517179571332053012598922517238815) * 10^40
        + 7080693494276874554484412046433543073441) : ℚ) /
        ((8340 * 10^40
        + 8781515554826815851359804479075949211870) * 10^40
        + 2087085281107477737937648185734172293764)),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP006Error2577 : ℝ := ((4933337008969 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeJet2N02705MinusPointP006BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP006Center2577‖ ≤
          nodeJet2N02705MinusPointP006Error2577 := by
  exact nodeExpN02705MinusPointP006BaseError2577

theorem nodeJet2N02705MinusPointP006DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨6, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP006Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP006Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP006Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP006Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨6, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨6, by omega⟩)
      (storedWidth ⟨6, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP006Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP006Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨6, by omega⟩) (pow_pos (storedWidth_pos ⟨6, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP006BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP006Factor2577)

def nodeJet2N02705MinusPointP007Input2577 : RatPair2542 := ((((-((550 * 10^40
        + 3595636945123166861610172112009740757253) * 10^40
        + 4707504622032470410174329256036448054837)) : ℚ) /
        ((814 * 10^40
        + 9744163722578444334730438810112964730168) * 10^40
        + 3441337274407317054940265789521920000000)),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP007Center2577 : RatPair2542 := (((248135493820243347566162584705 : ℚ)
    /
        (146150163 * 10^40
        + 7330902918203684832716283019655932542976)),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP007Factor2577 : RatPair2542 := ((((((((((1049301 * 10^40
        + 3274792763048739901115086575081197676846) * 10^40
        + 4070622110091933456870316627200743206767) * 10^40
        + 7296305705424418614922399402402664263833) * 10^40
        + 3342327878496767063263427943181730924673) * 10^40
        + 2299404360351255984082981638576816860868) * 10^40
        + 212881636615076890303511179381802072757) * 10^40
        + 1497335003030219196256950393112589401441) : ℚ) /
        (((((((5978 * 10^40
        + 5544451800233632820430742636911568795351) * 10^40
        + 5013096037731222883930865390245520989662) * 10^40
        + 8035436923110592587122265602624292446791) * 10^40
        + 225492355137801418421181923934139379379) * 10^40
        + 1632001303390110722238321314595919717869) * 10^40
        + 12039448580981825715203788649585274557) * 10^40
        + 3967782764120876785027801572450357605764)),
    ((0 : ℚ) /
        1))

noncomputable def nodeJet2N02705MinusPointP007Error2577 : ℝ := ((17152272637126015450671225 : ℝ) /
        (80346902212949513777 * 10^40
        + 981046170581301261101496891396417650688))

theorem nodeJet2N02705MinusPointP007BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP007Center2577‖ ≤
          nodeJet2N02705MinusPointP007Error2577 := by
  exact nodeExpN02705MinusPointP007BaseError2577

theorem nodeJet2N02705MinusPointP007DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨7, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP007Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP007Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP007Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP007Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨7, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨7, by omega⟩)
      (storedWidth ⟨7, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP007Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP007Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨7, by omega⟩) (pow_pos (storedWidth_pos ⟨7, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP007BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP007Factor2577)

def nodeJet2N02705MinusPointP008Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((125937256369443206862002451 : ℚ) /
        23611832414348226068480000000))

def nodeJet2N02705MinusPointP008Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP008Factor2577 : RatPair2542 := (((((((((((1 * 10^40
        + 5212980729688084183361568388853838789451) * 10^40
        + 8951810333983988777597155414777763357764) * 10^40
        + 8731111608792082441987935193753559389582) * 10^40
        + 3193794159090450730299215491742707023534) * 10^40
        + 5456272676917476397066797132170698277858) * 10^40
        + 6728444309657272109711172694418543926456) * 10^40
        + 3073576957709675613824923981230936448148) * 10^40
        + 7479813546722211833085339989618019525375) : ℚ) /
        (((((((11825218843849928641990724182 * 10^40
        + 6943999297503659575328139769073080567729) * 10^40
        + 6273723891841736909889641918079042013623) * 10^40
        + 3014733967897595534920310941846977151147) * 10^40
        + 3990080606724338341689175105281638495792) * 10^40
        + 6435984785894492424799545669541853781057) * 10^40
        + 7607572679484829075704262940569259396357) * 10^40
        + 6729106410213355883014742571241728638976)),
    (((-((((34 * 10^40
        + 8726016779249618306902630132428905512150) * 10^40
        + 3849047305935011552770581269171227899108) * 10^40
        + 9593637293764268627122966629467657738316) * 10^40
        + 1443758530354299470625752027724042670463)) : ℚ) /
        (((10874382209509618225919740204836606 * 10^40
        + 3611089045377415057904678722670245730993) * 10^40
        + 5375498452436832589615588703700504124728) * 10^40
        + 4697252923626309130267766234698194354176)))

noncomputable def nodeJet2N02705MinusPointP008Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP008BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP008Center2577‖ ≤
          nodeJet2N02705MinusPointP008Error2577 := by
  exact nodeExpN02705MinusPointP008BaseError2577

theorem nodeJet2N02705MinusPointP008DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨8, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP008Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP008Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP008Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP008Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨8, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨8, by omega⟩)
      (storedWidth ⟨8, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP008Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP008Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨8, by omega⟩) (pow_pos (storedWidth_pos ⟨8, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP008BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP008Factor2577)

def nodeJet2N02705MinusPointP009Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((187301696272790732683750413 : ℚ) /
        23611832414348226068480000000))

def nodeJet2N02705MinusPointP009Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP009Factor2577 : RatPair2542 := (((((((((((1 * 10^40
        + 5212980726824776591308156064345519695655) * 10^40
        + 3301453293780849554375604495259278912657) * 10^40
        + 7734506766105205858928132979492577116569) * 10^40
        + 2744484506134887289378572719792440145247) * 10^40
        + 3281954299310617104316496056817313591883) * 10^40
        + 4611552055896066235699504030058909328812) * 10^40
        + 8541609861236764184471571358048255633685) * 10^40
        + 1206261439203440545794471448543148725183) : ℚ) /
        (((((((11825218843849928641990724182 * 10^40
        + 6943999297503659575328139769073080567729) * 10^40
        + 6273723891841736909889641918079042013623) * 10^40
        + 3014733967897595534920310941846977151147) * 10^40
        + 3990080606724338341689175105281638495792) * 10^40
        + 6435984785894492424799545669541853781057) * 10^40
        + 7607572679484829075704262940569259396357) * 10^40
        + 6729106410213355883014742571241728638976)),
    (((-((((51 * 10^40
        + 8646954524692380390750690460344985820575) * 10^40
        + 5058044462561801759936799895792583616648) * 10^40
        + 5665606114717591311175360771606824561255) * 10^40
        + 6531476152183162684293475921648682587169)) : ℚ) /
        (((10874382209509618225919740204836606 * 10^40
        + 3611089045377415057904678722670245730993) * 10^40
        + 5375498452436832589615588703700504124728) * 10^40
        + 4697252923626309130267766234698194354176)))

noncomputable def nodeJet2N02705MinusPointP009Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP009BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP009Center2577‖ ≤
          nodeJet2N02705MinusPointP009Error2577 := by
  exact nodeExpN02705MinusPointP009BaseError2577

theorem nodeJet2N02705MinusPointP009DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨9, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP009Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP009Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP009Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP009Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨9, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨9, by omega⟩)
      (storedWidth ⟨9, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP009Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP009Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨9, by omega⟩) (pow_pos (storedWidth_pos ⟨9, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP009BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP009Factor2577)

def nodeJet2N02705MinusPointP010Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((111420588356197715176385643 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705MinusPointP010Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP010Factor2577 : RatPair2542 :=
    ((((((((((3803245181163366800038414102802542513228
    * 10^40
        + 5945700478620287572099751246584189869168) * 10^40
        + 7815378324596421971234333522389940474009) * 10^40
        + 4975507374726165482853095933005033170762) * 10^40
        + 6959575261639076790949326466834104054412) * 10^40
        + 547872832478766037539705992709355335405) * 10^40
        + 9628948789607952619251225210430907848705) * 10^40
        + 6583914608124258645399536055126256900655) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((30 * 10^40
        + 8528699804872966304625162978975447473118) * 10^40
        + 2748200041355683421386724597985771645801) * 10^40
        + 4347787100795651194759063759455648366423) * 10^40
        + 6668427224330745517070338721388868623159)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705MinusPointP010Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP010BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP010Center2577‖ ≤
          nodeJet2N02705MinusPointP010Error2577 := by
  exact nodeExpN02705MinusPointP010BaseError2577

theorem nodeJet2N02705MinusPointP010DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨10, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP010Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP010Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP010Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP010Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨10, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨10, by omega⟩)
      (storedWidth ⟨10, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP010Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP010Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨10, by omega⟩) (pow_pos (storedWidth_pos ⟨10, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP010BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP010Factor2577)

def nodeJet2N02705MinusPointP011Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((123268206202301004985337883 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705MinusPointP011Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP011Factor2577 : RatPair2542 :=
    ((((((((((3803245180749177516022352122096200588143
    * 10^40
        + 2766692817113256965473658667093483837827) * 10^40
        + 8129366722518356231672800123270352012908) * 10^40
        + 4752423083066456920072570613442215591701) * 10^40
        + 2419230554077438424780871496459872028649) * 10^40
        + 2195825503894907892969743912727046835465) * 10^40
        + 5146529974897089244606322336807369960437) * 10^40
        + 7774137787999398678504720568105696334095) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((34 * 10^40
        + 1335294921366368050100076465592760284460) * 10^40
        + 1981518118953386168350627527343025193939) * 10^40
        + 513502663073313511313246501779026674900) * 10^40
        + 3091806449964126728779102196636948666279)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705MinusPointP011Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP011BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP011Center2577‖ ≤
          nodeJet2N02705MinusPointP011Error2577 := by
  exact nodeExpN02705MinusPointP011BaseError2577

theorem nodeJet2N02705MinusPointP011DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨11, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP011Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP011Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP011Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP011Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨11, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨11, by omega⟩)
      (storedWidth ⟨11, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP011Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP011Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨11, by omega⟩) (pow_pos (storedWidth_pos ⟨11, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP011BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP011Factor2577)

def nodeJet2N02705MinusPointP012Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((2710788774631016534924847 : ℚ) /
        236118324143482260684800000))

def nodeJet2N02705MinusPointP012Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP012Factor2577 : RatPair2542 :=
    ((((((((((950811295069022699986927605184265778250
    * 10^40
        + 9479761991729262692148476067724131211940) * 10^40
        + 9138155237595937957014565335250049393039) * 10^40
        + 1551006724625507563087791051273911079185) * 10^40
        + 4457198088823828202974588375570292417846) * 10^40
        + 4000758181684343860056012759942304556570) * 10^40
        + 3859623118919210201671468061980383057995) * 10^40
        + 2713242076651094165630680942684127934359) : ℚ) /
        (((((((739076177740620540124420261 * 10^40
        + 4183999956093978723458008735567067535483) * 10^40
        + 1017107743240108556868102619879940125851) * 10^40
        + 4563420872993599720932519433865436071946) * 10^40
        + 7124380037920271146355573444080102405987) * 10^40
        + 402249049118405776549971604346365861316) * 10^40
        + 1100473292467801817231516433785578712272) * 10^40
        + 3545569150638334742688421410702608039936)),
    (((-((((18 * 10^40
        + 7657449224919310388265731334023593515434) * 10^40
        + 9791928414732006828994367259683480229998) * 10^40
        + 7895806824373273198890234051814013970828) * 10^40
        + 7563882119127146264806632995677325680275)) : ℚ) /
        (((2718595552377404556479935051209151 * 10^40
        + 5902772261344353764476169680667561432748) * 10^40
        + 3843874613109208147403897175925126031182) * 10^40
        + 1174313230906577282566941558674548588544)))

noncomputable def nodeJet2N02705MinusPointP012Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP012BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP012Center2577‖ ≤
          nodeJet2N02705MinusPointP012Error2577 := by
  exact nodeExpN02705MinusPointP012BaseError2577

theorem nodeJet2N02705MinusPointP012DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨12, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP012Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP012Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP012Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP012Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨12, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨12, by omega⟩)
      (storedWidth ⟨12, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP012Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP012Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨12, by omega⟩) (pow_pos (storedWidth_pos ⟨12, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP012BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP012Factor2577)

def nodeJet2N02705MinusPointP013Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((29344407147130955527319553 : ℚ) /
        2361183241434822606848000000))

def nodeJet2N02705MinusPointP013Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP013Factor2577 : RatPair2542 :=
    ((((((((((3803245179805904742149207601458130309004
    * 10^40
        + 720979117300473696297832155359834656902) * 10^40
        + 2725901244758153650087674345808952064125) * 10^40
        + 3568348552431403690640252160936303580399) * 10^40
        + 1213382832029014917919148199889276221385) * 10^40
        + 2621249478266379460242179425799731791727) * 10^40
        + 4904859086346706152716350502482599795782) * 10^40
        + 9073718974022756388951044739795202536911) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((40 * 10^40
        + 6280020470989271467333444369994431774891) * 10^40
        + 1291890059217931283349785635731331737187) * 10^40
        + 3448890936858869710981382980367003198629) * 10^40
        + 1493607030348502254813493326255409949945)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705MinusPointP013Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP013BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP013Center2577‖ ≤
          nodeJet2N02705MinusPointP013Error2577 := by
  exact nodeExpN02705MinusPointP013BaseError2577

theorem nodeJet2N02705MinusPointP013DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨13, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP013Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP013Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP013Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP013Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨13, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨13, by omega⟩)
      (storedWidth ⟨13, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP013Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP013Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨13, by omega⟩) (pow_pos (storedWidth_pos ⟨13, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP013BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP013Factor2577)

def nodeJet2N02705MinusPointP014Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((167442242677902990093140313 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705MinusPointP014Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP014Factor2577 : RatPair2542 :=
    ((((((((((3803245178836229386092381878620114796692
    * 10^40
        + 3962850524567402677742489644368171425731) * 10^40
        + 1901231900409432982091659683223559081372) * 10^40
        + 6450850364382229915323573061557747013347) * 10^40
        + 6670801975982550013624101431542501106858) * 10^40
        + 500207219238442311509760666391570215633) * 10^40
        + 4832677812839154598804614576157391611425) * 10^40
        + 5854383531367432583952553688135062574775) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((46 * 10^40
        + 3655220170553130415665127130293923277114) * 10^40
        + 7214008512828692628072236182363532822146) * 10^40
        + 8388352153978009257235047664513278719897) * 10^40
        + 3631741199569815224633542845504801795869)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705MinusPointP014Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP014BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP014Center2577‖ ≤
          nodeJet2N02705MinusPointP014Error2577 := by
  exact nodeExpN02705MinusPointP014BaseError2577

theorem nodeJet2N02705MinusPointP014DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨14, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP014Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP014Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP014Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP014Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨14, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨14, by omega⟩)
      (storedWidth ⟨14, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP014Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP014Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨14, by omega⟩) (pow_pos (storedWidth_pos ⟨14, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP014BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP014Factor2577)

def nodeJet2N02705MinusPointP015Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((182288341473529359843979701 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705MinusPointP015Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP015Factor2577 : RatPair2542 :=
    ((((((((((3803245178062798650537678212215888975573
    * 10^40
        + 5650940976626990756812101477485755013143) * 10^40
        + 5937869943577322068703874050366388582983) * 10^40
        + 7806589384583883908178442557046718660947) * 10^40
        + 405864250492888125140391374525975468390) * 10^40
        + 5908268425381869993636078381862979222219) * 10^40
        + 7142982213140070052328115501118631389236) * 10^40
        + 2227342102417394561423276805938227107567) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((50 * 10^40
        + 4764746032561461775169770546578702556065) * 10^40
        + 2235143528719312096585519845150986565790) * 10^40
        + 6316582921853656221486191082428287944063) * 10^40
        + 491358706962992358002298646074322724713)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705MinusPointP015Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP015BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP015Center2577‖ ≤
          nodeJet2N02705MinusPointP015Error2577 := by
  exact nodeExpN02705MinusPointP015BaseError2577

theorem nodeJet2N02705MinusPointP015DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨15, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP015Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP015Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP015Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP015Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨15, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨15, by omega⟩)
      (storedWidth ⟨15, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP015Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP015Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨15, by omega⟩) (pow_pos (storedWidth_pos ⟨15, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP015BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP015Factor2577)

def nodeJet2N02705MinusPointP016Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((96508645919919764395179147 : ℚ) /
        5902958103587056517120000000))

def nodeJet2N02705MinusPointP016Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP016Factor2577 : RatPair2542 :=
    ((((((((((950811294365745752377157950560481077301
    * 10^40
        + 3771606547770066369710370627733538917448) * 10^40
        + 6821925914823395924115248496124366708982) * 10^40
        + 7756789734818100310749315993326921632832) * 10^40
        + 6631582542275008056384370758369658898693) * 10^40
        + 2396721875096912876303854148305630560654) * 10^40
        + 8639371434852488665578217167116878595885) * 10^40
        + 3456784438142515014054674988522451511663) : ℚ) /
        (((((((739076177740620540124420261 * 10^40
        + 4183999956093978723458008735567067535483) * 10^40
        + 1017107743240108556868102619879940125851) * 10^40
        + 4563420872993599720932519433865436071946) * 10^40
        + 7124380037920271146355573444080102405987) * 10^40
        + 402249049118405776549971604346365861316) * 10^40
        + 1100473292467801817231516433785578712272) * 10^40
        + 3545569150638334742688421410702608039936)),
    (((-((((26 * 10^40
        + 7236849893599088400116801778707305953631) * 10^40
        + 6744111846165688477151373242760732774358) * 10^40
        + 3675699078090594998179701630431346325383) * 10^40
        + 7033825670398257871419609440929771313111)) : ℚ) /
        (((2718595552377404556479935051209151 * 10^40
        + 5902772261344353764476169680667561432748) * 10^40
        + 3843874613109208147403897175925126031182) * 10^40
        + 1174313230906577282566941558674548588544)))

noncomputable def nodeJet2N02705MinusPointP016Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP016BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP016Center2577‖ ≤
          nodeJet2N02705MinusPointP016Error2577 := by
  exact nodeExpN02705MinusPointP016BaseError2577

theorem nodeJet2N02705MinusPointP016DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨16, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP016Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP016Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP016Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP016Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨16, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨16, by omega⟩)
      (storedWidth ⟨16, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP016Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP016Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨16, by omega⟩) (pow_pos (storedWidth_pos ⟨16, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP016BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP016Factor2577)

def nodeJet2N02705MinusPointP017Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((213857607167923887040711041 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705MinusPointP017Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP017Factor2577 : RatPair2542 :=
    ((((((((((3803245176199874529044761817399892873324
    * 10^40
        + 5467405400526800348148731965231092372243) * 10^40
        + 8770578741962759468051846502520683066037) * 10^40
        + 1987216443964451366605624563276550038748) * 10^40
        + 606176451786548322801630017442461949608) * 10^40
        + 8970532338964550513430212325026538413915) * 10^40
        + 8915795001211246949475070172410966235895) * 10^40
        + 7987594768293335342042417851138190526247) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((59 * 10^40
        + 2181485094721866727636596812324521038892) * 10^40
        + 5228638802975848459472501792808741992426) * 10^40
        + 3082069999717297178546914756472153495023) * 10^40
        + 1939696341002624353135203474985940156133)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705MinusPointP017Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP017BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP017Center2577‖ ≤
          nodeJet2N02705MinusPointP017Error2577 := by
  exact nodeExpN02705MinusPointP017BaseError2577

theorem nodeJet2N02705MinusPointP017DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨17, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP017Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP017Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP017Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP017Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨17, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨17, by omega⟩)
      (storedWidth ⟨17, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP017Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP017Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨17, by omega⟩) (pow_pos (storedWidth_pos ⟨17, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP017BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP017Factor2577)

def nodeJet2N02705MinusPointP018Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((55434221733839136935063079 : ℚ) /
        2951479051793528258560000000))

def nodeJet2N02705MinusPointP018Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP018Factor2577 : RatPair2542 :=
    ((((((((((237702823480538220142429437116823723014
    * 10^40
        + 5593215772489062335982190337590829997564) * 10^40
        + 9731156537945054125804020361398514128029) * 10^40
        + 9555972036973566988994320781533029654922) * 10^40
        + 1148828674539587414133794045460462289213) * 10^40
        + 5202614010712089336507845138481733512236) * 10^40
        + 5766441616793367773879384581595006270178) * 10^40
        + 2690634824776782284240472428957005514167) : ℚ) /
        (((((((184769044435155135031105065 * 10^40
        + 3545999989023494680864502183891766883870) * 10^40
        + 7754276935810027139217025654969985031462) * 10^40
        + 8640855218248399930233129858466359017986) * 10^40
        + 6781095009480067786588893361020025601496) * 10^40
        + 7600562262279601444137492901086591465329) * 10^40
        + 275118323116950454307879108446394678068) * 10^40
        + 886392287659583685672105352675652009984)),
    (((-((((15 * 10^40
        + 3499892690928077127292912994554937141508) * 10^40
        + 2284499651532734998901141919757400079756) * 10^40
        + 8950282783395720329870755705942657590529) * 10^40
        + 7705854612085311127789061396620069539427)) : ℚ) /
        (((1359297776188702278239967525604575 * 10^40
        + 7951386130672176882238084840333780716374) * 10^40
        + 1921937306554604073701948587962563015591) * 10^40
        + 587156615453288641283470779337274294272)))

noncomputable def nodeJet2N02705MinusPointP018Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP018BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP018Center2577‖ ≤
          nodeJet2N02705MinusPointP018Error2577 := by
  exact nodeExpN02705MinusPointP018BaseError2577

theorem nodeJet2N02705MinusPointP018DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨18, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP018Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP018Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP018Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP018Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨18, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨18, by omega⟩)
      (storedWidth ⟨18, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP018Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP018Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨18, by omega⟩) (pow_pos (storedWidth_pos ⟨18, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP018BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP018Factor2577)

def nodeJet2N02705MinusPointP019Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((11798844492939419238077853 : ℚ) /
        590295810358705651712000000))

def nodeJet2N02705MinusPointP019Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP019Factor2577 : RatPair2542 :=
    ((((((((((237702823419856267479543471862446460164
    * 10^40
        + 7264862093139383678476134746872757416223) * 10^40
        + 8885513265116836149859993557522695210983) * 10^40
        + 8765959093014788770556829992223849326439) * 10^40
        + 7178584633725246681892932452659073163931) * 10^40
        + 8192074895403346717840083159280279718522) * 10^40
        + 7263141446845131754435987746474561344548) * 10^40
        + 7531498964619160637646226527040628094471) : ℚ) /
        (((((((184769044435155135031105065 * 10^40
        + 3545999989023494680864502183891766883870) * 10^40
        + 7754276935810027139217025654969985031462) * 10^40
        + 8640855218248399930233129858466359017986) * 10^40
        + 6781095009480067786588893361020025601496) * 10^40
        + 7600562262279601444137492901086591465329) * 10^40
        + 275118323116950454307879108446394678068) * 10^40
        + 886392287659583685672105352675652009984)),
    (((-((((16 * 10^40
        + 3357697365991146882592696879142158893568) * 10^40
        + 2372178090013944647888527157250976770177) * 10^40
        + 3792410322220304057445053233753273632005) * 10^40
        + 3874819243955126086106547356641956139445)) : ℚ) /
        (((1359297776188702278239967525604575 * 10^40
        + 7951386130672176882238084840333780716374) * 10^40
        + 1921937306554604073701948587962563015591) * 10^40
        + 587156615453288641283470779337274294272)))

noncomputable def nodeJet2N02705MinusPointP019Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP019BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP019Center2577‖ ≤
          nodeJet2N02705MinusPointP019Error2577 := by
  exact nodeExpN02705MinusPointP019BaseError2577

theorem nodeJet2N02705MinusPointP019DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨19, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP019Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP019Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP019Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP019Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨19, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨19, by omega⟩)
      (storedWidth ⟨19, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP019Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP019Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨19, by omega⟩) (pow_pos (storedWidth_pos ⟨19, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP019BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP019Factor2577)

def nodeJet2N02705MinusPointP020Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((251461754510132159483335377 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705MinusPointP020Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP020Factor2577 : RatPair2542 :=
    ((((((((((3803245173593346878478569805668148471550
    * 10^40
        + 3667242074656729423154626929375658453125) * 10^40
        + 6328532434655243964443181413134060352762) * 10^40
        + 8789370642674588496251747695154196669390) * 10^40
        + 3326982488772869595841690630063869672390) * 10^40
        + 2997003722844065230815530706833033979886) * 10^40
        + 5344388959794955341584267560629383624360) * 10^40
        + 3400160601793094734700759898077500185735) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((69 * 10^40
        + 6309087164748402185342683506862794664789) * 10^40
        + 5734624826178338750176070788812626442065) * 10^40
        + 2577365403694046263099912806291405411972) * 10^40
        + 9427219469234973522890579779599939722101)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705MinusPointP020Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP020BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP020Center2577‖ ≤
          nodeJet2N02705MinusPointP020Error2577 := by
  exact nodeExpN02705MinusPointP020BaseError2577

theorem nodeJet2N02705MinusPointP020DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨20, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP020Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP020Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP020Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP020Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨20, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨20, by omega⟩)
      (storedWidth ⟨20, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP020Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP020Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨20, by omega⟩) (pow_pos (storedWidth_pos ⟨20, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP020BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP020Factor2577)

def nodeJet2N02705MinusPointP021Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((264384479371882101864279921 : ℚ) /
        11805916207174113034240000000))

def nodeJet2N02705MinusPointP021Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP021Factor2577 : RatPair2542 :=
    ((((((((((3803245172600345551090643807590653238170
    * 10^40
        + 4318368521799941113966459504529956594679) * 10^40
        + 3322161429703931262355493501672589598010) * 10^40
        + 1657837987259418914059392502713992386733) * 10^40
        + 2226721349414155722129182207031001150191) * 10^40
        + 5032639635877906234498269365042543974054) * 10^40
        + 13086571881855618286009978411681152201) * 10^40
        + 7815462159815901502895413793392176737607) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((5 * 10^40
        + 6314823286743224081037467218103614808893) * 10^40
        + 7578951147831795285119284977997821219432) * 10^40
        + 4087840398425528288769563192144019917040) * 10^40
        + 5994657098474669930182684741814596286121)) : ℚ) /
        (((418245469596523777919990007878331 * 10^40
        + 138888040206823656073256873948855605038) * 10^40
        + 2129826863555262791908291873219250158643) * 10^40
        + 4026817420139473428087221778257622859776)))

noncomputable def nodeJet2N02705MinusPointP021Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP021BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP021Center2577‖ ≤
          nodeJet2N02705MinusPointP021Error2577 := by
  exact nodeExpN02705MinusPointP021BaseError2577

theorem nodeJet2N02705MinusPointP021DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨21, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP021Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP021Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP021Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP021Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨21, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨21, by omega⟩)
      (storedWidth ⟨21, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP021Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP021Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨21, by omega⟩) (pow_pos (storedWidth_pos ⟨21, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP021BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP021Factor2577)

def nodeJet2N02705MinusPointP022Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((54199761301639112700100539 : ℚ) /
        2361183241434822606848000000))

def nodeJet2N02705MinusPointP022Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP022Factor2577 : RatPair2542 :=
    ((((((((((3803245172072841320992660570848293536709
    * 10^40
        + 4111168598008201776144228601777935346243) * 10^40
        + 6462000836445642610526085908006767487626) * 10^40
        + 5220672288391583704917103996290691599356) * 10^40
        + 5735416142166501775000882409322647468200) * 10^40
        + 1536653900953763936025582728083991895244) * 10^40
        + 6478974967788986587102302490257273070481) * 10^40
        + 1112657316733866916158440811635690198711) : ℚ) /
        (((((((2956304710962482160497681045 * 10^40
        + 6735999824375914893832034942268270141932) * 10^40
        + 4068430972960434227472410479519760503405) * 10^40
        + 8253683491974398883730077735461744287786) * 10^40
        + 8497520151681084585422293776320409623948) * 10^40
        + 1608996196473623106199886417385463445264) * 10^40
        + 4401893169871207268926065735142314849089) * 10^40
        + 4182276602553338970753685642810432159744)),
    (((-((((75 * 10^40
        + 408076767215417219469123402727415025248) * 10^40
        + 793826383168410454813945119116005902304) * 10^40
        + 5511717286049695308099380985780707818381) * 10^40
        + 6194529469428752965605607105235473912035)) : ℚ) /
        (((5437191104754809112959870102418303 * 10^40
        + 1805544522688707528952339361335122865496) * 10^40
        + 7687749226218416294807794351850252062364) * 10^40
        + 2348626461813154565133883117349097177088)))

noncomputable def nodeJet2N02705MinusPointP022Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP022BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP022Center2577‖ ≤
          nodeJet2N02705MinusPointP022Error2577 := by
  exact nodeExpN02705MinusPointP022BaseError2577

theorem nodeJet2N02705MinusPointP022DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨22, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP022Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP022Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP022Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP022Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨22, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨22, by omega⟩)
      (storedWidth ⟨22, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP022Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP022Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨22, by omega⟩) (pow_pos (storedWidth_pos ⟨22, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP022BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP022Factor2577)

def nodeJet2N02705MinusPointP023Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((145034570365256380837972839 : ℚ) /
        5902958103587056517120000000))

def nodeJet2N02705MinusPointP023Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP023Factor2577 : RatPair2542 :=
    ((((((((((950811292619746193718529611221593020592
    * 10^40
        + 2209614414795207612252141153336643637732) * 10^40
        + 5424421254998720245972927983961401271233) * 10^40
        + 4461067649815230461038164569774727942318) * 10^40
        + 9878970338752272038023127501459097751236) * 10^40
        + 8694841588851642978983024357958095250528) * 10^40
        + 3434632272308114427890040548606647794774) * 10^40
        + 9324080959089469260662635293598230087735) : ℚ) /
        (((((((739076177740620540124420261 * 10^40
        + 4183999956093978723458008735567067535483) * 10^40
        + 1017107743240108556868102619879940125851) * 10^40
        + 4563420872993599720932519433865436071946) * 10^40
        + 7124380037920271146355573444080102405987) * 10^40
        + 402249049118405776549971604346365861316) * 10^40
        + 1100473292467801817231516433785578712272) * 10^40
        + 3545569150638334742688421410702608039936)),
    (((-((((40 * 10^40
        + 1607351762488363031720200978029586946603) * 10^40
        + 3434909650007759559924660518894991246510) * 10^40
        + 8341154727979261599651770300086708049627) * 10^40
        + 9434560578117711429258026112640976902307)) : ℚ) /
        (((2718595552377404556479935051209151 * 10^40
        + 5902772261344353764476169680667561432748) * 10^40
        + 3843874613109208147403897175925126031182) * 10^40
        + 1174313230906577282566941558674548588544)))

noncomputable def nodeJet2N02705MinusPointP023Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP023BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP023Center2577‖ ≤
          nodeJet2N02705MinusPointP023Error2577 := by
  exact nodeExpN02705MinusPointP023BaseError2577

theorem nodeJet2N02705MinusPointP023DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨23, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP023Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP023Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP023Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP023Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨23, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨23, by omega⟩)
      (storedWidth ⟨23, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP023Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP023Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨23, by omega⟩) (pow_pos (storedWidth_pos ⟨23, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP023BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP023Factor2577)

def nodeJet2N02705MinusPointP024Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((149416547034989152754795001 : ℚ) /
        5902958103587056517120000000))

def nodeJet2N02705MinusPointP024Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP024Factor2577 : RatPair2542 :=
    ((((((((((950811292427543825395276663199891904758
    * 10^40
        + 101023686665495738830962574399274753582) * 10^40
        + 8577648915009065374391365224105847584870) * 10^40
        + 6401380775637484341472671646611622499993) * 10^40
        + 550835315509637385926610453176927456493) * 10^40
        + 7939644288078034157796903973005867031758) * 10^40
        + 5976366876188562063955281428382192580716) * 10^40
        + 3746300446402510826176352559236043556215) : ℚ) /
        (((((((739076177740620540124420261 * 10^40
        + 4183999956093978723458008735567067535483) * 10^40
        + 1017107743240108556868102619879940125851) * 10^40
        + 4563420872993599720932519433865436071946) * 10^40
        + 7124380037920271146355573444080102405987) * 10^40
        + 402249049118405776549971604346365861316) * 10^40
        + 1100473292467801817231516433785578712272) * 10^40
        + 3545569150638334742688421410702608039936)),
    (((-((((41 * 10^40
        + 3741245367195189560192903829011219868017) * 10^40
        + 6513265228549649674217530641240106173418) * 10^40
        + 2057556535583803773062388398676784933227) * 10^40
        + 945129858188502050024277983984642903613)) : ℚ) /
        (((2718595552377404556479935051209151 * 10^40
        + 5902772261344353764476169680667561432748) * 10^40
        + 3843874613109208147403897175925126031182) * 10^40
        + 1174313230906577282566941558674548588544)))

noncomputable def nodeJet2N02705MinusPointP024Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP024BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP024Center2577‖ ≤
          nodeJet2N02705MinusPointP024Error2577 := by
  exact nodeExpN02705MinusPointP024BaseError2577

theorem nodeJet2N02705MinusPointP024DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨24, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP024Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP024Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP024Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP024Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨24, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨24, by omega⟩)
      (storedWidth ⟨24, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP024Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP024Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨24, by omega⟩) (pow_pos (storedWidth_pos ⟨24, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP024BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP024Factor2577)

def nodeJet2N02705MinusPointP025Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((4840960678205345786172339 : ℚ) /
        184467440737095516160000000))

def nodeJet2N02705MinusPointP025Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP025Factor2577 : RatPair2542 :=
    ((((((((((928526652518041412899077620787635577 *
    10^40
        + 191803491908641820074857384047536020333) * 10^40
        + 8142058925887944441915305755341973947571) * 10^40
        + 5428648247402011434590677439907190737923) * 10^40
        + 6778140405104868198126185051545164030052) * 10^40
        + 5959636427000459936094077261617664604229) * 10^40
        + 995231723304816669355677997043345147524) * 10^40
        + 7059587851994658039099130616182185935167) : ℚ) /
        (((((((721754079824824746215254 * 10^40
        + 1615414062457123026097126961655827214390) * 10^40
        + 1202165144280507918512566506464726504029) * 10^40
        + 1518128340696282812227473163509634214914) * 10^40
        + 104613652380781514791362864691484475005) * 10^40
        + 8467189696337029693141162081644869497911) * 10^40
        + 4415137180949675587712140152767368729211) * 10^40
        + 2034712469873670248772156661533889265664)),
    (((-((((1 * 10^40
        + 3404841294487133111213612827514544785104) * 10^40
        + 8412210123036830883190374675979268788700) * 10^40
        + 3102159741313443377719237168798586302508) * 10^40
        + 227214173450138965660929367635039195807)) : ℚ) /
        (((84956111011793892389997970350285 * 10^40
        + 9871961633167011055139880302520861294773) * 10^40
        + 3870121081659662754606371786747660188474) * 10^40
        + 4411697288465830540080216923708579643392)))

noncomputable def nodeJet2N02705MinusPointP025Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP025BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP025Center2577‖ ≤
          nodeJet2N02705MinusPointP025Error2577 := by
  exact nodeExpN02705MinusPointP025BaseError2577

theorem nodeJet2N02705MinusPointP025DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨25, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP025Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP025Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP025Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP025Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨25, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨25, by omega⟩)
      (storedWidth ⟨25, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP025Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP025Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨25, by omega⟩) (pow_pos (storedWidth_pos ⟨25, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP025BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP025Factor2577)

def nodeJet2N02705MinusPointP026Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((10032849088039534343392071 : ℚ) /
        368934881474191032320000000))

def nodeJet2N02705MinusPointP026Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP026Factor2577 : RatPair2542 :=
    ((((((((((3714106609041578127470115988022811440 *
    10^40
        + 8005194162347456300463812614432069981865) * 10^40
        + 1091038801174714495775578139902507261899) * 10^40
        + 1203235643800570330755860673048788343394) * 10^40
        + 2721623288095359038687713416018192561139) * 10^40
        + 5397008659104588044986705712798301658454) * 10^40
        + 9081482306807472686701913462053459403519) * 10^40
        + 8304682974168277673357782422093794310135) : ℚ) /
        (((((((2887016319299298984861016 * 10^40
        + 6461656249828492104388507846623308857560) * 10^40
        + 4808660577122031674050266025858906016116) * 10^40
        + 6072513362785131248909892654038536859656) * 10^40
        + 418454609523126059165451458765937900023) * 10^40
        + 3868758785348118772564648326579477991645) * 10^40
        + 7660548723798702350848560611069474916844) * 10^40
        + 8138849879494680995088626646135557062656)),
    (((-((((2 * 10^40
        + 7781417511238278114681136462884434343976) * 10^40
        + 4577447640792434430173063708432634300580) * 10^40
        + 2481697972395907862192946036561176138247) * 10^40
        + 2005156564173736318838099410960098667523)) : ℚ) /
        (((169912222023587784779995940700571 * 10^40
        + 9743923266334022110279760605041722589546) * 10^40
        + 7740242163319325509212743573495320376948) * 10^40
        + 8823394576931661080160433847417159286784)))

noncomputable def nodeJet2N02705MinusPointP026Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP026BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP026Center2577‖ ≤
          nodeJet2N02705MinusPointP026Error2577 := by
  exact nodeExpN02705MinusPointP026BaseError2577

theorem nodeJet2N02705MinusPointP026DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨26, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP026Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP026Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP026Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP026Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨26, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨26, by omega⟩)
      (storedWidth ⟨26, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP026Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP026Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨26, by omega⟩) (pow_pos (storedWidth_pos ⟨26, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP026BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP026Factor2577)

def nodeJet2N02705MinusPointP027Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((21078498488072348391776841 : ℚ) /
        737869762948382064640000000))

def nodeJet2N02705MinusPointP027Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP027Factor2577 : RatPair2542 :=
    ((((((((((14856426429958938969284030501174254269 *
    10^40
        + 94584572335150137368611863928497902852) * 10^40
        + 3700475836801814771908714790327476915015) * 10^40
        + 59753963667887165881496565029620584257) * 10^40
        + 3266942855976436426827289323409743738651) * 10^40
        + 2291924191513071530403241773183581583570) * 10^40
        + 4979023249002543757974554880999290139534) * 10^40
        + 8633926548996617610814526731841203972567) : ℚ) /
        (((((((11548065277197195939444066 * 10^40
        + 5846624999313968417554031386493235430241) * 10^40
        + 9234642308488126696201064103435624064466) * 10^40
        + 4290053451140524995639570616154147438624) * 10^40
        + 1673818438092504236661805835063751600093) * 10^40
        + 5475035141392475090258593306317911966583) * 10^40
        + 642194895194809403394242444277899667379) * 10^40
        + 2555399517978723980354506584542228250624)),
    (((-((((5 * 10^40
        + 8367325359776725791671624557091000982651) * 10^40
        + 231097095407567600459185695232499910916) * 10^40
        + 4032176714875513750989259887449976487161) * 10^40
        + 8743538143430229423337981002658917891533)) : ℚ) /
        (((339824444047175569559991881401143 * 10^40
        + 9487846532668044220559521210083445179093) * 10^40
        + 5480484326638651018425487146990640753897) * 10^40
        + 7646789153863322160320867694834318573568)))

noncomputable def nodeJet2N02705MinusPointP027Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP027BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP027Center2577‖ ≤
          nodeJet2N02705MinusPointP027Error2577 := by
  exact nodeExpN02705MinusPointP027BaseError2577

theorem nodeJet2N02705MinusPointP027DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨27, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP027Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP027Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP027Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP027Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨27, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨27, by omega⟩)
      (storedWidth ⟨27, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP027Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP027Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨27, by omega⟩) (pow_pos (storedWidth_pos ⟨27, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP027BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP027Factor2577)

def nodeJet2N02705MinusPointP028Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((85917920262979814161755141 : ℚ) /
        2951479051793528258560000000))

def nodeJet2N02705MinusPointP028Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP028Factor2577 : RatPair2542 :=
    ((((((((((237702822838670524118567245194055509073
    * 10^40
        + 8568376317167643394447757062115879409866) * 10^40
        + 2544454681837035018924082492196617857300) * 10^40
        + 891388400846629508210251862100590437846) * 10^40
        + 9845417030074103801528433103452097780506) * 10^40
        + 4290966866507523604365236867113229339959) * 10^40
        + 8978616576635819628822175727075326659492) * 10^40
        + 5888368797054722489423653955233327341007) : ℚ) /
        (((((((184769044435155135031105065 * 10^40
        + 3545999989023494680864502183891766883870) * 10^40
        + 7754276935810027139217025654969985031462) * 10^40
        + 8640855218248399930233129858466359017986) * 10^40
        + 6781095009480067786588893361020025601496) * 10^40
        + 7600562262279601444137492901086591465329) * 10^40
        + 275118323116950454307879108446394678068) * 10^40
        + 886392287659583685672105352675652009984)),
    (((-((((23 * 10^40
        + 7910646674496839899864530937833091428080) * 10^40
        + 6366140448362851934219725765506155719591) * 10^40
        + 7198529943181169827044976660780840423597) * 10^40
        + 3408172382874517406088926080095488989433)) : ℚ) /
        (((1359297776188702278239967525604575 * 10^40
        + 7951386130672176882238084840333780716374) * 10^40
        + 1921937306554604073701948587962563015591) * 10^40
        + 587156615453288641283470779337274294272)))

noncomputable def nodeJet2N02705MinusPointP028Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP028BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP028Center2577‖ ≤
          nodeJet2N02705MinusPointP028Error2577 := by
  exact nodeExpN02705MinusPointP028BaseError2577

theorem nodeJet2N02705MinusPointP028DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨28, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP028Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP028Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP028Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP028Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨28, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨28, by omega⟩)
      (storedWidth ⟨28, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP028Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP028Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨28, by omega⟩) (pow_pos (storedWidth_pos ⟨28, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP028BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP028Factor2577)

def nodeJet2N02705MinusPointP029Input2577 : RatPair2542 := ((((-((9249 * 10^40
        + 2960978010983741961194555739053181659694) * 10^40
        + 141556277698128789549706349203923437013)) : ℚ) /
        ((10428 * 10^40
        + 305952320729782124092521973314286972300) * 10^40
        + 6362039287226877449347031881482240000000)),
    ((88359795091650310792539297 : ℚ) /
        2951479051793528258560000000))

def nodeJet2N02705MinusPointP029Center2577 : RatPair2542 := (((0 : ℚ) /
        1),
    ((0 : ℚ) /
        1))

def nodeJet2N02705MinusPointP029Factor2577 : RatPair2542 :=
    ((((((((((237702822775277609010348158187627918398
    * 10^40
        + 3183878115011501256816508138775181002895) * 10^40
        + 5143706009662238455171982095557826859661) * 10^40
        + 8472449629074761933099341968382237679131) * 10^40
        + 8553235144703563682389588958189046305153) * 10^40
        + 4516548143846851175282817357250460329320) * 10^40
        + 2442401670018724077080712260923609157045) * 10^40
        + 6197918272366093003677850639701757228775) : ℚ) /
        (((((((184769044435155135031105065 * 10^40
        + 3545999989023494680864502183891766883870) * 10^40
        + 7754276935810027139217025654969985031462) * 10^40
        + 8640855218248399930233129858466359017986) * 10^40
        + 6781095009480067786588893361020025601496) * 10^40
        + 7600562262279601444137492901086591465329) * 10^40
        + 275118323116950454307879108446394678068) * 10^40
        + 886392287659583685672105352675652009984)),
    (((-((((24 * 10^40
        + 4672309640837193107057477929829063388019) * 10^40
        + 3912726702449254300739801562980594569978) * 10^40
        + 5443885231828692306339673249692802958234) * 10^40
        + 5863896963641639101562196480160868285061)) : ℚ) /
        (((1359297776188702278239967525604575 * 10^40
        + 7951386130672176882238084840333780716374) * 10^40
        + 1921937306554604073701948587962563015591) * 10^40
        + 587156615453288641283470779337274294272)))

noncomputable def nodeJet2N02705MinusPointP029Error2577 : ℝ := ((2199023255553 : ℝ) /
        (160693804425899027554 * 10^40
        + 1962092341162602522202993782792835301376))

theorem nodeJet2N02705MinusPointP029BaseError2577 :
    ‖weightedUnitJet2539 0 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP029Center2577‖ ≤
          nodeJet2N02705MinusPointP029Error2577 := by
  exact nodeExpN02705MinusPointP029BaseError2577

theorem nodeJet2N02705MinusPointP029DerivativeError2577 :
    ‖weightedUnitJet2539 2 (-1/2) nodeModulation2541 ⟨29, by omega⟩
        nodeJet2N02705MinusPointPosition2577 -
      embedPair2542 nodeJet2N02705MinusPointP029Factor2577 * embedPair2542
          nodeJet2N02705MinusPointP029Center2577‖ ≤
        (pairMagnitude2542 nodeJet2N02705MinusPointP029Factor2577 : ℝ) *
            nodeJet2N02705MinusPointP029Error2577 := by
  have hx : |nodeJet2N02705MinusPointPosition2577| < storedWidth ⟨29, by omega⟩ ^ 2 := by
    norm_num [nodeJet2N02705MinusPointPosition2577, storedWidth]
  have hf : weightedMultiplier2543 2 (-1/2) (nodeModulation2541 ⟨29, by omega⟩)
      (storedWidth ⟨29, by omega⟩ ^ 2) nodeJet2N02705MinusPointPosition2577 = embedPair2542
          nodeJet2N02705MinusPointP029Factor2577 :=
          by
    apply Complex.ext <;> norm_num [weightedMultiplier2543, Finset.sum_range_succ,
      weightedLambda2537, bumpMultiplier2543, bumpDeficit2350, bumpNumerator2350,
      nodeJet2N02705MinusPointPosition2577, storedWidth, nodeModulation2541, embedPair2542,
      nodeJet2N02705MinusPointP029Factor2577, Complex.mul_re, Complex.mul_im, pow_succ]
  have h := weightedFamily_inside_factor2543 2 (by omega) (-1/2)
    (nodeModulation2541 ⟨29, by omega⟩) (pow_pos (storedWidth_pos ⟨29, by omega⟩) 2) hx
  rw [hf] at h
  change ‖iteratedDeriv 2 _ _ - _‖ ≤ _
  rw [h]
  exact complex_multiplier_error2543 _ _ _ _ _ nodeJet2N02705MinusPointP029BaseError2577
    (embedPair_magnitude2542 nodeJet2N02705MinusPointP029Factor2577)

theorem nodeJet2N02705MinusPointGrid2577 :
    -stripRadius2303 + (2705 : ℝ) * (2 * stripRadius2303 / 10240) =
      nodeJet2N02705MinusPointPosition2577 := by
  norm_num [stripRadius2303, nodeJet2N02705MinusPointPosition2577]

end ConnesWeilRH.Dev
