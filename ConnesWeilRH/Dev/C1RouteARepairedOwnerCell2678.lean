import ConnesWeilRH.Dev.C1RouteABinary64Bridge2674
import ConnesWeilRH.Dev.MatrixConsValFamily2637
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family0
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family1
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family2
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family3
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family4
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family5
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family6
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family7
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family8
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family9
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family10
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family11
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family12
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family13
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family14
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family15
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family16
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family17
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family18
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family19
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family20
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family21
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family22
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family23
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family24
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family25
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family26
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family27
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family28
import ConnesWeilRH.Dev.C1RouteACellContainment2677Family29

namespace ConnesWeilRH.Dev

open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

/- Record 2678: the actual repaired binary64 point owner is decoded
   from the midpoint-cast bit patterns.  Its family rectangles are
   generated from exact 256-bit interval arithmetic and rounded
   outward to dyadic 2^-160 endpoints before Lean consumes them. -/

noncomputable def record2678BaseCoefficient : Fin 30 → ℂ :=
  ![
    ⟨binary64Value2674 4823034418914672305, binary64Value2674 14036130726401833002⟩,
    ⟨binary64Value2674 14032067444084851866, binary64Value2674 4798621723694306952⟩,
    ⟨binary64Value2674 4806169240827736120, binary64Value2674 4589164093995325069⟩,
    ⟨binary64Value2674 14025060429437655784, binary64Value2674 13810775161195722671⟩,
    ⟨binary64Value2674 13980027647480516992, binary64Value2674 13962659126816036104⟩,
    ⟨binary64Value2674 4808755879773200060, binary64Value2674 13955745383298021167⟩,
    ⟨binary64Value2674 14028161303818700465, binary64Value2674 4734020025278555541⟩,
    ⟨binary64Value2674 4792110455395659981, binary64Value2674 13950209813199254111⟩,
    ⟨binary64Value2674 4801744305911664660, binary64Value2674 4771576091297831883⟩,
    ⟨binary64Value2674 4800932483186830933, binary64Value2674 4783365806158295576⟩,
    ⟨binary64Value2674 4797299349544756459, binary64Value2674 14007874823166521824⟩,
    ⟨binary64Value2674 4795089583269782610, binary64Value2674 4786586563397869647⟩,
    ⟨binary64Value2674 4798183557039462118, binary64Value2674 14011305856171479768⟩,
    ⟨binary64Value2674 4789264240782508305, binary64Value2674 4788817433509278158⟩,
    ⟨binary64Value2674 14040263398301464522, binary64Value2674 4807247546034677027⟩,
    ⟨binary64Value2674 14040311481527232328, binary64Value2674 4807060120525854493⟩,
    ⟨binary64Value2674 4787765143011767205, binary64Value2674 4787559084938093386⟩,
    ⟨binary64Value2674 4799022457240706568, binary64Value2674 4780441451267189933⟩,
    ⟨binary64Value2674 4791225233192157022, binary64Value2674 14005900707546545330⟩,
    ⟨binary64Value2674 4798365669855150438, binary64Value2674 4779801649360682290⟩,
    ⟨binary64Value2674 4798009098064206246, binary64Value2674 14003231103753472786⟩,
    ⟨binary64Value2674 4788182869994242973, binary64Value2674 4782542917723556714⟩,
    ⟨binary64Value2674 4798597142944752018, binary64Value2674 14003427382228297747⟩,
    ⟨binary64Value2674 4798959619870820688, binary64Value2674 13994880404208517053⟩,
    ⟨binary64Value2674 4786717765842490051, binary64Value2674 4781218035165027082⟩,
    ⟨binary64Value2674 4798069280824189000, binary64Value2674 14008312106464145166⟩,
    ⟨binary64Value2674 4793959423905951945, binary64Value2674 4786761550846363003⟩,
    ⟨binary64Value2674 4802975639260479193, binary64Value2674 14016266340031661505⟩,
    ⟨binary64Value2674 14024714349145726572, binary64Value2674 4794368241887771089⟩,
    ⟨binary64Value2674 4802960787239624638, binary64Value2674 14013025559429333088⟩]

noncomputable def record2678BaseM0FamilyRects : Fin 30 → ComplexRect2427 :=
  ![
    ComplexRect2427.mk ((18265398393142836187757682176505065311228221497065 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((37146279243009130970342927164902845279412725380793 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-10277869719035861543786249917716538378323162126571 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-7887724255447689525929296794423726896510113414101 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((-4200572852251054148977349545415256636574062102479 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-2065151775400662197424242179195170895343036987327 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((112845832886424024578487684568749575967189375509 : ℚ) / (182687704666362864775460604089535377456991567872 : ℚ) : ℝ) ((1173076194758578864306238364270692149265814666071 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((2841480475174723283387043173012596609786512908557 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((712479224252269945964059803534809867041528819637 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((-1404434886669356589132779411524545183305742201 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((180184595070754283939537622646686537441262889181 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((-1431038632933118174593230138923321102539088461257 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-1426804495054025031739486449686850961728651311047 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-5654794637965489260016548850569212975415687651 : ℚ) / (91343852333181432387730302044767688728495783936 : ℚ) : ℝ) ((705213749342933759355012306363369062295274007 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((-702264596820641398773021008680476805828946587 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((-1394153101054871965194129563038819525492341155 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-98620313105127485217256287013207290050109507 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-2308084342305563585027336704251787431989681 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ),
    ComplexRect2427.mk ((4230321019042487208864479506505475471681403136633 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((1057590450991481841133213595341923812234508554933 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((-33003286515804374981227411388093819432155099 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-8250742082769455173291713042577236431725511 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ),
    ComplexRect2427.mk ((-2258617016726504298499976632578204109567088953269 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-2258606175389108630249014240015857979536774961693 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((2669861265363129330597016204261829063430287 : ℚ) / (91343852333181432387730302044767688728495783936 : ℚ) : ℝ) ((42717985291680166166479625893966120931972037 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((159734819775909772335095394192351652581025070989 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((159735243233079605483962747908702867905215875581 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((-7199290250529399302860066839305975590397429 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((-14398542330508422967298414695097937103920997 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((722397069314456511187653634062149858963709581313 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((1445681265624518672805454990277401103829081539179 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-4664215307824609163875863486099743939119569363 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((444257575066675236202071310684629796293811961 : ℚ) / (45671926166590716193865151022383844364247891968 : ℚ) : ℝ),
    ComplexRect2427.mk ((1227529988349543388859157291173836891862303556145 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((1231439152283924095082820172927156401763921883125 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((21353184509850681220171312983247553348169164305 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((84436411080106809568234521362316727565595413403 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((362789488213698508351092968899230915280678295637 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((365316683236589061986818819165721794617809737115 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((-66311295305472828203973683197886050680657214225 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((-3218181302423451684211102529068825637026255909 : ℚ) / (45671926166590716193865151022383844364247891968 : ℚ) : ℝ),
    ComplexRect2427.mk ((517738420644371873467375332810735346870358946465 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((16396271620154908530511206003755845086181755491 : ℚ) / (45671926166590716193865151022383844364247891968 : ℚ) : ℝ) ((57389420456997172510952631781534101614928218731 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((138180724221165429425716655424580962980357807265 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((838940152078342699308142394395849527562196255241 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((424430004366099733947489629851977033524821538341 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((-212245499965741647659699131887554719937481242343 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-42536709379944088326843766790565071989297875883 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ),
    ComplexRect2427.mk ((107314732327948139009631157545489547983223879873 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((225760517240981555057247016821150603395988727701 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((11775217781612803945906026696434228831004348951 : ℚ) / (91343852333181432387730302044767688728495783936 : ℚ) : ℝ) ((50074873041451039069876516529576541644507021283 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ),
    ComplexRect2427.mk ((-1883378343481685270183749489681949652668383263819 : ℚ) / (182687704666362864775460604089535377456991567872 : ℚ) : ℝ) ((-14817150559761410807868217045218087014063360813283 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((1704998576189490127286863350235369736257406212351 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((2168988778245889070621310223580820930115139956445 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ),
    ComplexRect2427.mk ((-15171324749648511810636662731310097005609598022731 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-3725354318078933575495163014733087273954783247857 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((3307390083833541696148021189614639607417617956413 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((1081564102035077442915893265658974325862749025125 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ),
    ComplexRect2427.mk ((5138390864393447159129974086236170784270377161 : ℚ) / (45671926166590716193865151022383844364247891968 : ℚ) : ℝ) ((176168467477649295979088703038401281673506581351 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((146134396174518894889051128095771902138317009677 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((19791793123397029021885614628493761188764559569 : ℚ) / (182687704666362864775460604089535377456991567872 : ℚ) : ℝ),
    ComplexRect2427.mk ((957009677841159549966122182402938709358710281989 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((241397932146341620235937786655926991301835536417 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((-4828564084530238471464634871949366196230139337 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((28028476514214961839629440182919375841837709677 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ),
    ComplexRect2427.mk ((273592174599551136237281992314879686576267301611 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((8775929195995685827211220199281904735296259051 : ℚ) / (45671926166590716193865151022383844364247891968 : ℚ) : ℝ) ((-95329301460264886466821957336232628790712572215 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-72219219392936534719100955113311044442752070111 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((868911820708917239576290028312945076037550150959 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((877938822203808898087471492294098180735929108411 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-6232861893164894290850434348792672466684143539 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((50795780509392545688298717843548588951539651443 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((408222679914227555393944082327684289585159506099 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((826150828468056653725449369059485893768773959345 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-62885187010629073516910698773132574295650317607 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((-49347613708035466036728472831633567483353552371 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((177876383932367717178882704895098390548807140593 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((186158697473042532819046057779104149444045373479 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((55268326604099050176057044684847377379567870497 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((36566562290713689779706993400454174670640134041 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ),
    ComplexRect2427.mk ((446658510743690946458051401407371233740522837507 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((904927087993638099397625279399839860841631059189 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-141045092137511265999044614188917943736093037127 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-50706007539082077475405885108553037031620172527 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((118033905400550205132902932737523785360936337823 : ℚ) / (182687704666362864775460604089535377456991567872 : ℚ) : ℝ) ((953517119323157197484112311565299300982945740571 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-114313996475162268926744162760007513478121089439 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-12594880864594719296326674365112453482701382493 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((139111502758012531422622554732598738853201448011 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((147120191271940309610794445136971813682873944941 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((46123678674855436374201897680258244616760863149 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((62081008202376154307044940009322843782019727599 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((814400713837666938955343829512567280250007405743 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((834756581414039193257785122028169933025468753903 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-204526337641692861902000720148270794080623282783 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-54193564173008206792060092635182911965187925963 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ),
    ComplexRect2427.mk ((54878255482523661002619699023872559004652026701 : ℚ) / (182687704666362864775460604089535377456991567872 : ℚ) : ℝ) ((115031828292063852995311498235585394425492123965 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((88072456211748399335235064088920207883671549249 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((141911630818380413073873587074131825131452378481 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((1712297626514031489882297653667180735869172494107 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((444527335143994771106321650407951597727602371649 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((-590126271587853234906062017126603520394975004357 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((-365151522540698613273683466270335285367295149447 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((-167666794345307611879299411211288665608344055335 : ℚ) / (182687704666362864775460604089535377456991567872 : ℚ) : ℝ) ((-1266362676567125222499585127276161908108514051553 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((231608339280819547040043666655849016691554091131 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ) : ℝ) ((638404123859866386945853738680566769149580659447 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ),
    ComplexRect2427.mk ((1723050643699155647820211567862182525085016119587 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ) ((443557856492255230633361945550536484258512525677 : ℚ) / (365375409332725729550921208179070754913983135744 : ℚ) : ℝ) ((-28512703239695727149895300446706317125190956163 : ℚ) / (91343852333181432387730302044767688728495783936 : ℚ) : ℝ) ((-222209794184778188801820335992093232150568125301 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ) : ℝ)]

def record2678BaseM0AggregateReLo : ℚ :=
  ((19343698897402274412078735768938152474972633481809 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ))
def record2678BaseM0AggregateReHi : ℚ :=
  ((20916671887856089083055673867404184207429802103705 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ))
def record2678BaseM0AggregateImLo : ℚ :=
  ((-3740081323437219887729365884504892205396943836243 : ℚ) / (1461501637330902918203684832716283019655932542976 : ℚ))
def record2678BaseM0AggregateImHi : ℚ :=
  ((1297283413491562779260814794607638975476629245767 : ℚ) / (730750818665451459101842416358141509827966271488 : ℚ))
noncomputable def record2678BaseM0Aggregate : ComplexRect2427 :=
  ComplexRect2427.mk (record2678BaseM0AggregateReLo : ℝ)
    (record2678BaseM0AggregateReHi : ℝ)
    (record2678BaseM0AggregateImLo : ℝ)
    (record2678BaseM0AggregateImHi : ℝ)

theorem fin30SumChain2678 {α : Type*} [AddCommMonoid α]
    (f : Fin 30 → α) :
    (∑ i : Fin 30, f i) =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 +
      (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 +
      (f 15 + (f 16 + (f 17 + (f 18 + (f 19 + (f 20 + (f 21 +
      (f 22 + (f 23 + (f 24 + (f 25 + (f 26 + (f 27 + (f 28 + f 29
      )))))))))))))))))))))))))))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

theorem record2678BaseM0AggregateFamilySumEq :
    ComplexRect2427.sumFinset record2678BaseM0FamilyRects Finset.univ =
      record2678BaseM0Aggregate := by
  ext <;> simp only [ComplexRect2427.sumFinset]
  all_goals rw [fin30SumChain2678]
  all_goals simp [record2678BaseM0FamilyRects]
  all_goals norm_num [record2678BaseM0FamilyRects, record2678BaseM0Aggregate,
    record2678BaseM0AggregateReLo, record2678BaseM0AggregateReHi,
    record2678BaseM0AggregateImLo, record2678BaseM0AggregateImHi]

set_option maxRecDepth 10000 in
theorem record2678BaseM0AggregateSubset :
    record2675BaseM0Rect.reLo ≤ record2678BaseM0Aggregate.reLo ∧
      record2678BaseM0Aggregate.reHi ≤ record2675BaseM0Rect.reHi ∧
      record2675BaseM0Rect.imLo ≤ record2678BaseM0Aggregate.imLo ∧
      record2678BaseM0Aggregate.imHi ≤ record2675BaseM0Rect.imHi := by
  norm_num [record2678BaseM0Aggregate, record2675BaseM0Rect,
    record2678BaseM0AggregateReLo, record2678BaseM0AggregateReHi,
    record2678BaseM0AggregateImLo, record2678BaseM0AggregateImHi,
    binary64Value2674, binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

set_option maxRecDepth 10000 in theorem record2678Family0BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 0).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 0)
        (capturedModulations2584 0) (storedWidth 0 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family0PhiMem hx)
    (record2677Family0TrigMem hx).1 (record2677Family0TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 0)
    (theta := capturedModulations2584 0) (radius := storedWidth 0 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 0).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 0))
        record2677Family0MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 0))
      record2677Family0MidRect).reHi ≤ (record2678BaseM0FamilyRects 0).reHi ∧
    (record2678BaseM0FamilyRects 0).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 0))
        record2677Family0MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 0))
      record2677Family0MidRect).imHi ≤ (record2678BaseM0FamilyRects 0).imHi := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family0MidRect, record2677Family0PhiRect,
      record2677Family0CosRect, record2677Family0SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family1BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 1).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 1)
        (capturedModulations2584 1) (storedWidth 1 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family1PhiMem hx)
    (record2677Family1TrigMem hx).1 (record2677Family1TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 1)
    (theta := capturedModulations2584 1) (radius := storedWidth 1 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 1).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 1))
        record2677Family1MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 1))
      record2677Family1MidRect).reHi ≤ (record2678BaseM0FamilyRects 1).reHi ∧
    (record2678BaseM0FamilyRects 1).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 1))
        record2677Family1MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 1))
      record2677Family1MidRect).imHi ≤ (record2678BaseM0FamilyRects 1).imHi := by
    norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family1MidRect, record2677Family1PhiRect,
      record2677Family1CosRect, record2677Family1SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family2BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 2).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 2)
        (capturedModulations2584 2) (storedWidth 2 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family2PhiMem hx)
    (record2677Family2TrigMem hx).1 (record2677Family2TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 2)
    (theta := capturedModulations2584 2) (radius := storedWidth 2 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 2).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 2))
        record2677Family2MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 2))
      record2677Family2MidRect).reHi ≤ (record2678BaseM0FamilyRects 2).reHi ∧
    (record2678BaseM0FamilyRects 2).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 2))
        record2677Family2MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 2))
      record2677Family2MidRect).imHi ≤ (record2678BaseM0FamilyRects 2).imHi := by
    norm_num [Matrix.cons_val_two, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family2MidRect, record2677Family2PhiRect,
      record2677Family2CosRect, record2677Family2SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family3BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 3).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 3)
        (capturedModulations2584 3) (storedWidth 3 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family3PhiMem hx)
    (record2677Family3TrigMem hx).1 (record2677Family3TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 3)
    (theta := capturedModulations2584 3) (radius := storedWidth 3 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 3).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 3))
        record2677Family3MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 3))
      record2677Family3MidRect).reHi ≤ (record2678BaseM0FamilyRects 3).reHi ∧
    (record2678BaseM0FamilyRects 3).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 3))
        record2677Family3MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 3))
      record2677Family3MidRect).imHi ≤ (record2678BaseM0FamilyRects 3).imHi := by
    norm_num [Matrix.cons_val_three, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family3MidRect, record2677Family3PhiRect,
      record2677Family3CosRect, record2677Family3SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family4BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 4).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 4)
        (capturedModulations2584 4) (storedWidth 4 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family4PhiMem hx)
    (record2677Family4TrigMem hx).1 (record2677Family4TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 4)
    (theta := capturedModulations2584 4) (radius := storedWidth 4 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 4).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 4))
        record2677Family4MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 4))
      record2677Family4MidRect).reHi ≤ (record2678BaseM0FamilyRects 4).reHi ∧
    (record2678BaseM0FamilyRects 4).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 4))
        record2677Family4MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 4))
      record2677Family4MidRect).imHi ≤ (record2678BaseM0FamilyRects 4).imHi := by
    norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family4MidRect, record2677Family4PhiRect,
      record2677Family4CosRect, record2677Family4SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family5BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 5).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 5)
        (capturedModulations2584 5) (storedWidth 5 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family5PhiMem hx)
    (record2677Family5TrigMem hx).1 (record2677Family5TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 5)
    (theta := capturedModulations2584 5) (radius := storedWidth 5 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 5).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 5))
        record2677Family5MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 5))
      record2677Family5MidRect).reHi ≤ (record2678BaseM0FamilyRects 5).reHi ∧
    (record2678BaseM0FamilyRects 5).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 5))
        record2677Family5MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 5))
      record2677Family5MidRect).imHi ≤ (record2678BaseM0FamilyRects 5).imHi := by
    norm_num [Matrix.cons_val_5, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family5MidRect, record2677Family5PhiRect,
      record2677Family5CosRect, record2677Family5SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family6BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 6).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 6)
        (capturedModulations2584 6) (storedWidth 6 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family6PhiMem hx)
    (record2677Family6TrigMem hx).1 (record2677Family6TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 6)
    (theta := capturedModulations2584 6) (radius := storedWidth 6 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 6).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 6))
        record2677Family6MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 6))
      record2677Family6MidRect).reHi ≤ (record2678BaseM0FamilyRects 6).reHi ∧
    (record2678BaseM0FamilyRects 6).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 6))
        record2677Family6MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 6))
      record2677Family6MidRect).imHi ≤ (record2678BaseM0FamilyRects 6).imHi := by
    norm_num [Matrix.cons_val_6, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family6MidRect, record2677Family6PhiRect,
      record2677Family6CosRect, record2677Family6SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family7BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 7).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 7)
        (capturedModulations2584 7) (storedWidth 7 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family7PhiMem hx)
    (record2677Family7TrigMem hx).1 (record2677Family7TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 7)
    (theta := capturedModulations2584 7) (radius := storedWidth 7 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 7).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 7))
        record2677Family7MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 7))
      record2677Family7MidRect).reHi ≤ (record2678BaseM0FamilyRects 7).reHi ∧
    (record2678BaseM0FamilyRects 7).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 7))
        record2677Family7MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 7))
      record2677Family7MidRect).imHi ≤ (record2678BaseM0FamilyRects 7).imHi := by
    norm_num [Matrix.cons_val_7, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family7MidRect, record2677Family7PhiRect,
      record2677Family7CosRect, record2677Family7SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family8BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 8).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 8)
        (capturedModulations2584 8) (storedWidth 8 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family8PhiMem hx)
    (record2677Family8TrigMem hx).1 (record2677Family8TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 8)
    (theta := capturedModulations2584 8) (radius := storedWidth 8 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 8).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 8))
        record2677Family8MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 8))
      record2677Family8MidRect).reHi ≤ (record2678BaseM0FamilyRects 8).reHi ∧
    (record2678BaseM0FamilyRects 8).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 8))
        record2677Family8MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 8))
      record2677Family8MidRect).imHi ≤ (record2678BaseM0FamilyRects 8).imHi := by
    norm_num [Matrix.cons_val_8, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family8MidRect, record2677Family8PhiRect,
      record2677Family8CosRect, record2677Family8SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family9BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 9).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 9)
        (capturedModulations2584 9) (storedWidth 9 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family9PhiMem hx)
    (record2677Family9TrigMem hx).1 (record2677Family9TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 9)
    (theta := capturedModulations2584 9) (radius := storedWidth 9 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 9).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 9))
        record2677Family9MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 9))
      record2677Family9MidRect).reHi ≤ (record2678BaseM0FamilyRects 9).reHi ∧
    (record2678BaseM0FamilyRects 9).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 9))
        record2677Family9MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 9))
      record2677Family9MidRect).imHi ≤ (record2678BaseM0FamilyRects 9).imHi := by
    norm_num [Matrix.cons_val_9, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family9MidRect, record2677Family9PhiRect,
      record2677Family9CosRect, record2677Family9SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family10BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 10).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 10)
        (capturedModulations2584 10) (storedWidth 10 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family10PhiMem hx)
    (record2677Family10TrigMem hx).1 (record2677Family10TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 10)
    (theta := capturedModulations2584 10) (radius := storedWidth 10 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 10).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 10))
        record2677Family10MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 10))
      record2677Family10MidRect).reHi ≤ (record2678BaseM0FamilyRects 10).reHi ∧
    (record2678BaseM0FamilyRects 10).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 10))
        record2677Family10MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 10))
      record2677Family10MidRect).imHi ≤ (record2678BaseM0FamilyRects 10).imHi := by
    norm_num [Matrix.cons_val_10, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family10MidRect, record2677Family10PhiRect,
      record2677Family10CosRect, record2677Family10SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family11BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 11).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 11)
        (capturedModulations2584 11) (storedWidth 11 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family11PhiMem hx)
    (record2677Family11TrigMem hx).1 (record2677Family11TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 11)
    (theta := capturedModulations2584 11) (radius := storedWidth 11 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 11).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 11))
        record2677Family11MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 11))
      record2677Family11MidRect).reHi ≤ (record2678BaseM0FamilyRects 11).reHi ∧
    (record2678BaseM0FamilyRects 11).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 11))
        record2677Family11MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 11))
      record2677Family11MidRect).imHi ≤ (record2678BaseM0FamilyRects 11).imHi := by
    norm_num [Matrix.cons_val_11, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family11MidRect, record2677Family11PhiRect,
      record2677Family11CosRect, record2677Family11SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family12BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 12).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 12)
        (capturedModulations2584 12) (storedWidth 12 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family12PhiMem hx)
    (record2677Family12TrigMem hx).1 (record2677Family12TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 12)
    (theta := capturedModulations2584 12) (radius := storedWidth 12 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 12).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 12))
        record2677Family12MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 12))
      record2677Family12MidRect).reHi ≤ (record2678BaseM0FamilyRects 12).reHi ∧
    (record2678BaseM0FamilyRects 12).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 12))
        record2677Family12MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 12))
      record2677Family12MidRect).imHi ≤ (record2678BaseM0FamilyRects 12).imHi := by
    norm_num [Matrix.cons_val_12, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family12MidRect, record2677Family12PhiRect,
      record2677Family12CosRect, record2677Family12SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family13BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 13).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 13)
        (capturedModulations2584 13) (storedWidth 13 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family13PhiMem hx)
    (record2677Family13TrigMem hx).1 (record2677Family13TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 13)
    (theta := capturedModulations2584 13) (radius := storedWidth 13 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 13).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 13))
        record2677Family13MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 13))
      record2677Family13MidRect).reHi ≤ (record2678BaseM0FamilyRects 13).reHi ∧
    (record2678BaseM0FamilyRects 13).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 13))
        record2677Family13MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 13))
      record2677Family13MidRect).imHi ≤ (record2678BaseM0FamilyRects 13).imHi := by
    norm_num [Matrix.cons_val_13, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family13MidRect, record2677Family13PhiRect,
      record2677Family13CosRect, record2677Family13SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family14BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 14).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 14)
        (capturedModulations2584 14) (storedWidth 14 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family14PhiMem hx)
    (record2677Family14TrigMem hx).1 (record2677Family14TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 14)
    (theta := capturedModulations2584 14) (radius := storedWidth 14 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 14).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 14))
        record2677Family14MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 14))
      record2677Family14MidRect).reHi ≤ (record2678BaseM0FamilyRects 14).reHi ∧
    (record2678BaseM0FamilyRects 14).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 14))
        record2677Family14MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 14))
      record2677Family14MidRect).imHi ≤ (record2678BaseM0FamilyRects 14).imHi := by
    norm_num [Matrix.cons_val_14, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family14MidRect, record2677Family14PhiRect,
      record2677Family14CosRect, record2677Family14SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family15BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 15).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 15)
        (capturedModulations2584 15) (storedWidth 15 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family15PhiMem hx)
    (record2677Family15TrigMem hx).1 (record2677Family15TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 15)
    (theta := capturedModulations2584 15) (radius := storedWidth 15 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 15).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 15))
        record2677Family15MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 15))
      record2677Family15MidRect).reHi ≤ (record2678BaseM0FamilyRects 15).reHi ∧
    (record2678BaseM0FamilyRects 15).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 15))
        record2677Family15MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 15))
      record2677Family15MidRect).imHi ≤ (record2678BaseM0FamilyRects 15).imHi := by
    norm_num [Matrix.cons_val_15, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family15MidRect, record2677Family15PhiRect,
      record2677Family15CosRect, record2677Family15SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family16BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 16).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 16)
        (capturedModulations2584 16) (storedWidth 16 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family16PhiMem hx)
    (record2677Family16TrigMem hx).1 (record2677Family16TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 16)
    (theta := capturedModulations2584 16) (radius := storedWidth 16 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 16).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 16))
        record2677Family16MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 16))
      record2677Family16MidRect).reHi ≤ (record2678BaseM0FamilyRects 16).reHi ∧
    (record2678BaseM0FamilyRects 16).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 16))
        record2677Family16MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 16))
      record2677Family16MidRect).imHi ≤ (record2678BaseM0FamilyRects 16).imHi := by
    norm_num [Matrix.cons_val_16, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family16MidRect, record2677Family16PhiRect,
      record2677Family16CosRect, record2677Family16SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family17BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 17).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 17)
        (capturedModulations2584 17) (storedWidth 17 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family17PhiMem hx)
    (record2677Family17TrigMem hx).1 (record2677Family17TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 17)
    (theta := capturedModulations2584 17) (radius := storedWidth 17 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 17).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 17))
        record2677Family17MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 17))
      record2677Family17MidRect).reHi ≤ (record2678BaseM0FamilyRects 17).reHi ∧
    (record2678BaseM0FamilyRects 17).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 17))
        record2677Family17MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 17))
      record2677Family17MidRect).imHi ≤ (record2678BaseM0FamilyRects 17).imHi := by
    norm_num [Matrix.cons_val_17, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family17MidRect, record2677Family17PhiRect,
      record2677Family17CosRect, record2677Family17SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family18BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 18).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 18)
        (capturedModulations2584 18) (storedWidth 18 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family18PhiMem hx)
    (record2677Family18TrigMem hx).1 (record2677Family18TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 18)
    (theta := capturedModulations2584 18) (radius := storedWidth 18 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 18).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 18))
        record2677Family18MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 18))
      record2677Family18MidRect).reHi ≤ (record2678BaseM0FamilyRects 18).reHi ∧
    (record2678BaseM0FamilyRects 18).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 18))
        record2677Family18MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 18))
      record2677Family18MidRect).imHi ≤ (record2678BaseM0FamilyRects 18).imHi := by
    norm_num [Matrix.cons_val_18, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family18MidRect, record2677Family18PhiRect,
      record2677Family18CosRect, record2677Family18SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family19BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 19).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 19)
        (capturedModulations2584 19) (storedWidth 19 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family19PhiMem hx)
    (record2677Family19TrigMem hx).1 (record2677Family19TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 19)
    (theta := capturedModulations2584 19) (radius := storedWidth 19 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 19).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 19))
        record2677Family19MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 19))
      record2677Family19MidRect).reHi ≤ (record2678BaseM0FamilyRects 19).reHi ∧
    (record2678BaseM0FamilyRects 19).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 19))
        record2677Family19MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 19))
      record2677Family19MidRect).imHi ≤ (record2678BaseM0FamilyRects 19).imHi := by
    norm_num [Matrix.cons_val_19, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family19MidRect, record2677Family19PhiRect,
      record2677Family19CosRect, record2677Family19SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family20BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 20).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 20)
        (capturedModulations2584 20) (storedWidth 20 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family20PhiMem hx)
    (record2677Family20TrigMem hx).1 (record2677Family20TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 20)
    (theta := capturedModulations2584 20) (radius := storedWidth 20 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 20).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 20))
        record2677Family20MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 20))
      record2677Family20MidRect).reHi ≤ (record2678BaseM0FamilyRects 20).reHi ∧
    (record2678BaseM0FamilyRects 20).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 20))
        record2677Family20MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 20))
      record2677Family20MidRect).imHi ≤ (record2678BaseM0FamilyRects 20).imHi := by
    norm_num [Matrix.cons_val_20, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family20MidRect, record2677Family20PhiRect,
      record2677Family20CosRect, record2677Family20SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family21BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 21).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 21)
        (capturedModulations2584 21) (storedWidth 21 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family21PhiMem hx)
    (record2677Family21TrigMem hx).1 (record2677Family21TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 21)
    (theta := capturedModulations2584 21) (radius := storedWidth 21 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 21).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 21))
        record2677Family21MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 21))
      record2677Family21MidRect).reHi ≤ (record2678BaseM0FamilyRects 21).reHi ∧
    (record2678BaseM0FamilyRects 21).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 21))
        record2677Family21MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 21))
      record2677Family21MidRect).imHi ≤ (record2678BaseM0FamilyRects 21).imHi := by
    norm_num [Matrix.cons_val_21, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family21MidRect, record2677Family21PhiRect,
      record2677Family21CosRect, record2677Family21SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family22BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 22).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 22)
        (capturedModulations2584 22) (storedWidth 22 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family22PhiMem hx)
    (record2677Family22TrigMem hx).1 (record2677Family22TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 22)
    (theta := capturedModulations2584 22) (radius := storedWidth 22 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 22).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 22))
        record2677Family22MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 22))
      record2677Family22MidRect).reHi ≤ (record2678BaseM0FamilyRects 22).reHi ∧
    (record2678BaseM0FamilyRects 22).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 22))
        record2677Family22MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 22))
      record2677Family22MidRect).imHi ≤ (record2678BaseM0FamilyRects 22).imHi := by
    norm_num [Matrix.cons_val_22, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family22MidRect, record2677Family22PhiRect,
      record2677Family22CosRect, record2677Family22SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family23BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 23).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 23)
        (capturedModulations2584 23) (storedWidth 23 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family23PhiMem hx)
    (record2677Family23TrigMem hx).1 (record2677Family23TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 23)
    (theta := capturedModulations2584 23) (radius := storedWidth 23 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 23).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 23))
        record2677Family23MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 23))
      record2677Family23MidRect).reHi ≤ (record2678BaseM0FamilyRects 23).reHi ∧
    (record2678BaseM0FamilyRects 23).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 23))
        record2677Family23MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 23))
      record2677Family23MidRect).imHi ≤ (record2678BaseM0FamilyRects 23).imHi := by
    norm_num [Matrix.cons_val_23, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family23MidRect, record2677Family23PhiRect,
      record2677Family23CosRect, record2677Family23SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family24BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 24).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 24)
        (capturedModulations2584 24) (storedWidth 24 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family24PhiMem hx)
    (record2677Family24TrigMem hx).1 (record2677Family24TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 24)
    (theta := capturedModulations2584 24) (radius := storedWidth 24 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 24).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 24))
        record2677Family24MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 24))
      record2677Family24MidRect).reHi ≤ (record2678BaseM0FamilyRects 24).reHi ∧
    (record2678BaseM0FamilyRects 24).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 24))
        record2677Family24MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 24))
      record2677Family24MidRect).imHi ≤ (record2678BaseM0FamilyRects 24).imHi := by
    norm_num [Matrix.cons_val_24, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family24MidRect, record2677Family24PhiRect,
      record2677Family24CosRect, record2677Family24SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family25BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 25).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 25)
        (capturedModulations2584 25) (storedWidth 25 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family25PhiMem hx)
    (record2677Family25TrigMem hx).1 (record2677Family25TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 25)
    (theta := capturedModulations2584 25) (radius := storedWidth 25 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 25).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 25))
        record2677Family25MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 25))
      record2677Family25MidRect).reHi ≤ (record2678BaseM0FamilyRects 25).reHi ∧
    (record2678BaseM0FamilyRects 25).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 25))
        record2677Family25MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 25))
      record2677Family25MidRect).imHi ≤ (record2678BaseM0FamilyRects 25).imHi := by
    norm_num [Matrix.cons_val_25, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family25MidRect, record2677Family25PhiRect,
      record2677Family25CosRect, record2677Family25SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family26BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 26).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 26)
        (capturedModulations2584 26) (storedWidth 26 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family26PhiMem hx)
    (record2677Family26TrigMem hx).1 (record2677Family26TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 26)
    (theta := capturedModulations2584 26) (radius := storedWidth 26 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 26).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 26))
        record2677Family26MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 26))
      record2677Family26MidRect).reHi ≤ (record2678BaseM0FamilyRects 26).reHi ∧
    (record2678BaseM0FamilyRects 26).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 26))
        record2677Family26MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 26))
      record2677Family26MidRect).imHi ≤ (record2678BaseM0FamilyRects 26).imHi := by
    norm_num [Matrix.cons_val_26, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family26MidRect, record2677Family26PhiRect,
      record2677Family26CosRect, record2677Family26SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family27BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 27).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 27)
        (capturedModulations2584 27) (storedWidth 27 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family27PhiMem hx)
    (record2677Family27TrigMem hx).1 (record2677Family27TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 27)
    (theta := capturedModulations2584 27) (radius := storedWidth 27 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 27).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 27))
        record2677Family27MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 27))
      record2677Family27MidRect).reHi ≤ (record2678BaseM0FamilyRects 27).reHi ∧
    (record2678BaseM0FamilyRects 27).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 27))
        record2677Family27MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 27))
      record2677Family27MidRect).imHi ≤ (record2678BaseM0FamilyRects 27).imHi := by
    norm_num [Matrix.cons_val_27, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family27MidRect, record2677Family27PhiRect,
      record2677Family27CosRect, record2677Family27SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family28BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 28).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 28)
        (capturedModulations2584 28) (storedWidth 28 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family28PhiMem hx)
    (record2677Family28TrigMem hx).1 (record2677Family28TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 28)
    (theta := capturedModulations2584 28) (radius := storedWidth 28 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 28).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 28))
        record2677Family28MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 28))
      record2677Family28MidRect).reHi ≤ (record2678BaseM0FamilyRects 28).reHi ∧
    (record2678BaseM0FamilyRects 28).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 28))
        record2677Family28MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 28))
      record2677Family28MidRect).imHi ≤ (record2678BaseM0FamilyRects 28).imHi := by
    norm_num [Matrix.cons_val_28, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family28MidRect, record2677Family28PhiRect,
      record2677Family28CosRect, record2677Family28SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

set_option maxRecDepth 10000 in theorem record2678Family29BaseM0CellRectMem {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    (record2678BaseM0FamilyRects 29).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient 29)
        (capturedModulations2584 29) (storedWidth 29 ^ 2) x) := by
  have hmid := familyMidMem2676 (record2677Family29PhiMem hx)
    (record2677Family29TrigMem hx).1 (record2677Family29TrigMem hx).2
  have hprod := familyK0Mem2676 (c := record2678BaseCoefficient 29)
    (theta := capturedModulations2584 29) (radius := storedWidth 29 ^ 2)
    (x := x) hmid
  have hsub : (record2678BaseM0FamilyRects 29).reLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 29))
        record2677Family29MidRect).reLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 29))
      record2677Family29MidRect).reHi ≤ (record2678BaseM0FamilyRects 29).reHi ∧
    (record2678BaseM0FamilyRects 29).imLo ≤
      (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 29))
        record2677Family29MidRect).imLo ∧
    (ComplexRect2427.mul (ComplexRect2427.point (record2678BaseCoefficient 29))
      record2677Family29MidRect).imHi ≤ (record2678BaseM0FamilyRects 29).imHi := by
    norm_num [Matrix.cons_val_29, Matrix.cons_val_zero, record2678BaseM0FamilyRects, record2678BaseCoefficient,
      record2677Family29MidRect, record2677Family29PhiRect,
      record2677Family29CosRect, record2677Family29SinRect,
      ComplexRect2427.mul, RealInterval2429.mul, RealInterval2429.add,
      RealInterval2429.sub, ComplexRect2427.point, binary64Value2674,
      binary64ExponentBits2674, binary64Significand2674,
      binary64FractionBits2674, binary64Sign2674]
  exact rectSubset2676 hsub.1 hsub.2.1 hsub.2.2.1 hsub.2.2.2 hprod

theorem record2678BaseM0CellContained {x : ℝ}
    (hx : x ∈ Set.Icc 0 record2675CellRight) :
    record2675BaseM0Rect.Mem
      (externalPhysical2344 record2678BaseCoefficient
        capturedModulations2584 x) := by
  have hfamily : ∀ index, (record2678BaseM0FamilyRects index).Mem
      (externalFamilyValue2344 (record2678BaseCoefficient index)
        (capturedModulations2584 index) (storedWidth index ^ 2) x) := by
    intro index; fin_cases index
    · exact record2678Family0BaseM0CellRectMem hx
    · exact record2678Family1BaseM0CellRectMem hx
    · exact record2678Family2BaseM0CellRectMem hx
    · exact record2678Family3BaseM0CellRectMem hx
    · exact record2678Family4BaseM0CellRectMem hx
    · exact record2678Family5BaseM0CellRectMem hx
    · exact record2678Family6BaseM0CellRectMem hx
    · exact record2678Family7BaseM0CellRectMem hx
    · exact record2678Family8BaseM0CellRectMem hx
    · exact record2678Family9BaseM0CellRectMem hx
    · exact record2678Family10BaseM0CellRectMem hx
    · exact record2678Family11BaseM0CellRectMem hx
    · exact record2678Family12BaseM0CellRectMem hx
    · exact record2678Family13BaseM0CellRectMem hx
    · exact record2678Family14BaseM0CellRectMem hx
    · exact record2678Family15BaseM0CellRectMem hx
    · exact record2678Family16BaseM0CellRectMem hx
    · exact record2678Family17BaseM0CellRectMem hx
    · exact record2678Family18BaseM0CellRectMem hx
    · exact record2678Family19BaseM0CellRectMem hx
    · exact record2678Family20BaseM0CellRectMem hx
    · exact record2678Family21BaseM0CellRectMem hx
    · exact record2678Family22BaseM0CellRectMem hx
    · exact record2678Family23BaseM0CellRectMem hx
    · exact record2678Family24BaseM0CellRectMem hx
    · exact record2678Family25BaseM0CellRectMem hx
    · exact record2678Family26BaseM0CellRectMem hx
    · exact record2678Family27BaseM0CellRectMem hx
    · exact record2678Family28BaseM0CellRectMem hx
    · exact record2678Family29BaseM0CellRectMem hx
  have hsum := externalPhysicalFamilySumMem2676
    (rect := record2678BaseM0FamilyRects) hfamily
  rw [record2678BaseM0AggregateFamilySumEq] at hsum
  exact rectSubset2676 record2678BaseM0AggregateSubset.1
    record2678BaseM0AggregateSubset.2.1 record2678BaseM0AggregateSubset.2.2.1
    record2678BaseM0AggregateSubset.2.2.2 hsum

end ConnesWeilRH.Dev
