import ConnesWeilRH.Dev.C1RouteAWeightedCellPartition2684
import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic

set_option maxRecDepth 4096
set_option exponentiation.threshold 1200

namespace ConnesWeilRH.Dev

/-- Record 2684 cells 0 through 31,
decoded and summed as exact rationals. -/
def record2684ChunkBits0002685 : List Nat :=
  [0x1e3eb0b757f44876,
   0x1e3eaa6eee79dc5e,
   0x1e3ea427ce44e6f0,
   0x1e3e9de1f711c7ac,
   0x1e3e979d689d5c20,
   0x1e3e915a22a444c8,
   0x1e3e8b1824e3429f,
   0x1e3e84d76f173707,
   0x1e3e7e9800fcc69a,
   0x1e3e7859da511380,
   0x1e3e721cfad10316,
   0x1e3e6be162399b0b,
   0x1e3e65a710480158,
   0x1e3e5f6e04b91f70,
   0x1e3e59363f4a5bd2,
   0x1e3e52ffbfb8e068,
   0x1e3e4cca85c1f758,
   0x1e3e469691230aef,
   0x1e3e4063e199492f,
   0x1e3e3a3276e25ca3,
   0x1e3e340250bbb384,
   0x1e3e2dd36ee2dc28,
   0x1e3e27a5d11584e6,
   0x1e3e217977112006,
   0x1e3e1b4e60939be2,
   0x1e3e15248d5aaabb,
   0x1e3e0efbfd241ecc,
   0x1e3e08d4afadea32,
   0x1e3e02aea4b5c33b,
   0x1e3dfc89dbf9dbc4,
   0x1e3df666553829d0,
   0x1e3df044102ec33e]

theorem record2684ChunkBits000Length2685 :
    (record2684ChunkBits0002685).length = 32 := by
  decide

theorem record2684ChunkSum0002685 :
    ((record2684ChunkBits0002685).map binary64Value2674).sum =
      (68258615401029349 : ℚ) / 4052261297735344686047273304385899561535592023674254785152009111026028136145418111718463914987406049109568248643848426935932764722081811824108276205189417663145685354884286644224 := by
  norm_num [record2684ChunkBits0002685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 32 through 63,
decoded and summed as exact rationals. -/
def record2684ChunkBits0012685 : List Nat :=
  [0x1e3dea230c9bddaa,
   0x1e3de4034a3d7322,
   0x1e3ddde4c8d1f8c2,
   0x1e3dd7c78817a80a,
   0x1e3dd1ab87ccda37,
   0x1e3dcb90c7b0081f,
   0x1e3dc577477f6f4b,
   0x1e3dbf5f06f9c7d2,
   0x1e3db94805dd8e6c,
   0x1e3db33243e95f6b,
   0x1e3dad1dc0dbf6a0,
   0x1e3da70a7c73d4c6,
   0x1e3da0f8766ff4ac,
   0x1e3d9ae7ae8f15ff,
   0x1e3d94d8249017e0,
   0x1e3d8ec9d831f8d8,
   0x1e3d88bcc9337c8c,
   0x1e3d82b0f753e042,
   0x1e3d7ca662522654,
   0x1e3d769d09ed7074,
   0x1e3d7094ede4ff94,
   0x1e3d6a8e0df7da0c,
   0x1e3d648869e57f4c,
   0x1e3d5e84016d3418,
   0x1e3d5880d44e5c70,
   0x1e3d527ee2487b73,
   0x1e3d4c7e2b1ad9d8,
   0x1e3d467eae853900,
   0x1e3d40806c471fd6,
   0x1e3d3a836420345f,
   0x1e3d348795d03ba0,
   0x1e3d2e8d0116c078]

theorem record2684ChunkBits001Length2685 :
    (record2684ChunkBits0012685).length = 32 := by
  decide

theorem record2684ChunkSum0012685 :
    ((record2684ChunkBits0012685).map binary64Value2674).sum =
      (266133488720976717 : ℚ) / 16209045190941378744189093217543598246142368094697019140608036444104112544581672446873855659949624196438272994575393707743731058888327247296433104820757670652582741419537146576896 := by
  norm_num [record2684ChunkBits0012685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 64 through 95,
decoded and summed as exact rationals. -/
def record2684ChunkBits0022685 : List Nat :=
  [0x1e3d2893a5b3c5ec,
   0x1e3d229b836714ca,
   0x1e3d1ca499f094de,
   0x1e3d16aee9104cce,
   0x1e3d10ba7086095a,
   0x1e3d0ac730120eea,
   0x1e3d04d5277467ee,
   0x1e3cfee4566d3db0,
   0x1e3cf8f4bcbcd83a,
   0x1e3cf3065a2345e6,
   0x1e3ced192e610c3e,
   0x1e3ce72d3936770f,
   0x1e3ce1427a63f0e2,
   0x1e3cdb58f1aa02dc,
   0x1e3cd5709ec8fcb4,
   0x1e3ccf898181a4d0,
   0x1e3cc9a39994881a,
   0x1e3cc3bee6c25213,
   0x1e3cbddb68cbccbe,
   0x1e3cb7f91f7188e6,
   0x1e3cb2180a748d90,
   0x1e3cac382995a87c,
   0x1e3ca6597c95c5e4,
   0x1e3ca07c0335f066,
   0x1e3c9a9fbd36f99e,
   0x1e3c94c4aa5a28ec,
   0x1e3c8eeaca608ca8,
   0x1e3c89121d0b5180,
   0x1e3c833aa21bc26a,
   0x1e3c7d645952f194,
   0x1e3c778f42726678,
   0x1e3c71bb5d3b6fbe]

theorem record2684ChunkBits002Length2685 :
    (record2684ChunkBits0022685).length = 32 := by
  decide

theorem record2684ChunkSum0022685 :
    ((record2684ChunkBits0022685).map binary64Value2674).sum =
      (126663544241451 : ℚ) / 7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416708758372352 := by
  norm_num [record2684ChunkBits0022685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 96 through 127,
decoded and summed as exact rationals. -/
def record2684ChunkBits0032685 : List Nat :=
  [0x1e3c6be8a96f7a4c,
   0x1e3c661726d0112b,
   0x1e3c6046d51e86d8,
   0x1e3c5a77b41ca2a8,
   0x1e3c54a9c38bf354,
   0x1e3c4edd032e25b3,
   0x1e3c491172c504a2,
   0x1e3c4347121222ae,
   0x1e3c3d7de0d786bf,
   0x1e3c37b5ded6ff60,
   0x1e3c31ef0bd27918,
   0x1e3c2c29678bfe5c,
   0x1e3c2664f1c56180,
   0x1e3c20a1aa40e8c4,
   0x1e3c1adf90c0a23f,
   0x1e3c151ea506b9ec,
   0x1e3c0f5ee6d5798f,
   0x1e3c09a055eef308,
   0x1e3c03e2f215abac,
   0x1e3bfe26bb0bf0e3,
   0x1e3bf86bb0942dd4,
   0x1e3bf2b1d270eb50,
   0x1e3becf920647a8b,
   0x1e3be7419a319fa7,
   0x1e3be18b3f9ae71b,
   0x1e3bdbd61062fafc,
   0x1e3bd6220c4ca2f0,
   0x1e3bd06f331a6f30,
   0x1e3bcabd848f6274,
   0x1e3bc50d006e47fe,
   0x1e3bbf5da67a0896,
   0x1e3bb9af7675aa6e]

theorem record2684ChunkBits003Length2685 :
    (record2684ChunkBits0032685).length = 32 := by
  decide

theorem record2684ChunkSum0032685 :
    ((record2684ChunkBits0032685).map binary64Value2674).sum =
      (252850402708039545 : ℚ) / 16209045190941378744189093217543598246142368094697019140608036444104112544581672446873855659949624196438272994575393707743731058888327247296433104820757670652582741419537146576896 := by
  norm_num [record2684ChunkBits0032685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 128 through 159,
decoded and summed as exact rationals. -/
def record2684ChunkBits0042685 : List Nat :=
  [0x1e3bb4027023fc87,
   0x1e3bae5693483ff3,
   0x1e3ba8abdfa57e7b,
   0x1e3ba30254fedf5a,
   0x1e3b9d59f317a70f,
   0x1e3b97b2b9b2e328,
   0x1e3b920ca89412c4,
   0x1e3b8c67bf7e7e03,
   0x1e3b86c3fe358a44,
   0x1e3b8121647cba20,
   0x1e3b7b7ff217596b,
   0x1e3b75dfa6c92517,
   0x1e3b70408255a350,
   0x1e3b6aa28480776b,
   0x1e3b6505ad0d61cb,
   0x1e3b5f69fbbfec4c,
   0x1e3b59cf705c1180,
   0x1e3b54360aa5955b,
   0x1e3b4e9dca6058de,
   0x1e3b4906af505a03,
   0x1e3ccb96b3cb0b0b,
   0x1e59f5d8ebb47f6a,
   0x1e93abc8e9ba7d76,
   0x1ed157811e094130,
   0x1f0de52abe60b0b0,
   0x1f48e1130573d17c,
   0x1f83fc08aed2b984,
   0x1fbf01a2c1dc900e,
   0x1ff73e81b5799201,
   0x2030d9586cca4aca,
   0x2067a2150a2ea616,
   0x20a00ba0cc0668b6]

theorem record2684ChunkBits004Length2685 :
    (record2684ChunkBits0042685).length = 32 := by
  decide

theorem record2684ChunkSum0042685 :
    ((record2684ChunkBits0042685).map binary64Value2674).sum =
      (683439793607090793257457725 : ℚ) / 4052261297735344686047273304385899561535592023674254785152009111026028136145418111718463914987406049109568248643848426935932764722081811824108276205189417663145685354884286644224 := by
  norm_num [record2684ChunkBits0042685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 160 through 191,
decoded and summed as exact rationals. -/
def record2684ChunkBits0052685 : List Nat :=
  [0x20d51ac68ad258fc,
   0x210ae7775bd83722,
   0x2140a155e2de403e,
   0x2173f2ef83b289b0,
   0x21a73ba7306fe657,
   0x21da48e5e736a6a7,
   0x220ce79cf9577ba3,
   0x223eea1150527332,
   0x227016a09fc91fe0,
   0x22a07ed256bb68ac,
   0x22d0c7c2acad9a4e,
   0x2300aa09654c4a44,
   0x233025fd02bfd105,
   0x235edd3f61431fbb,
   0x238cc5e473335b31,
   0x23ba2c969cb0b014,
   0x23e73d9f68ecc5f3,
   0x2414261c5ac8a1e3,
   0x24410fbb1cc07c59,
   0x246c3af9ac3c6bdb,
   0x2496d3893f402ed8,
   0x24c20b6ad0313fe4,
   0x24ebe6bf211756b8,
   0x25151a7f1c147fcd,
   0x253f3df8a880f734,
   0x2566a3b5ecfe4033,
   0x259010ee22ab7e41,
   0x25b6569fb81a7077,
   0x25de6ff86aaccb86,
   0x2604540e16c83b2b,
   0x262aa0fef5e39ee1,
   0x26511c4e5dbcd1a8]

theorem record2684ChunkBits005Length2685 :
    (record2684ChunkBits0052685).length = 32 := by
  decide

theorem record2684ChunkSum0052685 :
    ((record2684ChunkBits0052685).map binary64Value2674).sum =
      (462128719342265605481887816799352874677315 : ℚ) / 921377545122446619199598286374089084696513969828232526459034741270904336521520715841339532514076847544303802497745079321233052888165232576308943909041185557531590656 := by
  norm_num [record2684ChunkBits0052685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 192 through 223,
decoded and summed as exact rationals. -/
def record2684ChunkBits0062685 : List Nat :=
  [0x267594af537c0d2f,
   0x269ab98742456ae7,
   0x26c06c5c274d41b2,
   0x26e42d2a80a1a457,
   0x270866064db643ff,
   0x272d23963daa74dc,
   0x27513d952d25edbd,
   0x27740e8a5fc98290,
   0x2796f11f17356d3d,
   0x27b9ce3f8288c345,
   0x27dc8c7b958dbdd0,
   0x27ff118402a76dcb,
   0x2820a1ec51dca284,
   0x284186407d73e0d7,
   0x28622c5234750493,
   0x28828d6cfed4b842,
   0x28a2a60792fdd3b7,
   0x28c275f7f4832f2d,
   0x28e20064a42b37c2,
   0x29014b7659a01390,
   0x29205fd433d339bf,
   0x293e8ff270a1bbe4,
   0x295c1ee9a6454b1a,
   0x297984513dc249b0,
   0x2996d72867e56bd6,
   0x29b42c7905768e56,
   0x29d1966fd2eacf40,
   0x29ee8f3606c6e827,
   0x2a0aa41839bb2919,
   0x2a26f9426b8ae1b2,
   0x2a43c16a8f82e00d,
   0x2a60d80e731af5d6]

theorem record2684ChunkBits006Length2685 :
    (record2684ChunkBits0062685).length = 32 := by
  decide

theorem record2684ChunkSum0062685 :
    ((record2684ChunkBits0062685).map binary64Value2674).sum =
      (61794585073159948701314379077793931 : ℚ) / 2977131414714805823690030317109266572712515013375254774912983855843898524112477893944078543723575564536883288499266264815757728270805630976 := by
  norm_num [record2684ChunkBits0062685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 224 through 255,
decoded and summed as exact rationals. -/
def record2684ChunkBits0072685 : List Nat :=
  [0x2a7c5f0c39b1ed3c,
   0x2a979a16fa95293d,
   0x2ab36545fca393f5,
   0x2acf7e1920fada88,
   0x2ae942a594e5c773,
   0x2b04052c3696c146,
   0x2b1f5c1821cfc47a,
   0x2b3846232492887f,
   0x2b529268cb64773f,
   0x2b6c17ee2a683b5c,
   0x2b8502113d22c3f3,
   0x2b9f118a87ab2fdf,
   0x2bb6b86343ce5ea4,
   0x2bd06f4cc88f35c6,
   0x2be785a193ca9c37,
   0x2c00a7decb9bde87,
   0x2c175819f542858c,
   0x2c30319ccc319507,
   0x2c463ecadca61747,
   0x2c5e439c91d35e06,
   0x2c748fa29657eef4,
   0x2c8c178e7766e6df,
   0x2ca3104226c2ef3b,
   0x2cb9f731171c4a55,
   0x2cd18539e1dbc6a6,
   0x2ce76cdc48af28fd,
   0x2cff07a793a7e144,
   0x2d145c7f8d227386,
   0x2d2a79844ccc2b79,
   0x2d410dab23f4b8e2,
   0x2d55c4bb562f7e67,
   0x2d6b88dd48ac659d]

theorem record2684ChunkBits007Length2685 :
    (record2684ChunkBits0072685).length = 32 := by
  decide

theorem record2684ChunkSum0072685 :
    ((record2684ChunkBits0072685).map binary64Value2674).sum =
      (27419259098564414945435067 : ℚ) / 2462625387274654950767440006258975862817483704404090416746768337765357610718575663213391640930307227550414249394176 := by
  norm_num [record2684ChunkBits0072685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 256 through 287,
decoded and summed as exact rationals. -/
def record2684ChunkBits0082685 : List Nat :=
  [0x2d8141c81eda63d3,
   0x2d95700b1d7acab2,
   0x2daa653269ded934,
   0x2dc01b771e6daf49,
   0x2dd37cf3cd6a7ab9,
   0x2de7607950c65500,
   0x2dfbce1cf134948b,
   0x2e10661be584df32,
   0x2e232f84ece41032,
   0x2e364437db2bea20,
   0x2e49a3d9bb8a43c8,
   0x2e5d4cc04bb7384d,
   0x2e709e0079319226,
   0x2e82d94e2208952f,
   0x2e958554907e0a2f,
   0x2ea898cf4562a8a7,
   0x2ebc206b07aee872,
   0x2ecfeeb6bc237c6b,
   0x2ee1fedcc7870f14,
   0x2ef4229d8a12f642,
   0x2f065d63f58bffa0,
   0x2f18a8e66df38774,
   0x2f2afde4dcd5715a,
   0x2f3d544dd1d0a7ea,
   0x2f4fa36e8b902165,
   0x2f60f11642b10340,
   0x2f7203a3498ceaca,
   0x2f8304cd8b4b7d39,
   0x2f93f0383c6f7633,
   0x2fa4c1de69991502,
   0x2fb57634cfc910c4,
   0x2fc60a482f0a4fc8]

theorem record2684ChunkBits008Length2685 :
    (record2684ChunkBits0082685).length = 32 := by
  decide

theorem record2684ChunkSum0082685 :
    ((record2684ChunkBits0082685).map binary64Value2674).sum =
      (825902208585904119335058231 : ℚ) / 286687326998758938951352611912760867599570623646035140467198604923365359511060601008752319138765710819328 := by
  norm_num [record2684ChunkBits0082685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 288 through 319,
decoded and summed as exact rationals. -/
def record2684ChunkBits0092685 : List Nat :=
  [0x2fd67bd6ae2d24ac,
   0x2fe6c96319a152c7,
   0x2ff6f2410b59b5d9,
   0x3006f6995a15ff27,
   0x3016d7668705b9cc,
   0x30269669bdf32b6a,
   0x30365a3a21b1f6ed,
   0x304646bea2950a06,
   0x3056648c7b8c2e35,
   0x30666c59fbf2dd8b,
   0x30765330e81a307c,
   0x3086190432282517,
   0x3095be7d70c5cb19,
   0x30a544f4e241635b,
   0x30b4ae630607c1a0,
   0x30c3fd4d3985a46b,
   0x30d334ae636b93bc,
   0x30e257dce0d53f21,
   0x30f16a6eed763441,
   0x3100701eb6341b0d,
   0x310ed95e5d9a66ab,
   0x311cc7a54348e812,
   0x312ab2278e59b11d,
   0x31389f84070cd3b2,
   0x314695c26f2d6806,
   0x31549a3ac3c15fbd,
   0x3162b1843a1b62e7,
   0x3170df6bc0e72525,
   0x317e4de30db6e376,
   0x318b1499d96c6a7f,
   0x319815eb68b762ae,
   0x31a57208040d9233]

theorem record2684ChunkBits009Length2685 :
    (record2684ChunkBits0092685).length = 32 := by
  decide

theorem record2684ChunkSum0092685 :
    ((record2684ChunkBits0092685).map binary64Value2674).sum =
      (3682495353995277454107403 : ℚ) / 1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512 := by
  norm_num [record2684ChunkBits0092685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 320 through 351,
decoded and summed as exact rationals. -/
def record2684ChunkBits0102685 : List Nat :=
  [0x31b352164aa77090,
   0x31c188262356918a,
   0x31cfabcc19a2a3bb,
   0x31dc78cf053499fb,
   0x31e9790b5f0a90aa,
   0x31f6adae7027408f,
   0x3204174c50ed75d4,
   0x3211b5d983cacbfa,
   0x321f115b27f7f5c6,
   0x322b1d19d3db782e,
   0x32378b702171db2b,
   0x324457fd71f0e020,
   0x32517da9d42e0748,
   0x325deda419a76c5f,
   0x32697ae6056a0080,
   0x327596a590f2580b,
   0x3282344be8b9e441,
   0x328e8ec1958cd8da,
   0x32998783dc8f5c27,
   0x32a53b9fe143c88b,
   0x32b19521ecb116b9,
   0x32bcff2655830af2,
   0x32c7d0344a90a1e3,
   0x32d37b1485216ff1,
   0x32dfe9faf30f22dd,
   0x32eaa128747dd8fc,
   0x32f640497baa5e66,
   0x3302856d2d671af6,
   0x330eb5f84cb1715c,
   0x33195ba999e0e6f8,
   0x3324da00e0e4a1bf,
   0x333112efd4dd75ef]

theorem record2684ChunkBits010Length2685 :
    (record2684ChunkBits0102685).length = 32 := by
  decide

theorem record2684ChunkSum0102685 :
    ((record2684ChunkBits0102685).map binary64Value2674).sum =
      (102688151843678584648931 : ℚ) / 971334446112864535459730953411759453321203419526069760625906204869452142602604249088 := by
  norm_num [record2684ChunkBits0102685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 352 through 383,
decoded and summed as exact rationals. -/
def record2684ChunkBits0112685 : List Nat :=
  [0x333bd7c91ded47e1,
   0x33469aea94a030a5,
   0x3352462b88e528c2,
   0x335d6b4cbb16cdad,
   0x3367945348d08f5f,
   0x3372d1817e72cd9c,
   0x337de90bce8ea85e,
   0x3387aba30185595a,
   0x3392a79e8bc1670b,
   0x339d48a51bce78c2,
   0x33a6e46fe1d24ac7,
   0x33b1d360cf866805,
   0x33bba7a0f5faf362,
   0x33c55f56ee0efa80,
   0x33d07555b6b56171,
   0x33d9430dfc1cfc48,
   0x33e353244707043b,
   0x33edb8b646d4fc7f,
   0x33f7439f843fc5a5,
   0x340230976b5fe395,
   0x340c59eb68ee4c0e,
   0x341604f88b893d93,
   0x34210ab3a2b69bf2,
   0x342a48c890afae0c,
   0x3434322316e9eab8,
   0x343eebc0abd65093,
   0x3447952bc946cc38,
   0x3451eb33e3cb5b83,
   0x345b20d93142d8c4,
   0x3464757382eb6b93,
   0x346ebe34d57ca554,
   0x347703506c0543b4]

theorem record2684ChunkBits011Length2685 :
    (record2684ChunkBits0112685).length = 32 := by
  decide

theorem record2684ChunkSum0112685 :
    ((record2684ChunkBits0112685).map binary64Value2674).sum =
      (20169347757338356902527 : ℚ) / 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  norm_num [record2684ChunkBits0112685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 384 through 415,
decoded and summed as exact rationals. -/
def record2684ChunkBits0122685 : List Nat :=
  [0x348129d5aae81431,
   0x3489824469f23916,
   0x3492e379d58baaa9,
   0x349be012b76abf80,
   0x34a47fb01ae96ee2,
   0x34ae0c865e4be289,
   0x34b5f4379c33c1db,
   0x34bffb4a6ee0afb7,
   0x34c73a2fd4057f8c,
   0x34d0d2d19d1c2cb8,
   0x34d8adfdcebb2a16,
   0x34e24992a8b90c39,
   0x34eb15f6a96453bb,
   0x34f4005819bb1a3c,
   0x34fd73aa134d2ef4,
   0x35059df91023dd4c,
   0x350fa207d707599f,
   0x351711fb1d2655b9,
   0x3520c53be85b757f,
   0x35284d2e03cb0bb9,
   0x35318c7f8fa48f93,
   0x353942c1833b5cdd,
   0x35421ed79511c474,
   0x3549e933216b7951,
   0x355276e8cd137223,
   0x355a3b049aa7d609,
   0x3562925dc233a60c,
   0x356a372d24a31a82,
   0x3572721b96d50229,
   0x3579e13bdc9283ef,
   0x35821a3ce1d2d3bd,
   0x358941269b63d5e6]

theorem record2684ChunkBits012Length2685 :
    (record2684ChunkBits0122685).length = 32 := by
  decide

theorem record2684ChunkSum0122685 :
    ((record2684ChunkBits0122685).map binary64Value2674).sum =
      (1615967950107773397077 : ℚ) / 55213970774324510299478046898216203619608871777363092441300193790394368 := by
  norm_num [record2684ChunkBits0122685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 416 through 447,
decoded and summed as exact rationals. -/
def record2684ChunkBits0132685 : List Nat :=
  [0x359191d144811684,
   0x359862c1cdbbe650,
   0x35a0f93236e00847,
   0x35a7db577a0f7a04,
   0x35b0e4c5bb4bebac,
   0x35b7ebd7c6fa65b4,
   0x35c0e4aea3e38471,
   0x35c7cc0a008143c6,
   0x35d0b70d06b529ea,
   0x35d76a3e687f44f7,
   0x35e05a5ca7a0a205,
   0x35e6c658b8916c61,
   0x35ef9fdc070271e0,
   0x35f5e41291a81bff,
   0x35fe3739acde04e1,
   0x3604ca736aa47922,
   0x360c86bbf1197ae4,
   0x3613831b561c17b0,
   0x361a9d6917609d32,
   0x36221974396c74d0,
   0x36288c36eb73352e,
   0x363099dae28d88e1,
   0x363664dd2117ab57,
   0x363e219dac45ee08,
   0x364438babb168fcc,
   0x364b1468b5c1030b,
   0x36521d425742fd1c,
   0x36587605b0a911f6,
   0x36608baffa65e335,
   0x36668f3922537e48,
   0x366ec351ce4fc57f,
   0x3674ed4f3991f1cf]

theorem record2684ChunkBits013Length2685 :
    (record2684ChunkBits0132685).length = 32 := by
  decide

theorem record2684ChunkSum0132685 :
    ((record2684ChunkBits0132685).map binary64Value2674).sum =
      (183533498391348697145 : ℚ) / 210624583337114373395836055367340864637790190801098222508621955072 := by
  norm_num [record2684ChunkBits0132685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 448 through 479,
decoded and summed as exact rationals. -/
def record2684ChunkBits0142685 : List Nat :=
  [0x367c675ace69fd8d,
   0x36833a5c763a2a29,
   0x3689f75851593435,
   0x36917ca7c65ab4ef,
   0x36977d8a6e5de180,
   0x369f784647c83200,
   0x36a505cbd11c5005,
   0x36ac02c51a3e5bbc,
   0x36b29c36c479618c,
   0x36b8a97e16187f3b,
   0x36c04c12649df1de,
   0x36c57b5f6026fe82,
   0x36cc3e1a1c4ae8d4,
   0x36d284b1212ebf49,
   0x36d839812d457023,
   0x36df9d2caaacd5a5,
   0x36e494eff2ce2f1f,
   0x36eabdc57f199a22,
   0x36f15651d00b6034,
   0x36f6abc44a6018fd,
   0x36fda3d1dac6fad9,
   0x3703694a1333136a,
   0x3709a1355b6ddb0b,
   0x3710ed240badd387,
   0x37164f7554b05619,
   0x371d57b981b2c075,
   0x37234078505461d1,
   0x372933fa9397000b,
   0x3730750edcf03ec6,
   0x373570ab822abf87,
   0x373bdcc8a73d3cda,
   0x37420f1ff4dc83ba]

theorem record2684ChunkBits014Length2685 :
    (record2684ChunkBits0142685).length = 32 := by
  decide

theorem record2684ChunkSum0142685 :
    ((record2684ChunkBits0142685).map binary64Value2674).sum =
      (178419687984041961917 : ℚ) / 25711008708143844408671393477458601640355247900524685364822016 := by
  norm_num [record2684ChunkBits0142685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 480 through 511,
decoded and summed as exact rationals. -/
def record2684ChunkBits0152685 : List Nat :=
  [0x374759f9863559e7,
   0x374e1e91e9e33a8b,
   0x37536051b7f8bedf,
   0x3758de6a8f1cac10,
   0x375fd757cc8a7100,
   0x376455fe96ec72cc,
   0x3769ea76e4915bb4,
   0x37707a05ddd94d6c,
   0x3774e7f5ec7c53bc,
   0x377a78f4a617d3c3,
   0x3780ba8374f19ed0,
   0x378540de8edeece2,
   0x378b1ae144b3b7ae,
   0x37913cabec9217ef,
   0x3795f6aa61ca9ca0,
   0x379c36f8c306b60b,
   0x37a221f11e47e4ea,
   0x37a742efa31321af,
   0x37adc7d73e3505c9,
   0x37b305efd49e3f5c,
   0x37b8400f88752be2,
   0x37bed834f5ea0810,
   0x37c3924d035dec5f,
   0x37c8c7a98b4b6adf,
   0x37cf4d4958b58e13,
   0x37d3b972d415d3ef,
   0x37d8ccf71af147be,
   0x37df1ca0b46b82e6,
   0x37e3786a3d8461e6,
   0x37e850d1b38c9c12,
   0x37ee4d0a7eb0a633,
   0x37f2d70a560f39f2]

theorem record2684ChunkBits015Length2685 :
    (record2684ChunkBits0152685).length = 32 := by
  decide

theorem record2684ChunkSum0152685 :
    ((record2684ChunkBits0152685).map binary64Value2674).sum =
      (6709139402130818349 : ℚ) / 392318858461667547739736838950479151006397215279002157056 := by
  norm_num [record2684ChunkBits0152685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 512 through 543,
decoded and summed as exact rationals. -/
def record2684ChunkBits0162685 : List Nat :=
  [0x37f76170a405d74c,
   0x37fcf5aae59376d0,
   0x3801e7019aa0e594,
   0x38062eb8c8936772,
   0x380bb0b1edb430b8,
   0x38113d6613f98905,
   0x38156a0b54ffb4fc,
   0x381aa5bbc561f3c3,
   0x3820b75a6ef5737e,
   0x3824fcb2856924fd,
   0x382a4d4222518a2f,
   0x3830733175c61795,
   0x3834893d76ef509f,
   0x383995c30083f3db,
   0x383fcf0b2b18581a,
   0x3843bb37242a0de6,
   0x38486d33e345f3c9,
   0x384e2c8436584174,
   0x385298b609c23586,
   0x3856df8f2c30abf9,
   0x385c12dfe6e52fed,
   0x38613132a1ef43fd,
   0x38650379b4679aed,
   0x3869a21532a06035,
   0x386f3542b8f33468,
   0x3872f676b649ed29,
   0x38770118ea785011,
   0x387be3e9aa3cc90c,
   0x388116241b6d5a8c,
   0x3884e3464374346b,
   0x38897a21523023a1,
   0x388f015b4d7780ff]

theorem record2684ChunkBits016Length2685 :
    (record2684ChunkBits0162685).length = 32 := by
  decide

theorem record2684ChunkSum0162685 :
    ((record2684ChunkBits0162685).map binary64Value2674).sum =
      (3086088283351215085 : ℚ) / 191561942608236107294793378393788647952342390272950272 := by
  norm_num [record2684ChunkBits0162685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 544 through 575,
decoded and summed as exact rationals. -/
def record2684ChunkBits0172685 : List Nat :=
  [0x3892e63e418b53d8,
   0x38973b02c1fdf100,
   0x389c93ad62a22185,
   0x38a18c0b4f5345fb,
   0x38a582a8d60c2d66,
   0x38aa51e98a065120,
   0x38b0125618cca3e1,
   0x38b396c7c432fdc0,
   0x38b7d41c508ca40e,
   0x38bced65b8bce0c5,
   0x38c185e7a14ac532,
   0x38c52fcd1159f8e0,
   0x38c990a1c65e917f,
   0x38cec96e4c0f3809,
   0x38d28067ae16afa7,
   0x38d631f2a68d61af,
   0x38da93b8d913c2c6,
   0x38dfc4986ba00f78,
   0x38e2f45cb12bf903,
   0x38e6954711cb53fd,
   0x38eb2e7c34bac872,
   0x38f05958ad70d4fb,
   0x38f3a0401cdd4808,
   0x38f782d6cab904a5,
   0x38fc1ba1c319696c,
   0x3900d45e4fa2729a,
   0x390451b4e6dca54e,
   0x39088db1a12b72f2,
   0x390d9f5c8aef95bc,
   0x3911d6bae653b43d,
   0x39157288f2d43297,
   0x3919bd413d86cf6b]

theorem record2684ChunkBits017Length2685 :
    (record2684ChunkBits0172685).length = 32 := by
  decide

theorem record2684ChunkSum0172685 :
    ((record2684ChunkBits0172685).map binary64Value2674).sum =
      (10989178528797949055 : ℚ) / 1496577676626844588240573268701473812127674924007424 := by
  norm_num [record2684ChunkBits0172685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 576 through 607,
decoded and summed as exact rationals. -/
def record2684ChunkBits0182685 : List Nat :=
  [0x391ed531041dbb01,
   0x39226eb0aefd485e,
   0x3925ff21a6664ac0,
   0x392a333a4850d77a,
   0x392f25d0e2b39908,
   0x39327ae2f20457c7,
   0x3935e34e0776389b,
   0x3939e09596a2ec7c,
   0x393e8a39db3e5195,
   0x3941fda791fc1c4e,
   0x3945298984864ade,
   0x3948dad40377fe3d,
   0x394d6cacd00b2750,
   0x395172fadfd8d199,
   0x3954a7bf7f77a663,
   0x39586753b78e70c2,
   0x395cc70e5da378f3,
   0x3960efa6a36dd7f6,
   0x3963f71e8c0522b9,
   0x3967ba7ed13f48f9,
   0x396c39f72659343f,
   0x3970c3423baf9356,
   0x3973e0a8d03e87bb,
   0x3977882451b82f16,
   0x397bcf53df44288a,
   0x3980676b3378b2ae,
   0x398351552cbc816b,
   0x3986b54ca81bfb7e,
   0x398aa5595d2a5691,
   0x398f35ec47a118fd,
   0x39923f188affc63c,
   0x39954c36aee8810c]

theorem record2684ChunkBits018Length2685 :
    (record2684ChunkBits0182685).length = 32 := by
  decide

theorem record2684ChunkSum0182685 :
    ((record2684ChunkBits0182685).map binary64Value2674).sum =
      (10218604920413749381 : ℚ) / 5846006549323611672814739330865132078623730171904 := by
  norm_num [record2684ChunkBits0182685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 608 through 639,
decoded and summed as exact rationals. -/
def record2684ChunkBits0192685 : List Nat :=
  [0x3998d1388711d278,
   0x399cdf0f1d81cf01,
   0x39a0c481bba610e4,
   0x39a3728cc798d7c6,
   0x39a6b08cd2986857,
   0x39aa934e32729ccc,
   0x39af1236e5a57149,
   0x39b221a27e64b34b,
   0x39b51fa1357aeaab,
   0x39b891104577596c,
   0x39bc85b1bbb4142d,
   0x39c094b8edf4b00f,
   0x39c36f0775eac4c0,
   0x39c6cc545381468c,
   0x39cab4ad7531c93b,
   0x39cf3c274cc0631a,
   0x39d23cacfbfd50b4,
   0x39d542d21f7b5734,
   0x39d8bebcf3073b6a,
   0x39dcc05d4888e287,
   0x39e0acc4c602929c,
   0x39e34f1b49203ac9,
   0x39e6525c0b7bfe70,
   0x39e9c30613b4f476,
   0x39edaf1a2cc1f049,
   0x39f113288064a59e,
   0x39f39d2d060f41c2,
   0x39f67f9505939923,
   0x39f9e9d4fc02b3af,
   0x39fe03cdf687192e,
   0x3a015aa573875902,
   0x3a0408d567c397fa]

theorem record2684ChunkBits019Length2685 :
    (record2684ChunkBits0192685).length = 32 := by
  decide

theorem record2684ChunkSum0192685 :
    ((record2684ChunkBits0192685).map binary64Value2674).sum =
      (5311793283851358577 : ℚ) / 22835963083295358096932575511191922182123945984 := by
  norm_num [record2684ChunkBits0192685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 640 through 671,
decoded and summed as exact rationals. -/
def record2684ChunkBits0202685 : List Nat :=
  [0x3a071740b79da664,
   0x3a0a91eca3e27def,
   0x3a0e86408efd08a0,
   0x3a118199fe3f746a,
   0x3a141b29f0753add,
   0x3a1746835e159db6,
   0x3a1af8075250eceb,
   0x3a1f34494b9f73ee,
   0x3a220697f6016587,
   0x3a24cb4b74f2d2e9,
   0x3a27f33d7dcbbe72,
   0x3a2b8a97c74945eb,
   0x3a2f9ecd3f427bfa,
   0x3a321f5dc76e09a5,
   0x3a34bd692027d78d,
   0x3a37b2a06150f5ce,
   0x3a3b09169730a674,
   0x3a3ecbfb9bee28e9,
   0x3a4183e1b1e0c82d,
   0x3a43e52b18951ba1,
   0x3a46a7cc4d21fa56,
   0x3a49fb2cf327dfa5,
   0x3a4dbfead571d2fb,
   0x3a51019aa6d4c136,
   0x3a5369c9e04ec263,
   0x3a56208556a9c7c2,
   0x3a592ea3b0121b98,
   0x3a5c9dea06ca7bb3,
   0x3a603c95a18b8e08,
   0x3a62721ed8b4d25f,
   0x3a651e5b7a7d0544,
   0x3a683335a0ee23ce]

theorem record2684ChunkBits020Length2685 :
    (record2684ChunkBits0202685).length = 32 := by
  decide

theorem record2684ChunkSum0202685 :
    ((record2684ChunkBits0202685).map binary64Value2674).sum =
      (3472569876064132579 : ℚ) / 178405961588244985132285746181186892047843328 := by
  norm_num [record2684ChunkBits0202685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 672 through 703,
decoded and summed as exact rationals. -/
def record2684ChunkBits0212685 : List Nat :=
  [0x3a6bb185e113b57c,
   0x3a6fa57499777727,
   0x3a720e295d6d8ea0,
   0x3a749257c6723489,
   0x3a77673ae6d5c9e3,
   0x3a7a9586417ad283,
   0x3a7e26be063a2085,
   0x3a8112a6b0fd076a,
   0x3a834e50ab8244ed,
   0x3a85cca4f23f1e58,
   0x3a889490d7f24eff,
   0x3a8badbe9f2045aa,
   0x3a8f339cdc1bd8f6,
   0x3a91bb490ed5a6ff,
   0x3a942005be83bcac,
   0x3a96cf256bcae80c,
   0x3a99d06f31370e85,
   0x3a9d2c60fa9ea85d,
   0x3aa07621a7c611a3,
   0x3aa28d208cfa1c09,
   0x3aa4e0c238881e09,
   0x3aa7772cd3bbc9d1,
   0x3aaa665eeed523d7,
   0x3aaded4aec71e810,
   0x3ab0fa13e2e4f5a8,
   0x3ab33c6b50c45d8c,
   0x3ab5c426005b6e12,
   0x3ab89847bd60e2e5,
   0x3abbc0665544cf90,
   0x3abf44b6c73488eb,
   0x3ac1970e419c03e0,
   0x3ac3c31d5b959668]

theorem record2684ChunkBits021Length2685 :
    (record2684ChunkBits0212685).length = 32 := by
  decide

theorem record2684ChunkSum0212685 :
    ((record2684ChunkBits0212685).map binary64Value2674).sum =
      (3062765624051359835 : ℚ) / 2787593149816327892691964784081045188247552 := by
  norm_num [record2684ChunkBits0212685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 704 through 735,
decoded and summed as exact rationals. -/
def record2684ChunkBits0222685 : List Nat :=
  [0x3ac62bc4f52e06c0,
   0x3ac8d6b97e257cc4,
   0x3acbca3837996b3d,
   0x3acf0d1a0e2fc904,
   0x3ad1583a493363d8,
   0x3ad38e1ea204819d,
   0x3ad604d760f5fa97,
   0x3ad8c2a9bbf20dec,
   0x3adbce5d0842c6ad,
   0x3adf2f46fe55c046,
   0x3ae176ad3df48a55,
   0x3ae3889cb7683c50,
   0x3ae5d2255af04e2a,
   0x3ae8586a767c14fc,
   0x3aeb210fa1ecd04a,
   0x3aee41a4eeac5218,
   0x3af0ff32c6256bc1,
   0x3af31c8219432761,
   0x3af5763f430402e3,
   0x3af811f80dce0d78,
   0x3afaf5a10fb61c8f,
   0x3afe279b0f605db6,
   0x3b00d75ec1706bdb,
   0x3b02c9318dfe8b66,
   0x3b04ed3bf799332b,
   0x3b0747c5f8841032,
   0x3b09dd75631a4b98,
   0x3b0cb35a5f4a71e4,
   0x3b0fcf02f28f7b8e,
   0x3b11cc90cdd094a5,
   0x3b13e5d2e79e8cc9,
   0x3b16377f941279c2]

theorem record2684ChunkBits022Length2685 :
    (record2684ChunkBits0222685).length = 32 := by
  decide

theorem record2684ChunkSum0222685 :
    ((record2684ChunkBits0222685).map binary64Value2674).sum =
      (1868992750793941215 : ℚ) / 43556142965880123323311949751266331066368 := by
  norm_num [record2684ChunkBits0222685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 736 through 767,
decoded and summed as exact rationals. -/
def record2684ChunkBits0232685 : List Nat :=
  [0x3b18c67f70c7998b,
   0x3b1b9816d4b2c119,
   0x3b1eb1ef1356fa9d,
   0x3b210d10f0a2dbf5,
   0x3b22eba3b07a7a48,
   0x3b24f843bb3f29d2,
   0x3b2736d78ce1c957,
   0x3b29aba53be77037,
   0x3b2c683812d74d96,
   0x3b2fa879c7dc7e5f,
   0x3b31a7706612a546,
   0x3b33aa6cc24d3fc4,
   0x3b35e11cd7bcc717,
   0x3b384fab227866ac,
   0x3b3afa84b6cf4d1f,
   0x3b3de660d6e22a79,
   0x3b408c25292f4c0b,
   0x3b424ad4f1b81136,
   0x3b44322a7f54c1d9,
   0x3b46454ddf887d58,
   0x3b4887b0b165ed9d,
   0x3b4b3deaafc0cda1,
   0x3b4e4152b8421923,
   0x3b50c8356718824d,
   0x3b52989b23a9f52a,
   0x3b54950dde182bcc,
   0x3b56c0f7814f41f7,
   0x3b591ffed1dbe3a8,
   0x3b5bb60f3283ae05,
   0x3b5e87624a6aca30,
   0x3b60cc45f88270c7,
   0x3b627744681cff50]

theorem record2684ChunkBits023Length2685 :
    (record2684ChunkBits0232685).length = 32 := by
  decide

theorem record2684ChunkSum0232685 :
    ((record2684ChunkBits0232685).map binary64Value2674).sum =
      (1681188129680925921 : ℚ) / 1361129467683753853853498429727072845824 := by
  norm_num [record2684ChunkBits0232685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 768 through 799,
decoded and summed as exact rationals. -/
def record2684ChunkBits0242685 : List Nat :=
  [0x3b6447681c2cecb3,
   0x3b66489ead16a2da,
   0x3b68a6dae4bb37ce,
   0x3b6b4aaa3c454ed9,
   0x3b6e2de7c2199046,
   0x3b70aa9b339b66fd,
   0x3b7262be17a48c24,
   0x3b7441f29dbaae1b,
   0x3b764af6e7280042,
   0x3b7880b781d7e436,
   0x3b7ae656dc10a908,
   0x3b7d7f3460a6cda3,
   0x3b80277cb2b03734,
   0x3b81d07dd2ac5c59,
   0x3b83aac4f1b3f596,
   0x3b85b0a84e29e202,
   0x3b87e551efe26354,
   0x3b8a4c1989071977,
   0x3b8ce889281dec2a,
   0x3b8fbe632df2e00e,
   0x3b9168d4e8c1017a,
   0x3b931354434242f6,
   0x3b94e0ffd2e46315,
   0x3b96d459603b43c6,
   0x3b98f01d080aeb75,
   0x3b9b374bbdcdbab6,
   0x3b9db7a36d8e884f,
   0x3ba053ff368b02d8,
   0x3ba1f49c33e857d4,
   0x3ba3b92a684d447a,
   0x3ba5a40194d1ab89,
   0x3ba7b7988b4a8869]

theorem record2684ChunkBits024Length2685 :
    (record2684ChunkBits0242685).length = 32 := by
  decide

theorem record2684ChunkSum0242685 :
    ((record2684ChunkBits0242685).map binary64Value2674).sum =
      (8956019916498143 : ℚ) / 332306998946228968225951765070086144 := by
  norm_num [record2684ChunkBits0242685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 800 through 831,
decoded and summed as exact rationals. -/
def record2684ChunkBits0252685 : List Nat :=
  [0x3ba9f686ac76bce5,
   0x3bac6389e1297b7b,
   0x3baf018f078a1d95,
   0x3bb0e9dc0084d846,
   0x3bb26eb3b8cbfd28,
   0x3bb43231c679820b,
   0x3bb62cb974311e14,
   0x3bb85307e1944cc5,
   0x3bbaa803a0d7aa54,
   0x3bbd2eb74d2310ad,
   0x3bbfea55766008c1,
   0x3bc16f1ed8953ec0,
   0x3bc30701853319d3,
   0x3bc4beba1304f31a,
   0x3bc69852ac448c2c,
   0x3bc895fe88ac15f2,
   0x3bcaba217964f04b,
   0x3bcd0758fb8afb8a,
   0x3bcf8087016ccfa8,
   0x3bd119a24de9d541,
   0x3bd2ad550491e093,
   0x3bd469bb045fee67,
   0x3bd6496e328b7918,
   0x3bd84e7c7851d522,
   0x3bda7b0dd949b1a0,
   0x3bdcd165da6f9be7,
   0x3bdf53ea677531ed,
   0x3be1029577e1463d,
   0x3be273f47f19f906,
   0x3be4194ec29730c4,
   0x3be5f50ab6caa5d9,
   0x3be7f787aef833f4]

theorem record2684ChunkBits025Length2685 :
    (record2684ChunkBits0252685).length = 32 := by
  decide

theorem record2684ChunkSum0252685 :
    ((record2684ChunkBits0252685).map binary64Value2674).sum =
      (1230210597887030213 : ℚ) / 2658455991569831745807614120560689152 := by
  norm_num [record2684ChunkBits0252685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 832 through 863,
decoded and summed as exact rationals. -/
def record2684ChunkBits0262685 : List Nat :=
  [0x3bea231ddd3506fa,
   0x3bec7a3df0668dc7,
   0x3beeff740681ac1e,
   0x3bf0dab5c5186b27,
   0x3bf24f7a16130797,
   0x3bf3df8416e9e1c8,
   0x3bf58c6a1c35ca81,
   0x3bf757e07fb1940e,
   0x3bf943bf787ba03c,
   0x3bfb520a1c4ae5da,
   0x3bfd84f6ab0bb983,
   0x3bffdef84431442a,
   0x3c0135e080499e12,
   0x3c02b17d56cc8e88,
   0x3c04510b08817bd8,
   0x3c060f0c71489e2c,
   0x3c07ed17b87bfbbb,
   0x3c09ecd77d90f1c6,
   0x3c0c100c6ef450b8,
   0x3c0e589281880249,
   0x3c1064348b21fc7f,
   0x3c11c17c8f753fd6,
   0x3c134ec1e14ab77c,
   0x3c14fa9e203f980c,
   0x3c16c6c1ac471f77,
   0x3c18b4eb2f3e851f,
   0x3c1ac6e9a0f62088,
   0x3c1cfe9ef6310a33,
   0x3c1f5e039b6fe9d0,
   0x3c20f3956fd6b034,
   0x3c224e243b174afc,
   0x3c23bfdb9c74207d]

theorem record2684ChunkBits026Length2685 :
    (record2684ChunkBits0262685).length = 32 := by
  decide

theorem record2684ChunkSum0262685 :
    ((record2684ChunkBits0262685).map binary64Value2674).sum =
      (1073017733816757711 : ℚ) / 166153499473114484112975882535043072 := by
  norm_num [record2684ChunkBits0262685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 864 through 895,
decoded and summed as exact rationals. -/
def record2684ChunkBits0272685 : List Nat :=
  [0x3c254a00ab3d7ef9,
   0x3c26edf50b7d9632,
   0x3c28ad3cb09e9066,
   0x3c2a8984934ee531,
   0x3c2c84aa6a646561,
   0x3c2ea783ee962b70,
   0x3c309037d4e0361f,
   0x3c31e8d8b8ac229e,
   0x3c3358d26db8c621,
   0x3c34e13d1dbabdf6,
   0x3c3683406859333d,
   0x3c38401406651b15,
   0x3c3a19046f61a5e7,
   0x3c3c20790124a2df,
   0x3c3e74325c21e7a3,
   0x3c4079b2f4d329c9,
   0x3c41d02224b13fb9,
   0x3c433e8618394c59,
   0x3c44c606795998e1,
   0x3c4667d4f6da73d1,
   0x3c48252f7ece3361,
   0x3c49ff6313ecb5e7,
   0x3c4bf7cf555f53bf,
   0x3c4e0fead1a024ff,
   0x3c5024a41ece2902,
   0x3c5152ce547e3936,
   0x3c529363638db0b1,
   0x3c53e76bb0bcaada,
   0x3c55500d820b6d5d,
   0x3c56ce9276df4ee6,
   0x3c5868e47721a122,
   0x3c5a4186c93daa08]

theorem record2684ChunkBits027Length2685 :
    (record2684ChunkBits0272685).length = 32 := by
  decide

theorem record2684ChunkSum0272685 :
    ((record2684ChunkBits0272685).map binary64Value2674).sum =
      (765690695383420541 : ℚ) / 10384593717069655257060992658440192 := by
  norm_num [record2684ChunkBits0272685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 896 through 927,
decoded and summed as exact rationals. -/
def record2684ChunkBits0282685 : List Nat :=
  [0x3c5c41c0c7553904,
   0x3c5e622307513199,
   0x3c605205cbbaca5a,
   0x3c6184772c71b9c5,
   0x3c62c92aa84f179a,
   0x3c6426bdb0cf87d7,
   0x3c65bb47f00b6dec,
   0x3c676be17e7f42f4,
   0x3c6939d4505fdb65,
   0x3c6b266fea94a548,
   0x3c6d330add5278db,
   0x3c6f6104c7018704,
   0x3c70d8e47af1f06b,
   0x3c721368e05f7dec,
   0x3c7360d65820b6bd,
   0x3c74c1ffc9e63a96,
   0x3c7637c74e41e134,
   0x3c77c321cc62491e,
   0x3c79651b341c2012,
   0x3c7b1edb5e9b56ec,
   0x3c7cf1ab9d724275,
   0x3c7edefcfbfe6b5d,
   0x3c8074379917a432,
   0x3c818a89db19208f,
   0x3c82c99f3bcc3a76,
   0x3c8421e374443440,
   0x3c858e3d2b4eb928,
   0x3c870f74f8e70c48,
   0x3c88a66165db04d8,
   0x3c8a53e87df36283,
   0x3c8c4916a84e2336,
   0x3c8e5fbdfd3bbac4]

theorem record2684ChunkBits028Length2685 :
    (record2684ChunkBits0282685).length = 32 := by
  decide

theorem record2684ChunkSum0282685 :
    ((record2684ChunkBits0282685).map binary64Value2674).sum =
      (920769514301276581 : ℚ) / 1298074214633706907132624082305024 := by
  norm_num [record2684ChunkBits0282685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 928 through 959,
decoded and summed as exact rationals. -/
def record2684ChunkBits0292685 : List Nat :=
  [0x3c904c7742338578,
   0x3c917b0742cf2434,
   0x3c92bc4463962ec9,
   0x3c9410e76098c250,
   0x3c9579adbfd3e389,
   0x3c96f75ba5c9418b,
   0x3c988abe1a8f3aab,
   0x3c9a34adcc8db1e3,
   0x3c9bf6125e107f73,
   0x3c9dcfe64a445345,
   0x3c9fc33b6d04f869,
   0x3ca0e8a01b739e29,
   0x3ca1fda2ca023ffa,
   0x3ca32162c40a48e3,
   0x3ca454b53e9d3b11,
   0x3ca5988b9e381262,
   0x3ca6f0b151853180,
   0x3ca8796c055439a1,
   0x3caa1f6308ce8561,
   0x3cabdc4cc91ce366,
   0x3cadb0fd9649609e,
   0x3caf9e5c63ca642a,
   0x3cb0e850279f8c92,
   0x3cb21816a3bb64f9,
   0x3cb35a9889dbc7c1,
   0x3cb4b0860bef4da1,
   0x3cb61a8ff3b46a96,
   0x3cb79968c280a7f2,
   0x3cb92dc62a2c430f,
   0x3cbad862ea7e72c2,
   0x3cbc9a011ef87c4b,
   0x3cbe736d090c50b0]

theorem record2684ChunkBits029Length2685 :
    (record2684ChunkBits0292685).length = 32 := by
  decide

theorem record2684ChunkSum0292685 :
    ((record2684ChunkBits0292685).map binary64Value2674).sum =
      (239525731135521135 : ℚ) / 40564819207303340847894502572032 := by
  norm_num [record2684ChunkBits0292685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 960 through 991,
decoded and summed as exact rationals. -/
def record2684ChunkBits0302685 : List Nat :=
  [0x3cc032c0314da79c,
   0x3cc138ad331ece9a,
   0x3cc24c74a0dd98bb,
   0x3cc36e17228a7a25,
   0x3cc49e2b67a1fd64,
   0x3cc5dd5aa68f76df,
   0x3cc72c644b14030f,
   0x3cc88c2202bd1df9,
   0x3cc9fd8c20d59e67,
   0x3ccb84a0aa83260a,
   0x3ccd416020dc75b1,
   0x3ccf1d69b1ac583d,
   0x3cd088fdd6cb4e60,
   0x3cd19039fa8a253b,
   0x3cd2b59aa9f11854,
   0x3cd3f77a631e9d28,
   0x3cd54c93b576042c,
   0x3cd6b587b3a6d894,
   0x3cd832f414984d62,
   0x3cd9c5740257ce86,
   0x3cdb6da1423519bb,
   0x3cdd2c15c1e9e5a1,
   0x3cdf016d9681aa08,
   0x3ce07724bd258f2b,
   0x3ce179a8ebb3f6e5,
   0x3ce2889d36310c55,
   0x3ce3a4634bbe550e,
   0x3ce4cd672a03dd0b,
   0x3ce60421f9622fee,
   0x3ce7491d498d4ebd,
   0x3ce89cf6af38dc09,
   0x3cea0063c097f3e0]

theorem record2684ChunkBits030Length2685 :
    (record2684ChunkBits0302685).length = 32 := by
  decide

theorem record2684ChunkSum0302685 :
    ((record2684ChunkBits0302685).map binary64Value2674).sum =
      (216635749943560615 : ℚ) / 5070602400912917605986812821504 := by
  norm_num [record2684ChunkBits0302685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 992 through 1023,
decoded and summed as exact rationals. -/
def record2684ChunkBits0312685 : List Nat :=
  [0x3ceb74366ad62621,
   0x3cecf961964bc09a,
   0x3cee93cd5e1583a0,
   0x3cf0335d1707397c,
   0x3cf12cf04c562ba5,
   0x3cf2323d3cbceb00,
   0x3cf34ee895ba5a19,
   0x3cf48d34c27293f4,
   0x3cf5ddbf1223ca8f,
   0x3cf74107ac563ed3,
   0x3cf8b789ed23c439,
   0x3cfa41bc14aec89b,
   0x3cfbe0105ad216b1,
   0x3cfd92f661994042,
   0x3cff5add11a19267,
   0x3d009c1a76081cda,
   0x3d0195b96f0a250d,
   0x3d029a89d0e41ecd,
   0x3d03aacfdbd4cfe9,
   0x3d04c6d8014f04bd,
   0x3d05eef9873f6e67,
   0x3d072399831b362c,
   0x3d08652e2d43e97f,
   0x3d09b4428ab38331,
   0x3d0b117a67a66335,
   0x3d0c7d969a027fb6,
   0x3d0df9797d9b9fbb,
   0x3d0f88de5965593e,
   0x3d10a7d408f950ea,
   0x3d119a781f986b7a,
   0x3d129bcd686ba390,
   0x3d13c20d6b8501b2]

theorem record2684ChunkBits031Length2685 :
    (record2684ChunkBits0312685).length = 32 := by
  decide

theorem record2684ChunkSum0312685 :
    ((record2684ChunkBits0312685).map binary64Value2674).sum =
      (687530767095725323 : ℚ) / 2535301200456458802993406410752 := by
  norm_num [record2684ChunkBits0312685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1024 through 1055,
decoded and summed as exact rationals. -/
def record2684ChunkBits0322685 : List Nat :=
  [0x3d14f88cce93ff41,
   0x3d163fab4f6c9280,
   0x3d1797bfdfa92fac,
   0x3d19011bcfbeaf5b,
   0x3d1a7c0a9f068e21,
   0x3d1c08d344a6f571,
   0x3d1da7b9d4cc9791,
   0x3d1f59018bbdacd9,
   0x3d208e77a44ae0e5,
   0x3d2179e640b34ee0,
   0x3d226ef55d02918d,
   0x3d236dd3c2e1f78d,
   0x3d2476b88d60124f,
   0x3d2589e5bd7d972d,
   0x3d26a7ab1a1e5e79,
   0x3d27d06959b4f33b,
   0x3d290495914c6e8e,
   0x3d2a44bce1462aef,
   0x3d2b9188543a32b4,
   0x3d2cebc0e1fe7434,
   0x3d2e56bbe5c6bf81,
   0x3d2ff45634da7ef2,
   0x3d30d67ace1457db,
   0x3d31d35ddbce78ae,
   0x3d32e07522329ce8,
   0x3d33fb73ada1b134,
   0x3d352492de8ca57c,
   0x3d365c033b4c7713,
   0x3d37a1efcfd7b714,
   0x3d38f67e1d0c21d5,
   0x3d3a59cf7acffa19,
   0x3d3bcc02cd235bf8]

theorem record2684ChunkBits032Length2685 :
    (record2684ChunkBits0322685).length = 32 := by
  decide

theorem record2684ChunkSum0322685 :
    ((record2684ChunkBits0322685).map binary64Value2674).sum =
      (245908033104716709 : ℚ) / 158456325028528675187087900672 := by
  norm_num [record2684ChunkBits0322685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1056 through 1087,
decoded and summed as exact rationals. -/
def record2684ChunkBits0332685 : List Nat :=
  [0x3d3d4d3693a33fbc,
   0x3d3edd8b5afea5ab,
   0x3d403e934bc83a55,
   0x3d41161af7c8865c,
   0x3d41f5797d0cec25,
   0x3d42dcd3bb310aaf,
   0x3d43cc58fe0dfeba,
   0x3d44c44591434086,
   0x3d45c4e58bceddb8,
   0x3d46ce97cdd43b7a,
   0x3d47e1d127a2052e,
   0x3d48ff1f9d78cb44,
   0x3d4a272e0b4fe63f,
   0x3d4b5cc78087cd9c,
   0x3d4cbdb3043e0f9c,
   0x3d4e505ce1806d5c,
   0x3d500422b6e88955,
   0x3d50eb1ae6b302d3,
   0x3d51dd3964dd4202,
   0x3d52da98710916b3,
   0x3d53e34a595c34f2,
   0x3d54f75ccc2ce036,
   0x3d5616d8de3d7a23,
   0x3d5741c4664bb1aa,
   0x3d5878239dc4109f,
   0x3d59b9fb0c058358,
   0x3d5b0751c17205a0,
   0x3d5c6033e70ef689,
   0x3d5dc4b5a6994b66,
   0x3d5f34f66dabcfbc,
   0x3d6058924663ea14,
   0x3d611cc098561e51]

theorem record2684ChunkBits033Length2685 :
    (record2684ChunkBits0332685).length = 32 := by
  decide

theorem record2684ChunkSum0332685 :
    ((record2684ChunkBits0332685).map binary64Value2674).sum =
      (633608990880272215 : ℚ) / 79228162514264337593543950336 := by
  norm_num [record2684ChunkBits0332685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1088 through 1119,
decoded and summed as exact rationals. -/
def record2684ChunkBits0342685 : List Nat :=
  [0x3d61e73258b0b984,
   0x3d62b821974d476a,
   0x3d638fd8b645a993,
   0x3d646eb4ef880c72,
   0x3d655529106c2eda,
   0x3d6643bfbc80ef37,
   0x3d673cae6f611302,
   0x3d686341d9e8a32d,
   0x3d69b7a6a84f05be,
   0x3d6b1ca6d7bdfc4b,
   0x3d6c926421e3472d,
   0x3d6e18f55131ede8,
   0x3d6fb063e84c3d7a,
   0x3d70ac56396fd6bb,
   0x3d7188e24bf460f1,
   0x3d726dcd9f638422,
   0x3d735b0d818198b1,
   0x3d74509689ce1acf,
   0x3d754e5e4284e419,
   0x3d76545d0e46620b,
   0x3d7762904d2a8dd4,
   0x3d7878fcc325da97,
   0x3d7997b14073f9c9,
   0x3d7abec98b1ee742,
   0x3d7bee7186a53f5f,
   0x3d7d26e894303089,
   0x3d7e688522a6e370,
   0x3d7fb3b86246ae0f,
   0x3d8084890f3b733b,
   0x3d8134a26987d9ad,
   0x3d81ea93f7ba0c49,
   0x3d82a8053e3d8446]

theorem record2684ChunkBits034Length2685 :
    (record2684ChunkBits0342685).length = 32 := by
  decide

theorem record2684ChunkSum0342685 :
    ((record2684ChunkBits0342685).map binary64Value2674).sum =
      (366726582429972037 : ℚ) / 9903520314283042199192993792 := by
  norm_num [record2684ChunkBits0342685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1120 through 1151,
decoded and summed as exact rationals. -/
def record2684ChunkBits0352685 : List Nat :=
  [0x3d839b7c3597c847,
   0x3d84a19b561cc230,
   0x3d85b3bace1fa726,
   0x3d86d1ddddb58aa7,
   0x3d87fbff72196166,
   0x3d89321087f336ac,
   0x3d8a73f85e3e02d5,
   0x3d8bc199a7e52e9b,
   0x3d8d1ad2b71b086a,
   0x3d8e7f7f8b5f9c36,
   0x3d8fef7c2dddf1ad,
   0x3d90b553b0397c36,
   0x3d917872d1873ce7,
   0x3d924112490ad429,
   0x3d930f2f4f72f0e3,
   0x3d93e2cf90c64d7c,
   0x3d94bc03600e0083,
   0x3d959ae81253fd47,
   0x3d967faa7b7503b7,
   0x3d976a8984d86b66,
   0x3d985bd8d359804d,
   0x3d995403ccb4756a,
   0x3d9a538f30737a4e,
   0x3d9b5b1c51afafd9,
   0x3d9c86196d794495,
   0x3d9deae4911b33ed,
   0x3d9f6a2e29fa1f9d,
   0x3da07cf4c7873789,
   0x3da14cfee64bcf13,
   0x3da2252320e5810b,
   0x3da3054845936411,
   0x3da3ed4e5700e697]

theorem record2684ChunkBits035Length2685 :
    (record2684ChunkBits0352685).length = 32 := by
  decide

theorem record2684ChunkSum0352685 :
    ((record2684ChunkBits0352685).map binary64Value2674).sum =
      (390949145355830881 : ℚ) / 2475880078570760549798248448 := by
  norm_num [record2684ChunkBits0352685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1152 through 1183,
decoded and summed as exact rationals. -/
def record2684ChunkBits0362685 : List Nat :=
  [0x3da4dd12b9f120e4,
   0x3da5d4705b1cd486,
   0x3da6d3414b09770d,
   0x3da7d9608f8f3088,
   0x3da8e6ac2d625a1d,
   0x3da9fb076b5c13cf,
   0x3dab165d505cae63,
   0x3dac38a35b62c5fd,
   0x3dad61dc73d39d7a,
   0x3dae921c0de2bd89,
   0x3dafc9897c80716f,
   0x3db08431b39abde2,
   0x3db12781ab667b84,
   0x3db1cef0c86890d5,
   0x3db27acc135a0a4a,
   0x3db32b72fa51a560,
   0x3db3e8c437f918dc,
   0x3db4c2ab4e9846b1,
   0x3db5baf3ebd7b5ab,
   0x3db6c5e35e3a0f00,
   0x3db7db89b31e18ba,
   0x3db8fbc313be8556,
   0x3dba266412478b63,
   0x3dbb5b38677e376b,
   0x3dbc9a02f129ffdf,
   0x3dbde2840c87c597,
   0x3dbf3479cd11f3fb,
   0x3dc047d12d5b383e,
   0x3dc0f9df4abcadd8,
   0x3dc1b04a8055e66e,
   0x3dc26afa7b70f9b3,
   0x3dc329dd133826e9]

theorem record2684ChunkBits036Length2685 :
    (record2684ChunkBits0362685).length = 32 := by
  decide

theorem record2684ChunkSum0362685 :
    ((record2684ChunkBits0362685).map binary64Value2674).sum =
      (386770590107988245 : ℚ) / 618970019642690137449562112 := by
  norm_num [record2684ChunkBits0362685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1184 through 1215,
decoded and summed as exact rationals. -/
def record2684ChunkBits0372685 : List Nat :=
  [0x3dc3ece82a299cc0,
   0x3dc4b41bb082922c,
   0x3dc57f83c3e4f2d0,
   0x3dc64f3ae6b40065,
   0x3dc7236c4788022f,
   0x3dc7fc56131219a0,
   0x3dc8da4c230dba89,
   0x3dc9bdb8df1b78d9,
   0x3dcaa7209998f838,
   0x3dcbba0c387f4340,
   0x3dccdaf52effc7fb,
   0x3dce250b755c79f4,
   0x3dcf884635c7b68d,
   0x3dd07c68e6389229,
   0x3dd13b3453186f2a,
   0x3dd2005e01a4d555,
   0x3dd2cbb945c536ea,
   0x3dd39d1409b647d0,
   0x3dd4743b63a3f70d,
   0x3dd550fbb726017c,
   0x3dd633225ad3f385,
   0x3dd71a7f6854117c,
   0x3dd806e7b7a2c6c9,
   0x3dd8f83705953b9d,
   0x3dd9ee524490b895,
   0x3ddae92a1520e506,
   0x3ddbe8bd6269f76c,
   0x3ddced1c1c702979,
   0x3dddf66a07c7f8af,
   0x3ddf04e197823e4a,
   0x3de00c6b93f48749,
   0x3de0995d6704ebd1]

theorem record2684ChunkBits037Length2685 :
    (record2684ChunkBits0372685).length = 32 := by
  decide

theorem record2684ChunkSum0372685 :
    ((record2684ChunkBits0372685).map binary64Value2674).sum =
      (88057383062028753 : ℚ) / 38685626227668133590597632 := by
  norm_num [record2684ChunkBits0372685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1216 through 1247,
decoded and summed as exact rationals. -/
def record2684ChunkBits0382685 : List Nat :=
  [0x3de1298db1965792,
   0x3de1c9af0e26fc76,
   0x3de27bffe4b548b8,
   0x3de333785c78821c,
   0x3de405a6f4d8fe58,
   0x3de4e819e4493d69,
   0x3de5d27644903e5a,
   0x3de6c48355649fd5,
   0x3de7be032e947573,
   0x3de8beb2014c4d43,
   0x3de9c645c51dd05a,
   0x3dead47485bd9671,
   0x3debe8f4848be6a8,
   0x3ded037e652702ca,
   0x3dee23cf8b43eca2,
   0x3def49aca9f03e1c,
   0x3df03a7241a9158b,
   0x3df0d2a96b4c4bec,
   0x3df16d71bc010982,
   0x3df20acac65c3687,
   0x3df2aabf70ceab90,
   0x3df34d67a88f8cf6,
   0x3df3f2ea290f843f,
   0x3df49b7e388f26a8,
   0x3df5476c86848fe2,
   0x3df5f83538c4f8e8,
   0x3df6ce0aaf42d98a,
   0x3df7a806b47cd885,
   0x3df887d0d9249a95,
   0x3df988dcc5b9e171,
   0x3dfa9e29f210de68,
   0x3dfbbc79fc447180]

theorem record2684ChunkBits038Length2685 :
    (record2684ChunkBits0382685).length = 32 := by
  decide

theorem record2684ChunkSum0382685 :
    ((record2684ChunkBits0382685).map binary64Value2674).sum =
      (298348798382345701 : ℚ) / 38685626227668133590597632 := by
  norm_num [record2684ChunkBits0382685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1248 through 1279,
decoded and summed as exact rationals. -/
def record2684ChunkBits0392685 : List Nat :=
  [0x3dfce379ed5f6671,
   0x3dfe12d16f70565e,
   0x3dff4a22165b1455,
   0x3e0044835b998d8d,
   0x3e00e78dd8e055e9,
   0x3e018dff8403e4ef,
   0x3e0237a98d3ec63a,
   0x3e02e460cd3fc634,
   0x3e0393ff5926124b,
   0x3e04466630260870,
   0x3e04fb7f00dc309c,
   0x3e05b33e03307ff3,
   0x3e066da3e250baeb,
   0x3e072abfb0ae1f26,
   0x3e07eab0de142420,
   0x3e08ada983f23d4c,
   0x3e0973ef45cf1c23,
   0x3e0a3dddc2ea5bdd,
   0x3e0b244f15c70bde,
   0x3e0c2086084af478,
   0x3e0d21094dba8441,
   0x3e0e27cdd49cecd7,
   0x3e0f56667dbcd682,
   0x3e104ea8f655293f,
   0x3e10f70c6a776e3f,
   0x3e11a425ac6103ff,
   0x3e1255ba3b87f770,
   0x3e130b8cb78b88d6,
   0x3e13c55c4e8b2fbd,
   0x3e1482e9f698a757,
   0x3e1543f86daf9d1a,
   0x3e16084ddee5a0ca]

theorem record2684ChunkBits039Length2685 :
    (record2684ChunkBits0392685).length = 32 := by
  decide

theorem record2684ChunkSum0392685 :
    ((record2684ChunkBits0392685).map binary64Value2674).sum =
      (119770590224708297 : ℚ) / 4835703278458516698824704 := by
  norm_num [record2684ChunkBits0392685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1280 through 1311,
decoded and summed as exact rationals. -/
def record2684ChunkBits0402685 : List Nat :=
  [0x3e16cfb5a3fb9478,
   0x3e179a022257ac9f,
   0x3e18670ec18f8f45,
   0x3e1936c1f88d3123,
   0x3e1a090f6cfe4352,
   0x3e1addfa1f1af218,
   0x3e1bb59699f5d2dc,
   0x3e1c900d48c7d043,
   0x3e1d6d9c79d6d8bb,
   0x3e1e4e999e841820,
   0x3e1f3927f0e584e3,
   0x3e2029d2e1918077,
   0x3e20b94d1dadcaca,
   0x3e214ae5d4f35912,
   0x3e21dfb8be7b5172,
   0x3e228b893b63211e,
   0x3e234576f27c4978,
   0x3e240494c71257b2,
   0x3e24c89c0a790902,
   0x3e259143d872be5d,
   0x3e265e40e0794380,
   0x3e272f4483cb7da3,
   0x3e2804032b348983,
   0x3e28dc343355cf15,
   0x3e29b793d2b24d32,
   0x3e2a95e51be59d94,
   0x3e2b76f41a636fe6,
   0x3e2c5a980709b3c9,
   0x3e2d40b5908811b7,
   0x3e2e29413208261d,
   0x3e2f144190ab05f9,
   0x3e3000e8eb29e879]

theorem record2684ChunkBits040Length2685 :
    (record2684ChunkBits0402685).length = 32 := by
  decide

theorem record2684ChunkSum0402685 :
    ((record2684ChunkBits0402685).map binary64Value2674).sum =
      (90264839558606623 : ℚ) / 1208925819614629174706176 := by
  norm_num [record2684ChunkBits0402685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1312 through 1343,
decoded and summed as exact rationals. -/
def record2684ChunkBits0412685 : List Nat :=
  [0x3e30791241bdaa79,
   0x3e30f2c2189f6d28,
   0x3e316e2b5d2977ce,
   0x3e31fd2bfe2bd2bb,
   0x3e3298d63c050a13,
   0x3e33369dae051311,
   0x3e33d66179f509ac,
   0x3e34795641afd3e4,
   0x3e3535ee47d8ae92,
   0x3e36026296e06386,
   0x3e36d41a5c1be53f,
   0x3e37aac106b7df98,
   0x3e38860066fd3c38,
   0x3e396580986a01bc,
   0x3e3a48e6be91bda5,
   0x3e3b2fdc6d2bcb3e,
   0x3e3c1a0f78be9ea3,
   0x3e3d0734121ea445,
   0x3e3df706fc6c4e29,
   0x3e3ee94fdb31c854,
   0x3e3fdde3950f44c4,
   0x3e406a5362f64467,
   0x3e40e6c81cf4f93c,
   0x3e416455b4206f7e,
   0x3e41e30d8cd80f4f,
   0x3e42630dce5d7266,
   0x3e42e4820bf7fb74,
   0x3e436b5f7b22424e,
   0x3e440f6a927b1db4,
   0x3e44b5878f433e91,
   0x3e455d8b1a23e3d5,
   0x3e46075188315bbe]

theorem record2684ChunkBits041Length2685 :
    (record2684ChunkBits0412685).length = 32 := by
  decide

theorem record2684ChunkSum0412685 :
    ((record2684ChunkBits0412685).map binary64Value2674).sum =
      (255820894192773549 : ℚ) / 1208925819614629174706176 := by
  norm_num [record2684ChunkBits0412685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1344 through 1375,
decoded and summed as exact rationals. -/
def record2684ChunkBits0422685 : List Nat :=
  [0x3e46b41e08cfa9cd,
   0x3e477c9564d30650,
   0x3e48565678e7f9df,
   0x3e49353f25606791,
   0x3e4a18eef248cd76,
   0x3e4b01048e653d34,
   0x3e4bed1de19a47cf,
   0x3e4cdcd65c51c622,
   0x3e4dcfcf559c79c6,
   0x3e4ec5afb9626367,
   0x3e4fbe2649d14332,
   0x3e505c75fc232e48,
   0x3e50dae329523b79,
   0x3e515a45005772cc,
   0x3e51da8ea5ba14fd,
   0x3e525bbd53788c60,
   0x3e52ddd999fbe776,
   0x3e5360f8e282e560,
   0x3e53e53dc9ba500d,
   0x3e546ad9c7f7db06,
   0x3e5505b866cd1e33,
   0x3e55afdd7c812ad6,
   0x3e565bcd118c0593,
   0x3e570959524496a9,
   0x3e57b85d2ef85881,
   0x3e586a1f1df0df43,
   0x3e5938d3037dd691,
   0x3e5a19d5d3cfdf4f,
   0x3e5affb995d9d9a4,
   0x3e5bea14cf139cbf,
   0x3e5cd87e0e8409e3,
   0x3e5dca8c2c37d987]

theorem record2684ChunkBits042Length2685 :
    (record2684ChunkBits0422685).length = 32 := by
  decide

theorem record2684ChunkSum0422685 :
    ((record2684ChunkBits0422685).map binary64Value2674).sum =
      (346454956749131673 : ℚ) / 604462909807314587353088 := by
  norm_num [record2684ChunkBits0422685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1376 through 1407,
decoded and summed as exact rationals. -/
def record2684ChunkBits0432685 : List Nat :=
  [0x3e5ebfd42599d32a,
   0x3e5fb7f244fbb6b5,
   0x3e605944d44e6195,
   0x3e60d7a34bf88f40,
   0x3e6156f0762e9d7e,
   0x3e61d70f44d8d79a,
   0x3e6257eaf0a903a2,
   0x3e62d9783ca4b395,
   0x3e635bb6b754538e,
   0x3e63deb20bf2fcf0,
   0x3e6462833396437c,
   0x3e64e750eb7736d7,
   0x3e656f1c8f0e87f3,
   0x3e6618e0273f88ed,
   0x3e66c44f735f76a5,
   0x3e677133d6c2f6b8,
   0x3e681f5eb48096b8,
   0x3e68ceab143b9ef2,
   0x3e698057ae6f292c,
   0x3e6a4f6bb3fca83e,
   0x3e6b315d78b9309d,
   0x3e6c17c6cb56cc6e,
   0x3e6d0238ac997130,
   0x3e6df045121eaf70,
   0x3e6ee17f545d3c03,
   0x3e6fd5799a6208cb,
   0x3e7065e7489d0325,
   0x3e70e21065078525,
   0x3e715f0e88391d91,
   0x3e71dcbe67b5fa70,
   0x3e725b0440904834,
   0x3e72d9cd11b7439a]

theorem record2684ChunkBits043Length2685 :
    (record2684ChunkBits0432685).length = 32 := by
  decide

theorem record2684ChunkSum0432685 :
    ((record2684ChunkBits0432685).map binary64Value2674).sum =
      (448212608913496513 : ℚ) / 302231454903657293676544 := by
  norm_num [record2684ChunkBits0432685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1408 through 1439,
decoded and summed as exact rationals. -/
def record2684ChunkBits0442685 : List Nat :=
  [0x3e73590fd51f17e9,
   0x3e73d8ceb32d3375,
   0x3e7459186f4e6cf5,
   0x3e74da08d2b3a347,
   0x3e755bca0fe3fa9f,
   0x3e75ef94daebdc8c,
   0x3e76965326e41787,
   0x3e773e61062cf318,
   0x3e77e7881b134ae2,
   0x3e78919aa99c08cf,
   0x3e793c753467493d,
   0x3e79e944faa4e9df,
   0x3e7ab32105b1d965,
   0x3e7b8feea780fc7e,
   0x3e7c70b1f97aab78,
   0x3e7d54fa31686f2a,
   0x3e7e3c58590c8d9f,
   0x3e7f265fe8bd96e7,
   0x3e800951e6a0695d,
   0x3e80806036cb1b70,
   0x3e80f82d70dc1cdf,
   0x3e8170919c05a9d6,
   0x3e81e96b6257e56f,
   0x3e8262a13b16b99b,
   0x3e82dc2294c67360,
   0x3e8355e8fb296dbd,
   0x3e83cff93ef3af59,
   0x3e844a64be3bd87e,
   0x3e84c54975060fba,
   0x3e8540d3d3e8361c,
   0x3e85dc5836ebc698,
   0x3e867be5ce16dc0e]

theorem record2684ChunkBits044Length2685 :
    (record2684ChunkBits0442685).length = 32 := by
  decide

theorem record2684ChunkSum0442685 :
    ((record2684ChunkBits0442685).map binary64Value2674).sum =
      (68847545368499277 : ℚ) / 18889465931478580854784 := by
  norm_num [record2684ChunkBits0442685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1440 through 1471,
decoded and summed as exact rationals. -/
def record2684ChunkBits0452685 : List Nat :=
  [0x3e871c65e1a9c36b,
   0x3e87bda4104297c5,
   0x3e885f74f8410418,
   0x3e8901b7c17cca35,
   0x3e89a5807f8a2cfb,
   0x3e8a653b55e6329d,
   0x3e8b37854872e99a,
   0x3e8c0d358dc3896e,
   0x3e8ce5dd2adf499e,
   0x3e8dc10fba147672,
   0x3e8e9e642d2e1bfe,
   0x3e8f7d717f8f8419,
   0x3e902eec6333c03c,
   0x3e909fa222648e15,
   0x3e9110b4c8686777,
   0x3e918205defa0c76,
   0x3e91f37ec3e622a4,
   0x3e926511bbaba654,
   0x3e92d6bafd9015df,
   0x3e934881e5114160,
   0x3e93ba7980308c0a,
   0x3e942cc16cb3a55c,
   0x3e94aa000b0e3a71,
   0x3e953e1aa733a897,
   0x3e95d308bbc7dbfe,
   0x3e966891ae699676,
   0x3e96fe848d38f0a4,
   0x3e9794b97cd376f1,
   0x3e982b1325b7df1b,
   0x3e98c2872e4e4694,
   0x3e997432a687e8b4,
   0x3e9a37a1147f181a]

theorem record2684ChunkBits045Length2685 :
    (record2684ChunkBits0452685).length = 32 := by
  decide

theorem record2684ChunkSum0452685 :
    ((record2684ChunkBits0452685).map binary64Value2674).sum =
      (162471992755234187 : ℚ) / 18889465931478580854784 := by
  norm_num [record2684ChunkBits0452685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1472 through 1503,
decoded and summed as exact rationals. -/
def record2684ChunkBits0462685 : List Nat :=
  [0x3e9afde352526281,
   0x3e9bc68f626fb6b8,
   0x3e9c913e735dae50,
   0x3e9d5d8dc20f7a1f,
   0x3e9e2b1b10129dec,
   0x3e9ef98e7d04eb88,
   0x3e9fc8997f567f77,
   0x3ea04bfc6e8e10e8,
   0x3ea0b3bb52eb0c16,
   0x3ea11b76143f36c6,
   0x3ea18321effb1aac,
   0x3ea1eabda7412bb2,
   0x3ea25252b03487e3,
   0x3ea2b9f51d971f09,
   0x3ea321c528f3542c,
   0x3ea39facadae052a,
   0x3ea426f07b786d1e,
   0x3ea4aeb5edc310ef,
   0x3ea536c8fa16471c,
   0x3ea5befd3155ec37,
   0x3ea6472f0d4bbe72,
   0x3ea6cf453b2564b2,
   0x3ea758143381b41b,
   0x3ea7f8e6437bd959,
   0x3ea8aa580b1ff4fc,
   0x3ea95e10b559f473,
   0x3eaa13adce6f278a,
   0x3eaacad07441afdf,
   0x3eab831e4fa826a1,
   0x3eac3c3de9d92c8a,
   0x3eacf5e01552b152,
   0x3eadafbed45a32a4]

theorem record2684ChunkBits046Length2685 :
    (record2684ChunkBits0462685).length = 32 := by
  decide

theorem record2684ChunkSum0462685 :
    ((record2684ChunkBits0462685).map binary64Value2674).sum =
      (370222654986072893 : ℚ) / 18889465931478580854784 := by
  norm_num [record2684ChunkBits0462685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1504 through 1535,
decoded and summed as exact rationals. -/
def record2684ChunkBits0472685 : List Nat :=
  [0x3eae699f1d57865c,
   0x3eaf23529ca459c0,
   0x3eafdcb96f50db74,
   0x3eb04ae1e8a00781,
   0x3eb0a739f2f1b0a3,
   0x3eb1036f90db1b9b,
   0x3eb15f97693ba38f,
   0x3eb1be59c45f49bc,
   0x3eb236b2c16106af,
   0x3eb2af7cdc4b6df1,
   0x3eb3288351ce103e,
   0x3eb3a1978a971219,
   0x3eb41a9245ee4d5c,
   0x3eb49354c25b75a4,
   0x3eb50bc9e159d608,
   0x3eb584a475ce7d1d,
   0x3eb612fe3b6ae13e,
   0x3eb6b0937b65eaeb,
   0x3eb74feecf0b02e0,
   0x3eb7f0b71b54fc64,
   0x3eb892970a05172e,
   0x3eb9353e102bba0e,
   0x3eb9d85cbed15374,
   0x3eba7bad8c1e02f7,
   0x3ebb1ef3b173998e,
   0x3ebbc1fcb70b88bd,
   0x3ebc64a1fa61304b,
   0x3ebd06ca2b33bac7,
   0x3ebda86ab9f0cfdb,
   0x3ebe49898f3f0e23,
   0x3ebeea3d64c5cc6c,
   0x3ebf8aaf598f18c5]

theorem record2684ChunkBits047Length2685 :
    (record2684ChunkBits0472685).length = 32 := by
  decide

theorem record2684ChunkSum0472685 :
    ((record2684ChunkBits0472685).map binary64Value2674).sum =
      (101266272130287559 : ℚ) / 2361183241434822606848 := by
  norm_num [record2684ChunkBits0472685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1536 through 1567,
decoded and summed as exact rationals. -/
def record2684ChunkBits0482685 : List Nat :=
  [0x3ec020d9bb225fc3,
   0x3ec08a391f7de6c8,
   0x3ec0f3cc640b6b8e,
   0x3ec15d64fceb6d7f,
   0x3ec1c6da3cabc8b5,
   0x3ec2300a598ecb58,
   0x3ec298db6f54b139,
   0x3ec3013c7ac523e7,
   0x3ec369c00feef56a,
   0x3ec3e51865bc697a,
   0x3ec46e1e2f02253d,
   0x3ec4f879865ea1c9,
   0x3ec583dbb7365291,
   0x3ec60ff9d64c6743,
   0x3ec69c8dcbd4f85f,
   0x3ec72952b9d2be69,
   0x3ec7b60d02c90861,
   0x3ec84289291efa8b,
   0x3ec8ce9d213bb46d,
   0x3ec95a299c9e172d,
   0x3ec9e51b4a203408,
   0x3eca6f6c073d32ac,
   0x3ecaf92478a857ba,
   0x3ecb825b94349f81,
   0x3ecc0b38efcca7ae,
   0x3eccb7112ac4169a,
   0x3ecd6bd98e234834,
   0x3ece20aba0cadb28,
   0x3eced5372964c956,
   0x3ecf8936cc0f7a59,
   0x3ed01e38e4d0f3ee,
   0x3ed0775edaf6714e]

theorem record2684ChunkBits048Length2685 :
    (record2684ChunkBits0482685).length = 32 := by
  decide

theorem record2684ChunkSum0482685 :
    ((record2684ChunkBits0482685).map binary64Value2674).sum =
      (213751898038090635 : ℚ) / 2361183241434822606848 := by
  norm_num [record2684ChunkBits0482685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1568 through 1599,
decoded and summed as exact rationals. -/
def record2684ChunkBits0492685 : List Nat :=
  [0x3ed0d0000fffca87,
   0x3ed128919c42f91c,
   0x3ed1914b635463e9,
   0x3ed2061107f714b7,
   0x3ed27bcdf461e60c,
   0x3ed2f23e36d92746,
   0x3ed36921844b4bba,
   0x3ed3e03c3d26b117,
   0x3ed457540071972e,
   0x3ed4ce36da4c8ee8,
   0x3ed544ba2d51a256,
   0x3ed5babbcd44a9e9,
   0x3ed6302311b9603e,
   0x3ed6a4e1dd4f95ab,
   0x3ed718f5ba3e346f,
   0x3ed78c6898c55bdc,
   0x3ed7ff512d2d3530,
   0x3ed8770676ab2cfc,
   0x3ed90f087341f8bc,
   0x3ed9a71d02444a6c,
   0x3eda3ef833d7387e,
   0x3edad65669ab47e8,
   0x3edb6cfdd475295f,
   0x3edc02bfeacefd70,
   0x3edc977ad5fd502a,
   0x3edd2b1ad03a184e,
   0x3eddbe5646da9b2a,
   0x3ede6cc051cd5518,
   0x3edf2fff1b7ef0d9,
   0x3edff494a9603479,
   0x3ee05d07173774b2,
   0x3ee0bfffd4b24cec]

theorem record2684ChunkBits049Length2685 :
    (record2684ChunkBits0492685).length = 32 := by
  decide

theorem record2684ChunkSum0492685 :
    ((record2684ChunkBits0492685).map binary64Value2674).sum =
      (3416810996452915 : ℚ) / 18446744073709551616 := by
  norm_num [record2684ChunkBits0492685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1600 through 1631,
decoded and summed as exact rationals. -/
def record2684ChunkBits0502685 : List Nat :=
  [0x3ee12302ea9aca7e,
   0x3ee185dfe6a105f8,
   0x3ee1e86dd38c37cc,
   0x3ee24a8a33ba65ec,
   0x3ee2ac19e896bcbf,
   0x3ee30d0a11ab07bb,
   0x3ee36d50e06296b7,
   0x3ee3ccee9a00b801,
   0x3ee42bedb393c029,
   0x3ee48a63c28023a0,
   0x3ee4f7158e03f41f,
   0x3ee574ccfc57a424,
   0x3ee5f25f137fc778,
   0x3ee66f8c99c03496,
   0x3ee6ec1dc0765643,
   0x3ee767e35f788bcb,
   0x3ee7e2b829139d25,
   0x3ee85c81d39d292b,
   0x3ee8d53234d8dfdf,
   0x3ee94d53e9a08b95,
   0x3ee9dbe534b801ad,
   0x3eea7c288c8bcb2e,
   0x3eeb1d4d2eef5bfe,
   0x3eebbef415833a6d,
   0x3eec60c45b601a9b,
   0x3eed026d09228e4c,
   0x3eeda39f50e665f2,
   0x3eee44196755cfba,
   0x3eeee3a4a571334c,
   0x3eef8216fc1d07ef,
   0x3ef00faa2b9e7f3f,
   0x3ef05da7f5ba18ec]

theorem record2684ChunkBits050Length2685 :
    (record2684ChunkBits0502685).length = 32 := by
  decide

theorem record2684ChunkSum0502685 :
    ((record2684ChunkBits0502685).map binary64Value2674).sum =
      (108618950330441051 : ℚ) / 295147905179352825856 := by
  norm_num [record2684ChunkBits0502685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1632 through 1663,
decoded and summed as exact rationals. -/
def record2684ChunkBits0512685 : List Nat :=
  [0x3ef0ab06ff03db18,
   0x3ef0f7d19e71b70a,
   0x3ef1441ba8ab06d8,
   0x3ef1a45dbc647914,
   0x3ef20a7fda45f414,
   0x3ef270598026f0ee,
   0x3ef2d5b711a51de2,
   0x3ef33a6b6923b4d8,
   0x3ef39e50d79b3ef0,
   0x3ef4014a1cdb8230,
   0x3ef4634355ae4eb4,
   0x3ef4c432dcb1aced,
   0x3ef5247f6fecc5c0,
   0x3ef596fba62576d6,
   0x3ef6183f7e6310cd,
   0x3ef69a0d545c341f,
   0x3ef71c1801d96c5b,
   0x3ef79e17c1896557,
   0x3ef81fcbcef1599e,
   0x3ef8a0f549274a78,
   0x3ef921605efa9720,
   0x3ef9a0e2a42712e1,
   0x3efa1f5c35ebfed7,
   0x3efa9cb8d0485ca1,
   0x3efb18f0f24a4325,
   0x3efb940abb7583fc,
   0x3efc0e1a107aae2a,
   0x3efc8a58c0363c79,
   0x3efd2dd678465237,
   0x3efdd0fa2d864ffc,
   0x3efe7367cbe4b4e6,
   0x3eff14cca29f8ef1]

theorem record2684ChunkBits051Length2685 :
    (record2684ChunkBits0512685).length = 32 := by
  decide

theorem record2684ChunkSum0512685 :
    ((record2684ChunkBits0512685).map binary64Value2674).sum =
      (52218250364028615 : ℚ) / 73786976294838206464 := by
  norm_num [record2684ChunkBits0512685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1664 through 1695,
decoded and summed as exact rationals. -/
def record2684ChunkBits0522685 : List Nat :=
  [0x3effb4e106e3d12e,
   0x3f0029b4f5aaf8b2,
   0x3f00781d34886e2b,
   0x3f00c59a9aecf660,
   0x3f0112270129661f,
   0x3f015e0cada8fee9,
   0x3f01b86f3a6a7455,
   0x3f021ef72c9b7543,
   0x3f0285cb01c234da,
   0x3f02ecad3a598c3f,
   0x3f035364f0975226,
   0x3f03b9bf480ce66f,
   0x3f041f8afc2b4bc0,
   0x3f04849fffef0618,
   0x3f04e8de097cc5d8,
   0x3f054c2d74606914,
   0x3f05ae8016031ca2,
   0x3f060fd23967de3b,
   0x3f06702ad209ae37,
   0x3f06cf9c33f66c74,
   0x3f073aa97cad6eaf,
   0x3f07bb519278c177,
   0x3f083b802035f179,
   0x3f08baec285ece59,
   0x3f0939549995105f,
   0x3f09b681983753a0,
   0x3f0a3245bd6bc7f2,
   0x3f0aac7f48d02c39,
   0x3f0b25194159b110,
   0x3f0b9c0c812c6360,
   0x3f0c11c1b6c50bc4,
   0x3f0c9e2acce99bb9]

theorem record2684ChunkBits052Length2685 :
    (record2684ChunkBits0522685).length = 32 := by
  decide

theorem record2684ChunkSum0522685 :
    ((record2684ChunkBits0522685).map binary64Value2674).sum =
      (195638820371507325 : ℚ) / 147573952589676412928 := by
  norm_num [record2684ChunkBits0522685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1696 through 1727,
decoded and summed as exact rationals. -/
def record2684ChunkBits0532685 : List Nat :=
  [0x3f0d3e3baf7f98a4,
   0x3f0dde9047a221ba,
   0x3f0e7ec83b6a5c24,
   0x3f0f1e8ae163af81,
   0x3f0fbd89bcd0a889,
   0x3f102dbc75d8d06b,
   0x3f107c0dcf12ddde,
   0x3f10c9a0cd1d2b93,
   0x3f11166449e0825c,
   0x3f11624eb618fc24,
   0x3f11ad5eeddfe99d,
   0x3f11f79bfc97988a,
   0x3f124116297ed19a,
   0x3f129b442fd29546,
   0x3f12feefeb7e362b,
   0x3f136216b94b1332,
   0x3f13c47fb62bc034,
   0x3f1425f88c68f98b,
   0x3f14865672daf041,
   0x3f14e57722925828,
   0x3f154341c0b0461a,
   0x3f159fa7b9aa422d,
   0x3f15faa58a9fce9c,
   0x3f1654830839b7e8,
   0x3f16bfe224ec67aa,
   0x3f173aec588ba643,
   0x3f17b604c236721b,
   0x3f1830e124fc4304,
   0x3f18ab3d8dfb2661,
   0x3f1924de7032ac5e,
   0x3f199d8a50219999,
   0x3f1a1513cc523a05]

theorem record2684ChunkBits053Length2685 :
    (record2684ChunkBits0532685).length = 32 := by
  decide

theorem record2684ChunkSum0532685 :
    ((record2684ChunkBits0532685).map binary64Value2674).sum =
      (89363401926221361 : ℚ) / 36893488147419103232 := by
  norm_num [record2684ChunkBits0532685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1728 through 1759,
decoded and summed as exact rationals. -/
def record2684ChunkBits0542685 : List Nat :=
  [0x3f1a8b5788a5ee6f,
   0x3f1b003d2f43eb4d,
   0x3f1b73b86a3fd55c,
   0x3f1be5ca00182b28,
   0x3f1c567f68634876,
   0x3f1cc5f49977b7ac,
   0x3f1d5abe1f037a87,
   0x3f1df2df7a942bd0,
   0x3f1e89fb6d1748ea,
   0x3f1f1fbab656f40f,
   0x3f1fb3d0b86cd14f,
   0x3f2022fe7e6b30d2,
   0x3f206b0654686581,
   0x3f20b1edeeb80c77,
   0x3f20f7ab7f8eb740,
   0x3f213c3def9efd94,
   0x3f217fd527e609b4,
   0x3f21d0b7b6bf52fd,
   0x3f222dea3ac5b5e5,
   0x3f228b0bb249632b,
   0x3f22e7e3cf48045f,
   0x3f23443f4e95c764,
   0x3f239ff1b96a1b52,
   0x3f23fad03255ff5f,
   0x3f2454b9699bf192,
   0x3f24ad93e7719357,
   0x3f25054ec8edf9a8,
   0x3f255be290f08dd0,
   0x3f25b1518db4d611,
   0x3f2605a81911d449,
   0x3f265e44213e6041,
   0x3f26d15c2a3a58db]

theorem record2684ChunkBits054Length2685 :
    (record2684ChunkBits0542685).length = 32 := by
  decide

theorem record2684ChunkSum0542685 :
    ((record2684ChunkBits0542685).map binary64Value2674).sum =
      (318006700978067029 : ℚ) / 73786976294838206464 := by
  norm_num [record2684ChunkBits0542685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1760 through 1791,
decoded and summed as exact rationals. -/
def record2684ChunkBits0552685 : List Nat :=
  [0x3f2743cd23ce17bf,
   0x3f27b54de0c4e2aa,
   0x3f28259c7def0da9,
   0x3f28947f923341f7,
   0x3f2901c752acb936,
   0x3f296d4ea89e04cf,
   0x3f29d6fc3679c273,
   0x3f2a3ec348a9dc1f,
   0x3f2aa4a4ae0d36ce,
   0x3f2b08de5926d558,
   0x3f2b80fd7dbb6065,
   0x3f2c0c3293eb40fc,
   0x3f2c9725d4556f75,
   0x3f2d21831d69da70,
   0x3f2daafe3d206693,
   0x3f2e3355d0ab1c94,
   0x3f2eba4ade502b09,
   0x3f2f3fad43e7f53c,
   0x3f2fc358f41f167a,
   0x3f30229b84061620,
   0x3f30629f85f699f9,
   0x3f30a1bb88d7f441,
   0x3f30dffa5854fb4b,
   0x3f31278873da8251,
   0x3f317d0c89b5dff9,
   0x3f31d1f51cc64700,
   0x3f32260b638cae88,
   0x3f32791e57587a00,
   0x3f32cb03966fc436,
   0x3f331b983c37c5b1,
   0x3f336ac1adacf412,
   0x3f33b86e58133efd]

theorem record2684ChunkBits055Length2685 :
    (record2684ChunkBits0552685).length = 32 := by
  decide

theorem record2684ChunkSum0552685 :
    ((record2684ChunkBits0552685).map binary64Value2674).sum =
      (69177954761878835 : ℚ) / 9223372036854775808 := by
  norm_num [record2684ChunkBits0552685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1792 through 1823,
decoded and summed as exact rationals. -/
def record2684ChunkBits0562685 : List Nat :=
  [0x3f3404965f54174a,
   0x3f344f3c38fe0d18,
   0x3f34988689a98626,
   0x3f34f07ec66e4b9b,
   0x3f35571021e2c309,
   0x3f35bd541073247f,
   0x3f36230c9c6e7b77,
   0x3f368801f2e1d5a8,
   0x3f36ec04b3a394df,
   0x3f374ee74457374e,
   0x3f37b087650d29d8,
   0x3f3810cbff44655a,
   0x3f386fa5e913810f,
   0x3f38cd10f503bbdf,
   0x3f3929136d466d5a,
   0x3f3983bf91c4042e,
   0x3f39f51d2defa5de,
   0x3f3a72845d0bfa1a,
   0x3f3aeed9ded7cd09,
   0x3f3b69cccdfcfdf6,
   0x3f3be31539b72e9c,
   0x3f3c5a75719fe15f,
   0x3f3ccfbb412e9ab4,
   0x3f3d42c118634e42,
   0x3f3db36f1e77565c,
   0x3f3e21bc2ac7652e,
   0x3f3e8dae9f69f551,
   0x3f3ef774a89525d9,
   0x3f3f7698bbc792c5,
   0x3f4005e49dad33bc,
   0x3f4050301156d6b5,
   0x3f409a01b6deeadd]

theorem record2684ChunkBits056Length2685 :
    (record2684ChunkBits0562685).length = 32 := by
  decide

theorem record2684ChunkSum0562685 :
    ((record2684ChunkBits0562685).map binary64Value2674).sum =
      (58776446222515239 : ℚ) / 4611686018427387904 := by
  norm_num [record2684ChunkBits0562685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1824 through 1855,
decoded and summed as exact rationals. -/
def record2684ChunkBits0572685 : List Nat :=
  [0x3f40e33136e46ecf,
   0x3f412b9cb99d7e4e,
   0x3f417323ad29d065,
   0x3f41b9ae0eb48b5a,
   0x3f41ff2ab4359337,
   0x3f42438fd5aabd84,
   0x3f4286dbd75c92b0,
   0x3f42c914be1c3b7e,
   0x3f430a496da18f6b,
   0x3f43627f579c0b55,
   0x3f43bd4781b3462f,
   0x3f441728cc3de101,
   0x3f446fe84aebe4f5,
   0x3f44c751eb4c8827,
   0x3f451d3964f75929,
   0x3f45717b1cbb19f6,
   0x3f45c3fcf8f1388e,
   0x3f4614af24a37659,
   0x3f46638cbeb55304,
   0x3f46b09c71b85fc9,
   0x3f46fbf850296a7a,
   0x3f4756b38b980990,
   0x3f47c1d5103f8fba,
   0x3f482c71c5ee4548,
   0x3f489642f80c982c,
   0x3f48ff0f1918a4bf,
   0x3f4966a674296fac,
   0x3f49ccdb1d4a4843,
   0x3f4a318be224b1b3,
   0x3f4a94a1a7a356b5,
   0x3f4af6105d79dcec,
   0x3f4b55d74269766b]

theorem record2684ChunkBits057Length2685 :
    (record2684ChunkBits0572685).length = 32 := by
  decide

theorem record2684ChunkSum0572685 :
    ((record2684ChunkBits0572685).map binary64Value2674).sum =
      (195869352380663113 : ℚ) / 9223372036854775808 := by
  norm_num [record2684ChunkBits0572685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1856 through 1887,
decoded and summed as exact rationals. -/
def record2684ChunkBits0582685 : List Nat :=
  [0x3f4bb401538b2c23,
   0x3f4c14b43a1c03f0,
   0x3f4c97a58f58268e,
   0x3f4d197bbe599e3d,
   0x3f4d99d91d9909f9,
   0x3f4e1868ee1d2316,
   0x3f4e94e0c4c86409,
   0x3f4f0f01e1a59bf6,
   0x3f4f869a72f617d6,
   0x3f4ffb86c142b5e8,
   0x3f5036d920863ac8,
   0x3f506e8c430323f3,
   0x3f50a4e3097dcdb2,
   0x3f50d9ec805d48e1,
   0x3f5119e10cc1eea0,
   0x3f5165e0ad720092,
   0x3f51b1750cd025d1,
   0x3f51fc653c7d8c9a,
   0x3f524688b3781dae,
   0x3f528fbe43594b16,
   0x3f52d7e5f6a76e2e,
   0x3f531ee92dd0b538,
   0x3f5364b89fc084a9,
   0x3f53a94cfa09fd67,
   0x3f53eca7353e6197,
   0x3f542ed08f96b3f6,
   0x3f5478e193a4cc10,
   0x3f54d58b979178bc,
   0x3f55314d7e381466,
   0x3f558be46b32ebaa,
   0x3f55e5142e394f64,
   0x3f563ca84356cd12]

theorem record2684ChunkBits058Length2685 :
    (record2684ChunkBits0582685).length = 32 := by
  decide

theorem record2684ChunkSum0582685 :
    ((record2684ChunkBits0582685).map binary64Value2674).sum =
      (159770920768738265 : ℚ) / 4611686018427387904 := by
  norm_num [record2684ChunkBits0582685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1888 through 1919,
decoded and summed as exact rationals. -/
def record2684ChunkBits0592685 : List Nat :=
  [0x3f569274c54068a9,
   0x3f56e657502afdc1,
   0x3f573837d3287cda,
   0x3f5788094d9b84a3,
   0x3f57d5ca75d189a3,
   0x3f582186454784db,
   0x3f586b54668dbe2a,
   0x3f58c4662951ee81,
   0x3f592efd8e7216f2,
   0x3f5998ecda7c2291,
   0x3f5a01dacb290a78,
   0x3f5a698ef0e1e728,
   0x3f5acfdbb1cd7c5b,
   0x3f5b349515b8a02b,
   0x3f5b979caa72165f,
   0x3f5bf8de949eabf4,
   0x3f5c58527b11afd3,
   0x3f5cb5fb183dddac,
   0x3f5d11e7cb2c3ae9,
   0x3f5d817a43b7e1f5,
   0x3f5e0326099b2e1c,
   0x3f5e8360a38d7421,
   0x3f5f01cbb76eb727,
   0x3f5f7e12c45dadf7,
   0x3f5ff7ec89f5190a,
   0x3f60378e2d41f579,
   0x3f6071b9aafa854b,
   0x3f60aa68c54b0132,
   0x3f60e1937c221ec9,
   0x3f61173a38ea9ac5,
   0x3f614b662be4e604,
   0x3f617e29934b1d06]

theorem record2684ChunkBits059Length2685 :
    (record2684ChunkBits0592685).length = 32 := by
  decide

theorem record2684ChunkSum0592685 :
    ((record2684ChunkBits0592685).map binary64Value2674).sum =
      (127924033561769077 : ℚ) / 2305843009213693952 := by
  norm_num [record2684ChunkBits0592685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1920 through 1951,
decoded and summed as exact rationals. -/
def record2684ChunkBits0602685 : List Nat :=
  [0x3f61bb7847ccf597,
   0x3f620562e74e82f8,
   0x3f624eccfbf53bf0,
   0x3f6297722ff4f3e4,
   0x3f62df2bb2a1a8f0,
   0x3f6325da94ef7736,
   0x3f636b60f7b51cf2,
   0x3f63afaaa9743242,
   0x3f63f2aaf19e346a,
   0x3f64345d2cff20aa,
   0x3f6474c4ff3c7eb8,
   0x3f64b3ee454e6b48,
   0x3f6506a83b888ccf,
   0x3f656065bcb7422f,
   0x3f65b905752207d4,
   0x3f66104596a7fb0e,
   0x3f6665eb7e3ad263,
   0x3f66b9c4acca3850,
   0x3f670ba7b08a9c51,
   0x3f675b74fcfb0094,
   0x3f67a917afaf0212,
   0x3f67f4863f6cb494,
   0x3f683dc312b127cf,
   0x3f6884dcfa26dbc0,
   0x3f68c9ef8b114616,
   0x3f691d692922a90e,
   0x3f6982d84b6d9850,
   0x3f69e787296e9a01,
   0x3f6a4b0f391716c0,
   0x3f6aad3b9fb3b883,
   0x3f6b0de2d4ea2cfc,
   0x3f6b6cdca7797f27]

theorem record2684ChunkBits060Length2685 :
    (record2684ChunkBits0602685).length = 32 := by
  decide

theorem record2684ChunkSum0602685 :
    ((record2684ChunkBits0602685).map binary64Value2674).sum =
      (200958899810936665 : ℚ) / 2305843009213693952 := by
  norm_num [record2684ChunkBits0602685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1952 through 1983,
decoded and summed as exact rationals. -/
def record2684ChunkBits0612685 : List Nat :=
  [0x3f6bca0e9a92ef4f,
   0x3f6c25690a65080f,
   0x3f6c7ee69eaf0e89,
   0x3f6cd68df56a2be8,
   0x3f6d2c719d473734,
   0x3f6da5568c3a4a22,
   0x3f6e203fa9eeb965,
   0x3f6e99777978434e,
   0x3f6f10a3271889f8,
   0x3f6f85722e73275b,
   0x3f6ff79faff776e6,
   0x3f703379d7ad13dd,
   0x3f7069a21c70aede,
   0x3f709e3b35615c02,
   0x3f70d13faf995baf,
   0x3f7102b2798a1d00,
   0x3f71329f32413f88,
   0x3f71611a61da3718,
   0x3f71994fb6563a35,
   0x3f71de2e282d2a9e,
   0x3f72227f6d9c2eeb,
   0x3f7265f80faa382f,
   0x3f72a8748143bdba,
   0x3f72e9d93ff8e5bd,
   0x3f732a0b9bcf3b84,
   0x3f7368fa78fb8a78,
   0x3f73a69bfee5789b,
   0x3f73e2ee39ccaeec,
   0x3f741df7089fb8c4,
   0x3f745a94b522d05e,
   0x3f74aee3928d4447,
   0x3f75023560572502]

theorem record2684ChunkBits061Length2685 :
    (record2684ChunkBits0612685).length = 32 := by
  decide

theorem record2684ChunkSum0612685 :
    ((record2684ChunkBits0612685).map binary64Value2674).sum =
      (310278979717010125 : ℚ) / 2305843009213693952 := by
  norm_num [record2684ChunkBits0612685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 1984 through 2015,
decoded and summed as exact rationals. -/
def record2684ChunkBits0622685 : List Nat :=
  [0x3f755445c31ef0f5,
   0x3f75a4d6b90db4d7,
   0x3f75f3b190d33477,
   0x3f7640a7d15efcb0,
   0x3f768b941111fda8,
   0x3f76d45abad7ab4f,
   0x3f771aeabf3be155,
   0x3f775f3e2f26e0a0,
   0x3f77a15abd722b72,
   0x3f77e1522410d05c,
   0x3f781f4269090adc,
   0x3f786a32a8ffa8cd,
   0x3f78c6d076443ac1,
   0x3f7922a299d286c0,
   0x3f797d3bc2fa2b8d,
   0x3f79d66c7f5ceb59,
   0x3f7a2e10a61ac1ee,
   0x3f7a840539dbb166,
   0x3f7ad8343580875d,
   0x3f7b2a917ba338e9,
   0x3f7b7b1b858ab51f,
   0x3f7bc9dba8531ada,
   0x3f7c2184b99a2a49,
   0x3f7c92d994bf49c9,
   0x3f7d02b55da6612f,
   0x3f7d70bb410966f3,
   0x3f7ddc97664e4562,
   0x3f7e46003ca589f9,
   0x3f7eacb7b2359738,
   0x3f7f108c53a5014a,
   0x3f7f715a51ee00df,
   0x3f7fcf0c6be94b51]

theorem record2684ChunkBits062Length2685 :
    (record2684ChunkBits0622685).length = 32 := by
  decide

theorem record2684ChunkSum0622685 :
    ((record2684ChunkBits0622685).map binary64Value2674).sum =
      (236037310553767313 : ℚ) / 1152921504606846976 := by
  norm_num [record2684ChunkBits0622685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2016 through 2047,
decoded and summed as exact rationals. -/
def record2684ChunkBits0632685 : List Nat :=
  [0x3f8014ce5c351bc7,
   0x3f80408aa692228e,
   0x3f806ac85ef80bc8,
   0x3f80939d37b0369a,
   0x3f80c50a7158e7eb,
   0x3f8102b156db513b,
   0x3f813fc77652b2cd,
   0x3f817bfef2c3521d,
   0x3f81b7388c3dbf11,
   0x3f81f15cdc90caa9,
   0x3f822a550a369fd0,
   0x3f82621353f3ce85,
   0x3f829890bee190ee,
   0x3f82cdcd68379563,
   0x3f8301d1a6b84bd7,
   0x3f83404e9042fafe,
   0x3f838bc301213005,
   0x3f83d625496c5432,
   0x3f841f36fc8876ff,
   0x3f8466bfec36ce26,
   0x3f84ac8f0a0bc14f,
   0x3f84f07b38ae3b72,
   0x3f8532640b871fd3,
   0x3f85723273a2d5c6,
   0x3f85afd9584f46b9,
   0x3f85eb561992033c,
   0x3f8624b0fa11007d,
   0x3f865bfd6d8accb0,
   0x3f86915a4881d985,
   0x3f86d1f7fdc93f49,
   0x3f8723573c7944cc,
   0x3f8773ebdd4a92b4]

theorem record2684ChunkBits063Length2685 :
    (record2684ChunkBits0632685).length = 32 := by
  decide

theorem record2684ChunkSum0632685 :
    ((record2684ChunkBits0632685).map binary64Value2674).sum =
      (88095448853771153 : ℚ) / 288230376151711744 := by
  norm_num [record2684ChunkBits0632685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2048 through 2079,
decoded and summed as exact rationals. -/
def record2684ChunkBits0642685 : List Nat :=
  [0x3f87c3487091aa31,
   0x3f881143df71eb2d,
   0x3f885dbffd472863,
   0x3f88a89f2b391866,
   0x3f88f1d01b435aa2,
   0x3f89394a94515b2d,
   0x3f897f0fd99ac95a,
   0x3f89c32af7bcddf0,
   0x3f8a1b17db699830,
   0x3f8a7ea6af26a9a1,
   0x3f8ae0aab09d0a9d,
   0x3f8b40d0c3548482,
   0x3f8b9ece72b0467a,
   0x3f8bfa63185cfc1e,
   0x3f8c5358ed182a2e,
   0x3f8ca9860252bde8,
   0x3f8cfccd22d026df,
   0x3f8d4d1e97f31180,
   0x3f8d9a78d0e39cde,
   0x3f8de4e8e82b64ce,
   0x3f8e2c8b03d65e39,
   0x3f8e718a8b998a24,
   0x3f8ec51fad040b3d,
   0x3f8f2f77e34232c2,
   0x3f8f98b78bf418d0,
   0x3f900023786bd9f5,
   0x3f9032f88e0461b7,
   0x3f9064c7e5867c2e,
   0x3f90957ea4af791d,
   0x3f90c51245582a2c,
   0x3f90f37e6dd03e7b,
   0x3f9120c563d2c2c1]

theorem record2684ChunkBits064Length2685 :
    (record2684ChunkBits0642685).length = 32 := by
  decide

theorem record2684ChunkSum0642685 :
    ((record2684ChunkBits0642685).map binary64Value2674).sum =
      (259409628954714323 : ℚ) / 576460752303423488 := by
  norm_num [record2684ChunkBits0642685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2080 through 2111,
decoded and summed as exact rationals. -/
def record2684ChunkBits0652685 : List Nat :=
  [0x3f914cf462d1f96e,
   0x3f918a0e74a28554,
   0x3f91cb2d53e3b953,
   0x3f920b367a6a9c9a,
   0x3f9249f2c7d4b38c,
   0x3f92873155bf2399,
   0x3f92c2c7c0119490,
   0x3f92fc92db385b19,
   0x3f933477b8b391b7,
   0x3f936a63fa1f9844,
   0x3f939e4e4f6a7156,
   0x3f93d036e0979005,
   0x3f940027a0c8c1e8,
   0x3f942e3487ed4d93,
   0x3f945a7bb01ed6f4,
   0x3f94901fcd8edfef,
   0x3f94d518763e5cc9,
   0x3f951951c3c69785,
   0x3f955c63cfb1f7ae,
   0x3f959e2c854437c2,
   0x3f95de93b44ffbdb,
   0x3f961d81582b659f,
   0x3f965ae870876933,
   0x3f9696c3f60d1509,
   0x3f96d117295f2a9c,
   0x3f9709edca714f87,
   0x3f975dd55b51640c,
   0x3f97b2413e9577fb,
   0x3f9805288391f456,
   0x3f98564364946183,
   0x3f98a5521c1de260,
   0x3f98f21ddff7f0ce]

theorem record2684ChunkBits065Length2685 :
    (record2684ChunkBits0652685).length = 32 := by
  decide

theorem record2684ChunkSum0652685 :
    ((record2684ChunkBits0652685).map binary64Value2674).sum =
      (94167092163250155 : ℚ) / 144115188075855872 := by
  norm_num [record2684ChunkBits0652685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2112 through 2143,
decoded and summed as exact rationals. -/
def record2684ChunkBits0662685 : List Nat :=
  [0x3f993c79c7ec1540,
   0x3f9984439ed93028,
   0x3f99c9649c8bf131,
   0x3f9a0bd2065f2953,
   0x3f9a4b8db437bafd,
   0x3f9a88a6999695f7,
   0x3f9ac338d0631179,
   0x3f9afb6d9bbd6343,
   0x3f9b3f8a3ae79908,
   0x3f9b9821302b410b,
   0x3f9befb5ec58731c,
   0x3f9c45bc0d0a7021,
   0x3f9c9a086ec1ce47,
   0x3f9cec7d3de3bb06,
   0x3f9d3cfcc8b0b558,
   0x3f9d8b78132ab040,
   0x3f9dd7eab7a73000,
   0x3f9e225b26a8f0b6,
   0x3f9e6e90f6b4ea8d,
   0x3f9edcd98dea387d,
   0x3f9f497583465c92,
   0x3f9fb3fdc31d9cd7,
   0x3fa00e0a5e3890ac,
   0x3fa040b3db2c3753,
   0x3fa071d8048e9a29,
   0x3fa0a15a1f2dedb0,
   0x3fa0cf248b5898f1,
   0x3fa0fb29390e992c,
   0x3fa125620bea1639,
   0x3fa14dd12ced0f4e,
   0x3fa1748148297ce5,
   0x3fa19985b3faec4f]

theorem record2684ChunkBits066Length2685 :
    (record2684ChunkBits0662685).length = 32 := by
  decide

theorem record2684ChunkSum0662685 :
    ((record2684ChunkBits0662685).map binary64Value2674).sum =
      (134845744618706989 : ℚ) / 144115188075855872 := by
  norm_num [record2684ChunkBits0662685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2144 through 2175,
decoded and summed as exact rationals. -/
def record2684ChunkBits0672685 : List Nat :=
  [0x3fa1bcfa7f4d2762,
   0x3fa1e7efe6583df8,
   0x3fa22076cbe7f008,
   0x3fa25851431cbff6,
   0x3fa28f21420a3a17,
   0x3fa2c4cb5b7620ec,
   0x3fa2f93ce3da5d9e,
   0x3fa32c6309b80f50,
   0x3fa35e347fa8aec5,
   0x3fa38eaeb9ea1b38,
   0x3fa3bdd62821bc88,
   0x3fa3f1e158b0b827,
   0x3fa4384c82ad3535,
   0x3fa47d8ececd060e,
   0x3fa4c16612d29e15,
   0x3fa5039661ea687e,
   0x3fa543eb6bf062b3,
   0x3fa58237dc292e64,
   0x3fa5be5776c7faa6,
   0x3fa5f82f56ef1721,
   0x3fa62fae7fc2e0a5,
   0x3fa664ce5ac707ba,
   0x3fa697931de06674,
   0x3fa6c80c1693312b,
   0x3fa6f653d7b51462,
   0x3fa72290466d978e,
   0x3fa7582b1bf39832,
   0x3fa79f9d93554bb0,
   0x3fa7e62cf664d952,
   0x3fa82b5d0f4a7946,
   0x3fa86f0bcf790ed7,
   0x3fa8b122ad17d304]

theorem record2684ChunkBits067Length2685 :
    (record2684ChunkBits0672685).length = 32 := by
  decide

theorem record2684ChunkSum0672685 :
    ((record2684ChunkBits0672685).map binary64Value2674).sum =
      (47525802726969659 : ℚ) / 36028797018963968 := by
  norm_num [record2684ChunkBits0672685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2176 through 2207,
decoded and summed as exact rationals. -/
def record2684ChunkBits0682685 : List Nat :=
  [0x3fa8f18aba495302,
   0x3fa930395d0aa0e5,
   0x3fa96d2c9d5c58ac,
   0x3fa9a86b63824b66,
   0x3fa9eeb00f1180f8,
   0x3faa47f8b55aa0c8,
   0x3faa9fb115ba492c,
   0x3faaf584360495ab,
   0x3fab49255a159928,
   0x3fab9a5123eec274,
   0x3fabe8ce9b3b3c57,
   0x3fac34701bae2255,
   0x3fac7d14294b732b,
   0x3facc2a6292a83c4,
   0x3fad051efcb4d68f,
   0x3fad44857cdadbce,
   0x3fad80eed229f849,
   0x3fadba7ea62f895b,
   0x3fadf1672a1ef031,
   0x3fae33e8386dbfb9,
   0x3fae8db119fbefb9,
   0x3faee64fcb8b334f,
   0x3faf3d2127b98d4c,
   0x3faf91fa7437b85a,
   0x3fafe4bfbb859a1d,
   0x3fb01aaa4ccf36ac,
   0x3fb041d62dca61c7,
   0x3fb067e2b8cd94fa,
   0x3fb08cd4d8d58fd9,
   0x3fb0bbbb092a1665,
   0x3fb0f3e0182cca00,
   0x3fb12af77097f633]

theorem record2684ChunkBits068Length2685 :
    (record2684ChunkBits0682685).length = 32 := by
  decide

theorem record2684ChunkSum0682685 :
    ((record2684ChunkBits0682685).map binary64Value2674).sum =
      (264988334534449209 : ℚ) / 144115188075855872 := by
  norm_num [record2684ChunkBits0682685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2208 through 2239,
decoded and summed as exact rationals. -/
def record2684ChunkBits0692685 : List Nat :=
  [0x3fb160cb1701e750,
   0x3fb1952a3abff5e7,
   0x3fb1c7ea7a1163f3,
   0x3fb1f8e834b7d7dc,
   0x3fb228072194d0b3,
   0x3fb25532d381be34,
   0x3fb2805f2c50f03c,
   0x3fb2a988bc9e6d94,
   0x3fb2d0b50ecb9c7d,
   0x3fb2f5f2db2c345b,
   0x3fb3195a236f5e36,
   0x3fb33b0c31167513,
   0x3fb363dba0f522ff,
   0x3fb39bbff1c26bec,
   0x3fb3d2e3d3e62b31,
   0x3fb408dd9a29e73e,
   0x3fb43d9324b4da17,
   0x3fb470f3b6cf59fe,
   0x3fb4a2ee58c7c6fe,
   0x3fb4d37bed5755d0,
   0x3fb5029c6605ff83,
   0x3fb53056ddb414a4,
   0x3fb56e52c40a28d8,
   0x3fb5b4780af77e25,
   0x3fb5f93921845257,
   0x3fb63c51e4d1cb21,
   0x3fb67d8530e3bda8,
   0x3fb6bc9dc4aac05b,
   0x3fb6f96f11d82229,
   0x3fb733d5f7a65119,
   0x3fb76bb9679419ff,
   0x3fb7a10af2c92ab9]

theorem record2684ChunkBits069Length2685 :
    (record2684ChunkBits0692685).length = 32 := by
  decide

theorem record2684ChunkSum0692685 :
    ((record2684ChunkBits0692685).map binary64Value2674).sum =
      (45702501856275117 : ℚ) / 18014398509481984 := by
  norm_num [record2684ChunkBits0692685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2240 through 2271,
decoded and summed as exact rationals. -/
def record2684ChunkBits0702685 : List Nat :=
  [0x3fb7d3c73e80989b,
   0x3fb803f65d758e3f,
   0x3fb831ac0be3f2da,
   0x3fb85d07cb4dc0ca,
   0x3fb88634dadc3981,
   0x3fb8b80933922fc7,
   0x3fb8fd429a93311f,
   0x3fb9418393e6844a,
   0x3fb98443f2eea292,
   0x3fb9c5637447a852,
   0x3fba04cdb1ed97d7,
   0x3fba426e13963779,
   0x3fba7e3c5746c65a,
   0x3fbab839301b6466,
   0x3fbaf06e57c4eb9c,
   0x3fbb418695c66900,
   0x3fbb987fc53a1eb2,
   0x3fbbeda2c3eec0b1,
   0x3fbc409a2d64df5e,
   0x3fbc9119cc5d5cc3,
   0x3fbcdedf9184da57,
   0x3fbd29b4945b093d,
   0x3fbd716df95a51e6,
   0x3fbdb5edbc11116b,
   0x3fbdf7235b7d80b0,
   0x3fbe350c668b5f0e,
   0x3fbe6fb4e61a1a67,
   0x3fbea737a16e8c1a,
   0x3fbedbbe397bd429,
   0x3fbf0d811701531b,
   0x3fbf49b4a153fc4b,
   0x3fbf9eafc73fde45]

theorem record2684ChunkBits070Length2685 :
    (record2684ChunkBits0702685).length = 32 := by
  decide

theorem record2684ChunkSum0702685 :
    ((record2684ChunkBits0702685).map binary64Value2674).sum =
      (248394286894185787 : ℚ) / 72057594037927936 := by
  norm_num [record2684ChunkBits0702685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2272 through 2303,
decoded and summed as exact rationals. -/
def record2684ChunkBits0712685 : List Nat :=
  [0x3fbff27025a10c73,
   0x3fc0222438a889f8,
   0x3fc04a08e0f5cf64,
   0x3fc070da02c5dd5b,
   0x3fc0968b7d375a26,
   0x3fc0bb18cfd4e988,
   0x3fc0de8312a37b91,
   0x3fc100d29e2e7ef5,
   0x3fc13569da9cdc7b,
   0x3fc16b00d253e751,
   0x3fc19f67ad963eb7,
   0x3fc1d26945e87629,
   0x3fc203d637cce130,
   0x3fc233859210be44,
   0x3fc26155748711a3,
   0x3fc28d2b9d8ea4e4,
   0x3fc2b6f5e5988c69,
   0x3fc2deaaa7aa4be0,
   0x3fc30449159124b9,
   0x3fc327d97632bf30,
   0x3fc3496d4c1763a8,
   0x3fc3691f620225ba,
   0x3fc38713bb2a510f,
   0x3fc3ab45ab2bf232,
   0x3fc3df2ef180ec78,
   0x3fc412500adec302,
   0x3fc4443b3e05064d,
   0x3fc474d8dab9d524,
   0x3fc4a41a7223feb9,
   0x3fc4d1f18ba3dbae,
   0x3fc4fe591863eee6,
   0x3fc529530a5520e4]

theorem record2684ChunkBits071Length2685 :
    (record2684ChunkBits0712685).length = 32 := by
  decide

theorem record2684ChunkSum0712685 :
    ((record2684ChunkBits0712685).map binary64Value2674).sum =
      (333931079164989305 : ℚ) / 72057594037927936 := by
  norm_num [record2684ChunkBits0712685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2304 through 2335,
decoded and summed as exact rationals. -/
def record2684ChunkBits0722685 : List Nat :=
  [0x3fc553aa2cef5418,
   0x3fc59678f4485482,
   0x3fc5d80648c5b532,
   0x3fc61809c08d2b43,
   0x3fc65641bfab34d1,
   0x3fc69273ff597faa,
   0x3fc6cc6e64d1d35f,
   0x3fc70407c32ac02c,
   0x3fc7392087782cd3,
   0x3fc76ba34e344085,
   0x3fc79b8560aa5140,
   0x3fc7c8c718c5e296,
   0x3fc7f374294c78ec,
   0x3fc81ba3c87427ab,
   0x3fc84178b908701c,
   0x3fc865213010c536,
   0x3fc89030ea871433,
   0x3fc8cf116de8e0f7,
   0x3fc90cf84dc04c77,
   0x3fc9495c2bc6c488,
   0x3fc98420d7ad2f3f,
   0x3fc9bd358c21b13f,
   0x3fc9f4898324fe05,
   0x3fca2a177032a3e1,
   0x3fca5de2a9aa9204,
   0x3fca94c255dd67af,
   0x3fcae6196a10c29a,
   0x3fcb35d4e801ab8e,
   0x3fcb839bfe63baa9,
   0x3fcbcf1def255d31,
   0x3fcc1813301aa99a,
   0x3fcc5e3e71edff68]

theorem record2684ChunkBits072Length2685 :
    (record2684ChunkBits0722685).length = 32 := by
  decide

theorem record2684ChunkSum0722685 :
    ((record2684ChunkBits0722685).map binary64Value2674).sum =
      (13902177313275799 : ℚ) / 2251799813685248 := by
  norm_num [record2684ChunkBits0722685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2336 through 2367,
decoded and summed as exact rationals. -/
def record2684ChunkBits0732685 : List Nat :=
  [0x3fcca16d8c914cd4,
   0x3fcce17a504289ef,
   0x3fcd1e4b39f183ba,
   0x3fcd57d4097f4759,
   0x3fcd8e1637e301ee,
   0x3fcdc1214ad2078d,
   0x3fcdf113031499a7,
   0x3fce1e176243a358,
   0x3fce4868845356d2,
   0x3fce7b6d70c6bcaf,
   0x3fcec742ba441294,
   0x3fcf11df4f7ee7cf,
   0x3fcf5a9800805d66,
   0x3fcfa14aeb8ed5d3,
   0x3fcfe5e43ba167fb,
   0x3fd014281d0ecfa4,
   0x3fd0344493ecaa05,
   0x3fd05349f82e30c1,
   0x3fd0767e7a985029,
   0x3fd0a7adcc7e40ff,
   0x3fd0d7d5008da04b,
   0x3fd106bdcbbde24a,
   0x3fd13436f9e6f1e4,
   0x3fd160151d09534b,
   0x3fd18a332c72cd42,
   0x3fd1b273134d6aef,
   0x3fd1d8be2e0b81e2,
   0x3fd1fd05b5f76721,
   0x3fd21f4319f769fc,
   0x3fd23f7843533fcf,
   0x3fd25dafc5044cda,
   0x3fd279fcf3d38053]

theorem record2684ChunkBits073Length2685 :
    (record2684ChunkBits0732685).length = 32 := by
  decide

theorem record2684ChunkSum0732685 :
    ((record2684ChunkBits0732685).map binary64Value2674).sum =
      (73307000333185563 : ℚ) / 9007199254740992 := by
  norm_num [record2684ChunkBits0732685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2368 through 2399,
decoded and summed as exact rationals. -/
def record2684ChunkBits0742685 : List Nat :=
  [0x3fd2947be545abad,
   0x3fd2ad51532342be,
   0x3fd2cb3a50585868,
   0x3fd2f8963bf01695,
   0x3fd325321c0369d9,
   0x3fd350a465632a28,
   0x3fd37ad92f5bca33,
   0x3fd3a3c51ca8a09e,
   0x3fd3cb5ceae8fb75,
   0x3fd3f19dbcf17a96,
   0x3fd4168db44b170f,
   0x3fd44358fc6abd93,
   0x3fd47e82e43592ab,
   0x3fd4b860b3f9de92,
   0x3fd4f0b043b877b1,
   0x3fd52735bcc94a5a,
   0x3fd55bbc6e570452,
   0x3fd58e178dbd60e8,
   0x3fd5be22e243d820,
   0x3fd5ebc35b8e0f5c,
   0x3fd616e791e68a76,
   0x3fd63f882f471800,
   0x3fd665a83fb1475f,
   0x3fd689556717e48a,
   0x3fd6aaa7fac5b501,
   0x3fd6c9c2fbdf263f,
   0x3fd6e6d3f05f215a,
   0x3fd709c2477bd2c3,
   0x3fd73fccdbfb2fbc,
   0x3fd774e9e464dc6a,
   0x3fd7a897c99adf37,
   0x3fd7dabee79f3dd6]

theorem record2684ChunkBits074Length2685 :
    (record2684ChunkBits0742685).length = 32 := by
  decide

theorem record2684ChunkSum0742685 :
    ((record2684ChunkBits0742685).map binary64Value2674).sum =
      (47672062270323573 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits0742685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2400 through 2431,
decoded and summed as exact rationals. -/
def record2684ChunkBits0752685 : List Nat :=
  [0x3fd80b51fe70675e,
   0x3fd83a4406620a21,
   0x3fd867920e0944b2,
   0x3fd89342672ee5be,
   0x3fd8cbb6c84576bf,
   0x3fd912676b84f7db,
   0x3fd95774fbedafac,
   0x3fd99a8f935ab90a,
   0x3fd9db6f2565d136,
   0x3fda19d47e74ebdd,
   0x3fda558a29e3b4b1,
   0x3fda8e653ead9fa0,
   0x3fdac44611d38ad5,
   0x3fdaf718cd760495,
   0x3fdb26d5eb4d3a5e,
   0x3fdb538290c4935d,
   0x3fdb7d30ca9d8f3a,
   0x3fdba3ffa684d8f8,
   0x3fdbc81b23afbabb,
   0x3fdbe9bbfda5e9f1,
   0x3fdc1216b7dd0e2f,
   0x3fdc51f56155eb66,
   0x3fdc90b42ef8da4f,
   0x3fdccdb5921a44a4,
   0x3fdd08de18c513e1,
   0x3fdd421ecea758a5,
   0x3fdd79690f92995f,
   0x3fddaeba2fe36f19,
   0x3fdde21ef18a90cc,
   0x3fde28bc6244e0cd,
   0x3fde7cc7878d34a3,
   0x3fdececbf7c8d99d]

theorem record2684ChunkBits075Length2685 :
    (record2684ChunkBits0752685).length = 32 := by
  decide

theorem record2684ChunkSum0752685 :
    ((record2684ChunkBits0752685).map binary64Value2674).sum =
      (246148235241651205 : ℚ) / 18014398509481984 := by
  norm_num [record2684ChunkBits0752685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2432 through 2463,
decoded and summed as exact rationals. -/
def record2684ChunkBits0762685 : List Nat :=
  [0x3fdf1e6977ae321d,
   0x3fdf6b4969f65b2c,
   0x3fdfb52001020cf5,
   0x3fdffbad51e8b842,
   0x3fe01f5f241ed80a,
   0x3fe03f16bcd2cb2a,
   0x3fe05cf1ec03c292,
   0x3fe078eca062f98e,
   0x3fe0930a737a99dc,
   0x3fe0ab56cb083ab4,
   0x3fe0c1e4e51ab616,
   0x3fe0d6cfcd405c91,
   0x3fe0ea3a38e8d193,
   0x3fe1017603545b50,
   0x3fe1271285321948,
   0x3fe14bff621e7d4b,
   0x3fe16fdd3354f19a,
   0x3fe1929bdcad61a8,
   0x3fe1b432c2313f7e,
   0x3fe1d4998a04a149,
   0x3fe1f3cef4d93c12,
   0x3fe211dcfd11f5df,
   0x3fe23daa26ed0565,
   0x3fe26f50610553fb,
   0x3fe29fb47718c3c8,
   0x3fe2ce9cf5115bd6,
   0x3fe2fbd64cf8448a,
   0x3fe327338c547894,
   0x3fe3508efed65331,
   0x3fe377cabde92378,
   0x3fe39cd12ca4cab2,
   0x3fe3bf955f691f4e]

theorem record2684ChunkBits076Length2685 :
    (record2684ChunkBits0762685).length = 32 := by
  decide

theorem record2684ChunkSum0762685 :
    ((record2684ChunkBits0762685).map binary64Value2674).sum =
      (38516046169691 : ℚ) / 2199023255552 := by
  norm_num [record2684ChunkBits0762685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2464 through 2495,
decoded and summed as exact rationals. -/
def record2684ChunkBits0772685 : List Nat :=
  [0x3fe3e0136e32df72,
   0x3fe3fe50b072e779,
   0x3fe41a5be0ea832c,
   0x3fe4344d27c82bca,
   0x3fe44c4608ff83ac,
   0x3fe4627134a79603,
   0x3fe47ce99e8c35a9,
   0x3fe4a8e0a4df59a3,
   0x3fe4d4058ee66e98,
   0x3fe4fde5e4408985,
   0x3fe5266f2569d4e3,
   0x3fe54d97b9d3412d,
   0x3fe57356606a4aa5,
   0x3fe597ad06e79726,
   0x3fe5baa7e31b0d59,
   0x3fe5f0a25e1aa1c6,
   0x3fe62b08aced8a6f,
   0x3fe663e5b0ef8cef,
   0x3fe69af4f146f615,
   0x3fe6cff91891487d,
   0x3fe702bccbe3c541,
   0x3fe733136b1bb32a,
   0x3fe760d9ba09d237,
   0x3fe78bf671df820f,
   0x3fe7b45aba0adb02,
   0x3fe7da02876a5f06,
   0x3fe7fcf4e06cc26c,
   0x3fe81d44045edb0e,
   0x3fe83b0d73d59247,
   0x3fe85679d7d61f4c,
   0x3fe86fbcc5276b62,
   0x3fe88dca57772f89]

theorem record2684ChunkBits077Length2685 :
    (record2684ChunkBits0772685).length = 32 := by
  decide

theorem record2684ChunkSum0772685 :
    ((record2684ChunkBits0772685).map binary64Value2674).sum =
      (49913962415784229 : ℚ) / 2251799813685248 := by
  norm_num [record2684ChunkBits0772685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2496 through 2527,
decoded and summed as exact rationals. -/
def record2684ChunkBits0782685 : List Nat :=
  [0x3fe8c1008bacd247,
   0x3fe8f33904a1012a,
   0x3fe923eae974c865,
   0x3fe95300be0b5a8b,
   0x3fe9806f9b716600,
   0x3fe9ac2d1d0fb187,
   0x3fe9d63b7e5c5231,
   0x3fe9feab4a9bcb6c,
   0x3fea40a7b5c6e2df,
   0x3fea84e7990d75ff,
   0x3feac745a65f5e8d,
   0x3feb0770fed0ff6a,
   0x3feb452169a1a81a,
   0x3feb801850b3eda2,
   0x3febb821a1a09a55,
   0x3febed1492e083bd,
   0x3fec1ed44c59837e,
   0x3fec4d50725bb188,
   0x3fec788591c2f83f,
   0x3feca07d6b924485,
   0x3fecc54f1dfa910b,
   0x3fece71f2a431b20,
   0x3fed061f4c31561e,
   0x3fed228e2e504c5f,
   0x3fed4448d92e16ec,
   0x3fed7f7c6caedbc1,
   0x3fedb9840e7b9426,
   0x3fedf1bd8fd77978,
   0x3fee28108bfd56e8,
   0x3fee5c710cd905cb,
   0x3fee8ed3c2de41bf,
   0x3feebf40a93a0869]

theorem record2684ChunkBits078Length2685 :
    (record2684ChunkBits0782685).length = 32 := by
  decide

theorem record2684ChunkSum0782685 :
    ((record2684ChunkBits0782685).map binary64Value2674).sum =
      (3913286371257335 : ℚ) / 140737488355328 := by
  norm_num [record2684ChunkBits0782685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2528 through 2559,
decoded and summed as exact rationals. -/
def record2684ChunkBits0792685 : List Nat :=
  [0x3feeedc7c3cfea30,
   0x3fef3df616c5c21a,
   0x3fef8d6537aa3c73,
   0x3fefda8fe8524405,
   0x3ff0128b6330d2a0,
   0x3ff036526414be6b,
   0x3ff058783277513b,
   0x3ff078de4e2b31ee,
   0x3ff0976cee3314ce,
   0x3ff0b41362a50e37,
   0x3ff0cec864e66971,
   0x3ff0e78a5580c7d7,
   0x3ff0fe5f6699c513,
   0x3ff11355b1dc856e,
   0x3ff12683386979ca,
   0x3ff13805cb318f7b,
   0x3ff14802d9f9df8b,
   0x3ff15ae3c57f1a93,
   0x3ff17d0372d8ad4c,
   0x3ff19e70384b79b9,
   0x3ff1beca4fc5f669,
   0x3ff1de03b3f5beaf,
   0x3ff1fc15addacd50,
   0x3ff218f9fb829beb,
   0x3ff234b9b85710fd,
   0x3ff250a03a8eade7,
   0x3ff27fb66510d0f6,
   0x3ff2adaaf79385ea,
   0x3ff2da40bc90187f,
   0x3ff3053ff176b4ce,
   0x3ff32e77062f8fed,
   0x3ff355bb494533e2]

theorem record2684ChunkBits079Length2685 :
    (record2684ChunkBits0792685).length = 32 := by
  decide

theorem record2684ChunkSum0792685 :
    ((record2684ChunkBits0792685).map binary64Value2674).sum =
      (78089938295250047 : ℚ) / 2251799813685248 := by
  norm_num [record2684ChunkBits0792685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2560 through 2591,
decoded and summed as exact rationals. -/
def record2684ChunkBits0802685 : List Nat :=
  [0x3ff37ae9806fe701,
   0x3ff39de66d30189a,
   0x3ff3be9f3d0378b4,
   0x3ff3dd09e4942192,
   0x3ff3f92565036508,
   0x3ff412f9fa308cd8,
   0x3ff42a99309855ba,
   0x3ff4401de1256a4a,
   0x3ff453ac11145acc,
   0x3ff46570b3e0897a,
   0x3ff47a55c464ade6,
   0x3ff4a165df287e29,
   0x3ff4c7a4d1a1bb3b,
   0x3ff4eca26ae42d42,
   0x3ff5104ee6b37352,
   0x3ff532a2fc2f31ae,
   0x3ff55398646680f8,
   0x3ff57342ba1a9d96,
   0x3ff5954e6829daad,
   0x3ff5cba2e9eb092f,
   0x3ff6009d3fd510d3,
   0x3ff633f5cc4ad652,
   0x3ff6656b6825c307,
   0x3ff694c441c22406,
   0x3ff6c1cea5155901,
   0x3ff6ec61ac7f97fa,
   0x3ff7145dd9ff6065,
   0x3ff739ad9844c237,
   0x3ff75c45a2ef1c4d,
   0x3ff77c2554f7fa3c,
   0x3ff79956dc01ea1c,
   0x3ff7b3ef4ef3dbe2]

theorem record2684ChunkBits080Length2685 :
    (record2684ChunkBits0802685).length = 32 := by
  decide

theorem record2684ChunkSum0802685 :
    ((record2684ChunkBits0802685).map binary64Value2674).sum =
      (193214829361080913 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits0802685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2592 through 2623,
decoded and summed as exact rationals. -/
def record2684ChunkBits0812685 : List Nat :=
  [0x3ff7cc0ea5fa5cb7,
   0x3ff7e1df91ca39ca,
   0x3ff7f5972fccb6b3,
   0x3ff80ca35887a355,
   0x3ff8393793f92b0f,
   0x3ff864d4769d3f66,
   0x3ff88ef6fff541ad,
   0x3ff8b78d3c6b4a8d,
   0x3ff8de8f1a22a31a,
   0x3ff903f688e2afb7,
   0x3ff927dac0ba4731,
   0x3ff951079222538f,
   0x3ff98f57cb4ddbd1,
   0x3ff9cc07ee0b9aaa,
   0x3ffa06c4de447063,
   0x3ffa3f432f0a41bc,
   0x3ffa754024167865,
   0x3ffaa88298205867,
   0x3ffad8dbc7b73007,
   0x3ffb0628003d4269,
   0x3ffb304f32708108,
   0x3ffb574567b156bd,
   0x3ffb7b0b18e38163,
   0x3ffb9bad656cc301,
   0x3ffbb946287aaee0,
   0x3ffbd3fbed8c2aaf,
   0x3ffbec01b346ac5f,
   0x3ffc019692a55a61,
   0x3ffc1aae4af53b5a,
   0x3ffc4d2fe5fc13d8,
   0x3ffc7e9365a027a1,
   0x3ffcae4102310a3d]

theorem record2684ChunkBits081Length2685 :
    (record2684ChunkBits0812685).length = 32 := by
  decide

theorem record2684ChunkSum0812685 :
    ((record2684ChunkBits0812685).map binary64Value2674).sum =
      (236223653676367399 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits0812685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2624 through 2655,
decoded and summed as exact rationals. -/
def record2684ChunkBits0822685 : List Nat :=
  [0x3ffcdc24c1d71ff0,
   0x3ffd083609e16103,
   0x3ffd32732618a249,
   0x3ffd5af483bb92ff,
   0x3ffd8c74148466f0,
   0x3ffdd3a991136c34,
   0x3ffe18f3cde357f3,
   0x3ffe5bf276c031fd,
   0x3ffe9c4e3c3d4a89,
   0x3ffed9b9fcea3d35,
   0x3fff13f3ce9e229c,
   0x3fff4ac5e77f4b3c,
   0x3fff7e07665c7a96,
   0x3fffad9cf9b56206,
   0x3fffd9796489fe31,
   0x400000ceefd3a35f,
   0x4000130d2ae10f0f,
   0x40002386bc24be4e,
   0x400032525538418a,
   0x40003f8ddfd0cadb,
   0x40004b5e452596d0,
   0x400058ff838073f1,
   0x4000758c0b55ca67,
   0x400091714c5324c4,
   0x4000ac579db7115b,
   0x4000c633bbb4b638,
   0x4000df00f0559e93,
   0x4000f6c4705b8fcc,
   0x40010d828261ecd4,
   0x40012b0b8fb9f81e,
   0x40015384c427a9c7,
   0x40017ada69842671]

theorem record2684ChunkBits082Length2685 :
    (record2684ChunkBits0822685).length = 32 := by
  decide

theorem record2684ChunkSum0822685 :
    ((record2684ChunkBits0822685).map binary64Value2674).sum =
      (71804807697222145 : ℚ) / 1125899906842624 := by
  norm_num [record2684ChunkBits0822685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2656 through 2687,
decoded and summed as exact rationals. -/
def record2684ChunkBits0832685 : List Nat :=
  [0x4001a0d51c36b40d,
   0x4001c542c7172fe5,
   0x4001e7f74d63567f,
   0x400208cd2203de7c,
   0x400227a5cbf2669b,
   0x4002446a57887b66,
   0x40025f0bb456a8eb,
   0x40027782feff9ada,
   0x40028dd1b670daae,
   0x4002a201db639cda,
   0x4002b425f905b7da,
   0x4002c4591559ac51,
   0x4002d2be87b4061f,
   0x4002df81b39c8b55,
   0x4002ee1ee9ceae63,
   0x40030e2ebf29bd71,
   0x40032d7eeb8bd5d9,
   0x40034baaec49b03e,
   0x400368a6534fc3b9,
   0x4003846c2848ab48,
   0x40039f0d5a3b4ad9,
   0x4003b87e675dd461,
   0x4003db8e0e048676,
   0x400409693819280d,
   0x400435ef9997348b,
   0x400460e18aa76409,
   0x40048a058e636527,
   0x4004b1291547a58c,
   0x4004d62129e5ef7a,
   0x4004f8cb07a9143b,
   0x4005190c9b6ccef9,
   0x400536d4ed863c7c]

theorem record2684ChunkBits083Length2685 :
    (record2684ChunkBits0832685).length = 32 := by
  decide

theorem record2684ChunkSum0832685 :
    ((record2684ChunkBits0832685).map binary64Value2674).sum =
      (43453773856957245 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits0832685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2688 through 2719,
decoded and summed as exact rationals. -/
def record2684ChunkBits0842685 : List Nat :=
  [0x4005521c74ad8e5d,
   0x40056ae550f5d60d,
   0x4005813b6dbe4274,
   0x400595348944c50d,
   0x4005a6f0203e1540,
   0x4005b6973ba4d8fa,
   0x4005c45c1eca60aa,
   0x4005d3f717fad241,
   0x4005f7df0a2e19cb,
   0x40061ae87cd2ee6a,
   0x40063ca084ffe320,
   0x40065cf93ce0f07b,
   0x40067bed474d2afb,
   0x40069994a34776a9,
   0x4006b5dc827c94a4,
   0x4006df289bf6851c,
   0x400712ce41858f05,
   0x400744e390492939,
   0x4007751ffc7168b2,
   0x4007a34229a65be6,
   0x4007cf10c780fa98,
   0x4007f85b54cf49c4,
   0x40081efac9715767,
   0x400842d2268e211e,
   0x400863ceecb4fdab,
   0x400881e9773e4cc1,
   0x40089d253c0c528c,
   0x4008b590ee6d09a9,
   0x4008cb46838fdc78,
   0x4008de6b1b605b99,
   0x4008ef2eb686074b,
   0x4008fdcbdc0dacfc]

theorem record2684ChunkBits084Length2685 :
    (record2684ChunkBits0842685).length = 32 := by
  decide

theorem record2684ChunkSum0842685 :
    ((record2684ChunkBits0842685).map binary64Value2674).sum =
      (52040053271542845 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits0842685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2720 through 2751,
decoded and summed as exact rationals. -/
def record2684ChunkBits0852685 : List Nat :=
  [0x40090e313c106e2c,
   0x4009361f7c0ab83f,
   0x40095d11474f1d65,
   0x4009828425963705,
   0x4009a668e72ba5a3,
   0x4009c8b9ffd1f14a,
   0x4009e99e4a79338e,
   0x400a08f1a4dff6f2,
   0x400a395b99621e75,
   0x400a735ae4c8e229,
   0x400aab8b5b354957,
   0x400ae19a51a0117e,
   0x400b153d632bf685,
   0x400b46336b57beb9,
   0x400b7445631fd15d,
   0x400b9f4720dc8f1b,
   0x400bc717fa9a0fb2,
   0x400beba34a75d844,
   0x400c0ce0d458fbe5,
   0x400c2ad50bd57603,
   0x400c45913902e206,
   0x400c5d337ac34742,
   0x400c71e6a3ff4617,
   0x400c83e1f1da90d2,
   0x400c93689856dde6,
   0x400ca496bb54890e,
   0x400cd0ebbde93c9d,
   0x400cfc1eb1f7ade9,
   0x400d259bddbb5dc8,
   0x400d4d526b888009,
   0x400d7346943a5d87,
   0x400d9798aa10632f]

theorem record2684ChunkBits085Length2685 :
    (record2684ChunkBits0852685).length = 32 := by
  decide

theorem record2684ChunkSum0852685 :
    ((record2684ChunkBits0852685).map binary64Value2674).sum =
      (247192514246801275 : ℚ) / 2251799813685248 := by
  norm_num [record2684ChunkBits0852685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2752 through 2783,
decoded and summed as exact rationals. -/
def record2684ChunkBits0862685 : List Nat :=
  [0x400dba1eadbceeaa,
   0x400df2825a96eb33,
   0x400e334e0e16f45b,
   0x400e71ffea956b7c,
   0x400eae3a7c55deeb,
   0x400ee7a9dc764253,
   0x400f1e04ca3678c6,
   0x400f510da2dccccd,
   0x400f809338045331,
   0x400fac7183f789e6,
   0x400fd4923bd0cfbb,
   0x400ff8ed3e5f7264,
   0x40100cc46f8de248,
   0x40101b3d05466930,
   0x401027f22147408d,
   0x401032fcb95576ab,
   0x40103c7ccafee162,
   0x401044991722ec27,
   0x40104d712a8319f4,
   0x401065e4d557f25e,
   0x40107db54048fff8,
   0x4010948f5620dbe8,
   0x4010aa69f4ad802d,
   0x4010bf51f0324991,
   0x4010d34a4b621c8c,
   0x4010e640d5b4c784,
   0x401106f1579cdc61,
   0x40112b09c804ec23,
   0x40114dedf4f8de1f,
   0x40116f69073400cb,
   0x40118f4b9ad52960,
   0x4011ad6c5da9a0d6]

theorem record2684ChunkBits086Length2685 :
    (record2684ChunkBits0862685).length = 32 := by
  decide

theorem record2684ChunkSum0862685 :
    ((record2684ChunkBits0862685).map binary64Value2674).sum =
      (292596870780514165 : ℚ) / 2251799813685248 := by
  norm_num [record2684ChunkBits0862685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2784 through 2815,
decoded and summed as exact rationals. -/
def record2684ChunkBits0872685 : List Nat :=
  [0x4011c9a89a5c2f06,
   0x4011e3e4b09912df,
   0x4011fc0c79b9fab1,
   0x401212139a0a36f6,
   0x401225f5bdeeb486,
   0x401237b6c276bb9d,
   0x40124762c9210ae0,
   0x4012550e345f95a2,
   0x401260d588df59b4,
   0x40126add3da12705,
   0x401273516b371579,
   0x40127c5be0123bdd,
   0x4012974296877623,
   0x4012b16edccd212c,
   0x4012ca8377426ee5,
   0x4012e27657a83cf8,
   0x4012f95c02d0d416,
   0x40130f2fb66676e1,
   0x401323dfcb560904,
   0x4013497c0f4b6b5b,
   0x40137175e89e0c4b,
   0x4013980cca0a6240,
   0x4013bd0571e790d7,
   0x4013e02ada23790c,
   0x4014014ee937918e,
   0x4014204b0cd2e7a4,
   0x40143d00befd1907,
   0x40145759f538a472,
   0x40146f497978973f,
   0x401484cb2c56a1cc,
   0x401497e4302c21ae,
   0x4014a8a2fb221205]

theorem record2684ChunkBits087Length2685 :
    (record2684ChunkBits0872685).length = 32 := by
  decide

theorem record2684ChunkSum0872685 :
    ((record2684ChunkBits0872685).map binary64Value2674).sum =
      (172102162394018969 : ℚ) / 1125899906842624 := by
  norm_num [record2684ChunkBits0872685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2816 through 2847,
decoded and summed as exact rationals. -/
def record2684ChunkBits0882685 : List Nat :=
  [0x4014b71f5272938d,
   0x4014c37a30fdcc5a,
   0x4014cddd66d157a3,
   0x4014d67b5bcec0e9,
   0x4014df802c49947f,
   0x4014fce523bb1e6b,
   0x4015197a14aded73,
   0x401534d6fbf8df7b,
   0x40154ef1037810e3,
   0x401567eaa5d97b2d,
   0x40157fafeecfee24,
   0x401596310b999795,
   0x4015c13e0ea9442d,
   0x4015ed6a403766a3,
   0x40161803954741d6,
   0x401640c785bf9844,
   0x4016677a962c954b,
   0x40168be91de3b096,
   0x4016ade7f42dbb8b,
   0x4016cd5503c8f440,
   0x4016ea17c6b0d819,
   0x40170421a8370262,
   0x40171b6e4dfed770,
   0x40173003c4f13cfe,
   0x401741f29576780a,
   0x40175155b932f226,
   0x40175e527a466c2f,
   0x401769183d7f3c0e,
   0x401771dfc38c6a19,
   0x40177acd5feb5363,
   0x40179ae13d95bff2,
   0x4017ba09a16fb1ad]

theorem record2684ChunkBits088Length2685 :
    (record2684ChunkBits0882685).length = 32 := by
  decide

theorem record2684ChunkSum0882685 :
    ((record2684ChunkBits0882685).map binary64Value2674).sum =
      (200236941267547419 : ℚ) / 1125899906842624 := by
  norm_num [record2684ChunkBits0882685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2848 through 2879,
decoded and summed as exact rationals. -/
def record2684ChunkBits0892685 : List Nat :=
  [0x4017d7d2b01ccb7f,
   0x4017f430bac23414,
   0x40180f5d3bb00e50,
   0x40182921862e92a1,
   0x401841799e56c7f3,
   0x40187255108c57d6,
   0x4018a2e6edb99301,
   0x4018d1ad7aef72bb,
   0x4018fe5e90576319,
   0x401928b8039b8f7d,
   0x4019508082dd2541,
   0x4019758853a0c02d,
   0x401997a9f5d53659,
   0x4019b6caab309493,
   0x4019d2dae2187e0b,
   0x4019ebd6836581e2,
   0x401a01c5240172c0,
   0x401a14ba1662aba4,
   0x401a24d45c6b884d,
   0x401a323e77453886,
   0x401a3d2e245cbeb1,
   0x401a45e4530212ae,
   0x401a4e72e91f8892,
   0x401a713e79e1ba17,
   0x401a9304feb996b0,
   0x401ab346bd97419b,
   0x401ad1ff9e359621,
   0x401aef6e8f11d31b,
   0x401b0b46b00ff7d5,
   0x401b258b63007e5a,
   0x401b5c85864d61c1,
   0x401b91d7866a814e]

theorem record2684ChunkBits089Length2685 :
    (record2684ChunkBits0892685).length = 32 := by
  decide

theorem record2684ChunkSum0892685 :
    ((record2684ChunkBits0892685).map binary64Value2674).sum =
      (115966817780497269 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits0892685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2880 through 2911,
decoded and summed as exact rationals. -/
def record2684ChunkBits0902685 : List Nat :=
  [0x401bc524c3019c79,
   0x401bf61a5ae5c3d5,
   0x401c246e62038adc,
   0x401c4fe0d2eb3ac8,
   0x401c783c63b15749,
   0x401c9d573a414a80,
   0x401cbf1384481153,
   0x401cdd5fea01b62d,
   0x401cf837e669abbc,
   0x401d0fa3fe857e58,
   0x401d23b9d2e9b519,
   0x401d349c078c50dc,
   0x401d427a16138b2f,
   0x401d4d8fefc47004,
   0x401d56257a3a4db5,
   0x401d5e31b8058d87,
   0x401d83e65e897761,
   0x401da877cebef230,
   0x401dcb548c2514cc,
   0x401dec872c835fb7,
   0x401e0c3f0fbda8d1,
   0x401e2a2ea6786034,
   0x401e4720a748ccc7,
   0x401e834ec31a6358,
   0x401ebd9ad8a05433,
   0x401ef59fdc811a78,
   0x401f2b01a41533b1,
   0x401f5d6e0da1db64,
   0x401f8c9e1096ed2b,
   0x401fb856a49c3b90,
   0x401fe06991e36aed,
   0x4020025b01da6792]

theorem record2684ChunkBits090Length2685 :
    (record2684ChunkBits0902685).length = 32 := by
  decide

theorem record2684ChunkSum0902685 :
    ((record2684ChunkBits0902685).map binary64Value2674).sum =
      (267912492439407991 : ℚ) / 1125899906842624 := by
  norm_num [record2684ChunkBits0902685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2912 through 2943,
decoded and summed as exact rationals. -/
def record2684ChunkBits0912685 : List Nat :=
  [0x4020129485dd088e,
   0x402020df0e3f4b0c,
   0x40202d3f8b9fb7b3,
   0x402037c23d36e86d,
   0x4020407aa8c7e8c2,
   0x40204783824ac3ef,
   0x40204cfe93dc51ad,
   0x4020511401a5a3f2,
   0x402054aaab70b715,
   0x4020690a0d55b9d9,
   0x40207cc97a9586b1,
   0x40208f970341ce08,
   0x4020a18408105169,
   0x4020b29af6175253,
   0x4020c2b5078a3422,
   0x4020d215184e292b,
   0x4020f312d177a961,
   0x4021130527d5b1eb,
   0x402131b38f026e78,
   0x40214eea67775217,
   0x40216a7b95b451f2,
   0x4021843f3562863f,
   0x40219c142b00e624,
   0x4021b1e022bf23e0,
   0x4021c5903d911611,
   0x4021d7197122e6b2,
   0x4021e678b1018490,
   0x4021f3b2fc521916,
   0x4021fed592303d2f,
   0x402207f62baaa707,
   0x40220f3164a002b4,
   0x402214ac105a04d4]

theorem record2684ChunkBits091Length2685 :
    (record2684ChunkBits0912685).length = 32 := by
  decide

theorem record2684ChunkSum0912685 :
    ((record2684ChunkBits0912685).map binary64Value2674).sum =
      (153358129657012465 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits0912685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2944 through 2975,
decoded and summed as exact rationals. -/
def record2684ChunkBits0922685 : List Nat :=
  [0x402218945098582d,
   0x40221bc39d36495a,
   0x402231e4bcf168f3,
   0x40224757503264fb,
   0x40225bbf089f3828,
   0x40226f3b14f58cce,
   0x402281b6872c3d22,
   0x4022931358245460,
   0x4022a352156faf09,
   0x4022c6a5c321312e,
   0x4022e9c3c5b98508,
   0x40230b78d003e510,
   0x40232b8aae5d1e61,
   0x402349c5652e8bfe,
   0x402365fbd477f763,
   0x402380082e1f1e15,
   0x402397cc84e8bfcb,
   0x4023ad33506e46e1,
   0x4023c02f7b0da951,
   0x4023d0be2f05e322,
   0x4023dee4da34c4ef,
   0x4023eaafd662386c,
   0x4023f4366085bde8,
   0x4023fb98854f20e8,
   0x4024010394043436,
   0x402404c77a81a6c4,
   0x4024077a6bdc7335,
   0x40241facfe48781b,
   0x40243712de384859,
   0x40244d586eafaad3,
   0x402462bd5b86459d,
   0x402476f120c3bd5d]

theorem record2684ChunkBits092Length2685 :
    (record2684ChunkBits0922685).length = 32 := by
  decide

theorem record2684ChunkSum0922685 :
    ((record2684ChunkBits0922685).map binary64Value2674).sum =
      (174341028272929741 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits0922685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 2976 through 3007,
decoded and summed as exact rationals. -/
def record2684ChunkBits0932685 : List Nat :=
  [0x402489decf5416c4,
   0x40249b8509639c76,
   0x4024bfcc4132c650,
   0x4024e6e885a3a9e4,
   0x40250c78750fead8,
   0x4025303964ed3b4e,
   0x402551ef321ece31,
   0x402571657caec3b6,
   0x40258e6fdafd941c,
   0x4025a8eaacba870a,
   0x4025c0bebd816e05,
   0x4025d5d8d17fe610,
   0x4025e830d2e0903c,
   0x4025f7c988764025,
   0x402604b006e5e7be,
   0x40260efbbd7d68d6,
   0x402616dcb8df7e67,
   0x40261cca88acdf0e,
   0x402620b45ec87ab8,
   0x4026236545c9509d,
   0x40263e2179c257b1,
   0x4026582f7cd2cb23,
   0x402670d36aa7a49b,
   0x40268890e620e10d,
   0x40269f0cc4122b99,
   0x4026b403cbe05038,
   0x4026c770f99ce432,
   0x4026eaacdab138e1,
   0x402716fd995b9720,
   0x402741976feea98e,
   0x40276a2bb822323c,
   0x40279073a0eb3cf1]

theorem record2684ChunkBits093Length2685 :
    (record2684ChunkBits0932685).length = 32 := by
  decide

theorem record2684ChunkSum0932685 :
    ((record2684ChunkBits0932685).map binary64Value2674).sum =
      (12401224232863835 : ℚ) / 35184372088832 := by
  norm_num [record2684ChunkBits0932685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3008 through 3039,
decoded and summed as exact rationals. -/
def record2684ChunkBits0942685 : List Nat :=
  [0x4027b4330ad9f3b2,
   0x4027d53a49cc21cb,
   0x4027f3560025701f,
   0x40280e646ced5504,
   0x4028264f5a53d90f,
   0x40283b0a7cbd0e4a,
   0x40284c94e365eb0e,
   0x40285afa53db7fd6,
   0x402866732e892fe4,
   0x40286fcfaa5e0a71,
   0x4028769adf4d5457,
   0x40287aee278e9787,
   0x40287de3dbdb5b40,
   0x40289c1363a3b5c7,
   0x4028b9b8cfada43c,
   0x4028d5c0557d47b3,
   0x4028f069e9f05b18,
   0x4029097cf9661529,
   0x4029214f50a3cbec,
   0x4029373c6af83b88,
   0x40295691dc453b07,
   0x40298a539c60b576,
   0x4029bc2d7c09df4e,
   0x4029ebd10a6ac149,
   0x402a18e71307a6d3,
   0x402a4314e633c5ba,
   0x402a6a141c551ddd,
   0x402a8daa93094dd5,
   0x402aadaa7d34a6d3,
   0x402ac9f1fe90b3ff,
   0x402ae26d2978cd9b,
   0x402af712f096989d]

theorem record2684ChunkBits094Length2685 :
    (record2684ChunkBits0942685).length = 32 := by
  decide

theorem record2684ChunkSum0942685 :
    ((record2684ChunkBits0942685).map binary64Value2674).sum =
      (28306580543798851 : ℚ) / 70368744177664 := by
  norm_num [record2684ChunkBits0942685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3040 through 3071,
decoded and summed as exact rationals. -/
def record2684ChunkBits0952685 : List Nat :=
  [0x402b083a81b2f323,
   0x402b176e2d8f4a07,
   0x402b2366757b535e,
   0x402b2c11628fb2e9,
   0x402b31a4880c8661,
   0x402b359b81ae02eb,
   0x402b58eae3e62992,
   0x402b7bbc23f80855,
   0x402b9c8892e902a8,
   0x402bbb4572f81010,
   0x402bd7847e61dc4b,
   0x402bf1aba1848a3f,
   0x402c0abfad9fde04,
   0x402c221618cf610d,
   0x402c60b91912892d,
   0x402c9d3452ab812f,
   0x402cd7065f15ec10,
   0x402d0dbd785215a4,
   0x402d40f26c899782,
   0x402d704a43f8a57e,
   0x402d9b72ce4f0981,
   0x402dc22aec2c4e97,
   0x402de43f9b606620,
   0x402e01915a89c994,
   0x402e1ac6679da003,
   0x402e32d3da22f13a,
   0x402e46d8271e6c36,
   0x402e56753351f9d4,
   0x402e61ccc8110e37,
   0x402e69105e5835c0,
   0x402e6e54092ca15a,
   0x402e98970a819608]

theorem record2684ChunkBits095Length2685 :
    (record2684ChunkBits0952685).length = 32 := by
  decide

theorem record2684ChunkSum0952685 :
    ((record2684ChunkBits0952685).map binary64Value2674).sum =
      (259111906624862835 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits0952685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3072 through 3103,
decoded and summed as exact rationals. -/
def record2684ChunkBits0962685 : List Nat :=
  [0x402ec2452fa4e525,
   0x402ee920012b3080,
   0x402f0cf1ea12ba16,
   0x402f2d3acfb4cff4,
   0x402f49fdbb865378,
   0x402f63e7b5d62e57,
   0x402f7d7487127660,
   0x402fbe21ca8a0e56,
   0x40300514dd819609,
   0x40302974329d6e4c,
   0x40304be17ec5d59d,
   0x40306c251eb79fca,
   0x403089f31c7efb3b,
   0x4030a50fae5656a8,
   0x4030bd4afdcdd33d,
   0x4030d280dca1d717,
   0x4030e54ce300b938,
   0x4030f88671acd842,
   0x4031093944559ed5,
   0x403116f41a3d3c24,
   0x403121b03359538a,
   0x403129765b007483,
   0x40312e5f6f9a17d7,
   0x403131e0df0c7eed,
   0x40314bbcedcdd0d3,
   0x40316506a2dada59,
   0x40317c1e497378c6,
   0x403190e70bc25452,
   0x4031a3118da7a0ba,
   0x4031b26b1e03de99,
   0x4031beef7f0b54f0,
   0x4031c8cffb8b1d87]

theorem record2684ChunkBits096Length2685 :
    (record2684ChunkBits0962685).length = 32 := by
  decide

theorem record2684ChunkSum0962685 :
    ((record2684ChunkBits0962685).map binary64Value2674).sum =
      (150256311731945055 : ℚ) / 281474976710656 := by
  norm_num [record2684ChunkBits0962685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3104 through 3135,
decoded and summed as exact rationals. -/
def record2684ChunkBits0972685 : List Nat :=
  [0x4031ef4d97a89290,
   0x4032204b6315dc10,
   0x40324f0d4e265e15,
   0x40327b267b534d6a,
   0x4032a43310ba3486,
   0x4032c9d77811451f,
   0x4032ebcb1335837a,
   0x403309c7d6fe0389,
   0x4033250f7c449639,
   0x4033430f533f88c0,
   0x40335df113ff1231,
   0x403374d3d978a9b6,
   0x403387925ea1ca80,
   0x403396167b4c2c0b,
   0x4033a058edf5f99d,
   0x4033a665ef9e087b,
   0x4033aa50308e0376,
   0x4033c9e038474f5f,
   0x4033e8d946c5d0e4,
   0x403404561b6e698f,
   0x40341b9779a7f2b6,
   0x40342e7142466f2f,
   0x40343cc959e12c3f,
   0x4034469cd5f7cf21,
   0x403450d396a14a54,
   0x40348c2fc9399e0e,
   0x4034cb591320d0be,
   0x403508efa5d8484b,
   0x40354298d9f4ab20,
   0x403577cb5ac55340,
   0x4035a7fe4ea0e1c8,
   0x4035d2cb522bdc9f]

theorem record2684ChunkBits097Length2685 :
    (record2684ChunkBits0972685).length = 32 := by
  decide

theorem record2684ChunkSum0972685 :
    ((record2684ChunkBits0972685).map binary64Value2674).sum =
      (178158259862017801 : ℚ) / 281474976710656 := by
  norm_num [record2684ChunkBits0972685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3136 through 3167,
decoded and summed as exact rationals. -/
def record2684ChunkBits0982685 : List Nat :=
  [0x4035faa3b4b77335,
   0x4036292ed5f6fc45,
   0x403653b0fc557d96,
   0x40367894f434db79,
   0x4036978fb62395da,
   0x4036b05ccc0dfc91,
   0x4036c2fa1b805f4f,
   0x4036cf85333dd1ba,
   0x4036d61cc788426a,
   0x4036da26ba275383,
   0x403700d396eda3a7,
   0x4037252bbc640ec5,
   0x40374332a7f2f4b5,
   0x40375a52cef73ffe,
   0x40376a67fcda536d,
   0x403773507b1bcf38,
   0x40378055bafeff12,
   0x4037d2ad16ae07b8,
   0x40381f32d82015c9,
   0x40386567c1671c7e,
   0x4038b1b50642e8cd,
   0x4038fd2ce65d1c05,
   0x4039419e9e657276,
   0x40397e5aaa8fa1e4,
   0x4039b83be2a26c66,
   0x403a005a3a4d4b61,
   0x403a431adb71a4e0,
   0x403a7dc7ca32fb85,
   0x403aafcf5e4ddbaa,
   0x403ad8c4ac3ffadc,
   0x403af84c51591c4d,
   0x403b0f7e80f36f89]

theorem record2684ChunkBits098Length2685 :
    (record2684ChunkBits0982685).length = 32 := by
  decide

theorem record2684ChunkSum0982685 :
    ((record2684ChunkBits0982685).map binary64Value2674).sum =
      (217699270671874163 : ℚ) / 281474976710656 := by
  norm_num [record2684ChunkBits0982685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3168 through 3199,
decoded and summed as exact rationals. -/
def record2684ChunkBits0992685 : List Nat :=
  [0x403b1dc9c31ca755,
   0x403b227f46ad349e,
   0x403b21ef452cc487,
   0x403b4ccc28a834a9,
   0x403b73a20c083537,
   0x403b9045e9697173,
   0x403ba1f7d8dc80a5,
   0x403ba88ac71d5fba,
   0x403c269307f902a3,
   0x403c9d36f76bd739,
   0x403d0aa852f8b463,
   0x403d6dc64e1075c2,
   0x403dc58762bfb6be,
   0x403e118e1c49a04c,
   0x403e66e816ea81a5,
   0x403ebee646e4433f,
   0x403f146b06bb799d,
   0x403f8462881b2f66,
   0x403fecc34acf1e12,
   0x4040249c2c690c94,
   0x40404c75b6279300,
   0x40406ddd197e9e9c,
   0x40408997bced7d83,
   0x40409e344b23a91a,
   0x4040ab72aa2934e2,
   0x4040b193816644b5,
   0x4040b03da5b44e85,
   0x4040aa4c236d998f,
   0x4040bedbcd23435a,
   0x4040ced4d6ef1890,
   0x4041126abaa0b220,
   0x404172b0ecda50bc]

theorem record2684ChunkBits099Length2685 :
    (record2684ChunkBits0992685).length = 32 := by
  decide

theorem record2684ChunkSum0992685 :
    ((record2684ChunkBits0992685).map binary64Value2674).sum =
      (69198394499605355 : ℚ) / 70368744177664 := by
  norm_num [record2684ChunkBits0992685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3200 through 3231,
decoded and summed as exact rationals. -/
def record2684ChunkBits1002685 : List Nat :=
  [0x4041cd4447c512e7,
   0x40422145c58648bc,
   0x40426e7233680ff3,
   0x4042b3f3feeb86d0,
   0x4042f0cef8df8ee6,
   0x4043246eeea3a666,
   0x40434e7069eb724d,
   0x40436ee0e82f63ef,
   0x40439eafe61213e2,
   0x4043f5e82ca27f27,
   0x404447f5cd9601e7,
   0x40449137c96d4486,
   0x4044d1da561a495a,
   0x40450a5fe0c3a35f,
   0x4045385fd4c9cfc4,
   0x40455b7076b14e16,
   0x40457344587ebf34,
   0x40457fecf8e5d180,
   0x4045814a65e33582,
   0x404577740659b1a0,
   0x4045c39bb99745ec,
   0x404658b329603ea3,
   0x4046ecb96a6a9305,
   0x404778579516f54f,
   0x4047fa501758582e,
   0x404872317219461e,
   0x4048dea7148dcf2e,
   0x40493e94b3db5f18,
   0x404991495ad985c4,
   0x4049d6218a122319,
   0x404a0c6dfb356e98,
   0x404a34002ce23b0e]

theorem record2684ChunkBits100Length2685 :
    (record2684ChunkBits1002685).length = 32 := by
  decide

theorem record2684ChunkSum1002685 :
    ((record2684ChunkBits1002685).map binary64Value2674).sum =
      (195167942366102981 : ℚ) / 140737488355328 := by
  norm_num [record2684ChunkBits1002685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3232 through 3263,
decoded and summed as exact rationals. -/
def record2684ChunkBits1012685 : List Nat :=
  [0x404a5b63a3d762f1,
   0x404aa79b78897bf0,
   0x404b02b702782ba1,
   0x404b71a8d36b0978,
   0x404bd4eb25fef884,
   0x404c29c5565706f9,
   0x404c6f5698a1fcfb,
   0x404ca4dd0888442b,
   0x404cc9fb7d26d509,
   0x404cdea8e9d3d761,
   0x404d664db273b049,
   0x404e16782352d09f,
   0x404eb9bac32bbcba,
   0x404f52f09860808a,
   0x40500f8fdfadc3a4,
   0x405073ef4dba804f,
   0x4050d116a540a3e2,
   0x405126254263f608,
   0x40517250b6326821,
   0x4051b4fab370f5c4,
   0x4051edbf01ab3eb3,
   0x40521c4b2941ad24,
   0x4052402c264d6bf6,
   0x40525932d5f9e6c4,
   0x4052720b8558618c,
   0x4052a8232bf4a254,
   0x4052da36b360ed5b,
   0x405301caf9006a55,
   0x40532d7f30b91255,
   0x405369a1fa73caee,
   0x40539c700b00b5f9,
   0x4053c3824fc55671]

theorem record2684ChunkBits101Length2685 :
    (record2684ChunkBits1012685).length = 32 := by
  decide

theorem record2684ChunkSum1012685 :
    ((record2684ChunkBits1012685).map binary64Value2674).sum =
      (296711732814757459 : ℚ) / 140737488355328 := by
  norm_num [record2684ChunkBits1012685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3264 through 3295,
decoded and summed as exact rationals. -/
def record2684ChunkBits1022685 : List Nat :=
  [0x4053f5cf15c326e3,
   0x405485b0cd8fe4a5,
   0x40550d07faaa21a4,
   0x40558ae1cf20dfac,
   0x4055fe864c747ed6,
   0x405666e9b55b9355,
   0x4056c6819a1c01c9,
   0x405749a31604a2d8,
   0x4057ca21513e2a06,
   0x40583edc8b96e716,
   0x4058a6dc99c867c8,
   0x405901345d2eb8d3,
   0x40594d35971d8f0e,
   0x40598a6f6d69d42b,
   0x4059b8abdbc489ff,
   0x4059d7e26523f9a9,
   0x4059fa415d77f2d5,
   0x405a4c3c0d938943,
   0x405a93540c9a8534,
   0x405aca597d06a6af,
   0x405af0d1bea6f5d6,
   0x405b067f1e10543e,
   0x405b1c132a6b9845,
   0x405b502946642982,
   0x405c19ef82fd5622,
   0x405ce31689cdbcd3,
   0x405da077953d86be,
   0x405e50b3c2e10c69,
   0x405ef3105a134728,
   0x405f84df7720f077,
   0x4060026c77811c94,
   0x40603b331252aa12]

theorem record2684ChunkBits102Length2685 :
    (record2684ChunkBits1022685).length = 32 := by
  decide

theorem record2684ChunkSum1022685 :
    ((record2684ChunkBits1022685).map binary64Value2674).sum =
      (234058920086469401 : ℚ) / 70368744177664 := by
  norm_num [record2684ChunkBits1022685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3296 through 3327,
decoded and summed as exact rationals. -/
def record2684ChunkBits1032685 : List Nat :=
  [0x40608bcb52f583bd,
   0x4060da18964376ce,
   0x40611f48048b39f4,
   0x40615b183c411b58,
   0x40618cdb41df6bf5,
   0x4061b417a910af12,
   0x4061d1159c0e8e9b,
   0x4061e5f8753d65cd,
   0x4061fe68ab743815,
   0x4062380fff4402f4,
   0x40626a279d0686ac,
   0x4062911d692606f4,
   0x4062acd10850a4af,
   0x4062bc5cd1273ff7,
   0x4062bf9056186f61,
   0x4062b66f3e66b605,
   0x40631715ca90b934,
   0x4063a1919feb185b,
   0x4064247df125584c,
   0x40649dc0b2c5def7,
   0x40650c9284e75d67,
   0x40656fe0fcbc466c,
   0x4065c71cfbb00c11,
   0x406611d7f96d5a5b,
   0x4066521b2c6b2531,
   0x4066b44c3fb3cb09,
   0x4067154d4ffa8b2a,
   0x40676939b408b0ce,
   0x4067af4fa4a0f86d,
   0x4067e764e47c3d51,
   0x4068154b80663213,
   0x40683515cc400ee8]

theorem record2684ChunkBits103Length2685 :
    (record2684ChunkBits1032685).length = 32 := by
  decide

theorem record2684ChunkSum1032685 :
    ((record2684ChunkBits1032685).map binary64Value2674).sum =
      (180178632867244023 : ℚ) / 35184372088832 := by
  norm_num [record2684ChunkBits1032685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3328 through 3359,
decoded and summed as exact rationals. -/
def record2684ChunkBits1042685 : List Nat :=
  [0x40685990837120c3,
   0x4068aed5ba62edf0,
   0x4068f8eb1ce6327d,
   0x40693306b2879a07,
   0x40695c630ccb3951,
   0x4069748e5f393416,
   0x40697b38f5bec4e6,
   0x4069705dca46d1c1,
   0x406976cde6ba73b7,
   0x4069ecf898b4950b,
   0x406a59987cc76d7d,
   0x406afe447253f44e,
   0x406b998e53c0b48c,
   0x406c25cbe453a464,
   0x406ca21145fa3993,
   0x406d0cf51cf7e8b8,
   0x406d6580fddc88d5,
   0x406daea47abb0d12,
   0x406e24c67e9751d9,
   0x406e98bde000b3c1,
   0x406efd32eb4b94a3,
   0x406f541fa1f2d0b8,
   0x406f97a8de526270,
   0x406fc95cab7ce5c8,
   0x407002b6eb5ee33a,
   0x4070446945c3bd2f,
   0x40707f0a81641942,
   0x4070aefcd8a8504c,
   0x4070d35a26aa50c3,
   0x4070ebc85f9522f0,
   0x4070f7f6639c0920,
   0x4070f78687a3da62]

theorem record2684ChunkBits104Length2685 :
    (record2684ChunkBits1042685).length = 32 := by
  decide

theorem record2684ChunkSum1042685 :
    ((record2684ChunkBits1042685).map binary64Value2674).sum =
      (262025114943934585 : ℚ) / 35184372088832 := by
  norm_num [record2684ChunkBits1042685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3360 through 3391,
decoded and summed as exact rationals. -/
def record2684ChunkBits1052685 : List Nat :=
  [0x4070ea827d896ba5,
   0x4070da42bd92dc9b,
   0x407122c4542c6a0f,
   0x40715fb74a4e1466,
   0x407193d280b2b3d2,
   0x4071ebb666d0a296,
   0x4072415db8ca60da,
   0x40728bd2f5b3ac98,
   0x4072ca299e00ca85,
   0x4072fbd5a4b3c3d0,
   0x40732333e0deca2c,
   0x40736d53b976a396,
   0x4073b89dcd6ec9de,
   0x4073f7de7c84f038,
   0x40742abb40db2f15,
   0x40744fe731d792d7,
   0x40747cf0cdfbde7a,
   0x4074dc8ad1635618,
   0x4075315ff07d4519,
   0x4075772514ce6494,
   0x4075ad569291e02e,
   0x4075d5058a05698e,
   0x4075ebc0d7860252,
   0x4075f136384b516d,
   0x4075e4ffa1fc70b4,
   0x4075c6e64982aa4d,
   0x4075a0ab40399736,
   0x4075f4011f8848ac,
   0x407636d1a42ebc07,
   0x4076683272f54bdc,
   0x40768ac4f4cf9179,
   0x4076d99208d367e7]

theorem record2684ChunkBits105Length2685 :
    (record2684ChunkBits1052685).length = 32 := by
  decide

theorem record2684ChunkSum1052685 :
    ((record2684ChunkBits1052685).map binary64Value2674).sum =
      (22719604561052497 : ℚ) / 2199023255552 := by
  norm_num [record2684ChunkBits1052685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3392 through 3423,
decoded and summed as exact rationals. -/
def record2684ChunkBits1062685 : List Nat :=
  [0x40772cc962acd555,
   0x40776f534a1efd42,
   0x4077a68f62af6312,
   0x4077cf09a4df7885,
   0x40782333fe38f5ab,
   0x4078779886ea6b33,
   0x4078ba91e8d77832,
   0x4078eb63afe5c06a,
   0x4079298aa363907e,
   0x4079aee15bceedc7,
   0x407a2698de432b87,
   0x407a8abc85f86aa0,
   0x407ad9ec1e435fda,
   0x407b1346edbcdf92,
   0x407b36ff24117991,
   0x407b4396efc0ebc5,
   0x407b384a1d64096f,
   0x407b1506ab20e1ba,
   0x407ada08614ad49f,
   0x407ae0805c5298c8,
   0x407b2dfc01d9674d,
   0x407b639b948becd0,
   0x407b808c7fbd5a0f,
   0x407b8438b82af9e9,
   0x407b73b30b137396,
   0x407b9dbe7e073631,
   0x407bdb0da4a5345d,
   0x407c0266cc155b92,
   0x407c14f926d90699,
   0x407c65b3ab899d48,
   0x407cbb2f56566773,
   0x407cfad19a6754c0]

theorem record2684ChunkBits106Length2685 :
    (record2684ChunkBits1062685).length = 32 := by
  decide

theorem record2684ChunkSum1062685 :
    ((record2684ChunkBits1062685).map binary64Value2674).sum =
      (238411282684943173 : ℚ) / 17592186044416 := by
  norm_num [record2684ChunkBits1062685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3424 through 3455,
decoded and summed as exact rationals. -/
def record2684ChunkBits1072685 : List Nat :=
  [0x407d4ee0a3d52854,
   0x407e02acd0639d5b,
   0x407ea5794a6cd0bf,
   0x407f2f59bc278854,
   0x407f9f2823bf46ef,
   0x407ff491e50adcc6,
   0x4080170fcd580488,
   0x4080255d8ca11ce6,
   0x408024e1f2805c49,
   0x408015cf71566e94,
   0x407fefdd987d8b60,
   0x407fd5bca06335af,
   0x4080127d06a02711,
   0x40802a7f52fb3b30,
   0x408032ae1ffdb98e,
   0x40802e9ca8b49c50,
   0x40801d2e0054f354,
   0x407ff92554f96abc,
   0x407f9784aaa01657,
   0x407f70caddee8c6b,
   0x407f73981bc59a8e,
   0x407f5cc2deecbec0,
   0x407fa057230d72a3,
   0x407fefefd7c8c7e4,
   0x408030959bec4a4e,
   0x4080a9f05df4dc74,
   0x4081193bbe46acb4,
   0x40817be937e45cc9,
   0x4081d0277bddfc05,
   0x40821571657a872b,
   0x40824ac33ed1760c,
   0x40826fa6c9c9b11a]

theorem record2684ChunkBits107Length2685 :
    (record2684ChunkBits1072685).length = 32 := by
  decide

theorem record2684ChunkSum1072685 :
    ((record2684ChunkBits1072685).map binary64Value2674).sum =
      (292846465341819263 : ℚ) / 17592186044416 := by
  norm_num [record2684ChunkBits1072685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3456 through 3487,
decoded and summed as exact rationals. -/
def record2684ChunkBits1082685 : List Nat :=
  [0x408283d34a285267,
   0x4082871023041add,
   0x4082796d1abbaf1a,
   0x4082800a959f25e9,
   0x4082a647568e22e4,
   0x4082b9c4d7eecb66,
   0x4082c1549e13d0a1,
   0x4082b5b75461895a,
   0x408295bfd01e547c,
   0x408261dd9d37f7f7,
   0x40821a1df848017f,
   0x4081be9d969bb93a,
   0x40814f5fba7bba6c,
   0x4080fc97b1944515,
   0x4080d8c3b185dbb2,
   0x4080f87a8ee92016,
   0x40814d2616eefb78,
   0x4081f87660a6263a,
   0x408299ba3a76d777,
   0x40832bf9a4ab4ee6,
   0x4083ae6cfeb4b45e,
   0x4084206052931826,
   0x40848173bdfdccbd,
   0x4084d0f4a036ef5c,
   0x40850e52e04ae26f,
   0x4085393335b9c91a,
   0x408561037c5fa21e,
   0x40859d57827009c9,
   0x4085c7f435e18aaa,
   0x4085e4400eb08984,
   0x4085e976c3e34031,
   0x4085d71353e3c128]

theorem record2684ChunkBits108Length2685 :
    (record2684ChunkBits1082685).length = 32 := by
  decide

theorem record2684ChunkSum1082685 :
    ((record2684ChunkBits1082685).map binary64Value2674).sum =
      (43393368174424745 : ℚ) / 2199023255552 := by
  norm_num [record2684ChunkBits1082685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3488 through 3519,
decoded and summed as exact rationals. -/
def record2684ChunkBits1092685 : List Nat :=
  [0x4085aca679c9d6b3,
   0x408569bb98bf7e1b,
   0x40850e595aadc82e,
   0x40849a5603746cd0,
   0x40840dd31026aac3,
   0x408369b222fe7ce7,
   0x4082ae2b587a7f7d,
   0x40820d45fb919340,
   0x40825c61e1acf009,
   0x40834777ec32795a,
   0x40842953623ee156,
   0x4085096cb66a6e16,
   0x4085f212bc6bbee9,
   0x4086c8de2f3f7c28,
   0x40878a2184861b11,
   0x408835cb23fea274,
   0x4088cac69b36c602,
   0x40894df92df50d1b,
   0x4089e0d6fcca8c6a,
   0x408a61fe72276c23,
   0x408acc9184e58a06,
   0x408b1ac01afc9372,
   0x408b4b6a99be2dc7,
   0x408b5e48edbe169e,
   0x408b524719f6a575,
   0x408b26e506912876,
   0x408adb253526c4ac,
   0x408a6fede75411e2,
   0x408a103a82bbedcc,
   0x4089958449c422ea,
   0x4088fe912c3366f7,
   0x40884aa35396584e]

theorem record2684ChunkBits109Length2685 :
    (record2684ChunkBits1092685).length = 32 := by
  decide

theorem record2684ChunkSum1092685 :
    ((record2684ChunkBits1092685).map binary64Value2674).sum =
      (211637624599615379 : ℚ) / 8796093022208 := by
  norm_num [record2684ChunkBits1092685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3520 through 3551,
decoded and summed as exact rationals. -/
def record2684ChunkBits1102685 : List Nat :=
  [0x4087d9fadf5c8f70,
   0x40889440b850beca,
   0x408a0abf4c538e59,
   0x408b777f02afa053,
   0x408cd1dc3f026825,
   0x408e1586139dd0a0,
   0x408f3fe0549d96af,
   0x40902751ccf79a60,
   0x4090a017e15abf20,
   0x40910a1ff5f65bed,
   0x40916dc084e22bb0,
   0x4091c1744a42012f,
   0x409204305d64713a,
   0x409234a4a706ed24,
   0x409252ac0ce3e685,
   0x40925d4d18cc7556,
   0x409254254d3c1f36,
   0x40923f284084a472,
   0x409234673bf222b2,
   0x40921729189d9555,
   0x4091e7ba77829710,
   0x4091a559c554914e,
   0x40914f88ae42fe7d,
   0x4090e64b9287515c,
   0x4090a4099d122074,
   0x4090af313b68e927,
   0x409110e769fdaf35,
   0x40918df19decbd72,
   0x409266c9ff45c730,
   0x4093382d72f0dcb8,
   0x4093f9bd886da1ac,
   0x4094aa619666715a]

theorem record2684ChunkBits110Length2685 :
    (record2684ChunkBits1102685).length = 32 := by
  decide

theorem record2684ChunkSum1102685 :
    ((record2684ChunkBits1102685).map binary64Value2674).sum =
      (19098016455343225 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1102685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3552 through 3583,
decoded and summed as exact rationals. -/
def record2684ChunkBits1112685 : List Nat :=
  [0x40954c9496db891b,
   0x4095e1f5e91d8279,
   0x4096633ced1f9d50,
   0x4096cf829e3234de,
   0x409725b121c9715a,
   0x4097655a89128fab,
   0x40978e5dd492347c,
   0x4097a03201c4011b,
   0x40979d068a2f2924,
   0x40978118fc6c0514,
   0x409777c7abbf92c4,
   0x409761706f452460,
   0x4097352be19b1760,
   0x4096f17b54a90c63,
   0x409694f9f9ecf435,
   0x409620393efffb04,
   0x4095d9c18a45865e,
   0x4095ebc645e20123,
   0x4095ec901baf4194,
   0x40965ed48320be43,
   0x4096f1e4d30ead9c,
   0x4097717d89aaabb7,
   0x409853b5ec069301,
   0x40994114553b352d,
   0x409a1c5cd1c7eb05,
   0x409ae0d115365ebe,
   0x409b8d7255e997e4,
   0x409c20aded2058b1,
   0x409c9b8a6f4de057,
   0x409cfb520ee4ba68,
   0x409d3eb53682d6e2,
   0x409d65c80f21e40c]

theorem record2684ChunkBits111Length2685 :
    (record2684ChunkBits1112685).length = 32 := by
  decide

theorem record2684ChunkSum1112685 :
    ((record2684ChunkBits1112685).map binary64Value2674).sum =
      (54596757321421157 : ℚ) / 1099511627776 := by
  norm_num [record2684ChunkBits1112685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3584 through 3615,
decoded and summed as exact rationals. -/
def record2684ChunkBits1122685 : List Nat :=
  [0x409d71476d9ec291,
   0x409d5f8407b702c0,
   0x409d2feb3dbc6810,
   0x409d1dab3db971f1,
   0x409cf1bc397c53e7,
   0x409ca8d5fb3adba7,
   0x409c44a03c9dd204,
   0x409bc1e0a16e3463,
   0x409b78885f9446c4,
   0x409b98c74d292af6,
   0x409b9d0260825047,
   0x409b8a124e049026,
   0x409c0c9ddea17fc5,
   0x409cbdd89f71fee1,
   0x409d62fc65991497,
   0x409def539d1a9d09,
   0x409ee0141e08ccd1,
   0x409fe67a06487a1d,
   0x40a06844a68ab347,
   0x40a0cee5eba73845,
   0x40a1266664c4d883,
   0x40a16de649d98707,
   0x40a1a52773f79eae,
   0x40a1cb37404293bf,
   0x40a1dfb01fd83cb7,
   0x40a1e2a25b45ab5c,
   0x40a1d39570f31e19,
   0x40a1b221f1a9f652,
   0x40a19f9769243122,
   0x40a17baf18b41625,
   0x40a145b8ff6c4020,
   0x40a0fd7448105197]

theorem record2684ChunkBits112Length2685 :
    (record2684ChunkBits1122685).length = 32 := by
  decide

theorem record2684ChunkSum1122685 :
    ((record2684ChunkBits1122685).map binary64Value2674).sum =
      (8863157491663397 : ℚ) / 137438953472 := by
  norm_num [record2684ChunkBits1122685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3616 through 3647,
decoded and summed as exact rationals. -/
def record2684ChunkBits1132685 : List Nat :=
  [0x40a0d74f82c2641b,
   0x40a0efb7919a9e71,
   0x40a0f70540be5a81,
   0x40a0edf895225b61,
   0x40a0dbba65219a4e,
   0x40a12ebe8fc05cdd,
   0x40a1a14eaab5dd45,
   0x40a204bc8f9df505,
   0x40a257b439bffefd,
   0x40a299fc1e9e47e0,
   0x40a30bec7a732af3,
   0x40a3966d36868d75,
   0x40a40f7e8065c993,
   0x40a4769a477eac12,
   0x40a4ca8ac3b80b50,
   0x40a50a9990c53d53,
   0x40a53623565d3d70,
   0x40a54dbdb79a5c96,
   0x40a550592049d400,
   0x40a53dc03a79b474,
   0x40a5218be628954e,
   0x40a5021ac512f0d7,
   0x40a4cca0558567ac,
   0x40a481059c3d41ab,
   0x40a45dbc5cb8f3e9,
   0x40a48245c962d29c,
   0x40a492aa68fc7ca1,
   0x40a495d0f66b32fa,
   0x40a487c36506481c,
   0x40a46a28d51b11bb,
   0x40a4c5cf341b0d95,
   0x40a54c55c95c0654]

theorem record2684ChunkBits113Length2685 :
    (record2684ChunkBits1132685).length = 32 := by
  decide

theorem record2684ChunkSum1132685 :
    ((record2684ChunkBits1132685).map binary64Value2674).sum =
      (88503895709530787 : ℚ) / 1099511627776 := by
  norm_num [record2684ChunkBits1132685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3648 through 3679,
decoded and summed as exact rationals. -/
def record2684ChunkBits1142685 : List Nat :=
  [0x40a5bf7e6c7bb99f,
   0x40a6211b991389d4,
   0x40a66fa596be9eaf,
   0x40a6a958090c0cbd,
   0x40a70bdf2ad8d691,
   0x40a7985d08b25b03,
   0x40a80efa479adfba,
   0x40a86f2705e2c746,
   0x40a8b7d4515ee50a,
   0x40a8e8691a2cd0e7,
   0x40a9006b6faea70d,
   0x40a8ffb7d46a53d7,
   0x40a8f73ffe896a91,
   0x40a8e0f1ce7716c6,
   0x40a8b190a6656461,
   0x40a8690189a5dbc4,
   0x40a85063dd40ed53,
   0x40a88b55ec856485,
   0x40a8b946fa452cae,
   0x40a8cf2ee3ae8c65,
   0x40a8cb8163e8f373,
   0x40a8ade1c50a1ef5,
   0x40a87bdcca26430a,
   0x40a8e0aed3a83e05,
   0x40a97d610411f477,
   0x40aa02cb90a7208b,
   0x40aa7021aa68edf1,
   0x40aac47327fdcebb,
   0x40aaff5d49094418,
   0x40ab22894f8079f1,
   0x40ab644be7b93289,
   0x40abe8c6682808bf]

theorem record2684ChunkBits114Length2685 :
    (record2684ChunkBits1142685).length = 32 := by
  decide

theorem record2684ChunkSum1142685 :
    ((record2684ChunkBits1142685).map binary64Value2674).sum =
      (223505367464256293 : ℚ) / 2199023255552 := by
  norm_num [record2684ChunkBits1142685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3680 through 3711,
decoded and summed as exact rationals. -/
def record2684ChunkBits1152685 : List Nat :=
  [0x40ac548768e1a7ff,
   0x40aca4eadb3a50c0,
   0x40acda665d37da9c,
   0x40ad03428efae9a2,
   0x40ad1a9eb63d75a8,
   0x40ad145272652440,
   0x40acf0282ca2e25e,
   0x40acaee83269f398,
   0x40acabb2a665e336,
   0x40ad0fcc70a2e83a,
   0x40ad57c11875822b,
   0x40ad821f85d7ae7a,
   0x40ad8e57e9d934c3,
   0x40ad7caa1d20458b,
   0x40ad4c49608dc31f,
   0x40ad02c9cec5045f,
   0x40ad70a7e96f8e2d,
   0x40ae268e2b3d630d,
   0x40aec0890d75b1d5,
   0x40af3e2465f0d5a7,
   0x40af9e8f93c87dfd,
   0x40afe12db0f3fc39,
   0x40b00361426875eb,
   0x40b0065dac996158,
   0x40b0117922e2ee31,
   0x40b04898ca20fd9a,
   0x40b0770ed6e2d479,
   0x40b09c781a7d0533,
   0x40b0b235c754f04e,
   0x40b0baa48181cec8,
   0x40b0b2afe17be702,
   0x40b09edec8149e18]

theorem record2684ChunkBits115Length2685 :
    (record2684ChunkBits1152685).length = 32 := by
  decide

theorem record2684ChunkSum1152685 :
    ((record2684ChunkBits1152685).map binary64Value2674).sum =
      (68826597448386527 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1152685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3712 through 3743,
decoded and summed as exact rationals. -/
def record2684ChunkBits1162685 : List Nat :=
  [0x40b0ad62337a8fde,
   0x40b0f080ddac6d92,
   0x40b123a0f7c7ccc7,
   0x40b146117db628e0,
   0x40b157e1dfc8eb1f,
   0x40b1586806b04fe2,
   0x40b14740a8127edc,
   0x40b12435a7d069ae,
   0x40b0f28e87daabdc,
   0x40b12e993e80b29e,
   0x40b198942a8d7fde,
   0x40b1f288fb91b961,
   0x40b23ba354ec96b4,
   0x40b273e5c8202b72,
   0x40b29b00f58ca3a0,
   0x40b2b0162ba70df7,
   0x40b2b340023f9f84,
   0x40b2a43af398cfd2,
   0x40b29770d667026c,
   0x40b2cd2f8bdbc6a2,
   0x40b2f35fe6ce20c3,
   0x40b307c3e429fbee,
   0x40b310dc3d0b74bd,
   0x40b306d2c709e228,
   0x40b321849836e213,
   0x40b37666ac227d4f,
   0x40b3b966155507ab,
   0x40b3eb2ec92e1598,
   0x40b409527d36ddd7,
   0x40b414e6a71665a5,
   0x40b40e189ec4d8b5,
   0x40b3f31cc21f8aae]

theorem record2684ChunkBits116Length2685 :
    (record2684ChunkBits1162685).length = 32 := by
  decide

theorem record2684ChunkSum1162685 :
    ((record2684ChunkBits1162685).map binary64Value2674).sum =
      (83029121742502091 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1162685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3744 through 3775,
decoded and summed as exact rationals. -/
def record2684ChunkBits1172685 : List Nat :=
  [0x40b3c42eb43afc6a,
   0x40b3846bc11afd25,
   0x40b3c4fb33e76b3c,
   0x40b43d9269eaadff,
   0x40b4a3a767977bd1,
   0x40b4f7d9167b8a92,
   0x40b5388138bd6307,
   0x40b56533e48b03a0,
   0x40b57d46f2838819,
   0x40b580716eb69f51,
   0x40b56e4c5eabdc9e,
   0x40b548c896d9eb62,
   0x40b5205e1ec420a3,
   0x40b54b8b874c1464,
   0x40b565c87b983e34,
   0x40b56ab5eb0cab76,
   0x40b59982085544af,
   0x40b60942de11ac0e,
   0x40b6647b575c0b14,
   0x40b6aa8d76bad8a0,
   0x40b6da67f2bfffeb,
   0x40b6f413bd159f70,
   0x40b6f7d14846a32c,
   0x40b6e45cd92d964a,
   0x40b6baf776741245,
   0x40b67ca7685b4c49,
   0x40b62afa78974f70,
   0x40b66c7d58aa1239,
   0x40b6f20e057547c2,
   0x40b762c0ac2d3327,
   0x40b7bf42340f07b2,
   0x40b805704b1c0421]

theorem record2684ChunkBits117Length2685 :
    (record2684ChunkBits1172685).length = 32 := by
  decide

theorem record2684ChunkSum1172685 :
    ((record2684ChunkBits1172685).map binary64Value2674).sum =
      (49168685178790025 : ℚ) / 274877906944 := by
  norm_num [record2684ChunkBits1172685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3776 through 3807,
decoded and summed as exact rationals. -/
def record2684ChunkBits1182685 : List Nat :=
  [0x40b83485c8d21628,
   0x40b84c9b22d36a7e,
   0x40b84d57f9883e40,
   0x40b83dfcd011287c,
   0x40b819d637ba77a3,
   0x40b7df09c1587978,
   0x40b7967f6918c991,
   0x40b7a42f53a5661c,
   0x40b7ecc08320c182,
   0x40b87b6522308e3c,
   0x40b8f33f67754ed1,
   0x40b9533e7b41fcf1,
   0x40b99aa7451e019c,
   0x40b9c975cb820723,
   0x40b9dfe9e0766080,
   0x40b9dccc869577db,
   0x40b9bfb4a91937ce,
   0x40b98888fe88ff0c,
   0x40b9375980c992e5,
   0x40b8d03dd706280f,
   0x40b90f00a9e70a0e,
   0x40b99e4ccad59ac6,
   0x40ba1832d0d18449,
   0x40ba7bb7b1e61f12,
   0x40bac7dae78d5fd7,
   0x40bafc9ec8ab41eb,
   0x40bb21899070aca7,
   0x40bb2c2d0d86b9a0,
   0x40bb1c86dc18556c,
   0x40baf2112f66e334,
   0x40baaefaafe3a1aa,
   0x40ba515a4789ed9c]

theorem record2684ChunkBits118Length2685 :
    (record2684ChunkBits1182685).length = 32 := by
  decide

theorem record2684ChunkSum1182685 :
    ((record2684ChunkBits1182685).map binary64Value2674).sum =
      (14315754592434411 : ℚ) / 68719476736 := by
  norm_num [record2684ChunkBits1182685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3808 through 3839,
decoded and summed as exact rationals. -/
def record2684ChunkBits1192685 : List Nat :=
  [0x40ba28307253dc48,
   0x40bab83478a405d5,
   0x40bb4cab3850c7a5,
   0x40bbc798a8417afb,
   0x40bc2841a3683c0a,
   0x40bc6e4cc525bfd9,
   0x40bc99267b177f54,
   0x40bca878c537ec49,
   0x40bc9bc95d3a2dea,
   0x40bc72bada88fc22,
   0x40bc2e33cf9440b9,
   0x40bbce191d9f6d97,
   0x40bb56b195d837b8,
   0x40bb974410c3889d,
   0x40bc3638e7826972,
   0x40bcbacc117aea94,
   0x40bd29fbb79c0c4b,
   0x40bd84cb7421d9dc,
   0x40bdc33f86861198,
   0x40bde4ec37ffeef7,
   0x40bdeca8a8d35262,
   0x40bdd82b3cda5d27,
   0x40bda6a6d9f29e83,
   0x40bd588559dbef49,
   0x40bd395bdbded16d,
   0x40bd75283c867fb7,
   0x40bd97ddf807a232,
   0x40bdff77d3165b97,
   0x40be7a3330b8dca5,
   0x40bed8e13b3a9d62,
   0x40bf1be576d5f26b,
   0x40bf41af87eaa556]

theorem record2684ChunkBits119Length2685 :
    (record2684ChunkBits1192685).length = 32 := by
  decide

theorem record2684ChunkSum1192685 :
    ((record2684ChunkBits1192685).map binary64Value2674).sum =
      (65146090298261357 : ℚ) / 274877906944 := by
  norm_num [record2684ChunkBits1192685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3840 through 3871,
decoded and summed as exact rationals. -/
def record2684ChunkBits1202685 : List Nat :=
  [0x40bf4a615c7847cf,
   0x40bf346d2209c3f7,
   0x40bf000704dcc072,
   0x40beacedb0139638,
   0x40be3b41f61468a4,
   0x40bdaedf78a6385c,
   0x40bde9c17c0cbf2d,
   0x40be9a8b08b25807,
   0x40bf337e6f69603b,
   0x40bfaf78f20ca574,
   0x40c006bac7f85dae,
   0x40c026dbb2d585c5,
   0x40c03771373e66a5,
   0x40c0389625d21584,
   0x40c02a1f05b3d4d5,
   0x40c00c5d1e64c450,
   0x40c00b7d276a0a8c,
   0x40c03505da84c972,
   0x40c05233bb423b9c,
   0x40c06105cd76b410,
   0x40c061bb4a986936,
   0x40c07db90c82b77c,
   0x40c0ac055fb7c673,
   0x40c0ca78ccfa0553,
   0x40c0d94bc959585f,
   0x40c0d98fcb608a91,
   0x40c0c967e8bcb88d,
   0x40c0a8ec5ad2cbe9,
   0x40c0782d43d5d4f6,
   0x40c0380c298e31b8,
   0x40bfdf547ae11103,
   0x40c0096057b4460d]

theorem record2684ChunkBits120Length2685 :
    (record2684ChunkBits1202685).length = 32 := by
  decide

theorem record2684ChunkSum1202685 :
    ((record2684ChunkBits1202685).map binary64Value2674).sum =
      (144584478372591023 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1202685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3872 through 3903,
decoded and summed as exact rationals. -/
def record2684ChunkBits1212685 : List Nat :=
  [0x40c069cf4f484015,
   0x40c0bab0cb8f2fae,
   0x40c0fc4e3096851f,
   0x40c12dab2751447f,
   0x40c14e924da3edf0,
   0x40c15f436105eba5,
   0x40c16060d1fb766b,
   0x40c150f969b09355,
   0x40c1606e01429b5e,
   0x40c199203f041820,
   0x40c1c2f225dd2b94,
   0x40c1dd58a8ef3d56,
   0x40c1e8481cc014c9,
   0x40c1e390544b4013,
   0x40c1cf3d9a7ac59d,
   0x40c1d1dba57d322a,
   0x40c1eef130458bdf,
   0x40c1fb1f130ab494,
   0x40c1f60987fc87fb,
   0x40c1dfc04c9ef484,
   0x40c1bc877e6c670b,
   0x40c18cddcbfcc5b2,
   0x40c14dda6e32d9be,
   0x40c0feb71141826c,
   0x40c114c98fa1069e,
   0x40c177608c0183b2,
   0x40c1ca1475d1488c,
   0x40c20cacbbc9b835,
   0x40c23e687b2bb16a,
   0x40c25ebda39f8251,
   0x40c26dc18e4f489d,
   0x40c26c42a91f800e]

theorem record2684ChunkBits121Length2685 :
    (record2684ChunkBits1212685).length = 32 := by
  decide

theorem record2684ChunkSum1212685 :
    ((record2684ChunkBits1212685).map binary64Value2674).sum =
      (158721489811297041 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1212685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3904 through 3935,
decoded and summed as exact rationals. -/
def record2684ChunkBits1222685 : List Nat :=
  [0x40c28a25b8c69623,
   0x40c2d15cee375faf,
   0x40c30903f71897b6,
   0x40c3305bab558247,
   0x40c3471c5cfca48e,
   0x40c34d96d2d7cb6f,
   0x40c3435175b97412,
   0x40c328d3d605f0fb,
   0x40c2fe22bdbaf016,
   0x40c2e11a590b82ac,
   0x40c2e810090e51bf,
   0x40c2e39a974dfed3,
   0x40c2cf8ab76c4e15,
   0x40c2aabb0331144d,
   0x40c2760e05dec591,
   0x40c231afac91d4ed,
   0x40c1dc9ef310f2f6,
   0x40c1ef3e32103b2e,
   0x40c2538547d525e9,
   0x40c2a6d7c77b231a,
   0x40c2e88375d56834,
   0x40c3182c28f5084e,
   0x40c33593c23285dc,
   0x40c340b7f6390699,
   0x40c36c31655f781f,
   0x40c3c0aaecd1ab54,
   0x40c405360bc587fa,
   0x40c439bd914f5924,
   0x40c45d969e74ebd6,
   0x40c470c2092681dc,
   0x40c47281f353e5ab,
   0x40c464dd08894bfe]

theorem record2684ChunkBits122Length2685 :
    (record2684ChunkBits1222685).length = 32 := by
  decide

theorem record2684ChunkSum1222685 :
    ((record2684ChunkBits1222685).map binary64Value2674).sum =
      (172457724634119447 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1222685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3936 through 3967,
decoded and summed as exact rationals. -/
def record2684ChunkBits1232685 : List Nat :=
  [0x40c4486112edc66f,
   0x40c41b753def9ed7,
   0x40c3e4aace5e69cf,
   0x40c3b1a53c1e1203,
   0x40c3ab24b43f97d8,
   0x40c392bdfe0c7ba5,
   0x40c3681c0ccdad9f,
   0x40c32bf4b6985e83,
   0x40c2de5e2a279088,
   0x40c27fb14e61822f,
   0x40c2894e871e3d79,
   0x40c2e9c4d172bd3a,
   0x40c33a7618166e6d,
   0x40c3791f20bdb937,
   0x40c3a584458e4bf4,
   0x40c3bf92c4d0e457,
   0x40c3fa57333fe074,
   0x40c45e162a01011f,
   0x40c4b2005c68ec1f,
   0x40c4f55d4232c5eb,
   0x40c5279051a79f8e,
   0x40c549e15949fefe,
   0x40c55d0fb370c234,
   0x40c55e96576b60ba,
   0x40c551c69b0f5920,
   0x40c537bc97c56601,
   0x40c50c1227192276,
   0x40c4cf0bb342829f,
   0x40c4818c074e2e6b,
   0x40c42d75d856a379,
   0x40c40eff88dca4a3,
   0x40c3dfdf9f315cc5]

theorem record2684ChunkBits123Length2685 :
    (record2684ChunkBits1232685).length = 32 := by
  decide

theorem record2684ChunkSum1232685 :
    ((record2684ChunkBits1232685).map binary64Value2674).sum =
      (180959056807522985 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1232685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 3968 through 3999,
decoded and summed as exact rationals. -/
def record2684ChunkBits1242685 : List Nat :=
  [0x40c39f67b4ad25b4,
   0x40c34da35a40f5ec,
   0x40c2eaca4bd468c0,
   0x40c2ee8040e53b60,
   0x40c34939b6293232,
   0x40c392281c53cb3a,
   0x40c3c96c9271c643,
   0x40c3ee6f3cf2405b,
   0x40c4340bf66f8da9,
   0x40c4a319fc0b796e,
   0x40c50439f7cdd498,
   0x40c55876a223c1e7,
   0x40c59c98a5f11898,
   0x40c5cf6b0f3753e4,
   0x40c5f06c6ab3afae,
   0x40c605a306914be3,
   0x40c60ac50b62e4e8,
   0x40c5fe4395ec64f1,
   0x40c5dfe81e664f3d,
   0x40c5afcb27ad40ff,
   0x40c56e42c31e67db,
   0x40c51bdaa31d37ba,
   0x40c4b9c31ef14859,
   0x40c44978417a9354,
   0x40c41472fd80442b,
   0x40c3cf88ee35d5e5,
   0x40c379bdc1f0d782,
   0x40c31354199bfea3,
   0x40c30fff229f224f,
   0x40c364417f02295b,
   0x40c3a79b741f15a9,
   0x40c3d933201286ab]

theorem record2684ChunkBits124Length2685 :
    (record2684ChunkBits1242685).length = 32 := by
  decide

theorem record2684ChunkSum1242685 :
    ((record2684ChunkBits1242685).map binary64Value2674).sum =
      (183939149655635703 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1242685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4000 through 4031,
decoded and summed as exact rationals. -/
def record2684ChunkBits1252685 : List Nat :=
  [0x40c42bab195cf0c9,
   0x40c4a7dbf214cc19,
   0x40c51578f71dee10,
   0x40c572de496cb40a,
   0x40c5c05d5919c453,
   0x40c5fda7e6090b9d,
   0x40c630461fa35c0e,
   0x40c653c2d4bd3b15,
   0x40c665ab2127671e,
   0x40c665ed00fd7460,
   0x40c6548d40e5c733,
   0x40c631646d009366,
   0x40c5fcd21d344e58,
   0x40c5b757acc9a7ab,
   0x40c5624d55018ac2,
   0x40c4fdd757861e94,
   0x40c48a7c24b04363,
   0x40c409ea84907d39,
   0x40c3ba90573beb5a,
   0x40c364d7ecf140f9,
   0x40c2fef6ab54d7c5,
   0x40c2f6f2a4e98234,
   0x40c3441a0b6e0545,
   0x40c38092429a86c1,
   0x40c3ddb56030f679,
   0x40c460abb34cdfef,
   0x40c4d58493ce210d,
   0x40c53bbcea9c49ba,
   0x40c59576d277e520,
   0x40c5e29e7c1b5c14,
   0x40c61f51cce76aab,
   0x40c64b2c65c989ab]

theorem record2684ChunkBits125Length2685 :
    (record2684ChunkBits1252685).length = 32 := by
  decide

theorem record2684ChunkSum1252685 :
    ((record2684ChunkBits1252685).map binary64Value2674).sum =
      (94806694474347155 : ℚ) / 274877906944 := by
  norm_num [record2684ChunkBits1252685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4032 through 4063,
decoded and summed as exact rationals. -/
def record2684ChunkBits1262685 : List Nat :=
  [0x40c6675ec2e80c54,
   0x40c672341cfa7d8c,
   0x40c66b84cd094694,
   0x40c653fb16c7999c,
   0x40c62bc7adcaa146,
   0x40c5f56942ec8249,
   0x40c5af0416a23cfb,
   0x40c5594e5cf1980c,
   0x40c4f4c569ca370c,
   0x40c4824bb2036f79,
   0x40c402750a0197b5,
   0x40c37696608a837d,
   0x40c3113a0929c0d7,
   0x40c2aeafbb7ba52e,
   0x40c2a28ca2b1a2fb,
   0x40c2e7208c06d8be,
   0x40c34b2b8924c709,
   0x40c3d25b96087aaa,
   0x40c44c6f6c20ba46,
   0x40c4be3af9e06dc6,
   0x40c522d1b6f83e79,
   0x40c5784243bf1fd1,
   0x40c5be08b520d48e,
   0x40c5f3e5f8a988e9,
   0x40c619ae24ec4bdf,
   0x40c62fc1a5b0dea9,
   0x40c635593fca31ee,
   0x40c62a984e7ee083,
   0x40c60f788824d8d8,
   0x40c5e47c6ec91276,
   0x40c5a9c5b61b09fe,
   0x40c55fd24cc2d259]

theorem record2684ChunkBits126Length2685 :
    (record2684ChunkBits1262685).length = 32 := by
  decide

theorem record2684ChunkSum1262685 :
    ((record2684ChunkBits1262685).map binary64Value2674).sum =
      (190022461987237945 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1262685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4064 through 4095,
decoded and summed as exact rationals. -/
def record2684ChunkBits1272685 : List Nat :=
  [0x40c5084873ffd333,
   0x40c4a2cfdd582a28,
   0x40c431153df811ba,
   0x40c3b473ba249f01,
   0x40c32c6a33c68c33,
   0x40c29a4c1f86dea8,
   0x40c22468dc0497c1,
   0x40c213be0fd866a3,
   0x40c277cb62e33684,
   0x40c2feb98b7163d8,
   0x40c37f42de471d30,
   0x40c3f3aace34347a,
   0x40c45bc3ba5247fc,
   0x40c4b6b4e7a50055,
   0x40c503aa95bcddba,
   0x40c5420b36c6699b,
   0x40c572558648e572,
   0x40c593941b836888,
   0x40c5a55623c7b16e,
   0x40c5a772ddebc578,
   0x40c59a04769cbffc,
   0x40c57cd3526bc625,
   0x40c5502086d3ae5c,
   0x40c51450127ee259,
   0x40c4c9e4b4c6c65e,
   0x40c4718091725f2b,
   0x40c40be61e6595cf,
   0x40c399f9688c6f17,
   0x40c31cc1bfe582f1,
   0x40c2956bdc25232f,
   0x40c2054c8af59900,
   0x40c16de7115faaac]

theorem record2684ChunkBits127Length2685 :
    (record2684ChunkBits1272685).length = 32 := by
  decide

theorem record2684ChunkSum1272685 :
    ((record2684ChunkBits1272685).map binary64Value2674).sum =
      (90303853381534073 : ℚ) / 274877906944 := by
  norm_num [record2684ChunkBits1272685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4096 through 4127,
decoded and summed as exact rationals. -/
def record2684ChunkBits1282685 : List Nat :=
  [0x40c1696a1ea9e753,
   0x40c1f93628e95121,
   0x40c28142198e3e8b,
   0x40c300178e75ce13,
   0x40c374700641dc64,
   0x40c3dd2f5e97ec61,
   0x40c43960805aa53d,
   0x40c48832ce56906d,
   0x40c4c8f832f62d27,
   0x40c4fb239869bdf1,
   0x40c51e47ba5938a2,
   0x40c532164306f5f9,
   0x40c53663a19eb790,
   0x40c52b7ac3ecd869,
   0x40c51155f4dbb8da,
   0x40c4e83103d815a1,
   0x40c4b0a94610c8a0,
   0x40c46b88921f9329,
   0x40c41881840ab4f0,
   0x40c3b83b2da154c5,
   0x40c34b940bb25fbc,
   0x40c2d36e1fc8599a,
   0x40c250039e33c0af,
   0x40c1c6e7a66ea278,
   0x40c15fe9e34b4079,
   0x40c1677c90f15106,
   0x40c1d104eac0d17a,
   0x40c254fd14f9246b,
   0x40c2cedfd8da8bb5,
   0x40c33d80810747c1,
   0x40c3a17ce49e575b,
   0x40c3f96e221bc501]

theorem record2684ChunkBits128Length2685 :
    (record2684ChunkBits1282685).length = 32 := by
  decide

theorem record2684ChunkSum1282685 :
    ((record2684ChunkBits1282685).map binary64Value2674).sum =
      (175955514074445017 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1282685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4128 through 4159,
decoded and summed as exact rationals. -/
def record2684ChunkBits1292685 : List Nat :=
  [0x40c443e18bafb74e,
   0x40c4813e7054e7c6,
   0x40c4b006a2d71c33,
   0x40c4cfd62960e679,
   0x40c4e09fc62f1d1e,
   0x40c4e1fba04b200e,
   0x40c4d404675b06bf,
   0x40c4b6acb349c48c,
   0x40c48ac361d834c2,
   0x40c45000e0b2e313,
   0x40c406a231d3711f,
   0x40c3aef4c4220e03,
   0x40c34985dfd01af1,
   0x40c2d836cbd27cbb,
   0x40c25fb1c46c6022,
   0x40c1dc98a79956ec,
   0x40c17baac7acf9f5,
   0x40c134b762c70a32,
   0x40c13718dbd2f4b8,
   0x40c189e832ddf592,
   0x40c1df50769423d5,
   0x40c2578b5ffd5c9a,
   0x40c2c45055d31973,
   0x40c3248c6da473eb,
   0x40c377c96e8ece38,
   0x40c3bd615dbfd676,
   0x40c3f4c2c9c25ce0,
   0x40c41d76be698283,
   0x40c4393f5d779e05,
   0x40c445e6cedc343d,
   0x40c44358a96bd43f,
   0x40c4310f64c8a4f5]

theorem record2684ChunkBits129Length2685 :
    (record2684ChunkBits1292685).length = 32 := by
  decide

theorem record2684ChunkSum1292685 :
    ((record2684ChunkBits1292685).map binary64Value2674).sum =
      (175724747143076781 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1292685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4160 through 4191,
decoded and summed as exact rationals. -/
def record2684ChunkBits1302685 : List Nat :=
  [0x40c40f41893c2f23,
   0x40c3df8ea47d5d95,
   0x40c3a0fb07abecce,
   0x40c353f07fceaf8e,
   0x40c2fbff07be74aa,
   0x40c29956b47e6036,
   0x40c22a2498822d5b,
   0x40c1b1e3667fb916,
   0x40c15a4a98873968,
   0x40c11d49d04cb100,
   0x40c0d110dacc9ea3,
   0x40c0cefe615f6362,
   0x40c120fe63f62ed7,
   0x40c1648bc841d66f,
   0x40c1a28fee5d1622,
   0x40c20b8bbb6bf9ac,
   0x40c2688214b03d3f,
   0x40c2b8326ad80e50,
   0x40c2fa39e1622e6f,
   0x40c32e9465b5389d,
   0x40c354139a1184c5,
   0x40c36a655e614223,
   0x40c3714a54a00d5e,
   0x40c368f8a7498979,
   0x40c35181ce606c16,
   0x40c32b0c5d93fbc4,
   0x40c2f7c72a85dc39,
   0x40c2bb99a38aa9b0,
   0x40c271e5d3e5634b,
   0x40c21b28ea3822a5,
   0x40c1b8cc24ea79d9,
   0x40c1498d3369e0a6]

theorem record2684ChunkBits130Length2685 :
    (record2684ChunkBits1302685).length = 32 := by
  decide

theorem record2684ChunkSum1302685 :
    ((record2684ChunkBits1302685).map binary64Value2674).sum =
      (83212123856134713 : ℚ) / 274877906944 := by
  norm_num [record2684ChunkBits1302685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4192 through 4223,
decoded and summed as exact rationals. -/
def record2684ChunkBits1312685 : List Nat :=
  [0x40c0fb8260692f7a,
   0x40c0c9260b629389,
   0x40c087c69978a46a,
   0x40c03833855e555c,
   0x40c031b97139afb3,
   0x40c080c1bc27be57,
   0x40c0c19c1ed38847,
   0x40c0f4102e9d8c37,
   0x40c1194b0027e0f1,
   0x40c1707eea68e369,
   0x40c1bb5fa5b04089,
   0x40c1f907c19181ed,
   0x40c2286d1a6f4312,
   0x40c2493c82e67b06,
   0x40c25b3f82e95c10,
   0x40c25e752b991453,
   0x40c2531b46f336d3,
   0x40c23a9374c00f48,
   0x40c2187a472117c5,
   0x40c1e7d85b24728b,
   0x40c1aa59fc2dd1c8,
   0x40c15f4ef3238efc,
   0x40c1070ad0961153,
   0x40c0a3a2ef5c722f,
   0x40c06323adb351ee,
   0x40c03cf220def9e4,
   0x40c007e25db281c6,
   0x40bf890b355d132f,
   0x40bee5aa8d09f6cd,
   0x40becd9420973bf2,
   0x40bf602ecf7a9bc8,
   0x40bfd71201f1272e]

theorem record2684ChunkBits131Length2685 :
    (record2684ChunkBits1312685).length = 32 := by
  decide

theorem record2684ChunkSum1312685 :
    ((record2684ChunkBits1312685).map binary64Value2674).sum =
      (153257005410581335 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1312685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4224 through 4255,
decoded and summed as exact rationals. -/
def record2684ChunkBits1322685 : List Nat :=
  [0x40c018e4693f8ae4,
   0x40c0381a85cba820,
   0x40c04a17d1d58088,
   0x40c087bfe0484aa2,
   0x40c0bfbb81696cc4,
   0x40c0ea6db2abcda6,
   0x40c1072ec879b996,
   0x40c1167c4d909159,
   0x40c11b44c40178dc,
   0x40c114c2303582fc,
   0x40c10040721227b3,
   0x40c0de1c3b07a777,
   0x40c0ae5387f4eaab,
   0x40c071065d81b997,
   0x40c026c231bdb134,
   0x40bfa06c6a452a74,
   0x40bf3605fd8de099,
   0x40befe36838d3ffe,
   0x40bea9a649ccf6d2,
   0x40be38966cadd4d8,
   0x40bdab8b058e8399,
   0x40bd062d17b8bae2,
   0x40bcec34b0057ec1,
   0x40bd74f285148a48,
   0x40bde2ad5b32aeab,
   0x40be3550021e60e2,
   0x40be6c4eeb3d25bb,
   0x40be86f2f3282d0a,
   0x40be85b1582ff50c,
   0x40bec9df1459f92a,
   0x40bf1468b65b3a0f,
   0x40bf4f994d3a8c5b]

theorem record2684ChunkBits132Length2685 :
    (record2684ChunkBits1322685).length = 32 := by
  decide

theorem record2684ChunkSum1322685 :
    ((record2684ChunkBits1322685).map binary64Value2674).sum =
      (286267661588741417 : ℚ) / 1099511627776 := by
  norm_num [record2684ChunkBits1322685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4256 through 4287,
decoded and summed as exact rationals. -/
def record2684ChunkBits1332685 : List Nat :=
  [0x40bf717998a9461f,
   0x40bf79157ece5ba3,
   0x40bf68f7284f58f0,
   0x40bf3eca80bca432,
   0x40befb59242ffc7b,
   0x40be9e3c11cf7d9f,
   0x40be28d708e8eda7,
   0x40bd9b58f12f3aa1,
   0x40bd4c39c189faf5,
   0x40bd2f4a31decab5,
   0x40bcf6a3753aab70,
   0x40bca26998f75376,
   0x40bc331a5573fbde,
   0x40bba960035620c2,
   0x40bb066b38959a9a,
   0x40bae0d6eda3881f,
   0x40bb56ae1aa59481,
   0x40bbb308075c8817,
   0x40bbf7aa8fe9a4b4,
   0x40bc247337fb42a0,
   0x40bc380fb9051a68,
   0x40bc34342bde10ed,
   0x40bc21c0dc595dd8,
   0x40bc45f876b0afe9,
   0x40bc7aedb0da30ac,
   0x40bc9798b2a478c0,
   0x40bc9c058f4e7125,
   0x40bc87d9377408b1,
   0x40bc5b32f86c684d,
   0x40bc1610c67f9f0d,
   0x40bbb8faf62c6c17,
   0x40bb4511e8ab0695]

theorem record2684ChunkBits133Length2685 :
    (record2684ChunkBits1332685).length = 32 := by
  decide

theorem record2684ChunkSum1332685 :
    ((record2684ChunkBits1332685).map binary64Value2674).sum =
      (259634184775147385 : ℚ) / 1099511627776 := by
  norm_num [record2684ChunkBits1332685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4288 through 4319,
decoded and summed as exact rationals. -/
def record2684ChunkBits1342685 : List Nat :=
  [0x40bb0d96a575ed8d,
   0x40bb050dbd4f9a4a,
   0x40bae447c50f5b27,
   0x40baaa32d63ec620,
   0x40ba56ca4637d3ea,
   0x40b9eaf7c7bdf52c,
   0x40b968632db50b85,
   0x40b8d1f75820bee2,
   0x40b8a5a68bbe2d62,
   0x40b90ee82a4360c0,
   0x40b96063f38d07d1,
   0x40b99ba009a5689d,
   0x40b9c5a0a2425ff7,
   0x40b9dceef0a70230,
   0x40b9db6f4f56ce17,
   0x40b9c1235db1e8f5,
   0x40b98ed53322f750,
   0x40b985b38cc10ba6,
   0x40b999ee36609710,
   0x40b997a5f43d2fc5,
   0x40b97ee65d195fc7,
   0x40b9500a0f3e614e,
   0x40b90b3c0a8cfdb4,
   0x40b8b1580d01cc6c,
   0x40b89144e5b76dcf,
   0x40b89d9e51ae6314,
   0x40b8927bbf499558,
   0x40b86f88bc2fdffc,
   0x40b83546d9800219,
   0x40b7e42086d95f19,
   0x40b77f54af3aec3a,
   0x40b706dd35fd5c4f]

theorem record2684ChunkBits134Length2685 :
    (record2684ChunkBits1342685).length = 32 := by
  decide

theorem record2684ChunkSum1342685 :
    ((record2684ChunkBits1342685).map binary64Value2674).sum =
      (14244109497526677 : ℚ) / 68719476736 := by
  norm_num [record2684ChunkBits1342685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4320 through 4351,
decoded and summed as exact rationals. -/
def record2684ChunkBits1352685 : List Nat :=
  [0x40b6792a4a2114b4,
   0x40b6440d86c31311,
   0x40b6a160e36061e1,
   0x40b6f41ba5aabd4f,
   0x40b73133348e4a10,
   0x40b7577a6a7ce013,
   0x40b766f2598266e8,
   0x40b75f90dc2535eb,
   0x40b7423702236853,
   0x40b70e931cb33619,
   0x40b6c538c4b6c9d8,
   0x40b693be0a7c2548,
   0x40b689017179c157,
   0x40b66b09a642f097,
   0x40b63978a9e9eddf,
   0x40b5f70c18a0ac97,
   0x40b5ea67aab78e80,
   0x40b606903b2a2aad,
   0x40b60dac37d1912f,
   0x40b5ff6b402f615b,
   0x40b5dc283125c79f,
   0x40b5a6c896af38a6,
   0x40b55f352b89354d,
   0x40b503a84c56336b,
   0x40b494e8a59f1a77,
   0x40b4169f6f21dee0,
   0x40b3eb3d5d604391,
   0x40b44226f122da7d,
   0x40b486625d990a41,
   0x40b4b5f2b02aabb7,
   0x40b4d0dd57e64821,
   0x40b4d765085247cf]

theorem record2684ChunkBits135Length2685 :
    (record2684ChunkBits1352685).length = 32 := by
  decide

theorem record2684ChunkSum1352685 :
    ((record2684ChunkBits1352685).map binary64Value2674).sum =
      (49403693899093623 : ℚ) / 274877906944 := by
  norm_num [record2684ChunkBits1352685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4352 through 4383,
decoded and summed as exact rationals. -/
def record2684ChunkBits1362685 : List Nat :=
  [0x40b4c9833b3e199c,
   0x40b4a868fb1f3ec6,
   0x40b47417c8d8f65a,
   0x40b42d74b15e710b,
   0x40b3d47fea84e4e7,
   0x40b38727daede518,
   0x40b36842e6b42240,
   0x40b3386e6f3dd55b,
   0x40b33ad0c95584e6,
   0x40b3620c1f06dbe4,
   0x40b3764e7834faf5,
   0x40b377d660de6a50,
   0x40b36b74cbcd3384,
   0x40b34e39761dfca8,
   0x40b31e63ddc498a4,
   0x40b2dc5120e91fd4,
   0x40b28d2e3bc06435,
   0x40b2308ceefc9a61,
   0x40b1c33406a79f53,
   0x40b1965ee72d1c9d,
   0x40b1dcf708695e3c,
   0x40b213b7457ecb06,
   0x40b238a1a83825dd,
   0x40b24bcd591e19d2,
   0x40b24cbec83e3eb8,
   0x40b23bc17da2e1d1,
   0x40b219670e059fcc,
   0x40b1e5cf0fc5bbc1,
   0x40b1a14245327e10,
   0x40b14c3d592be5ef,
   0x40b0e749f5661605,
   0x40b0844f7c3ac267]

theorem record2684ChunkBits136Length2685 :
    (record2684ChunkBits1362685).length = 32 := by
  decide

theorem record2684ChunkSum1362685 :
    ((record2684ChunkBits1362685).map binary64Value2674).sum =
      (42202676852654851 : ℚ) / 274877906944 := by
  norm_num [record2684ChunkBits1362685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4384 through 4415,
decoded and summed as exact rationals. -/
def record2684ChunkBits1372685 : List Nat :=
  [0x40b092206cbea9a9,
   0x40b0c17c9f857737,
   0x40b0e3920a3b65c2,
   0x40b0f788a6c4c800,
   0x40b0fa98e63df41f,
   0x40b0ed2e2197be5d,
   0x40b0cf55b592b065,
   0x40b0a7a6f6509dcd,
   0x40b071ae0b9246db,
   0x40b02d371a709c0b,
   0x40afb60e9e497863,
   0x40aef78e4909c00c,
   0x40aea32ff08d49b6,
   0x40af16523995cc5c,
   0x40af6cf33548d4de,
   0x40afa32b2deac374,
   0x40afb911d87e9fbe,
   0x40afaeef7d4836a4,
   0x40af856fc259bd73,
   0x40af3e3427969c0d,
   0x40aed91d1a725e3d,
   0x40ae56575a8097b3,
   0x40adb6ec01c852e2,
   0x40acfc19c5edb8d9,
   0x40ac9502b8bddacf,
   0x40ac7fbbd613cdc4,
   0x40acd5f0364f49f1,
   0x40ad10398b8435cf,
   0x40ad2f20f63eb150,
   0x40ad34b5ccbc9889,
   0x40ad268e2dd097e0,
   0x40acfc596880d047]

theorem record2684ChunkBits137Length2685 :
    (record2684ChunkBits1372685).length = 32 := by
  decide

theorem record2684ChunkSum1372685 :
    ((record2684ChunkBits1372685).map binary64Value2674).sum =
      (281298800524154655 : ℚ) / 2199023255552 := by
  norm_num [record2684ChunkBits1372685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4416 through 4447,
decoded and summed as exact rationals. -/
def record2684ChunkBits1382685 : List Nat :=
  [0x40acb6a50f2fb3ae,
   0x40ac5577249fa08e,
   0x40abd9dd20f2f6a4,
   0x40ab468e529165f9,
   0x40aa9ac96328a3b3,
   0x40aa457fb90057c8,
   0x40aa9a08b2a9af0a,
   0x40aad6618d3b403b,
   0x40aaf9e0923648f9,
   0x40ab034743e0913f,
   0x40aaf1591b31906c,
   0x40aac5b2bcfd3ccd,
   0x40aa8036e79513a2,
   0x40aa20fc1b45228e,
   0x40a9a969730d8318,
   0x40a91a1a3e677aed,
   0x40a8d79d424accf7,
   0x40a8d089c7e29266,
   0x40a8b0c0ab83ba78,
   0x40a87e0b09db550f,
   0x40a8ac96e12d66a1,
   0x40a8cddab9808741,
   0x40a8d6249ddbf2fa,
   0x40a8c5bae486406a,
   0x40a89d37038a4d5a,
   0x40a85d3b86903a8b,
   0x40a80646dd01b11d,
   0x40a7992a27642bef,
   0x40a717ec1fc40794,
   0x40a681f75c74aa63,
   0x40a630d7aa39c29b,
   0x40a66e1b78f7e3d3]

theorem record2684ChunkBits138Length2685 :
    (record2684ChunkBits1382685).length = 32 := by
  decide

theorem record2684ChunkSum1382685 :
    ((record2684ChunkBits1382685).map binary64Value2674).sum =
      (229215341253608639 : ℚ) / 2199023255552 := by
  norm_num [record2684ChunkBits1382685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4448 through 4479,
decoded and summed as exact rationals. -/
def record2684ChunkBits1392685 : List Nat :=
  [0x40a6975a51c6e8e3,
   0x40a6a9bcd6d70759,
   0x40a6a5335bc26046,
   0x40a68bfe30ae0c2d,
   0x40a65e2054b10619,
   0x40a61a78b62ac71c,
   0x40a5c3e403cd5342,
   0x40a5596d225c917c,
   0x40a52f8e8872fcbc,
   0x40a5352e22af5c53,
   0x40a52a6cb03fe1bc,
   0x40a51332f4cb7306,
   0x40a4e84f37a50383,
   0x40a4acb66e4d5c3e,
   0x40a4b48e738d6e32,
   0x40a4b981beaabebe,
   0x40a4aa4590d63cd9,
   0x40a4874cbd452dbf,
   0x40a4509157aac6b0,
   0x40a4072153f030b9,
   0x40a3ab75a95f484d,
   0x40a33da62aa69d15,
   0x40a2be6de626d4ec,
   0x40a2760281885368,
   0x40a2a29c86e169e3,
   0x40a2be839f7fdb26,
   0x40a2c7220a757e55,
   0x40a2bcf253044c76,
   0x40a29fe67d7ad049,
   0x40a2712e383f1384,
   0x40a230cd54f56d76,
   0x40a1df6fe8387a1a]

theorem record2684ChunkBits139Length2685 :
    (record2684ChunkBits1392685).length = 32 := by
  decide

theorem record2684ChunkSum1392685 :
    ((record2684ChunkBits1392685).map binary64Value2674).sum =
      (45835062836897027 : ℚ) / 549755813888 := by
  norm_num [record2684ChunkBits1392685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4480 through 4511,
decoded and summed as exact rationals. -/
def record2684ChunkBits1402685 : List Nat :=
  [0x40a1c641645ffd57,
   0x40a1d3efab467071,
   0x40a1d4f6f7eed9d9,
   0x40a1ca410b092761,
   0x40a1b3b54a2adbb5,
   0x40a18cbc0fa54c59,
   0x40a1553e665fa1c3,
   0x40a10f524db7a1ea,
   0x40a0f9a073e87fc0,
   0x40a0ec00ba8c229d,
   0x40a0cdb99d53e02a,
   0x40a0a048892d95e2,
   0x40a0635c39c33cf2,
   0x40a01762f1b4654c,
   0x409f79aee3bd3d75,
   0x409ea826c599ade4,
   0x409e29de8585b741,
   0x409e68117f38c6ce,
   0x409e8af4c03f146a,
   0x409e8e428ec30dce,
   0x409e7301d1bbe226,
   0x409e391ff2702e10,
   0x409de15b65c5c560,
   0x409d6d07da635b86,
   0x409d62ee583c02d2,
   0x409d9c1056f02b55,
   0x409db77abd4c7ca7,
   0x409db49ee6de011a,
   0x409d945a70dbe33c,
   0x409d620b203ee63d,
   0x409d155a2508936e,
   0x409cad9b95c77667]

theorem record2684ChunkBits140Length2685 :
    (record2684ChunkBits1402685).length = 32 := by
  decide

theorem record2684ChunkSum1402685 :
    ((record2684ChunkBits1402685).map binary64Value2674).sum =
      (143590482411959133 : ℚ) / 2199023255552 := by
  norm_num [record2684ChunkBits1402685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4512 through 4543,
decoded and summed as exact rationals. -/
def record2684ChunkBits1412685 : List Nat :=
  [0x409c2a8b70314403,
   0x409b8f2e6906d63f,
   0x409b3b2284781b27,
   0x409b05bae2fc390f,
   0x409ab8ca48210f0b,
   0x409a52c8937d3ed2,
   0x4099d446ee097e1b,
   0x40993e6412121535,
   0x4098920fd617abe5,
   0x409824aa0e343129,
   0x40984cff88f12728,
   0x4098605bd28e521d,
   0x40985a83d5a21d02,
   0x40983bf856d3c85e,
   0x4098068d27a935c1,
   0x4097c4f00015f605,
   0x4097d5712106cbee,
   0x40981854a398bfea,
   0x409842ac03f0aaf6,
   0x409854ba2ce7ee78,
   0x40984ea21d93e434,
   0x40983055ff7b1d9b,
   0x409800b84f2abe05,
   0x4097bcddcac93d1a,
   0x4097622035cdbe8e,
   0x4096f13f12eb9b4e,
   0x40966ba47c93f548,
   0x4095d17d8cc31e0b,
   0x409563ac86a0fb35,
   0x40951e166f82347c,
   0x4094c5170843d7c1,
   0x40945a88465cc4bb]

theorem record2684ChunkBits141Length2685 :
    (record2684ChunkBits1412685).length = 32 := by
  decide

theorem record2684ChunkSum1412685 :
    ((record2684ChunkBits1412685).map binary64Value2674).sum =
      (109046542703987031 : ℚ) / 2199023255552 := by
  norm_num [record2684ChunkBits1412685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4544 through 4575,
decoded and summed as exact rationals. -/
def record2684ChunkBits1422685 : List Nat :=
  [0x4093dfd5b0b5a122,
   0x4093537770746a04,
   0x4092f63c43924d80,
   0x40930d4bb53b5a15,
   0x40931557ffa8b9bf,
   0x40930df947c86b7d,
   0x4092facc3d7bc952,
   0x4092d507674a5592,
   0x4092f33c392d2a7d,
   0x40933a528153b519,
   0x40936ccff8beb3c2,
   0x40938added251281,
   0x4093948948ea44a1,
   0x40938a5464dc6cdf,
   0x409372ad45722842,
   0x409349386453cb16,
   0x40930dca14c807d1,
   0x4092bffb5123073b,
   0x4092608957fdeb4b,
   0x4091f049b4546dae,
   0x40917058fba7a271,
   0x4090e17acd9ca792,
   0x40906c8f144d9ebc,
   0x409025321c91aad2,
   0x408f9e3d0da7084b,
   0x408ed5af1852ed79,
   0x408df363f2b9bfae,
   0x408d55f1615ddd69,
   0x408d73f045dda56d,
   0x408d808df524f25e,
   0x408d712026614c4a,
   0x408d43be05eb80b3]

theorem record2684ChunkBits142Length2685 :
    (record2684ChunkBits1422685).length = 32 := by
  decide

theorem record2684ChunkSum1422685 :
    ((record2684ChunkBits1422685).map binary64Value2674).sum =
      (320246972401545703 : ℚ) / 8796093022208 := by
  norm_num [record2684ChunkBits1422685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4576 through 4607,
decoded and summed as exact rationals. -/
def record2684ChunkBits1432685 : List Nat :=
  [0x408d8855fcaf2f81,
   0x408e0fcf67d12cbe,
   0x408e76c591efe2a0,
   0x408ec032ea937f67,
   0x408ef42ae717983a,
   0x408f09b743861b2a,
   0x408eff0e31e832c7,
   0x408ed52b36217ba8,
   0x408e8cd8c1da7324,
   0x408e268c90213b05,
   0x408da34bc08e27e7,
   0x408d0515a1e3ec4e,
   0x408c4c76d1b6317f,
   0x408b7b3c97dd59bc,
   0x408a92f86f3edb7d,
   0x4089943c2737070b,
   0x4088adede3068b3a,
   0x408824bb7d6e28c7,
   0x40878744c2a69829,
   0x4086e17761a541b7,
   0x40866c64fdf9fc03,
   0x40867d519a529e11,
   0x40867a897415a903,
   0x408660979181b532,
   0x4086ac2b61ae1c8e,
   0x40872f50f25685a3,
   0x4087986883b8ee4b,
   0x4087ea94cc398515,
   0x408824354b7afd3c,
   0x4088442c49345aa8,
   0x40884abfdf9c5b38,
   0x408838a2ccca4c78]

theorem record2684ChunkBits143Length2685 :
    (record2684ChunkBits1432685).length = 32 := by
  decide

theorem record2684ChunkSum1432685 :
    ((record2684ChunkBits1432685).map binary64Value2674).sum =
      (238469104906005385 : ℚ) / 8796093022208 := by
  norm_num [record2684ChunkBits1432685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4608 through 4639,
decoded and summed as exact rationals. -/
def record2684ChunkBits1442685 : List Nat :=
  [0x40880ebd4412cbb0,
   0x4087ceb7847baac8,
   0x4087783d53d3f1bb,
   0x40870b5b72de4b23,
   0x408689616ddc924d,
   0x4085f4db3ebb3370,
   0x40854cffd9880b1b,
   0x4084934909aa3e8c,
   0x4083c8b91c244a14,
   0x4082f1c25b612077,
   0x408228570e12c8be,
   0x4081b705b92194a7,
   0x408136bd3653d753,
   0x4080d81ef6f0f7cf,
   0x4080e07bd372636f,
   0x4080df4142c27dc9,
   0x408130de47f4bd6f,
   0x4081a2f39ddc58e6,
   0x408201094e08d07b,
   0x40824aa8aac09687,
   0x408280fd99f438a3,
   0x4082a5343b18217a,
   0x4082b58afbfcd303,
   0x4082b268b970e3be,
   0x40829c2d6f7afbe7,
   0x4082764c18a9f802,
   0x40823f6dfe77799d,
   0x4081f719af39ec87,
   0x40819e1c6173475d,
   0x408134e8744d23c4,
   0x4080bc76456db883,
   0x408035b58eac8824]

theorem record2684ChunkBits144Length2685 :
    (record2684ChunkBits1442685).length = 32 := by
  decide

theorem record2684ChunkSum1442685 :
    ((record2684ChunkBits1442685).map binary64Value2674).sum =
      (85834405830059911 : ℚ) / 4398046511104 := by
  norm_num [record2684ChunkBits1442685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4640 through 4671,
decoded and summed as exact rationals. -/
def record2684ChunkBits1452685 : List Nat :=
  [0x407f4e1d488b6d34,
   0x407e1d58ba6dd0f6,
   0x407ce0cb69472038,
   0x407b8e3fae3c8eac,
   0x407a2d7673876526,
   0x407968110a400be4,
   0x4078d54c786d2886,
   0x4078db26f4d6c7b7,
   0x40796d145d11847d,
   0x407a32da50497370,
   0x407ad913548ab08c,
   0x407b5fb8763acf19,
   0x407bc79153baaf8c,
   0x407c11bc9f2f1be8,
   0x407c3daec25e1e71,
   0x407c4ba790ee5f5f,
   0x407c3c12244db4b3,
   0x407c0fac4619d4db,
   0x407bc732d605c44f,
   0x407b64786ead1460,
   0x407ae7f0e984c1f3,
   0x407a55948e5999ce,
   0x4079b3681b8d9c0b,
   0x40790a0cc8fecc9a,
   0x40784c1a779f0625,
   0x40777992cb3a7200,
   0x40769412bc8c83b1,
   0x40759d46429228f0,
   0x407496bda7eed033,
   0x407382f66922c4ef,
   0x407265c961e56c0e,
   0x4071dbe67f2c099b]

theorem record2684ChunkBits145Length2685 :
    (record2684ChunkBits1452685).length = 32 := by
  decide

theorem record2684ChunkSum1452685 :
    ((record2684ChunkBits1452685).map binary64Value2674).sum =
      (231126866159691103 : ℚ) / 17592186044416 := by
  norm_num [record2684ChunkBits1452685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4672 through 4703,
decoded and summed as exact rationals. -/
def record2684ChunkBits1462685 : List Nat :=
  [0x407250628f98180c,
   0x4072f021e1bc5c2d,
   0x40738073f44c2551,
   0x4073fae3dd798189,
   0x40745e69747da9f2,
   0x4074ac1f9d299040,
   0x4074e35cdec55985,
   0x40750371162a1267,
   0x40750ceb63577f05,
   0x4075002067837e39,
   0x4074de0d6daaecc1,
   0x4074a6d3f1b61e0f,
   0x40745b384fb2abb4,
   0x4074028ab08ff2b3,
   0x4073a5bd0f505255,
   0x4073375f270d981f,
   0x4072b9554012fc5f,
   0x40722c47f62e2d8a,
   0x4071910795d18377,
   0x4070e79b07a29213,
   0x407032b37cee4c11,
   0x406ee821db5798d8,
   0x406d55ad46b75582,
   0x406bb7572ffc0806,
   0x406b094d7969c56f,
   0x406bc9b81d8745a9,
   0x406cb6092c63308c,
   0x406d7f24ae36d0a7,
   0x406e253949581a4f,
   0x406ea7614d503425,
   0x406f064f9566dd92,
   0x406f4298e4a1fe2a]

theorem record2684ChunkBits146Length2685 :
    (record2684ChunkBits1462685).length = 32 := by
  decide

theorem record2684ChunkSum1462685 :
    ((record2684ChunkBits1462685).map binary64Value2674).sum =
      (322052190445824023 : ℚ) / 35184372088832 := by
  norm_num [record2684ChunkBits1462685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4704 through 4735,
decoded and summed as exact rationals. -/
def record2684ChunkBits1472685 : List Nat :=
  [0x406f69ef7fc59e99,
   0x406f8446bfe2f7ec,
   0x406f7f31b770fcaa,
   0x406f5b711ea325d9,
   0x406f2710125ae327,
   0x406edc04790f3fd1,
   0x406e7726947af011,
   0x406df66867dac7c6,
   0x406d5a96b41e7bb7,
   0x406ca4cd0cb429c9,
   0x406bd66944597cdc,
   0x406af106e1873c8d,
   0x4069f5b31fca85ee,
   0x4068e5f3550af595,
   0x4067c3be956566ca,
   0x406697030c8756aa,
   0x4065f0eebb12e769,
   0x40659908a8f8bc86,
   0x4065a72ced887b9e,
   0x4065fb67cdfba0e1,
   0x40667d9003e19c37,
   0x4066e55362dd5dd3,
   0x4067331afa8bc186,
   0x406767016b955caa,
   0x4067ad69b45c4d98,
   0x4067e569e55831a6,
   0x4068067bd9aafb6c,
   0x40681a609057027e,
   0x406816edac5a3024,
   0x4067fbf8b70f756f,
   0x4067c9f26dd5c36c,
   0x406782192bd68947]

theorem record2684ChunkBits147Length2685 :
    (record2684ChunkBits1472685).length = 32 := by
  decide

theorem record2684ChunkSum1472685 :
    ((record2684ChunkBits1472685).map binary64Value2674).sum =
      (233187615169213389 : ℚ) / 35184372088832 := by
  norm_num [record2684ChunkBits1472685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4736 through 4767,
decoded and summed as exact rationals. -/
def record2684ChunkBits1482685 : List Nat :=
  [0x406724b8e5806444,
   0x4066b296b538f014,
   0x40662c9dfa53289a,
   0x406593e8b3970276,
   0x4064e9e7f2b5141a,
   0x40642fb3897efb1c,
   0x406367fa90aa4b48,
   0x406296dc81877f7d,
   0x4062288569246bea,
   0x4061d4720ed2122c,
   0x40618b55fda8378a,
   0x4061853e6d3d6477,
   0x406170a251e173cf,
   0x40617a845b14f8c3,
   0x4061b298741a6785,
   0x4061d709addd96cc,
   0x4061ec73a785f658,
   0x406235577161ab0f,
   0x406270d540ec362d,
   0x4062997dfeb1b60e,
   0x4062af4868fa5e66,
   0x4062b2c8f31bef2d,
   0x4062a54cf3c3cd4c,
   0x40628655572ea6e7,
   0x40625667ac751516,
   0x406215c69cfcdfa8,
   0x4061c510429899c7,
   0x406165820285ada2,
   0x4060f7f2baa50c1b,
   0x40607c916483bdf2,
   0x405fe85656643121,
   0x405ec8ca7277d5f1]

theorem record2684ChunkBits148Length2685 :
    (record2684ChunkBits1482685).length = 32 := by
  decide

theorem record2684ChunkSum1482685 :
    ((record2684ChunkBits1482685).map binary64Value2674).sum =
      (83642195873405889 : ℚ) / 17592186044416 := by
  norm_num [record2684ChunkBits1482685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4768 through 4799,
decoded and summed as exact rationals. -/
def record2684ChunkBits1492685 : List Nat :=
  [0x405e374cb6ee31f6,
   0x405dc5f696a027c1,
   0x405d3bafd10bf8aa,
   0x405cbccafb429476,
   0x405c9678dc6d646a,
   0x405c592050e50079,
   0x405c0319e61ad8ac,
   0x405bc8904bfe4910,
   0x405be36c2aefd442,
   0x405beb6908241c06,
   0x405c6802a073364c,
   0x405cc76db2d2bdb1,
   0x405d09f511f346bd,
   0x405d2fb4bd8a37b3,
   0x405d3d02a6960410,
   0x405d2f8d07d6e014,
   0x405d076435eeb3f4,
   0x405cc4e66d86f2b5,
   0x405c691ebeafc650,
   0x405bf679e6752196,
   0x405b6cb594e26d7f,
   0x405accbc2f6d3d10,
   0x405a1849100caf88,
   0x40595785e9977644,
   0x4058fb9340f362ae,
   0x4058b2ef46c86ccf,
   0x405855a71657f997,
   0x4057e4a6ffeeacf0,
   0x405777023a318780,
   0x40574400a027840b,
   0x4057003412ec6e30,
   0x4056b0674c153e87]

theorem record2684ChunkBits149Length2685 :
    (record2684ChunkBits1492685).length = 32 := by
  decide

theorem record2684ChunkSum1492685 :
    ((record2684ChunkBits1492685).map binary64Value2674).sum =
      (245022950853984639 : ℚ) / 70368744177664 := by
  norm_num [record2684ChunkBits1492685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4800 through 4831,
decoded and summed as exact rationals. -/
def record2684ChunkBits1502685 : List Nat :=
  [0x40564d5922cbdf52,
   0x4055effc47518aa6,
   0x4055e630e2241e51,
   0x405640209d728506,
   0x4056840bf9426eab,
   0x4056b23e7a6f631c,
   0x4056cc8752a9352e,
   0x4056d3024c30914f,
   0x4056c4d0b11db6f6,
   0x4056a26fbbb9067f,
   0x40566c7e4846af8b,
   0x4056239bf2da848b,
   0x4055cb101a54e8f9,
   0x405561692896a32f,
   0x4054e7570d99dd9b,
   0x405462ccd2e9550c,
   0x405423685f125e67,
   0x4053ef15e8c4ed36,
   0x4053aaea65188c62,
   0x405357e8f3892cf0,
   0x4052f6bec90847a9,
   0x405298ce5da5b8b3,
   0x405266253d6ec208,
   0x405226f8bbe5a705,
   0x4051d8fd7dac603e,
   0x40517ce2b2a03ab2,
   0x405113dbd3b4c92b,
   0x4050f2237ce427f8,
   0x405126e9ae871f08,
   0x40514ef98287d4ab,
   0x4051670af5e15f64,
   0x40516f4b26ae5b46]

theorem record2684ChunkBits150Length2685 :
    (record2684ChunkBits1502685).length = 32 := by
  decide

theorem record2684ChunkSum1502685 :
    ((record2684ChunkBits1502685).map binary64Value2674).sum =
      (181693782547627701 : ℚ) / 70368744177664 := by
  norm_num [record2684ChunkBits1502685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4832 through 4863,
decoded and summed as exact rationals. -/
def record2684ChunkBits1512685 : List Nat :=
  [0x4051681ad3d30bd0,
   0x405151ebd2139b71,
   0x40512cf163b5cfb6,
   0x4050f9d6a712cf8b,
   0x4050b9234cace7e6,
   0x40506b79ebf8abe1,
   0x4050121d3053f167,
   0x404f635058469dc6,
   0x404eff8019731dc8,
   0x404ea9684e22a7b5,
   0x404e3ed10ca71714,
   0x404dbe120ef43c76,
   0x404d2e8375db01e9,
   0x404c8e104f27de7b,
   0x404bed324e83cf7f,
   0x404b811001c72a38,
   0x404b0398fe892e01,
   0x404a71f3e0474691,
   0x4049cd81b4731aa1,
   0x404959b7ce478beb,
   0x404940e409ea92fd,
   0x404918c8e4471c1b,
   0x4049300aa7dd3cb1,
   0x404937f1155af522,
   0x40492a9227c6aa73,
   0x4049086d25d3c981,
   0x4048d1fa5dfb6754,
   0x404887af65339503,
   0x40482a60710eb37a,
   0x4047bafeee7eb84a,
   0x40473acd586c8ee1,
   0x4046afaba7ac021d]

theorem record2684ChunkBits151Length2685 :
    (record2684ChunkBits1512685).length = 32 := by
  decide

theorem record2684ChunkSum1512685 :
    ((record2684ChunkBits1512685).map binary64Value2674).sum =
      (126820945267378351 : ℚ) / 70368744177664 := by
  norm_num [record2684ChunkBits1512685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4864 through 4895,
decoded and summed as exact rationals. -/
def record2684ChunkBits1522685 : List Nat :=
  [0x404662ded49f8a79,
   0x40461d0657e34042,
   0x4045c7d10d0f703a,
   0x4045683fd4227c47,
   0x4044fa1722329324,
   0x40447dcb00736fbf,
   0x4043f477fa5f4a12,
   0x40436c49c7571105,
   0x40430ab9a58b2258,
   0x40429ec4d7444766,
   0x404226a873f4e6e5,
   0x4041b0cdf56efc7f,
   0x4041988955a2e864,
   0x4041720ff776daa6,
   0x40413d9adca3a8d7,
   0x4040fdc9f8b4e79f,
   0x4040e2ae547af945,
   0x4040c3c55c6fd42b,
   0x404097725635d0e4,
   0x40405ebfaf7df71b,
   0x40401a06124d7846,
   0x403f943916990d0e,
   0x403edf4fadf77d16,
   0x403e1df66094c75f,
   0x403db04408d4b415,
   0x403d4dd78fe29f74,
   0x403cdb30907591c1,
   0x403c53ff9e428c98,
   0x403bb8ecc576972f,
   0x403b0b7bbad27e2d,
   0x403a4d75e42a3cc4,
   0x40397fa47b064dc3]

theorem record2684ChunkBits152Length2685 :
    (record2684ChunkBits1522685).length = 32 := by
  decide

theorem record2684ChunkSum1522685 :
    ((record2684ChunkBits1522685).map binary64Value2674).sum =
      (155284438059185457 : ℚ) / 140737488355328 := by
  norm_num [record2684ChunkBits1522685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4896 through 4927,
decoded and summed as exact rationals. -/
def record2684ChunkBits1532685 : List Nat :=
  [0x4038b229f624e6e8,
   0x40381ad03de3f5b2,
   0x403777426f5be3b5,
   0x4036c4a659b49400,
   0x40366e979b0841e1,
   0x40363363a7b0829c,
   0x4035e6ee8a47f733,
   0x403589d88c3fdbca,
   0x40351c7ac4ae3edc,
   0x4034a1b741612762,
   0x40344e52670c3498,
   0x4034002c25b90ed3,
   0x4033a27b7a9b8630,
   0x403336073cf1da77,
   0x4032bbc7fc350ef7,
   0x403239cfaa4995f9,
   0x4031f1d427239281,
   0x4031b0794f68b51a,
   0x403161e045311789,
   0x4031067f58cd1408,
   0x40309edc66ae4eeb,
   0x40302bae9adb8070,
   0x402f5baa35104734,
   0x402e4caa3f83711d,
   0x402d2d9673be7fd0,
   0x402c128172280439,
   0x402b47fdcfaad91d,
   0x402a71423596c9e0,
   0x4029c94531b0e08b,
   0x402976d61a8e651d,
   0x40290d698c5eb739,
   0x40288dc92da4699c]

theorem record2684ChunkBits153Length2685 :
    (record2684ChunkBits1532685).length = 32 := by
  decide

theorem record2684ChunkSum1532685 :
    ((record2684ChunkBits1532685).map binary64Value2674).sum =
      (81703690215817277 : ℚ) / 140737488355328 := by
  norm_num [record2684ChunkBits1532685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4928 through 4959,
decoded and summed as exact rationals. -/
def record2684ChunkBits1542685 : List Nat :=
  [0x4027f9040fcbe6fa,
   0x4027506350dc80bc,
   0x40269594ecc307e5,
   0x4025cdf1843bf713,
   0x4025300275a64bc6,
   0x4024a452923be116,
   0x4024089e4c07960e,
   0x40236aed0476a2d7,
   0x402312ab30e28701,
   0x4022bf50a922fc10,
   0x40225aec5dca3517,
   0x4021e679c4cf17be,
   0x4021635bafb9d16c,
   0x4020d28e34d52c9a,
   0x402035063d6b1d57,
   0x401f182f43cc0398,
   0x401db292db67b1c2,
   0x401c3c507c9b3a3c,
   0x401ad875d2070da4,
   0x401a84cf4dd41d04,
   0x401a1dd27199d3b3,
   0x40199a8a65a8dc49,
   0x4018fa3374a205de,
   0x40183e53b6dcb622,
   0x401769155792151c,
   0x40167bdb8cb63378,
   0x4015788305a408a2,
   0x4014617fe0712c9c,
   0x4013391075c9329e,
   0x4012051a683fbc49,
   0x4011a7e15b743f68,
   0x40117ac69e052013]

theorem record2684ChunkBits154Length2685 :
    (record2684ChunkBits1542685).length = 32 := by
  decide

theorem record2684ChunkSum1542685 :
    ((record2684ChunkBits1542685).map binary64Value2674).sum =
      (140506184917868777 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits1542685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4960 through 4991,
decoded and summed as exact rationals. -/
def record2684ChunkBits1552685 : List Nat :=
  [0x4011934d91919a67,
   0x4011b32926684868,
   0x4011b5067963f08e,
   0x4011a4668cd6e330,
   0x4012068d5820f62a,
   0x4012529200523e03,
   0x40128875a1d12b61,
   0x4012a8e146480d54,
   0x4012b4de64f4aae9,
   0x4012ab8e2c165212,
   0x40128d98b6b7be1f,
   0x40126e57834ee53b,
   0x40129f0f403d8670,
   0x4012be99b538185b,
   0x4012c8e408811ef2,
   0x4012bed44801b41e,
   0x4012a16d9b829237,
   0x40127167136609fc,
   0x40123010fdf26b6c,
   0x401210cc919b9c06,
   0x40123682afc83ac6,
   0x40124f37364f38fb,
   0x40125a2f60f2776e,
   0x4012589fe13ba4d3,
   0x40129ade3c226d07,
   0x4013065b1acdeebf,
   0x40136110480fe933,
   0x4013aa423e177c76,
   0x4013e1fa75b84a8a,
   0x4014088a96bb24d3,
   0x40141efa04d90255,
   0x4014261ab5858d80]

theorem record2684ChunkBits155Length2685 :
    (record2684ChunkBits1552685).length = 32 := by
  decide

theorem record2684ChunkSum1552685 :
    ((record2684ChunkBits1552685).map binary64Value2674).sum =
      (167992702719306215 : ℚ) / 1125899906842624 := by
  norm_num [record2684ChunkBits1552685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 4992 through 5023,
decoded and summed as exact rationals. -/
def record2684ChunkBits1562685 : List Nat :=
  [0x40141d7063d9bd20,
   0x401405a81bf219d4,
   0x4013dfe950f79d08,
   0x4013ad7c4388aee2,
   0x40137b2292da6b83,
   0x401380897e747743,
   0x40137a8a518bfc61,
   0x4013673bfde6903c,
   0x401348232c8cb192,
   0x40131da2fe603d5a,
   0x4012f4ee710f7d26,
   0x40132e7553487282,
   0x40135bd798555feb,
   0x40137cebb027b085,
   0x401391e703b3d98f,
   0x40139b8d3e7bedc9,
   0x4013b6c1301a3950,
   0x4013d4d9cb4ab974,
   0x4013f39735d068ea,
   0x40141a39e269fa57,
   0x401434f919ca0150,
   0x4014436e45f147e8,
   0x401445f0fc72369f,
   0x40143ced1c9e9a8e,
   0x40142918eb5fd80e,
   0x40140b2b96c3ce0c,
   0x4013e3c3eb7c1645,
   0x4013b3c9037c2371,
   0x40137c9d2a50adf4,
   0x40134710d9026e43,
   0x401339d1bf6a58b8,
   0x40132606a1ff826d]

theorem record2684ChunkBits156Length2685 :
    (record2684ChunkBits1562685).length = 32 := by
  decide

theorem record2684ChunkSum1562685 :
    ((record2684ChunkBits1562685).map binary64Value2674).sum =
      (177225173928480819 : ℚ) / 1125899906842624 := by
  norm_num [record2684ChunkBits1562685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5024 through 5055,
decoded and summed as exact rationals. -/
def record2684ChunkBits1572685 : List Nat :=
  [0x40130a537016a596,
   0x4012e8210033e3ef,
   0x4012bfecf4e8bf0b,
   0x4012da525b302ffe,
   0x4012fa29676ce464,
   0x4013115f281aa4e3,
   0x401320068755f1ac,
   0x401326904716d5a3,
   0x401335186ff5e67d,
   0x4013436a4ba2fa3e,
   0x401349616ee222b6,
   0x401347284420a1d0,
   0x401341cb647cafa8,
   0x401340e2eab05864,
   0x4013387af7e4acd3,
   0x4013284d5472bca9,
   0x401310aeee8aa5f9,
   0x4012f2105156e44c,
   0x4012cd0598e5377e,
   0x4012a22ed5a44fe6,
   0x40127219feef9419,
   0x40123dba8f36a190,
   0x40120aa6d815c3ef,
   0x4011f58798bab7d1,
   0x4011dd24cb6d5790,
   0x4011c02d2f3839d0,
   0x40119f019a3704a3,
   0x401191a7ab7fdf58,
   0x4011a2e95107d426,
   0x4011aeca77c76f12,
   0x4011b5313b4a9398,
   0x4011b64a4ce45269]

theorem record2684ChunkBits157Length2685 :
    (record2684ChunkBits1572685).length = 32 := by
  decide

theorem record2684ChunkSum1572685 :
    ((record2684ChunkBits1572685).map binary64Value2674).sum =
      (167610065370759571 : ℚ) / 1125899906842624 := by
  norm_num [record2684ChunkBits1572685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5056 through 5087,
decoded and summed as exact rationals. -/
def record2684ChunkBits1582685 : List Nat :=
  [0x4011ba8667efab9b,
   0x4011bd6344739c4d,
   0x4011baae87ee3ad1,
   0x4011b268fc405738,
   0x4011a4b5851255de,
   0x401191be0759cbb8,
   0x40117b34e44a4047,
   0x401166e7ec5a246c,
   0x40114e223768139a,
   0x401130c25856816c,
   0x40110f04068ca809,
   0x4010e94ab0734dd4,
   0x4010c005cff107f1,
   0x401093b0e2898301,
   0x401065485aa86d60,
   0x40103860e42f7c29,
   0x401022346ab46851,
   0x401009ac229285fb,
   0x400fdc924db71077,
   0x400fa09d218dc701,
   0x400fa6ea9efaee3c,
   0x400fae4d3f73acc4,
   0x400faf0dd1b65fc5,
   0x400fa91ff46f0f75,
   0x400fa52c5f5e7c58,
   0x400f9e45aaf7deb8,
   0x400f9002fd8e3708,
   0x400f7a5952633a77,
   0x400f5d46396030b0,
   0x400f38edf552ca2d,
   0x400f0d89b3da8862,
   0x400edb6a87890008]

theorem record2684ChunkBits158Length2685 :
    (record2684ChunkBits1582685).length = 32 := by
  decide

theorem record2684ChunkSum1582685 :
    ((record2684ChunkBits1582685).map binary64Value2674).sum =
      (18579244286393557 : ℚ) / 140737488355328 := by
  norm_num [record2684ChunkBits1582685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5088 through 5119,
decoded and summed as exact rationals. -/
def record2684ChunkBits1592685 : List Nat :=
  [0x400ea3d0f2d4eab9,
   0x400e6d393b51ab76,
   0x400e31a448d2e70d,
   0x400df09b49e0d259,
   0x400daab0204c08a7,
   0x400d60cc4a6a3190,
   0x400d13ba58269ddb,
   0x400cc4369fc0f4d2,
   0x400c7655d1b3c6c8,
   0x400c4bfbaf4c8976,
   0x400c1ede1b7eee36,
   0x400bee48b1c35a9d,
   0x400bcec4fc760b3a,
   0x400bccd6e11105d8,
   0x400bc6eda0fdfc70,
   0x400bbcdf6669a7ed,
   0x400bb2ae097b1150,
   0x400ba5ca426ce1c5,
   0x400b94010fc2df7e,
   0x400b7d3050a6ce66,
   0x400b614b5c2ddb05,
   0x400b40584e5b683e,
   0x400b1a8afdf4d9e4,
   0x400aeff26fa7f8cc,
   0x400ac0c1070e610d,
   0x400a8d4102a2c96c,
   0x400a560dac856bb3,
   0x400a1e1b3bb7750e,
   0x4009e3b8a6623aa9,
   0x4009a64761061d20,
   0x40096629e55d47bd,
   0x4009242a78a8026a]

theorem record2684ChunkBits159Length2685 :
    (record2684ChunkBits1592685).length = 32 := by
  decide

theorem record2684ChunkSum1592685 :
    ((record2684ChunkBits1592685).map binary64Value2674).sum =
      (250215734204747535 : ℚ) / 2251799813685248 := by
  norm_num [record2684ChunkBits1592685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5120 through 5151,
decoded and summed as exact rationals. -/
def record2684ChunkBits1602685 : List Nat :=
  [0x4008e0c5fe302224,
   0x40089ea0c40dcf50,
   0x400878e6e381036c,
   0x4008517e5da4a352,
   0x400827e457147497,
   0x40081ab6abbe1195,
   0x400812570d9f172f,
   0x40080771b2dfde2c,
   0x4007fbc7e73c07a3,
   0x4007edf8a66e584f,
   0x4007dcdd7a1e163e,
   0x4007c849e92c6e8d,
   0x4007b023117bfae3,
   0x4007945b8d5e254b,
   0x400774f620a94397,
   0x4007520007393303,
   0x40072b93120a4781,
   0x400701d56038761a,
   0x4006d501b5a47b4f,
   0x4006a56cd3818a14,
   0x4006735cb4c6e5b8,
   0x40064018c0025b4a,
   0x40060b3b409fc999,
   0x4005d48ec6754cd6,
   0x40059cb17b2025f2,
   0x400563f918fb2b26,
   0x40052c0ebb0dcd9b,
   0x40050b5fb1008d23,
   0x4004e990168be636,
   0x4004cb570a382faa,
   0x4004c275231aaad4,
   0x4004b811db60fd0e]

theorem record2684ChunkBits160Length2685 :
    (record2684ChunkBits1602685).length = 32 := by
  decide

theorem record2684ChunkSum1602685 :
    ((record2684ChunkBits1602685).map binary64Value2674).sum =
      (206289452834165573 : ℚ) / 2251799813685248 := by
  norm_num [record2684ChunkBits1602685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5152 through 5183,
decoded and summed as exact rationals. -/
def record2684ChunkBits1612685 : List Nat :=
  [0x4004acd68773069c,
   0x40049ff9ed80adb1,
   0x400490dd2306275a,
   0x40047f5448e06e65,
   0x40046b3cb8e99112,
   0x4004547ebf111aa6,
   0x40043b0d3d31a68a,
   0x40041ee5e7aa146e,
   0x4004001279231db2,
   0x4003deafbad07fed,
   0x4003bad8e7e17914,
   0x400394a3b49138fe,
   0x40036c3cdc108c7b,
   0x400341d9406e74f4,
   0x400315b8108b94ab,
   0x4002e87f84b455a1,
   0x4002ba46d630031f,
   0x40028b5a0f0769e7,
   0x40025bcad45c5f35,
   0x40022cb04cfc6676,
   0x400210fe8942bec3,
   0x4001f47b9046a5f4,
   0x4001e1565a210147,
   0x4001d86a1fa4ede1,
   0x4001cec647e90846,
   0x4001c3f4e474042f,
   0x4001b79430117016,
   0x4001a975e7e30171,
   0x400199747f5c5943,
   0x400187731b0d2030,
   0x4001735c9609135f,
   0x40015d247b51a04e]

theorem record2684ChunkBits161Length2685 :
    (record2684ChunkBits1612685).length = 32 := by
  decide

theorem record2684ChunkSum1612685 :
    ((record2684ChunkBits1612685).map binary64Value2674).sum =
      (42626899229460341 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits1612685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5184 through 5215,
decoded and summed as exact rationals. -/
def record2684ChunkBits1622685 : List Nat :=
  [0x400144ccc436f44e,
   0x40012a55af90f1c2,
   0x40010dc9c3eb5dea,
   0x4000ef3d43f5a843,
   0x4000cecc46395e37,
   0x4000ac999fd0a207,
   0x400088ced03fdd3b,
   0x4000639ae1fe7754,
   0x40003d3283927aa6,
   0x400015f253064abe,
   0x3fffdcaff43868bc,
   0x3fff8c6675a7adef,
   0x3fff3c7415df55c7,
   0x3fff0d6cbf3a54b3,
   0x3ffedd18b93848c3,
   0x3ffec427204a133b,
   0x3ffeb415276135c5,
   0x3ffea25e2e01d254,
   0x3ffe8e7f41b8cee1,
   0x3ffe781a62bef194,
   0x3ffe5ee28e79634b,
   0x3ffe429831fb4f26,
   0x3ffe230a527dfd59,
   0x3ffe0018a9cc03b9,
   0x3ffdd9a8e8670679,
   0x3ffdafb2ae6cd555,
   0x3ffd823c1ae744a0,
   0x3ffd5158605f54cd,
   0x3ffd1d2836c28fcf,
   0x3ffce5d890d1c7f0,
   0x3ffcaba24dc537bb,
   0x3ffc6ec943aa6713]

theorem record2684ChunkBits162Length2685 :
    (record2684ChunkBits1622685).length = 32 := by
  decide

theorem record2684ChunkSum1622685 :
    ((record2684ChunkBits1622685).map binary64Value2674).sum =
      (35122590090068539 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits1622685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5216 through 5247,
decoded and summed as exact rationals. -/
def record2684ChunkBits1632685 : List Nat :=
  [0x3ffc2f9b65623dd9,
   0x3ffbee6f910f5a4e,
   0x3ffbabbc439501a1,
   0x3ffb6840e97c2cc2,
   0x3ffb2407071311b6,
   0x3ffadfc28e71c891,
   0x3ffab7b8aef6c341,
   0x3ffa8ea0d8df1570,
   0x3ffa7e3c7792a513,
   0x3ffa70058e1b60a6,
   0x3ffa60589e41b7f6,
   0x3ffa4ee02e9601b0,
   0x3ffa3b4cb120f8d1,
   0x3ffa255dc9dbf093,
   0x3ffa0cdcfa658324,
   0x3ff9f19cde4a70b2,
   0x3ff9d37dfac676b3,
   0x3ff9b26c9a88899b,
   0x3ff98e611592de67,
   0x3ff9675f8eb4d0e1,
   0x3ff93d7792592dde,
   0x3ff910c3e502c8a3,
   0x3ff8e16a0b13d7a2,
   0x3ff8af99586c0546,
   0x3ff87b8ac341c05c,
   0x3ff8457fd09ac471,
   0x3ff80dc1b815d037,
   0x3ff7d4c4be0026d4,
   0x3ff79af154520bc2,
   0x3ff7606a355220c8,
   0x3ff725da01ca7298,
   0x3ff70323d2c91fd3]

theorem record2684ChunkBits163Length2685 :
    (record2684ChunkBits1632685).length = 32 := by
  decide

theorem record2684ChunkSum1632685 :
    ((record2684ChunkBits1632685).map binary64Value2674).sum =
      (230980587629630439 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits1632685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5248 through 5279,
decoded and summed as exact rationals. -/
def record2684ChunkBits1642685 : List Nat :=
  [0x3ff6e03d8cd415c2,
   0x3ff6d490231288fe,
   0x3ff6c7f1cf91b9e9,
   0x3ff6ba13ab5277cc,
   0x3ff6aaad1cf9d903,
   0x3ff6997ac2d3e5fa,
   0x3ff686443815dae0,
   0x3ff670dac3b53ce1,
   0x3ff659197afabd0f,
   0x3ff63ee58f7e49e3,
   0x3ff6222e7745bd49,
   0x3ff602edc9fc8ad1,
   0x3ff5e126e3304433,
   0x3ff5bce6ff4c018c,
   0x3ff5964501c97887,
   0x3ff56d60dc31c6c0,
   0x3ff542632a55009f,
   0x3ff5157c8660f32e,
   0x3ff4e6e4f2d93406,
   0x3ff4b6db1bb1f8d5,
   0x3ff485d02d90ac3a,
   0x3ff453fd56d7d3b5,
   0x3ff4218eaee7e8a3,
   0x3ff3ef0eca5d87da,
   0x3ff3d0d1bd43447a,
   0x3ff3b4b1a0245a2c,
   0x3ff3aa60e03da940,
   0x3ff39f41176847dc,
   0x3ff3930e860767c8,
   0x3ff38589d3f2ca33,
   0x3ff3767998856408,
   0x3ff365ad95e6b8c1]

theorem record2684ChunkBits164Length2685 :
    (record2684ChunkBits1642685).length = 32 := by
  decide

theorem record2684ChunkSum1642685 :
    ((record2684ChunkBits1642685).map binary64Value2674).sum =
      (190968508173609695 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits1642685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5280 through 5311,
decoded and summed as exact rationals. -/
def record2684ChunkBits1652685 : List Nat :=
  [0x3ff352fda81a14b3,
   0x3ff33e4a0a0eda5f,
   0x3ff3277ba226a9b7,
   0x3ff30e840afa69a8,
   0x3ff2f35d92c7bf7c,
   0x3ff2d60b2e931fa5,
   0x3ff2b69846ae2ae2,
   0x3ff29518756c853b,
   0x3ff271a72b7a52b3,
   0x3ff24c674d1bc6c1,
   0x3ff225829802f1e8,
   0x3ff1fd2922a828ba,
   0x3ff1d390ba2db3fa,
   0x3ff1a920a232b646,
   0x3ff17df72e027636,
   0x3ff1524795da7ab8,
   0x3ff1268694d01e1b,
   0x3ff10bf10a42a892,
   0x3ff0f4d532e6df85,
   0x3ff0eb8ed8caa209,
   0x3ff0e1935eb383b0,
   0x3ff0d6a928b64381,
   0x3ff0ca9a153aaedc,
   0x3ff0bd354d364b78,
   0x3ff0ae51c23f24e8,
   0x3ff09dcd5d6d1463,
   0x3ff08b8d458e5689,
   0x3ff0777e0ae11715,
   0x3ff06193babb4713,
   0x3ff049c9e0c4b818,
   0x3ff030237032b766,
   0x3ff014aa9b66a0a8]

theorem record2684ChunkBits165Length2685 :
    (record2684ChunkBits1652685).length = 32 := by
  decide

theorem record2684ChunkSum1652685 :
    ((record2684ChunkBits1652685).map binary64Value2674).sum =
      (158079298678434005 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits1652685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5312 through 5343,
decoded and summed as exact rationals. -/
def record2684ChunkBits1662685 : List Nat :=
  [0x3fefeee12fceeba3,
   0x3fefb11aa5639e31,
   0x3fef703e2344792f,
   0x3fef2c94068911f7,
   0x3feee66f8360fb68,
   0x3fee9e2d852676e8,
   0x3fee5485f6952277,
   0x3fee099a64d6ad8e,
   0x3fedbdd06721b6dc,
   0x3fed71eb8edbde8b,
   0x3fed432993d5bfb8,
   0x3fed1cf65cda7bc2,
   0x3fed0c5042ae66b4,
   0x3fecfa72244a8b37,
   0x3fece6f90ecb9baa,
   0x3fecd1880a48b0f1,
   0x3fecb9cb6071423e,
   0x3fec9f7cbb491547,
   0x3fec8261c272d436,
   0x3fec624c92035e00,
   0x3fec3f1c046ebafd,
   0x3fec18bbd6885360,
   0x3febef24a45c7be8,
   0x3febc25bc3025dbc,
   0x3feb9272f9351b08,
   0x3feb5f88183a6a22,
   0x3feb29c476663103,
   0x3feaf15c4bb5b62b,
   0x3feab68df142582c,
   0x3fea79a108b238b3,
   0x3fea3aee3e24cbc7,
   0x3fe9fb032ad15bf2]

theorem record2684ChunkBits166Length2685 :
    (record2684ChunkBits1662685).length = 32 := by
  decide

theorem record2684ChunkSum1662685 :
    ((record2684ChunkBits1662685).map binary64Value2674).sum =
      (129782619567390385 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits1662685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5344 through 5375,
decoded and summed as exact rationals. -/
def record2684ChunkBits1672685 : List Nat :=
  [0x3fe9b9fa77e6661b,
   0x3fe97834fe605ac2,
   0x3fe9365a8d70d200,
   0x3fe90d2786ec3ee5,
   0x3fe8ed67c4760902,
   0x3fe8de518da5832f,
   0x3fe8ce2c22e0dd2a,
   0x3fe8bca3581f5d1c,
   0x3fe8a96822508711,
   0x3fe894337bf6818e,
   0x3fe87cc9e206ee42,
   0x3fe862fa1ff1fb3d,
   0x3fe8469db131d8e0,
   0x3fe82798ffeae426,
   0x3fe805db7f2b6a31,
   0x3fe7e15fa590e78d,
   0x3fe7ba2ac94ee750,
   0x3fe7904ce0a59063,
   0x3fe763e0267edd1a,
   0x3fe73508a42891a9,
   0x3fe703f3a511de5b,
   0x3fe6d0d7104a0665,
   0x3fe69bf0a990de49,
   0x3fe66597e6122ad3,
   0x3fe62e2b07182632,
   0x3fe5f5d0e8358596,
   0x3fe5bcdcbc612761,
   0x3fe583ddc2a5d542,
   0x3fe55faf17a09318,
   0x3fe54562f9f6f369,
   0x3fe537d045d6843c,
   0x3fe52955406c888e]

theorem record2684ChunkBits167Length2685 :
    (record2684ChunkBits1672685).length = 32 := by
  decide

theorem record2684ChunkSum1672685 :
    ((record2684ChunkBits1672685).map binary64Value2674).sum =
      (211778779543152931 : ℚ) / 9007199254740992 := by
  norm_num [record2684ChunkBits1672685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5376 through 5407,
decoded and summed as exact rationals. -/
def record2684ChunkBits1682685 : List Nat :=
  [0x3fe519aa22ffbaf6,
   0x3fe5088b90616e2b,
   0x3fe4f5bcfc60e732,
   0x3fe4e10bc23dd34f,
   0x3fe4ca4e139c212d,
   0x3fe4b1634adb81c0,
   0x3fe496341d84f021,
   0x3fe478b2b16e6b4d,
   0x3fe458da964a966e,
   0x3fe436b0a571c6fd,
   0x3fe41242c97269a9,
   0x3fe3eba7aec93465,
   0x3fe3c2fe5e81e0db,
   0x3fe3986dc2f29ed3,
   0x3fe36c241963cdd6,
   0x3fe33e564f5cce4d,
   0x3fe30f541a66fa2e,
   0x3fe2df5e1dffd0f4,
   0x3fe2aea0ec082046,
   0x3fe27d63b8bb5c08,
   0x3fe24c20a06f2148,
   0x3fe22c5d2270c307,
   0x3fe21690e42c5b77,
   0x3fe20a4a6693f0c3,
   0x3fe1fd3bc3ceaf2d,
   0x3fe1ef2846e69882,
   0x3fe1dfd7311db998,
   0x3fe1cf1583769e71,
   0x3fe1bcb8bad9bffb,
   0x3fe1a89de24208aa,
   0x3fe192a9d506bcbb,
   0x3fe17ac9673d23e2]

theorem record2684ChunkBits168Length2685 :
    (record2684ChunkBits1682685).length = 32 := by
  decide

theorem record2684ChunkSum1682685 :
    ((record2684ChunkBits1682685).map binary64Value2674).sum =
      (86532177952890141 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits1682685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5408 through 5439,
decoded and summed as exact rationals. -/
def record2684ChunkBits1692685 : List Nat :=
  [0x3fe160f1750f522a,
   0x3fe1451eda98ad15,
   0x3fe127565619a51f,
   0x3fe107a45585a1bf,
   0x3fe0e61cb08d2692,
   0x3fe0c2da50498027,
   0x3fe09dfec4de0c61,
   0x3fe077b1c9e8c6d0,
   0x3fe05020b9d7169d,
   0x3fe02790db4f54eb,
   0x3fdffc68b0904c86,
   0x3fdfa86a235e4956,
   0x3fdf539f3895378e,
   0x3fdefed7290dd753,
   0x3fdec76478fa5822,
   0x3fdea38d8c24c81d,
   0x3fde8d9d06ab1900,
   0x3fde76594a86a9c4,
   0x3fde5d5b691fb60b,
   0x3fde4243691a1f95,
   0x3fde24baff804af6,
   0x3fde047a63d3c8b7,
   0x3fdde146aa09515f,
   0x3fddbaf2322bc5e7,
   0x3fdd915ce9665b30,
   0x3fdd647460ef43e9,
   0x3fdd3433bd56f978,
   0x3fdd00a380efbebb,
   0x3fdcc9d9338c992e,
   0x3fdc8ff6e968c432,
   0x3fdc532aaacbd78e,
   0x3fdc13adbd9ccc59]

theorem record2684ChunkBits169Length2685 :
    (record2684ChunkBits1692685).length = 32 := by
  decide

theorem record2684ChunkSum1692685 :
    ((record2684ChunkBits1692685).map binary64Value2674).sum =
      (70073344831884801 : ℚ) / 4503599627370496 := by
  norm_num [record2684ChunkBits1692685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5440 through 5471,
decoded and summed as exact rationals. -/
def record2684ChunkBits1702685 : List Nat :=
  [0x3fdbd1c3d1ab5d2e,
   0x3fdb8dba0fc3999b,
   0x3fdb481100d70031,
   0x3fdb0100988ff1b0,
   0x3fdab8e2855dbcf6,
   0x3fda701da9004762,
   0x3fda27615a383fa3,
   0x3fd9f71d1f2baf03,
   0x3fd9d9bb32309743,
   0x3fd9c61f73a2cc62,
   0x3fd9b162148c2418,
   0x3fd99b2cbb4f66cf,
   0x3fd9832f2b620c69,
   0x3fd96921464fa922,
   0x3fd94cc74abeb13b,
   0x3fd92df0601bfe7a,
   0x3fd90c76efdf89da,
   0x3fd8e840d89a6f4b,
   0x3fd8c13f7d1b8737,
   0x3fd8976fb253c88e,
   0x3fd86ad98e2f5396,
   0x3fd83b901952cb99,
   0x3fd809b0e555b9ac,
   0x3fd7d56388ccd811,
   0x3fd79ed9021969a2,
   0x3fd7664b01adb919,
   0x3fd72bfd046beea2,
   0x3fd6f05bbba2a112,
   0x3fd6b38db0c8a697,
   0x3fd675e5e1675cb7,
   0x3fd637bb20fd3d11,
   0x3fd5f9a0f66b8887]

theorem record2684ChunkBits170Length2685 :
    (record2684ChunkBits1702685).length = 32 := by
  decide

theorem record2684ChunkSum1702685 :
    ((record2684ChunkBits1702685).map binary64Value2674).sum =
      (224496846147396767 : ℚ) / 18014398509481984 := by
  norm_num [record2684ChunkBits1702685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5472 through 5503,
decoded and summed as exact rationals. -/
def record2684ChunkBits1712685 : List Nat :=
  [0x3fd5cfddc636d031,
   0x3fd5b8007b2831a6,
   0x3fd5a6ab88b2e08d,
   0x3fd59462b8bbe463,
   0x3fd580dd748021b1,
   0x3fd56bd8733d3237,
   0x3fd5551735ad05b8,
   0x3fd53c67ba053280,
   0x3fd521a136aa9309,
   0x3fd504a462ef6080,
   0x3fd4e55b9f7f172e,
   0x3fd4c3bb00c7c20f,
   0x3fd49fc03d6f11e4,
   0x3fd4797282c3c7eb,
   0x3fd450e230d221d2,
   0x3fd426287f7c1920,
   0x3fd3f9670daf5e97,
   0x3fd3cac75b91ef0c,
   0x3fd39a7a30520fbb,
   0x3fd368bcf40a3e98,
   0x3fd335dd754df16c,
   0x3fd30205c0ad724c,
   0x3fd2cd7bcdfc3464,
   0x3fd29888bf9e7c24,
   0x3fd263a8502a6a84,
   0x3fd23f9a789e90b7,
   0x3fd22c424d61b3e0,
   0x3fd21cec224cb10b,
   0x3fd20cc7a3eb51d8,
   0x3fd1fb9875647ecb,
   0x3fd1e926dcabc244,
   0x3fd1d540c09dcf68]

theorem record2684ChunkBits171Length2685 :
    (record2684ChunkBits1712685).length = 32 := by
  decide

theorem record2684ChunkSum1712685 :
    ((record2684ChunkBits1712685).map binary64Value2674).sum =
      (179221775167760153 : ℚ) / 18014398509481984 := by
  norm_num [record2684ChunkBits1712685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5504 through 5535,
decoded and summed as exact rationals. -/
def record2684ChunkBits1722685 : List Nat :=
  [0x3fd1bfbce5161a5a,
   0x3fd1a879cefe7922,
   0x3fd18f5dfe1322cd,
   0x3fd174580ba6e35e,
   0x3fd1575eb05192aa,
   0x3fd13870b255a065,
   0x3fd11794be57c6b1,
   0x3fd0f4d92bd15fb8,
   0x3fd0d053ae64c889,
   0x3fd0aa20f506bb77,
   0x3fd0826437b63348,
   0x3fd05946b44f9fc8,
   0x3fd02efc626f7332,
   0x3fd003c49132685c,
   0x3fcfaf89085801c7,
   0x3fcf566dbeb57656,
   0x3fcefcb1a53d431d,
   0x3fcea32301859999,
   0x3fce654e2e35d8ce,
   0x3fce464d675b7829,
   0x3fce2b7d4049496b,
   0x3fce0f552f576d92,
   0x3fcdf17092d8e161,
   0x3fcdd172ca3632e5,
   0x3fcdaf0884f86ce5,
   0x3fcd89ed5ceab0a7,
   0x3fcd61e9eb3b6bae,
   0x3fcd36d42548691f,
   0x3fcd088f8c43bb92,
   0x3fccd70d33269fd4,
   0x3fcca24b9ddeb420,
   0x3fcc6a567c71a45a]

theorem record2684ChunkBits172Length2685 :
    (record2684ChunkBits1722685).length = 32 := by
  decide

theorem record2684ChunkSum1722685 :
    ((record2684ChunkBits1722685).map binary64Value2674).sum =
      (4456031033646475 : ℚ) / 562949953421312 := by
  norm_num [record2684ChunkBits1722685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5536 through 5567,
decoded and summed as exact rationals. -/
def record2684ChunkBits1732685 : List Nat :=
  [0x3fcc2f4644802c2a,
   0x3fcbf13fab1f6b52,
   0x3fcbb073009fcf1f,
   0x3fcb6d1b6f7dc17d,
   0x3fcb277e1f6b9aa0,
   0x3fcadffc66beef18,
   0x3fca96e598321f08,
   0x3fca4c884b9047cb,
   0x3fca0146810dd020,
   0x3fc9b58665014009,
   0x3fc969f35625f242,
   0x3fc9351a3e407fca,
   0x3fc91c5a320523fe,
   0x3fc904ef5ec1d8e7,
   0x3fc8ec642ada6a54,
   0x3fc8d265a8adc358,
   0x3fc8b6a7cdd7db17,
   0x3fc898e63d963e5f,
   0x3fc878e9195dd450,
   0x3fc856835926ea4a,
   0x3fc8319313c52bf6,
   0x3fc80a01a1ef7590,
   0x3fc7dfc39eb6075b,
   0x3fc7b2d8c7f6a695,
   0x3fc7834bc119f286,
   0x3fc75131ba194fcd,
   0x3fc71ca9fc723cd9,
   0x3fc6e5dd5f61efe4,
   0x3fc6acfda4729fe4,
   0x3fc67244bd28fd62,
   0x3fc63607f755a2e9,
   0x3fc5f87f2ededb0b]

theorem record2684ChunkBits173Length2685 :
    (record2684ChunkBits1732685).length = 32 := by
  decide

theorem record2684ChunkSum1732685 :
    ((record2684ChunkBits1732685).map binary64Value2674).sum =
      (224178208727791417 : ℚ) / 36028797018963968 := by
  norm_num [record2684ChunkBits1732685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5568 through 5599,
decoded and summed as exact rationals. -/
def record2684ChunkBits1742685 : List Nat :=
  [0x3fc5b9f20824ab94,
   0x3fc57ab1e6ec1da9,
   0x3fc53b1382b14ed1,
   0x3fc4fba450c00d22,
   0x3fc4ced82c763839,
   0x3fc4bb3cd8e212ab,
   0x3fc4a6ffc29942b9,
   0x3fc491d408a23277,
   0x3fc47b753223d3bd,
   0x3fc463a4a4b9c9ee,
   0x3fc44a2a153f86fc,
   0x3fc42ed7a3f4cbd4,
   0x3fc411887245e43d,
   0x3fc3f220dbeb958c,
   0x3fc3d08e91323b56,
   0x3fc3acc894bbe85b,
   0x3fc386cf1ee2e030,
   0x3fc35eab68ab32de,
   0x3fc3346f5fee7905,
   0x3fc308354626238b,
   0x3fc2da1f3af3be62,
   0x3fc2aa56b347b59c,
   0x3fc2790bddd316ea,
   0x3fc24685d999bcdd,
   0x3fc212eeb00e9162,
   0x3fc1de85de00e587,
   0x3fc1a98ecf6f3baf,
   0x3fc1744f9f002112,
   0x3fc13f3ca8f599d7,
   0x3fc11ad56b203683,
   0x3fc109dec34cad58,
   0x3fc0f860dd629753]

theorem record2684ChunkBits174Length2685 :
    (record2684ChunkBits1742685).length = 32 := by
  decide

theorem record2684ChunkSum1742685 :
    ((record2684ChunkBits1742685).map binary64Value2674).sum =
      (174471794052715339 : ℚ) / 36028797018963968 := by
  norm_num [record2684ChunkBits1742685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5600 through 5631,
decoded and summed as exact rationals. -/
def record2684ChunkBits1752685 : List Nat :=
  [0x3fc0e61ce1fe2e6b,
   0x3fc0d2daf060247b,
   0x3fc0be68296085e6,
   0x3fc0a896d35d5544,
   0x3fc09141da0b670f,
   0x3fc0784b9977539b,
   0x3fc05d9e09beb675,
   0x3fc0412ad17d1ad5,
   0x3fc022eb40da5633,
   0x3fc002e03705042b,
   0x3fbfc223e76760d9,
   0x3fbf7b1fac1da98d,
   0x3fbf30e0145b4000,
   0x3fbee39e4c247a95,
   0x3fbe939f6dc925e6,
   0x3fbe41337df75d90,
   0x3fbdeccd5b411880,
   0x3fbd96b68554dcd5,
   0x3fbd3f5685222b63,
   0x3fbce71c4bab83a6,
   0x3fbc8e7afe5ff370,
   0x3fbc3630bb8713d1,
   0x3fbbfb7c8b9e33d6,
   0x3fbbde7488c0588e,
   0x3fbbc08f1a9fa377,
   0x3fbba16561f29494,
   0x3fbb809bf7b09ee0,
   0x3fbb5ddfeb2c48d7,
   0x3fbb38e6aac1f658,
   0x3fbb1173ee826381,
   0x3fbae757addb38f2,
   0x3fbaba6e634fe527]

theorem record2684ChunkBits175Length2685 :
    (record2684ChunkBits1752685).length = 32 := by
  decide

theorem record2684ChunkSum1752685 :
    ((record2684ChunkBits1752685).map binary64Value2674).sum =
      (67868431737704507 : ℚ) / 18014398509481984 := by
  norm_num [record2684ChunkBits1752685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5632 through 5663,
decoded and summed as exact rationals. -/
def record2684ChunkBits1762685 : List Nat :=
  [0x3fba8aa126c89d51,
   0x3fba57e5a1abd40f,
   0x3fba223ddfc3b51f,
   0x3fb9e9b7ff984456,
   0x3fb9ae6dc48d1668,
   0x3fb970840caf12c7,
   0x3fb9302a2bc04dfc,
   0x3fb8ed992cbabbba,
   0x3fb8a91a6272d00e,
   0x3fb862fa86243350,
   0x3fb81b7f07229786,
   0x3fb7d2fe457dc594,
   0x3fb789d343102a00,
   0x3fb7405c5d5a8165,
   0x3fb6f73455adb06c,
   0x3fb6c8111f9bd9b9,
   0x3fb6af44e58608ad,
   0x3fb695c167831816,
   0x3fb67b3363735292,
   0x3fb65f5101f056b1,
   0x3fb641d78a1bc191,
   0x3fb6228b09e8c363,
   0x3fb6013b4d312205,
   0x3fb5ddc225391826,
   0x3fb5b8039b368849,
   0x3fb58fee01365701,
   0x3fb56579e4092c19,
   0x3fb538a9e0add659,
   0x3fb5098a5f6bea8b,
   0x3fb4d83136836629,
   0x3fb4a4bd360954e6,
   0x3fb46f559e36b7cb]

theorem record2684ChunkBits176Length2685 :
    (record2684ChunkBits1762685).length = 32 := by
  decide

theorem record2684ChunkSum1762685 :
    ((record2684ChunkBits1762685).map binary64Value2674).sum =
      (104558074623229441 : ℚ) / 36028797018963968 := by
  norm_num [record2684ChunkBits1762685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5664 through 5695,
decoded and summed as exact rationals. -/
def record2684ChunkBits1772685 : List Nat :=
  [0x3fb4382981315e1a,
   0x3fb3ff774a60f578,
   0x3fb3c57882a0af04,
   0x3fb38a6927a59512,
   0x3fb34e8fb53c2e8a,
   0x3fb312364ba878be,
   0x3fb2d5a9a599cc62,
   0x3fb29966d1d0afc2,
   0x3fb273d9a1760528,
   0x3fb25ee06627d9bd,
   0x3fb249524d86fcff,
   0x3fb232ebe52a76b8,
   0x3fb21b716a4238e3,
   0x3fb202ad0b5c464c,
   0x3fb1e86e6e77657a,
   0x3fb1cc8ed52abd24,
   0x3fb1aeefac970c84,
   0x3fb18f7ab3934854,
   0x3fb16e22059c49ac,
   0x3fb14ae00cb7ddc6,
   0x3fb125b75c565622,
   0x3fb0feb2770011d0,
   0x3fb0d5e3805f048d,
   0x3fb0ab63dcf19a13,
   0x3fb07f53c07503ee,
   0x3fb051d9abdc368c,
   0x3fb0232975e0f323,
   0x3fafe6db45849dba,
   0x3faf85b52d6fc010,
   0x3faf23534dfb1e46,
   0x3faec02e176313bf,
   0x3fae5cc20e676094]

theorem record2684ChunkBits177Length2685 :
    (record2684ChunkBits1772685).length = 32 := by
  decide

theorem record2684ChunkSum1772685 :
    ((record2684ChunkBits1772685).map binary64Value2674).sum =
      (317999201241313359 : ℚ) / 144115188075855872 := by
  norm_num [record2684ChunkBits1772685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5696 through 5727,
decoded and summed as exact rationals. -/
def record2684ChunkBits1782685 : List Nat :=
  [0x3fadf9d88cf32adb,
   0x3fadbe3f1885b528,
   0x3fad9ad0125fecfb,
   0x3fad766d8bcc01f3,
   0x3fad50ab81afd042,
   0x3fad292a6edd8e51,
   0x3facff94b2fda0a5,
   0x3facd39d6ea3fe4e,
   0x3faca507633ea6bf,
   0x3fac73a28dd91b9f,
   0x3fac3f4c5e6bd55d,
   0x3fac07efc3646730,
   0x3fabcd850cfed578,
   0x3fab9011abbff955,
   0x3fab4fa7cd0396ee,
   0x3fab0c65d8277112,
   0x3faac675ce75b133,
   0x3faa7e0c8f834c7d,
   0x3faa33690365e51c,
   0x3fa9e6dcc064a94e,
   0x3fa998b1e76120c5,
   0x3fa9493af659cc5f,
   0x3fa8f8d486db8c0c,
   0x3fa8a7dfad25f85f,
   0x3fa856c09725d512,
   0x3fa806181c9f530b,
   0x3fa7d737c07a881a,
   0x3fa7b999b11056b4,
   0x3fa79b383f216545,
   0x3fa77bbcd6b8eeb6,
   0x3fa75adafc00566d,
   0x3fa7384e60095827]

theorem record2684ChunkBits178Length2685 :
    (record2684ChunkBits1782685).length = 32 := by
  decide

theorem record2684ChunkSum1782685 :
    ((record2684ChunkBits1782685).map binary64Value2674).sum =
      (120142041206019241 : ℚ) / 72057594037927936 := by
  norm_num [record2684ChunkBits1782685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5728 through 5759,
decoded and summed as exact rationals. -/
def record2684ChunkBits1792685 : List Nat :=
  [0x3fa713d9b06fb5fc,
   0x3fa6ed4c42c454af,
   0x3fa6c4801a340847,
   0x3fa6995a10001e6e,
   0x3fa66bc9d8e363c7,
   0x3fa63bc9ea5171c2,
   0x3fa6095f42490063,
   0x3fa5d499141e4510,
   0x3fa59d905c4fdaf0,
   0x3fa564675d2051fb,
   0x3fa52949055b4242,
   0x3fa4ec6b64c9f55f,
   0x3fa4ae0ab88e8548,
   0x3fa46e61d722e0b0,
   0x3fa42db6bbc802f8,
   0x3fa3ec53eb9de98b,
   0x3fa3aa876b9e9fb9,
   0x3fa368a1a6cdeec8,
   0x3fa3272296c558d9,
   0x3fa3026f40237e0c,
   0x3fa2e9bc395e2b1d,
   0x3fa2d06b365d1d41,
   0x3fa2b637a8f5fe6a,
   0x3fa29ae521e4ac06,
   0x3fa27e3de8e432a7,
   0x3fa26011d06faffa,
   0x3fa2403ad9d0ecb9,
   0x3fa21e9b9468d271,
   0x3fa1fb1f39b472a5,
   0x3fa1d5b9ad7422a5,
   0x3fa1ae676455b179,
   0x3fa1852d335049da]

theorem record2684ChunkBits179Length2685 :
    (record2684ChunkBits1792685).length = 32 := by
  decide

theorem record2684ChunkSum1792685 :
    ((record2684ChunkBits1792685).map binary64Value2674).sum =
      (180913928245120511 : ℚ) / 144115188075855872 := by
  norm_num [record2684ChunkBits1792685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5760 through 5791,
decoded and summed as exact rationals. -/
def record2684ChunkBits1802685 : List Nat :=
  [0x3fa15a1809a1cf52,
   0x3fa12d3c9717cf1d,
   0x3fa0feb6e00aaae6,
   0x3fa0cea9c02a9c64,
   0x3fa09d415407489a,
   0x3fa06aad04b4cf0d,
   0x3fa0371cad7bcff0,
   0x3fa002c850a0c1fe,
   0x3f9f9bd6e344d3b5,
   0x3f9f318880e2ccc8,
   0x3f9ec72570e9d8cf,
   0x3f9e5d77aceb7415,
   0x3f9e24877a9e5a80,
   0x3f9dfbbcf8e38fb8,
   0x3f9dd1f76058c2e9,
   0x3f9da6ca0c82748e,
   0x3f9d79d556a91336,
   0x3f9d4ac48d818801,
   0x3f9d194bc2e63453,
   0x3f9ce52f5901390c,
   0x3f9cae415a75c577,
   0x3f9c7461a16fd64e,
   0x3f9c377dd2942e77,
   0x3f9bf7912fa61a10,
   0x3f9bb4a4456e8a3c,
   0x3f9b6ecc7800c85c,
   0x3f9b262b700c6baa,
   0x3f9adaee6b798b32,
   0x3f9a8d4d732110a9,
   0x3f9a3d917070e52b,
   0x3f99ebfe64153f03,
   0x3f9998e65f2132b2]

theorem record2684ChunkBits180Length2685 :
    (record2684ChunkBits1802685).length = 32 := by
  decide

theorem record2684ChunkSum1802685 :
    ((record2684ChunkBits1802685).map binary64Value2674).sum =
      (268598771323554699 : ℚ) / 288230376151711744 := by
  norm_num [record2684ChunkBits1802685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5792 through 5823,
decoded and summed as exact rationals. -/
def record2684ChunkBits1812685 : List Nat :=
  [0x3f9944a2b134cd8d,
   0x3f98ef921ae4ce43,
   0x3f989a177a0b2b15,
   0x3f984498633ff6af,
   0x3f97efb38de80bef,
   0x3f97c3bbff7fb29b,
   0x3f97a2203bb45b5f,
   0x3f977fbc29f76aec,
   0x3f975c3ac7c5c202,
   0x3f9737516814a226,
   0x3f9710be422c97cf,
   0x3f96e8466c0a6fda,
   0x3f96bdbbf55057f7,
   0x3f9690fbbefe6172,
   0x3f9661ed94c07cb5,
   0x3f9630842396af8e,
   0x3f95fcbcd0eaaec6,
   0x3f95c69f74e17cef,
   0x3f958e3dfa64e91a,
   0x3f9553b3e70671ac,
   0x3f951725cc869acf,
   0x3f94d8c0a571e817,
   0x3f9498bc14f6ec79,
   0x3f945753c2859184,
   0x3f9414c5dce04441,
   0x3f93d1590b7dd2ab,
   0x3f938d5819b25934,
   0x3f934910ead38762,
   0x3f9304d35cf4c6eb,
   0x3f92c11b10eb24ed,
   0x3f929f8165af7fcc,
   0x3f928419e84e7419]

theorem record2684ChunkBits181Length2685 :
    (record2684ChunkBits1812685).length = 32 := by
  decide

theorem record2684ChunkSum1812685 :
    ((record2684ChunkBits1812685).map binary64Value2674).sum =
      (196893124903957123 : ℚ) / 288230376151711744 := by
  norm_num [record2684ChunkBits1812685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5824 through 5855,
decoded and summed as exact rationals. -/
def record2684ChunkBits1822685 : List Nat :=
  [0x3f9268155663b993,
   0x3f924b3120f071f0,
   0x3f922d32e5c6b650,
   0x3f920de76e4c0bfe,
   0x3f91ed20e295c223,
   0x3f91cabbb0d3186e,
   0x3f91a69cd07b5ef7,
   0x3f9180b1d27f4ba0,
   0x3f9158f0d661ea57,
   0x3f912f5866ad4c48,
   0x3f9103ef3f04da11,
   0x3f90d6c3fdcecb2f,
   0x3f90a7ecc3286b70,
   0x3f907786be90074b,
   0x3f9045b79d1935cc,
   0x3f9012a85d33dc56,
   0x3f8fbd0d458871ad,
   0x3f8f530c4c876122,
   0x3f8ee7bd25c35c5c,
   0x3f8e7b957d129d60,
   0x3f8e0f0fac0123c4,
   0x3f8da2a8fc4165c3,
   0x3f8d3940827512bb,
   0x3f8d040b0e869c44,
   0x3f8cd77c604ca5c6,
   0x3f8ca9f65b260517,
   0x3f8c7b12246c34fa,
   0x3f8c4a75bcab2c8f,
   0x3f8c17d29e55bc74,
   0x3f8be2e297c55c60,
   0x3f8bab6f9c8d6794,
   0x3f8b7150fc3f7ca5]

theorem record2684ChunkBits182Length2685 :
    (record2684ChunkBits1822685).length = 32 := by
  decide

theorem record2684ChunkSum1822685 :
    ((record2684ChunkBits1822685).map binary64Value2674).sum =
      (143984124539820791 : ℚ) / 288230376151711744 := by
  norm_num [record2684ChunkBits1822685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5856 through 5887,
decoded and summed as exact rationals. -/
def record2684ChunkBits1832685 : List Nat :=
  [0x3f8b346b7488b237,
   0x3f8af4b1194b1282,
   0x3f8ab2211694a024,
   0x3f8a6cc74ffabb98,
   0x3f8a24bbe0769d96,
   0x3f89da227d6de0bc,
   0x3f898d29bf269cf1,
   0x3f893e0c06bb5543,
   0x3f88ed0d4dff15bf,
   0x3f889a73666c14a3,
   0x3f88468f565a37e3,
   0x3f87f1b81b06f2f6,
   0x3f879c496fa6d2a8,
   0x3f8746a28297fbee,
   0x3f86f1249a4b0ccd,
   0x3f86a0dbe074a514,
   0x3f8675fa31a6bb91,
   0x3f86521e1f77fca0,
   0x3f862d825ce1fd12,
   0x3f8607d76c3e5549,
   0x3f85e0d7ddd4faf8,
   0x3f85b84763d37068,
   0x3f858df020876e16,
   0x3f8561a8d7111701,
   0x3f853352b4633b84,
   0x3f8502d958697358,
   0x3f84d032bec964bc,
   0x3f849b5f0a4efc56,
   0x3f84646835d0bc8c,
   0x3f842b61acfd53f0,
   0x3f83f067cf2bf1b1,
   0x3f83b3a062a5c658]

theorem record2684ChunkBits183Length2685 :
    (record2684ChunkBits1832685).length = 32 := by
  decide

theorem record2684ChunkSum1832685 :
    ((record2684ChunkBits1832685).map binary64Value2674).sum =
      (208188712402106915 : ℚ) / 576460752303423488 := by
  norm_num [record2684ChunkBits1832685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5888 through 5919,
decoded and summed as exact rationals. -/
def record2684ChunkBits1842685 : List Nat :=
  [0x3f837538569d0ea3,
   0x3f83356194034eda,
   0x3f82f455deff71bf,
   0x3f82b254672d9c09,
   0x3f826fa0e1b7a7c1,
   0x3f822c8294fc14a6,
   0x3f81e94356be6f55,
   0x3f81a62e7e25fe52,
   0x3f816966ed388f2a,
   0x3f8146fc79c4ba5b,
   0x3f812a3854101bfd,
   0x3f810cdf92459d1f,
   0x3f80eeb598a110de,
   0x3f80cf8599c84a79,
   0x3f80af21fdb0d1bd,
   0x3f808d621a169cad,
   0x3f806a271059bc41,
   0x3f80455a0d5c392a,
   0x3f801eec4c3ccc23,
   0x3f7fedae008bef29,
   0x3f7f9a3650e5b64e,
   0x3f7f43829d60becf,
   0x3f7ee9b2697cc1fb,
   0x3f7e8cf2e09c9d88,
   0x3f7e2d7def773ada,
   0x3f7dcb9a31da9bc1,
   0x3f7d679b08e85f6a,
   0x3f7d01d5d69494c6,
   0x3f7c9aac504681f6,
   0x3f7c3286e314bc8d,
   0x3f7bc9d33a61f8b6,
   0x3f7b6102b32a0b0b]

theorem record2684ChunkBits184Length2685 :
    (record2684ChunkBits1842685).length = 32 := by
  decide

theorem record2684ChunkSum1842685 :
    ((record2684ChunkBits1842685).map binary64Value2674).sum =
      (148191973905075119 : ℚ) / 576460752303423488 := by
  norm_num [record2684ChunkBits1842685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5920 through 5951,
decoded and summed as exact rationals. -/
def record2684ChunkBits1852685 : List Nat :=
  [0x3f7af888bc1fcc75,
   0x3f7a9d57f0949cc3,
   0x3f7a66a4dea8b541,
   0x3f7a38f95a70dda3,
   0x3f7a0a6ad4422f9c,
   0x3f79da9ce1b3a64d,
   0x3f79a93f286feac4,
   0x3f79760c9ffb898e,
   0x3f7940c7c7108902,
   0x3f7909423c4b947a,
   0x3f78cf59ff3e5891,
   0x3f7892f96e1fd240,
   0x3f7854171dd20fae,
   0x3f7812b58ff6c647,
   0x3f77cee2ca75f0d8,
   0x3f7788b7d3678749,
   0x3f774059013f9947,
   0x3f76f5f36e4577ef,
   0x3f76a9bc06db3d39,
   0x3f765bf0cd8accc5,
   0x3f760cd6dd3a696b,
   0x3f75bcb9672686a2,
   0x3f756be89ff64f58,
   0x3f751ab89ce345a6,
   0x3f74c980222c35b4,
   0x3f7478976465587c,
   0x3f7434a1cea291e9,
   0x3f74095deb8b9a87,
   0x3f73e5410bbf1480,
   0x3f73c076e570d498,
   0x3f739aba02461474,
   0x3f7373ce29631480]

theorem record2684ChunkBits185Length2685 :
    (record2684ChunkBits1852685).length = 32 := by
  decide

theorem record2684ChunkSum1852685 :
    ((record2684ChunkBits1852685).map binary64Value2674).sum =
      (208965591897098661 : ℚ) / 1152921504606846976 := by
  norm_num [record2684ChunkBits1852685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5952 through 5983,
decoded and summed as exact rationals. -/
def record2684ChunkBits1862685 : List Nat :=
  [0x3f734b7fef2bbd58,
   0x3f7321a19854fa83,
   0x3f72f610fc03ca11,
   0x3f72c8b56074f55f,
   0x3f72997f7426debf,
   0x3f7268692a90a1c4,
   0x3f7235757f3a933f,
   0x3f7200b021c0c669,
   0x3f71ca2d0cf517cd,
   0x3f7192080b033c09,
   0x3f715864282ca711,
   0x3f711d6d49088418,
   0x3f70e150e4893388,
   0x3f70a443b58abe87,
   0x3f70667f0d1b0264,
   0x3f70283fe3bd95b8,
   0x3f6fd38bf926f9d7,
   0x3f6f56a5fc1eecb2,
   0x3f6eda530287b1ca,
   0x3f6e7604b337ed10,
   0x3f6e3240f259523e,
   0x3f6df9bcd77ab711,
   0x3f6dc033ba93a772,
   0x3f6d853d441a28bd,
   0x3f6d487f34bc6364,
   0x3f6d09acecb35d58,
   0x3f6cc8825fe3e7f9,
   0x3f6c84cd2022b389,
   0x3f6c3e690e9c7432,
   0x3f6bf540491c77ff,
   0x3f6ba94aece3732d,
   0x3f6b5a8eb376c3f9]

theorem record2684ChunkBits186Length2685 :
    (record2684ChunkBits1862685).length = 32 := by
  decide

theorem record2684ChunkSum1862685 :
    ((record2684ChunkBits1862685).map binary64Value2674).sum =
      (146555879449086427 : ℚ) / 1152921504606846976 := by
  norm_num [record2684ChunkBits1862685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 5984 through 6015,
decoded and summed as exact rationals. -/
def record2684ChunkBits1872685 : List Nat :=
  [0x3f6b091e991bc38f,
   0x3f6ab51ac6ae9bdd,
   0x3f6a5ead0bfdf05b,
   0x3f6a060b38fe71c1,
   0x3f69ab75080f5bdb,
   0x3f694f3317f997ab,
   0x3f68f195d19341c9,
   0x3f6892f43a2c7804,
   0x3f6833aab3dccb41,
   0x3f67d419ace58484,
   0x3f6774a43f99afd0,
   0x3f6715aec4b657bd,
   0x3f66cc2da280e03d,
   0x3f66976112d18220,
   0x3f666b597b5e67e3,
   0x3f663e8e3cbd64f4,
   0x3f6610b20ff25ccb,
   0x3f65e18251fdebf7,
   0x3f65b0c6cd85e03a,
   0x3f657e4db0dffde8,
   0x3f6549f273630a51,
   0x3f65139b4cc7e77f,
   0x3f64db3921b39dc6,
   0x3f64a0c750c62fb3,
   0x3f64644b637940b1,
   0x3f6425d4a5b2f1b2,
   0x3f63e57ba679221f,
   0x3f63a361a3ae3d8a,
   0x3f635fafe23f3a45,
   0x3f631a9817d1a121,
   0x3f62d4515a30e5fe,
   0x3f628d170f62e7e2]

theorem record2684ChunkBits187Length2685 :
    (record2684ChunkBits1872685).length = 32 := by
  decide

theorem record2684ChunkSum1872685 :
    ((record2684ChunkBits1872685).map binary64Value2674).sum =
      (6317079563606199 : ℚ) / 72057594037927936 := by
  norm_num [record2684ChunkBits1872685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6016 through 6047,
decoded and summed as exact rationals. -/
def record2684ChunkBits1882685 : List Nat :=
  [0x3f62452a8d8e21c1,
   0x3f61fcd0f8b1808b,
   0x3f61b4524a09cc03,
   0x3f616bf84d505d14,
   0x3f61240d94169209,
   0x3f60eec31fd273bd,
   0x3f60c60b9ca9b4f6,
   0x3f60a41c73331efc,
   0x3f60819c45619138,
   0x3f605e51f71135b5,
   0x3f603a0c6dc1b197,
   0x3f6014a281822033,
   0x3f5fdbdf93ed3992,
   0x3f5f8bb3a91a4e54,
   0x3f5f389c6c57c9a1,
   0x3f5ee2852f5dd24d,
   0x3f5e8968d9614240,
   0x3f5e2d5088a4b123,
   0x3f5dce545e789f55,
   0x3f5d6c9a24f047ea,
   0x3f5d08546c2d0fe1,
   0x3f5ca1c18ccc7ecb,
   0x3f5c392a91b7ae8d,
   0x3f5bcee20b280d54,
   0x3f5b6342cc648a48,
   0x3f5af6ae9589c4ce,
   0x3f5a898caaa3bb8d,
   0x3f5a1c485982e71d,
   0x3f59af4f6ffdfefc,
   0x3f5945d6bd4e9a75,
   0x3f58f662827544a9,
   0x3f58b7f0e47cfd82]

theorem record2684ChunkBits188Length2685 :
    (record2684ChunkBits1882685).length = 32 := by
  decide

theorem record2684ChunkSum1882685 :
    ((record2684ChunkBits1882685).map binary64Value2674).sum =
      (274408928333632003 : ℚ) / 4611686018427387904 := by
  norm_num [record2684ChunkBits1882685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6048 through 6079,
decoded and summed as exact rationals. -/
def record2684ChunkBits1892685 : List Nat :=
  [0x3f5883e612a8b473,
   0x3f584f060052458f,
   0x3f5818fd6793588e,
   0x3f57e184e8897509,
   0x3f57a8611af2baad,
   0x3f576d5d8ea00103,
   0x3f5730549ddb1d28,
   0x3f56f12c847450aa,
   0x3f56afd73c9c3e23,
   0x3f566c523a5a0900,
   0x3f5626a609b37b00,
   0x3f55dee5d363ccf8,
   0x3f55952ecbb6c61d,
   0x3f5549a78e579cda,
   0x3f54fc7f66e84ca4,
   0x3f54adf03efa3d9d,
   0x3f545e35ba0fae7b,
   0x3f540d9255757476,
   0x3f53bc4ddddc7110,
   0x3f536ab4063fa3e2,
   0x3f5319136a94b70c,
   0x3f52c7bc6f69a754,
   0x3f527c2fd5d73ce4,
   0x3f524077e5743631,
   0x3f5211159bf65979,
   0x3f51e99b76480bcc,
   0x3f51c186220b795b,
   0x3f519898ef4bd0c4,
   0x3f516ea03ed6a0f8,
   0x3f51437167baf497,
   0x3f5116e6d8c5d389,
   0x3f50e8e5e8aa8774]

theorem record2684ChunkBits189Length2685 :
    (record2684ChunkBits1892685).length = 32 := by
  decide

theorem record2684ChunkSum1892685 :
    ((record2684ChunkBits1892685).map binary64Value2674).sum =
      (92591303522356059 : ℚ) / 2305843009213693952 := by
  norm_num [record2684ChunkBits1892685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6080 through 6111,
decoded and summed as exact rationals. -/
def record2684ChunkBits1902685 : List Nat :=
  [0x3f50b95ca7c8fa0a,
   0x3f508841c03db453,
   0x3f5055943d764e11,
   0x3f50215b3e12bc0e,
   0x3f4fd74b2512b0f1,
   0x3f4f69129570f65d,
   0x3f4ef846684cf82a,
   0x3f4e852c95232b48,
   0x3f4e101637da55ea,
   0x3f4d995e41bb9be7,
   0x3f4d216815109324,
   0x3f4ca89e0ce2b351,
   0x3f4c2f6ff24dcf72,
   0x3f4bb651610128b8,
   0x3f4b3db81cdba7c5,
   0x3f4ad26553ceba58,
   0x3f4a7932620cd009,
   0x3f4a31bea6f4a97e,
   0x3f49f6360af02a72,
   0x3f49b9cdd60a3a24,
   0x3f497c2f524ab918,
   0x3f493d10aec247ee,
   0x3f48fc35618f7611,
   0x3f48b9683edc73d9,
   0x3f4874840a9516ab,
   0x3f482d703c3354d3,
   0x3f47e420c897185a,
   0x3f479895c8d33137,
   0x3f474adb024b39c6,
   0x3f46fb07e0201bb8,
   0x3f46a93db1f3641a,
   0x3f4655a77fb71e6e]

theorem record2684ChunkBits190Length2685 :
    (record2684ChunkBits1902685).length = 32 := by
  decide

theorem record2684ChunkSum1902685 :
    ((record2684ChunkBits1902685).map binary64Value2674).sum =
      (246507806861239399 : ℚ) / 9223372036854775808 := by
  norm_num [record2684ChunkBits1902685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6112 through 6143,
decoded and summed as exact rationals. -/
def record2684ChunkBits1912685 : List Nat :=
  [0x3f460079b1a77aac,
   0x3f45a9f0fcbba2fe,
   0x3f455253af4913dd,
   0x3f44f9e5c3907a4b,
   0x3f44a0f30ebca7c8,
   0x3f4447cc6570b41d,
   0x3f43eec55ad74e33,
   0x3f439632f164111e,
   0x3f434ad3ba65b6ec,
   0x3f4308db3cd74fab,
   0x3f42d38c3d1d61b3,
   0x3f42a7236aca3c29,
   0x3f427a1aec3ca4fa,
   0x3f424c3500dc3b01,
   0x3f421d3d49009343,
   0x3f41ed092835100b,
   0x3f41bb734d6a0df5,
   0x3f418861f49ccf00,
   0x3f4153c485934625,
   0x3f411d9366a0e986,
   0x3f40e5cfb67b5a6a,
   0x3f40ac82f01e64f1,
   0x3f4071be7b6123f2,
   0x3f40359b2c878452,
   0x3f3ff071697785c0,
   0x3f3f737a0a130378,
   0x3f3ef4a74a523ba1,
   0x3f3e7459fe5a71e1,
   0x3f3df2fb41f05097,
   0x3f3d70fae88c5e59,
   0x3f3ceecddc2c5bdd,
   0x3f3c6cec6ca50725]

theorem record2684ChunkBits191Length2685 :
    (record2684ChunkBits1912685).length = 32 := by
  decide

theorem record2684ChunkSum1912685 :
    ((record2684ChunkBits1912685).map binary64Value2674).sum =
      (160925041324238681 : ℚ) / 9223372036854775808 := by
  norm_num [record2684ChunkBits1912685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6144 through 6175,
decoded and summed as exact rationals. -/
def record2684ChunkBits1922685 : List Nat :=
  [0x3f3bebd091911e6a,
   0x3f3b82f3b68bd1f3,
   0x3f3b2216228abf80,
   0x3f3ad3237692801b,
   0x3f3a915c87b9b220,
   0x3f3a4eb5369d3c40,
   0x3f3a0ad650750079,
   0x3f39c57656ebb6d7,
   0x3f397e5a03839570,
   0x3f39354d9a21aa92,
   0x3f38ea2df638e546,
   0x3f389ce512eae9e7,
   0x3f384d69c1adc5fe,
   0x3f37fbbf3d9da384,
   0x3f37a7f49f8e4182,
   0x3f375224366402ce,
   0x3f36fa72c6d5212a,
   0x3f36a10eb5978e1e,
   0x3f36462f1f24fbca,
   0x3f35ea12e041ce7c,
   0x3f358d001b7bd90b,
   0x3f352f41e9be8712,
   0x3f34d1279802e56b,
   0x3f34730465b65c9d,
   0x3f34152dcada9801,
   0x3f33b7fa397e6513,
   0x3f336fe5bc4d10b3,
   0x3f33297a33efe8c3,
   0x3f32ef9fa93b9ff1,
   0x3f32bf6bc3c03e4e,
   0x3f328e9b34e9c50d,
   0x3f325cf13303c35f]

theorem record2684ChunkBits192Length2685 :
    (record2684ChunkBits1922685).length = 32 := by
  decide

theorem record2684ChunkSum1922685 :
    ((record2684ChunkBits1922685).map binary64Value2674).sum =
      (207270766796802961 : ℚ) / 18446744073709551616 := by
  norm_num [record2684ChunkBits1922685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6176 through 6207,
decoded and summed as exact rationals. -/
def record2684ChunkBits1932685 : List Nat :=
  [0x3f322a3a9ce0b788,
   0x3f31f64e9329fe35,
   0x3f31c10988dce72a,
   0x3f318a53be9b6eee,
   0x3f31521ec15a0076,
   0x3f3118652fd548ed,
   0x3f30dd2a67b0cecd,
   0x3f30a07a1d56776c,
   0x3f306267e14ab02c,
   0x3f30230e954d384a,
   0x3f2fc51fa67667f7,
   0x3f2f42268ea59e07,
   0x3f2ebd8bfe590b1c,
   0x3f2e37b35d028a79,
   0x3f2db107d55212e8,
   0x3f2d29fabb4c967e,
   0x3f2ca301e322f486,
   0x3f2c1c95eaa49edf,
   0x3f2b995ea97ed83d,
   0x3f2b352e4718c2e1,
   0x3f2acfa9b619b816,
   0x3f2a7b9d22bed1ea,
   0x3f2a35928cb32f91,
   0x3f29eeb0bf9a14ec,
   0x3f29a6a3ca1c3cd9,
   0x3f295d2563aeda97,
   0x3f2911fde869a8c6,
   0x3f28c4fd2369fe1c,
   0x3f2876037fea3038,
   0x3f2824fe742c7d88,
   0x3f27d1e825fcc63e,
   0x3f277cc6edb2a2ba]

theorem record2684ChunkBits193Length2685 :
    (record2684ChunkBits1932685).length = 32 := by
  decide

theorem record2684ChunkSum1932685 :
    ((record2684ChunkBits1932685).map binary64Value2674).sum =
      (264670827216314065 : ℚ) / 36893488147419103232 := by
  norm_num [record2684ChunkBits1932685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6208 through 6239,
decoded and summed as exact rationals. -/
def record2684ChunkBits1942685 : List Nat :=
  [0x3f2725acbc193456,
   0x3f26ccb667190ce6,
   0x3f26720ae074fcfe,
   0x3f2615da59638e9b,
   0x3f25b85d555100ac,
   0x3f2559d3adaaf713,
   0x3f24fa8388379718,
   0x3f249ab89b460d5f,
   0x3f243ac22078bfb7,
   0x3f23daf2439a6e7c,
   0x3f237b9d18433540,
   0x3f2322d64e1f5e6f,
   0x3f22db4beb35c620,
   0x3f2292d959455444,
   0x3f22566e33e2886d,
   0x3f222412e6d3652f,
   0x3f21f1255bb6f43b,
   0x3f21bd6c289ef828,
   0x3f2188b776c1c34b,
   0x3f2152e1c9fd994d,
   0x3f211bcacc7c1a89,
   0x3f20e35dc1d121ab,
   0x3f20a98efde907b5,
   0x3f206e5b9ee96824,
   0x3f2031c930531fba,
   0x3f1fe7ca74f162e8,
   0x3f1f698981e88394,
   0x3f1ee90764d5288f,
   0x3f1e66889709fcf4,
   0x3f1de25cdd713031,
   0x3f1d5cdde44cd36a,
   0x3f1cd66dc94b47e9]

theorem record2684ChunkBits194Length2685 :
    (record2684ChunkBits1942685).length = 32 := by
  decide

theorem record2684ChunkSum1942685 :
    ((record2684ChunkBits1942685).map binary64Value2674).sum =
      (330972387865061089 : ℚ) / 73786976294838206464 := by
  norm_num [record2684ChunkBits1942685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6240 through 6271,
decoded and summed as exact rationals. -/
def record2684ChunkBits1952685 : List Nat :=
  [0x3f1c4f7595bfa89c,
   0x3f1bc863aaa48b4e,
   0x3f1b41aa57d5cfea,
   0x3f1abbbdb477decb,
   0x3f1a4507b86fb159,
   0x3f19dfd5afc4cfb5,
   0x3f19796ac4ba8b5b,
   0x3f1923684de702a7,
   0x3f18dbb43b7297a5,
   0x3f18933c97d2132c,
   0x3f1849b3ca4ddb72,
   0x3f17fed981238ae1,
   0x3f17b27be4bd559b,
   0x3f1764702afd0875,
   0x3f17149b8b82a583,
   0x3f16c2efb27a98ac,
   0x3f166f6a56de24c2,
   0x3f161a14b22bf987,
   0x3f15c302ddda6e90,
   0x3f156a531a382abe,
   0x3f15102d01e40f1c,
   0x3f14b4c0ac810a5a,
   0x3f145845c2d263b6,
   0x3f13fafa860a37d9,
   0x3f139d22cbbdad9b,
   0x3f133f0724c76f53,
   0x3f12e0f34c40e966,
   0x3f1283352f93c283,
   0x3f12261c14117dea,
   0x3f11d7c10c653801,
   0x3f1190ecd1013d42,
   0x3f1149488f406e3e]

theorem record2684ChunkBits195Length2685 :
    (record2684ChunkBits1952685).length = 32 := by
  decide

theorem record2684ChunkSum1952685 :
    ((record2684ChunkBits1952685).map binary64Value2674).sum =
      (12673267132687199 : ℚ) / 4611686018427387904 := by
  norm_num [record2684ChunkBits1952685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6272 through 6303,
decoded and summed as exact rationals. -/
def record2684ChunkBits1962685 : List Nat :=
  [0x3f110cb8b2b3202d,
   0x3f10da385e7dd04e,
   0x3f10a73713a8a87e,
   0x3f107380f4672fa3,
   0x3f103eeb40774b9a,
   0x3f1009553bb5918e,
   0x3f0fa545e575b8c7,
   0x3f0f3586c09736d9,
   0x3f0ec35beeaae4a6,
   0x3f0e4ec4a8c923f4,
   0x3f0dd7cfb5b8ecf8,
   0x3f0d5e9a81c1269c,
   0x3f0ce35018e531a4,
   0x3f0c662807e09713,
   0x3f0be7652776f92d,
   0x3f0b6754550e880c,
   0x3f0ae64b1affaf1f,
   0x3f0a64a64a9877e1,
   0x3f09e2c889884df9,
   0x3f0961190fd811ba,
   0x3f08e00192cca771,
   0x3f085fecf3bc1ebb,
   0x3f07f9d885212fa7,
   0x3f0797bae701e7ce,
   0x3f07348cb6ee5b7a,
   0x3f06e02e04a0208d,
   0x3f0699cdd268013d,
   0x3f0652c68bbfbc46,
   0x3f060ad3b5c536fe,
   0x3f05c1bd3562665c,
   0x3f057758a1b2ea5d,
   0x3f052b81fbda6ce1]

theorem record2684ChunkBits196Length2685 :
    (record2684ChunkBits1962685).length = 32 := by
  decide

theorem record2684ChunkSum1962685 :
    ((record2684ChunkBits1962685).map binary64Value2674).sum =
      (61440825527913711 : ℚ) / 36893488147419103232 := by
  norm_num [record2684ChunkBits1962685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6304 through 6335,
decoded and summed as exact rationals. -/
def record2684ChunkBits1972685 : List Nat :=
  [0x3f04de2406387c67,
   0x3f048f34e51d163a,
   0x3f043eb5ac068e55,
   0x3f03ecb1d06ab86e,
   0x3f03993e85ff5672,
   0x3f03447a07ed7698,
   0x3f02ee8ad1d6351d,
   0x3f02979ecb134a84,
   0x3f023fea662e9d3b,
   0x3f01e7a7b631b141,
   0x3f018f157b2053f2,
   0x3f0136764df5f009,
   0x3f00de0f4ab831f2,
   0x3f0086271423a48c,
   0x3f002fdf94391bd4,
   0x3effdaea6420bddb,
   0x3eff548028aa3e30,
   0x3efeccb639cf5cd1,
   0x3efe5882c73e7a79,
   0x3efdf78d413efb50,
   0x3efd95c304ebc3cd,
   0x3efd32cac355cb5d,
   0x3efcce5bca664d40,
   0x3efc683feb014b13,
   0x3efc004977692221,
   0x3efb965e72195ec4,
   0x3efb2a73fc64242d,
   0x3efabc8db146321a,
   0x3efa4cbcde2196f4,
   0x3ef9db1f9ea93d4f,
   0x3ef967dfe0907fee,
   0x3ef8f33252d5c354]

theorem record2684ChunkBits197Length2685 :
    (record2684ChunkBits1972685).length = 32 := by
  decide

theorem record2684ChunkSum1972685 :
    ((record2684ChunkBits1972685).map binary64Value2674).sum =
      (292531250813483651 : ℚ) / 295147905179352825856 := by
  norm_num [record2684ChunkBits1972685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6336 through 6367,
decoded and summed as exact rationals. -/
def record2684ChunkBits1982685 : List Nat :=
  [0x3ef87d5543e13635,
   0x3ef8068f71159735,
   0x3ef78f2ec9f9166d,
   0x3ef7178728bc3ac2,
   0x3ef69ff11d72ffa4,
   0x3ef628c880992d45,
   0x3ef5b26aa6b5cde3,
   0x3ef544439b7f421d,
   0x3ef4ea3a3c475fd9,
   0x3ef48f32e196180d,
   0x3ef4334c727c7451,
   0x3ef3e43ab06d70f5,
   0x3ef3a23179fcfe67,
   0x3ef35fa8a0aee7c6,
   0x3ef31c61b0fd00d4,
   0x3ef2d82e3693c8cc,
   0x3ef292ec17e7beba,
   0x3ef24c7ecd4798b5,
   0x3ef204d6c85ca9f9,
   0x3ef1bbee65b4fb14,
   0x3ef171c977c89677,
   0x3ef12674bc5938df,
   0x3ef0da053fac92f8,
   0x3ef08c97b0a263dd,
   0x3ef03e4fa82ec0d0,
   0x3eefdeadcca35c0a,
   0x3eef3fb90c8749bd,
   0x3eeea028567a0864,
   0x3eee006a4e05a939,
   0x3eed60f39cda5ef9,
   0x3eecc23c08f711dd,
   0x3eec24bda2c4895a]

theorem record2684ChunkBits198Length2685 :
    (record2684ChunkBits1982685).length = 32 := by
  decide

theorem record2684ChunkSum1982685 :
    ((record2684ChunkBits1982685).map binary64Value2674).sum =
      (42454943251858735 : ℚ) / 73786976294838206464 := by
  norm_num [record2684ChunkBits1982685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6368 through 6399,
decoded and summed as exact rationals. -/
def record2684ChunkBits1992685 : List Nat :=
  [0x3eeb9a2b4c140d01,
   0x3eeb218da7d3c3f3,
   0x3eeaa7b87d71c84d,
   0x3eea2cd0c7893142,
   0x3ee9c28349ff7a8d,
   0x3ee969a53c188ecb,
   0x3ee91034fb0cbc11,
   0x3ee8b5da0e004a07,
   0x3ee85a59ebd81301,
   0x3ee7fd8a53a3397a,
   0x3ee79f4838d2a06e,
   0x3ee73f8170ed619a,
   0x3ee6de30a9764dc6,
   0x3ee67b5cc4c28625,
   0x3ee617181bc68117,
   0x3ee5b17fa968b7c1,
   0x3ee54aba23441513,
   0x3ee4e2f7031ddf9f,
   0x3ee47a6d83c8af8e,
   0x3ee4115b93a86e88,
   0x3ee3a804bea5b48d,
   0x3ee33eb1110ecbaa,
   0x3ee2d5ac3994aeff,
   0x3ee26d43986368d0,
   0x3ee205c5cd060dbb,
   0x3ee1aff3dd8ce886,
   0x3ee16026cdcaf356,
   0x3ee10f9f3b9caf57,
   0x3ee0be767065b882,
   0x3ee077e378ecdcba,
   0x3ee03cd78b779754,
   0x3ee0017be240ef12]

theorem record2684ChunkBits199Length2685 :
    (record2684ChunkBits1992685).length = 32 := by
  decide

theorem record2684ChunkSum1992685 :
    ((record2684ChunkBits1992685).map binary64Value2674).sum =
      (193470726629528727 : ℚ) / 590295810358705651712 := by
  norm_num [record2684ChunkBits1992685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6400 through 6431,
decoded and summed as exact rationals. -/
def record2684ChunkBits2002685 : List Nat :=
  [0x3edf8b251035ec4a,
   0x3edf11ee4f550360,
   0x3ede97200310752d,
   0x3ede1a8fdece0f6e,
   0x3edd9c2943aa141f,
   0x3edd1be7fb8011c1,
   0x3edc99d758f4bf0b,
   0x3edc1611364bbc0b,
   0x3edb90bcd8e8959e,
   0x3edb0a0dbe7bbf94,
   0x3eda8242580b74ec,
   0x3ed9f9a2b64b4bbc,
   0x3ed9707f2a11b3e3,
   0x3ed8e72edb33d218,
   0x3ed85e0e6cdf500b,
   0x3ed7d57e970a9260,
   0x3ed74de1f33aeeb7,
   0x3ed6c79c673021dd,
   0x3ed65f0a51ba3865,
   0x3ed5f6cb13ba116b,
   0x3ed58db296de4a49,
   0x3ed523e2ec3b7166,
   0x3ed4c767ab132adc,
   0x3ed479f6c3d0ff37,
   0x3ed42c34a4ba258c,
   0x3ed3ddcb94924dda,
   0x3ed38e8f2b57bb2c,
   0x3ed33e60942e9d4c,
   0x3ed2ed26c4255d7c,
   0x3ed29ad66a33dcad,
   0x3ed2476e8b3a0765,
   0x3ed1f2f7eabac87c]

theorem record2684ChunkBits200Length2685 :
    (record2684ChunkBits2002685).length = 32 := by
  decide

theorem record2684ChunkSum2002685 :
    ((record2684ChunkBits2002685).map binary64Value2674).sum =
      (217105455967414665 : ℚ) / 1180591620717411303424 := by
  norm_num [record2684ChunkBits2002685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6432 through 6463,
decoded and summed as exact rationals. -/
def record2684ChunkBits2012685 : List Nat :=
  [0x3ed19d845f948c70,
   0x3ed1472e186ed19f,
   0x3ed0f016d3071a49,
   0x3ed0986708fc29c9,
   0x3ed0404d1443f058,
   0x3ecfcff89a176f24,
   0x3ecf1f5844e11d10,
   0x3ece6f2e935e0469,
   0x3ecdbff5499ea1bd,
   0x3ecd122860ac40a1,
   0x3ecc6e539955fcb7,
   0x3ecbe90b0cddc5eb,
   0x3ecb62ab43a67317,
   0x3ecadb569a414ad2,
   0x3eca533a41bdc0ad,
   0x3ec9dbaf8c0edafe,
   0x3ec9777f3f6ea196,
   0x3ec91304db3cfb9b,
   0x3ec8adcb503ae568,
   0x3ec8479d3a574831,
   0x3ec7e0565da26a2d,
   0x3ec777d9ace3752a,
   0x3ec70e1b3c8b7801,
   0x3ec6a31bf54e1fb0,
   0x3ec636e8cb2157bf,
   0x3ec5c999dc971701,
   0x3ec55b517f36b334,
   0x3ec4ec3b3cc273d6,
   0x3ec47c8ac4abca8b,
   0x3ec40c7ad46092db,
   0x3ec39c4c189a2eb2,
   0x3ec32c44096e6bc6]

theorem record2684ChunkBits201Length2685 :
    (record2684ChunkBits2012685).length = 32 := by
  decide

theorem record2684ChunkSum2012685 :
    ((record2684ChunkBits2012685).map binary64Value2674).sum =
      (237128216379294621 : ℚ) / 2361183241434822606848 := by
  norm_num [record2684ChunkBits2012685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6464 through 6495,
decoded and summed as exact rationals. -/
def record2684ChunkBits2022685 : List Nat :=
  [0x3ec2bcabfaf868a8,
   0x3ec24dcf5e5c6bf9,
   0x3ec1dffafbc55c92,
   0x3ec17eac0c265c64,
   0x3ec129df8c5513e0,
   0x3ec0d477a1ac0428,
   0x3ec07e8b2b760a5a,
   0x3ec02837a8b57f15,
   0x3ebfb819d9f2a375,
   0x3ebf384ff251820f,
   0x3ebeb850109b4fce,
   0x3ebe377c93a8c3de,
   0x3ebdb5966273fd75,
   0x3ebd3273bfa89559,
   0x3ebcadf3b4e44538,
   0x3ebc280a5b18ee4c,
   0x3ebba0bb796476b5,
   0x3ebb18197e6d403c,
   0x3eba8e445e677934,
   0x3eba03685b7647ae,
   0x3eb977bcbd385447,
   0x3eb8eb827b72d9e9,
   0x3eb85f02df1b7132,
   0x3eb7d28e1c59cfbb,
   0x3eb74679e79fa54c,
   0x3eb6bb2065a7d5d5,
   0x3eb630dda0030f10,
   0x3eb5a80f2bfad0ec,
   0x3eb53691445e0129,
   0x3eb4cc374b55bb8d,
   0x3eb461374dfe08c4,
   0x3eb3f5af33206b62]

theorem record2684ChunkBits202Length2685 :
    (record2684ChunkBits2022685).length = 32 := by
  decide

theorem record2684ChunkSum2022685 :
    ((record2684ChunkBits2022685).map binary64Value2674).sum =
      (252146876170883207 : ℚ) / 4722366482869645213696 := by
  norm_num [record2684ChunkBits2022685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6496 through 6527,
decoded and summed as exact rationals. -/
def record2684ChunkBits2032685 : List Nat :=
  [0x3eb389c4d8367c7a,
   0x3eb32a234f4c5655,
   0x3eb2d9d6ebabc2de,
   0x3eb28982c1f86998,
   0x3eb238be41c5abd4,
   0x3eb1e764cd620bfd,
   0x3eb1955edd0abb90,
   0x3eb1429a300fb761,
   0x3eb0ef1143699f7b,
   0x3eb09ac801d7d5be,
   0x3eb045cb1b3c2a54,
   0x3eafe05e990ceea7,
   0x3eaf34213744e9b4,
   0x3eae872314942ba7,
   0x3eadd9b484382430,
   0x3ead2c2f77c6d268,
   0x3eac7ef5c738a8dd,
   0x3eabd26f91997ff9,
   0x3eab270983417c63,
   0x3eaa7d3256282450,
   0x3ea9d626f403765b,
   0x3ea953893ca90a4f,
   0x3ea8d027a471c08f,
   0x3ea84c1dfbc9f713,
   0x3ea7c792a0baa501,
   0x3ea742b557fa6897,
   0x3ea6cc7b76b645bf,
   0x3ea6691d229a7066,
   0x3ea605d66a5d3dd2,
   0x3ea5a21ebf082478,
   0x3ea53dcc6ec02d98,
   0x3ea4d8c58d459c6f]

theorem record2684ChunkBits203Length2685 :
    (record2684ChunkBits2032685).length = 32 := by
  decide

theorem record2684ChunkSum2032685 :
    ((record2684ChunkBits2032685).map binary64Value2674).sum =
      (263066447293939621 : ℚ) / 9444732965739290427392 := by
  norm_num [record2684ChunkBits2032685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6528 through 6559,
decoded and summed as exact rationals. -/
def record2684ChunkBits2042685 : List Nat :=
  [0x3ea472f66bf8436f,
   0x3ea40c5a85bcd541,
   0x3ea3a4f87b85d780,
   0x3ea33ce13f936051,
   0x3ea2d42f2fb9c1e9,
   0x3ea26b0522c48f28,
   0x3ea2018d6c5f874f,
   0x3ea197f8da4b9e94,
   0x3ea12e7dad2362d9,
   0x3ea0c5568e7a03e6,
   0x3ea05cc1abe56389,
   0x3e9fe9feb2209e7d,
   0x3e9f1ca227fd15c7,
   0x3e9e5f807598ed77,
   0x3e9dc07f4e0e9803,
   0x3e9d20bc8a0319e4,
   0x3e9c805c24333f19,
   0x3e9bdf8e6694bf8d,
   0x3e9b3e8e7dd472c8,
   0x3e9aaebc71c00bdd,
   0x3e9a35bb8938c570,
   0x3e99bd00f633ad8c,
   0x3e9943dd52cdcc19,
   0x3e98ca22164aa184,
   0x3e984fb36703f6e6,
   0x3e97d47cab3799f1,
   0x3e97587b04afaea9,
   0x3e96dbb8884c4f86,
   0x3e965e4b3685c0ef,
   0x3e95e053e1d0cb8c,
   0x3e9561fd07a833bd,
   0x3e94e379a02c578f]

theorem record2684ChunkBits204Length2685 :
    (record2684ChunkBits2042685).length = 32 := by
  decide

theorem record2684ChunkSum2042685 :
    ((record2684ChunkBits2042685).map binary64Value2674).sum =
      (267549379634756557 : ℚ) / 18889465931478580854784 := by
  norm_num [record2684ChunkBits2042685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6560 through 6591,
decoded and summed as exact rationals. -/
def record2684ChunkBits2052685 : List Nat :=
  [0x3e946503e78e90c9,
   0x3e93e6dc23dbde17,
   0x3e9369476934b21f,
   0x3e92ec8ea47b6280,
   0x3e9270fc9778c4e3,
   0x3e91f6dd50b4ac1a,
   0x3e918dfe0b72225b,
   0x3e912eca0836cd2f,
   0x3e90cf3e09d6606d,
   0x3e906f70cfb3d0df,
   0x3e900f80230482c5,
   0x3e8f5f1ff34b9936,
   0x3e8eb3176b17591f,
   0x3e8e2232d4688edb,
   0x3e8d91d5a7ed19e6,
   0x3e8d0122894a9fce,
   0x3e8c6fe69fbd38a6,
   0x3e8bde04cf280509,
   0x3e8b4b683f4e828b,
   0x3e8ab81075246533,
   0x3e8a240bb8d98562,
   0x3e898f75d5aeec20,
   0x3e88fa76c71fc49f,
   0x3e88654158cbcfeb,
   0x3e87d011bd9effcc,
   0x3e873b2c21d042f3,
   0x3e86a6db3a9f0bcd,
   0x3e86136ee3ca7e08,
   0x3e85813adbffd81d,
   0x3e84f0947fc06c3b,
   0x3e8461d25f278cef,
   0x3e83f00dee92c62d]

theorem record2684ChunkBits205Length2685 :
    (record2684ChunkBits2052685).length = 32 := by
  decide

theorem record2684ChunkSum2052685 :
    ((record2684ChunkBits2052685).map binary64Value2674).sum =
      (263142020479056531 : ℚ) / 37778931862957161709568 := by
  norm_num [record2684ChunkBits2052685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6592 through 6623,
decoded and summed as exact rationals. -/
def record2684ChunkBits2062685 : List Nat :=
  [0x3e837ffe2a18da24,
   0x3e830fa919b66bf7,
   0x3e829f2ad8bc8cc5,
   0x3e822ea76441ec35,
   0x3e81be4993d7d3a1,
   0x3e815931339d5fba,
   0x3e8103f4087fd7b8,
   0x3e80af2580bd9dcf,
   0x3e805a3c7d613bf9,
   0x3e80051dd414a1dc,
   0x3e7f5f75856c4ad1,
   0x3e7eb4124b40420d,
   0x3e7e0814a3a8aa84,
   0x3e7d5b8fb914382e,
   0x3e7caea5b8f8ef2a,
   0x3e7c018643f6fe13,
   0x3e7b546cd195c110,
   0x3e7aa79f0c92146e,
   0x3e79fb6b2bbb8fda,
   0x3e7950264a8a11c0,
   0x3e78a62af895449a,
   0x3e77fdd73257e722,
   0x3e77578ab3c2543f,
   0x3e76bc6729df8170,
   0x3e763b186d2151fe,
   0x3e75b98ac572a716,
   0x3e7537d64dde3cc6,
   0x3e74b61cf0ed6cc6,
   0x3e7434893b0e74b7,
   0x3e73b34d275addb5,
   0x3e733ea6b857a9d2,
   0x3e72dc2fb308c412]

theorem record2684ChunkBits206Length2685 :
    (record2684ChunkBits2062685).length = 32 := by
  decide

theorem record2684ChunkSum2062685 :
    ((record2684ChunkBits2062685).map binary64Value2674).sum =
      (31493722286684283 : ℚ) / 9444732965739290427392 := by
  norm_num [record2684ChunkBits2062685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6624 through 6655,
decoded and summed as exact rationals. -/
def record2684ChunkBits2072685 : List Nat :=
  [0x3e727a5d4ad401c8,
   0x3e721888e71788b6,
   0x3e71b6962e5835ae,
   0x3e715476a99b6f5b,
   0x3e70f220f02eac26,
   0x3e708f9844047f52,
   0x3e702ce8efa97f10,
   0x3e6f944ecf7c6ba2,
   0x3e6ecedec788a91c,
   0x3e6e09c5e3203151,
   0x3e6d45530c227efb,
   0x3e6c81de1b2d75a2,
   0x3e6bbfc5fa804acc,
   0x3e6aff6f32c76813,
   0x3e6a4140fc578328,
   0x3e6985a4682b1922,
   0x3e68e351fe452bca,
   0x3e68506faf3e264a,
   0x3e67bd74e28211f3,
   0x3e672a7ef1e29a13,
   0x3e6697b5ce15417f,
   0x3e66054aa37c0320,
   0x3e6573767b205cda,
   0x3e64ef6eb70e43c4,
   0x3e647fdaf0c30b64,
   0x3e64112c9d5b492a,
   0x3e63a29d71e74cc5,
   0x3e6334109301a62f,
   0x3e62c5785d037aa3,
   0x3e6256cc95ca5154,
   0x3e61e812b4d09d3d,
   0x3e617959ded712cc]

theorem record2684ChunkBits207Length2685 :
    (record2684ChunkBits2072685).length = 32 := by
  decide

theorem record2684ChunkSum2072685 :
    ((record2684ChunkBits2072685).map binary64Value2674).sum =
      (58710738142165299 : ℚ) / 37778931862957161709568 := by
  norm_num [record2684ChunkBits2072685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6656 through 6687,
decoded and summed as exact rationals. -/
def record2684ChunkBits2082685 : List Nat :=
  [0x3e610ab9e7c2b23d,
   0x3e609c524cdf44dc,
   0x3e602e492b11b1d7,
   0x3e5f819467a861a3,
   0x3e5ea80b467abef2,
   0x3e5dd05e870ab529,
   0x3e5cfafb067248ef,
   0x3e5c284fccbad895,
   0x3e5b58cd739d648b,
   0x3e5ab32fb794c05b,
   0x3e5a0f9706d3a8ee,
   0x3e596c19d3d2a33f,
   0x3e58c8dad2beb12b,
   0x3e582607dfc425ca,
   0x3e5783d8781e0e04,
   0x3e56e28c31ca12ef,
   0x3e56501837f2b172,
   0x3e55d42e059fdc99,
   0x3e555973ae983ba1,
   0x3e54df023a31adfc,
   0x3e5464bd0bea5dce,
   0x3e53ea97d8718506,
   0x3e53708bfd0fa6fd,
   0x3e52f6a151887b84,
   0x3e527ce9cec5bc20,
   0x3e520380730e7554,
   0x3e518a88203b003f,
   0x3e51122a77947ad9,
   0x3e509a96b65240af,
   0x3e50240094ff0289,
   0x3e4f5d3ea4bbd0e7,
   0x3e4e755892c515a0]

theorem record2684ChunkBits208Length2685 :
    (record2684ChunkBits2082685).length = 32 := by
  decide

theorem record2684ChunkSum2082685 :
    ((record2684ChunkBits2082685).map binary64Value2674).sum =
      (421924730310173763 : ℚ) / 604462909807314587353088 := by
  norm_num [record2684ChunkBits2082685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6688 through 6719,
decoded and summed as exact rationals. -/
def record2684ChunkBits2092685 : List Nat :=
  [0x3e4d90c3e0238214,
   0x3e4cbe35cc2221af,
   0x3e4c0b77a91a2acd,
   0x3e4b58fb64c6f073,
   0x3e4aa6dbb51dd7d3,
   0x3e49f5406fadc75a,
   0x3e49445cde28420a,
   0x3e48946e10586619,
   0x3e47e5b92fc8947b,
   0x3e4746ac5313772f,
   0x3e46bfee905202d9,
   0x3e463ab2112ffc82,
   0x3e45b5efdad21c20,
   0x3e45318c5cbb9365,
   0x3e44ad7d0178cc38,
   0x3e4429bd2567af80,
   0x3e43a656fb07c98d,
   0x3e43235f1555e31e,
   0x3e42a0f32acc31a3,
   0x3e421f38dbed038c,
   0x3e419e5c7998311e,
   0x3e411e8fce1de7e7,
   0x3e40a008eb5553f8,
   0x3e4023014564dcb5,
   0x3e3f4f6780bf6b1b,
   0x3e3e5cb8b39f9c35,
   0x3e3d8ec8737ba611,
   0x3e3ccfb16c6516e3,
   0x3e3c1124275bf07c,
   0x3e3b533fc11c865d,
   0x3e3a9630954781fc,
   0x3e39da2e6fd2d481]

theorem record2684ChunkBits209Length2685 :
    (record2684ChunkBits2092685).length = 32 := by
  decide

theorem record2684ChunkSum2092685 :
    ((record2684ChunkBits2092685).map binary64Value2674).sum =
      (91342803314399351 : ℚ) / 302231454903657293676544 := by
  norm_num [record2684ChunkBits2092685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6720 through 6751,
decoded and summed as exact rationals. -/
def record2684ChunkBits2102685 : List Nat :=
  [0x3e391f7abf76fa1b,
   0x3e38665ecd437f60,
   0x3e37bd6ea93299bc,
   0x3e372e212c2a6050,
   0x3e36a0a972d455ee,
   0x3e3613e3289e8843,
   0x3e3587b4849957b7,
   0x3e34fc14f5d89853,
   0x3e3471020bf1acc9,
   0x3e33e68823260b33,
   0x3e335cbdf5d6e53c,
   0x3e32d3c342155d09,
   0x3e324bbf7ecb321a,
   0x3e31c4e093167d00,
   0x3e313f5992b39a17,
   0x3e30bb61998ce6a0,
   0x3e30393286eb2208,
   0x3e2f720ee4a84361,
   0x3e2e7b0689ce7af2,
   0x3e2db28cf1a413d0,
   0x3e2cead95abf5ff2,
   0x3e2c23ffbf3b9844,
   0x3e2b5e22ffa87265,
   0x3e2a9972fb8e52fc,
   0x3e29d62aa9b47430,
   0x3e29148e35541b7d,
   0x3e2854e924292663,
   0x3e27a59b5331aa14,
   0x3e2710b47e3dbcd1,
   0x3e267df5ebfd68b4,
   0x3e25ec22c31987c0,
   0x3e255b239d9e4829]

theorem record2684ChunkBits210Length2685 :
    (record2684ChunkBits2102685).length = 32 := by
  decide

theorem record2684ChunkSum2102685 :
    ((record2684ChunkBits2102685).map binary64Value2674).sum =
      (76512249152241729 : ℚ) / 604462909807314587353088 := by
  norm_num [record2684ChunkBits2102685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6752 through 6783,
decoded and summed as exact rationals. -/
def record2684ChunkBits2112685 : List Nat :=
  [0x3e24caf21b280a89,
   0x3e243b8dfeaa7fec,
   0x3e23ad056c2f07cc,
   0x3e231f709c1e8d4c,
   0x3e2292f06b882300,
   0x3e2207ad07d7ad88,
   0x3e217dd49f480e34,
   0x3e20f59a18bfaab5,
   0x3e206f340e27e9d2,
   0x3e1fd5b6013dab9a,
   0x3e1ed1913727de82,
   0x3e1deb0e9ed32ffa,
   0x3e1d1e320968cced,
   0x3e1c526c0d8a88af,
   0x3e1b87d3f712c9ba,
   0x3e1abe8f6964a039,
   0x3e19f6d066d68830,
   0x3e1930d35c46de5c,
   0x3e186cdd35a83cc8,
   0x3e17ab397f216293,
   0x3e16f9b8a608e6e1,
   0x3e1662bdfe0baa54,
   0x3e15ce362b7aca0a,
   0x3e153ad2c9202d30,
   0x3e14a87f4276b54a,
   0x3e1417376470f3b9,
   0x3e1386fcf3b2672a,
   0x3e12f7df4b1aed6d,
   0x3e1269f74a94ba03,
   0x3e11dd65dc4ff287,
   0x3e115252a025b784,
   0x3e10c8ea9e32c0f4]

theorem record2684ChunkBits211Length2685 :
    (record2684ChunkBits2112685).length = 32 := by
  decide

theorem record2684ChunkSum2112685 :
    ((record2684ChunkBits2112685).map binary64Value2674).sum =
      (246625042476781623 : ℚ) / 4835703278458516698824704 := by
  norm_num [record2684ChunkBits2112685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6784 through 6815,
decoded and summed as exact rationals. -/
def record2684ChunkBits2122685 : List Nat :=
  [0x3e10415f0d8fd954,
   0x3e0f77c880586827,
   0x3e0e715f8b2b5863,
   0x3e0d6ff03110a876,
   0x3e0c9f7eeb74e517,
   0x3e0bd355cf426827,
   0x3e0b0892a25888f1,
   0x3e0a3f4f17a83f22,
   0x3e0977b243e11eff,
   0x3e08b1eea2075d82,
   0x3e07ee40208e77df,
   0x3e072cea3b47a12e,
   0x3e066e362543952c,
   0x3e05bf0f6e7564e0,
   0x3e0529ddf8d165c2,
   0x3e04975bd7b332c2,
   0x3e040631e9f8c66f,
   0x3e03764ea468fcec,
   0x3e02e7afce482880,
   0x3e025a58cdc406f0,
   0x3e01ce597fd89be3,
   0x3e0143ca79600209,
   0x3e00bacb8cda02f1,
   0x3e0033827f22d0ae,
   0x3dff5c338b365f2f,
   0x3dfe557ef7473ff9,
   0x3dfd5347a4cea5d4,
   0x3dfc55f03b0f3340,
   0x3dfb6f615c0af60b,
   0x3dfaa79892c7cf2a,
   0x3df9e170a7e9f81a,
   0x3df91cf67c34e9b5]

theorem record2684ChunkBits212Length2685 :
    (record2684ChunkBits2122685).length = 32 := by
  decide

theorem record2684ChunkSum2122685 :
    ((record2684ChunkBits2122685).map binary64Value2674).sum =
      (189644832265882893 : ℚ) / 9671406556917033397649408 := by
  norm_num [record2684ChunkBits2122685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6816 through 6847,
decoded and summed as exact rationals. -/
def record2684ChunkBits2132685 : List Nat :=
  [0x3df85a44fab41f34,
   0x3df79983224134fb,
   0x3df6dae2168b31f4,
   0x3df61e9b3d97eded,
   0x3df564ee6d6af323,
   0x3df4ae202c683bb5,
   0x3df405ee53bfae8f,
   0x3df37672e8f4d671,
   0x3df2e9cf9b01a398,
   0x3df25eae9fcad533,
   0x3df1d501742ddf9e,
   0x3df14cc77d5a8d68,
   0x3df0c6053f058981,
   0x3df040ca518379e0,
   0x3def7a5c0e54cae0,
   0x3dee769bfd4b4fc9,
   0x3ded7699d4c0a9df,
   0x3dec7aa2cb290631,
   0x3deb830a20507045,
   0x3dea902567ba5248,
   0x3de9a24c257bdbc1,
   0x3de8dcfcec849b09,
   0x3de820194019a265,
   0x3de7650eef237683,
   0x3de6abec63b4ebdb,
   0x3de5f4cc6b8ba588,
   0x3de53fd458f4ccdb,
   0x3de48d322f3b26d0,
   0x3de3dd1adec508c2,
   0x3de32fc893dbb31d,
   0x3de285791a1603d8,
   0x3de1e886142c6632]

theorem record2684ChunkBits213Length2685 :
    (record2684ChunkBits2132685).length = 32 := by
  decide

theorem record2684ChunkSum2132685 :
    ((record2684ChunkBits2132685).map binary64Value2674).sum =
      (279713625489402403 : ℚ) / 38685626227668133590597632 := by
  norm_num [record2684ChunkBits2132685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6848 through 6879,
decoded and summed as exact rationals. -/
def record2684ChunkBits2142685 : List Nat :=
  [0x3de1626d3126cac5,
   0x3de0df3d2ce3c1d5,
   0x3de05dac190633ae,
   0x3ddfbb5c8b318464,
   0x3ddebe8879d229a9,
   0x3dddc4e6120ae8b1,
   0x3ddcce9275c876eb,
   0x3ddbdbb8006bcc99,
   0x3ddaec8b9b1e7afd,
   0x3dda014a819c6348,
   0x3dd91a3861bf22b3,
   0x3dd8379cc6f98d81,
   0x3dd759c1441279ad,
   0x3dd68d8b8ea84f31,
   0x3dd5de216bb68ee2,
   0x3dd530b48ed89e1f,
   0x3dd485477b8576a1,
   0x3dd3dbe902d46414,
   0x3dd334b27fe0d31c,
   0x3dd28fc61e411fb6,
   0x3dd1ed4d2f17a5a0,
   0x3dd14d76900840f9,
   0x3dd0b07526502166,
   0x3dd0167e6f657149,
   0x3dcf10cf423c9432,
   0x3dce1d9d9cca72c0,
   0x3dcd302aa696e42a,
   0x3dcc460e3a0da2cb,
   0x3dcb5f35e52fd53a,
   0x3dca7ba3ff8049b6,
   0x3dc99b627d8934ae,
   0x3dc8be8b23294ec4]

theorem record2684ChunkBits214Length2685 :
    (record2684ChunkBits2142685).length = 32 := by
  decide

theorem record2684ChunkSum2142685 :
    ((record2684ChunkBits2142685).map binary64Value2674).sum =
      (393470472046804027 : ℚ) / 154742504910672534362390528 := by
  norm_num [record2684ChunkBits2142685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6880 through 6911,
decoded and summed as exact rationals. -/
def record2684ChunkBits2152685 : List Nat :=
  [0x3dc7e5429b093b3d,
   0x3dc70fb60dac3dd6,
   0x3dc63e192a0f279d,
   0x3dc570a4b1c77da9,
   0x3dc4a79367be6f7f,
   0x3dc3e321c1ccbd01,
   0x3dc33ec2f1e8a677,
   0x3dc2a25938f245f4,
   0x3dc207fc03756ec8,
   0x3dc16faf3ad05aca,
   0x3dc0d980fc92fc9d,
   0x3dc0458804f91f8b,
   0x3dbf67c44cc24ea8,
   0x3dbe4965a282e62c,
   0x3dbd30435e167c86,
   0x3dbc1cb2a3140001,
   0x3dbb0f0bef2c3939,
   0x3dba15dffa25331f,
   0x3db94047c1653807,
   0x3db87027239471cb,
   0x3db7a352b5f27507,
   0x3db6d9bc0f9a6711,
   0x3db61365d3cecc7e,
   0x3db55058d586e53d,
   0x3db490aa88fbb20c,
   0x3db3d47904a3b427,
   0x3db31be8e8bebed4,
   0x3db26723e3f17ef0,
   0x3db1b656b0f2c94c,
   0x3db109afb331e992,
   0x3db06b3ccee6c5fb,
   0x3dafc46e122e56bc]

theorem record2684ChunkBits215Length2685 :
    (record2684ChunkBits2152685).length = 32 := by
  decide

theorem record2684ChunkSum2152685 :
    ((record2684ChunkBits2152685).map binary64Value2674).sum =
      (131162071282478017 : ℚ) / 154742504910672534362390528 := by
  norm_num [record2684ChunkBits2152685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6912 through 6943,
decoded and summed as exact rationals. -/
def record2684ChunkBits2162685 : List Nat :=
  [0x3daeb677accc5279,
   0x3dadac8c0ff287e6,
   0x3daca6b3f25b7154,
   0x3daba5084c310f7c,
   0x3daaa7af9a05f8f2,
   0x3da9aedb3cfe31b1,
   0x3da8bac4fd38cd41,
   0x3da7cbacb1cc4595,
   0x3da6e1d61038a26f,
   0x3da5fd86a4153fbe,
   0x3da52a51d60e71c1,
   0x3da474f409d9edf9,
   0x3da3c4989580c6ce,
   0x3da3175d2a67227c,
   0x3da26d367c61966d,
   0x3da1c626b4cf60b2,
   0x3da12234cd87e999,
   0x3da0817170e1efd0,
   0x3d9fc7e7ac1d3ef7,
   0x3d9e93b00ab852e5,
   0x3d9d667b63202771,
   0x3d9c408c41cb5aba,
   0x3d9b2227b573694c,
   0x3d9a33e27dbf7682,
   0x3d994f0161f079dd,
   0x3d986df89068ca11,
   0x3d9790c149980670,
   0x3d96b76393334ef8,
   0x3d95e1f3d99180d6,
   0x3d951090a9bd4a58,
   0x3d944360894fe081,
   0x3d937a8fef7754d0]

theorem record2684ChunkBits216Length2685 :
    (record2684ChunkBits2162685).length = 32 := by
  decide

theorem record2684ChunkSum2162685 :
    ((record2684ChunkBits2162685).map binary64Value2674).sum =
      (82861650726776219 : ℚ) / 309485009821345068724781056 := by
  norm_num [record2684ChunkBits2162685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6944 through 6975,
decoded and summed as exact rationals. -/
def record2684ChunkBits2172685 : List Nat :=
  [0x3d92b64f612854fb,
   0x3d91f6d1b163ef95,
   0x3d913c4a659d2f93,
   0x3d908f9201f2253e,
   0x3d8ff5f75cc06494,
   0x3d8ed59d7e1d205c,
   0x3d8dbaf16010298f,
   0x3d8ca5e0fc2788dc,
   0x3d8b966eb57d9e78,
   0x3d8a8ca41701e343,
   0x3d898898e8c8f1ce,
   0x3d888a6e70a871cf,
   0x3d87924cee635c89,
   0x3d86a060b65f219e,
   0x3d85b4d893841b7b,
   0x3d84e0252442d060,
   0x3d8424537bc2d480,
   0x3d836c0be1937c44,
   0x3d82b73cba82e049,
   0x3d8205e157217cb9,
   0x3d8157fff8203f26,
   0x3d80ada7e6aeb682,
   0x3d8006efa5ae94eb,
   0x3d7ec7e67e185e96,
   0x3d7d89a55e7c1859,
   0x3d7c5360dfceb6d3,
   0x3d7b2560439439e3,
   0x3d79ffeaab390967,
   0x3d78eff682f5a6c9,
   0x3d780590faf97a9d,
   0x3d7722a057f28ee4,
   0x3d7644a08c7e2d5f]

theorem record2684ChunkBits217Length2685 :
    (record2684ChunkBits2172685).length = 32 := by
  decide

theorem record2684ChunkSum2172685 :
    ((record2684ChunkBits2172685).map binary64Value2674).sum =
      (393804904173285973 : ℚ) / 4951760157141521099596496896 := by
  norm_num [record2684ChunkBits2172685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 6976 through 7007,
decoded and summed as exact rationals. -/
def record2684ChunkBits2182685 : List Nat :=
  [0x3d756b82d8c48706,
   0x3d74974751b06089,
   0x3d73c7f31c356857,
   0x3d72fd955b187e16,
   0x3d723843ced85a96,
   0x3d717818bef4445b,
   0x3d70bd30ae6144e8,
   0x3d70084adfc332c1,
   0x3d6ee6cabeec2186,
   0x3d6dc3487086bead,
   0x3d6ca5df10e5ee64,
   0x3d6b8e7498c99abe,
   0x3d6a7d0189815569,
   0x3d69718dd8258381,
   0x3d686c2e007f4925,
   0x3d676d0045bd8e5e,
   0x3d66742a24cfaffa,
   0x3d6581d5fa646908,
   0x3d649630dd13e1a4,
   0x3d63b168ab21f886,
   0x3d62d3aa4a733493,
   0x3d620609d243341a,
   0x3d6154765f76a4f0,
   0x3d60a8ebbf4056d2,
   0x3d60017d5df0a55e,
   0x3d5ebc3dc63d946b,
   0x3d5d7d9c861b0a92,
   0x3d5c4719b0a630c3,
   0x3d5b18c5553f2751,
   0x3d59f2b87e098205,
   0x3d58d510d83b79de,
   0x3d57bfef57c6d9fc]

theorem record2684ChunkBits218Length2685 :
    (record2684ChunkBits2182685).length = 32 := by
  decide

theorem record2684ChunkSum2182685 :
    ((record2684ChunkBits2182685).map binary64Value2674).sum =
      (219912634506069599 : ℚ) / 9903520314283042199192993792 := by
  norm_num [record2684ChunkBits2182685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7008 through 7039,
decoded and summed as exact rationals. -/
def record2684ChunkBits2192685 : List Nat :=
  [0x3d56cc811f2470e5,
   0x3d55ee440deec5a7,
   0x3d55152fb5b971c2,
   0x3d5441216ff58ab6,
   0x3d537205a5de1262,
   0x3d52a7d56a3f6551,
   0x3d51e294318c6265,
   0x3d51224dada807ed,
   0x3d506713d0d9033c,
   0x3d4f61f9f39da36c,
   0x3d4e004492aed7f6,
   0x3d4ca93c42db0ead,
   0x3d4b5d15991d525e,
   0x3d4a1c029794410b,
   0x3d48f22023f0d8c3,
   0x3d47f05b6a271c36,
   0x3d46f7eba9b180f1,
   0x3d460602c99a9332,
   0x3d451a8bedcca5c7,
   0x3d44357fddceccd8,
   0x3d4356dbb3a5344c,
   0x3d427ea529303e07,
   0x3d41ace729e256d4,
   0x3d40e1af6e713f95,
   0x3d4023f9c1183d01,
   0x3d3f0211b8607611,
   0x3d3dc491783057ea,
   0x3d3c8f295553f576,
   0x3d3b61a75545fb6c,
   0x3d3a3bed589a4d38,
   0x3d391dedb07feb0a,
   0x3d3807a7e978881f]

theorem record2684ChunkBits219Length2685 :
    (record2684ChunkBits2192685).length = 32 := by
  decide

theorem record2684ChunkSum2192685 :
    ((record2684ChunkBits2192685).map binary64Value2674).sum =
      (229251900440235801 : ℚ) / 39614081257132168796771975168 := by
  norm_num [record2684ChunkBits2192685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7040 through 7071,
decoded and summed as exact rationals. -/
def record2684ChunkBits2202685 : List Nat :=
  [0x3d36f925d13228ed,
   0x3d35f278bade162b,
   0x3d34f3b7034e95ff,
   0x3d33fcf9d4871957,
   0x3d330e5b27332aaf,
   0x3d3227f3ff9f3c91,
   0x3d3149dae33b6aa8,
   0x3d307bba8e9cbdc4,
   0x3d2f91fa9240b092,
   0x3d2e3a40f404f488,
   0x3d2cec65d4070024,
   0x3d2ba84647539e03,
   0x3d2a6dd0917570a3,
   0x3d293cf82d819c44,
   0x3d2815bb2fe84298,
   0x3d26f81ceb58d6dc,
   0x3d25e4247087927f,
   0x3d24fa879d67f786,
   0x3d241bd492f19ad8,
   0x3d234360fa221814,
   0x3d2270fa13c8c275,
   0x3d21a47bff81ab3a,
   0x3d20ddcf485ba2f9,
   0x3d201ce69757d0c7,
   0x3d1ec379210d5024,
   0x3d1d58a3bb1a894c,
   0x3d1bf956cd7b3764,
   0x3d1aa5a1755a0b93,
   0x3d195d9546728da7,
   0x3d182143cc783960,
   0x3d16f0bc5f6a59ad,
   0x3d15cc0a45da3211]

theorem record2684ChunkBits220Length2685 :
    (record2684ChunkBits2202685).length = 32 := by
  decide

theorem record2684ChunkSum2202685 :
    ((record2684ChunkBits2202685).map binary64Value2674).sum =
      (110700669857979875 : ℚ) / 79228162514264337593543950336 := by
  norm_num [record2684ChunkBits2202685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7072 through 7103,
decoded and summed as exact rationals. -/
def record2684ChunkBits2212685 : List Nat :=
  [0x3d14bc584a74d2a2,
   0x3d13d03e4b71bee9,
   0x3d12edc630d1420b,
   0x3d1212644d7a0d17,
   0x3d113dfc341174a4,
   0x3d10707bbdc75d3e,
   0x3d0f53a7de97f8dc,
   0x3d0dd3f674f9839e,
   0x3d0c61d707870d52,
   0x3d0b173d093eec0f,
   0x3d09ec68991633e0,
   0x3d08cac9ef464e61,
   0x3d07b206dfba960e,
   0x3d06a1da79ea1d7f,
   0x3d059a11acf532e7,
   0x3d049a881f1113e1,
   0x3d03a3253f7e3ae6,
   0x3d02b3d99759e6e7,
   0x3d01cc9c5b4075fa,
   0x3d00ed693dd3a405,
   0x3d00163e81c690d2,
   0x3cfe8e3692051494,
   0x3cfcfffc3b7af18f,
   0x3cfb81c763cfdc37,
   0x3cfa138ba249fde1,
   0x3cf8bf955c5e04ae,
   0x3cf79782c25de1c6,
   0x3cf67c38b6b1a913,
   0x3cf56a9217c6da07,
   0x3cf462628b760f7a,
   0x3cf3638985499cd5,
   0x3cf26de9938ffd55]

theorem record2684ChunkBits221Length2685 :
    (record2684ChunkBits2212685).length = 32 := by
  decide

theorem record2684ChunkSum2212685 :
    ((record2684ChunkBits2212685).map binary64Value2674).sum =
      (393661895542586311 : ℚ) / 1267650600228229401496703205376 := by
  norm_num [record2684ChunkBits2212685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7104 through 7135,
decoded and summed as exact rationals. -/
def record2684ChunkBits2222685 : List Nat :=
  [0x3cf1816b3489ea16,
   0x3cf0a4b78a5df54d,
   0x3cefcb045f38a1aa,
   0x3cee5984f7310dba,
   0x3cecf45fd4c451a2,
   0x3ceb9b20c5d88095,
   0x3cea4d6c0b793e32,
   0x3ce90afa39695838,
   0x3ce7d3946228d359,
   0x3ce6a71095b2f8b4,
   0x3ce5854eb5edc287,
   0x3ce46e35a121eb6c,
   0x3ce361b0b0cdd7d0,
   0x3ce25fad899e1ed6,
   0x3ce1681a3850e7ab,
   0x3ce07ae39697eb47,
   0x3cdf2fe7e56d4d5f,
   0x3cdd7e63e9069208,
   0x3cdbec0899dc7085,
   0x3cda8cd73362c7a0,
   0x3cd93daad4237f26,
   0x3cd7faddf9124dd0,
   0x3cd6c42f1d601c30,
   0x3cd59969919d1b17,
   0x3cd47a5b3b8c9a6c,
   0x3cd366d8cb0c3c7f,
   0x3cd27c5f05fe529c,
   0x3cd19c5d40c0ac09,
   0x3cd0c487aeef891c,
   0x3ccfe90b7dd85732,
   0x3cce581d7521bb74,
   0x3cccd5ce6fcbc4a4]

theorem record2684ChunkBits222Length2685 :
    (record2684ChunkBits2222685).length = 32 := by
  decide

theorem record2684ChunkSum2222685 :
    ((record2684ChunkBits2222685).map binary64Value2674).sum =
      (10061552370324695 : ℚ) / 158456325028528675187087900672 := by
  norm_num [record2684ChunkBits2222685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7136 through 7167,
decoded and summed as exact rationals. -/
def record2684ChunkBits2232685 : List Nat :=
  [0x3ccb61bd7274008e,
   0x3cc9fb9b01a7f423,
   0x3cc8a32534a3df4b,
   0x3cc75824341a5f8a,
   0x3cc61a6723072e25,
   0x3cc4e9c16d8d2ca0,
   0x3cc3c6087875ca4b,
   0x3cc2af11aafc8df2,
   0x3cc1a4b0cc0fcbdb,
   0x3cc0a6b6ac0308c6,
   0x3cbf69e027966564,
   0x3cbda939c0017140,
   0x3cbc20befd358590,
   0x3cbaab26e98f6fad,
   0x3cb9447ebdc85e9b,
   0x3cb7ec6bce5b021c,
   0x3cb6a29f99a0eb36,
   0x3cb566cf38a789ad,
   0x3cb44f5400ef97b5,
   0x3cb34e205b356857,
   0x3cb257254b7a1597,
   0x3cb169e70cf5fb90,
   0x3cb085fd4ea78853,
   0x3caf562063f87211,
   0x3cadb1ab02331f28,
   0x3cac1e1c4411dfef,
   0x3caa9b0792d3eaf9,
   0x3ca9280dda5f6dfe,
   0x3ca7c4d9ec8a7bac,
   0x3ca6711d5d6d6743,
   0x3ca52c8dd238019d,
   0x3ca3f6e2bad298e7]

theorem record2684ChunkBits223Length2685 :
    (record2684ChunkBits2232685).length = 32 := by
  decide

theorem record2684ChunkSum2232685 :
    ((record2684ChunkBits2232685).map binary64Value2674).sum =
      (59767701589562695 : ℚ) / 5070602400912917605986812821504 := by
  norm_num [record2684ChunkBits2232685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7168 through 7199,
decoded and summed as exact rationals. -/
def record2684ChunkBits2242685 : List Nat :=
  [0x3ca2cfd36df2b747,
   0x3ca1b7159f037aee,
   0x3ca0ac5c255669ea,
   0x3c9f5eac18c51141,
   0x3c9d89639b68cf8b,
   0x3c9bedf05c828f6d,
   0x3c9a6758e7e15ab4,
   0x3c98f1a4fde2ef05,
   0x3c978c5e9c96173b,
   0x3c96371c2a0b858f,
   0x3c94ffa25aa8a83c,
   0x3c93e916c8d49013,
   0x3c92de934296dd5d,
   0x3c91df784f525876,
   0x3c90eb3cf638aa41,
   0x3c90016b6a71b1e8,
   0x3c8e433be9f1972c,
   0x3c8c96f84473c234,
   0x3c8afd706cfd7c90,
   0x3c897619d397f2df,
   0x3c880076d3d60ce9,
   0x3c869c133fd79ff5,
   0x3c8548816ac87b44,
   0x3c840557aa0bf011,
   0x3c82d22e437d60f8,
   0x3c81ae9dbedcb4cd,
   0x3c809a3d908993ae,
   0x3c7f29462807534e,
   0x3c7d3ac19a63ca5f,
   0x3c7b707d25e70252,
   0x3c79ddcf1d16edf9,
   0x3c78609d8547c4df]

theorem record2684ChunkBits224Length2685 :
    (record2684ChunkBits2242685).length = 32 := by
  decide

theorem record2684ChunkSum2242685 :
    ((record2684ChunkBits2242685).map binary64Value2674).sum =
      (634562282804956373 : ℚ) / 324518553658426726783156020576256 := by
  norm_num [record2684ChunkBits2242685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7200 through 7231,
decoded and summed as exact rationals. -/
def record2684ChunkBits2252685 : List Nat :=
  [0x3c76f538c93e02be,
   0x3c759b12edcf01b5,
   0x3c74579c010e5d4c,
   0x3c733c52ea1f6c6f,
   0x3c722e4f1b0d2549,
   0x3c712cd2c5cd0e9e,
   0x3c703738912b90cd,
   0x3c6e99e044e03864,
   0x3c6cdaf5cf25fefc,
   0x3c6b30d250b081a3,
   0x3c699aaec303ada0,
   0x3c6817d7d5747eb4,
   0x3c66a7a9cba6e817,
   0x3c65498ce8dfa6e3,
   0x3c63fcf260265875,
   0x3c62c151bfc1087d,
   0x3c619626cdbee526,
   0x3c607aefcae996c3,
   0x3c5ede58230c7e3e,
   0x3c5ce4b60b3e6004,
   0x3c5b089c57b9e6b8,
   0x3c594881ffce2e56,
   0x3c57a94ff7ce4cd7,
   0x3c563be7cbe21b81,
   0x3c54e317b16cd1e8,
   0x3c539b8f46d5fe78,
   0x3c5264ae4b80f407,
   0x3c515762c6c527aa,
   0x3c505839d9573023,
   0x3c4ecbb112bf349d,
   0x3c4cff0d5ef77430,
   0x3c4b4a06992a33a2]

theorem record2684ChunkBits225Length2685 :
    (record2684ChunkBits2252685).length = 32 := by
  decide

theorem record2684ChunkSum2252685 :
    ((record2684ChunkBits2252685).map binary64Value2674).sum =
      (756117772676736999 : ℚ) / 2596148429267413814265248164610048 := by
  norm_num [record2684ChunkBits2252685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7232 through 7263,
decoded and summed as exact rationals. -/
def record2684ChunkBits2262685 : List Nat :=
  [0x3c49aae04294b564,
   0x3c48206c2cf89b12,
   0x3c46a9bbc5df253c,
   0x3c4545f7f5f11035,
   0x3c43f45d0b1678da,
   0x3c42b4371fcb794b,
   0x3c4184defaabbe73,
   0x3c4065b75f587079,
   0x3c3eac55914442a2,
   0x3c3cab5306496984,
   0x3c3ac7503e658114,
   0x3c38ff3c61e39b24,
   0x3c37520aab9c6078,
   0x3c35beb0edc57b11,
   0x3c3444268115cbc5,
   0x3c32e65436ecc7e8,
   0x3c31b2da75107e55,
   0x3c309178f0c542ef,
   0x3c2efef7a7baa33d,
   0x3c2d1bb8ab33369a,
   0x3c2b5be38e9a8fe5,
   0x3c29b41279cef7d3,
   0x3c2822c6db189079,
   0x3c26a6af04c9b33c,
   0x3c253e9f863c3cac,
   0x3c23e98dbd975884,
   0x3c22a68ae5f0f339,
   0x3c2174bfa5cdf448,
   0x3c2053681ddc78cf,
   0x3c1e83a0e8f7b88e,
   0x3c1c7ea3b0640669,
   0x3c1a969fe2e3a768]

theorem record2684ChunkBits226Length2685 :
    (record2684ChunkBits2262685).length = 32 := by
  decide

theorem record2684ChunkSum2262685 :
    ((record2684ChunkBits2262685).map binary64Value2674).sum =
      (799836632859653895 : ℚ) / 20769187434139310514121985316880384 := by
  norm_num [record2684ChunkBits2262685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7264 through 7295,
decoded and summed as exact rationals. -/
def record2684ChunkBits2272685 : List Nat :=
  [0x3c18ca6d75f1b582,
   0x3c1718f16edbb35f,
   0x3c15811af57123b1,
   0x3c1401e0fb4c23d3,
   0x3c129a40659acb23,
   0x3c11493aa85baff3,
   0x3c100dd4c352c393,
   0x3c0dce2d24dfba68,
   0x3c0baf382848b159,
   0x3c09d32acd1cdf2e,
   0x3c0814ddd57ff376,
   0x3c068571ba33d071,
   0x3c051a364c42ff57,
   0x3c03c3b4047105ec,
   0x3c02808ae676dc28,
   0x3c014f83ea85a0aa,
   0x3c002f8b941d56f5,
   0x3bfe3f58eb30b58e,
   0x3bfc3e156fa3c393,
   0x3bfa59c034fbd409,
   0x3bf890f0d8074bf3,
   0x3bf6e25ce9710275,
   0x3bf54cd29e63c34b,
   0x3bf3cf344bcb643c,
   0x3bf268749ade41f4,
   0x3bf1179364b4e0ff,
   0x3befb73645318622,
   0x3bed673dc245b365,
   0x3beb3d714a397ebd,
   0x3be9381064796edb,
   0x3be755644a52fd5f,
   0x3be593bea7456299]

theorem record2684ChunkBits227Length2685 :
    (record2684ChunkBits2272685).length = 32 := by
  decide

theorem record2684ChunkSum2272685 :
    ((record2684ChunkBits2272685).map binary64Value2674).sum =
      (731317163214990111 : ℚ) / 166153499473114484112975882535043072 := by
  norm_num [record2684ChunkBits2272685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7296 through 7327,
decoded and summed as exact rationals. -/
def record2684ChunkBits2282685 : List Nat :=
  [0x3be3f178fe3b4ac7,
   0x3be2719d2efe4fa2,
   0x3be121d649548bfa,
   0x3bdfe7c4b2c89b0d,
   0x3bddcb5b6e532971,
   0x3bdbcfc4f5b6b731,
   0x3bd9f2b43c4aa3d2,
   0x3bd8321cd035bc99,
   0x3bd68c2dde665d96,
   0x3bd4ff49f8d42aea,
   0x3bd389fee85e4f61,
   0x3bd22aff08ab1c4a,
   0x3bd0e11b717f3367,
   0x3bcf567dc9750674,
   0x3bcd10d2e96f9ef2,
   0x3bcaef59a90c2c0a,
   0x3bc8f052845783f5,
   0x3bc71215f54dde51,
   0x3bc553104efc6aca,
   0x3bc3b1be6c937e85,
   0x3bc22cab170a9721,
   0x3bc0c26d062d8eac,
   0x3bbee34ac8df49dd,
   0x3bbc71fd7eedf45c,
   0x3bba2e58d71a3394,
   0x3bb815d3c74be8b8,
   0x3bb62b6bbd6f3739,
   0x3bb4898ef7b988a8,
   0x3bb31b8bf94a2480,
   0x3bb1c53c4def12d8,
   0x3bb084dabcce84cc,
   0x3baeb1aef2022910]

theorem record2684ChunkBits228Length2685 :
    (record2684ChunkBits2282685).length = 32 := by
  decide

theorem record2684ChunkSum2282685 :
    ((record2684ChunkBits2282685).map binary64Value2674).sum =
      (286956795119098175 : ℚ) / 664613997892457936451903530140172288 := by
  norm_num [record2684ChunkBits2282685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7328 through 7359,
decoded and summed as exact rationals. -/
def record2684ChunkBits2292685 : List Nat :=
  [0x3bac7f9c7f00c0ee,
   0x3baa710459603c39,
   0x3ba883b03870c2e1,
   0x3ba6b5a25f4dfc6f,
   0x3ba5050cc4a1ee59,
   0x3ba370496d42a564,
   0x3ba1f5d3e402ef9c,
   0x3ba09443b5fb12d3,
   0x3b9e948fb2116efa,
   0x3b9c2d45c3dc5851,
   0x3b99f04fe030cefc,
   0x3b97db706c9edded,
   0x3b95ec821296d077,
   0x3b942174be448e23,
   0x3b92784b5941c6e3,
   0x3b90ef1a1f96d613,
   0x3b8f080b103cf52b,
   0x3b8c6a82cd5a4f10,
   0x3b8a02202552d2c8,
   0x3b87d76e5d875a4d,
   0x3b86145ec5f5145d,
   0x3b84739bb65e89b7,
   0x3b82ef55901eafcf,
   0x3b8185617e41d52d,
   0x3b8033d51d9efe6c,
   0x3b7df1f587a43871,
   0x3b7ba69752c4661b,
   0x3b7982d219328732,
   0x3b77842b559a38f7,
   0x3b75a861048528f0,
   0x3b73ed60b8c10f19,
   0x3b7251401a5e1fe1]

theorem record2684ChunkBits229Length2685 :
    (record2684ChunkBits2292685).length = 32 := by
  decide

theorem record2684ChunkSum2292685 :
    ((record2684ChunkBits2292685).map binary64Value2674).sum =
      (770351537288065119 : ℚ) / 21267647932558653966460912964485513216 := by
  norm_num [record2684ChunkBits2292685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7360 through 7391,
decoded and summed as exact rationals. -/
def record2684ChunkBits2302685 : List Nat :=
  [0x3b70d236a8d4e62e,
   0x3b6edd31323b4013,
   0x3b6c49a553f21294,
   0x3b69e6cd95f243cb,
   0x3b67b1d2eb62beed,
   0x3b65a7ff37343c4f,
   0x3b63c6ba1cecf33e,
   0x3b620b869887d647,
   0x3b60740143de8f49,
   0x3b5dfbbe4b479858,
   0x3b5b4dd81cb67471,
   0x3b58dac50bb6dd42,
   0x3b56c9e9349d0e5e,
   0x3b54ffe81bc529c2,
   0x3b535b3e069a7125,
   0x3b51d507f1c1ba53,
   0x3b506ae62efecf80,
   0x3b4e357cd142cedf,
   0x3b4bc55e798d601c,
   0x3b49821290007699,
   0x3b47688f7bc0adf0,
   0x3b45761311a8f9fc,
   0x3b43a81798634e3c,
   0x3b41fc4a92d70829,
   0x3b4070851bc8517c,
   0x3b3e058b3d8b4299,
   0x3b3b62557a6c893b,
   0x3b38f3de63fbceb3,
   0x3b36b6cd14c4a70d,
   0x3b34a7f51e9bdf17,
   0x3b32c4527d0713f5,
   0x3b3109066f564e8e]

theorem record2684ChunkBits230Length2685 :
    (record2684ChunkBits2302685).length = 32 := by
  decide

theorem record2684ChunkSum2302685 :
    ((record2684ChunkBits2302685).map binary64Value2674).sum =
      (210481531240867407 : ℚ) / 85070591730234615865843651857942052864 := by
  norm_num [record2684ChunkBits2302685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7392 through 7423,
decoded and summed as exact rationals. -/
def record2684ChunkBits2312685 : List Nat :=
  [0x3b2ee6aa1b3ccfd6,
   0x3b2c014766211ef2,
   0x3b295ced0de21447,
   0x3b26f4e103b9e38f,
   0x3b24e78452700ac9,
   0x3b230db536c4f1c3,
   0x3b2176112c26e22d,
   0x3b200213c4340876,
   0x3b1d55670f979b3b,
   0x3b1adb46eff1cfec,
   0x3b1891b1274a84ee,
   0x3b1674fc96225857,
   0x3b1481ded2725911,
   0x3b12b55e29757739,
   0x3b110cc4ed576a2d,
   0x3b0f0b2eba7cb6f2,
   0x3b0c3b169280d5cb,
   0x3b09a5026a867bb6,
   0x3b0744fd83b71fac,
   0x3b0517544e78403f,
   0x3b03188d2761cad7,
   0x3b014562895c0d84,
   0x3aff357cdb9153ed,
   0x3afc2b6d3bb3bedb,
   0x3af96713836d7f1c,
   0x3af6e33a9409d218,
   0x3af49af53d0ac441,
   0x3af2899cdfcfbd3c,
   0x3af0c61453c4675b,
   0x3aee5ece5c56497f,
   0x3aeb80446520758e,
   0x3ae90c9cc5d4c291]

theorem record2684ChunkBits231Length2685 :
    (record2684ChunkBits2312685).length = 32 := by
  decide

theorem record2684ChunkSum2312685 :
    ((record2684ChunkBits2312685).map binary64Value2674).sum =
      (737320608396216585 : ℚ) / 5444517870735015415413993718908291383296 := by
  norm_num [record2684ChunkBits2312685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7424 through 7455,
decoded and summed as exact rationals. -/
def record2684ChunkBits2322685 : List Nat :=
  [0x3ae6d3de49891b70,
   0x3ae4c9c315717911,
   0x3ae2ea65913013ea,
   0x3ae1324e219e9787,
   0x3adf3cc0d190f6a4,
   0x3adc579deef9c951,
   0x3ad9b01fa8090d08,
   0x3ad741a494316c3e,
   0x3ad507edae045eb4,
   0x3ad2ff110f93a424,
   0x3ad1236f1f3664a8,
   0x3acee353893ec8ee,
   0x3acbcd3a94c4bce6,
   0x3ac8feb53818ac5e,
   0x3ac6724538e1f078,
   0x3ac422c4b4d06ef4,
   0x3ac20b5fe7af3d7c,
   0x3ac027905fe1386a,
   0x3abce62eeb3d45a6,
   0x3ab9d3f742a15459,
   0x3ab7350927ae5ff0,
   0x3ab4e267e17d85f9,
   0x3ab2c4ebac0cd94e,
   0x3ab0dfa7e7d4e61d,
   0x3aae87e8b1c7e12f,
   0x3aaba37b235fdb43,
   0x3aa8fffd380cf07d,
   0x3aa697c082920a2f,
   0x3aa465b544c79cb2,
   0x3aa265503e3bb65a,
   0x3aa0927892954464,
   0x3a9dd2ef3d7f3ad3]

theorem record2684ChunkBits232Length2685 :
    (record2684ChunkBits2322685).length = 32 := by
  decide

theorem record2684ChunkSum2322685 :
    ((record2684ChunkBits2322685).map binary64Value2674).sum =
      (2076153337438870347 : ℚ) / 348449143727040986586495598010130648530944 := by
  norm_num [record2684ChunkBits2322685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7456 through 7487,
decoded and summed as exact rationals. -/
def record2684ChunkBits2332685 : List Nat :=
  [0x3a9acdd5c5e11493,
   0x3a980f71aa991206,
   0x3a95920f7acdb01c,
   0x3a93506c7c55b116,
   0x3a9145aa7eea125a,
   0x3a8eda8bcfa6444f,
   0x3a8b861b083d09a9,
   0x3a88863784cfd21d,
   0x3a85d3a20c309c09,
   0x3a83679e17452ed1,
   0x3a813be839ae3ace,
   0x3a7e955faad4e4c5,
   0x3a7b444f5ba83e96,
   0x3a78606cfbfafe34,
   0x3a75c32b4596bd7f,
   0x3a7366bb4d61f01f,
   0x3a714d972d7ac8d3,
   0x3a6f12805f72c2b7,
   0x3a6bebc9a84c5181,
   0x3a6910fb435f2837,
   0x3a667b135bef8708,
   0x3a6423d38473c1a7,
   0x3a6205a1a3d161bc,
   0x3a601b71982368da,
   0x3a5cc163b11657f2,
   0x3a59a275aa5c5abc,
   0x3a56d28368364be8,
   0x3a544a9ae476d3dc,
   0x3a52045be9ea51ea,
   0x3a4ff3d2ac408662,
   0x3a4c4bb9aeced293,
   0x3a49067943167cc6]

theorem record2684ChunkBits233Length2685 :
    (record2684ChunkBits2332685).length = 32 := by
  decide

theorem record2684ChunkSum2332685 :
    ((record2684ChunkBits2332685).map binary64Value2674).sum =
      (2205541851532213683 : ℚ) / 11150372599265311570767859136324180752990208 := by
  norm_num [record2684ChunkBits2332685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7488 through 7519,
decoded and summed as exact rationals. -/
def record2684ChunkBits2342685 : List Nat :=
  [0x3a461ae559f76294,
   0x3a43808ab837a670,
   0x3a412fa0a70795f3,
   0x3a3e41fbbc7a5555,
   0x3a3abe352c97cc19,
   0x3a37bbfc7a574356,
   0x3a35087c67b3ceb5,
   0x3a329ca2940173fc,
   0x3a3071ee0cf1b6a5,
   0x3a2d134cc2f4c202,
   0x3a29e2d04a510b5d,
   0x3a2711ab214a4a7c,
   0x3a24898d7aa3e97e,
   0x3a22434d08fd32ca,
   0x3a20388957eb9680,
   0x3a1cc719def49f94,
   0x3a197e6cba2f51dc,
   0x3a168dc96cf933b3,
   0x3a13ecce119df7a5,
   0x3a1193ddfe68fc10,
   0x3a0ef8176d6af04b,
   0x3a0b3e0d25f0b4d4,
   0x3a07ee16ba3389cb,
   0x3a04fdae86692a19,
   0x3a026339444ec597,
   0x3a0015f2d075933c,
   0x39fc1bb87ec4d0bb,
   0x39f88759600ae03b,
   0x39f5782e57a7e3de,
   0x39f2e64d325fb9cb,
   0x39f09c973313f8a1,
   0x39ed27ee30937957]

theorem record2684ChunkBits234Length2685 :
    (record2684ChunkBits2342685).length = 32 := by
  decide

theorem record2684ChunkSum2342685 :
    ((record2684ChunkBits2342685).map binary64Value2674).sum =
      (3373036331708825887 : ℚ) / 713623846352979940529142984724747568191373312 := by
  norm_num [record2684ChunkBits2342685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7520 through 7551,
decoded and summed as exact rationals. -/
def record2684ChunkBits2352685 : List Nat :=
  [0x39e98bf2db92714b,
   0x39e65979a922a1a7,
   0x39e3906dd13543f7,
   0x39e140f79f13478b,
   0x39de77ef26671f53,
   0x39dadef861ef3fca,
   0x39d7ab2c75f45daf,
   0x39d4d20351643ec1,
   0x39d24a18cec8fcca,
   0x39d00b060c484290,
   0x39cc1a81f27d1017,
   0x39c89401c10537d3,
   0x39c5764ff0fe1059,
   0x39c2b661433a08ad,
   0x39c04a3b23df26d0,
   0x39bc51b14dd80375,
   0x39b89426699f8ea7,
   0x39b54d1c9ca1e2ac,
   0x39b26f4a6e77da92,
   0x39afdd6ad35c52e0,
   0x39ab96483220dbee,
   0x39a81094b4037555,
   0x39a4f54e51a5b646,
   0x39a2390aa8cd8376,
   0x399fa300b0c1eb9b,
   0x399b6ad210659310,
   0x3997b8cfa1425e68,
   0x399489f1756cf80f,
   0x3991ebf3f6839438,
   0x398f51d70c8e7a1f,
   0x398b54d7adcd005d,
   0x3987d169c13c2020]

theorem record2684ChunkBits235Length2685 :
    (record2684ChunkBits2352685).length = 32 := by
  decide

theorem record2684ChunkSum2352685 :
    ((record2684ChunkBits2352685).map binary64Value2674).sum =
      (920563881593238879 : ℚ) / 11417981541647679048466287755595961091061972992 := by
  norm_num [record2684ChunkBits2352685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7552 through 7583,
decoded and summed as exact rationals. -/
def record2684ChunkBits2362685 : List Nat :=
  [0x3984b9ddd979b5ae,
   0x3982021273cc7c06,
   0x397f3e7f3c39c35e,
   0x397b0f965a461a7c,
   0x397766475a2fe940,
   0x39743343477057ce,
   0x397168db166e52f2,
   0x396df5a641a62550,
   0x3969bc794d4e1b46,
   0x396612a88a52cf55,
   0x3962e6c84d56c65c,
   0x3960295220a2e7e6,
   0x395ba3c5c0f3cd26,
   0x3957dd7ddc921099,
   0x3954923870888e47,
   0x3951b388009e529c,
   0x394e692673f5e9d9,
   0x394a13cf7ae07de3,
   0x394652a6b9930f31,
   0x39431384f9e717a0,
   0x3940507fb3fa5b57,
   0x393c21d32de3cee3,
   0x39384b4900e6812e,
   0x3934f30568b51e96,
   0x39320990f345eb26,
   0x392f02b99f7d8521,
   0x392a9cfac3c2956d,
   0x3926cce543911a78,
   0x39237ff30e0e4898,
   0x3920a5c90a3159bb,
   0x391c5fe954ee0714,
   0x3918236650fe7ef6]

theorem record2684ChunkBits236Length2685 :
    (record2684ChunkBits2362685).length = 32 := by
  decide

theorem record2684ChunkSum2362685 :
    ((record2684ChunkBits2362685).map binary64Value2674).sum =
      (337876580685659829 : ℚ) / 365375409332725729550921208179070754913983135744 := by
  norm_num [record2684ChunkBits2362685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7584 through 7615,
decoded and summed as exact rationals. -/
def record2684ChunkBits2372685 : List Nat :=
  [0x39147f810e12a54b,
   0x39116059e1469d49,
   0x390d68dd67fc05f0,
   0x3908d8ae93b4b54c,
   0x3904f5181a4ad312,
   0x3901e1cf9d332369,
   0x38fe78990e317769,
   0x38f9ea1996dd4b9d,
   0x38f5ffb9d65557f3,
   0x38f2a405e2551309,
   0x38ef8846b72a0aa2,
   0x38ea9f07ff7c499c,
   0x38e66f443b4a4e51,
   0x38e2ec21a458af1b,
   0x38e018556d31090c,
   0x38db6e20c7ac3e92,
   0x38d756204e715a5c,
   0x38d3d1ec2b8aae96,
   0x38d0cdc635a1a213,
   0x38cc7102817eab9e,
   0x38c8064ee50adc50,
   0x38c4415df4b3e087,
   0x38c10b74320df0cf,
   0x38bca183a337efd3,
   0x38b8000b4772ea90,
   0x38b4147912c987cc,
   0x38b0c4b745a5fcb3,
   0x38abf446cfb393b7,
   0x38a742493e03aabb,
   0x38a38b042943835f,
   0x38a06eb3032ddd01,
   0x389b94d03d2410e4]

theorem record2684ChunkBits237Length2685 :
    (record2684ChunkBits2372685).length = 32 := by
  decide

theorem record2684ChunkSum2372685 :
    ((record2684ChunkBits2372685).map binary64Value2674).sum =
      (300802855732269987 : ℚ) / 46768052394588893382517914646921056628989841375232 := by
  norm_num [record2684ChunkBits2372685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7616 through 7647,
decoded and summed as exact rationals. -/
def record2684ChunkBits2382685 : List Nat :=
  [0x38971a4174d565bd,
   0x3893504118081111,
   0x38901d4b4d4ddd9e,
   0x388ad69c8d518d06,
   0x38864e7287b60ca1,
   0x38828134a813d2c1,
   0x387ebab131c5ade0,
   0x3879bd12fda71469,
   0x38759a2729c411dc,
   0x387219136126c547,
   0x386e447c1d18d342,
   0x386942d2f43d614b,
   0x38650a686a9fa22f,
   0x38617d604114b4df,
   0x385d0428e667c9f7,
   0x385804ff0bc7a25a,
   0x3853d77ad45d1e1b,
   0x38505b3d250de808,
   0x384ae92964549411,
   0x384617b4455a41ed,
   0x384219c914ec93b3,
   0x383de262e00aee6d,
   0x3838c0afc140d10d,
   0x38347610ebada105,
   0x3830e11b01889661,
   0x382bcaa8edf3459d,
   0x3826d4fddb6a441e,
   0x3822b7f81efc3ec7,
   0x381ea124519eaba4,
   0x38190234b1a759fe,
   0x381460df35883190,
   0x38109eeb75addd5d]

theorem record2684ChunkBits238Length2685 :
    (record2684ChunkBits2382685).length = 32 := by
  decide

theorem record2684ChunkSum2382685 :
    ((record2684ChunkBits2382685).map binary64Value2674).sum =
      (9956157982322222139 : ℚ) / 383123885216472214589586756787577295904684780545900544 := by
  norm_num [record2684ChunkBits2382685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7648 through 7679,
decoded and summed as exact rationals. -/
def record2684ChunkBits2392685 : List Nat :=
  [0x380b5b978b07a9a4,
   0x380690d05593e980,
   0x38029363966a28dc,
   0x37fe84df4ba7680b,
   0x37f9045a832920dc,
   0x37f476457c9cab78,
   0x37f0b2f5d7d73554,
   0x37eb31de05d6c51e,
   0x37e617e6bc05d24b,
   0x37e1e874e06d2d79,
   0x37dcf7169bcc98e9,
   0x37d75f3697710619,
   0x37d2d1175df82a62,
   0x37ce7064b160cd9f,
   0x37c8c80de843b053,
   0x37c421ff4ffb4d52,
   0x37c0522806f8b4b6,
   0x37ba675b98d6ffa5,
   0x37b54f8c52bcd141,
   0x37b1297f2d8b0383,
   0x37ab94c813d9bc19,
   0x37a61d3fe87f6c8d,
   0x37a1b14b76646c18,
   0x379c3ff09041e6e7,
   0x379692fc3022abfd,
   0x3792350fc1f8354d,
   0x378d71020348377e,
   0x3787c01f0c89c665,
   0x37831d89269cf4f6,
   0x377eb2688e8865fb,
   0x377896957d53fb4a,
   0x3773a59bf8e3597f]

theorem record2684ChunkBits239Length2685 :
    (record2684ChunkBits2392685).length = 32 := by
  decide

theorem record2684ChunkSum2392685 :
    ((record2684ChunkBits2392685).map binary64Value2674).sum =
      (10831633300743296253 : ℚ) / 196159429230833773869868419475239575503198607639501078528 := by
  norm_num [record2684ChunkBits2392685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7680 through 7711,
decoded and summed as exact rationals. -/
def record2684ChunkBits2402685 : List Nat :=
  [0x376f51cca26fad89,
   0x3768e6c0b189fae4,
   0x3763bfc3e5b54c1f,
   0x375f3f6c88a4c4d0,
   0x3758a8dd2957fcc8,
   0x37537b096bb23683,
   0x374f1896583c1bd5,
   0x3748c3562c75a714,
   0x3743acb60053032b,
   0x373f30e12f2b603a,
   0x3738aa76c915ba3a,
   0x373375ab32c049c2,
   0x372ea1b9e78f5df3,
   0x37280d4be23d1d05,
   0x3722d757a0ec5f52,
   0x371d7344412b495e,
   0x3716f6d8e29db738,
   0x3711ec3e96199410,
   0x370c3ea4a91c20ed,
   0x3706503611d51313,
   0x370195607d046abd,
   0x36fba4317196d30d,
   0x36f5ab4f04562aa0,
   0x36f0f12415a4dedb,
   0x36ea6b9aa9c3c262,
   0x36e48b64d37d422c,
   0x36dfdcfd3d913212,
   0x36d8a41bf06172d6,
   0x36d300ece11af61e,
   0x36cd3b64fe449155,
   0x36c6c99097f7d5ab,
   0x36c1bb163bc28265]

theorem record2684ChunkBits240Length2685 :
    (record2684ChunkBits2402685).length = 32 := by
  decide

theorem record2684ChunkSum2402685 :
    ((record2684ChunkBits2402685).map binary64Value2674).sum =
      (43446888594829655545 : ℚ) / 803469022129495137770981046170581301261101496891396417650688 := by
  norm_num [record2684ChunkBits2402685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7712 through 7743,
decoded and summed as exact rationals. -/
def record2684ChunkBits2412685 : List Nat :=
  [0x36bb86706709d0be,
   0x36b54fca06a0a7db,
   0x36b0758a69fdf844,
   0x36a95bb37384a496,
   0x36a37bff82ee9821,
   0x369ddd927a385cc1,
   0x3696d496e727fae5,
   0x3691688a1f1f51ed,
   0x368a7b51cf937927,
   0x368417bfd0c23715,
   0x367e84185f8a58df,
   0x3677669b70f593d5,
   0x3671fe77b9573777,
   0x366b9868a331d7ae,
   0x36651961bf663338,
   0x366015c35cc03315,
   0x365873bd00cafa56,
   0x365287abfa722022,
   0x364bffce50185646,
   0x364516e5192664b1,
   0x363fac449e2b4afe,
   0x3637b621a71b3983,
   0x3631e89d5d0bc24a,
   0x362b201562b49c0d,
   0x36247d19f72ced2e,
   0x361ede562e1ed22d,
   0x361730a4fe8e5ad4,
   0x36115f9c09c78bb5,
   0x3609f5965661e13f,
   0x3603570ba74f2ce5,
   0x35fcbc9c54e9f7f6,
   0x35f54a4fa36a02ad]

theorem record2684ChunkBits241Length2685 :
    (record2684ChunkBits2412685).length = 32 := by
  decide

theorem record2684ChunkSum2412685 :
    ((record2684ChunkBits2412685).map binary64Value2674).sum =
      (137338798717426540971 : ℚ) / 6582018229284824168619876730229402019930943462534319453394436096 := by
  norm_num [record2684ChunkBits2412685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7744 through 7775,
decoded and summed as exact rationals. -/
def record2684ChunkBits2422685 : List Nat :=
  [0x35ef75bf4da26582,
   0x35e72e399c33b7a5,
   0x35e108da9f7a96ac,
   0x35d90df54c740e7b,
   0x35d29c22961f6772,
   0x35cbb9bf8725db22,
   0x35c49680c8a0d789,
   0x35be7a14642f0ad2,
   0x35b67be3e600401b,
   0x35b0883c2768722d,
   0x35a83af04c326756,
   0x35a1b247642ed66c,
   0x3599c2d979ec170b,
   0x3592afcf2838a2eb,
   0x358b334526fff57f,
   0x3583f42f0da9f99e,
   0x357d314444033e4a,
   0x35754ac07183d5cd,
   0x356ef796faa3e872,
   0x3566739ac84e9862,
   0x35603a6bdb700c89,
   0x35576356af98936c,
   0x3550cd3bf5c93066,
   0x354810f9847e7720,
   0x35412ef2b81f0774,
   0x353876b6f5c5646e,
   0x35315cc14db4ea13,
   0x35289289f4a34dd2,
   0x352165ed0aa7de1f,
   0x3518e36598c5cd7a,
   0x3511dab49ed8a53c,
   0x35098659f36be97a]

theorem record2684ChunkBits242Length2685 :
    (record2684ChunkBits2422685).length = 32 := by
  decide

theorem record2684ChunkSum2422685 :
    ((record2684ChunkBits2422685).map binary64Value2674).sum =
      (276334983295495492857 : ℚ) / 107839786668602559178668060348078522694548577690162289924414440996864 := by
  norm_num [record2684ChunkBits2422685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7776 through 7807,
decoded and summed as exact rationals. -/
def record2684ChunkBits2432685 : List Nat :=
  [0x35022dc65820dc3f,
   0x34f9cc5704388f0b,
   0x34f23cb358c24c86,
   0x34e9afd248f1f0ee,
   0x34e2056244214047,
   0x34d9307492fa7903,
   0x34d18cde5d412b5b,
   0x34c8cb683185c240,
   0x34c175bba263e4c4,
   0x34b882e162e909b0,
   0x34b12628257a77e6,
   0x34a7eab2945a1413,
   0x34a09f2a0b13c924,
   0x3497068328373a14,
   0x348fc9a8382f35ba,
   0x3485de0eba863d32,
   0x347dfbc9f1d14f59,
   0x34747c7b654ad861,
   0x346be675496bc3fa,
   0x3462ef7a7b0b9167,
   0x34599e4cda9a30e9,
   0x345155e6d7fe201d,
   0x3447b42053438ecf,
   0x34404110cc0885f1,
   0x343633576ccfa41f,
   0x342e324b9e9e330e,
   0x34247327084696ce,
   0x341b94a4eeae619b,
   0x341284f1dd863290,
   0x3408c33c23516234,
   0x34007bc4bb859e26,
   0x33f61fcb9ec50f59]

theorem record2684ChunkBits243Length2685 :
    (record2684ChunkBits2432685).length = 32 := by
  decide

theorem record2684ChunkSum2432685 :
    ((record2684ChunkBits2432685).map binary64Value2674).sum =
      (2273177231067195766153 : ℚ) / 28269553036454149273332760011886696253239742350009903329945699220681916416 := by
  norm_num [record2684ChunkBits2432685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7808 through 7839,
decoded and summed as exact rationals. -/
def record2684ChunkBits2442685 : List Nat :=
  [0x33edc50cc1e8cf56,
   0x33e3f5208f0381d6,
   0x33daa96cfcf5522a,
   0x33d1be4db5cb3473,
   0x33c787258e6a0f6f,
   0x33bf14890a0dacb8,
   0x33b47337f665abe4,
   0x33aacee5674c8af4,
   0x33a18107b8923fa6,
   0x3396c52c2ba83117,
   0x338d81e290aefb93,
   0x33830bd76705d66e,
   0x33787ec9232fdf97,
   0x336f62ed087c0366,
   0x33641b9cd58c04ed,
   0x335a0832802b2f99,
   0x3350e69d058beaa3,
   0x3345d77c6638ec49,
   0x333c17abeac4c788,
   0x3331fa99f84b1df2,
   0x3326e6904377d672,
   0x331d06c51a8c7829,
   0x33124deb7eb7da69,
   0x3307161bee0e48d3,
   0x32fd6504815f0efe,
   0x32f2a36c69bf6c1e,
   0x32e78a1ae8f1a661,
   0x32dd9af6c2c7cf8e,
   0x32d289cbb5011b33,
   0x32c71df242e79b6e,
   0x32bcb3a0ed4f9696,
   0x32b1bd70497c74b1]

theorem record2684ChunkBits244Length2685 :
    (record2684ChunkBits2442685).length = 32 := by
  decide

theorem record2684ChunkSum2442685 :
    ((record2684ChunkBits2442685).map binary64Value2674).sum =
      (13138242252290033495503 : ℚ) / 29642774844752946028434172162224104410437116074403984394101141506025761187823616 := by
  norm_num [record2684ChunkBits2442685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7840 through 7871,
decoded and summed as exact rationals. -/
def record2684ChunkBits2452685 : List Nat :=
  [0x32a5d555721cbff4,
   0x329ac0c1b71700df,
   0x32905183c3d59a07,
   0x3283d1eaa75b1c51,
   0x3277f7c0fe937cd4,
   0x326cdbaf179fca85,
   0x32614c83ec97551a,
   0x3254bab9f155b53a,
   0x324918fbb51efac9,
   0x323e78ef903e6f56,
   0x323265d18cbaefa7,
   0x3226179b0cd3d152,
   0x321a615473e89d9f,
   0x320f5298d293f9df,
   0x32027d57ed730569,
   0x31f5b4094e36ef73,
   0x31e9bd77ff2c6de8,
   0x31de7c64f0c4ec9f,
   0x31d1f7f2e28db4ea,
   0x31c5147a8335af2b,
   0x31b89c1529fcc2ba,
   0x31ac96a3b0eb8dae,
   0x31a085ae3b10652a,
   0x31930043bed91f40,
   0x3185bd9c44e4b66d,
   0x3178bf850df00f3b,
   0x316c06ee795dfd8b,
   0x315f93d014c2e1bb,
   0x3151b289a3ab079d,
   0x3143bc4382fc259b,
   0x3135e56f7e3438e9,
   0x31282be035e02d1a]

theorem record2684ChunkBits245Length2685 :
    (record2684ChunkBits2452685).length = 32 := by
  decide

theorem record2684ChunkSum2452685 :
    ((record2684ChunkBits2452685).map binary64Value2674).sum =
      (32961451128551800365933 : ℚ) / 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264 := by
  norm_num [record2684ChunkBits2452685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7872 through 7903,
decoded and summed as exact rationals. -/
def record2684ChunkBits2462685 : List Nat :=
  [0x311aa6fe06d59a1d,
   0x310db0054520ccbe,
   0x3100938f0f8e21de,
   0x30f2644575bf3fd1,
   0x30e445d2ecf664cd,
   0x30d633017d72b81e,
   0x30c825c0c97929a8,
   0x30ba173912d3489f,
   0x30ac31bc9d13ff44,
   0x309eab7dd776c364,
   0x309096f712d301d3,
   0x3081d8ac4bd0b7ae,
   0x307316a963937a6b,
   0x30644c73af7acb88,
   0x305575649a95d24f,
   0x30468cc6e34d861b,
   0x30378df6b5ea54ae,
   0x302874839a529a99,
   0x30193c52fd85f994,
   0x3009e1c1fce25038,
   0x2ffa61c505446d14,
   0x2feaba03d4e249c4,
   0x2fdae8f07de0aafe,
   0x2fcaedd829b10d70,
   0x2fbac8ec91b74768,
   0x2faa95fc6ccf77b4,
   0x2f9aa5c171b12ba4,
   0x2f8ac378b8b71a93,
   0x2f7aac1f1def503d,
   0x2f6a5fd0387d24d3,
   0x2f59dfdff1c1c677,
   0x2f492ecca81631b7]

theorem record2684ChunkBits246Length2685 :
    (record2684ChunkBits2462685).length = 32 := by
  decide

theorem record2684ChunkSum2462685 :
    ((record2684ChunkBits2462685).map binary64Value2674).sum =
      (9058676630183149533982345 : ℚ) / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288 := by
  norm_num [record2684ChunkBits2462685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7904 through 7935,
decoded and summed as exact rationals. -/
def record2684ChunkBits2472685 : List Nat :=
  [0x2f38502d15def4b0,
   0x2f27aeb7929a6b58,
   0x2f16fb474e7457aa,
   0x2f0626ba7192a6fb,
   0x2ef53461668a135b,
   0x2ee4282d3656bbdc,
   0x2ed3068c65a52eab,
   0x2ec1d4445859c534,
   0x2eb096490bf8ac41,
   0x2e9ea329f13b50bb,
   0x2e8c16059efaf4b9,
   0x2e798e553f00b199,
   0x2e6714874f9fe373,
   0x2e54b017a36bd468,
   0x2e42676ae84b8abe,
   0x2e303fb752ab0a7a,
   0x2e1c79f49db877e3,
   0x2e08c3f4f6535128,
   0x2df576d537435f35,
   0x2de2c5a3a3870078,
   0x2dd06fc17549b60e,
   0x2dbc82fe13f0ac32,
   0x2da87e69da250387,
   0x2d94d71e6cfdae71,
   0x2d818f5fd7ba8df0,
   0x2d6d7b61b19022a7,
   0x2d58dd4de1f318bc,
   0x2d44cbe1078f62f8,
   0x2d313f396f2003c3,
   0x2d1c5c602f18574d,
   0x2d071d5f9f9c55cf,
   0x2cf2ac1fba63bc62]

theorem record2684ChunkBits247Length2685 :
    (record2684ChunkBits2472685).length = 32 := by
  decide

theorem record2684ChunkSum2472685 :
    ((record2684ChunkBits2472685).map binary64Value2674).sum =
      (228149625897607133821261753 : ℚ) / 36695977855841144185773134324833391052745039826692497979801421430190766017415756929120296849762010984873984 := by
  norm_num [record2684ChunkBits2472685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7936 through 7967,
decoded and summed as exact rationals. -/
def record2684ChunkBits2482685 : List Nat :=
  [0x2cdde5af4bd84baf,
   0x2cc7b7ceb05e84a8,
   0x2cb2a4c2c6e34656,
   0x2c9d09e9197208c2,
   0x2c86676ec1364b49,
   0x2c711f711046c69a,
   0x2c59eceffbafd867,
   0x2c4370b4560069b2,
   0x2c2ce0558269c2b5,
   0x2c153dbb81f5707d,
   0x2bfef35df239c6cb,
   0x2be66d4ce4aa1814,
   0x2bd0607652ac2561,
   0x2bb7e8ffc8ea751d,
   0x2ba13f95bb297d4b,
   0x2b8896daf0d68711,
   0x2b715117a9261748,
   0x2b58182c65751fca,
   0x2b40cd3344047a8b,
   0x2b274c6fbb531cdc,
   0x2b0ff60360131065,
   0x2af5aeb06758d2f9,
   0x2add17809f424300,
   0x2ac34be4bbb8466d,
   0x2aa94e416856cf40,
   0x2a90669d9af91a14,
   0x2a750278bfc5ae28,
   0x2a5a981bc06bd05d,
   0x2a40a12d896cb692,
   0x2a248b93aaafb725,
   0x2a09127cd263c3ea,
   0x29ee3812a099824b]

theorem record2684ChunkBits248Length2685 :
    (record2684ChunkBits2482685).length = 32 := by
  decide

theorem record2684ChunkSum2482685 :
    ((record2684ChunkBits2482685).map binary64Value2674).sum =
      (1955398024367730959148876826435 : ℚ) / 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032 := by
  norm_num [record2684ChunkBits2482685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 7968 through 7999,
decoded and summed as exact rationals. -/
def record2684ChunkBits2492685 : List Nat :=
  [0x29d1fc11f73029aa,
   0x29b52387803ceb90,
   0x29988881d5f3d60f,
   0x297c1ce12d7bab61,
   0x295ff134d93db7e9,
   0x29423eae292e83f4,
   0x2924c8ad1faec6ca,
   0x290750b042b43aa1,
   0x28e9c099c4e5f324,
   0x28cc008c75040d71,
   0x28ae0c6ecc72d9b6,
   0x289024e1d1fd5e67,
   0x28711a03bbe06b50,
   0x2851dac31286881e,
   0x28325dedbb55fe2b,
   0x28129cad4ad7910e,
   0x27f29317aad9fbce,
   0x27d2408ca46dc11c,
   0x27b1a7d4d671e3ef,
   0x2790cefced83fb5d,
   0x276f7dde615674f6,
   0x274d05a95c58f799,
   0x272a4e9b05701535,
   0x27077327f1cfd118,
   0x26e48d3ffe9905bb,
   0x26c1b4bef650619e,
   0x269dfc521536291d,
   0x2678f394f9b6dae9,
   0x26546689f6fc5370,
   0x263075476727b873,
   0x260a96646ab76172,
   0x25e5529903609d55]

theorem record2684ChunkBits249Length2685 :
    (record2684ChunkBits2492685).length = 32 := by
  decide

theorem record2684ChunkSum2492685 :
    ((record2684ChunkBits2492685).map binary64Value2674).sum =
      (65984789244321755041592378399925117 : ℚ) / 1524291284333980581729295522359944485228807686848130444755447734192076044345588681699368214386470689042884243711624327585667956874652483059712 := by
  norm_num [record2684ChunkBits2492685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 8000 through 8031,
decoded and summed as exact rationals. -/
def record2684ChunkBits2502685 : List Nat :=
  [0x25c0bfbc28178155,
   0x2599c42595ce0d54,
   0x2573670c753f84dd,
   0x254cded12e66b142,
   0x25253e74d95babbf,
   0x24fea450ac28c26c,
   0x24d5a67e52567424,
   0x24adf688a43c09ba,
   0x24844c5c278b9186,
   0x245aea31f6fe6b81,
   0x243174fd95445b32,
   0x24062572cd0cfa2a,
   0x23db776f4439f4bf,
   0x23b0a540d0a9b7aa,
   0x2383b5cb9b7ea6c7,
   0x2356cafc41006cc6,
   0x2329bb7351ef0dc6,
   0x22fc59f023a5d750,
   0x22ce798a6f6b9eb8,
   0x229ff285bfa5008b,
   0x227053877642778d,
   0x2240438f7e20c91f,
   0x220fb61b601992a0,
   0x21deb74c61666d00,
   0x21ad4f14530f1279,
   0x217b25df7565a8a4,
   0x2148668c0554c506,
   0x211545789e77258e,
   0x20e241379a9c8693,
   0x20ae8246f46789cf,
   0x2078bd7f73a66a02,
   0x204374fd7795b43b]

theorem record2684ChunkBits250Length2685 :
    (record2684ChunkBits2502685).length = 32 := by
  decide

theorem record2684ChunkSum2502685 :
    ((record2684ChunkBits2502685).map binary64Value2674).sum =
      (1804455078942999907224418198369063789233163 : ℚ) / 1886981212410770676120777290494134445458460610208220214188103150122812081196074426043063362588829383770734187515381922449885292314962396316280717125716348021824697663488 := by
  norm_num [record2684ChunkBits2502685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 8032 through 8063,
decoded and summed as exact rationals. -/
def record2684ChunkBits2512685 : List Nat :=
  [0x200da9ae940a2856,
   0x1fd5e70ab78dcbcc,
   0x1f9f50054f507bc1,
   0x1f65a7c2e2125e4c,
   0x1f2cf636f76fd8a3,
   0x1ef2b6d7b0b4a75e,
   0x1eb75b11f6717f36,
   0x1e7c21e03b255de6,
   0x1e405b4f0f28039f,
   0x1e0296cbab4ca48f,
   0x1dc881221fddf9ca,
   0x1da939d47e4b936b,
   0x1da934aa7568cd8f,
   0x1da92f817b2b017c,
   0x1da92a598f5ae608,
   0x1da92532b1c0c277,
   0x1da9200ce225a1c8,
   0x1da91ae820521f5b,
   0x1da915c46c0f009a,
   0x1da910a1c5251643,
   0x1da90b802b5d3c5e,
   0x1da9065f9e805a3c,
   0x1da901401e576276,
   0x1da8fc21aaab52eb,
   0x1da8f70443455337,
   0x1da8f1e7e7ee1c44,
   0x1da8eccc986f2930,
   0x1da8e7b254918658,
   0x1da8e2991c1e69cc,
   0x1da8dd80eedf14df,
   0x1da8d869cc9cd410,
   0x1da8d353b520ff13]

theorem record2684ChunkBits251Length2685 :
    (record2684ChunkBits2512685).length = 32 := by
  decide

theorem record2684ChunkSum2512685 :
    ((record2684ChunkBits2512685).map binary64Value2674).sum =
      (2527589865426375785055184553 : ℚ) / 8299031137761985917024815727382322302024892464484873799991314659381305622825816292799414097894207588576395773222601578364790302150823550615773749668227927374122363606803019047370752 := by
  norm_num [record2684ChunkBits2512685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 8064 through 8095,
decoded and summed as exact rationals. -/
def record2684ChunkBits2522685 : List Nat :=
  [0x1da8ce3ea834f8cf,
   0x1da8c92aa5a22f56,
   0x1da8c417ad323a26,
   0x1da8bf05beae42eb,
   0x1da8b9f4d9e033f8,
   0x1da8b4e4fe9189be,
   0x1da8afd62c8bea17,
   0x1da8aac8639905fa,
   0x1da8a5bba382997f,
   0x1da8a0afec126bd8,
   0x1da89ba53d124f53,
   0x1da8969b964c2152,
   0x1da89192f789e84c,
   0x1da88c8b60953dcc,
   0x1da88784d1387a76,
   0x1da8827f493d89f0,
   0x1da87d7ac86e80f2,
   0x1da878774e957f3a,
   0x1da87374db7caf90,
   0x1da86e736eee47c3,
   0x1da8697308b488a2,
   0x1da86473a899bdfe,
   0x1da85f754e685c68,
   0x1da85a77f9ea6c63,
   0x1da8557baaeab403,
   0x1da8508061338d3e,
   0x1da84b861c8f7ac8,
   0x1da8468cdcc90a47,
   0x1da84194a1aad452,
   0x1da83c9d6aff7c6f,
   0x1da837a73891b110,
   0x1da832b20a2c2b94]

theorem record2684ChunkBits252Length2685 :
    (record2684ChunkBits2522685).length = 32 := by
  decide

theorem record2684ChunkSum2522685 :
    ((record2684ChunkBits2522685).map binary64Value2674).sum =
      (110340988301670155 : ℚ) / 4149515568880992958512407863691161151012446232242436899995657329690652811412908146399707048947103794288197886611300789182395151075411775307886874834113963687061181803401509523685376 := by
  norm_num [record2684ChunkBits2522685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 8096 through 8127,
decoded and summed as exact rationals. -/
def record2684ChunkBits2532685 : List Nat :=
  [0x1da82dbddf99cdc4,
   0x1da828cab8a50e36,
   0x1da823d895191f90,
   0x1da81ee774c0c93e,
   0x1da819f75766fb08,
   0x1da815083cd6af9f,
   0x1da8101a24daec86,
   0x1da80b2d0f3ec21e,
   0x1da80640fbcd4b9b,
   0x1da80155ea51af08,
   0x1da7fc6bda973a88,
   0x1da7f782cc68d1e7,
   0x1da7f29abf921380,
   0x1da7edb3b3de334c,
   0x1da7e8cda9188d54,
   0x1da7e3e89f0c8870,
   0x1da7df0495859632,
   0x1da7da218c4f32f7,
   0x1da7d53f8334e5da,
   0x1da7d05e7a0240b0,
   0x1da7cb7e7082fd1c,
   0x1da7c69f66826b42,
   0x1da7c1c15bcc9454,
   0x1da7bce4502d17fc,
   0x1da7b808436fbda8,
   0x1da7b32d35605774,
   0x1da7ae5325cac22c,
   0x1da7a97a147ae54c,
   0x1da7a4a2013cb2f4,
   0x1da79fcaebdc27f0,
   0x1da79af4d4256884,
   0x1da7961fb9e43048]

theorem record2684ChunkBits253Length2685 :
    (record2684ChunkBits2532685).length = 32 := by
  decide

theorem record2684ChunkSum2532685 :
    ((record2684ChunkBits2532685).map binary64Value2674).sum =
      (107552108964993837 : ℚ) / 4149515568880992958512407863691161151012446232242436899995657329690652811412908146399707048947103794288197886611300789182395151075411775307886874834113963687061181803401509523685376 := by
  norm_num [record2684ChunkBits2532685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 8128 through 8159,
decoded and summed as exact rationals. -/
def record2684ChunkBits2542685 : List Nat :=
  [0x1da7914b9ce4f274,
   0x1da78c787cf3b987,
   0x1da787a659dcb770,
   0x1da782d5336c28c0,
   0x1da77e05096e549e,
   0x1da77935dbaf8cc4,
   0x1da77467a9fc2d86,
   0x1da76f9a74209dc7,
   0x1da76ace39e96b92,
   0x1da76602fb22bd1f,
   0x1da76138b7996ecc,
   0x1da75c6f6f19f514,
   0x1da757a72170eb94,
   0x1da752dfce6af874,
   0x1da74e1975d4cc58,
   0x1da74954177b226c,
   0x1da7448fb32ac054,
   0x1da73fcc48b07637,
   0x1da73b09d7d93b0f,
   0x1da7364860719ed8,
   0x1da73187e246e642,
   0x1da72cc85d25eeeb,
   0x1da72809d0dbbd46,
   0x1da7234c3d35603a,
   0x1da71e8fa1fff114,
   0x1da719d3ff089396,
   0x1da71519541c75e3,
   0x1da7105fa108d088,
   0x1da70ba6e59b029f,
   0x1da706ef21a0050e,
   0x1da7023854e58400,
   0x1da6fd827f38c560]

theorem record2684ChunkBits254Length2685 :
    (record2684ChunkBits2542685).length = 32 := by
  decide

theorem record2684ChunkSum2542685 :
    ((record2684ChunkBits2542685).map binary64Value2674).sum =
      (26208429706991343 : ℚ) / 1037378892220248239628101965922790287753111558060609224998914332422663202853227036599926762236775948572049471652825197295598787768852943826971718708528490921765295450850377380921344 := by
  norm_num [record2684ChunkBits2542685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- Record 2684 cells 8160 through 8191,
decoded and summed as exact rationals. -/
def record2684ChunkBits2552685 : List Nat :=
  [0x1da6f8cda06735a4,
   0x1da6f419b83e4b9a,
   0x1da6ef66c68b8864,
   0x1da6eab4cb1c7782,
   0x1da6e603c5beaec2,
   0x1da6e153b63fce47,
   0x1da6dca49c6d9c6e,
   0x1da6d7f678157a34,
   0x1da6d34949057a6f,
   0x1da6ce9d0f0b4a83,
   0x1da6c9f1c9f4be10,
   0x1da6c547798fb2f8,
   0x1da6c09e1daa1160,
   0x1da6bbf5b611cbb3,
   0x1da6b74e4294de96,
   0x1da6b2a7c30150ec,
   0x1da6ae0237254f84,
   0x1da6a95d9ecea2a2,
   0x1da6a4b9f9cbc2ef,
   0x1da6a01747eac478,
   0x1da69b7588f9e133,
   0x1da696d4bcc75d47,
   0x1da69234e3218708,
   0x1da68d95fbd6b6f8,
   0x1da688f806b54fc3,
   0x1da6845b038bbe3b,
   0x1da67fbef22894d3,
   0x1da67b23d25a023b,
   0x1da67689a3eee426,
   0x1da671f066b5b477,
   0x1da66d581a7d12a8,
   0x1da668c0bf13a857]

theorem record2684ChunkBits255Length2685 :
    (record2684ChunkBits2552685).length = 32 := by
  decide

theorem record2684ChunkSum2552685 :
    ((record2684ChunkBits2552685).map binary64Value2674).sum =
      (204368072538277389 : ℚ) / 8299031137761985917024815727382322302024892464484873799991314659381305622825816292799414097894207588576395773222601578364790302150823550615773749668227927374122363606803019047370752 := by
  norm_num [record2684ChunkBits2552685, binary64Value2674, binary64ExponentBits2674, binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- The complete bit-pattern ledger, grouped into the 256 certified
chunks below so its exact sum can be checked incrementally. -/
def record2684CellTotalBits2685 : List Nat :=
  record2684ChunkBits0002685 ++
    record2684ChunkBits0012685 ++
    record2684ChunkBits0022685 ++
    record2684ChunkBits0032685 ++
    record2684ChunkBits0042685 ++
    record2684ChunkBits0052685 ++
    record2684ChunkBits0062685 ++
    record2684ChunkBits0072685 ++
    record2684ChunkBits0082685 ++
    record2684ChunkBits0092685 ++
    record2684ChunkBits0102685 ++
    record2684ChunkBits0112685 ++
    record2684ChunkBits0122685 ++
    record2684ChunkBits0132685 ++
    record2684ChunkBits0142685 ++
    record2684ChunkBits0152685 ++
    record2684ChunkBits0162685 ++
    record2684ChunkBits0172685 ++
    record2684ChunkBits0182685 ++
    record2684ChunkBits0192685 ++
    record2684ChunkBits0202685 ++
    record2684ChunkBits0212685 ++
    record2684ChunkBits0222685 ++
    record2684ChunkBits0232685 ++
    record2684ChunkBits0242685 ++
    record2684ChunkBits0252685 ++
    record2684ChunkBits0262685 ++
    record2684ChunkBits0272685 ++
    record2684ChunkBits0282685 ++
    record2684ChunkBits0292685 ++
    record2684ChunkBits0302685 ++
    record2684ChunkBits0312685 ++
    record2684ChunkBits0322685 ++
    record2684ChunkBits0332685 ++
    record2684ChunkBits0342685 ++
    record2684ChunkBits0352685 ++
    record2684ChunkBits0362685 ++
    record2684ChunkBits0372685 ++
    record2684ChunkBits0382685 ++
    record2684ChunkBits0392685 ++
    record2684ChunkBits0402685 ++
    record2684ChunkBits0412685 ++
    record2684ChunkBits0422685 ++
    record2684ChunkBits0432685 ++
    record2684ChunkBits0442685 ++
    record2684ChunkBits0452685 ++
    record2684ChunkBits0462685 ++
    record2684ChunkBits0472685 ++
    record2684ChunkBits0482685 ++
    record2684ChunkBits0492685 ++
    record2684ChunkBits0502685 ++
    record2684ChunkBits0512685 ++
    record2684ChunkBits0522685 ++
    record2684ChunkBits0532685 ++
    record2684ChunkBits0542685 ++
    record2684ChunkBits0552685 ++
    record2684ChunkBits0562685 ++
    record2684ChunkBits0572685 ++
    record2684ChunkBits0582685 ++
    record2684ChunkBits0592685 ++
    record2684ChunkBits0602685 ++
    record2684ChunkBits0612685 ++
    record2684ChunkBits0622685 ++
    record2684ChunkBits0632685 ++
    record2684ChunkBits0642685 ++
    record2684ChunkBits0652685 ++
    record2684ChunkBits0662685 ++
    record2684ChunkBits0672685 ++
    record2684ChunkBits0682685 ++
    record2684ChunkBits0692685 ++
    record2684ChunkBits0702685 ++
    record2684ChunkBits0712685 ++
    record2684ChunkBits0722685 ++
    record2684ChunkBits0732685 ++
    record2684ChunkBits0742685 ++
    record2684ChunkBits0752685 ++
    record2684ChunkBits0762685 ++
    record2684ChunkBits0772685 ++
    record2684ChunkBits0782685 ++
    record2684ChunkBits0792685 ++
    record2684ChunkBits0802685 ++
    record2684ChunkBits0812685 ++
    record2684ChunkBits0822685 ++
    record2684ChunkBits0832685 ++
    record2684ChunkBits0842685 ++
    record2684ChunkBits0852685 ++
    record2684ChunkBits0862685 ++
    record2684ChunkBits0872685 ++
    record2684ChunkBits0882685 ++
    record2684ChunkBits0892685 ++
    record2684ChunkBits0902685 ++
    record2684ChunkBits0912685 ++
    record2684ChunkBits0922685 ++
    record2684ChunkBits0932685 ++
    record2684ChunkBits0942685 ++
    record2684ChunkBits0952685 ++
    record2684ChunkBits0962685 ++
    record2684ChunkBits0972685 ++
    record2684ChunkBits0982685 ++
    record2684ChunkBits0992685 ++
    record2684ChunkBits1002685 ++
    record2684ChunkBits1012685 ++
    record2684ChunkBits1022685 ++
    record2684ChunkBits1032685 ++
    record2684ChunkBits1042685 ++
    record2684ChunkBits1052685 ++
    record2684ChunkBits1062685 ++
    record2684ChunkBits1072685 ++
    record2684ChunkBits1082685 ++
    record2684ChunkBits1092685 ++
    record2684ChunkBits1102685 ++
    record2684ChunkBits1112685 ++
    record2684ChunkBits1122685 ++
    record2684ChunkBits1132685 ++
    record2684ChunkBits1142685 ++
    record2684ChunkBits1152685 ++
    record2684ChunkBits1162685 ++
    record2684ChunkBits1172685 ++
    record2684ChunkBits1182685 ++
    record2684ChunkBits1192685 ++
    record2684ChunkBits1202685 ++
    record2684ChunkBits1212685 ++
    record2684ChunkBits1222685 ++
    record2684ChunkBits1232685 ++
    record2684ChunkBits1242685 ++
    record2684ChunkBits1252685 ++
    record2684ChunkBits1262685 ++
    record2684ChunkBits1272685 ++
    record2684ChunkBits1282685 ++
    record2684ChunkBits1292685 ++
    record2684ChunkBits1302685 ++
    record2684ChunkBits1312685 ++
    record2684ChunkBits1322685 ++
    record2684ChunkBits1332685 ++
    record2684ChunkBits1342685 ++
    record2684ChunkBits1352685 ++
    record2684ChunkBits1362685 ++
    record2684ChunkBits1372685 ++
    record2684ChunkBits1382685 ++
    record2684ChunkBits1392685 ++
    record2684ChunkBits1402685 ++
    record2684ChunkBits1412685 ++
    record2684ChunkBits1422685 ++
    record2684ChunkBits1432685 ++
    record2684ChunkBits1442685 ++
    record2684ChunkBits1452685 ++
    record2684ChunkBits1462685 ++
    record2684ChunkBits1472685 ++
    record2684ChunkBits1482685 ++
    record2684ChunkBits1492685 ++
    record2684ChunkBits1502685 ++
    record2684ChunkBits1512685 ++
    record2684ChunkBits1522685 ++
    record2684ChunkBits1532685 ++
    record2684ChunkBits1542685 ++
    record2684ChunkBits1552685 ++
    record2684ChunkBits1562685 ++
    record2684ChunkBits1572685 ++
    record2684ChunkBits1582685 ++
    record2684ChunkBits1592685 ++
    record2684ChunkBits1602685 ++
    record2684ChunkBits1612685 ++
    record2684ChunkBits1622685 ++
    record2684ChunkBits1632685 ++
    record2684ChunkBits1642685 ++
    record2684ChunkBits1652685 ++
    record2684ChunkBits1662685 ++
    record2684ChunkBits1672685 ++
    record2684ChunkBits1682685 ++
    record2684ChunkBits1692685 ++
    record2684ChunkBits1702685 ++
    record2684ChunkBits1712685 ++
    record2684ChunkBits1722685 ++
    record2684ChunkBits1732685 ++
    record2684ChunkBits1742685 ++
    record2684ChunkBits1752685 ++
    record2684ChunkBits1762685 ++
    record2684ChunkBits1772685 ++
    record2684ChunkBits1782685 ++
    record2684ChunkBits1792685 ++
    record2684ChunkBits1802685 ++
    record2684ChunkBits1812685 ++
    record2684ChunkBits1822685 ++
    record2684ChunkBits1832685 ++
    record2684ChunkBits1842685 ++
    record2684ChunkBits1852685 ++
    record2684ChunkBits1862685 ++
    record2684ChunkBits1872685 ++
    record2684ChunkBits1882685 ++
    record2684ChunkBits1892685 ++
    record2684ChunkBits1902685 ++
    record2684ChunkBits1912685 ++
    record2684ChunkBits1922685 ++
    record2684ChunkBits1932685 ++
    record2684ChunkBits1942685 ++
    record2684ChunkBits1952685 ++
    record2684ChunkBits1962685 ++
    record2684ChunkBits1972685 ++
    record2684ChunkBits1982685 ++
    record2684ChunkBits1992685 ++
    record2684ChunkBits2002685 ++
    record2684ChunkBits2012685 ++
    record2684ChunkBits2022685 ++
    record2684ChunkBits2032685 ++
    record2684ChunkBits2042685 ++
    record2684ChunkBits2052685 ++
    record2684ChunkBits2062685 ++
    record2684ChunkBits2072685 ++
    record2684ChunkBits2082685 ++
    record2684ChunkBits2092685 ++
    record2684ChunkBits2102685 ++
    record2684ChunkBits2112685 ++
    record2684ChunkBits2122685 ++
    record2684ChunkBits2132685 ++
    record2684ChunkBits2142685 ++
    record2684ChunkBits2152685 ++
    record2684ChunkBits2162685 ++
    record2684ChunkBits2172685 ++
    record2684ChunkBits2182685 ++
    record2684ChunkBits2192685 ++
    record2684ChunkBits2202685 ++
    record2684ChunkBits2212685 ++
    record2684ChunkBits2222685 ++
    record2684ChunkBits2232685 ++
    record2684ChunkBits2242685 ++
    record2684ChunkBits2252685 ++
    record2684ChunkBits2262685 ++
    record2684ChunkBits2272685 ++
    record2684ChunkBits2282685 ++
    record2684ChunkBits2292685 ++
    record2684ChunkBits2302685 ++
    record2684ChunkBits2312685 ++
    record2684ChunkBits2322685 ++
    record2684ChunkBits2332685 ++
    record2684ChunkBits2342685 ++
    record2684ChunkBits2352685 ++
    record2684ChunkBits2362685 ++
    record2684ChunkBits2372685 ++
    record2684ChunkBits2382685 ++
    record2684ChunkBits2392685 ++
    record2684ChunkBits2402685 ++
    record2684ChunkBits2412685 ++
    record2684ChunkBits2422685 ++
    record2684ChunkBits2432685 ++
    record2684ChunkBits2442685 ++
    record2684ChunkBits2452685 ++
    record2684ChunkBits2462685 ++
    record2684ChunkBits2472685 ++
    record2684ChunkBits2482685 ++
    record2684ChunkBits2492685 ++
    record2684ChunkBits2502685 ++
    record2684ChunkBits2512685 ++
    record2684ChunkBits2522685 ++
    record2684ChunkBits2532685 ++
    record2684ChunkBits2542685 ++
    record2684ChunkBits2552685

/-- The imported ledger contains exactly the 8192 partition cells. -/
theorem record2684GridCellCount2685 :
    record2684CellTotalBits2685.length = 8192 := by
  simp only [record2684CellTotalBits2685, List.length_append, record2684ChunkBits000Length2685, record2684ChunkBits001Length2685, record2684ChunkBits002Length2685, record2684ChunkBits003Length2685, record2684ChunkBits004Length2685, record2684ChunkBits005Length2685, record2684ChunkBits006Length2685, record2684ChunkBits007Length2685, record2684ChunkBits008Length2685, record2684ChunkBits009Length2685, record2684ChunkBits010Length2685, record2684ChunkBits011Length2685, record2684ChunkBits012Length2685, record2684ChunkBits013Length2685, record2684ChunkBits014Length2685, record2684ChunkBits015Length2685, record2684ChunkBits016Length2685, record2684ChunkBits017Length2685, record2684ChunkBits018Length2685, record2684ChunkBits019Length2685, record2684ChunkBits020Length2685, record2684ChunkBits021Length2685, record2684ChunkBits022Length2685, record2684ChunkBits023Length2685, record2684ChunkBits024Length2685, record2684ChunkBits025Length2685, record2684ChunkBits026Length2685, record2684ChunkBits027Length2685, record2684ChunkBits028Length2685, record2684ChunkBits029Length2685, record2684ChunkBits030Length2685, record2684ChunkBits031Length2685, record2684ChunkBits032Length2685, record2684ChunkBits033Length2685, record2684ChunkBits034Length2685, record2684ChunkBits035Length2685, record2684ChunkBits036Length2685, record2684ChunkBits037Length2685, record2684ChunkBits038Length2685, record2684ChunkBits039Length2685, record2684ChunkBits040Length2685, record2684ChunkBits041Length2685, record2684ChunkBits042Length2685, record2684ChunkBits043Length2685, record2684ChunkBits044Length2685, record2684ChunkBits045Length2685, record2684ChunkBits046Length2685, record2684ChunkBits047Length2685, record2684ChunkBits048Length2685, record2684ChunkBits049Length2685, record2684ChunkBits050Length2685, record2684ChunkBits051Length2685, record2684ChunkBits052Length2685, record2684ChunkBits053Length2685, record2684ChunkBits054Length2685, record2684ChunkBits055Length2685, record2684ChunkBits056Length2685, record2684ChunkBits057Length2685, record2684ChunkBits058Length2685, record2684ChunkBits059Length2685, record2684ChunkBits060Length2685, record2684ChunkBits061Length2685, record2684ChunkBits062Length2685, record2684ChunkBits063Length2685, record2684ChunkBits064Length2685, record2684ChunkBits065Length2685, record2684ChunkBits066Length2685, record2684ChunkBits067Length2685, record2684ChunkBits068Length2685, record2684ChunkBits069Length2685, record2684ChunkBits070Length2685, record2684ChunkBits071Length2685, record2684ChunkBits072Length2685, record2684ChunkBits073Length2685, record2684ChunkBits074Length2685, record2684ChunkBits075Length2685, record2684ChunkBits076Length2685, record2684ChunkBits077Length2685, record2684ChunkBits078Length2685, record2684ChunkBits079Length2685, record2684ChunkBits080Length2685, record2684ChunkBits081Length2685, record2684ChunkBits082Length2685, record2684ChunkBits083Length2685, record2684ChunkBits084Length2685, record2684ChunkBits085Length2685, record2684ChunkBits086Length2685, record2684ChunkBits087Length2685, record2684ChunkBits088Length2685, record2684ChunkBits089Length2685, record2684ChunkBits090Length2685, record2684ChunkBits091Length2685, record2684ChunkBits092Length2685, record2684ChunkBits093Length2685, record2684ChunkBits094Length2685, record2684ChunkBits095Length2685, record2684ChunkBits096Length2685, record2684ChunkBits097Length2685, record2684ChunkBits098Length2685, record2684ChunkBits099Length2685, record2684ChunkBits100Length2685, record2684ChunkBits101Length2685, record2684ChunkBits102Length2685, record2684ChunkBits103Length2685, record2684ChunkBits104Length2685, record2684ChunkBits105Length2685, record2684ChunkBits106Length2685, record2684ChunkBits107Length2685, record2684ChunkBits108Length2685, record2684ChunkBits109Length2685, record2684ChunkBits110Length2685, record2684ChunkBits111Length2685, record2684ChunkBits112Length2685, record2684ChunkBits113Length2685, record2684ChunkBits114Length2685, record2684ChunkBits115Length2685, record2684ChunkBits116Length2685, record2684ChunkBits117Length2685, record2684ChunkBits118Length2685, record2684ChunkBits119Length2685, record2684ChunkBits120Length2685, record2684ChunkBits121Length2685, record2684ChunkBits122Length2685, record2684ChunkBits123Length2685, record2684ChunkBits124Length2685, record2684ChunkBits125Length2685, record2684ChunkBits126Length2685, record2684ChunkBits127Length2685, record2684ChunkBits128Length2685, record2684ChunkBits129Length2685, record2684ChunkBits130Length2685, record2684ChunkBits131Length2685, record2684ChunkBits132Length2685, record2684ChunkBits133Length2685, record2684ChunkBits134Length2685, record2684ChunkBits135Length2685, record2684ChunkBits136Length2685, record2684ChunkBits137Length2685, record2684ChunkBits138Length2685, record2684ChunkBits139Length2685, record2684ChunkBits140Length2685, record2684ChunkBits141Length2685, record2684ChunkBits142Length2685, record2684ChunkBits143Length2685, record2684ChunkBits144Length2685, record2684ChunkBits145Length2685, record2684ChunkBits146Length2685, record2684ChunkBits147Length2685, record2684ChunkBits148Length2685, record2684ChunkBits149Length2685, record2684ChunkBits150Length2685, record2684ChunkBits151Length2685, record2684ChunkBits152Length2685, record2684ChunkBits153Length2685, record2684ChunkBits154Length2685, record2684ChunkBits155Length2685, record2684ChunkBits156Length2685, record2684ChunkBits157Length2685, record2684ChunkBits158Length2685, record2684ChunkBits159Length2685, record2684ChunkBits160Length2685, record2684ChunkBits161Length2685, record2684ChunkBits162Length2685, record2684ChunkBits163Length2685, record2684ChunkBits164Length2685, record2684ChunkBits165Length2685, record2684ChunkBits166Length2685, record2684ChunkBits167Length2685, record2684ChunkBits168Length2685, record2684ChunkBits169Length2685, record2684ChunkBits170Length2685, record2684ChunkBits171Length2685, record2684ChunkBits172Length2685, record2684ChunkBits173Length2685, record2684ChunkBits174Length2685, record2684ChunkBits175Length2685, record2684ChunkBits176Length2685, record2684ChunkBits177Length2685, record2684ChunkBits178Length2685, record2684ChunkBits179Length2685, record2684ChunkBits180Length2685, record2684ChunkBits181Length2685, record2684ChunkBits182Length2685, record2684ChunkBits183Length2685, record2684ChunkBits184Length2685, record2684ChunkBits185Length2685, record2684ChunkBits186Length2685, record2684ChunkBits187Length2685, record2684ChunkBits188Length2685, record2684ChunkBits189Length2685, record2684ChunkBits190Length2685, record2684ChunkBits191Length2685, record2684ChunkBits192Length2685, record2684ChunkBits193Length2685, record2684ChunkBits194Length2685, record2684ChunkBits195Length2685, record2684ChunkBits196Length2685, record2684ChunkBits197Length2685, record2684ChunkBits198Length2685, record2684ChunkBits199Length2685, record2684ChunkBits200Length2685, record2684ChunkBits201Length2685, record2684ChunkBits202Length2685, record2684ChunkBits203Length2685, record2684ChunkBits204Length2685, record2684ChunkBits205Length2685, record2684ChunkBits206Length2685, record2684ChunkBits207Length2685, record2684ChunkBits208Length2685, record2684ChunkBits209Length2685, record2684ChunkBits210Length2685, record2684ChunkBits211Length2685, record2684ChunkBits212Length2685, record2684ChunkBits213Length2685, record2684ChunkBits214Length2685, record2684ChunkBits215Length2685, record2684ChunkBits216Length2685, record2684ChunkBits217Length2685, record2684ChunkBits218Length2685, record2684ChunkBits219Length2685, record2684ChunkBits220Length2685, record2684ChunkBits221Length2685, record2684ChunkBits222Length2685, record2684ChunkBits223Length2685, record2684ChunkBits224Length2685, record2684ChunkBits225Length2685, record2684ChunkBits226Length2685, record2684ChunkBits227Length2685, record2684ChunkBits228Length2685, record2684ChunkBits229Length2685, record2684ChunkBits230Length2685, record2684ChunkBits231Length2685, record2684ChunkBits232Length2685, record2684ChunkBits233Length2685, record2684ChunkBits234Length2685, record2684ChunkBits235Length2685, record2684ChunkBits236Length2685, record2684ChunkBits237Length2685, record2684ChunkBits238Length2685, record2684ChunkBits239Length2685, record2684ChunkBits240Length2685, record2684ChunkBits241Length2685, record2684ChunkBits242Length2685, record2684ChunkBits243Length2685, record2684ChunkBits244Length2685, record2684ChunkBits245Length2685, record2684ChunkBits246Length2685, record2684ChunkBits247Length2685, record2684ChunkBits248Length2685, record2684ChunkBits249Length2685, record2684ChunkBits250Length2685, record2684ChunkBits251Length2685, record2684ChunkBits252Length2685, record2684ChunkBits253Length2685, record2684ChunkBits254Length2685, record2684ChunkBits255Length2685]

/-- The full finite-grid charge, reconstructed solely from the cell
bit patterns. -/
theorem record2684GridChargeExact2685 :
    (record2684CellTotalBits2685.map binary64Value2674).sum =
      (27826487222051325198041966163480097965157650346221323904080535990128504748326629176194241607668881109848544731421469099613184421559488956705303625787269582323428822387794031520193315377743 : ℚ) / 4149515568880992958512407863691161151012446232242436899995657329690652811412908146399707048947103794288197886611300789182395151075411775307886874834113963687061181803401509523685376 := by
  simp only [record2684CellTotalBits2685, List.map_append,
    List.sum_append, record2684ChunkSum0002685, record2684ChunkSum0012685, record2684ChunkSum0022685, record2684ChunkSum0032685, record2684ChunkSum0042685, record2684ChunkSum0052685, record2684ChunkSum0062685, record2684ChunkSum0072685, record2684ChunkSum0082685, record2684ChunkSum0092685, record2684ChunkSum0102685, record2684ChunkSum0112685, record2684ChunkSum0122685, record2684ChunkSum0132685, record2684ChunkSum0142685, record2684ChunkSum0152685, record2684ChunkSum0162685, record2684ChunkSum0172685, record2684ChunkSum0182685, record2684ChunkSum0192685, record2684ChunkSum0202685, record2684ChunkSum0212685, record2684ChunkSum0222685, record2684ChunkSum0232685, record2684ChunkSum0242685, record2684ChunkSum0252685, record2684ChunkSum0262685, record2684ChunkSum0272685, record2684ChunkSum0282685, record2684ChunkSum0292685, record2684ChunkSum0302685, record2684ChunkSum0312685, record2684ChunkSum0322685, record2684ChunkSum0332685, record2684ChunkSum0342685, record2684ChunkSum0352685, record2684ChunkSum0362685, record2684ChunkSum0372685, record2684ChunkSum0382685, record2684ChunkSum0392685, record2684ChunkSum0402685, record2684ChunkSum0412685, record2684ChunkSum0422685, record2684ChunkSum0432685, record2684ChunkSum0442685, record2684ChunkSum0452685, record2684ChunkSum0462685, record2684ChunkSum0472685, record2684ChunkSum0482685, record2684ChunkSum0492685, record2684ChunkSum0502685, record2684ChunkSum0512685, record2684ChunkSum0522685, record2684ChunkSum0532685, record2684ChunkSum0542685, record2684ChunkSum0552685, record2684ChunkSum0562685, record2684ChunkSum0572685, record2684ChunkSum0582685, record2684ChunkSum0592685, record2684ChunkSum0602685, record2684ChunkSum0612685, record2684ChunkSum0622685, record2684ChunkSum0632685, record2684ChunkSum0642685, record2684ChunkSum0652685, record2684ChunkSum0662685, record2684ChunkSum0672685, record2684ChunkSum0682685, record2684ChunkSum0692685, record2684ChunkSum0702685, record2684ChunkSum0712685, record2684ChunkSum0722685, record2684ChunkSum0732685, record2684ChunkSum0742685, record2684ChunkSum0752685, record2684ChunkSum0762685, record2684ChunkSum0772685, record2684ChunkSum0782685, record2684ChunkSum0792685, record2684ChunkSum0802685, record2684ChunkSum0812685, record2684ChunkSum0822685, record2684ChunkSum0832685, record2684ChunkSum0842685, record2684ChunkSum0852685, record2684ChunkSum0862685, record2684ChunkSum0872685, record2684ChunkSum0882685, record2684ChunkSum0892685, record2684ChunkSum0902685, record2684ChunkSum0912685, record2684ChunkSum0922685, record2684ChunkSum0932685, record2684ChunkSum0942685, record2684ChunkSum0952685, record2684ChunkSum0962685, record2684ChunkSum0972685, record2684ChunkSum0982685, record2684ChunkSum0992685, record2684ChunkSum1002685, record2684ChunkSum1012685, record2684ChunkSum1022685, record2684ChunkSum1032685, record2684ChunkSum1042685, record2684ChunkSum1052685, record2684ChunkSum1062685, record2684ChunkSum1072685, record2684ChunkSum1082685, record2684ChunkSum1092685, record2684ChunkSum1102685, record2684ChunkSum1112685, record2684ChunkSum1122685, record2684ChunkSum1132685, record2684ChunkSum1142685, record2684ChunkSum1152685, record2684ChunkSum1162685, record2684ChunkSum1172685, record2684ChunkSum1182685, record2684ChunkSum1192685, record2684ChunkSum1202685, record2684ChunkSum1212685, record2684ChunkSum1222685, record2684ChunkSum1232685, record2684ChunkSum1242685, record2684ChunkSum1252685, record2684ChunkSum1262685, record2684ChunkSum1272685, record2684ChunkSum1282685, record2684ChunkSum1292685, record2684ChunkSum1302685, record2684ChunkSum1312685, record2684ChunkSum1322685, record2684ChunkSum1332685, record2684ChunkSum1342685, record2684ChunkSum1352685, record2684ChunkSum1362685, record2684ChunkSum1372685, record2684ChunkSum1382685, record2684ChunkSum1392685, record2684ChunkSum1402685, record2684ChunkSum1412685, record2684ChunkSum1422685, record2684ChunkSum1432685, record2684ChunkSum1442685, record2684ChunkSum1452685, record2684ChunkSum1462685, record2684ChunkSum1472685, record2684ChunkSum1482685, record2684ChunkSum1492685, record2684ChunkSum1502685, record2684ChunkSum1512685, record2684ChunkSum1522685, record2684ChunkSum1532685, record2684ChunkSum1542685, record2684ChunkSum1552685, record2684ChunkSum1562685, record2684ChunkSum1572685, record2684ChunkSum1582685, record2684ChunkSum1592685, record2684ChunkSum1602685, record2684ChunkSum1612685, record2684ChunkSum1622685, record2684ChunkSum1632685, record2684ChunkSum1642685, record2684ChunkSum1652685, record2684ChunkSum1662685, record2684ChunkSum1672685, record2684ChunkSum1682685, record2684ChunkSum1692685, record2684ChunkSum1702685, record2684ChunkSum1712685, record2684ChunkSum1722685, record2684ChunkSum1732685, record2684ChunkSum1742685, record2684ChunkSum1752685, record2684ChunkSum1762685, record2684ChunkSum1772685, record2684ChunkSum1782685, record2684ChunkSum1792685, record2684ChunkSum1802685, record2684ChunkSum1812685, record2684ChunkSum1822685, record2684ChunkSum1832685, record2684ChunkSum1842685, record2684ChunkSum1852685, record2684ChunkSum1862685, record2684ChunkSum1872685, record2684ChunkSum1882685, record2684ChunkSum1892685, record2684ChunkSum1902685, record2684ChunkSum1912685, record2684ChunkSum1922685, record2684ChunkSum1932685, record2684ChunkSum1942685, record2684ChunkSum1952685, record2684ChunkSum1962685, record2684ChunkSum1972685, record2684ChunkSum1982685, record2684ChunkSum1992685, record2684ChunkSum2002685, record2684ChunkSum2012685, record2684ChunkSum2022685, record2684ChunkSum2032685, record2684ChunkSum2042685, record2684ChunkSum2052685, record2684ChunkSum2062685, record2684ChunkSum2072685, record2684ChunkSum2082685, record2684ChunkSum2092685, record2684ChunkSum2102685, record2684ChunkSum2112685, record2684ChunkSum2122685, record2684ChunkSum2132685, record2684ChunkSum2142685, record2684ChunkSum2152685, record2684ChunkSum2162685, record2684ChunkSum2172685, record2684ChunkSum2182685, record2684ChunkSum2192685, record2684ChunkSum2202685, record2684ChunkSum2212685, record2684ChunkSum2222685, record2684ChunkSum2232685, record2684ChunkSum2242685, record2684ChunkSum2252685, record2684ChunkSum2262685, record2684ChunkSum2272685, record2684ChunkSum2282685, record2684ChunkSum2292685, record2684ChunkSum2302685, record2684ChunkSum2312685, record2684ChunkSum2322685, record2684ChunkSum2332685, record2684ChunkSum2342685, record2684ChunkSum2352685, record2684ChunkSum2362685, record2684ChunkSum2372685, record2684ChunkSum2382685, record2684ChunkSum2392685, record2684ChunkSum2402685, record2684ChunkSum2412685, record2684ChunkSum2422685, record2684ChunkSum2432685, record2684ChunkSum2442685, record2684ChunkSum2452685, record2684ChunkSum2462685, record2684ChunkSum2472685, record2684ChunkSum2482685, record2684ChunkSum2492685, record2684ChunkSum2502685, record2684ChunkSum2512685, record2684ChunkSum2522685, record2684ChunkSum2532685, record2684ChunkSum2542685, record2684ChunkSum2552685]
  norm_num

/-- The displayed binary64 total in record 2684 rounds upward for this
input, so it is a valid readable upper bound on the exact rational sum. -/
theorem record2684RoundedTotalUpper2685 :
    (record2684CellTotalBits2685.map binary64Value2674).sum ≤
      binary64Value2674 0x415994ca1bba4a85 := by
  rw [record2684GridChargeExact2685]
  norm_num [binary64Value2674, binary64ExponentBits2674,
    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]

/-- The exact grid charge is below record 2109's known-error budget.
This certifies the finite rational ledger only; cell containment and
the live-owner identity remain explicit premises of the integral route. -/
theorem record2684GridChargeBelowKnownError2685 :
    (((record2684CellTotalBits2685.map binary64Value2674).sum : ℚ) : ℝ) <
      ConnesWeilRH.Source.C1RouteAItem5Arithmetic.knownError2109 := by
  rw [record2684GridChargeExact2685]
  norm_num [ConnesWeilRH.Source.C1RouteAItem5Arithmetic.knownError2109]

end ConnesWeilRH.Dev
