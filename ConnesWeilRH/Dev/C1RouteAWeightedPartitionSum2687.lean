import ConnesWeilRH.Dev.C1RouteAWeightedCellPartition2684
import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic

set_option maxRecDepth 4096
set_option exponentiation.threshold 1200

namespace ConnesWeilRH.Dev

/-- Record 2687 cells 0 through 31,
decoded and summed as exact rationals. -/
def record2687ChunkBits000 : List Nat :=
  [0x1e5eb0b757f44d24,
   0x1e5e979d689d60cb,
   0x1e5e7e9800fcc69a,
   0x1e5e65a71047f36e,
   0x1e5e4cca85c1fbf8,
   0x1e5e340250bbb820,
   0x1e5e1b4e6093a07a,
   0x1e5e02aea4b5c33b,
   0x1e5dea230c9bcff8,
   0x1e5dd1ab87ccdec4,
   0x1e5db94805dd92f4,
   0x1e5da0f8766ff932,
   0x1e5d88bcc9337c8c,
   0x1e5d7094ede4f21b,
   0x1e5d5880d44e60eb,
   0x1e5d40806c47244c,
   0x1e5d2893a5b3ca5f,
   0x1e5d10ba7086095a,
   0x1e5cf8f4bcbccaf7,
   0x1e5ce1427a63f54a,
   0x1e5cc9a399948c7f,
   0x1e5cb2180a7491f2,
   0x1e5c9a9fbd36f99e,
   0x1e5c833aa21bb55c,
   0x1e5c6be8a96f7ea2,
   0x1e5c54a9c38bf7a7,
   0x1e5c3d7de0d78b0e,
   0x1e5c2664f1c56180,
   0x1e5c0f5ee6d56cb7,
   0x1e5bf86bb0943218,
   0x1e5be18b3f9aeb5c,
   0x1e5bcabd848f66b2]

theorem record2687ChunkBits000Length :
    (record2687ChunkBits000).length = 32 := by
  decide

theorem record2687ChunkSum000 :
    ((record2687ChunkBits000).map binary64Value2674).sum =
      (263171834560930717 : ℚ) / 4052261297735344686047273304385899561535592023674254785152009111026028136145418111718463914987406049109568248643848426935932764722081811824108276205189417663145685354884286644224 := by
  norm_num [record2687ChunkBits000, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 32 through 63,
decoded and summed as exact rationals. -/
def record2687ChunkBits001 : List Nat :=
  [0x1e5bb4027023fc87,
   0x1e5b9d59f3179a6b,
   0x1e5b86c3fe358e78,
   0x1e5b70408255a780,
   0x1e5b59cf705c15ac,
   0x1ef2924262012a64,
   0x1fe105e4403b3aa9,
   0x20c1de5a1a3d0110,
   0x219646da5e628f5e,
   0x22610f5db19e2b51,
   0x23217dfc6c5978bd,
   0x23dc04e6830b9b6d,
   0x248f232a97fde9e2,
   0x2537afe06db7c216,
   0x25d9330dcbc67fa2,
   0x26731ba9cd75f907,
   0x270598fdabc6c5dc,
   0x27957362dab3b63c,
   0x2821395058a79034,
   0x28a504d0a6d85e9d,
   0x2923bec7980dfc3b,
   0x299ce4523cf5425f,
   0x2a10d499dd1b338f,
   0x2a81f576799e4a76,
   0x2af1890e166427d0,
   0x2b5bc26250b85ccc,
   0x2bc1f629e1453614,
   0x2c23252803cfe4ce,
   0x2c80eafa12118a02,
   0x2cdb93bb0527d63c,
   0x2d36b957b99a490e,
   0x2d8fbe7dfe24bd1d]

theorem record2687ChunkBits001Length :
    (record2687ChunkBits001).length = 32 := by
  decide

theorem record2687ChunkSum001 :
    ((record2687ChunkBits001).map binary64Value2674).sum =
      (64588289717680279920293332039801597694208378383592792820635733268775521770391189974301003 : ℚ) / 2026130648867672343023636652192949780767796011837127392576004555513014068072709055859231957493703024554784124321924213467966382361040905912054138102594708831572842677442143322112 := by
  norm_num [record2687ChunkBits001, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 64 through 95,
decoded and summed as exact rationals. -/
def record2687ChunkBits002 : List Nat :=
  [0x2de2da3dd381bebc,
   0x2e3323e7cb28be5b,
   0x2e80adbef05c1e1c,
   0x2eca5883827e465e,
   0x2f16739b63631882,
   0x2f6101b70785b196,
   0x2fa6801950ca0ebc,
   0x2fea19cc04c237a4,
   0x302a9ef32e0348f2,
   0x30688125699172a8,
   0x30a8882211f7e301,
   0x30e74138b7c02a43,
   0x31239d88cb1c73b2,
   0x315d8a663620d06d,
   0x3193e6112842565d,
   0x31c83e93886917c5,
   0x31ff5b1c34aa9052,
   0x32349afccf996fc6,
   0x32686cbc9b543ccf,
   0x329a2f50f9284223,
   0x32c96ed74de9e77d,
   0x32f66529cd2df023,
   0x33244264632e1e00,
   0x3353ce3a1534e866,
   0x3381b88f466b6735,
   0x33acf55254461b21,
   0x33d5a44b75f33a68,
   0x33fd991547623fbf,
   0x3423d9135e282458,
   0x344e4e7e3a58ca99,
   0x34759a3a4c65c419,
   0x349c53d54344df2f]

theorem record2687ChunkBits002Length :
    (record2687ChunkBits002).length = 32 := by
  decide

theorem record2687ChunkSum002 :
    ((record2687ChunkBits002).map binary64Value2674).sum =
      (398093158606332345205629732379566884111615155847 : ℚ) / 1119872371088902105278721140284222139060822748617324767449994550481895935590080472690438746635803557888 := by
  norm_num [record2687ChunkBits002, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 96 through 127,
decoded and summed as exact rationals. -/
def record2687ChunkBits003 : List Nat :=
  [0x34c11ca962d24f40,
   0x34e30d9180926b24,
   0x350400523f81a1ac,
   0x3528b478b64b35c8,
   0x354d3d8ba6466f61,
   0x35700182d525a109,
   0x35903c42ef9a888c,
   0x35ae86eb09d4ab9e,
   0x35cac9a13c5d8669,
   0x35eae273be320787,
   0x360b47dc586e1366,
   0x3629b7bad50f1dbf,
   0x36468fdba8ca4ff7,
   0x36626dd6e155968a,
   0x367c04b7033ecdec,
   0x36977685a0eb3adf,
   0x36b4cd7d67bed98d,
   0x36d14e09a2a17f20,
   0x36eae2f085dcfe78,
   0x370384c36147e5ab,
   0x371a78bdc3cd383f,
   0x3732f08ce7ce7729,
   0x374db56abbefa5e1,
   0x37663d00392116e3,
   0x377f2df14fd37eae,
   0x37947cd01fa4f361,
   0x37a93a5c46b06b1f,
   0x37bfb024311cea05,
   0x37d62c4e73a90f18,
   0x37ee58c0beaaa0d8,
   0x38037e81be926461,
   0x381788adb91ef564]

theorem record2687ChunkBits003Length :
    (record2687ChunkBits003).length = 32 := by
  decide

theorem record2687ChunkSum003 :
    ((record2687ChunkBits003).map binary64Value2674).sum =
      (6224022470605240537914847367961 : ℚ) / 215679573337205118357336120696157045389097155380324579848828881993728 := by
  norm_num [record2687ChunkBits003, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 128 through 159,
decoded and summed as exact rationals. -/
def record2687ChunkBits004 : List Nat :=
  [0x382ab1145d8c555d,
   0x383e3de73868e0cb,
   0x3852ec2e2b05684c,
   0x3867fb88a35b4448,
   0x387c971e8efa4a34,
   0x38900bfb296bc513,
   0x38a0f63929745001,
   0x38b1b06d3154ca65,
   0x38c407095bdccdb8,
   0x38d796066f65daf5,
   0x38ea5c7a6191a585,
   0x38fbcafd10faff52,
   0x390ba5a20a9ab55a,
   0x391b24fbec1695ae,
   0x392bf457378d1777,
   0x393ea55bc9cb67a1,
   0x395031bfe96f696e,
   0x39602bb31b4885c0,
   0x396e85eccead3e74,
   0x397c70eff63b61a9,
   0x398b1dedb625d85f,
   0x399ba8fa1536bf19,
   0x39abd74a0d70f850,
   0x39ba83c4b8bf56ce,
   0x39c7e77be6564382,
   0x39d5482dfb1030dd,
   0x39e321ba0ad62914,
   0x39f218904d5279ba,
   0x3a017369afb804c1,
   0x3a0fe3a5c3dd1551,
   0x3a1b9f268f2ff227,
   0x3a27a1824e46527f]

theorem record2687ChunkBits004Length :
    (record2687ChunkBits004).length = 32 := by
  decide

theorem record2687ChunkSum004 :
    ((record2687ChunkBits004).map binary64Value2674).sum =
      (66126416435377358947864787 : ℚ) / 191561942608236107294793378393788647952342390272950272 := by
  norm_num [record2687ChunkBits004, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 160 through 191,
decoded and summed as exact rationals. -/
def record2687ChunkBits005 : List Nat :=
  [0x3a3449b4225a12c6,
   0x3a41ec50a0382602,
   0x3a5086850922558a,
   0x3a5d1dd422245a6f,
   0x3a68596a6a7e4b5f,
   0x3a741d3305ccc373,
   0x3a80b9989b528088,
   0x3a8badb68ba9d6d6,
   0x3a985ecf42c09099,
   0x3aa4c9a620fc9374,
   0x3ab0daa035ec0dfb,
   0x3abafee965f19699,
   0x3ac5d1c590cbe88e,
   0x3ad127f214783bc0,
   0x3adcb9e283f5a7e5,
   0x3ae7cf66af0f1b07,
   0x3af2c85a968f9331,
   0x3afd447bf8917c2e,
   0x3b0710ca817dc63c,
   0x3b117a944a966368,
   0x3b1bafb727686b25,
   0x3b265df18cceded7,
   0x3b313838f5783cf4,
   0x3b3a2daadac1c194,
   0x3b442b97dd7f7cd1,
   0x3b4dbb6c4cbe8eae,
   0x3b56651831f81a93,
   0x3b6191a3a47faae1,
   0x3b6a783e10d68281,
   0x3b73ad8cf3053af7,
   0x3b7db6e3200070c9,
   0x3b857eb6cde58bc6]

theorem record2687ChunkBits005Length :
    (record2687ChunkBits005).length = 32 := by
  decide

theorem record2687ChunkSum005 :
    ((record2687ChunkBits005).map binary64Value2674).sum =
      (19308846230497175770219 : ℚ) / 11150372599265311570767859136324180752990208 := by
  norm_num [record2687ChunkBits005, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 192 through 223,
decoded and summed as exact rationals. -/
def record2687ChunkBits006 : List Nat :=
  [0x3b8edca74e5e94d1,
   0x3b977926dc132e57,
   0x3ba15754423b2597,
   0x3ba9446af95c3b8a,
   0x3bb2bb282c6f79c4,
   0x3bbaa619372f8f31,
   0x3bc279324bbceb03,
   0x3bcb12ecc5b3e365,
   0x3bd3a6fe372229c7,
   0x3bdc1bf07fc81610,
   0x3be47e97eb723dd2,
   0x3becb86c7029b371,
   0x3bf3731a5f1df13f,
   0x3bfb50d945bf844f,
   0x3c03837bdf178cb1,
   0x3c0b6fd2b4bf3761,
   0x3c13b411109329d1,
   0x3c1b3cb59707bf98,
   0x3c22230f23cb97c5,
   0x3c2882bac8006b4b,
   0x3c312c15e4142a4a,
   0x3c37c32b2d4cbcd3,
   0x3c40d42ccccdbe60,
   0x3c46fa0ee4288cc5,
   0x3c4e420ff4d7d9de,
   0x3c53b70651e93e5f,
   0x3c5b0f9138b50a71,
   0x3c6271bc7c59cfdd,
   0x3c69ca7c2fb16e59,
   0x3c7168989cd21e77,
   0x3c76b1916dea6a8f,
   0x3c7cdf7a47d9f309]

theorem record2687ChunkBits006Length :
    (record2687ChunkBits006).length = 32 := by
  decide

theorem record2687ChunkSum006 :
    ((record2687ChunkBits006).map binary64Value2674).sum =
      (1078234422783095468747 : ℚ) / 10633823966279326983230456482242756608 := by
  norm_num [record2687ChunkBits006, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 224 through 255,
decoded and summed as exact rationals. -/
def record2687ChunkBits007 : List Nat :=
  [0x3c8343f921a40a07,
   0x3c89e45e7fb04859,
   0x3c91e31017b63005,
   0x3c97e5e3a9f51266,
   0x3c9ede1f8bd529e6,
   0x3ca35b91d61a590a,
   0x3ca8fd3a71eccb25,
   0x3cb0910db8668969,
   0x3cb6a2111f943f51,
   0x3cbdf3935ace8aa5,
   0x3cc32e952cfdc921,
   0x3cc7d2147905e562,
   0x3ccdd65c109019b6,
   0x3cd3772543c42a1d,
   0x3cda4fa51e8ee199,
   0x3ce1416f9af632a1,
   0x3ce5f0cd98ed19b3,
   0x3ceb1874fd876464,
   0x3cf0855a9656f8c8,
   0x3cf53da486a6ef97,
   0x3cfc918210ae2301,
   0x3d02abd2dd4d43ef,
   0x3d07a766905a6952,
   0x3d0d0af99c7fe84d,
   0x3d1168967b8fab40,
   0x3d15d1b6c16b785a,
   0x3d1d2734e9d75925,
   0x3d22ef61b73a9685,
   0x3d27d62764dc7eff,
   0x3d2d1154047c6da1,
   0x3d313b2a071a7b21,
   0x3d34f351712ea164]

theorem record2687ChunkBits007Length :
    (record2687ChunkBits007).length = 32 := by
  decide

theorem record2687ChunkSum007 :
    ((record2687ChunkBits007).map binary64Value2674).sum =
      (31148696933964839811 : ℚ) / 81129638414606681695789005144064 := by
  norm_num [record2687ChunkBits007, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 256 through 287,
decoded and summed as exact rationals. -/
def record2687ChunkBits008 : List Nat :=
  [0x3d3bc2081bbea220,
   0x3d41ee5fce79509e,
   0x3d467393df5347ae,
   0x3d4b39015ddaacd0,
   0x3d50026f483d2bed,
   0x3d52f2fbb90f3693,
   0x3d58c6d755043a45,
   0x3d5fdbc27dffa52b,
   0x3d63daafb0a88419,
   0x3d67f5b850d34e2a,
   0x3d6c07bb68d8ae27,
   0x3d702a3de0d4ae47,
   0x3d74d2844c632559,
   0x3d7aa94633d9d99f,
   0x3d808d3e905e29e3,
   0x3d83e5ab13d0ed15,
   0x3d872d2366ec3150,
   0x3d8a5bfb2a74a4d2,
   0x3d908a7d5cab006d,
   0x3d95197adddf2e21,
   0x3d9a1d1c622b0c7a,
   0x3d9f4b2d1759dfcb,
   0x3da229a9fa38e28c,
   0x3da4827fb77e50db,
   0x3da8ee60cf8a0a25,
   0x3dafb15e0e92a06e,
   0x3db38f3704387622,
   0x3db761936113be50,
   0x3dbb118434af1ddd,
   0x3dbe6d7c1163cde4,
   0x3dc1ed2ad889bafe,
   0x3dc6a95e1654e590]

theorem record2687ChunkBits008Length :
    (record2687ChunkBits008).length = 32 := by
  decide

theorem record2687ChunkSum008 :
    ((record2687ChunkBits008).map binary64Value2674).sum =
      (2450516188510565867 : ℚ) / 9903520314283042199192993792 := by
  norm_num [record2687ChunkBits008, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 288 through 319,
decoded and summed as exact rationals. -/
def record2687ChunkBits009 : List Nat :=
  [0x3dcbe884116f6014,
   0x3dd0a60afb3dcf14,
   0x3dd33c659fc0739e,
   0x3dd5912f1e9550fe,
   0x3dd8a39b110274ef,
   0x3ddef260b727c288,
   0x3de304f62c92d13c,
   0x3de6a8c342ed51b3,
   0x3dea24eea8d89307,
   0x3ded424582602842,
   0x3df066a7fd40df28,
   0x3df43bd6dbb4ba6a,
   0x3df8d4593c724b7b,
   0x3dfd8cf4a96c8609,
   0x3e010868aefa28a8,
   0x3e030a1eb64ea2af,
   0x3e05106989591322,
   0x3e09667e8f983e4e,
   0x3e0f1fa83a029b9a,
   0x3e1282000fc22e46,
   0x3e15538ffefb08ad,
   0x3e17d30feb538b69,
   0x3e1a1593893a2323,
   0x3e1ec5214bf368a0,
   0x3e22c5db5a8295e3,
   0x3e26512d73de2694,
   0x3e29b6e41cb2b577,
   0x3e2cb9247b36391f,
   0x3e2f311525317893,
   0x3e31fd016d7777d2,
   0x3e35d750a33c153f,
   0x3e39f5681696211d]

theorem record2687ChunkBits009Length :
    (record2687ChunkBits009).length = 32 := by
  decide

theorem record2687ChunkSum009 :
    ((record2687ChunkBits009).map binary64Value2674).sum =
      (3318071356822882417 : ℚ) / 77371252455336267181195264 := by
  norm_num [record2687ChunkBits009, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 320 through 351,
decoded and summed as exact rationals. -/
def record2687ChunkBits010 : List Nat :=
  [0x3e3deb0cc76f7d42,
   0x3e40b6f3efbe7a75,
   0x3e4225a4f31560b0,
   0x3e449328957e0872,
   0x3e488e4ff40588d9,
   0x3e4d2eb311c28b7b,
   0x3e50d36034487b9d,
   0x3e52d02715eac113,
   0x3e546e69afedeb08,
   0x3e56e0cad2e43225,
   0x3e5aba9822e497af,
   0x3e5fc39529af6965,
   0x3e6253dc4b9c5027,
   0x3e64833dc3327341,
   0x3e664b24d8ef7841,
   0x3e68b860d0f9a03b,
   0x3e6c4cb481e7c76f,
   0x3e70c40197f93227,
   0x3e735d50668ca44f,
   0x3e75b344eb2ab306,
   0x3e779c57dbe9af16,
   0x3e79f4cf0babdfe3,
   0x3e7d1f5fe6e19b48,
   0x3e813112dcdfc3d0,
   0x3e83e05594957a6f,
   0x3e864e6afd620dd8,
   0x3e884e259460ec6c,
   0x3e8a7d1898f79770,
   0x3e8d8933746ce56e,
   0x3e9126306de3c202,
   0x3e93d902a9194450,
   0x3e964f7917ad2d01]

theorem record2687ChunkBits010Length :
    (record2687ChunkBits010).length = 32 := by
  decide

theorem record2687ChunkSum010 :
    ((record2687ChunkBits010).map binary64Value2674).sum =
      (855809382240824329 : ℚ) / 302231454903657293676544 := by
  norm_num [record2687ChunkBits010, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 352 through 383,
decoded and summed as exact rationals. -/
def record2687ChunkBits011 : List Nat :=
  [0x3e985a0374fa83c5,
   0x3e9a4ecc34d187a7,
   0x3e9d479cf50774ae,
   0x3ea0aa21c74d9af2,
   0x3ea34e8861d8f2b8,
   0x3ea5bd8812e75810,
   0x3ea7c690bee68f88,
   0x3ea975cb3c9989d7,
   0x3eac5d845df74267,
   0x3eafaee319fe792b,
   0x3eb2516d55ad5bf6,
   0x3eb4aa2e32505e7d,
   0x3eb6a5c936ac9f70,
   0x3eb824750b62d914,
   0x3ebad741ed5b3902,
   0x3ebd6ce51b6724b0,
   0x3ec0f8dcdc59db3c,
   0x3ec32e9d3f853ea0,
   0x3ec51210214e517f,
   0x3ec6828aeffac47c,
   0x3ec8cf442ba5fec3,
   0x3ecb16322f415213,
   0x3ecebf2726a6edd0,
   0x3ed16842fa812c19,
   0x3ed32aa684179987,
   0x3ed4865c77099e72,
   0x3ed66c5aebb7a825,
   0x3ed87765627d2727,
   0x3edb419945052752,
   0x3edeeaf000076906,
   0x3ee1102182a8a0a5,
   0x3ee251b47b07b627]

theorem record2687ChunkBits011Length :
    (record2687ChunkBits011).length = 32 := by
  decide

theorem record2687ChunkSum011 :
    ((record2687ChunkBits011).map binary64Value2674).sum =
      (422770923570262071 : ℚ) / 4722366482869645213696 := by
  norm_num [record2687ChunkBits011, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 384 through 415,
decoded and summed as exact rationals. -/
def record2687ChunkBits012 : List Nat :=
  [0x3ee3d5eb4798d1a6,
   0x3ee5aff5726c6224,
   0x3ee7bc67ed738d6a,
   0x3eeae5573519c136,
   0x3eedc2b1f2bbdbb6,
   0x3ef004e0ee387189,
   0x3ef1306824fe4371,
   0x3ef2d992b71d4e55,
   0x3ef445ff3e56f443,
   0x3ef6f0a310a422d3,
   0x3ef97235c9595cdf,
   0x3efb7880e8255598,
   0x3efd3592c1c300da,
   0x3f0010cea6aa1d85,
   0x3f013d56289e40ec,
   0x3f0333534c67072a,
   0x3f0559852b5aa91d,
   0x3f071d69d11ca8ad,
   0x3f08616aabfcd6a6,
   0x3f0adfe596bfd174,
   0x3f0cd9a546d5a033,
   0x3f0f919cbf0ebcbb,
   0x3f1197564cbe3113,
   0x3f1319ed49efad46,
   0x3f1434dc8637a88e,
   0x3f16132f6708a938,
   0x3f17c3d38c421a85,
   0x3f19925bfca07ae9,
   0x3f1c7d62a7694309,
   0x3f1f06a50b2d0612,
   0x3f2075fccecb891b,
   0x3f21d1e4d38cd6d4]

theorem record2687ChunkBits012Length :
    (record2687ChunkBits012).length = 32 := by
  decide

theorem record2687ChunkSum012 :
    ((record2687ChunkBits012).map binary64Value2674).sum =
      (59151807481697783 : ℚ) / 36893488147419103232 := by
  norm_num [record2687ChunkBits012, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 416 through 447,
decoded and summed as exact rationals. -/
def record2687ChunkBits013 : List Nat :=
  [0x3f234090fa56098c,
   0x3f2460de1067ca60,
   0x3f26b095a01dfb3d,
   0x3f28c7f16a0faa87,
   0x3f2a60ccf4f944b1,
   0x3f2c4aff424c5252,
   0x3f2eadca3f578377,
   0x3f3039e8ddd09164,
   0x3f31c8edd35c364b,
   0x3f337a8d36f22473,
   0x3f34cced8ae4ed20,
   0x3f361a2979988834,
   0x3f380e38289c27df,
   0x3f397a4607aa66b7,
   0x3f3b76433af615a0,
   0x3f3e278a47dc78ed,
   0x3f4026f69f332c00,
   0x3f410038bd34b8ff,
   0x3f4292c1a975a8e2,
   0x3f43bd2dcabfbf74,
   0x3f44f01eb2c8baea,
   0x3f46ff8cc49ed5b6,
   0x3f48b78d2ac0de9e,
   0x3f49ebf7e422fac5,
   0x3f4c41d26ff9ec24,
   0x3f4e265d3eb440fe,
   0x3f4f7cc794d96e3e,
   0x3f514b07dd64153e,
   0x3f52a4e8d69f8c8f,
   0x3f539e41d0646979,
   0x3f553048eebf3e45,
   0x3f56b32b5aeb96e4]

theorem record2687ChunkBits013Length :
    (record2687ChunkBits013).length = 32 := by
  decide

theorem record2687ChunkSum013 :
    ((record2687ChunkBits013).map binary64Value2674).sum =
      (168802362286340077 : ℚ) / 9223372036854775808 := by
  norm_num [record2687ChunkBits013, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 448 through 479,
decoded and summed as exact rationals. -/
def record2687ChunkBits014 : List Nat :=
  [0x3f57b9dab7c994a1,
   0x3f59a77f0633a36b,
   0x3f5bbe5c4c0db890,
   0x3f5d4aafa33ad65e,
   0x3f5f56ec731e4318,
   0x3f60db58e7097567,
   0x3f61a6ffe51a7935,
   0x3f62c912a59f6fe4,
   0x3f645efd8a6e7025,
   0x3f6594afedfce5a2,
   0x3f66de7e5bb49b24,
   0x3f68b43edea98f84,
   0x3f69f894d049b595,
   0x3f6b3733992f553b,
   0x3f6d8980a12f4f17,
   0x3f6f659712494181,
   0x3f707970ee76eb4a,
   0x3f71ded180c9c943,
   0x3f72de151832f065,
   0x3f737bd477384685,
   0x3f75272a0a01dddc,
   0x3f768f39aad0f8c0,
   0x3f77837d765d4b65,
   0x3f7988996e3d9d6d,
   0x3f7b13996102ed24,
   0x3f7c03eacf8e312d,
   0x3f7df13ca6bb677f,
   0x3f8004aa3e93346a,
   0x3f80c0eba7c696ed,
   0x3f8205da76ea3e73,
   0x3f8332693cbb6b25,
   0x3f83e936cc293d83]

theorem record2687ChunkBits014Length :
    (record2687ChunkBits014).length = 32 := by
  decide

theorem record2687ChunkSum014 :
    ((record2687ChunkBits014).map binary64Value2674).sum =
      (166972075851896137 : ℚ) / 1152921504606846976 := by
  norm_num [record2687ChunkBits014, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 480 through 511,
decoded and summed as exact rationals. -/
def record2687ChunkBits015 : List Nat :=
  [0x3f84f546cb243fe5,
   0x3f867cdde9612939,
   0x3f879a15a682811b,
   0x3f8925c125c2ecb9,
   0x3f8ae7cdf8842a11,
   0x3f8c067faf10d688,
   0x3f8d105aa65d98a2,
   0x3f8f3916273953b1,
   0x3f907112bdf36223,
   0x3f915902f5bad382,
   0x3f92a4aeac75c287,
   0x3f9381e69894df90,
   0x3f93f63144273bb5,
   0x3f9571fa907f9144,
   0x3f96a994c23e8f55,
   0x3f97ac909b739336,
   0x3f998e014af5ad72,
   0x3f9adcfa785600b4,
   0x3f9b8e429f44d312,
   0x3f9d285c013e4615,
   0x3f9eea3ebc1691ee,
   0x3fa00a5fea23b854,
   0x3fa154675a698b17,
   0x3fa24d67149101b2,
   0x3fa2d40068479f06,
   0x3fa3a1a07cfd8fb1,
   0x3fa4dff29c799d33,
   0x3fa5bcd8b0c6c536,
   0x3fa7431d9e049ae2,
   0x3fa8af0f8a5a074a,
   0x3fa9823277810b4c,
   0x3faa376d4ae4235e]

theorem record2687ChunkBits015Length :
    (record2687ChunkBits015).length = 32 := by
  decide

theorem record2687ChunkSum015 :
    ((record2687ChunkBits015).map binary64Value2674).sum =
      (15274725092367625 : ℚ) / 18014398509481984 := by
  norm_num [record2687ChunkBits015, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 512 through 543,
decoded and summed as exact rationals. -/
def record2687ChunkBits016 : List Nat :=
  [0x3fabeb64ec9fb6ac,
   0x3fad2cdd83c417d8,
   0x3faeeae9ce845d24,
   0x3fb07b04b92b2217,
   0x3fb11c8f9b37ca3a,
   0x3fb15fa8a66ccff9,
   0x3fb27ec4a39cf09a,
   0x3fb36499b2b057b1,
   0x3fb458c2933de4df,
   0x3fb5cafeb7a06a64,
   0x3fb6bcb6b1f68bc7,
   0x3fb726b488321bb2,
   0x3fb848f0091a271a,
   0x3fb98cb6bce0cf2c,
   0x3fba88ce84b5d5b3,
   0x3fbc8cbcc5907ef0,
   0x3fbdee6a40efa0ee,
   0x3fbe92fefd7727b2,
   0x3fbf9dbd2384a1ff,
   0x3fc0adf6c2cd34eb,
   0x3fc141037a99865e,
   0x3fc2872e9234f1fe,
   0x3fc385415190098e,
   0x3fc409084b453308,
   0x3fc46e20c151a68c,
   0x3fc5982a0e6f109e,
   0x3fc66a76f7963563,
   0x3fc7d69d6bfb98d5,
   0x3fc93cc716c2394b,
   0x3fca07562be09705,
   0x3fca3fe93768e80e,
   0x3fcbb8e0387a9fd8]

theorem record2687ChunkBits016Length :
    (record2687ChunkBits016).length = 32 := by
  decide

theorem record2687ChunkSum016 :
    ((record2687ChunkBits016).map binary64Value2674).sum =
      (278377820166051223 : ℚ) / 72057594037927936 := by
  norm_num [record2687ChunkBits016, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 544 through 575,
decoded and summed as exact rationals. -/
def record2687ChunkBits017 : List Nat :=
  [0x3fccdfedbe502825,
   0x3fce6720a3ea1d9d,
   0x3fd02c0ddea147cc,
   0x3fd0c3430c21b6de,
   0x3fd0f5732933a698,
   0x3fd1a776ba72e5ed,
   0x3fd27331efedfca8,
   0x3fd33a8cbfcfdf73,
   0x3fd48da4d21466bf,
   0x3fd56919097986d1,
   0x3fd5bcd78daf36bd,
   0x3fd650af32671487,
   0x3fd76375c6f41fa4,
   0x3fd81f603a4813d4,
   0x3fd9e784c0cc588d,
   0x3fdb1f49054d900d,
   0x3fdbabffb90f5a03,
   0x3fdc05e1c373204f,
   0x3fdd6d648ce0bfbf,
   0x3fde5f6eca856667,
   0x3fe0322ad2469eb4,
   0x3fe10adea2daa83c,
   0x3fe17969e68247eb,
   0x3fe1850977d186b6,
   0x3fe25f7fdffa8a3d,
   0x3fe306f8ba2e7e30,
   0x3fe417b8db6d9018,
   0x3fe53fcd0481253a,
   0x3fe5e64b034a39f6,
   0x3fe60833ac5f3f75,
   0x3fe6c81595f7b34b,
   0x3fe7abd3dc497531]

theorem record2687ChunkBits017Length :
    (record2687ChunkBits017).length = 32 := by
  decide

theorem record2687ChunkSum017 :
    ((record2687ChunkBits017).map binary64Value2674).sum =
      (256601707714603511 : ℚ) / 18014398509481984 := by
  norm_num [record2687ChunkBits017, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 576 through 607,
decoded and summed as exact rationals. -/
def record2687ChunkBits018 : List Nat :=
  [0x3fe8be1856bc27bf,
   0x3fea4b6783205023,
   0x3feb3cf6eb622902,
   0x3feb81e9806e0d79,
   0x3fec0e87809b2a8e,
   0x3fed3c600a2130fd,
   0x3fee3db9f1b1e6cc,
   0x3ff0257634f0e819,
   0x3ff0d023021f5acc,
   0x3ff110721afac8f8,
   0x3ff12ce01482702f,
   0x3ff1ef002771f32b,
   0x3ff26b3046760831,
   0x3ff3b029222e39e9,
   0x3ff49b414695cfe8,
   0x3ff5053096808bf1,
   0x3ff4f79440e50716,
   0x3ff5da13071f1215,
   0x3ff6846be017570c,
   0x3ff7d5cbcbb59d4b,
   0x3ff9135cfa830abf,
   0x3ff9b690fff02f31,
   0x3ff9bdeb613186d8,
   0x3ffa7573ed715c46,
   0x3ffb5a87ef66a531,
   0x3ffca9582668ed94,
   0x3ffe4ddb71ea0bfb,
   0x3fff3c9b24857c10,
   0x3fff65e09224dbf5,
   0x3fffd76e92b4b291,
   0x40008171e8c5fbdf,
   0x40011d76229418a7]

theorem record2687ChunkBits018Length :
    (record2687ChunkBits018).length = 32 := by
  decide

theorem record2687ChunkSum018 :
    ((record2687ChunkBits018).map binary64Value2674).sum =
      (98758602235167035 : ℚ) / 2251799813685248 := by
  norm_num [record2687ChunkBits018, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 608 through 639,
decoded and summed as exact rationals. -/
def record2687ChunkBits019 : List Nat :=
  [0x40022f7506bb6a2f,
   0x4002d84199d0ef72,
   0x400309c2b4931e15,
   0x40030ec1275b6b86,
   0x4003ccb843aa91b6,
   0x40044fd1c155af5d,
   0x4005af0939d93767,
   0x40069675f273cf1c,
   0x4006efd24965e176,
   0x4006c6912c9ce79b,
   0x40079adb573b0fbe,
   0x400837e7fb28d6c6,
   0x4009af9d4e57f6ed,
   0x400ae5cf146d40dc,
   0x400b7561878a8028,
   0x400b5ebc92107ff3,
   0x400bfb5f2498a422,
   0x400ccce37815dea7,
   0x400e3d3d4e4bdffd,
   0x400fd3cf5395cd83,
   0x401054df029a7c90,
   0x401058fd6628dd4f,
   0x40107e4bd29f1873,
   0x401105d3882ccd38,
   0x4011b027b060812b,
   0x4012b605f15c9278,
   0x40134e5769c63ea0,
   0x40136c944967211e,
   0x40135948d2e6cdf0,
   0x4014036792eb5ab1,
   0x401492d1fb13a999,
   0x4015de40faaeba02]

theorem record2687ChunkBits019Length :
    (record2687ChunkBits019).length = 32 := by
  decide

theorem record2687ChunkSum019 :
    ((record2687ChunkBits019).map binary64Value2674).sum =
      (130261318155231345 : ℚ) / 1125899906842624 := by
  norm_num [record2687ChunkBits019, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 640 through 671,
decoded and summed as exact rationals. -/
def record2687ChunkBits020 : List Nat :=
  [0x4016af06d3a49275,
   0x4016f0ecfc792c04,
   0x4016b0532e9a0dae,
   0x401765b0e5f66d25,
   0x4017ea2090f696dc,
   0x40196777a213737a,
   0x401a7e12a25531f1,
   0x401aefe7902ab6cb,
   0x401abf2927fe27d8,
   0x401b366ed41cb211,
   0x401be657d85acf4a,
   0x401d57f67324abf7,
   0x401ec267924cda1d,
   0x401f717444a7b6df,
   0x401f5b7296cbe3a9,
   0x401f7d57b3f16b1f,
   0x40202f869208eb83,
   0x4020d930f8667e62,
   0x4021c08083aa9416,
   0x40223eeaecf37c88,
   0x40224a3816b98dee,
   0x4022235405bad91e,
   0x4022afdf376f283f,
   0x40233ea60d52e393,
   0x4024605243ad1bfc,
   0x40250e531712779a,
   0x402537b23b32ea59,
   0x4024e8b374ee9336,
   0x402576c47f3c4568,
   0x4025ddb5391cda4e,
   0x40274206193f2057,
   0x402829f3acdbc2f2]

theorem record2687ChunkBits020Length :
    (record2687ChunkBits020).length = 32 := by
  decide

theorem record2687ChunkSum020 :
    ((record2687ChunkBits020).map binary64Value2674).sum =
      (150042372856295979 : ℚ) / 562949953421312 := by
  norm_num [record2687ChunkBits020, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 672 through 703,
decoded and summed as exact rationals. -/
def record2687ChunkBits021 : List Nat :=
  [0x40287b387eabafa4,
   0x402839571e67e102,
   0x402889a15f09aca8,
   0x40291248b13cabf1,
   0x402a67efc0fea031,
   0x402b9426b4449f54,
   0x402c178d8d55d59c,
   0x402bebd7a89b84fc,
   0x402beb8e43160a9d,
   0x402c99e10e751366,
   0x402dd13f7288fe47,
   0x402f4dbc1a526829,
   0x403007f542133f50,
   0x403004340cf3de3a,
   0x402fa33465482c3c,
   0x40303d64f851bc60,
   0x4030c04241d0e0e9,
   0x4031ac6c5a70aaab,
   0x403233479fee532d,
   0x403247925cff2c5f,
   0x4031f48c2422e4b6,
   0x40325aec40405346,
   0x4032b9bb28bf7e85,
   0x4033da1d27284b24,
   0x40348e3b56a99042,
   0x4034c1fbdeceaa86,
   0x40347988537a3aaf,
   0x4034a7f74b6c3cb2,
   0x40350ad69c8fdb7a,
   0x40362ffa63dadefc,
   0x4037188ff76b2487,
   0x4037733b7fa81b1f]

theorem record2687ChunkBits021Length :
    (record2687ChunkBits021).length = 32 := by
  decide

theorem record2687ChunkSum021 :
    ((record2687ChunkBits021).map binary64Value2674).sum =
      (306861645204576755 : ℚ) / 562949953421312 := by
  norm_num [record2687ChunkBits021, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 704 through 735,
decoded and summed as exact rationals. -/
def record2687ChunkBits022 : List Nat :=
  [0x40373c766ec6f003,
   0x403724fb9cd2b843,
   0x4037a2dd6ed69830,
   0x4038aba8cbc9d3f6,
   0x4039d10e4871c8a2,
   0x403a5bd7a710d652,
   0x403a413663d051c3,
   0x4039d54e50b4c1e5,
   0x403a7050c86aa0ba,
   0x403b4d8776324d80,
   0x403cb78ccb5aaf76,
   0x403d7b853aa1b98e,
   0x403d85da2eec68be,
   0x403ce9c7e817a638,
   0x403d72733974c318,
   0x403e123a74b63f7b,
   0x403fc9ae7cf445c6,
   0x404068e730da7585,
   0x40408627a5bf20d3,
   0x404040a331bf9839,
   0x404056b25edf874f,
   0x40409ae4df9caf4c,
   0x404183a38bdc33b0,
   0x40422f541667f23b,
   0x40426a8daba779f4,
   0x40423344044304d4,
   0x404211a9265a69ba,
   0x40426a0f8c7ec9e9,
   0x4043377d026f9caa,
   0x4044121349adef9c,
   0x4044733f4dca7909,
   0x404452e2602d2e33]

theorem record2687ChunkBits022Length :
    (record2687ChunkBits022).length = 32 := by
  decide

theorem record2687ChunkSum022 :
    ((record2687ChunkBits022).map binary64Value2674).sum =
      (282210850585139101 : ℚ) / 281474976710656 := by
  norm_num [record2687ChunkBits022, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 736 through 767,
decoded and summed as exact rationals. -/
def record2687ChunkBits023 : List Nat :=
  [0x4043f0077b5ab933,
   0x40445fde2655e1ae,
   0x4045041714859591,
   0x4046161ba5cb2703,
   0x4046a689ad8520da,
   0x4046a5bcee643865,
   0x40462398441f2b89,
   0x40468480ba6600bd,
   0x4046ee0a2a6781c9,
   0x4048442a8e5d845e,
   0x404911dee2cf07b2,
   0x40493da748ed0c58,
   0x4048cdbca7f8bf30,
   0x4048eec90f38fed1,
   0x40495e3146abba94,
   0x404aafe69adf6044,
   0x404bce3fa41ad362,
   0x404c381e48a500e2,
   0x404be8dd04e9a332,
   0x404bc2d1caac2221,
   0x404c5fff674b783b,
   0x404d7771348ecb1c,
   0x404f05469bd00dfc,
   0x404fc8f1e160f6fd,
   0x404fb4c18d855c5e,
   0x404f3e73761b59c0,
   0x40500f22695c8f08,
   0x4050685555dfd228,
   0x40517e0fb28bd833,
   0x4052203b83309a9b,
   0x405243ff538f6862,
   0x405205259293f637]

theorem record2687ChunkBits023Length :
    (record2687ChunkBits023).length = 32 := by
  decide

theorem record2687ChunkSum023 :
    ((record2687ChunkBits023).map binary64Value2674).sum =
      (246769489229106487 : ℚ) / 140737488355328 := by
  norm_num [record2687ChunkBits023, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 768 through 799,
decoded and summed as exact rationals. -/
def record2687ChunkBits024 : List Nat :=
  [0x405280b6ac98740a,
   0x4052cf5a490e24e2,
   0x40540b234b3ff569,
   0x40550c12098e764b,
   0x4055789069250a64,
   0x40556b33dfce6e5f,
   0x4055d5442a6e085a,
   0x4056565ce7e09aa7,
   0x40577adef1ff8ff1,
   0x405903973267a4a7,
   0x4059dc6af7e6c3d9,
   0x405a29039068f65e,
   0x405a7dd905a354f7,
   0x405b54315af376d6,
   0x405c5bc767adb02a,
   0x405e9a6cfae5f381,
   0x40600ae86e65bb43,
   0x40607d139aa1a478,
   0x40609204f19a6d2a,
   0x40613d49c8f284a8,
   0x4061f92ef5ef3945,
   0x40635dd09931cd1b,
   0x40649053841512b4,
   0x40657ba01422b34f,
   0x40659e10734feef5,
   0x4066665e4ae66079,
   0x40680a49dbe5e8ff,
   0x406989a9e1d94637,
   0x406b465fd8989d45,
   0x406ceb93a413dc86,
   0x406d5c1bceb2b910,
   0x406e336e8b5aa5d0]

theorem record2687ChunkBits024Length :
    (record2687ChunkBits024).length = 32 := by
  decide

theorem record2687ChunkSum024 :
    ((record2687ChunkBits024).map binary64Value2674).sum =
      (306503209568004393 : ℚ) / 70368744177664 := by
  norm_num [record2687ChunkBits024, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 800 through 831,
decoded and summed as exact rationals. -/
def record2687ChunkBits025 : List Nat :=
  [0x4070d84b77a5834b,
   0x4071bf17934446c3,
   0x40729d7b928c8928,
   0x407408e9ca5df4c3,
   0x407484955bea6711,
   0x407600ba6ef94e60,
   0x4078683be99636a0,
   0x40798f815211f832,
   0x407a16a1d47a24ee,
   0x407c3c25aab3c653,
   0x407d82debbf5bb64,
   0x40802f19629469bc,
   0x4081e26bef4caf2e,
   0x4082ab739d391a07,
   0x4082fc2c759dbfcc,
   0x408407a43d148096,
   0x4085ddcf6018ca67,
   0x4087ce21d37b4ad1,
   0x4089fd698b33382e,
   0x408b1f225f3cce57,
   0x408bb98dd167d448,
   0x408c8b0ed8d237ab,
   0x408f8be23245d555,
   0x4091310b7cf2251a,
   0x4092816e9a074e2c,
   0x40935f7527e6d125,
   0x4093f43d129b3742,
   0x4094aabc9d02e3ca,
   0x40961d476af392ee,
   0x409825326bc91411,
   0x4099adb075796983,
   0x409b12707b5e8ecd]

theorem record2687ChunkBits025Length :
    (record2687ChunkBits025).length = 32 := by
  decide

theorem record2687ChunkSum025 :
    ((record2687ChunkBits025).map binary64Value2674).sum =
      (446157722617949865 : ℚ) / 17592186044416 := by
  norm_num [record2687ChunkBits025, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 832 through 863,
decoded and summed as exact rationals. -/
def record2687ChunkBits026 : List Nat :=
  [0x409c31d828421582,
   0x409d8988f43af987,
   0x409e5dda4d299f0f,
   0x40a08ddd1d9d14f7,
   0x40a1698501e06122,
   0x40a27aacb8d9f49c,
   0x40a376ed0bfb4439,
   0x40a4b13d4528b6f4,
   0x40a4f601c34b2525,
   0x40a6215536188bc0,
   0x40a74d42e1900a7e,
   0x40a8bf71435b4b55,
   0x40aa56c257a25fa4,
   0x40ac4ac1e585c0e2,
   0x40acc5a6106d0e36,
   0x40ad4f7f0379d340,
   0x40ae8f5edd9cfa0f,
   0x40b01a2145aeb90f,
   0x40b158673c6d3ef3,
   0x40b2e13e29cf5dea,
   0x40b36be09a61ec68,
   0x40b392740d208120,
   0x40b38e829df7f01a,
   0x40b452d793ac0edd,
   0x40b62b89ad9bc2a5,
   0x40b87fc2e4d32562,
   0x40b98eb54424c86f,
   0x40b9d04c7e581e3b,
   0x40b918be6615a506,
   0x40b90138c9d11520,
   0x40bb99410698fe51,
   0x40bf0f71b955ddfe]

theorem record2687ChunkBits026Length :
    (record2687ChunkBits026).length = 32 := by
  decide

theorem record2687ChunkSum026 :
    ((record2687ChunkBits026).map binary64Value2674).sum =
      (294723841625689811 : ℚ) / 2199023255552 := by
  norm_num [record2687ChunkBits026, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 864 through 895,
decoded and summed as exact rationals. -/
def record2687ChunkBits027 : List Nat :=
  [0x40c07d4e57de0981,
   0x40c0cd1d38db4173,
   0x40c0535c501ca9c7,
   0x40beb25e620deac3,
   0x40c0ec6707842f9c,
   0x40c36cc878d25d9d,
   0x40c4fbba833e57b8,
   0x40c5b2098368537b,
   0x40c53f96b7560b3c,
   0x40c37e7bdb562b39,
   0x40c48121b99d4b27,
   0x40c8194052d2a95a,
   0x40caa55d043a7c16,
   0x40cc040fab004cbb,
   0x40cbc57e23cebbf3,
   0x40c9d917371371a8,
   0x40c9c425471536b0,
   0x40cea1c2ca682ce9,
   0x40d125b4a2c8eb05,
   0x40d231b93b9e09ac,
   0x40d2302359debe4b,
   0x40d1346b46018421,
   0x40d08e3022a2be7e,
   0x40d3116c6d90c29e,
   0x40d59a3b30ab85db,
   0x40d71023506191cb,
   0x40d73b85675f6c0c,
   0x40d63f122f5d9acd,
   0x40d56f72caef0084,
   0x40d73e95a2fcd61e,
   0x40da890dc3967268,
   0x40dc9ed19ec0edee]

theorem record2687ChunkBits027Length :
    (record2687ChunkBits027).length = 32 := by
  decide

theorem record2687ChunkSum027 :
    ((record2687ChunkBits027).map binary64Value2674).sum =
      (555458355804603847 : ℚ) / 1099511627776 := by
  norm_num [record2687ChunkBits027, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 896 through 927,
decoded and summed as exact rationals. -/
def record2687ChunkBits028 : List Nat :=
  [0x40dd1e79f87ca663,
   0x40dc1348d5597514,
   0x40db36476128a27a,
   0x40dca8db3a8458dd,
   0x40dfe6cddafd336d,
   0x40e1695cb30a0d66,
   0x40e1e78da764bb19,
   0x40e163c718b827c0,
   0x40e0f78eb2b10bf1,
   0x40e17f52c64eb094,
   0x40e2df75dc859584,
   0x40e4c438939d40f2,
   0x40e59d027d7b1802,
   0x40e533f4ee277ae1,
   0x40e4dd9fa96998fb,
   0x40e4f47ae3212595,
   0x40e6bf8a0e48e7d7,
   0x40e8563fa7788759,
   0x40e99e08d2c498e0,
   0x40e96c1e4187cf87,
   0x40e94c1f9513bcf0,
   0x40e9645739b0feae,
   0x40eb131611959afa,
   0x40ec25944ba0fcd5,
   0x40edcf8bfa7aaa94,
   0x40edf73a524d89c8,
   0x40ee33e7631d960e,
   0x40ee787403c12cad,
   0x40efb2da72e28d44,
   0x40f0a904a5f1290c,
   0x40f1185a3b30cda9,
   0x40f15a4b3790132c]

theorem record2687ChunkBits028Length :
    (record2687ChunkBits028).length = 32 := by
  decide

theorem record2687ChunkSum028 :
    ((record2687ChunkBits028).map binary64Value2674).sum =
      (417894814057200087 : ℚ) / 274877906944 := by
  norm_num [record2687ChunkBits028, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 928 through 959,
decoded and summed as exact rationals. -/
def record2687ChunkBits029 : List Nat :=
  [0x40f1b790912e593d,
   0x40f2092f25a7cc99,
   0x40f23aa55a43892e,
   0x40f365be7387bf0b,
   0x40f38625bc9652de,
   0x40f3df903426e898,
   0x40f4736622ceb0a0,
   0x40f4f8ccad1110e8,
   0x40f48c2563adf118,
   0x40f624ef1521036b,
   0x40f694a708a51b0d,
   0x40f6699b389c8b8b,
   0x40f746a4945771ef,
   0x40f80fe944cc30ce,
   0x40f7854e3f49c974,
   0x40f8cd584fc6a5b5,
   0x40f99a8ff8674004,
   0x40f9187a255ef780,
   0x40fa06b16788c60d,
   0x40fb2c4e97f8ff87,
   0x40fac7565f7824d9,
   0x40fb4dc06fb8bb1d,
   0x40fc90e9242699b2,
   0x40fc6162d9d35223,
   0x40fc98efb8a766ec,
   0x40fe2251f75174b3,
   0x40fdfb03b17fcbde,
   0x40fd9f9edfeda757,
   0x40ff617b3810fc85,
   0x40ff8a09ebcc70c7,
   0x40ff5ce5c553247e,
   0x41007088a9fc08cb]

theorem record2687ChunkBits029Length :
    (record2687ChunkBits029).length = 32 := by
  decide

theorem record2687ChunkSum029 :
    ((record2687ChunkBits029).map binary64Value2674).sum =
      (224608668317176613 : ℚ) / 68719476736 := by
  norm_num [record2687ChunkBits029, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 960 through 991,
decoded and summed as exact rationals. -/
def record2687ChunkBits030 : List Nat :=
  [0x410087de7c379678,
   0x40ff8f808c31d29d,
   0x4100f0464d934dc5,
   0x41013a59592eb59f,
   0x41014c8256035468,
   0x4101ae14cdca15da,
   0x4101ef2327386295,
   0x410136b3648c7f02,
   0x4101f9c9cda83182,
   0x4102865a7c6620cf,
   0x4102cef85a495ce7,
   0x410300a6471105ee,
   0x4103233a3f5c57c6,
   0x41029a9a4e812960,
   0x4102c512d2cf0b1d,
   0x410391b66a218a34,
   0x4104180a2d188bfc,
   0x4104788243c44ffa,
   0x41041e31df05d2b1,
   0x4103c43709164556,
   0x41034ff09320c6ff,
   0x41045a3179cec83b,
   0x41051849868fd606,
   0x4105aeb31e9fc1c6,
   0x41053fecc95a67f6,
   0x4104bb4d4f43d159,
   0x41039580675723c9,
   0x4104cbfd9a0e7c3c,
   0x4105c826384e9a40,
   0x41069a963b0f4f3d,
   0x410664beb2bad6d5,
   0x410561f642e3a3ba]

theorem record2687ChunkBits030Length :
    (record2687ChunkBits030).length = 32 := by
  decide

theorem record2687ChunkSum030 :
    ((record2687ChunkBits030).map binary64Value2674).sum =
      (349260507337188871 : ℚ) / 68719476736 := by
  norm_num [record2687ChunkBits030, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 992 through 1023,
decoded and summed as exact rationals. -/
def record2687ChunkBits031 : List Nat :=
  [0x41045f51f8eb5c82,
   0x4104f210a9e2c6ad,
   0x41061fe2da2b359f,
   0x41072ade9b62b409,
   0x4107359740a91d40,
   0x41062ef20fe2aa23,
   0x4104e79a49482e5e,
   0x4104cc6e976db113,
   0x41062a731fe6e2a8,
   0x410760ff9a961f90,
   0x4107a46ba52a0273,
   0x4106d0e12f4258b0,
   0x410520216260b87d,
   0x410461ffef5449ba,
   0x4105e1471087acce,
   0x4107457270e26157,
   0x4107b15660c1c344,
   0x410712d6b716f2a2,
   0x41057ed1ba817924,
   0x4103b57a35ad1c75,
   0x41054bd963d927fe,
   0x4106d57f1f3dc119,
   0x4107698516748be8,
   0x4106faaec18ade19,
   0x410598ebd5b8baf9,
   0x41037e1e89c1b1d5,
   0x41046c6be341f7f8,
   0x41060b3eab8a0746,
   0x4106c7f54c12a58e,
   0x41068e58ad93b381,
   0x4105625fdbb57bf4,
   0x410369b0c8cc7329]

theorem record2687ChunkBits031Length :
    (record2687ChunkBits031).length = 32 := by
  decide

theorem record2687ChunkSum031 :
    ((record2687ChunkBits031).map binary64Value2674).sum =
      (197187968412316721 : ℚ) / 34359738368 := by
  norm_num [record2687ChunkBits031, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1024 through 1055,
decoded and summed as exact rationals. -/
def record2687ChunkBits032 : List Nat :=
  [0x41035976fe9836e6,
   0x41052d42e00dc64a,
   0x41063160971aed86,
   0x41064508b8052b9d,
   0x41056926dd370f04,
   0x4103b5bf1dbdbb3e,
   0x4102b1f1df33efe8,
   0x410493b19ab3cd15,
   0x4105c067dd123af8,
   0x410604b080937a67,
   0x41055630275cac88,
   0x4103c5f8435c80df,
   0x410230d0052aeb13,
   0x4103b45124638a8e,
   0x41050373b8e02a0d,
   0x41057008902bc472,
   0x4104ebbca039c78a,
   0x41038c8f3d95b9b9,
   0x41021a281938e015,
   0x4102a0c96c06f877,
   0x4103fd9c83a65c26,
   0x4104948c571b48ba,
   0x4104390d910c2956,
   0x41030f23a6a4a8b4,
   0x4101c576f42857ac,
   0x4101bc41105343ee,
   0x4102b280a328efb1,
   0x410370e7a4e8c965,
   0x410349b6f40794b6,
   0x41024f0de98762ef,
   0x410139d7369a0fa0,
   0x4100a20e85718d29]

theorem record2687ChunkBits032Length :
    (record2687ChunkBits032).length = 32 := by
  decide

theorem record2687ChunkSum032 :
    ((record2687ChunkBits032).map binary64Value2674).sum =
      (178106509405036111 : ℚ) / 34359738368 := by
  norm_num [record2687ChunkBits032, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1056 through 1087,
decoded and summed as exact rationals. -/
def record2687ChunkBits033 : List Nat :=
  [0x4101594b106d83ac,
   0x41020de20060ac38,
   0x41021cc3e434c9b5,
   0x4101590fb5bc09cb,
   0x410075e4a55c2bae,
   0x40fec6f7268d833a,
   0x410031edf92c0369,
   0x41007dbd9abc50bb,
   0x4100b9124600c449,
   0x41002ac02874f1c3,
   0x40ff000d483addab,
   0x40fd3e656ea86172,
   0x40fdbc81a8fa73d2,
   0x40fe1164861ba484,
   0x40fe65985d71ca9e,
   0x40fda4bb394ab4a9,
   0x40fcad538be0e5ba,
   0x40fb5a390dbdeb21,
   0x40faf0cc1b5569fe,
   0x40fb8b4e81d767d0,
   0x40fb2a9eba27bebd,
   0x40fab631ceceacf6,
   0x40fa1e5f04ccdb17,
   0x40f932775b08eb53,
   0x40f7fd67ff529f7b,
   0x40f8d96b2c8c04df,
   0x40f8579e1bfabd21,
   0x40f7a739cb9bb54e,
   0x40f75fdaabcc96e0,
   0x40f6d4906a31c095,
   0x40f52c9ce1f01cab,
   0x40f60c1d2699980d]

theorem record2687ChunkBits033Length :
    (record2687ChunkBits033).length = 32 := by
  decide

theorem record2687ChunkSum033 :
    ((record2687ChunkBits033).map binary64Value2674).sum =
      (64643184049959181 : ℚ) / 17179869184 := by
  norm_num [record2687ChunkBits033, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1088 through 1119,
decoded and summed as exact rationals. -/
def record2687ChunkBits034 : List Nat :=
  [0x40f5caf33ecd991f,
   0x40f4a5d4f6a73acf,
   0x40f4956c28bfa263,
   0x40f4569982dd18a7,
   0x40f31a50d4f4c5b1,
   0x40f33c4cd7f105c6,
   0x40f337c37915e65a,
   0x40f220debe3c3629,
   0x40f1d07d94cd56e2,
   0x40f1cf6876542492,
   0x40f0ec77ec9703fe,
   0x40f084b8329e7a33,
   0x40f0aa033fd30529,
   0x40efbcbe5430740a,
   0x40ee573294046de2,
   0x40eeb96a57532120,
   0x40ed94fd9be7373c,
   0x40ebf2e9633e0ca4,
   0x40ec5f1757c1ae17,
   0x40eb4a893a8ef219,
   0x40ea1bc72a4cfad5,
   0x40ea13737b20039f,
   0x40e969e5cd943e8e,
   0x40e77a130ce06ee2,
   0x40e7c93aba923ca1,
   0x40e70f8e48fe9947,
   0x40e6477811097626,
   0x40e5aee5551db090,
   0x40e569a3a392f9b0,
   0x40e40348115429d7,
   0x40e3b17665a5d795,
   0x40e33b75703bb149]

theorem record2687ChunkBits034Length :
    (record2687ChunkBits034).length = 32 := by
  decide

theorem record2687ChunkSum034 :
    ((record2687ChunkBits034).map binary64Value2674).sum =
      (272407727979308931 : ℚ) / 137438953472 := by
  norm_num [record2687ChunkBits034, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1120 through 1151,
decoded and summed as exact rationals. -/
def record2687ChunkBits035 : List Nat :=
  [0x40e2bc17676fcac6,
   0x40e2488945889e50,
   0x40e1accf993168e2,
   0x40e0b4c2ccdab402,
   0x40e003d3c2bc7fac,
   0x40df8ce0eaa0e23f,
   0x40df21887e882e3f,
   0x40dea1d2bf05eae2,
   0x40dca4b235329560,
   0x40db62777c63bf3d,
   0x40d99670a76bb882,
   0x40d95ef275c3dc6c,
   0x40d96289d4a952b7,
   0x40d9458699df5853,
   0x40d7c8e42b26c55d,
   0x40d60ad5fdc87ff9,
   0x40d434db45f83ab8,
   0x40d40e3d9ec3efe8,
   0x40d454b802c024a3,
   0x40d4778619f55699,
   0x40d3772d27664572,
   0x40d17dc158ef1f08,
   0x40d0206069d0edc3,
   0x40cf33ef65cd1bf1,
   0x40cfeb6168c862d5,
   0x40d043728af4cc7b,
   0x40cf4e8d81863c2b,
   0x40cc63abed73d378,
   0x40c93d5e5468d27b,
   0x40c7e9bc15350a09,
   0x40c8a1caa32bf104,
   0x40c9647829991896]

theorem record2687ChunkBits035Length :
    (record2687ChunkBits035).length = 32 := by
  decide

theorem record2687ChunkSum035 :
    ((record2687ChunkBits035).map binary64Value2674).sum =
      (412651502069989085 : ℚ) / 549755813888 := by
  norm_num [record2687ChunkBits035, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1152 through 1183,
decoded and summed as exact rationals. -/
def record2687ChunkBits036 : List Nat :=
  [0x40c8b37fe655776b,
   0x40c6abeaca2627a4,
   0x40c39b731cb34305,
   0x40c205d9f994b1e4,
   0x40c2af63e0062c11,
   0x40c37d7d02dc6281,
   0x40c328a037d2d426,
   0x40c1c6c9a2d0b178,
   0x40bf182ce2c4f05d,
   0x40bac578592c2781,
   0x40bbd5980f7fbd39,
   0x40bd71020df27fda,
   0x40bd3896a78ff9ae,
   0x40bb547e3b498abc,
   0x40b83f0ed47871ba,
   0x40b4388594cfd909,
   0x40b45e85fdc06d1a,
   0x40b5d2d117394b6f,
   0x40b5e5950c5e9bd5,
   0x40b4c00c209528dd,
   0x40b2a31d17d4e1cc,
   0x40af75ece91204d3,
   0x40ad885b6bfc13b1,
   0x40afdc732b078f93,
   0x40b02da40ae9710c,
   0x40af228f49e4c10f,
   0x40ac67f43a0dedcd,
   0x40a85630d25efd3a,
   0x40a5c1d5b8969771,
   0x40a6ef889f73504c,
   0x40a79ef5fef1ee43,
   0x40a71d61078cea0e]

theorem record2687ChunkBits036Length :
    (record2687ChunkBits036).length = 32 := by
  decide

theorem record2687ChunkSum036 :
    ((record2687ChunkBits036).map binary64Value2674).sum =
      (444799128362851645 : ℚ) / 2199023255552 := by
  norm_num [record2687ChunkBits036, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1184 through 1215,
decoded and summed as exact rationals. -/
def record2687ChunkBits037 : List Nat :=
  [0x40a5596c543dcda1,
   0x40a29158b30f2b7e,
   0x40a08c3bca6202ad,
   0x40a07748c3ca6a2c,
   0x40a1081a5274c22e,
   0x40a0ec2547f117b6,
   0x409fbbc4ad07a899,
   0x409c102a8b894fc1,
   0x4099526a44e41705,
   0x40982b70fc649b67,
   0x40984257827a0f75,
   0x409872dae1538017,
   0x409743a890cc8242,
   0x4094eae45314cd30,
   0x409326ce515ff04a,
   0x4092086268e70e81,
   0x409138a8a2e6fe86,
   0x40916dba6dd3df40,
   0x4090cc503acacb28,
   0x408ea485d2550be9,
   0x408c66c9a010c53a,
   0x408a77b2a1e33a5f,
   0x4088f245ac68ee9e,
   0x40887d210afb49c1,
   0x4087d7d48f00cc9e,
   0x4085ebb432b40cbc,
   0x4084728df55e1974,
   0x4082f6b08cbe7541,
   0x4081cd2788f15710,
   0x4080c1eede8f9d53,
   0x40806444b24ae6ef,
   0x407e69890836e290]

theorem record2687ChunkBits037Length :
    (record2687ChunkBits037).length = 32 := by
  decide

theorem record2687ChunkSum037 :
    ((record2687ChunkBits037).map binary64Value2674).sum =
      (91158395916342973 : ℚ) / 2199023255552 := by
  norm_num [record2687ChunkBits037, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1216 through 1247,
decoded and summed as exact rationals. -/
def record2687ChunkBits038 : List Nat :=
  [0x407c86e999b7ffc1,
   0x407a7c4776e87c98,
   0x407875a8f5e4c972,
   0x4076c1f162435618,
   0x40759d14b646098e,
   0x40742683d219942e,
   0x407309b72e3441e0,
   0x4071c154e49a3d3a,
   0x40702c542650b98d,
   0x406deb524c819db3,
   0x406b5b349740c565,
   0x406977cb4ef185d9,
   0x406835da858d7e7e,
   0x4066ada5992aaa06,
   0x40645e797cfe735c,
   0x4062d5c9b119f2c9,
   0x406108b467371854,
   0x405e7c303beb9420,
   0x405d27a54e36b618,
   0x405b5dc8d6c8dde3,
   0x405843aad5a9069c,
   0x4056965fefe03cdf,
   0x40544deda127e6cc,
   0x40517680bbd395eb,
   0x40511312dafce61b,
   0x4050909457124ef6,
   0x404f1753be6ce6f2,
   0x404dad0d561f0c50,
   0x404be06f9036a868,
   0x4049e8ae5e67ffe1,
   0x40491ef84e9a483f,
   0x40491495e4fd6fd1]

theorem record2687ChunkBits038Length :
    (record2687ChunkBits038).length = 32 := by
  decide

theorem record2687ChunkSum038 :
    ((record2687ChunkBits038).map binary64Value2674).sum =
      (814713736050401343 : ℚ) / 140737488355328 := by
  norm_num [record2687ChunkBits038, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1248 through 1279,
decoded and summed as exact rationals. -/
def record2687ChunkBits039 : List Nat :=
  [0x40479a0ae60d9ddd,
   0x404600652ea4e59f,
   0x4044bf852f251d6f,
   0x404444b8d6dc90f9,
   0x4043a16fc01a3d4a,
   0x4043875ea7c4055b,
   0x404274e851e96e3b,
   0x4040e2ebde98149d,
   0x40400c26dfd82a9a,
   0x4040019caa695584,
   0x403f8e6393e83953,
   0x403ef9d77aed4e0d,
   0x403d75840fadc878,
   0x403ad7dd34c3b557,
   0x40397ed40592a3a3,
   0x40398dcbbb328d3b,
   0x403992a1715057e6,
   0x40390048d54c389e,
   0x4037d704cb4bbf5d,
   0x4035ee425e930aa2,
   0x4034a21f2332ace1,
   0x4034a1a5dc79f881,
   0x4034d81880ceed82,
   0x4034815fdb8e8cd1,
   0x40338f95e2434b62,
   0x40322877f4b85287,
   0x4030efe469a8bc69,
   0x4030db1c5bc4fd50,
   0x403122a1e93d5abf,
   0x4030f688b59c89e4,
   0x4030443530ab5751,
   0x402e6edde00d7900]

theorem record2687ChunkBits039Length :
    (record2687ChunkBits039).length = 32 := by
  decide

theorem record2687ChunkSum039 :
    ((record2687ChunkBits039).map binary64Value2674).sum =
      (245527203028266841 : ℚ) / 281474976710656 := by
  norm_num [record2687ChunkBits039, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1280 through 1311,
decoded and summed as exact rationals. -/
def record2687ChunkBits040 : List Nat :=
  [0x402c224d82a1571c,
   0x402bd6b2ecc98f98,
   0x402c6edbc8cbaf47,
   0x402c50fe4fb52e71,
   0x402b605e85fc743f,
   0x4029c8c50a03bb15,
   0x4027cc6222682f13,
   0x402738d8fbdc39e9,
   0x4027cee204a9333b,
   0x4027d79839d45802,
   0x40273ba0f32b5c09,
   0x40260cb20f807a7e,
   0x40247add7d42cbed,
   0x40238819ee204743,
   0x4024194151f15249,
   0x40243d44e305b771,
   0x4023dd56e158ddd0,
   0x4022ffae49f40247,
   0x4021c1326f0f7509,
   0x4020bdde14c780f3,
   0x40211293581ed8ac,
   0x402148794e57224c,
   0x402113479d555b71,
   0x4020726c9778e823,
   0x401eefedfd97edc6,
   0x401cd4fbfe493057,
   0x401d1d9cf1d68ac5,
   0x401da03177f629c6,
   0x401d740e0b009359,
   0x401c8ed34f60f4ce,
   0x401b06f2cb174a18,
   0x401917790c1d4932]

theorem record2687ChunkBits040Length :
    (record2687ChunkBits040).length = 32 := by
  decide

theorem record2687ChunkSum040 :
    ((record2687ChunkBits040).map binary64Value2674).sum =
      (361269537107856939 : ℚ) / 1125899906842624 := by
  norm_num [record2687ChunkBits040, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1312 through 1343,
decoded and summed as exact rationals. -/
def record2687ChunkBits041 : List Nat :=
  [0x4018df8cb74fcb7c,
   0x40196d7c295b5409,
   0x40196d72dd5f7cae,
   0x4018ced48bc8d393,
   0x40179df9f276aa11,
   0x4016043028af3d08,
   0x40153f070b61ba59,
   0x4015d0566313d2f2,
   0x4015ef97f6dd3594,
   0x401587c904c8d4f6,
   0x40149d9b4aca03cf,
   0x40134d7f615a2839,
   0x4012354baf38e974,
   0x4012adc6a0a015d5,
   0x4012e177d4812be2,
   0x4012a35c1a759f09,
   0x4011f2696e43aba6,
   0x4010e1eb182a830b,
   0x400f70dc429a057c,
   0x400fe4758b1080be,
   0x401032a46ed7d64d,
   0x4010146ab8697444,
   0x400f2460517544a8,
   0x400d70b96bda9670,
   0x400b4d42355b40da,
   0x400b2233557cd2d1,
   0x400baf41e3dd324d,
   0x400ba16ddf708aa6,
   0x400ae7b9d5224db2,
   0x40099095b4b4bc0a,
   0x4007c975b8aaa7ca,
   0x4006fe16a94d3c69]

theorem record2687ChunkBits041Length :
    (record2687ChunkBits041).length = 32 := by
  decide

theorem record2687ChunkSum041 :
    ((record2687ChunkBits041).map binary64Value2674).sum =
      (326840446709914691 : ℚ) / 2251799813685248 := by
  norm_num [record2687ChunkBits041, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1344 through 1375,
decoded and summed as exact rationals. -/
def record2687ChunkBits042 : List Nat :=
  [0x40078e4ada48d94d,
   0x4007a21e9f674542,
   0x40072425414c07f1,
   0x40061aabd01d2e91,
   0x4004a5809df932d0,
   0x40036985be64229d,
   0x4003f39822a8d0e4,
   0x40041db4beffa1bd,
   0x4003cded08d24992,
   0x400304693b398a60,
   0x4001d71c32b97a18,
   0x40008d6edd8f970a,
   0x4000d13cc7d7d8f3,
   0x4001096911190c6c,
   0x4000dd35c54986ca,
   0x4000482be9071cdc,
   0x3ffeb11a95e62558,
   0x3ffc5fa40732c1fa,
   0x3ffc384d1cf21e9c,
   0x3ffcb68b709ce5bc,
   0x3ffc924c74127628,
   0x3ffbbc0ba129a39d,
   0x3ffa44c44bf9c705,
   0x3ff85cbdfa2e1f4d,
   0x3ff790171bc7ced3,
   0x3ff812764119b482,
   0x3ff813cc12531656,
   0x3ff780072fc24106,
   0x3ff65f661900bb6b,
   0x3ff4d3b7aae80e26,
   0x3ff3967e9e45504a,
   0x3ff413df84821207]

theorem record2687ChunkBits042Length :
    (record2687ChunkBits042).length = 32 := by
  decide

theorem record2687ChunkSum042 :
    ((record2687ChunkBits042).map binary64Value2674).sum =
      (72237977652658737 : ℚ) / 1125899906842624 := by
  norm_num [record2687ChunkBits042, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1376 through 1407,
decoded and summed as exact rationals. -/
def record2687ChunkBits043 : List Nat :=
  [0x3ff42e2669952685,
   0x3ff3cd63d22fcdf8,
   0x3ff2f35868fb80d7,
   0x3ff1b77a83b9d715,
   0x3ff05ea331c9c54f,
   0x3ff0a86368f842bb,
   0x3ff0d27ea650ac9a,
   0x3ff09899ecc679e1,
   0x3fefef5a3d83b74a,
   0x3fedfe5f5c52f26a,
   0x3feba0c5a5d3fb9b,
   0x3feb805a48d94506,
   0x3febe4d595a5dc0a,
   0x3feba98c8728814a,
   0x3feac1c4decf4318,
   0x3fe9404c24dd13cb,
   0x3fe754f204219b47,
   0x3fe6955cb51d9ff1,
   0x3fe6ffb6804cb44c,
   0x3fe6eccfc0a7e31d,
   0x3fe64b77b3b71358,
   0x3fe5257cba6dfa36,
   0x3fe39c77665149d5,
   0x3fe274f640273cff,
   0x3fe2db978f654d46,
   0x3fe2e37fd8fe0fa9,
   0x3fe2778f99034943,
   0x3fe19b17619d0297,
   0x3fe0656e88aafb3f,
   0x3fde29e7139089c8,
   0x3fdebfdefae76a88,
   0x3fdef1eb098dbcb9]

theorem record2687ChunkBits043Length :
    (record2687ChunkBits043).length = 32 := by
  decide

theorem record2687ChunkSum043 :
    ((record2687ChunkBits043).map binary64Value2674).sum =
      (461791601108250607 : ℚ) / 18014398509481984 := by
  norm_num [record2687ChunkBits043, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1408 through 1439,
decoded and summed as exact rationals. -/
def record2687ChunkBits044 : List Nat :=
  [0x3fde6a5ecdcf8e45,
   0x3fdd267e21bc8533,
   0x3fdb454d74fddcfa,
   0x3fd9054772822efd,
   0x3fd8eeb1e425fd3d,
   0x3fd9331f310c65b9,
   0x3fd8e571c181345b,
   0x3fd7fc8cb362c0ac,
   0x3fd68bc18e1353ed,
   0x3fd4bf1cdd1d33fe,
   0x3fd419e4866fd48d,
   0x3fd46628ad9effd6,
   0x3fd44184dd27f122,
   0x3fd39eb61bc2340e,
   0x3fd2885fd4f32d57,
   0x3fd11d6edb8504e0,
   0x3fd01f5e3c5c1367,
   0x3fd069e60615af33,
   0x3fd06089f3667c4f,
   0x3fcfe46b88519c24,
   0x3fce46d2c73c5ee6,
   0x3fcc13558156f88b,
   0x3fc9b7d66be283f6,
   0x3fca40797cbb0b5b,
   0x3fca50d9f4a8ecac,
   0x3fc9c21117b9ea53,
   0x3fc8948246feb36c,
   0x3fc6e4dcb50ff79d,
   0x3fc4e9e67da7876a,
   0x3fc4ddf957ea1e2c,
   0x3fc5020bea984a24,
   0x3fc4aadbc9bc82af]

theorem record2687ChunkBits044Length :
    (record2687ChunkBits044).length = 32 := by
  decide

theorem record2687ChunkSum044 :
    ((record2687ChunkBits044).map binary64Value2674).sum =
      (327474141061139307 : ℚ) / 36028797018963968 := by
  norm_num [record2687ChunkBits044, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1440 through 1471,
decoded and summed as exact rationals. -/
def record2687ChunkBits045 : List Nat :=
  [0x3fc3d30e3f4dbbc8,
   0x3fc28cc768bb7f27,
   0x3fc0fdef7605a543,
   0x3fc07be30a7eaea4,
   0x3fc0a989c6c89d02,
   0x3fc07976ff0ec67c,
   0x3fbfc557d251ed72,
   0x3fbddf37a64219d8,
   0x3fbb7521e8fd06d3,
   0x3fb9e57ab7db32e1,
   0x3fba41df00a4f059,
   0x3fba15cd579a5cf8,
   0x3fb94842b941cbf3,
   0x3fb7e351d6d57a7b,
   0x3fb60b8757ca6d0a,
   0x3fb43769bce54943,
   0x3fb48ceb8c5a5d11,
   0x3fb4829838df4701,
   0x3fb3fb4bbeecf06f,
   0x3fb2f9b63e9fc65c,
   0x3fb196280d5d0e0b,
   0x3faff9bc429aa584,
   0x3faff443c8d7cb95,
   0x3fb00381be7f08c5,
   0x3faf5bbbffeae5db,
   0x3fadee2117f1c530,
   0x3fabdd392a4a8049,
   0x3fa96515ab55f3df,
   0x3fa8ac56daaaac1c,
   0x3fa8d43006139103,
   0x3fa86e2afbbcd3b0,
   0x3fa76ffc0e7dff81]

theorem record2687ChunkBits045Length :
    (record2687ChunkBits045).length = 32 := by
  decide

theorem record2687ChunkSum045 :
    ((record2687ChunkBits045).map binary64Value2674).sum =
      (202742575941235117 : ℚ) / 72057594037927936 := by
  norm_num [record2687ChunkBits045, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1472 through 1503,
decoded and summed as exact rationals. -/
def record2687ChunkBits046 : List Nat :=
  [0x3fa5ec0ac0fc4e22,
   0x3fa40b7db94c7adf,
   0x3fa2eefcb0bcb1de,
   0x3fa31becf0e84fb0,
   0x3fa2e403d038d09c,
   0x3fa236e8889bd96e,
   0x3fa11e4a15ea1501,
   0x3f9f6cccad2dc795,
   0x3f9cdc10d9fbc2b1,
   0x3f9d32980ce70383,
   0x3f9cfed3b9f155d1,
   0x3f9c19588fdb050b,
   0x3f9a89cd1c2ff4f5,
   0x3f987581f14cdeaf,
   0x3f962091b0ea576c,
   0x3f9624376e43ce43,
   0x3f9614a24b0a2531,
   0x3f9580bdad479f95,
   0x3f946897b333244e,
   0x3f92e426457f50be,
   0x3f911e966a30fcb4,
   0x3f90a9d43726eb2d,
   0x3f90aef35e2827be,
   0x3f905357b769228e,
   0x3f8f24f5114fd01d,
   0x3f8cf58f42a4bde0,
   0x3f8a52ec7118e3e0,
   0x3f88e8fbb411f01d,
   0x3f89023e52c6f7a1,
   0x3f8895c5e2a0bceb,
   0x3f8790d9f1bdfb23,
   0x3f86038b821f16ff]

theorem record2687ChunkBits046Length :
    (record2687ChunkBits046).length = 32 := by
  decide

theorem record2687ChunkSum046 :
    ((record2687ChunkBits046).map binary64Value2674).sum =
      (214832794612823423 : ℚ) / 288230376151711744 := by
  norm_num [record2687ChunkBits046, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1504 through 1535,
decoded and summed as exact rationals. -/
def record2687ChunkBits047 : List Nat :=
  [0x3f84154eb6ce535c,
   0x3f827a1132e0d1b3,
   0x3f829773ae7733dd,
   0x3f825bb3eab7290c,
   0x3f81af10b5b1ca5c,
   0x3f80990eadd177e6,
   0x3f7e6711710aa991,
   0x3f7b926701fadb24,
   0x3f7b69eeef52d884,
   0x3f7b2e74b0c3d891,
   0x3f7a4ed62b2570bd,
   0x3f78cf5a63a2999f,
   0x3f76d10b551e961e,
   0x3f748b5985f37986,
   0x3f740a5890a93929,
   0x3f73f2a47484ca68,
   0x3f7365d231cbf758,
   0x3f7261ad3507ffcf,
   0x3f70fa42b7f5bb03,
   0x3f6ea8f3aa27eae0,
   0x3f6d13e1097140a0,
   0x3f6d04206c7c2104,
   0x3f6c57b7b839de0c,
   0x3f6afc56528b6d6e,
   0x3f6909015345c492,
   0x3f66aea637a18804,
   0x3f64e9f7bb73a5b8,
   0x3f64e9565a61fe7a,
   0x3f6483c5fb3b3158,
   0x3f63a01622b2df16,
   0x3f624a20d880d6de,
   0x3f60a184004cac71]

theorem record2687ChunkBits047Length :
    (record2687ChunkBits047).length = 32 := by
  decide

theorem record2687ChunkSum047 :
    ((record2687ChunkBits047).map binary64Value2674).sum =
      (380396348290250869 : ℚ) / 2305843009213693952 := by
  norm_num [record2687ChunkBits047, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1536 through 1567,
decoded and summed as exact rationals. -/
def record2687ChunkBits048 : List Nat :=
  [0x3f5e40bd6d1e0871,
   0x3f5ddc40ff8b2633,
   0x3f5d698704c57d22,
   0x3f5c446f94bb0ffe,
   0x3f5a76c65946cdf3,
   0x3f582863ecf18e2c,
   0x3f55b6536a7f2b6a,
   0x3f551e35fe55fcbd,
   0x3f54e0e74d63abe4,
   0x3f54281db2fdf6b0,
   0x3f52f525e6aa88cc,
   0x3f5160399e72fcdc,
   0x3f4f2433f3ba87b7,
   0x3f4d9ce56b5d2594,
   0x3f4d57d70c43af7d,
   0x3f4c73b60da8be7d,
   0x3f4ae1bbb7ab8fc7,
   0x3f48be088c66d503,
   0x3f463d673ca52611,
   0x3f448f9334f2bb86,
   0x3f446863dbbfe968,
   0x3f43ded63979a858,
   0x3f42dbd811ae05be,
   0x3f416ea513230e9e,
   0x3f3f716fd1688eb3,
   0x3f3cb283968d37f7,
   0x3f3c1652718e9c55,
   0x3f3b7463330e26fb,
   0x3f3a2c1ae4833bf7,
   0x3f384c18ca76e65f,
   0x3f35fdd67ceee843,
   0x3f33d55e959a99a6]

theorem record2687ChunkBits048Length :
    (record2687ChunkBits048).length = 32 := by
  decide

theorem record2687ChunkSum048 :
    ((record2687ChunkBits048).map binary64Value2674).sum =
      (546488613112766165 : ℚ) / 18446744073709551616 := by
  norm_num [record2687ChunkBits048, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1568 through 1599,
decoded and summed as exact rationals. -/
def record2687ChunkBits049 : List Nat :=
  [0x3f331f212a784163,
   0x3f32c1b1e0475465,
   0x3f31f52a66e789c9,
   0x3f30be574faf8fe7,
   0x3f2e6c5a88123851,
   0x3f2b25c6c252c097,
   0x3f29c7b2135e58c2,
   0x3f295607c9678786,
   0x3f285b90660c6a8a,
   0x3f26cf0e646fcbc9,
   0x3f24cd7758f61042,
   0x3f2287666d94beb2,
   0x3f212f7c4205a246,
   0x3f20e9400f6c875a,
   0x3f20528f53971bc7,
   0x3f1eb309e0195be0,
   0x3f1c1c3e35a3f8e9,
   0x3f191cc91ff88e39,
   0x3f170330ee9c607e,
   0x3f164da3d5b44cf5,
   0x3f159b679202ecfa,
   0x3f14676c559811c0,
   0x3f12c219e359bc9f,
   0x3f10cfbd9f9993b2,
   0x3f0e72c477470c25,
   0x3f0d0e5509e851cc,
   0x3f0c3d702d83dd44,
   0x3f0ac68b03ffee05,
   0x3f08b6fa48f29851,
   0x3f06398b55d6e9b9,
   0x3f03eb82e02312be,
   0x3f02b672d88ac445]

theorem record2687ChunkBits049Length :
    (record2687ChunkBits049).length = 32 := by
  decide

theorem record2687ChunkSum049 :
    ((record2687ChunkBits049).map binary64Value2674).sum =
      (612709341370666111 : ℚ) / 147573952589676412928 := by
  norm_num [record2687ChunkBits049, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1600 through 1631,
decoded and summed as exact rationals. -/
def record2687ChunkBits050 : List Nat :=
  [0x3f0236950a94f33a,
   0x3f0155fef857373b,
   0x3f0010c2dfa2c457,
   0x3efcfebd68ba4572,
   0x3ef9b9c3923363c9,
   0x3ef7ce7132c09a5d,
   0x3ef72d13d35f2fba,
   0x3ef6242a65f17b92,
   0x3ef499662e25f8df,
   0x3ef2a7c6728d4d98,
   0x3ef07ba225cd3efa,
   0x3eee5a5a693aaec6,
   0x3eed14ac2a2d301b,
   0x3eebe0deb346bd8a,
   0x3eea093ecf58360a,
   0x3ee7aa1a43af1d5f,
   0x3ee4f74d18362b29,
   0x3ee31440a1186f39,
   0x3ee1fd139ae27385,
   0x3ee14b466f69cc23,
   0x3ee0360434198274,
   0x3edd93378076e06b,
   0x3eda47617e8004dd,
   0x3ed7adebe9e8539f,
   0x3ed5f62d2a05526b,
   0x3ed5219081bf9085,
   0x3ed3e0bf3fcae107,
   0x3ed2327c887d4a69,
   0x3ed037ca523a6819,
   0x3eccf154a4bd8ecd,
   0x3eca71a169183161,
   0x3ec96a14f92370a2]

theorem record2687ChunkBits050Length :
    (record2687ChunkBits050).length = 32 := by
  decide

theorem record2687ChunkSum050 :
    ((record2687ChunkBits050).map binary64Value2674).sum =
      (15882817867049281 : ℚ) / 36893488147419103232 := by
  norm_num [record2687ChunkBits050, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1632 through 1663,
decoded and summed as exact rationals. -/
def record2687ChunkBits051 : List Nat :=
  [0x3ec7fcb147088e0e,
   0x3ec60925cf6e0966,
   0x3ec3b3167797e106,
   0x3ec167f1c2b40cc3,
   0x3ebfd0b99935a118,
   0x3ebe11b2492de725,
   0x3ebc77f0d5b6cc1d,
   0x3eba3dc4659062fc,
   0x3eb7883c487de625,
   0x3eb496add21d4d09,
   0x3eb2d3357851ee63,
   0x3eb17f49464514e9,
   0x3eb09abfaa8162df,
   0x3eaeb5dc0acca803,
   0x3eab9ffed81af722,
   0x3ea833a89d993d82,
   0x3ea5f2481a701b05,
   0x3ea40c0b395c5869,
   0x3ea3066c08535808,
   0x3ea1a5d92160f26d,
   0x3e9fd88d55f9132f,
   0x3e9bf782468e1f4b,
   0x3e99203f25311683,
   0x3e969b60b584fca1,
   0x3e95655c4502bbc0,
   0x3e93e76e07f34ce9,
   0x3e9202ed5ee815c0,
   0x3e8fb672395f4a69,
   0x3e8c39bc42701e71,
   0x3e8961758bcdd04a,
   0x3e8799a3ffc99fc0,
   0x3e86031a2fea45e7]

theorem record2687ChunkBits051Length :
    (record2687ChunkBits051).length = 32 := by
  decide

theorem record2687ChunkSum051 :
    ((record2687ChunkBits051).map binary64Value2674).sum =
      (1167740595836889673 : ℚ) / 37778931862957161709568 := by
  norm_num [record2687ChunkBits051, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1664 through 1695,
decoded and summed as exact rationals. -/
def record2687ChunkBits052 : List Nat :=
  [0x3e83f9a3e989d2de,
   0x3e81a0d7fd29e3eb,
   0x3e7f15e4df08719a,
   0x3e7bf118a3f22fdb,
   0x3e7987843097a9b8,
   0x3e77d9adf2ce206b,
   0x3e75b3628ac1ffdc,
   0x3e7332861812b8a7,
   0x3e70c460904da835,
   0x3e6e378f1db6b4b4,
   0x3e6b1a5723df86cb,
   0x3e694bd5234a6bf9,
   0x3e6712af120ced98,
   0x3e64757ba20fdbfe,
   0x3e61b371a1192822,
   0x3e5ff9e9bbb322b5,
   0x3e5c3da53ae523f0,
   0x3e5a3d1edf59c033,
   0x3e57fc6e98e8f215,
   0x3e5550c9aff13b28,
   0x3e526c29ed5ac423,
   0x3e5089f3f454b2f5,
   0x3e4d29e9c1b861fc,
   0x3e4a972d978bd64a,
   0x3e485af72e4204ae,
   0x3e45b02ca26320c8,
   0x3e42c650d3fdfa83,
   0x3e40b4cac126b560,
   0x3e3d6aff0df3df5f,
   0x3e3a5348a3f9808e,
   0x3e3820f781263c93,
   0x3e3586c14cbd5e44]

theorem record2687ChunkBits052Length :
    (record2687ChunkBits052).length = 32 := by
  decide

theorem record2687ChunkSum052 :
    ((record2687ChunkBits052).map binary64Value2674).sum =
      (852037137424061739 : ℚ) / 604462909807314587353088 := by
  norm_num [record2687ChunkBits052, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1696 through 1727,
decoded and summed as exact rationals. -/
def record2687ChunkBits053 : List Nat :=
  [0x3e32a9c0de7b7fdf,
   0x3e30759cd1365f9e,
   0x3e2d086ce938af25,
   0x3e297920b0ad75f7,
   0x3e274bbad67907fb,
   0x3e24d12f1166d704,
   0x3e2212d38a7b8d16,
   0x3e1f98432a43b060,
   0x3e1be8be5c131c48,
   0x3e1819033c6b9c95,
   0x3e15e45a23b22a56,
   0x3e1396d86c625a3d,
   0x3e11074f2a050912,
   0x3e0d8094e618ecb9,
   0x3e0a18eebdbe736e,
   0x3e067697fa965e3a,
   0x3e03ff728a139a5b,
   0x3e01e9bf1ea9d1d7,
   0x3dff2cd14f07f957,
   0x3dfac3c5a89b2c05,
   0x3df7b433b79eccf2,
   0x3df4595f40f3b57d,
   0x3df1c1425a6a83ae,
   0x3defc9f6906155d3,
   0x3debaefe3e2682cd,
   0x3de78e3bc6b108ad,
   0x3de4e1899cd14cd5,
   0x3de1efec36c9664e,
   0x3ddea4a1798eb5e4,
   0x3ddb53cc50a56772,
   0x3dd7cf4fb2680804,
   0x3dd424c137de239e]

theorem record2687ChunkBits053Length :
    (record2687ChunkBits053).length = 32 := by
  decide

theorem record2687ChunkSum053 :
    ((record2687ChunkBits053).map binary64Value2674).sum =
      (704263341242661365 : ℚ) / 19342813113834066795298816 := by
  norm_num [record2687ChunkBits053, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1728 through 1759,
decoded and summed as exact rationals. -/
def record2687ChunkBits054 : List Nat :=
  [0x3dd1cf88c2fceba1,
   0x3dce9cc5fd62bd26,
   0x3dc9b5fa459bc1e5,
   0x3dc6b8bd9597a5b4,
   0x3dc3ccc901e60d76,
   0x3dc0bff893db43e0,
   0x3dbd5e39758ca09a,
   0x3db93e03edfd9461,
   0x3db51921cf72eb55,
   0x3db23d6b0136bbce,
   0x3dafc8191c081b11,
   0x3daae047da87e8ad,
   0x3da75bf1e326106c,
   0x3da412f08104135d,
   0x3da0b547f6e0e92f,
   0x3d9c43d5a4efb225,
   0x3d98917366cb4389,
   0x3d94c2ed530629ad,
   0x3d91e37805be0c93,
   0x3d8eba69effc956b,
   0x3d898de116023db1,
   0x3d851f84361774e4,
   0x3d824103c479056d,
   0x3d7ed142b11802e9,
   0x3d7a52482008f575,
   0x3d76957df6c3de66,
   0x3d72c2468c59f96a,
   0x3d6e757ffea6283f,
   0x3d6a02e1fda80d59,
   0x3d65ec4a437c3412,
   0x3d628f4f8fefb714,
   0x3d5fccc95b1cdfed]

theorem record2687ChunkBits054Length :
    (record2687ChunkBits054).length = 32 := by
  decide

theorem record2687ChunkSum054 :
    ((record2687ChunkBits054).map binary64Value2674).sum =
      (9012424056703112745 : ℚ) / 19807040628566084398385987584 := by
  norm_num [record2687ChunkBits054, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1760 through 1791,
decoded and summed as exact rationals. -/
def record2687ChunkBits055 : List Nat :=
  [0x3d5a5f18d3e941ab,
   0x3d55434f89e2ff80,
   0x3d51ba37704c414b,
   0x3d4dd23439731425,
   0x3d4905929b180d8c,
   0x3d4563dbe7ab16c2,
   0x3d41b3908a0eb8e0,
   0x3d3c5f625c8ec381,
   0x3d37188dfb4f633d,
   0x3d33568719d68da7,
   0x3d30146bb9e879db,
   0x3d2b6a0e14c86b20,
   0x3d26a0535e464fa2,
   0x3d2214a7852c3357,
   0x3d1cb564808a4281,
   0x3d17d754b046bfbe,
   0x3d13a4aa38b0b935,
   0x3d10af367fc867ec,
   0x3d0b7308d381f6ce,
   0x3d05dc13d8360158,
   0x3d01057bdcdfc7db,
   0x3cfbd9bb7ce650da,
   0x3cf6bbc5c5745f07,
   0x3cf338ecdee5f60c,
   0x3cef7ef69fddda18,
   0x3ce8fb0bd191c4d4,
   0x3ce3462009302e4f,
   0x3cdeb7e4d9ecc447,
   0x3cd8d6284d9d4135,
   0x3cd4e283258759d4,
   0x3cd1068a032e02fb,
   0x3ccae0d1c41f5747]

theorem record2687ChunkBits055Length :
    (record2687ChunkBits055).length = 32 := by
  decide

theorem record2687ChunkSum055 :
    ((record2687ChunkBits055).map binary64Value2674).sum =
      (21947807338318254465 : ℚ) / 10141204801825835211973625643008 := by
  norm_num [record2687ChunkBits055, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1792 through 1823,
decoded and summed as exact rationals. -/
def record2687ChunkBits056 : List Nat :=
  [0x3cc491897169c1b2,
   0x3cbfee14f0643f2b,
   0x3cb983de7ef5d495,
   0x3cb54ff1d0f1610f,
   0x3cb145746b18b6b1,
   0x3cab1cf1cd9b21f7,
   0x3ca4a1508b03ad96,
   0x3c9f2aaaee76970f,
   0x3c989975cea6111a,
   0x3c94563e44a05a3c,
   0x3c905d7284bdefdc,
   0x3c89857867656bdd,
   0x3c834b000098cdd6,
   0x3c7c9200922741cf,
   0x3c762dea0bb110dd,
   0x3c722638488459be,
   0x3c6d1393b54c94c0,
   0x3c66972e74fbf157,
   0x3c610193bed1d1ad,
   0x3c58ea7c690043fa,
   0x3c52cf07b1f5aae8,
   0x3c4e806175decb89,
   0x3c4842f2b318900c,
   0x3c42b2316493ccbf,
   0x3c3be233b0b8bc8a,
   0x3c3425eb4bae381d,
   0x3c2d78483883962e,
   0x3c2797ee83db0c16,
   0x3c229d8f12058b3e,
   0x3c1c6f5f9090316a,
   0x3c14fd54aa7042b1,
   0x3c0df90e3eff9d5d]

theorem record2687ChunkBits056Length :
    (record2687ChunkBits056).length = 32 := by
  decide

theorem record2687ChunkSum056 :
    ((record2687ChunkBits056).map binary64Value2674).sum =
      (114056197792186560851 : ℚ) / 41538374868278621028243970633760768 := by
  norm_num [record2687ChunkBits056, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1824 through 1855,
decoded and summed as exact rationals. -/
def record2687ChunkBits057 : List Nat :=
  [0x3c053171f0125db3,
   0x3c00ae0db0506556,
   0x3bfa15f0c8a46a60,
   0x3bf3ba77ea5684e0,
   0x3becce6de49432e2,
   0x3be44eda050c5932,
   0x3bdbecf78f55c36c,
   0x3bd5641440067ce8,
   0x3bd08f6d7dfaf74f,
   0x3bc8c789b31785b3,
   0x3bc1e00b3127f447,
   0x3bb8dce35af2d1e2,
   0x3bb0c17451e09953,
   0x3ba8ab6e3a0aa8ee,
   0x3ba2e3129c159cb7,
   0x3b9becdfbab6dcd9,
   0x3b93e1b952b29a74,
   0x3b8b402e0edca6b3,
   0x3b8201af72110a93,
   0x3b7969848681be27,
   0x3b7329939db71032,
   0x3b6bf5ab208224c5,
   0x3b639ee88a309f8e,
   0x3b5a7796ab7d344a,
   0x3b512ca3fab221b6,
   0x3b472816b63564e0,
   0x3b411bb8236a2b22,
   0x3b3899003c447c7f,
   0x3b30fcf90b7eaaa6,
   0x3b2684f23d268e1a,
   0x3b1ca8f6b08762ef,
   0x3b128e9a977e7736]

theorem record2687ChunkBits057Length :
    (record2687ChunkBits057).length = 32 := by
  decide

theorem record2687ChunkSum057 :
    ((record2687ChunkBits057).map binary64Value2674).sum =
      (799326853522688221597 : ℚ) / 1361129467683753853853498429727072845824 := by
  norm_num [record2687ChunkBits057, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1856 through 1887,
decoded and summed as exact rationals. -/
def record2687ChunkBits058 : List Nat :=
  [0x3b0a8e1987940f46,
   0x3b02c785f65959a0,
   0x3af97c0adfb85008,
   0x3af091ccd9d4a303,
   0x3ae4a53e2327ba12,
   0x3ad9d4c72cfa8397,
   0x3ad1ab3fffd8fbbb,
   0x3ac889753981a956,
   0x3ac052f51cbedb52,
   0x3ab4c7d47725dfaa,
   0x3aa94c8dd2003c7a,
   0x3a9e9f3bfd5bc1ea,
   0x3a93f39a0868b0cd,
   0x3a8affe7364193c3,
   0x3a819245a251976d,
   0x3a75d88432d4b88f,
   0x3a69ecdc5a8884a6,
   0x3a5e7962e7fce2d1,
   0x3a52c8679bb08bc3,
   0x3a4891f545202f41,
   0x3a3f3385a668d275,
   0x3a32e3d35ae7389f,
   0x3a25ca9e198ec52e,
   0x3a18cd5d87ee4ade,
   0x3a0d0d6153b5c8ce,
   0x3a021c802e8bdaa6,
   0x39f65ebc127be843,
   0x39ea4b98fc3541f9,
   0x39dd63fa6b61252a,
   0x39d0235bc8dc98ed,
   0x39c20669519cce52,
   0x39b51e21eec32ff5]

theorem record2687ChunkBits058Length :
    (record2687ChunkBits058).length = 32 := by
  decide

theorem record2687ChunkSum058 :
    ((record2687ChunkBits058).map binary64Value2674).sum =
      (47952940407732214356973 : ℚ) / 5708990770823839524233143877797980545530986496 := by
  norm_num [record2687ChunkBits058, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1888 through 1919,
decoded and summed as exact rationals. -/
def record2687ChunkBits059 : List Nat :=
  [0x39a9479386932460,
   0x399cbd08bd7b4a19,
   0x398f005789e1e296,
   0x39805b46e3056ed9,
   0x397170fa6bf34a6f,
   0x39631a77e68ee6d4,
   0x3955e382a10dd6a7,
   0x3947f58a372ca4db,
   0x3938d496ba251257,
   0x39290d6b687fd3e2,
   0x3919944423169561,
   0x3909ef6b567a166e,
   0x38fc1baa1280ec1d,
   0x38ed784304323b4e,
   0x38dd2eb5c819091a,
   0x38cbfcdeedeca2f1,
   0x38bb32258f70bb99,
   0x38a995e91cfb479d,
   0x3899c2a1a704d1a9,
   0x3889b5f0b7083389,
   0x38782b8bcb521bfe,
   0x3865e1b08b552b8c,
   0x385416d0d1869114,
   0x3841864853bdc1dd,
   0x38301b74e51e579c,
   0x381e62583004c67d,
   0x380ae835f54a26b9,
   0x37f6cdc2a2e08bc6,
   0x37e39c15b12c4b95,
   0x37cfb23efca762a8,
   0x37ba5b93ce2e4d3c,
   0x37a705ad09a0133a]

theorem record2687ChunkBits059Length :
    (record2687ChunkBits059).length = 32 := by
  decide

theorem record2687ChunkSum059 :
    ((record2687ChunkBits059).map binary64Value2674).sum =
      (34040757437957944433406353 : ℚ) / 24519928653854221733733552434404946937899825954937634816 := by
  norm_num [record2687ChunkBits059, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1920 through 1951,
decoded and summed as exact rationals. -/
def record2687ChunkBits060 : List Nat :=
  [0x379306ed178253f0,
   0x377de420b2b8d005,
   0x3767d3a944110ab7,
   0x3751d06439652420,
   0x373a6327594b8875,
   0x3724f35a31f86dbf,
   0x370ff4b860397693,
   0x36f6fc45e3ce1d03,
   0x36e0c55f7cd84b8e,
   0x36c6e64ce1e35b5d,
   0x36ae1857ad173660,
   0x369529000985583e,
   0x367d600d16c9acdf,
   0x366310ed8135572e,
   0x3649140638760603,
   0x362ec66ff373a048,
   0x3611c3c7c05b3a45,
   0x35f58c8e776b0132,
   0x35dac47b3e8a9ba3,
   0x35becb197e6a2de2,
   0x35a1e94703373972,
   0x35835ec07050eb0d,
   0x3563736abb929569,
   0x3543f339198de889,
   0x352566617c2c0f49,
   0x35055eb91f8fdf4c,
   0x34e56fd7483d0586,
   0x34c3ef80dd883978,
   0x34a123ba862d6db6,
   0x347cd4668e9c4ac7,
   0x3459c9d4cc2840bf,
   0x3435cca3f39980a9]

theorem record2687ChunkBits060Length :
    (record2687ChunkBits060).length = 32 := by
  decide

theorem record2687ChunkSum060 :
    ((record2687ChunkBits060).map binary64Value2674).sum =
      (158531336928141658088870416034581 : ℚ) / 1766847064778384329583297500742918515827483896875618958121606201292619776 := by
  norm_num [record2687ChunkBits060, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1952 through 1983,
decoded and summed as exact rationals. -/
def record2687ChunkBits061 : List Nat :=
  [0x34123f2df10abd74,
   0x33ec4b6fdcdbae20,
   0x33c42b006fcfc74a,
   0x339b312b97468318,
   0x33735677dbefd71a,
   0x334ab23311cdc32d,
   0x3321f30411e79ecd,
   0x32f64dd594837a6d,
   0x32c94b32612068f4,
   0x329a5b2e067a6196,
   0x326c3fa5862d4dd8,
   0x323e6413ce270d24,
   0x320f3f29ee8b6782,
   0x31dd8d61ad9958d6,
   0x31a942f940d6d6a0,
   0x317377a9a79feeeb,
   0x313db5787cacf179,
   0x31070aaff8be85d0,
   0x30d0f8bbe6cb2d25,
   0x3096d2bd595b78db,
   0x305b61592e4a75e8,
   0x301d37a54320be90,
   0x2fdd3cdbad5c9eb4,
   0x2f9de11d6d731e7c,
   0x2f5ce22f749e03ed,
   0x2f192efb2202f731,
   0x2ed33d1801319d90,
   0x2e89a952da0ddd99,
   0x2e3e9bf7ad5d4421,
   0x2df225d917c4611c,
   0x2da4667acba56aa5,
   0x2d544d256feea66e]

theorem record2687ChunkBits061Length :
    (record2687ChunkBits061).length = 32 := by
  decide

theorem record2687ChunkSum061 :
    ((record2687ChunkBits061).map binary64Value2674).sum =
      (1029577095428806715409937654675180237933738743175 : ℚ) / 1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312 := by
  norm_num [record2687ChunkBits061, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 1984 through 2015,
decoded and summed as exact rationals. -/
def record2687ChunkBits062 : List Nat :=
  [0x2d0141d9337a017a,
   0x2ca8f025106cabca,
   0x2c4eaf8f03b012d0,
   0x2bf1d8000932d1c5,
   0x2b93a6efe3042aad,
   0x2b329c4e0ecbcd62,
   0x2acd0416ad79c270,
   0x2a627c3490688930,
   0x29f315f88c56f77a,
   0x29814862d4790450,
   0x290c8e9225142cfd,
   0x2893af224f894f89,
   0x28151fc60b7ee00d,
   0x27917229b917e598,
   0x2705e451fa7cf3da,
   0x26759c7fc5336b44,
   0x25e22ea3590c0156,
   0x25482ad5e03ccf7b,
   0x24a6e38761d3e172,
   0x23fe4ed19446031b,
   0x234b7752cb3b1819,
   0x22910c57298ff917,
   0x21cf5bd486c6de8e,
   0x21048cc074ff9e9b,
   0x2030999a79553251,
   0x1f4fd87d9081a42e,
   0x1e617c91dc758090,
   0x1dc934aa7568d540,
   0x1dc9200ce225a1c8,
   0x1dc90b802b5d3c5e,
   0x1dc8f70443453c5b,
   0x1dc8e2991c1e69cc]

theorem record2687ChunkBits062Length :
    (record2687ChunkBits062).length = 32 := by
  decide

theorem record2687ChunkSum062 :
    ((record2687ChunkBits062).map binary64Value2674).sum =
      (140479952169184262152939867986856387950962705928410441543217385392520565251038504432015757 : ℚ) / 2074757784440496479256203931845580575506223116121218449997828664845326405706454073199853524473551897144098943305650394591197575537705887653943437417056981843530590901700754761842688 := by
  norm_num [record2687ChunkBits062, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- Record 2687 cells 2016 through 2047,
decoded and summed as exact rationals. -/
def record2687ChunkBits063 : List Nat :=
  [0x1dc8ce3ea8350060,
   0x1dc8b9f4d9e033f8,
   0x1dc8a5bba382997f,
   0x1dc89192f789d1cc,
   0x1dc87d7ac86e80f2,
   0x1dc8697308b49014,
   0x1dc8557baaeab403,
   0x1dc84194a1aad452,
   0x1dc82dbddf99b7a0,
   0x1dc819f75766fb08,
   0x1dc80640fbcd52ef,
   0x1dc7f29abf921380,
   0x1dc7df0495859632,
   0x1dc7cb7e7082e754,
   0x1dc7b808436fbda8,
   0x1dc7a4a2013cba2b,
   0x1dc7914b9ce4f274,
   0x1dc77e05096e549e,
   0x1dc76ace39e95620,
   0x1dc757a72170eb94,
   0x1dc7448fb32ac76e,
   0x1dc73187e246e642,
   0x1dc71e8fa1fff114,
   0x1dc70ba6e59aed84,
   0x1dc6f8cda06735a4,
   0x1dc6e603c5beb5bf,
   0x1dc6d34949057a6f,
   0x1dc6c09e1daa1160,
   0x1dc6ae0237253ac0,
   0x1dc69b7588f9e133,
   0x1dc688f806b556a3,
   0x1dc67689a3eee426]

theorem record2687ChunkBits063Length :
    (record2687ChunkBits063).length = 32 := by
  decide

theorem record2687ChunkSum063 :
    ((record2687ChunkBits063).map binary64Value2674).sum =
      (106355220319114549 : ℚ) / 1037378892220248239628101965922790287753111558060609224998914332422663202853227036599926762236775948572049471652825197295598787768852943826971718708528490921765295450850377380921344 := by
  norm_num [record2687ChunkBits063, binary64Value2674,
    binary64ExponentBits2674, binary64Significand2674,
    binary64FractionBits2674, binary64Sign2674]

/-- The 2048-cell finite price ledger, grouped into certified chunks. -/
def record2687CellTotalBits : List Nat :=
  record2687ChunkBits000 ++
    record2687ChunkBits001 ++
    record2687ChunkBits002 ++
    record2687ChunkBits003 ++
    record2687ChunkBits004 ++
    record2687ChunkBits005 ++
    record2687ChunkBits006 ++
    record2687ChunkBits007 ++
    record2687ChunkBits008 ++
    record2687ChunkBits009 ++
    record2687ChunkBits010 ++
    record2687ChunkBits011 ++
    record2687ChunkBits012 ++
    record2687ChunkBits013 ++
    record2687ChunkBits014 ++
    record2687ChunkBits015 ++
    record2687ChunkBits016 ++
    record2687ChunkBits017 ++
    record2687ChunkBits018 ++
    record2687ChunkBits019 ++
    record2687ChunkBits020 ++
    record2687ChunkBits021 ++
    record2687ChunkBits022 ++
    record2687ChunkBits023 ++
    record2687ChunkBits024 ++
    record2687ChunkBits025 ++
    record2687ChunkBits026 ++
    record2687ChunkBits027 ++
    record2687ChunkBits028 ++
    record2687ChunkBits029 ++
    record2687ChunkBits030 ++
    record2687ChunkBits031 ++
    record2687ChunkBits032 ++
    record2687ChunkBits033 ++
    record2687ChunkBits034 ++
    record2687ChunkBits035 ++
    record2687ChunkBits036 ++
    record2687ChunkBits037 ++
    record2687ChunkBits038 ++
    record2687ChunkBits039 ++
    record2687ChunkBits040 ++
    record2687ChunkBits041 ++
    record2687ChunkBits042 ++
    record2687ChunkBits043 ++
    record2687ChunkBits044 ++
    record2687ChunkBits045 ++
    record2687ChunkBits046 ++
    record2687ChunkBits047 ++
    record2687ChunkBits048 ++
    record2687ChunkBits049 ++
    record2687ChunkBits050 ++
    record2687ChunkBits051 ++
    record2687ChunkBits052 ++
    record2687ChunkBits053 ++
    record2687ChunkBits054 ++
    record2687ChunkBits055 ++
    record2687ChunkBits056 ++
    record2687ChunkBits057 ++
    record2687ChunkBits058 ++
    record2687ChunkBits059 ++
    record2687ChunkBits060 ++
    record2687ChunkBits061 ++
    record2687ChunkBits062 ++
    record2687ChunkBits063

theorem record2687GridCellCount :
    record2687CellTotalBits.length = 2048 := by
  simp only [record2687CellTotalBits, List.length_append, record2687ChunkBits000Length, record2687ChunkBits001Length, record2687ChunkBits002Length, record2687ChunkBits003Length, record2687ChunkBits004Length, record2687ChunkBits005Length, record2687ChunkBits006Length, record2687ChunkBits007Length, record2687ChunkBits008Length, record2687ChunkBits009Length, record2687ChunkBits010Length, record2687ChunkBits011Length, record2687ChunkBits012Length, record2687ChunkBits013Length, record2687ChunkBits014Length, record2687ChunkBits015Length, record2687ChunkBits016Length, record2687ChunkBits017Length, record2687ChunkBits018Length, record2687ChunkBits019Length, record2687ChunkBits020Length, record2687ChunkBits021Length, record2687ChunkBits022Length, record2687ChunkBits023Length, record2687ChunkBits024Length, record2687ChunkBits025Length, record2687ChunkBits026Length, record2687ChunkBits027Length, record2687ChunkBits028Length, record2687ChunkBits029Length, record2687ChunkBits030Length, record2687ChunkBits031Length, record2687ChunkBits032Length, record2687ChunkBits033Length, record2687ChunkBits034Length, record2687ChunkBits035Length, record2687ChunkBits036Length, record2687ChunkBits037Length, record2687ChunkBits038Length, record2687ChunkBits039Length, record2687ChunkBits040Length, record2687ChunkBits041Length, record2687ChunkBits042Length, record2687ChunkBits043Length, record2687ChunkBits044Length, record2687ChunkBits045Length, record2687ChunkBits046Length, record2687ChunkBits047Length, record2687ChunkBits048Length, record2687ChunkBits049Length, record2687ChunkBits050Length, record2687ChunkBits051Length, record2687ChunkBits052Length, record2687ChunkBits053Length, record2687ChunkBits054Length, record2687ChunkBits055Length, record2687ChunkBits056Length, record2687ChunkBits057Length, record2687ChunkBits058Length, record2687ChunkBits059Length, record2687ChunkBits060Length, record2687ChunkBits061Length, record2687ChunkBits062Length, record2687ChunkBits063Length]

theorem record2687GridChargeExact :
    (record2687CellTotalBits.map binary64Value2674).sum =
      (58534495695895061432762086474614127713225914260257004228403083853930265073908046153975589962258299470630303834986199438973953061983264310180345140374619699415339673143319231982165557258743 : ℚ) / 2074757784440496479256203931845580575506223116121218449997828664845326405706454073199853524473551897144098943305650394591197575537705887653943437417056981843530590901700754761842688 := by
  simp only [record2687CellTotalBits, List.map_append,
    List.sum_append, record2687ChunkSum000, record2687ChunkSum001, record2687ChunkSum002, record2687ChunkSum003, record2687ChunkSum004, record2687ChunkSum005, record2687ChunkSum006, record2687ChunkSum007, record2687ChunkSum008, record2687ChunkSum009, record2687ChunkSum010, record2687ChunkSum011, record2687ChunkSum012, record2687ChunkSum013, record2687ChunkSum014, record2687ChunkSum015, record2687ChunkSum016, record2687ChunkSum017, record2687ChunkSum018, record2687ChunkSum019, record2687ChunkSum020, record2687ChunkSum021, record2687ChunkSum022, record2687ChunkSum023, record2687ChunkSum024, record2687ChunkSum025, record2687ChunkSum026, record2687ChunkSum027, record2687ChunkSum028, record2687ChunkSum029, record2687ChunkSum030, record2687ChunkSum031, record2687ChunkSum032, record2687ChunkSum033, record2687ChunkSum034, record2687ChunkSum035, record2687ChunkSum036, record2687ChunkSum037, record2687ChunkSum038, record2687ChunkSum039, record2687ChunkSum040, record2687ChunkSum041, record2687ChunkSum042, record2687ChunkSum043, record2687ChunkSum044, record2687ChunkSum045, record2687ChunkSum046, record2687ChunkSum047, record2687ChunkSum048, record2687ChunkSum049, record2687ChunkSum050, record2687ChunkSum051, record2687ChunkSum052, record2687ChunkSum053, record2687ChunkSum054, record2687ChunkSum055, record2687ChunkSum056, record2687ChunkSum057, record2687ChunkSum058, record2687ChunkSum059, record2687ChunkSum060, record2687ChunkSum061, record2687ChunkSum062, record2687ChunkSum063]
  norm_num

theorem record2687GridChargeBelowKnownError :
    (((record2687CellTotalBits.map binary64Value2674).sum : ℚ) : ℝ) <
      ConnesWeilRH.Source.C1RouteAItem5Arithmetic.knownError2109 := by
  rw [record2687GridChargeExact]
  norm_num [ConnesWeilRH.Source.C1RouteAItem5Arithmetic.knownError2109]

end ConnesWeilRH.Dev
