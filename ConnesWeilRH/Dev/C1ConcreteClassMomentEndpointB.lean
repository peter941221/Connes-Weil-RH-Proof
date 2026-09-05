/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ConcreteClassMomentBase

/-!
# Record 1145 RED-9: isolated endpointB rational value certificates.
Generated; RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ConcreteClassMomentCertificate

open scoped BigOperators

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option exponentiation.threshold 1000
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000000

-- per-index value theorems: `k + 2` equation lemmas do not match
-- closed Nat literals under simp, so each index is grounded
-- through the step theorem with an explicit `n + 1 + 1` bridge.

theorem endpointBQ_step (n : ℕ) :
    endpointBQ (n + 1 + 1) = ((2 * (n : ℚ) + 1) / (2 * ((n : ℚ) + 1))) * endpointBQ (n + 1) := by
  rw [endpointBQ]

theorem endpointB_at_0 : endpointBQ 0 =
    0 := by
  norm_num (config := { maxSteps := 2000000000 })
    [endpointBQ, rationalRadiusQ]

theorem endpointB_at_1 : endpointBQ 1 =
    1 := by
  rfl

theorem endpointB_at_2 : endpointBQ 2 =
    (1 / 2) := by
  show endpointBQ (0 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_1]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_3 : endpointBQ 3 =
    (3 / 8) := by
  show endpointBQ (1 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_2]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_4 : endpointBQ 4 =
    (5 / 16) := by
  show endpointBQ (2 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_3]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_5 : endpointBQ 5 =
    (35 / 128) := by
  show endpointBQ (3 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_4]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_6 : endpointBQ 6 =
    (63 / 256) := by
  show endpointBQ (4 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_5]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_7 : endpointBQ 7 =
    (231 / 1024) := by
  show endpointBQ (5 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_6]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_8 : endpointBQ 8 =
    (429 / 2048) := by
  show endpointBQ (6 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_7]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_9 : endpointBQ 9 =
    (6435 / 32768) := by
  show endpointBQ (7 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_8]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_10 : endpointBQ 10 =
    (12155 / 65536) := by
  show endpointBQ (8 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_9]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_11 : endpointBQ 11 =
    (46189 / 262144) := by
  show endpointBQ (9 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_10]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_12 : endpointBQ 12 =
    (88179 / 524288) := by
  show endpointBQ (10 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_11]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_13 : endpointBQ 13 =
    (676039 / 4194304) := by
  show endpointBQ (11 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_12]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_14 : endpointBQ 14 =
    (1300075 / 8388608) := by
  show endpointBQ (12 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_13]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_15 : endpointBQ 15 =
    (5014575 / 33554432) := by
  show endpointBQ (13 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_14]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_16 : endpointBQ 16 =
    (9694845 / 67108864) := by
  show endpointBQ (14 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_15]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_17 : endpointBQ 17 =
    (300540195 / 2147483648) := by
  show endpointBQ (15 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_16]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_18 : endpointBQ 18 =
    (583401555 / 4294967296) := by
  show endpointBQ (16 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_17]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_19 : endpointBQ 19 =
    (2268783825 / 17179869184) := by
  show endpointBQ (17 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_18]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_20 : endpointBQ 20 =
    (4418157975 / 34359738368) := by
  show endpointBQ (18 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_19]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_21 : endpointBQ 21 =
    (34461632205 / 274877906944) := by
  show endpointBQ (19 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_20]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_22 : endpointBQ 22 =
    (67282234305 / 549755813888) := by
  show endpointBQ (20 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_21]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_23 : endpointBQ 23 =
    (263012370465 / 2199023255552) := by
  show endpointBQ (21 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_22]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_24 : endpointBQ 24 =
    (514589420475 / 4398046511104) := by
  show endpointBQ (22 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_23]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_25 : endpointBQ 25 =
    (8061900920775 / 70368744177664) := by
  show endpointBQ (23 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_24]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_26 : endpointBQ 26 =
    (15801325804719 / 140737488355328) := by
  show endpointBQ (24 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_25]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_27 : endpointBQ 27 =
    (61989816618513 / 562949953421312) := by
  show endpointBQ (25 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_26]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_28 : endpointBQ 28 =
    (121683714103007 / 1125899906842624) := by
  show endpointBQ (26 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_27]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_29 : endpointBQ 29 =
    (956086325095055 / 9007199254740992) := by
  show endpointBQ (27 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_28]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_30 : endpointBQ 30 =
    (1879204156221315 / 18014398509481984) := by
  show endpointBQ (28 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_29]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_31 : endpointBQ 31 =
    (7391536347803839 / 72057594037927936) := by
  show endpointBQ (29 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_30]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_32 : endpointBQ 32 =
    (14544636039226909 / 144115188075855872) := by
  show endpointBQ (30 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_31]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_33 : endpointBQ 33 =
    (916312070471295267 / 9223372036854775808) := by
  show endpointBQ (31 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_32]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_34 : endpointBQ 34 =
    (1804857108504066435 / 18446744073709551616) := by
  show endpointBQ (32 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_33]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_35 : endpointBQ 35 =
    (7113260368810144185 / 73786976294838206464) := by
  show endpointBQ (33 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_34]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_36 : endpointBQ 36 =
    (14023284727082855679 / 147573952589676412928) := by
  show endpointBQ (34 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_35]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_37 : endpointBQ 37 =
    (110628135069209194801 / 1180591620717411303424) := by
  show endpointBQ (35 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_36]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_38 : endpointBQ 38 =
    (218266320541953276229 / 2361183241434822606848) := by
  show endpointBQ (36 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_37]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_39 : endpointBQ 39 =
    (861577581086657669325 / 9444732965739290427392) := by
  show endpointBQ (37 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_38]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_40 : endpointBQ 40 =
    (1701063429324939500975 / 18889465931478580854784) := by
  show endpointBQ (38 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_39]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_41 : endpointBQ 41 =
    (26876802183334044115405 / 302231454903657293676544) := by
  show endpointBQ (39 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_40]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_42 : endpointBQ 42 =
    (53098072606098965203605 / 604462909807314587353088) := by
  show endpointBQ (40 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_41]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_43 : endpointBQ 43 =
    (209863810776486386280915 / 2417851639229258349412352) := by
  show endpointBQ (41 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_42]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_44 : endpointBQ 44 =
    (414847067813984717066925 / 4835703278458516698824704) := by
  show endpointBQ (42 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_43]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_45 : endpointBQ 45 =
    (3281063172710606398620225 / 38685626227668133590597632) := by
  show endpointBQ (43 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_44]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_46 : endpointBQ 46 =
    (6489213830472088210604445 / 77371252455336267181195264) := by
  show endpointBQ (44 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_45]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_47 : endpointBQ 47 =
    (25674715590128696833261065 / 309485009821345068724781056) := by
  show endpointBQ (45 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_46]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_48 : endpointBQ 48 =
    (50803160635786570329644235 / 618970019642690137449562112) := by
  show endpointBQ (46 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_47]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_49 : endpointBQ 49 =
    (1608766753466574727105400775 / 19807040628566084398385987584) := by
  show endpointBQ (47 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_48]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_50 : endpointBQ 50 =
    (3184701532372607112841303575 / 39614081257132168796771975168) := by
  show endpointBQ (48 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_49]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_51 : endpointBQ 51 =
    (12611418068195524166851562157 / 158456325028528675187087900672) := by
  show endpointBQ (49 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_50]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_52 : endpointBQ 52 =
    (24975553429171528252000152507 / 316912650057057350374175801344) := by
  show endpointBQ (50 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_51]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_53 : endpointBQ 53 =
    (197883231015743646919693516017 / 2535301200456458802993406410752) := by
  show endpointBQ (51 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_52]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_54 : endpointBQ 54 =
    (392032816163265715595619229845 / 5070602400912917605986812821504) := by
  show endpointBQ (52 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_53]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_55 : endpointBQ 55 =
    (1553611530721090058101157688645 / 20282409603651670423947251286016) := by
  show endpointBQ (53 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_54]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_56 : endpointBQ 56 =
    (3078975579065433024236839782951 / 40564819207303340847894502572032) := by
  show endpointBQ (54 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_55]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_57 : endpointBQ 57 =
    (48823755610894723670041316558223 / 649037107316853453566312041152512) := by
  show endpointBQ (55 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_56]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_58 : endpointBQ 58 =
    (96790954105808838152888925808407 / 1298074214633706907132624082305024) := by
  show endpointBQ (56 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_57]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_59 : endpointBQ 59 =
    (383826197316138496123525050619545 / 5192296858534827628530496329220096) := by
  show endpointBQ (57 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_58]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_60 : endpointBQ 60 =
    (761146865864206848244956456313335 / 10384593717069655257060992658440192) := by
  show endpointBQ (58 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_59]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_61 : endpointBQ 61 =
    (6038431802522707662743321220085791 / 83076749736557242056487941267521536) := by
  show endpointBQ (59 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_60]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_62 : endpointBQ 62 =
    (11977872919758157822818719141481651 / 166153499473114484112975882535043072) := by
  show endpointBQ (60 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_61]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_63 : endpointBQ 63 =
    (47525108681621077813119434012975583 / 664613997892457936451903530140172288) := by
  show endpointBQ (61 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_62]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_64 : endpointBQ 64 =
    (94295850558771979787935384946380125 / 1329227995784915872903807060280344576) := by
  show endpointBQ (62 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_63]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_65 : endpointBQ 65 =
    (11975573020964041433067793888190275875 / 170141183460469231731687303715884105728) := by
  show endpointBQ (63 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_64]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_66 : endpointBQ 66 =
    (23766906456990174536396083255023778275 / 340282366920938463463374607431768211456) := by
  show endpointBQ (64 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_65]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_67 : endpointBQ 67 =
    (94347416541385238311148088072973180425 / 1361129467683753853853498429727072845824) := by
  show endpointBQ (65 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_66]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_68 : endpointBQ 68 =
    (187286662686630398438547697219484074575 / 2722258935367507707706996859454145691648) := by
  show endpointBQ (66 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_67]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_69 : endpointBQ 69 =
    (1487276438982064928776702301448844121625 / 21778071482940061661655974875633165533184) := by
  show endpointBQ (67 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_68]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_70 : endpointBQ 70 =
    (2952998146964389786121858192731762966125 / 43556142965880123323311949751266331066368) := by
  show endpointBQ (68 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_69]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_71 : endpointBQ 71 =
    (11727621212230005150598236822563287208325 / 174224571863520493293247799005065324265472) := by
  show endpointBQ (69 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_70]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_72 : endpointBQ 72 =
    (23290064660907475017385230872977795723575 / 348449143727040986586495598010130648530944) := by
  show endpointBQ (70 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_71]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_73 : endpointBQ 73 =
    (370053249612196547498454223870647198719025 / 5575186299632655785383929568162090376495104) := by
  show endpointBQ (71 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_72]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_74 : endpointBQ 74 =
    (735037276626965745031176198099230737181625 / 11150372599265311570767859136324180752990208) := by
  show endpointBQ (72 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_73]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_75 : endpointBQ 75 =
    (2920283234166593635664402732988835631505375 / 44601490397061246283071436545296723011960832) := by
  show endpointBQ (73 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_74]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_76 : endpointBQ 76 =
    (5801629358544299356186613429537820121257345 / 89202980794122492566142873090593446023921664) := by
  show endpointBQ (74 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_75]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_77 : endpointBQ 77 =
    (46107685954746800146535717255800570437361005 / 713623846352979940529142984724747568191373312) := by
  show endpointBQ (75 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_76]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_78 : endpointBQ 78 =
    (91616570793198187304155386235551782817093945 / 1427247692705959881058285969449495136382746624) := by
  show endpointBQ (76 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_77]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_79 : endpointBQ 79 =
    (364117140331941513644720124782321188119219525 / 5708990770823839524233143877797980545530986496) := by
  show endpointBQ (77 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_78]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_80 : endpointBQ 80 =
    (723625202938162248635709615073726918160980575 / 11417981541647679048466287755595961091061972992) := by
  show endpointBQ (78 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_79]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_81 : endpointBQ 81 =
    (23011281453433559506615565759344515997519182285 / 365375409332725729550921208179070754913983135744) := by
  show endpointBQ (79 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_80]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_82 : endpointBQ 82 =
    (45738473012380284945248223299437865130871461085 / 730750818665451459101842416358141509827966271488) := by
  show endpointBQ (80 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_81]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_83 : endpointBQ 83 =
    (181838319537024059660377082873374927227610930655 / 2923003274661805836407369665432566039311865085952) := by
  show endpointBQ (81 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_82]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_84 : endpointBQ 84 =
    (361485815947096022216412273182010397500672332025 / 5846006549323611672814739330865132078623730171904) := by
  show endpointBQ (82 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_83]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_85 : endpointBQ 85 =
    (2874672917293573129054326172447416018219632354675 / 46768052394588893382517914646921056628989841375232) := by
  show endpointBQ (83 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_84]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_86 : endpointBQ 86 =
    (5715526153207221868355072036983685965636680799295 / 93536104789177786765035829293842113257979682750464) := by
  show endpointBQ (84 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_85]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_87 : endpointBQ 87 =
    (22729185399963603243923658565679309305206335271615 / 374144419156711147060143317175368453031918731001856) := by
  show endpointBQ (85 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_86]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_88 : endpointBQ 88 =
    (45197115795329923691940148642097936894260873586085 / 748288838313422294120286634350736906063837462003712) := by
  show endpointBQ (86 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_87]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_89 : endpointBQ 89 =
    (719045024016612422371775092033376268772332079778625 / 11972621413014756705924586149611790497021399392059392) := by
  show endpointBQ (87 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_88]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_90 : endpointBQ 90 =
    (1430010890460004480447238104380984264861828967649625 / 23945242826029513411849172299223580994042798784118784) := by
  show endpointBQ (88 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_89]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_91 : endpointBQ 91 =
    (5688265542052017822223458237426581853561497449095175 / 95780971304118053647396689196894323976171195136475136) := by
  show endpointBQ (89 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_90]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_92 : endpointBQ 92 =
    (11314022671554013470576329021694629840600341080068425 / 191561942608236107294793378393788647952342390272950272) := by
  show endpointBQ (90 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_91]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_93 : endpointBQ 93 =
    (90020267343234107178933400476961620036080974680544425 / 1532495540865888858358347027150309183618739122183602176) := by
  show endpointBQ (91 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_92]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_94 : endpointBQ 94 =
    (179072574822562471269921280518687093620161078665599125 / 3064991081731777716716694054300618367237478244367204352) := by
  show endpointBQ (92 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_93]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_95 : endpointBQ 95 =
    (712480244506791109095218711850946521424896206605681625 / 12259964326927110866866776217202473468949912977468817408) := by
  show endpointBQ (93 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_94]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_96 : endpointBQ 96 =
    (1417460696966142311778908805682409395255846137352356075 / 24519928653854221733733552434404946937899825954937634816) := by
  show endpointBQ (94 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_95]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_97 : endpointBQ 97 =
    (90244997706844393849923860628446731497955537411433336775 / 1569275433846670190958947355801916604025588861116008628224) := by
  show endpointBQ (95 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_96]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_98 : endpointBQ 98 =
    (179559634612587299103456753621548651330983698148521999975 / 3138550867693340381917894711603833208051177722232017256448) := by
  show endpointBQ (96 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_97]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_99 : endpointBQ 99 =
    (714574056111316802554572795024530347133506553856363061125 / 12554203470773361527671578846415332832204710888928069025792) := by
  show endpointBQ (97 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_98]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_100 : endpointBQ 100 =
    (1421930192463933435386372127473055337225260516259631545875 / 25108406941546723055343157692830665664409421777856138051584) := by
  show endpointBQ (98 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_99]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_101 : endpointBQ 101 =
    (11318564332012910145675522134685520484313073709426667105165 / 200867255532373784442745261542645325315275374222849104412672) := by
  show endpointBQ (99 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_100]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_102 : endpointBQ 102 =
    (22525063670639553854265148010611778389573542728660990971665 / 401734511064747568885490523085290650630550748445698208825344) := by
  show endpointBQ (100 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_101]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_103 : endpointBQ 103 =
    (89658586767447635929722059728513549276145670076827081710745 / 1606938044258990275541962092341162602522202993782792835301376) := by
  show endpointBQ (101 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_102]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_104 : endpointBQ 104 =
    (178446701818706459860126429556750267976794780249995648065075 / 3213876088517980551083924184682325205044405987565585670602752) := by
  show endpointBQ (102 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_103]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_105 : endpointBQ 105 =
    (2841420559728633630080474686019023497784347654749930703805425 / 51422017416287688817342786954917203280710495801049370729644032) := by
  show endpointBQ (103 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_104]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_106 : endpointBQ 106 =
    (5655779971269375511303040089314056295589796760407004924717465 / 102844034832575377634685573909834406561420991602098741459288064) := by
  show endpointBQ (104 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_105]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_107 : endpointBQ 107 =
    (22516407055430910054432857714061620346593341819733547907837455 / 411376139330301510538742295639337626245683966408394965837152256) := by
  show endpointBQ (105 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_106]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_108 : endpointBQ 108 =
    (44822380400063400388730828907431076017050297267320053311863345 / 822752278660603021077484591278675252491367932816789931674304512) := by
  show endpointBQ (106 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_107]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_109 : endpointBQ 109 =
    (356918955037541891984338082040654864580215330091622646742615525 / 6582018229284824168619876730229402019930943462534319453394436096) := by
  show endpointBQ (107 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_108]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_110 : endpointBQ 110 =
    (710563424249051289546801502778184455173456207613597379294931825 / 13164036458569648337239753460458804039861886925068638906788872192) := by
  show endpointBQ (108 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_109]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_111 : endpointBQ 111 =
    (2829334362009858771104536892880407194236125626679596837556183085 / 52656145834278593348959013841835216159447547700274555627155488768) := by
  show endpointBQ (109 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_110]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_112 : endpointBQ 112 =
    (5633179225262871967694618498437567476812466337803521631530778935 / 105312291668557186697918027683670432318895095400549111254310977536) := by
  show endpointBQ (110 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_111]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_113 : endpointBQ 113 =
    (179456995319088635542271417878796792475597141904312189118766243215 / 3369993333393829974333376885877453834204643052817571560137951281152) := by
  show endpointBQ (111 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_112]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_114 : endpointBQ 114 =
    (357325875635353477849655478077250250504507583437789757094888537375 / 6739986666787659948666753771754907668409286105635143120275902562304) := by
  show endpointBQ (112 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_113]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_115 : endpointBQ 115 =
    (1423034627530267359155645500412908892360056516497864471237538561125 / 26959946667150639794667015087019630673637144422540572481103610249216) := by
  show endpointBQ (113 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_114]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_116 : endpointBQ 116 =
    (2833695040908097610840372344300488142177851671982704034029533308675 / 53919893334301279589334030174039261347274288845081144962207220498432) := by
  show endpointBQ (114 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_115]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_117 : endpointBQ 117 =
    (22571846705164501658762965914945267615278749525103607995200765320825 / 431359146674410236714672241392314090778194310760649159697657763987456) := by
  show endpointBQ (115 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_116]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_118 : endpointBQ 118 =
    (44950771643618195611040778275061943199657680678197783443434002732925 / 862718293348820473429344482784628181556388621521298319395315527974912) := by
  show endpointBQ (116 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_117]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_119 : endpointBQ 119 =
    (179041209088987728281264116858297570371517880667397951003508315970125 / 3450873173395281893717377931138512726225554486085193277581262111899648) := by
  show endpointBQ (117 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_118]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_120 : endpointBQ 120 =
    (356577870202437744560164669709382556118065022841792557880936730125375 / 6901746346790563787434755862277025452451108972170386555162524223799296) := by
  show endpointBQ (118 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_119]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_121 : endpointBQ 121 =
    (5681474065225508063325290404036162060814502697279228088902925233330975 / 110427941548649020598956093796432407239217743554726184882600387580788736) := by
  show endpointBQ (119 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_120]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_122 : endpointBQ 122 =
    (11315993799333449944309049482419132699638802892928049334095908935807975 / 220855883097298041197912187592864814478435487109452369765200775161577472) := by
  show endpointBQ (120 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_121]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_123 : endpointBQ 123 =
    (45078467102262759614214738102095889278889001688221573576808292973792425 / 883423532389192164791648750371459257913741948437809479060803100646309888) := by
  show endpointBQ (121 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_122]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_124 : endpointBQ 124 =
    (89790442602068098418557811666776364823803296045644597774943347793326375 / 1766847064778384329583297500742918515827483896875618958121606201292619776) := by
  show endpointBQ (122 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_123]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_125 : endpointBQ 125 =
    (715427074926155493851089660699798777789658520105619859690677642095213375 / 14134776518227074636666380005943348126619871175004951664972849610340958208) := by
  show endpointBQ (123 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_124]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_126 : endpointBQ 126 =
    (1425130733252901743751370604113999165356999772050394760503829863053665043 / 28269553036454149273332760011886696253239742350009903329945699220681916416) := by
  show endpointBQ (124 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_125]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_127 : endpointBQ 127 =
    (5677901810261560915580857486231964928644554647375382299785099930578887711 / 113078212145816597093331040047546785012958969400039613319782796882727665664) := by
  show endpointBQ (125 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_126]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_128 : endpointBQ 128 =
    (11311095732253345760960290897769189975961199415637572612957718759342193629 / 226156424291633194186662080095093570025917938800079226639565593765455331328) := by
  show endpointBQ (126 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_127]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_129 : endpointBQ 129 =
    (2884329411724603169044874178931143443870105850987581016304218283632259375395 / 57896044618658097711785492504343953926634992332820282019728792003956564819968) := by
  show endpointBQ (127 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_128]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_130 : endpointBQ 130 =
    (5746299680722659026701803596785301279648195377548901714652589913903028368035 / 115792089237316195423570985008687907853269984665640564039457584007913129639936) := by
  show endpointBQ (128 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_129]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_131 : endpointBQ 131 =
    (22896794112417979814088725101036815868136655427464085293769550580013605343401 / 463168356949264781694283940034751631413079938662562256157830336031652518559744) := by
  show endpointBQ (129 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_130]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_132 : endpointBQ 132 =
    (45618803536954906347153872147867243828882954706626918028044677109798099195631 / 926336713898529563388567880069503262826159877325124512315660672063305037119488) := by
  show endpointBQ (130 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_131]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_133 : endpointBQ 133 =
    (363568040309670920281862678026941973545339911752814528526537881208390911771241 / 7410693711188236507108543040556026102609279018600996098525285376506440296955904) := by
  show endpointBQ (131 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_132]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_134 : endpointBQ 134 =
    (724402486331299202065365486294282879620414109883427444056635627971605952025405 / 14821387422376473014217086081112052205218558037201992197050570753012880593911808) := by
  show endpointBQ (132 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_133]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_135 : endpointBQ 135 =
    (2886797967917266969424665445381694460576874139386195933777936009976399838668405 / 59285549689505892056868344324448208820874232148807968788202283012051522375647232) := by
  show endpointBQ (133 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_134]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_136 : endpointBQ 136 =
    (5752212247183294924261000035612413406630956618480642268046405827286307826680007 / 118571099379011784113736688648896417641748464297615937576404566024103044751294464) := by
  show endpointBQ (134 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_135]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_137 : endpointBQ 137 =
    (91697030528627819086748882920644943129234661388720826743563292893799377707663641 / 1897137590064188545819787018382342682267975428761855001222473056385648716020711424) := by
  show endpointBQ (135 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_136]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_138 : endpointBQ 138 =
    (182724739666535727085273321440409266235628193862195516065640722335819197913811489 / 3794275180128377091639574036764685364535950857523710002444946112771297432041422848) := by
  show endpointBQ (136 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_137]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_139 : endpointBQ 139 =
    (728250774033294564470292223132065916156489178436286477073205777425366368497074775 / 15177100720513508366558296147058741458143803430094840009779784451085189728165691392) := by
  show endpointBQ (137 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_138]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_140 : endpointBQ 140 =
    (1451262333864910750778927667680447904858615125373031324814949642782924345853882825 / 30354201441027016733116592294117482916287606860189680019559568902170379456331382784) := by
  show endpointBQ (138 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_139]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_141 : endpointBQ 141 =
    (11568634032808859984780594836652713298730103427973592560667741438183882642663808805 / 242833611528216133864932738352939863330300854881517440156476551217363035650651062272) := by
  show endpointBQ (139 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_140]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_142 : endpointBQ 142 =
    (23055221015739642948392532972336258418036589101138861769841385419359368954528583505 / 485667223056432267729865476705879726660601709763034880312953102434726071301302124544) := by
  show endpointBQ (140 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_141]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_143 : endpointBQ 143 =
    (91896162640201675414015307481283959609920488952426730716410029206742273438473086365 / 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176) := by
  show endpointBQ (141 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_142]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_144 : endpointBQ 144 =
    (183149694772429912538422116308852646775016359100990337441796212055395440069684123175 / 3885337784451458141838923813647037813284813678104279042503624819477808570410416996352) := by
  show endpointBQ (142 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_143]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_145 : endpointBQ 145 =
    (5840440266631931655391905264515634402714410562442691871755056984433165699999927039025 / 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264) := by
  show endpointBQ (143 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_144]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_146 : endpointBQ 146 =
    (11640601634873298264884556009965643740582514845144399661635941162077137153792958029505 / 248661618204893321077691124073410420050228075398673858720231988446579748506266687766528) := by
  show endpointBQ (144 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_145]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_147 : endpointBQ 147 =
    (46402946243125065686046654779452086691911120821055072623781628468006122078818503925835 / 994646472819573284310764496293641680200912301594695434880927953786318994025066751066112) := by
  show endpointBQ (145 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_146]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_148 : endpointBQ 148 =
    (92490226185276491469467141839316063950543934697749226386176987354597236524447766328365 / 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224) := by
  show endpointBQ (146 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_147]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_149 : endpointBQ 149 =
    (737422073639366621175481266016168617984066506373946534700600304583950939857083542347775 / 15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792) := by
  show endpointBQ (147 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_148]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_150 : endpointBQ 150 =
    (1469895005844911989859851919508738788867568808007128327557572419204251202265461826022075 / 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584) := by
  show endpointBQ (148 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_149]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_151 : endpointBQ 151 =
    (5859981423301715799574609652441505304952040981255084932529522044560948126364974479741339 / 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336) := by
  show endpointBQ (149 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_150]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_152 : endpointBQ 152 =
    (11681155022608055997827533148244325144308373081839606388684676393462552225403028598689689 / 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672) := by
  show endpointBQ (150 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_151]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_153 : endpointBQ 153 =
    (186283682728960050912723291785159500985549318094600038724813523537850174963006192915946093 / 4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752) := by
  show endpointBQ (151 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_152]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_154 : endpointBQ 154 =
    (371349825047926898878304601271069593467925111234333410529857024046041198455665940126559205 / 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504) := by
  show endpointBQ (152 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_153]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_155 : endpointBQ 155 =
    (1480576575191085168255058605067770976553935183752472169255403978988761661375187579465632155 / 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016) := by
  show endpointBQ (153 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_154]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_156 : endpointBQ 156 =
    (2951601043445453658005245864296395043581715946964605808386579545209853892676986851966969909 / 65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032) := by
  show endpointBQ (154 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_155]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_157 : endpointBQ 157 =
    (23537126269526566349734140097337919450100350243743395036108365091288834887757510537480195941 / 521481209941628438084722096232800809229175908778479680162851955034721612739414196782949728256) := by
  show endpointBQ (155 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_156]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_158 : endpointBQ 158 =
    (46924334537336402977495451276858399922811526282112628320394383908110861909987903173447779169 / 1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512) := by
  show endpointBQ (156 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_157]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_159 : endpointBQ 159 =
    (187103359231151480226722369015321468046653554162854150897775075076644575970204930375139878965 / 4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048) := by
  show endpointBQ (157 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_158]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_160 : endpointBQ 160 =
    (373029967775314586363968496716081165854019979054243810280469803769159311839968320307668815295 / 8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096) := by
  show endpointBQ (158 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_159]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_161 : endpointBQ 161 =
    (23799311944065070610021190090485978381486474663660755095893973480472364095389978835629270415821 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144) := by
  show endpointBQ (159 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_160]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_162 : endpointBQ 162 =
    (47450802074812966868427341733204963108429555074752188731565003026283409159131572709546557785581 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288) := by
  show endpointBQ (160 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_161]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_163 : endpointBQ 163 =
    (189217395927957880228420140491669173876824028261048851361672789845549890844438246730660964996823 / 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152) := by
  show endpointBQ (161 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_162]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_164 : endpointBQ 164 =
    (377273948936112337878751813863757555275876129968348936764071513495728309965904479677698243091825 / 8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304) := by
  show endpointBQ (162 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_163]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_165 : endpointBQ 165 =
    (3008989787856310597228093734962163916468573036576831763947594753978125789240262557429446963195775 / 68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432) := by
  show endpointBQ (163 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_164]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_166 : endpointBQ 166 =
    (5999743273968037493866926295773041991019154721416834244477325297326081119151796250874473035705515 / 136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864) := by
  show endpointBQ (164 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_165]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_167 : endpointBQ 167 =
    (23926687032330366391204248239769601193100484491433399215927646667649793378786079024571693672512355 / 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456) := by
  show endpointBQ (165 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_166]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_168 : endpointBQ 168 =
    (47710100489616838372880327328402857468877013985912107418586265510942402366082421048996251454770145 / 1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912) := by
  show endpointBQ (166 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_167]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_169 : endpointBQ 169 =
    (761089698286744802614995697857855107241609508822883618344114235531700228220838621495892582730857075 / 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592) := by
  show endpointBQ (167 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_168]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_170 : endpointBQ 170 =
    (1517675907234514783912742900462113438700724286824330055514594659018834182901908967124945564380466475 / 34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184) := by
  show endpointBQ (168 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_169]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_171 : endpointBQ 171 =
    (6052848618264711902899056979490075949641712155687622221405265757733938682397025174768900544999742765 / 139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736) := by
  show endpointBQ (169 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_170]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_172 : endpointBQ 172 =
    (12070300460984016133851335847988981864490197924499878230989448089984053161973015114597632080964399315 / 279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472) := by
  show endpointBQ (170 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_171]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_173 : endpointBQ 173 =
    (96281699025988779858395539438609785570235764839615307749520481275919307780389399635046227994669510815 / 2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776) := by
  show endpointBQ (171 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_172]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_174 : endpointBQ 174 =
    (192006856439110572549979543967169803593822768032758850714361653411515382567828571526537275480699313475 / 4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986543214231552) := by
  show endpointBQ (172 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_173]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_175 : endpointBQ 175 =
    (765820450395073203159113813294343929276511500084681852849235560158572847713063382985154420595432893975 / 17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208) := by
  show endpointBQ (173 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_174]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_176 : endpointBQ 176 =
    (1527264783930745988014461261941291607528585791597451237967904059973382422010623546638965101644606171413 / 35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416) := by
  show endpointBQ (174 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_175]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_177 : endpointBQ 177 =
    (48733630832699258344825082085581214022048510259155034956975847731877930011429896806388795516114251469633 / 1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312) := by
  show endpointBQ (175 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_176]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_178 : endpointBQ 178 =
    (97191930417756147998436463142430330789735164528145352202330362990694402791156799845509857724227857450737 / 2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624) := by
  show endpointBQ (176 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_177]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_179 : endpointBQ 179 =
    (387675677509027331903875779950143454273662734915635955413789650131421494279333302754561792046077408932715 / 9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496) := by
  show endpointBQ (177 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_178]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_180 : endpointBQ 180 =
    (773185569110183002735662868392185548467584337233977855210742486574957952277776475326137205365640418932845 / 18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992) := by
  show endpointBQ (178 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_179]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_181 : endpointBQ 181 =
    (6168302651345682177380065994506546931108061712599956667125701170675775663727150103157405705028109119930919 / 146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936) := by
  show endpointBQ (179 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_180]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_182 : endpointBQ 182 =
    (12302526282518183790244220022192615702375747393638587606808718909469364721577354625634383754227333659088739 / 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872) := by
  show endpointBQ (180 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_181]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_183 : endpointBQ 183 =
    (49074912533561546328117053495119994505081278064734146167819395210300872460797579440717376953676067233507827 / 1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488) := by
  show endpointBQ (181 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_182]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_184 : endpointBQ 184 =
    (97881656146174668905807237845457912537457193954251165853847427605244909552956920742414440372086145028581185 / 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976) := by
  show endpointBQ (182 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_183]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_185 : endpointBQ 185 =
    (1561850774158526238627445925621002343532469138313485994276608953527168774171095213585482592024157183716925865 / 37576681324381331646231689548629392438010920782533117931316655544515344401833735095419183974156299248510959616) := by
  show endpointBQ (183 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_184]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_186 : endpointBQ 186 =
    (3115259111699979362451500251644053323045843848852304496692263264062298798211535858448881494361697301575922401 / 75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232) := by
  show endpointBQ (184 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_185]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_187 : endpointBQ 187 =
    (12427539036996691865263511756558535299462452343271021164223974956635622087489030144995000369980534396609324847 / 300613450595050653169853516389035139504087366260264943450533244356122755214669880763353471793250393988087676928) := by
  show endpointBQ (185 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_186]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_188 : endpointBQ 188 =
    (24788620645988053827504223985007131907483929005561983391740869833289235500713413069963289508036039197514856513 / 601226901190101306339707032778070279008174732520529886901066488712245510429339761526706943586500787976175353856) := by
  show endpointBQ (186 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_187]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_189 : endpointBQ 189 =
    (197781547707351493304554978603780307772478156959271144083038855052839644952500636196515607776883291469533429625 / 4809815209520810450717656262224562232065397860164239095208531909697964083434718092213655548692006303809402830848) := by
  show endpointBQ (187 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_188]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_190 : endpointBQ 190 =
    (394516632199320174475223422929233735609652196685953551953998139444024053688321374847017905459708999386318005125 / 9619630419041620901435312524449124464130795720328478190417063819395928166869436184427311097384012607618805661696) := by
  show endpointBQ (188 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_189]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_191 : endpointBQ 191 =
    (1573913722142551011853786076738732482063770342568172591479634682624053856293408432284418801781365376499100252025 / 38478521676166483605741250097796497856523182881313912761668255277583712667477744737709244389536050430475222646784) := by
  show endpointBQ (189 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_190]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_192 : endpointBQ 192 =
    (3139587058305298091708337671400298825477992149311380928553616827642746174072191689530699285228796902859461759275 / 76957043352332967211482500195592995713046365762627825523336510555167425334955489475418488779072100860950445293568) := by
  show endpointBQ (190 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_191]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_193 : endpointBQ 193 =
    (400820614443643056374764442715438150052690331062086298545345081662390594889883139030085942080876404598391284600775 / 9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704) := by
  show endpointBQ (191 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_192]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_194 : endpointBQ 194 =
    (799564438138873454426343577437532060985936670771519300207035525595960513122305743661052267881541014354303857882375 / 19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408) := by
  show endpointBQ (192 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_193]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_195 : endpointBQ 195 =
    (3190014820203546668690669736786854717541829810191525455465182973253986789467343533987909563609859510877480340211125 / 78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) := by
  show endpointBQ (193 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_194]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_196 : endpointBQ 196 =
    (6363670590047075149336771936461981974993701518792325139363877828696414672322034024211778565355053075545332576113475 / 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) := by
  show endpointBQ (194 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_195]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_197 : endpointBQ 197 =
    (50779493892008293538585261778706835759643618241791818969209719000414247691386026601363375899057668419147449740007525 / 1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112) := by
  show endpointBQ (195 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_196]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_198 : endpointBQ 198 =
    (101301223855630758175959430858029372860608842482356268298981825214024362145759941392567546844313013648349988567629225 / 2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224) := by
  show endpointBQ (196 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_197]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_199 : endpointBQ 199 =
    (404181650737112621005090658473955578585257502833643696748462837975147707551264412626910919227309498899982277618318625 / 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896) := by
  show endpointBQ (197 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_198]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_200 : endpointBQ 200 =
    (806332237902681962507643172935479219589684565954555515623817822493133868833426994034591130317798347051723438263680875 / 20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792) := by
  show endpointBQ (198 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_199]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_201 : endpointBQ 201 =
    (12869062516926804121621985040050248344651365672634706029356132446990416546581494824792074439872061618945506074688346765 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672) := by
  show endpointBQ (199 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_200]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_202 : endpointBQ 202 =
    (25674099847202231108310527368458455652762177287196602575979149807179885747160096640505581345217396563169890228607099765 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344) := by
  show endpointBQ (200 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_201]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_203 : endpointBQ 203 =
    (102442200380420783531179629004839184436268885611289414238807894775183108476292266793304448337847631831262037248798625795 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376) := by
  show endpointBQ (201 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_202]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_204 : endpointBQ 204 =
    (204379759379657228227230294319999358111767973756513363382843336866744625285213635720632027472060546264340517663859327325 / 5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343945494986752) := by
  show endpointBQ (202 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_203]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_205 : endpointBQ 205 =
    (1631030628774911605656524113494896838264501280762763507780730158916962009629057838005828140806443967246795895866485220025 / 41315998049390537434494706752048189989275292685267576205290549704650361952269459114074325652482205302974450751563959894016) := by
  show endpointBQ (203 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_204]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_206 : endpointBQ 206 =
    (3254105010580189496163504206923964911464297677229123291133261634131890058235534906070164437023588207824095226387280268245 / 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032) := by
  show endpointBQ (204 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_205]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_207 : endpointBQ 207 =
    (12984826789790853232264079893648054161279867430496792938405539142021425378007814042668326054531017023453428524710409614065 / 330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128) := by
  show endpointBQ (205 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_206]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_208 : endpointBQ 208 =
    (25906924947746968043116256019693943809703310380653021659717331718139365609261967147932457297204396283508531307755551548835 / 661055968790248598951915308032771039828404682964281219284648795274405791236311345825189210439715284847591212025023358304256) := by
  show endpointBQ (206 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_207]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_209 : endpointBQ 209 =
    (827028757947307056761018942167152821617451831382384922214053281771372055987978182030151521410755727512003114824504145597425 / 21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192) := by
  show endpointBQ (207 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_208]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_210 : endpointBQ 210 =
    (1650100440497737046264808128630156586672140735341887619919905351668239939459267473237192269991794920442609085558938893369025 / 42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384) := by
  show endpointBQ (208 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_209]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_211 : endpointBQ 211 =
    (6584686519700493546523377199009862950625018743888103930918479450942786044127934012251272010729162587290030541420908536396395 / 169230328010303641331690318856389386196071598838855992136870091590247882556495704531248437872567112920983350278405979725889536) := by
  show endpointBQ (209 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_210]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_212 : endpointBQ 212 =
    (13138165994283923142589297634043375839872667730696169454581421084582525708899811465202774959796101655209018284067310397264845 / 338460656020607282663380637712778772392143197677711984273740183180495765112991409062496875745134225841966700556811959451779072) := by
  show endpointBQ (210 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_211]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_213 : endpointBQ 213 =
    (104857438029850933760665526400006565665398838680839239231847945637328459903106042448693845433844358493460655361518345246094895 / 2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576) := by
  show endpointBQ (211 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_212]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_214 : endpointBQ 214 =
    (209222587618247168301797411830999015999035241499327120533029938478237537365352432115938423987717616712304124547630501077888875 / 5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152) := by
  show endpointBQ (212 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_213]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_215 : endpointBQ 215 =
    (834934999186836830512780325718098876930729421684230658575736296543994658457995219752389785446312358281811786746151625796808875 / 21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608) := by
  show endpointBQ (213 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_214]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_216 : endpointBQ 216 =
    (1665986579772804652511547719688671712573408939081557918739492424266854458039441624529187060262641868385568634949297895194562825 / 43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216) := by
  show endpointBQ (214 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_215]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_217 : endpointBQ 217 =
    (26594082069706622416017669155030278078486638990524128258397082772556084126481457043410356406414764639784447469005458993661354725 / 693167423530203714894603546035770925859109268843954143792619895153655326951406405759993601526034894524347802740350892957243539456) := by
  show endpointBQ (215 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_216]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_218 : endpointBQ 218 =
    (53065610765820126756385487300129541050620804990308513990257773458602693210905395851597623612799968152196616378245915872144546525 / 1386334847060407429789207092071541851718218537687908287585239790307310653902812811519987203052069789048695605480701785914487078912) := by
  show endpointBQ (216 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_217]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_219 : endpointBQ 219 =
    (211775602597539037972731073170241746394679359364992693447359004169652949970127038490320791482275102258766313069146544994338327875 / 5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143657948315648) := by
  show endpointBQ (217 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_218]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_220 : endpointBQ 220 =
    (422584193311071048374810406280345402623172968230601858614136460375060909301121076804886693505727030534615884982726210787789266125 / 11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296) := by
  show endpointBQ (218 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_219]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_221 : endpointBQ 221 =
    (3372990197519276186118941242855847850028598782786076653301925565539122530603493685769913789982075752812661336498487391560717960525 / 88725430211866075506509253892578678509965986412026130405455346579667881849780019937279180995332466499116518750764914298527173050368) := by
  show endpointBQ (219 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_220]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_222 : endpointBQ 222 =
    (6730717995954754742436439312667099103450733317686243457493887666980782968308329029070280458742513153802640947492456740625686066025 / 177450860423732151013018507785157357019931972824052260810910693159335763699560039874558361990664932998233037501529828597054346100736) := by
  show endpointBQ (220 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_221]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_223 : endpointBQ 223 =
    (26862234884756363521615699238842566692150223961576629294322452580833214909554862701604813002008408352563693150803228253127738083325 / 709803441694928604052074031140629428079727891296209043243642772637343054798240159498233447962659731992932150006119314388217384402944) := by
  show endpointBQ (221 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_222]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_224 : endpointBQ 224 =
    (53604011317114716444479758570784494071779594900904036035755566809286011815031004045803326394142339537627100682096128128438759852375 / 1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888) := by
  show endpointBQ (222 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_223]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_225 : endpointBQ 225 =
    (3422999008392896892954636011591524121440782702957729158283248337678692468759836972639155271168803681902759143556709896201732236287375 / 90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832) := by
  show endpointBQ (223 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_224]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_226 : endpointBQ 226 =
    (6830784687859603133051695863131530357897384149457868409196348904967701859880741336511025407799079347441506024253167748420345662635695 / 181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664) := by
  show endpointBQ (224 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_225]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_227 : endpointBQ 227 =
    (27262689329421955867312520657277169835501949127482288960597817310977287954037295068729844769180396333593975371134324376438724724324765 / 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656) := by
  show endpointBQ (225 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_226]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_228 : endpointBQ 228 =
    (54405278705850863470892387038531092226794638567178312331060842475210182569070020555659117534972332771445246004950876398796221586427835 / 1453677448591213781098647615776009068707282721374636120562980398361278576226795846652382101427527131121525043212532355867069203257229312) := by
  show endpointBQ (226 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_227]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_229 : endpointBQ 229 =
    (434287751073020050513263791272485034441957202597651440537415496951239176647839637768857868042323007210659419864081557218461067049555525 / 11629419588729710248789180926208072549658261770997088964503843186890228609814366773219056811420217048972200345700258846936553626057834496) := by
  show endpointBQ (227 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_228]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_230 : endpointBQ 230 =
    (866679049084585864998085382583081487947486644485269468670737476448542811039575172316017666791884778581970981999499002833348068304134825 / 23258839177459420497578361852416145099316523541994177929007686373780457219628733546438113622840434097944400691400517693873107252115668992) := by
  show endpointBQ (228 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_229]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_231 : endpointBQ 231 =
    (3459179856781086191601053831353342634503446694075988574955378275564183915366652209504800948325870551035866789024087324352232724796503345 / 93035356709837681990313447409664580397266094167976711716030745495121828878514934185752454491361736391777602765602070775492429008462675968) := by
  show endpointBQ (229 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_230]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_232 : endpointBQ 232 =
    (6903384908987362486268769767332861274918133878653812697205322013138912489108340556630793234537776294491491730476641803144499074160987195 / 186070713419675363980626894819329160794532188335953423432061490990243657757029868371504908982723472783555205531204141550984858016925351936) := by
  show endpointBQ (230 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_231]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_233 : endpointBQ 233 =
    (110216110788315476935946220768107405871968827097128113062278072140804016636453850955864043710034152563777954179678798443307002459880588665 / 2977131414714805823690030317109266572712515013375254774912983855843898524112477893944078543723575564536883288499266264815757728270805630976) := by
  show endpointBQ (231 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_232]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_234 : endpointBQ 234 =
    (219959191058226166417231728142360273521311178541478852248752375731647501012665410705908928434188330223848706839273138524196378299761689825 / 5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456541611261952) := by
  show endpointBQ (232 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_233]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_235 : endpointBQ 235 =
    (877956771146936920656813820875916647303011285289492512821943243304951991221493562390251876741589318072968770033679963169228279196484693575 / 23817051317718446589520242536874132581700120107002038199303870846751188192899823151552628349788604516295066307994130118526061826166445047808) := by
  show endpointBQ (233 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_234]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_236 : endpointBQ 236 =
    (1752177556033674109736364604216191096106860820428816972397835664297968016522895662812885660390661234792435545301259160537736438055963069305 / 47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616) := by
  show endpointBQ (234 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_235]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_237 : endpointBQ 237 =
    (13987722523590856028573351331963152648581888922406318542362383014988863318343794189574053322779685450631137997235475671411421395328111960045 / 381072821083495145432323880589986121307201921712032611188861933548019011086397170424842053596617672260721060927906081896416989218663120764928) := by
  show endpointBQ (235 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_236]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_238 : endpointBQ 238 =
    (27916425120921835027490275021175405918899719241764509158385684245104355905386559711681549458543422861386195243427763681762035105443869017305 / 762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235344521442121855812163792833978437326241529856) := by
  show endpointBQ (236 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_237]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_239 : endpointBQ 239 =
    (111431108675948501160150257437464855558633333107883544959942857280878731555114419017216268847127108060154981013682249990226610715007040195125 / 3048582568667961163458591044719888970457615373696260889510895468384152088691177363398736428772941378085768487423248655171335913749304966119424) := by
  show endpointBQ (237 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_238]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_240 : endpointBQ 240 =
    (222395978403462071353103233463057473227899999550043727807082606372297719463554719126410712301588412320895087629817712323590348581834134615375 / 6097165137335922326917182089439777940915230747392521779021790936768304177382354726797472857545882756171536974846497310342671827498609932238848) := by
  show endpointBQ (238 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_239]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_241 : endpointBQ 241 =
    (7101844910350555478542429921920301978410939985631396374639504563488707174869514030770048746164056633447249798312178946866651798046570032050975 / 195109284394749514461349826862072894109287383916560696928697309976585733676235351257519131441468248197489183195087913930965498479955517831643136) := by
  show endpointBQ (239 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_240]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_242 : endpointBQ 242 =
    (14174221584558577531862692084828486521226813830243575336936106618415220544034175306225698949812909712398867854722647607646719978673859690524975 / 390218568789499028922699653724145788218574767833121393857394619953171467352470702515038262882936496394978366390175827861930996959911035663286272) := by
  show endpointBQ (240 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_241]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_243 : endpointBQ 243 =
    (56579744011089197916443638652662470989690504793451627171406111542930177874119889858735641262476325546187216312653213177631121898342762235731925 / 1560874275157996115690798614896583152874299071332485575429578479812685869409882810060153051531745985579913465560703311447723987839644142653145088) := by
  show endpointBQ (241 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_242]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_244 : endpointBQ 244 =
    (112926649569457864154218784965190528518518085698864358757744708223543770654107599100768666717288139464612345315377812309263761813564772363497875 / 3121748550315992231381597229793166305748598142664971150859156959625371738819765620120306103063491971159826931121406622895447975679288285306290176) := by
  show endpointBQ (242 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_243]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_245 : endpointBQ 245 =
    (901561940005343931854172922590947334238005044841753159262650375489603546041809848558595749038021703594528068337524501551007409888623674443007625 / 24973988402527937851052777838345330445988785141319769206873255677002973910558124960962448824507935769278615448971252983163583805434306282450321408) := by
  show endpointBQ (243 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_244]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_246 : endpointBQ 246 =
    (1799444035357604827251798200599890801805650885418846101548718504548637281691612309980217637875888216562139695579793801054867850757293782867880525 / 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642816) := by
  show endpointBQ (244 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_245]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_247 : endpointBQ 247 =
    (7183146515126698944557991191012572225094102314964662080166022648238869148866517432522657399976106620585451955525843547300326135949847539740888925 / 199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571264) := by
  show endpointBQ (245 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_246]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_248 : endpointBQ 248 =
    (14337211465414828257761496587729546991787013932297888281464976378873532349761915361269919425863241149589586291798546027607533542604351567175134575 / 399583814440447005616844445413525287135820562261116307309972090832047582568929999375399181192126972308457847183540047730617340886948900519205142528) := by
  show endpointBQ (246 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_247]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_249 : endpointBQ 249 =
    (228932892754204515728772284223423411643050706338304990300811719598141887520391874317051939219429173195059523046460654311797713019004968572635213375 / 6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408307282280448) := by
  show endpointBQ (247 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_248]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_250 : endpointBQ 250 =
    (456946376300560820551003314293339098741350205020632852126519777671793245372027154761344633703037345694556558048558012823146439238736824821685546375 / 12786682062094304179739022253232809188346257992355721833919106906625522642205759980012773798148063113870651109873281527379754908382364816614564560896) := by
  show endpointBQ (248 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_249]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_251 : endpointBQ 251 =
    (1824129934191838795639605230659009682175470018442366345689066952465798635525132401807287777742525084012669779729843587190000585441037404688168701129 / 51146728248377216718956089012931236753385031969422887335676427626502090568823039920051095192592252455482604439493126109519019633529459266458258243584) := by
  show endpointBQ (249 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_250]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_252 : endpointBQ 252 =
    (3640992418446658313208933149642087054860201112508468283626384634204641898000363877710960863143446482431663584241639988773666507195058724098695295879 / 102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168) := by
  show endpointBQ (250 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_251]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_253 : endpointBQ 253 =
    (29070145817121732246731640861428091882455256501456500740699547158808490074510841753787512923192913978779790204341982767510384970144675209867360854399 / 818347651974035467503297424206899788054160511510766197370822842024033449101168638720817523081476039287721671031890017752304314136471348263332131897344) := by
  show endpointBQ (251 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_252]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_254 : endpointBQ 254 =
    (58025389872120453694069085513917732808853377601721473810487238399993231176395158441354521842736844107841083214200400385742072766494312177798487080915 / 1636695303948070935006594848413799576108321023021532394741645684048066898202337277441635046162952078575443342063780035504608628272942696526664263794688) := by
  show endpointBQ (252 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_253]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_255 : endpointBQ 255 =
    (231644666654843071046401782327214886095186318457266041117456928100760379578207443541470413970610865847838025114957503902135676319784380111368763386015 / 6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752) := by
  show endpointBQ (253 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_254]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_256 : endpointBQ 256 =
    (462380922852216169265170616488440694205685631744111431093276770208968757667872897108268394945258551829606097190248507788968859791255880300732159072477 / 13093562431584567480052758787310396608866568184172259157933165472384535185618698219533080369303616628603546736510240284036869026183541572213314110357504) := by
  show endpointBQ (254 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_255]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_257 : endpointBQ 257 =
    (236276651577482462494502185025593194739105357821240941288664429576783035168283050422325149817027119984928715664216987480163087353331754833674133286035747 / 6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048) := by
  show endpointBQ (255 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_256]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_258 : endpointBQ 258 =
    (471633938751939701399531598903226882883895130592593785529513044252489093546028034500594559751497714211161210644915620923438380592448211010407900294693923 / 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096) := by
  show endpointBQ (256 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_257]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_259 : endpointBQ 259 =
    (1882879677963170125742316073140789493683767381823145732927900913101022350203135176494621692031173045106573825442880192058688108566750609847752470168739305 / 53631231719770388398296099992823384509917463282369573510894245774887056120294187907207497192667613710760127432745944203415015531247786279785734596024336384) := by
  show endpointBQ (257 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_258]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_260 : endpointBQ 260 =
    (3758489550219918745207634786925823043376477746728055381944883289858025309092744734547179207645237313977214933413007950943404448374556236645899718444935215 / 107262463439540776796592199985646769019834926564739147021788491549774112240588375814414994385335227421520254865491888406830031062495572559571469192048672768) := by
  show endpointBQ (258 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_259]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_261 : endpointBQ 261 =
    (30010093485602120442504037760223110146344491546951703741990683499020232852602069495845938596428894860833454622174632715994260133944533643372645444198790409 / 858099707516326214372737599885174152158679412517913176174307932398192897924707006515319955082681819372162038923935107254640248499964580476571753536389382144) := by
  show endpointBQ (259 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_260]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_262 : endpointBQ 262 =
    (59905205770109979887144075375771035962626360520926581032862628747086365196190337959140743328503656024882106736218328141888925401475486698073365043783792349 / 1716199415032652428745475199770348304317358825035826352348615864796385795849414013030639910165363638744324077847870214509280496999929160953143507072778764288) := by
  show endpointBQ (260 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_261]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_263 : endpointBQ 263 =
    (239163531433339843366231690240673677927126614904157266260970647593329534332882036279622967639751237412315586435436531436701587671539538496888319983961247317 / 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057152) := by
  show endpointBQ (261 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_262]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_264 : endpointBQ 264 =
    (477417695827009193031451092685755440729055029751644733030454714777558956367920414626623794718134599397207919690510186328016477291096036923446266127679295975 / 13729595320261219429963801598162786434538870600286610818788926918371086366795312104245119281322909109954592622782961716074243975999433287625148056582230114304) := by
  show endpointBQ (262 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_263]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_265 : endpointBQ 265 =
    (7624215930328298325078021995314942947400363656942932554759079839023441515330122985097901206559301026737229505360571763480747985830533680565338856038999666025 / 219673525124179510879420825570604582952621929604585773100622830693937381868724993667921908501166545759273481964527387457187903615990932602002368905315681828864) := by
  show endpointBQ (263 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_264]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_266 : endpointBQ 266 =
    (15219661234504414392325560888760772902546386318954004986670012206956228534375981355157697125546680162807526069191480992004964847186235158562506622055210654065 / 439347050248359021758841651141209165905243859209171546201245661387874763737449987335843817002333091518546963929054774914375807231981865204004737810631363657728) := by
  show endpointBQ (264 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_265]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_267 : endpointBQ 267 =
    (60764211394901083024999043849112559483098730341087042465577266781156070313937188718712309576430730574818017614591551930485987472600683227042789596325690656455 / 1757388200993436087035366604564836663620975436836686184804982645551499054949799949343375268009332366074187855716219099657503228927927460816018951242525454630912) := by
  show endpointBQ (265 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_266]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_268 : endpointBQ 268 =
    (121300841473716394203462510754970015747159637722095107244017540053768484933814687592036183536470334817895143777443060595314724055790877003797029418882371235545 / 3514776401986872174070733209129673327241950873673372369609965291102998109899599898686750536018664732148375711432438199315006457855854921632037902485050909261824) := by
  show endpointBQ (266 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_267]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_269 : endpointBQ 269 =
    (968596271469227923863469302297148633204931435542102722023125133265166260292400863608050122268830285486177640610925931619304139848479391000468817001523412104725 / 28118211215894977392565865673037386617935606989386978956879722328823984879196799189494004288149317857187005691459505594520051662846839373056303219880407274094592) := by
  show endpointBQ (267 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_268]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_270 : endpointBQ 270 =
    (1933591813304741245779490763321817159966721862030145582626089950049792869059551166384843552633315476974265401516978532637793022671499750807627341003041160967425 / 56236422431789954785131731346074773235871213978773957913759444657647969758393598378988008576298635714374011382919011189040103325693678746112606439760814548189184) := by
  show endpointBQ (268 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_269]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_271 : endpointBQ 271 =
    (7720044350898189122038114973558958883126393212105544215077499874643247084615541323566153147180422533993548529019640215494595846073617523594897309634364338973645 / 224945689727159819140526925384299092943484855915095831655037778630591879033574393515952034305194542857496045531676044756160413302774714984450425759043258192756736) := by
  show endpointBQ (269 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_270]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_272 : endpointBQ 272 =
    (15411601453269078653220000740573419762994017445568632547442536650118068903236191350735383220017005870444685439851016075950466246220764133818595736207347259722295 / 449891379454319638281053850768598185886969711830191663310075557261183758067148787031904068610389085714992091063352089512320826605549429968900851518086516385513472) := by
  show endpointBQ (270 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_271]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_273 : endpointBQ 273 =
    (492264681713241747570497670713609819488573616055515733721252788294947730262191288438194887557013775744203776108182454661241363041051466156676322632975856589953305 / 14396524142538228424993723224595141948383030778566133225922417832357880258148761185020930195532450742879746914027266864394266451377581759004827248578768524336431104) := by
  show endpointBQ (271 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_272]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_274 : endpointBQ 274 =
    (982726196094200558336707804171858430847152456960644962923380108500902977995949641753905544756675852676157721534649955276104552591110069799958226501728358393862825 / 28793048285076456849987446449190283896766061557132266451844835664715760516297522370041860391064901485759493828054533728788532902755163518009654497157537048672862208) := by
  show endpointBQ (272 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_273]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_275 : endpointBQ 275 =
    (3923731600463705878906417291109536946521112364653086092840065104744481233312295284959024328335048842436921705689441792233789709980563563361877006543397168185715075 / 115172193140305827399949785796761135587064246228529065807379342658863042065190089480167441564259605943037975312218134915154131611020654072038617988630148194691448832) := by
  show endpointBQ (273 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_274]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_276 : endpointBQ 276 =
    (7833195086016634645525902155705948304145784320707433690797075427289891625776182223427288568203424779992254605176376523404911093743015986493347187608454710305300277 / 230344386280611654799899571593522271174128492457058131614758685317726084130380178960334883128519211886075950624436269830308263222041308144077235977260296389382897664) := by
  show endpointBQ (274 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_275]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_277 : endpointBQ 277 =
    (62552036121669067966445972286869239356294596532026028458394037107778699794241687030557043493914305127184525905104108179653710328295678384896149280757370222872760183 / 1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312) := by
  show endpointBQ (275 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_276]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_278 : endpointBQ 278 =
    (124878252618350160958283836370536784707692822679459905189501453142966140744460840894938790801930002654631923557843219578875457803420614248547186109237638026168362387 / 3685510180489786476798393145496356338786055879312930105836138965083617346086082863365358130056307390177215209990980317284932211552660930305235775636164742230126362624) := by
  show endpointBQ (276 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_277]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_279 : endpointBQ 279 =
    (498614605778304599509694454573006586422802277605037750936498607872994302972487530192021790612022672469933219961172567383279705617974395021177613601632295715995979315 / 14742040721959145907193572581985425355144223517251720423344555860334469384344331453461432520225229560708860839963921269139728846210643721220943102544658968920505450496) := by
  show endpointBQ (277 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_278]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_280 : endpointBQ 280 =
    (995442062431955777515769932606324977195343615146975008142042023603074647869804854182638485200346338945350550245064946352999268921905871063784698122255156680321722145 / 29484081443918291814387145163970850710288447034503440846689111720668938768688662906922865040450459121417721679927842538279457692421287442441886205089317937841010900992) := by
  show endpointBQ (278 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_279]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_281 : endpointBQ 281 =
    (15898631797127522275180439780769590350062773739061686558611471176974820804549168956802711806485531527727170216771180143180759752209868054990161321438303788122852647973 / 471745303102692669030194322623533611364615152552055053547025787530703020299018606510765840647207345942683546878845480612471323078740599079070179281429087005456174415872) := by
  show endpointBQ (279 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_280]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_282 : endpointBQ 282 =
    (31740684833411174364328208957337153688203615898980804837654930001006670716555458308776944211524495327597660112486235090122442067579131597329112104366150979134947813213 / 943490606205385338060388645247067222729230305104110107094051575061406040598037213021531681294414691885367093757690961224942646157481198158140358562858174010912348831744) := by
  show endpointBQ (280 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_281]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_283 : endpointBQ 283 =
    (126737628093691426717140295340289486003252735823590022153189543195508905059721439913768933270129722478280018747019506069070460170546461626214823508923000008886351906659 / 3773962424821541352241554580988268890916921220416440428376206300245624162392148852086126725177658767541468375030763844899770584629924792632561434251432696043649395326976) := by
  show endpointBQ (281 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_282]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_284 : endpointBQ 284 =
    (253027420045709032138460306951461341313914472580665591931279476697747460631599341170598753701849092580311698205180285968285547690313607133609099938309169629048723771245 / 7547924849643082704483109161976537781833842440832880856752412600491248324784297704172253450355317535082936750061527689799541169259849585265122868502865392087298790653952) := by
  show endpointBQ (282 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_283]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_285 : endpointBQ 285 =
    (2020655593886155228486014000584205359506894450045597051056837511093279016593194738644077371111949795676573702568129889352364866766307256968399431901708439150290512370365 / 60383398797144661635864873295812302254670739526663046854019300803929986598274381633378027602842540280663494000492221518396329354078796682120982948022923136698390325231616) := by
  show endpointBQ (283 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_284]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_286 : endpointBQ 286 =
    (4034221168144639736872077074850571401962887516055946393162598399340616703303606337854315874255085732420948900916722480847353014701855541105330795621305620619351935223641 / 120766797594289323271729746591624604509341479053326093708038601607859973196548763266756055205685080561326988000984443036792658708157593364241965896045846273396780650463232) := by
  show endpointBQ (284 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_285]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_287 : endpointBQ 287 =
    (16108673335738386641636056012165568325320341060615002730740165636527917046058456076327373176221356316170362394569570185761108890872444153644362827271087478137412272816077 / 483067190377157293086918986366498418037365916213304374832154406431439892786195053067024220822740322245307952003937772147170634832630373456967863584183385093587122601852928) := by
  show endpointBQ (285 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_286]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_288 : endpointBQ 288 =
    (32161218889819148242708920191536134670413085114050162246390644284775249015301377462493326933710234038904591122259107025927231339616412892119233101137049215932882342590983 / 966134380754314586173837972732996836074731832426608749664308812862879785572390106134048441645480644490615904007875544294341269665260746913935727168366770187174245203705856) := by
  show endpointBQ (286 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_287]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_289 : endpointBQ 289 =
    (2054744540182890026617514345570364159498613771175427032408291162638418687088699115659295887431487174707793321699887393323128668919937490329839892572644811017934149665535025 / 61832600368276133515125630254911797508782837275302959978515764023224306276632966792579100265310761247399417856504034834837841258576687802491886538775473291979151693037174784) := by
  show endpointBQ (287 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_288]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_290 : endpointBQ 290 =
    (4102379237666185278056421375066090380729066249024987535292678203606808243772247023305929851377052248465040645746833999818149626182712567198330858181370435838574409539839825 / 123665200736552267030251260509823595017565674550605919957031528046448612553265933585158200530621522494798835713008069669675682517153375604983773077550946583958303386074349568) := by
  show endpointBQ (288 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_289]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_291 : endpointBQ 291 =
    (16381224680060146730997710180436319520290547297830812296099728826816151538925041562028506096188367254215576095775288868239369886619245354536783219910437809314031607748739715 / 494660802946209068121005042039294380070262698202423679828126112185794450213063734340632802122486089979195342852032278678702730068613502419935092310203786335833213544297398272) := by
  show endpointBQ (289 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_290]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_292 : endpointBQ 292 =
    (32706156491803935569449036477091070932263944948590041044790180234983450323420787448586123855276430840890892479881246846897161182562823199264161686487850059145884412721710565 / 989321605892418136242010084078588760140525396404847359656252224371588900426127468681265604244972179958390685704064557357405460137227004839870184620407572671666427088594796544) := by
  show endpointBQ (290 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_291]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_293 : endpointBQ 293 =
    (261201222393447868999846414604713621280957258972986218207022946260210295048689302500352194625015879181361511174942012489603355745672957879054880318115295677836309761873387115 / 7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416708758372352) := by
  show endpointBQ (291 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_292]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_294 : endpointBQ 294 =
    (521510973038112639470683114483813885492696233785655077307537281782331135165471815572375542169400304850158648591607772376853116420541571191969641590776272940389901742989527175 / 15829145694278690179872161345257420162248406342477557754500035589945422406818039498900249667919554879334250971265032917718487362195632077437922953926521162746662833417516744704) := by
  show endpointBQ (292 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_293]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_295 : endpointBQ 295 =
    (2082496198458313737206061144231284018940222375729112451561390370110397117973686773748193491519986251340429433491658247518454281216720423739361766080174640925230423966903758175 / 63316582777114760719488645381029680648993625369910231018000142359781689627272157995600998671678219517337003885060131670873949448782528309751691815706084650986651333670066978816) := by
  show endpointBQ (293 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_294]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_296 : endpointBQ 296 =
    (4157933087769311156658881403227885719172172811201516047354776027101775940632208507585376157644989498439026902801988839960574819107282473160962983800755469508341422767818012085 / 126633165554229521438977290762059361297987250739820462036000284719563379254544315991201997343356439034674007770120263341747898897565056619503383631412169301973302667340133957632) := by
  show endpointBQ (294 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_295]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_297 : endpointBQ 297 =
    (66414552834369267394199970521829201622452814362705296864504665730193231916584735891431278626167264691282835123134470389640532921416322746976462795303958985930534617723795814655 / 2026130648867672343023636652192949780767796011837127392576004555513014068072709055859231957493703024554784124321924213467966382361040905912054138102594708831572842677442143322112) := by
  show endpointBQ (295 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_296]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_298 : endpointBQ 298 =
    (132605487645727190453739335082305442970082555276377915961788777030318473153315651123295448570091541959362697737436838185376552263972657875276237163687702621740091004411484572695 / 4052261297735344686047273304385899561535592023674254785152009111026028136145418111718463914987406049109568248643848426935932764722081811824108276205189417663145685354884286644224) := by
  show endpointBQ (296 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_297]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_299 : endpointBQ 299 =
    (529531980867165626308556405194441198437577989190905100652780686798922761920958472606448267779895754804166477542113548458382876490360613663015846391907268858626537903522371280225 / 16209045190941378744189093217543598246142368094697019140608036444104112544581672446873855659949624196438272994575393707743731058888327247296433104820757670652582741419537146576896) := by
  show endpointBQ (297 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_298]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_300 : endpointBQ 300 =
    (1057292951764875849184642722077195302566000199153746973544180836183802303902381967043644200216046038856479555493785245584129020952325372430837659852737924777926565646832293158175 / 32418090381882757488378186435087196492284736189394038281216072888208225089163344893747711319899248392876545989150787415487462117776654494592866209641515341305165482839074293153792) := by
  show endpointBQ (298 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_299]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_301 : endpointBQ 301 =
    (8444246374762141782154679873656533149827121590574592495372857611654634400500357310121905012392154363667083383210364828065243780672571974480956776690533559226373504299367248023291 / 259344723055062059907025491480697571938277889515152306249728583105665800713306759149981690559193987143012367913206299323899696942213235956742929677132122730441323862712594345230336) := by
  show endpointBQ (299 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_300]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_302 : endpointBQ 302 =
    (16860438774857299704567982073314207385535216199120697972488662540214070680068819745459351868596959377288761173785479274641898711575467630109817351465151724568274006923321315820591 / 518689446110124119814050982961395143876555779030304612499457166211331601426613518299963381118387974286024735826412598647799393884426471913485859354264245460882647725425188690460672) := by
  show endpointBQ (300 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_301]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_303 : endpointBQ 303 =
    (67330096564496369018903928411976603003163810384568085280865321269861487550208598056370789250092493407318695283394993394762019358145741595736555383665473443143504809104389095627923 / 2074757784440496479256203931845580575506223116121218449997828664845326405706454073199853524473551897144098943305650394591197575537705887653943437417056981843530590901700754761842688) := by
  show endpointBQ (301 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_302]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_304 : endpointBQ 304 =
    (134437981589175918338075500624573745270343581790969279191166730588337293623353801399684249162725935681279903123610465359178289477485721668054838307318849614197427094086321461567305 / 4149515568880992958512407863691161151012446232242436899995657329690652811412908146399707048947103794288197886611300789182395151075411775307886874834113963687061181803401509523685376) := by
  show endpointBQ (302 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_303]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_305 : endpointBQ 305 =
    (4294939727612093812169043625216645441005187060374650129949379235111617748914513549979386275882875945186152694527976445948485353307043844868909834344344300832517802426863006693229165 / 132784498204191774672397051638117156832398279431757980799861034550100889965213060684790625566307321417222332371561625253836644834413176809852379994691646837985957817708848304757932032) := by
  show endpointBQ (303 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_304]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_306 : endpointBQ 306 =
    (8575797685625459447904746123793236306793963671371022718489088374370410521603077875204741777090726067601203249073893952729926492340949841066118324969526817072142103862162528118611677 / 265568996408383549344794103276234313664796558863515961599722069100201779930426121369581251132614642834444664743123250507673289668826353619704759989383293675971915635417696609515864064) := by
  show endpointBQ (304 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_305]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_307 : endpointBQ 307 =
    (34247139777236311912874509030311551525824260151684280267953156841440005416336474390523511279754468152315916243033654935411667234119740868571230696446933890399208009541054278957331599 / 1062275985633534197379176413104937254659186235454063846398888276400807119721704485478325004530458571337778658972493002030693158675305414478819039957533174703887662541670786438063456256) := by
  show endpointBQ (305 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_306]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_308 : endpointBQ 308 =
    (68382725353243841050788514773879417216059516198639947245131221966784115049557846258602320568369670936057513540650262134877368125457332744085226113752346823500698729148750074921316841 / 2124551971267068394758352826209874509318372470908127692797776552801614239443408970956650009060917142675557317944986004061386317350610828957638079915066349407775325083341572876126912512) := by
  show endpointBQ (306 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_307]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_309 : endpointBQ 309 =
    (546173715483700808392661514103062877764631200807319059165658461163275724097117862974551001942173345787991828928570275492851706456574800488472909869580432421466619719824432416579348795 / 16996415770136547158066822609678996074546979767265021542382212422412913915547271767653200072487337141404458543559888032491090538804886631661104639320530795262202600666732583009015300096) := by
  show endpointBQ (307 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_308]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_310 : endpointBQ 310 =
    (1090579878490108086661074932691229111911901135592607959563790519539615280802335668140122874428223153240100189155106342974399685707788517480219370192657368297879949408193122333428667335 / 33992831540273094316133645219357992149093959534530043084764424844825827831094543535306400144974674282808917087119776064982181077609773263322209278641061590524405201333465166018030600192) := by
  show endpointBQ (308 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_309]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_311 : endpointBQ 311 =
    (4355283514744367133181970215070134324344947115689189206257976332871108766559005023088619737232710528100787207012973072910667131955619950453263162253257490170243152797880920802531258583 / 135971326161092377264534580877431968596375838138120172339057699379303311324378174141225600579898697131235668348479104259928724310439093053288837114564246362097620805333860664072122400768) := by
  show endpointBQ (309 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_310]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_312 : endpointBQ 312 =
    (8696562902431678423491972680252583329319010157051403527608370748273178598177305849961520439940557035210896641656129512146380350303665560229827729129494859793315105747537144110520616013 / 271942652322184754529069161754863937192751676276240344678115398758606622648756348282451201159797394262471336696958208519857448620878186106577674229128492724195241610667721328144244801536) := by
  show endpointBQ (310 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_311]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_313 : endpointBQ 313 =
    (138922017646536811739371768712752805491429316098539087120513204517286929914473372936564800873922231613753554044917145796594742518953426769825196801222443529518854125146554891816778045541 / 4351082437154956072465106588077822995084026820419845514849846380137705962380101572519219218556758308199541387151331336317719177934050977705242787666055883587123865770683541250307916824576) := by
  show endpointBQ (311 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_312]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_314 : endpointBQ 314 =
    (277400194981103857307052253819394579655409976235102011023388986655924380819635329346175720594892635011488726128029444482018255828581123741663731631833952734662248652449191077908901848125 / 8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500615833649152) := by
  show endpointBQ (312 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_313]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_315 : endpointBQ 315 =
    (1107833899701605850519246899011212748050586338212795929373661749256462336139562748407975648490431096510849880778818227326276728691212513286771718045604384488109744618379890483113894641875 / 34808659497239648579720852704622583960672214563358764118798771041101647699040812580153753748454066465596331097210650690541753423472407821641942301328447068696990926165468330002463334596608) := by
  show endpointBQ (313 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_314]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_316 : endpointBQ 316 =
    (2212150866388285968179702538025564503250218434082059173257248381848618442640587202376560898096765586366109761936116396788025594751659272563109240160905262993717553539558574964694094380125 / 69617318994479297159441705409245167921344429126717528237597542082203295398081625160307507496908132931192662194421301381083506846944815643283884602656894137393981852330936660004926669193216) := by
  show endpointBQ (314 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_315]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_317 : endpointBQ 317 =
    (17669205021405170201536611411318116475327694074756700485130680113246559965901399046830505401253912468316648857996068941433470256813886088447113044829509125937161725107107098768632576631125 / 556938551955834377275533643273961343370755433013740225900780336657626363184653001282460059975265063449541297555370411048668054775558525146271076821255153099151854818647493280039413353545728) := by
  show endpointBQ (315 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_316]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_318 : endpointBQ 318 =
    (35282671225708115891396451177805576431805773972621423997122146724558588196894591787519589649822481364178040148616755961916046285688296195542657909706874689962849753920500925932316785512625 / 1113877103911668754551067286547922686741510866027480451801560673315252726369306002564920119950530126899082595110740822097336109551117050292542153642510306198303709637294986560078826707091456) := by
  show endpointBQ (316 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_317]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_319 : endpointBQ 319 =
    (140908781310217947113438657219537993925765197940972353699198510503740273616528715629402134765014312366371418203595220351048360952277157762072879073357644202052890526663635773377491564783125 / 4455508415646675018204269146191690746966043464109921807206242693261010905477224010259680479802120507596330380442963288389344438204468201170168614570041224793214838549179946240315306828365824) := by
  show endpointBQ (317 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_318]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_320 : endpointBQ 320 =
    (281375842302849004110534246548105649312578153882129747041973201225337160795388062244292037132646134725324744187116474494099705099061283681631423102598179801591508669231147296681699456949375 / 8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630613656731648) := by
  show endpointBQ (318 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_319]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_321 : endpointBQ 321 =
    (35959832646304102725326276708847901982147488066136181671964175116598089149650594354820522345552176017896502307113485440345942311660032054512495872512047378643394807927740624515921190598130125 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944) := by
  show endpointBQ (319 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_320]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_322 : endpointBQ 322 =
    (71807640891840902949950602399911231060923800156988450005386405762427959953040594957756868609030980770939744482429109555332551469701185504493800169097265949253632622684366792257649480290970125 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888) := by
  show endpointBQ (320 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_321]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_323 : endpointBQ 323 =
    (286784553375488823582721971075421873119093189446854492878655024256156386644752189800233953513086463575864942249701350584340562701974299871984555954841875809752085567615204021252600098304930375 / 9124881235244390437282343211400582649786457014497119861158385035798550334417354773011825622634742799557284619147188814621377409442750875996505322639444428376503989348720529900165748384493207552) := by
  show endpointBQ (321 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_322]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_324 : endpointBQ 324 =
    (572681228876750127587788456172282068612430672424833275253041766703470183857167685514399071256782566583383553408846350238079451835211837205665754151309628164984814833163487906216492456367430625 / 18249762470488780874564686422801165299572914028994239722316770071597100668834709546023651245269485599114569238294377629242754818885501751993010645278888856753007978697441059800331496768986415104) := by
  show endpointBQ (322 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_323]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_325 : endpointBQ 325 =
    (4574379692385892994435791742511932078916575864924285544305160778483274184636882623800199988927633587400606901920044303753548214041753810766243739949349745959816977741441687349655192830490464375 / 145998099763910246996517491382409322396583312231953917778534160572776805350677676368189209962155884792916553906355021033942038551084014015944085162231110854024063829579528478402651974151891320832) := by
  show endpointBQ (323 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_324]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_326 : endpointBQ 326 =
    (9134684370333675548888704125816135136051869957956496363858613369955830602551805608757937824043182148378442705680334625034008587424917609807052883775778415778219134012909707969003754298425573475 / 291996199527820493993034982764818644793166624463907835557068321145553610701355352736378419924311769585833107812710042067884077102168028031888170324462221708048127659159056956805303948303782641664) := by
  show endpointBQ (324 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_325]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_327 : endpointBQ 327 =
    (36482696472927747130837707888995729899201026641899871980809554011295986026142487431297040021178598641683228229434956079123555769408720024444119186122894163629574578174259017716695975756288640075 / 1167984798111281975972139931059274579172666497855631342228273284582214442805421410945513679697247078343332431250840168271536308408672112127552681297848886832192510636636227827221215793215130566656) := by
  show endpointBQ (325 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_326]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_328 : endpointBQ 328 =
    (72853825066733391059440438078025112000545169410277114383696143025615531728046007011122223650855122058162532213519958164121351429430869039639173787578745837462116818188963726510710924063781290425 / 2335969596222563951944279862118549158345332995711262684456546569164428885610842821891027359394494156686664862501680336543072616817344224255105362595697773664385021273272455654442431586430261133312) := by
  show endpointBQ (326 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_327]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_329 : endpointBQ 329 =
    (1163884278505131003510572852222108496594075267408085607837096919067760323948052063226464792470978169465767282923306648719499638689688273682040459289367768866772841851555396118646723299067725493375 / 37375513539561023231108477793896786533525327931380202951304745106630862169773485150256437750311906506986637800026885384689161869077507588081685801531164378630160340372359290471078905382884178132992) := by
  show endpointBQ (327 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_328]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_330 : endpointBQ 330 =
    (2324230914826355833758195634984575326025250609991222627200524850539570008613587250880812670679126618051699406931952790907936968447189045012463774325576365183798653788668374619911541664095731456375 / 74751027079122046462216955587793573067050655862760405902609490213261724339546970300512875500623813013973275600053770769378323738155015176163371603062328757260320680744718580942157810765768356265984) := by
  show endpointBQ (328 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_329]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_331 : endpointBQ 331 =
    (9282837411336778754222126808817182665761455466571004311061490160639858398038509080790639696833602674521635813140344783080790680040591397958870468366998937309838259677166417421343672464479315331825 / 299004108316488185848867822351174292268202623451041623610437960853046897358187881202051502002495252055893102400215083077513294952620060704653486412249315029041282722978874323768631243063073425063936) := by
  show endpointBQ (329 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_330]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_332 : endpointBQ 332 =
    (18537629996657434309791014563831292272109734330523969334174154067017964958016478859222395285821786609845321064911685503372817642014594906497925618098448028887622627331138978596701412383748723366575 / 598008216632976371697735644702348584536405246902083247220875921706093794716375762404103004004990504111786204800430166155026589905240121409306972824498630058082565445957748647537262486126146850127872) := by
  show endpointBQ (330 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_331]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_333 : endpointBQ 333 =
    (148077695033540710209535453684580081643478962182378212874186315017263985146565367273065639451805355690692142964294548057062386706694896662748490178304470399427636167717411359151964294101510886651075 / 4784065733063810973581885157618788676291241975216665977767007373648750357731006099232824032039924032894289638403441329240212719241920971274455782595989040464660523567661989180298099889009174801022976) := by
  show endpointBQ (331 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_332]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_334 : endpointBQ 334 =
    (295710712304217934802826056156894157035776305859704238922924623082524174541939847557323273980332016619550375589356980354193655134991310152335573479196615061920054208805040702210379145878392611480375 / 9568131466127621947163770315237577352582483950433331955534014747297500715462012198465648064079848065788579276806882658480425438483841942548911565191978080929321047135323978360596199778018349602045952) := by
  show endpointBQ (332 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_333]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_335 : endpointBQ 335 =
    (1181072126388702769541826224291307800855465844361812738692160021533195355805232804315776190089110509492455691725156322732018969910414394440765434195354145187429198546544683523199538265274777675792875 / 38272525864510487788655081260950309410329935801733327822136058989190002861848048793862592256319392263154317107227530633921701753935367770195646260767912323717284188541295913442384799112073398408183808) := by
  show endpointBQ (333 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_334]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_336 : endpointBQ 336 =
    (2358618664340424336786512668808611697827781044412097678164343445987187143384181331603744093043626659255083157504864417634987136925573820539916643214005740687731742769069830677673107759608436612255025 / 76545051729020975577310162521900618820659871603466655644272117978380005723696097587725184512638784526308634214455061267843403507870735540391292521535824647434568377082591826884769598224146796816367616) := by
  show endpointBQ (334 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_335]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_337 : endpointBQ 337 =
    (75363482084401177618273809560503735678211480038119882954679735821781074914799317786005346972965404207626704699322096392051255660812382551537336552218945333403238066573612208796126443176060046039196275 / 2449441655328671218473925200700819802261115891310932980616707775308160183158275122807205904404441104841876294862561960570988912251863537292521360689146388717906188066642938460312627143172697498123763712) := by
  show endpointBQ (335 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_336]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_338 : endpointBQ 338 =
    (150503333658166149961715946095605383119989098117669677235903448688601375126587361631992873925239516414637306417340566385313041720257369309153197328318546615372045159655908060889593757440618430220709475 / 4898883310657342436947850401401639604522231782621865961233415550616320366316550245614411808808882209683752589725123921141977824503727074585042721378292777435812376133285876920625254286345394996247527424) := by
  show endpointBQ (336 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_337]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_339 : endpointBQ 339 =
    (601122782362497936237622861624459370449660598990692497835709040620153421363588574565652011239861973845444862909496345030096468409311978009931409447426147724119115282649336929588614119955132783425910625 / 19595533242629369747791401605606558418088927130487463844933662202465281465266200982457647235235528838735010358900495684567911298014908298340170885513171109743249504533143507682501017145381579984990109696) := by
  show endpointBQ (337 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_338]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_340 : endpointBQ 340 =
    (1200472341178203843164810257580410011192980016273447849660103305309273941779201961595712128641258278151522631828109220015856369065204156674700779338960182918078587157385253986228589260205383169260594375 / 39191066485258739495582803211213116836177854260974927689867324404930562930532401964915294470471057677470020717800991369135822596029816596680341771026342219486499009066287015365002034290763159969980219392) := by
  show endpointBQ (338 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_339]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_341 : endpointBQ 341 =
    (9589655525411769523634190175259981148235687424113777528461295815352905958447978022629276886440169068998633729544543063420782054062042616260256813778281931780886596233701028901755436560934766728564042125 / 313528531882069915964662425689704934689422834087799421518938595239444503444259215719322355763768461419760165742407930953086580768238532773442734168210737755891992072530296122920016274326105279759841755136) := by
  show endpointBQ (339 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_340]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_342 : endpointBQ 342 =
    (19151188893857522127844233165255270269643704210620183275314200733886595183879979570118878474093123565947418093313295677975227503859973670595996745404721394553618099809825221941628892369491425636809714625 / 627057063764139831929324851379409869378845668175598843037877190478889006888518431438644711527536922839520331484815861906173161536477065546885468336421475511783984145060592245840032548652210559519683510272) := by
  show endpointBQ (340 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_341]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_343 : endpointBQ 343 =
    (76492760318740863235775504396896781252436549566395234953447947960494412342631731265445578934535692371591149460426789169924446696703871444544244310593126973567960012690705418632353997007968676666321842625 / 2508228255056559327717299405517639477515382672702395372151508761915556027554073725754578846110147691358081325939263447624692646145908262187541873345685902047135936580242368983360130194608842238078734041088) := by
  show endpointBQ (341 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_342]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_344 : endpointBQ 344 =
    (152762509674453327453370905282432347399180864294404477968256105985243943016626052235656622653518802549679117727091401111948239029860501281378447092583941623597821016598056010971319206852648814916706886875 / 5016456510113118655434598811035278955030765345404790744303017523831112055108147451509157692220295382716162651878526895249385292291816524375083746691371804094271873160484737966720260389217684476157468082176) := by
  show endpointBQ (342 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_343]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_345 : endpointBQ 345 =
    (2440647538287196185127111905326302852633424506285020380562603367717734624474932508974327901464358543061152415779344013114149772407306148379232398897794602218876814846578243710169681281576040368552968169375 / 80263304161809898486953580976564463280492245526476651908848280381297792881730359224146523075524726123458602430056430323990164676669064390001339947061948865508349970567755807467524166227482951618519489314816) := by
  show endpointBQ (343 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_344]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_346 : endpointBQ 346 =
    (4874220735883704845079942326869051204244723144435881281761257160456577264531097097632788185823023293243866708614400072567099110691692568792148182146610089648713407041427275119730175081176498011399985706375 / 160526608323619796973907161953128926560984491052953303817696560762595585763460718448293046151049452246917204860112860647980329353338128780002679894123897731016699941135511614935048332454965903237038978629632) := by
  show endpointBQ (344 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_345]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_347 : endpointBQ 347 =
    (19468708257200231491041850565702395272445686085579155871081090739164710345612647944880096164183289570124346217644800289848933442126933901938580311348598681776074937951596804090945381393600925583106301289625 / 642106433294479187895628647812515706243937964211813215270786243050382343053842873793172184604197808987668819440451442591921317413352515120010719576495590924066799764542046459740193329819863612948155914518528) := by
  show endpointBQ (345 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_346]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_348 : endpointBQ 348 =
    (38881310726915736090178681389140518512405937917309380457231112052568139105214884800581863520977001936876576163769010377133460736005663383410478835056423303950489717580566528054827519613156891726491835140375 / 1284212866588958375791257295625031412487875928423626430541572486100764686107685747586344369208395617975337638880902885183842634826705030240021439152991181848133599529084092919480386659639727225896311829037056) := by
  show endpointBQ (346 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_347]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_349 : endpointBQ 349 =
    (310603574197775133134186017993708739840484216695747349629604860649825938829015459039130978702057659150910579699074278300089140362344092545635434372002462025811383376074640655150633633691310801723124430144375 / 10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170494632296448) := by
  show endpointBQ (347 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_348]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_350 : endpointBQ 350 =
    (620317166807591025199219640520386795612657590363713188228752400782030599896343194699926338553966155954683879800156939756911549663478030098303431969300045936935628117833881193810864305681500369057357386276875 / 20547405865423334012660116730000502599806014854778022888665159777612234977722971961381509907334329887605402222094446162941482157227280483840343026447858909570137592465345486711686186554235635614340989264592896) := by
  show endpointBQ (348 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_349]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_351 : endpointBQ 351 =
    (2477723997705749294938597306992859257904272318081345820410845303695082224728822246258562917995556245784708754173198290800463846941549388792651993980232754913817166024947902596993109426693535759834816074328775 / 82189623461693336050640466920002010399224059419112091554660639110448939910891887845526039629337319550421608888377784651765928628909121935361372105791435638280550369861381946846744746216942542457363957058371584) := by
  show endpointBQ (349 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_350]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_352 : endpointBQ 352 =
    (4948388952682992181629506302569784443848703404487246211133910421339751109786052406345449018560925721638406942095190888464744036199504619782475919601547467790842830152388831112513304011715579964798307886337525 / 164379246923386672101280933840004020798448118838224183109321278220897879821783775691052079258674639100843217776755569303531857257818243870722744211582871276561100739722763893693489492433885084914727914116743168) := by
  show endpointBQ (350 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_351]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_353 : endpointBQ 353 =
    (316247039430558500335049357336959860365967135759503098766103547836531366379963167423713696368030071119254552753901744962792277949841067973370961043626169986996591781557213479281532065476004792295746404008661825 / 10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586503471562752) := by
  show endpointBQ (351 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_352]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_354 : endpointBQ 354 =
    (631598194896724483671982427542653545490104336290225735496042496387406836537886779132346050820003399827406401392353343339287693922487118757015658741519687934369963756367805957205326079775023735321533186476222625 / 21040543606193494028963959531520514662201359211292695437993123612274928617188323288454666145110353804907931875424712870852077729000735215452511259082607523399820894684513778392766655031537290869085173006943125504) := by
  show endpointBQ (352 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_353]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_355 : endpointBQ 355 =
    (2522824428203300621220856363122350602607365908232709576246904208733879284928169225121856824461821489706080936634993297971053105102815779441864806385618188528811098168090614755616754454242608931482056287224233875 / 84162174424773976115855838126082058648805436845170781751972494449099714468753293153818664580441415219631727501698851483408310916002940861810045036330430093599283578738055113571066620126149163476340692027772502016) := by
  show endpointBQ (353 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_354]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_356 : endpointBQ 356 =
    (5038542308721521522381935666066891766897527968836594618476211504203719473279076001722243629699806862539750377673831685243596201458863063730372247119445903287118503101904917920372616642416928823720501148287272725 / 168324348849547952231711676252164117297610873690341563503944988898199428937506586307637329160882830439263455003397702966816621832005881723620090072660860187198567157476110227142133240252298326952681384055545004032) := by
  show endpointBQ (354 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_355]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_357 : endpointBQ 357 =
    (40251725634842716881051193916556854452406094222953019929624566061672410623611494800275451918163625609727668747484205934923560665587097059688704131482315025136418603432071872375111577896162206670396363105980347275 / 1346594790796383617853693410017312938380886989522732508031559911185595431500052690461098633287062643514107640027181623734532974656047053788960720581286881497588537259808881817137065922018386615621451072444360032256) := by
  show endpointBQ (355 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_356]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_358 : endpointBQ 358 =
    (80390701337935174050950983928585538444161190983096647646561108128774310293095226309793829741318389523069545705759772637536411077208964155624778839627144574011950880243885840345811078543315555619026910068806687975 / 2693189581592767235707386820034625876761773979045465016063119822371190863000105380922197266574125287028215280054363247469065949312094107577921441162573762995177074519617763634274131844036773231242902144888720064512) := by
  show endpointBQ (356 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_357]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_359 : endpointBQ 359 =
    (321113695288400276237038846418651731774163416496726832778163085542310792511525624645265856229288539156395112735297415842673373855890555146769367990689432236975111057957421094118742576304305152332984584911713865375 / 10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579554880258048) := by
  show endpointBQ (357 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_358]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_360 : endpointBQ 360 =
    (641332923459005565632191790758142873766226099242766404183685048283668073066194631951686960769916107451630350504758348632860192352851053036862498187532932907830514285669835444242725423983807226247214338110581731125 / 21545516652742137885659094560277007014094191832363720128504958578969526904000843047377578132593002296225722240434905979752527594496752860623371529300590103961416596156942109074193054752294185849943217159109760516096) := by
  show endpointBQ (358 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_359]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_361 : endpointBQ 361 =
    (10247074932600555593101019945668993916398145896789978769068212215910163211879865341628064995412659583504938266953805614822810628926664602966758582151915083571780883808813592986900435107652386570483269091144628103975 / 344728266443874206170545512964432112225507069317819522056079337263512430464013488758041250121488036739611555846958495676040441511948045769973944468809441663382665538511073745187088876036706973599091474545756168257536) := by
  show endpointBQ (359 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_360]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_362 : endpointBQ 362 =
    (20465764616080334023894280833316744082335355101345082250687482015709771955028761527185138121031932298357508283860647779189048375224723486811725589284018768020094230543364544441981201419992716668472124694502151974975 / 689456532887748412341091025928864224451014138635639044112158674527024860928026977516082500242976073479223111693916991352080883023896091539947888937618883326765331077022147490374177752073413947198182949091512336515072) := by
  show endpointBQ (360 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_361]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_363 : endpointBQ 363 =
    (81749987941580560769478259903248651776400341095428146227884251366619696814838644111352789290088878738742975078625681460517579973963950723562859674322351211483580821452224119511339274180412895863565448365331800430425 / 2757826131550993649364364103715456897804056554542556176448634698108099443712107910064330000971904293916892446775667965408323532095584366159791555750475533307061324308088589961496711008293655788792731796366049346060288) := by
  show endpointBQ (361 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_362]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_364 : endpointBQ 364 =
    (163274769304809659939040601735138491839918036623100292052936865677133003280325115649396066763951617315671231217640823853650813997586402960283948385354558204753708252211742387453776787274929337468553581445910620694375 / 5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893551335930816647064191168732319583111500951066614122648616177179922993422016587311577585463592732098692120576) := by
  show endpointBQ (362 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_363]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_365 : endpointBQ 365 =
    (1304403926204358492040467224851051467776048490384548487060275838981051575657102847001219126784536547126296539507965702654990568969728735737653082155524877086329075817120183688779073893943666245490532458364582651041875 / 44125218104815898389829825659447310364864904872680898823178155169729591099393726561029280015550468702670279148410687446533176513529349858556664892007608532912981188929417439383947376132698492620683708741856789536964608) := by
  show endpointBQ (363 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_364]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_366 : endpointBQ 366 =
    (2605234143021855727938357827168264438380107806822837937169701607170374242887747877983256831303909980424849800825498622562981163777896570829449580524322288755983277453919490161972451695027212857431775786706248637286375 / 88250436209631796779659651318894620729729809745361797646356310339459182198787453122058560031100937405340558296821374893066353027058699717113329784015217065825962377858834878767894752265396985241367417483713579073929216) := by
  show endpointBQ (364 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_365]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_367 : endpointBQ 367 =
    (10406700319939762497939560500874324068064802222882483781809026638478380172409528408774648872585563910877405488543385208161416561320450236482664717832128923937834840539973482559573017426584112561653705464930424884460875 / 353001744838527187118638605275578482918919238981447190585425241357836728795149812488234240124403749621362233187285499572265412108234798868453319136060868263303849511435339515071579009061587940965469669934854316295716864) := by
  show endpointBQ (365 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_366]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_368 : endpointBQ 368 =
    (20785044508217563790162664433626374773546321605920601122795685356960906447891510418615306876308496857419995158316897432104409644272179900113878033163352864431697379062126873886013683307046742527771569770555862235176625 / 706003489677054374237277210551156965837838477962894381170850482715673457590299624976468480248807499242724466374570999144530824216469597736906638272121736526607699022870679030143158018123175881930939339869708632591433728) := by
  show endpointBQ (366 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_367]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_369 : endpointBQ 369 =
    (664217726675648234163893841683277628632893320884853992402383858146359401704359137290532632786380225661030280059257374460727873414784879416682624103263667624230329287420141404618263357855624163387482773102546032298035625 / 22592111669665739975592870737637022906810831294812620197467215446901550642889587999246991367961839975767182923986271972624986374927027127581012424707895568851446368731861728964581056579941628221790058875830676242925879296) := by
  show endpointBQ (367 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_368]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_370 : endpointBQ 370 =
    (1326635405311525063899159244771207621415833001333705670462213830498284225084316217298435095836211995425960207056023536524543205167199068103238737030095726393110440880294428767489593752681829291101828736521887332801225625 / 45184223339331479951185741475274045813621662589625240394934430893803101285779175998493982735923679951534365847972543945249972749854054255162024849415791137702892737463723457929162113159883256443580117751661352485851758592) := by
  show endpointBQ (368 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_369]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_371 : endpointBQ 371 =
    (5299370619055227147143128010194175309331354529651937786332843355341794823444917213965100193637625214160997800077845370225067181721946547720505009001301307051397923300203150590134106936388496465536494250214458048324895875 / 180736893357325919804742965901096183254486650358500961579737723575212405143116703993975930943694719806137463391890175780999890999416217020648099397663164550811570949854893831716648452639533025774320471006645409943407034368) := by
  show endpointBQ (369 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_370]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_372 : endpointBQ 372 =
    (10584457220269335083647056214430953919715724276205083287527323251504770792918284785844041087561941465480591293416936440260848468075370328466022133881305305997536013923047263038515830835212603452729224364983594107301207125 / 361473786714651839609485931802192366508973300717001923159475447150424810286233407987951861887389439612274926783780351561999781998832434041296198795326329101623141899709787663433296905279066051548640942013290819886814068736) := by
  show endpointBQ (370 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_371]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_373 : endpointBQ 373 =
    (84561846394194795345696373842174180240309496099143837447664528772774674184282640815936801376973360310237412161384771775417316255698926387637144574987202605980314605858323832662551207640461982423417351647126993781987063375 / 2891790293717214716875887454417538932071786405736015385275803577203398482289867263903614895099115516898199414270242812495998255990659472330369590362610632812985135197678301307466375242232528412389127536106326559094512549888) := by
  show endpointBQ (371 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_372]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_374 : endpointBQ 374 =
    (168896985425402473277597315046701780908929154407137155223887597682887754067803129779820152884303360405165876837082184913367025765404021873430757931274707617842719521084319719393031232418617096261249133986889035838017056875 / 5783580587434429433751774908835077864143572811472030770551607154406796964579734527807229790198231033796398828540485624991996511981318944660739180725221265625970270395356602614932750484465056824778255072212653118189025099776) := by
  show endpointBQ (372 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_373]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_375 : endpointBQ 375 =
    (674684749266179933360241680961958451010535178300168208300770243150359103147855283131153231040505937019566363621927230643236193832924087376752813768247094066997387605614902836291948292067951716081032636835326790219244606875 / 23134322349737717735007099635340311456574291245888123082206428617627187858318938111228919160792924135185595314161942499967986047925275778642956722900885062503881081581426410459731001937860227299113020288850612472756100399104) := by
  show endpointBQ (373 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_374]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_376 : endpointBQ 376 =
    (1347570339200983386898189384108018346151708929458202634712738432318983915353982952173956720131570524873747216940862655338090424482293710520500953366445529216482782177614832598353784722023722227585849186639092708997904561465 / 46268644699475435470014199270680622913148582491776246164412857235254375716637876222457838321585848270371190628323884999935972095850551557285913445801770125007762163162852820919462003875720454598226040577701224945512200798208) := by
  show endpointBQ (374 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_375]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_377 : endpointBQ 377 =
    (21532453717871032416181706967343016552339008638789578269558863035565040860230663767715776528059775833620939572821018173593742740131969714912685446344693456203799349263590197475823240983825859423765377429062949456540985652345 / 740298315191606967520227188330889966610377319868419938630605715764070011466206019559325413145373572325939050053182159998975553533608824916574615132828322000124194610605645134711392062011527273571616649243219599128195212771328) := by
  show endpointBQ (375 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_376]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_378 : endpointBQ 378 =
    (43007792173890948035503515507716953485175791790473613891187861712945559065659654687241325532172443508532009279401131789697846905356427573817644936598286929765148302375287582756750399100320615772136151734971885784550032350705 / 1480596630383213935040454376661779933220754639736839877261211431528140022932412039118650826290747144651878100106364319997951107067217649833149230265656644000248389221211290269422784124023054547143233298486439198256390425542656) := by
  show endpointBQ (376 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_377]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_379 : endpointBQ 379 =
    (171803614239617279189445260361514814186813348157712055491253098377110566637952588829985189295186216131966492094962193128158065680127528138795354111807971597739084488324561507837812440850487115915147061163512030515001451982975 / 5922386521532855740161817506647119732883018558947359509044845726112560091729648156474603305162988578607512400425457279991804428268870599332596921062626576000993556884845161077691136496092218188572933193945756793025561702170624) := by
  show endpointBQ (377 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_378]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_380 : endpointBQ 380 =
    (343153920789947969251741588637643045750442492230575266508914499924730076371847255262002079937878537234561040939014195773128379208064746176960641326223310025035585640268319423306659677371553421498064182851658593931018731269425 / 11844773043065711480323635013294239465766037117894719018089691452225120183459296312949206610325977157215024800850914559983608856537741198665193842125253152001987113769690322155382272992184436377145866387891513586051123404341248) := by
  show endpointBQ (378 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_379]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_381 : endpointBQ 381 =
    (2741619219784952722758651218694432333943008964242175024002801109924948715434021755198521880766840102747703474449597627282151998093906761561190808069510445357915889483827941497786891527631674178074007524046409187301507547720985 / 94758184344525691842589080106353915726128296943157752144717531617800961467674370503593652882607817257720198406807316479868870852301929589321550737002025216015896910157522577243058183937475491017166931103132108688408987234729984) := by
  show endpointBQ (379 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_380]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_382 : endpointBQ 382 =
    (5476042588599341265142607814767619438663070398394475572876985943970829324003387285317782549248202934884520588073868226671174988318800644483113398795006427604656146711792817532324998563064840024971967784250176880673089878781285 / 189516368689051383685178160212707831452256593886315504289435063235601922935348741007187305765215634515440396813614632959737741704603859178643101474004050432031793820315045154486116367874950982034333862206264217376817974469459968) := by
  show endpointBQ (380 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_381]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_383 : endpointBQ 383 =
    (21875499974352342331433558966846563516753522062696255822540001441098129707929761773285173220295177169198372820420740612304222597315418281364479179479528294567291308592135705639601957610567921146877546698339711832217631295864505 / 758065474756205534740712640850831325809026375545262017157740252942407691741394964028749223060862538061761587254458531838950966818415436714572405896016201728127175281260180617944465471499803928137335448825056869507271897877839872) := by
  show endpointBQ (381 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_382]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_384 : endpointBQ 384 =
    (43693883760782093690722382792787522429024658950294088000634728726997569782157357066744536588840236382341397408934377463218616937196592650767171207054410301159211099407268445990327669901003811168045230350469659403776730917327275 / 1516130949512411069481425281701662651618052751090524034315480505884815383482789928057498446121725076123523174508917063677901933636830873429144811792032403456254350562520361235888930942999607856274670897650113739014543795755679744) := by
  show endpointBQ (382 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_383]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_385 : endpointBQ 385 =
    (11171069614839955286928022534022676567687304471625188498828945644535712007638230956731019854546820435085283937550889171429559730276595521046140105270244233663038304415124966024860440938023307721963563892936742920898917537863339975 / 388129523075177233787244872115625638814221504279174152784763009506512738171594221582719602207161619487621932674282768301542895011028703597861071818760295284801113744005212476387566321407899611206315749798429117187723211713454014464) := by
  show endpointBQ (383 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_384]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_386 : endpointBQ 386 =
    (22313123464446560040643245009515424105328667892674727157401192728955746841230648326561439657523389388520995709030217591764497227487537547232420106370955365420458327520080776293812153458025775683610339308229494301743552173030931015 / 776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928) := by
  show endpointBQ (384 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_385]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_387 : endpointBQ 387 =
    (89136881819110351250445294830758507695380326141203184654695956445724771060045750568802435108551985588340350734001542814769053691154877973659046124414541900202970831699390044158182229617294679026236122314222487599193154017652061205 / 3105036184601417870297958976925005110513772034233393222278104076052101905372753772661756817657292955900975461394262146412343160088229628782888574550082362278408909952041699811100530571263196889650525998387432937501785693707632115712) := by
  show endpointBQ (385 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_386]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_388 : endpointBQ 388 =
    (178043435778223001334868767194254073510410832318217213793488305768850770101848488862233287697443630128648814256804115234667903109205996572709154145148426069397665252980952207065309724791133816246202900643136906754977540195465228195 / 6210072369202835740595917953850010221027544068466786444556208152104203810745507545323513635314585911801950922788524292824686320176459257565777149100164724556817819904083399622201061142526393779301051996774865875003571387415264231424) := by
  show endpointBQ (386 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_387]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_389 : endpointBQ 389 =
    (1422511986887864185922920562634504195572870052026993202989210690421230379679717307919905133665142405667039495350754528936779638243656158184016437757629177358589593516084927427583660172300295954544404618540526832320696841767892287125 / 49680578953622685924767343630800081768220352547734291556449665216833630485964060362588109082516687294415607382308194342597490561411674060526217192801317796454542559232667196977608489140211150234408415974198927000028571099322113851392) := by
  show endpointBQ (387 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_388]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_390 : endpointBQ 390 =
    (2841367130621774993475859324336786015321645322429238351472022381638293072008072874688345215572790871987891228502663930549814341684629395652906869248529230867928314041125934733245511449556118140568129533691489328311520426873142177625 / 99361157907245371849534687261600163536440705095468583112899330433667260971928120725176218165033374588831214764616388685194981122823348121052434385602635592909085118465334393955216978280422300468816831948397854000057142198644227702784) := by
  show endpointBQ (388 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_389]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_391 : endpointBQ 391 =
    (11350897408996731897013817505940288748387495929089111157931822745108873349201480868626773963749764560402909061556795907170796780370904098531356159715919337672390546861728734139478222662585723238474732855106000957716279038636809007025 / 397444631628981487398138749046400654145762820381874332451597321734669043887712482900704872660133498355324859058465554740779924491293392484209737542410542371636340473861337575820867913121689201875267327793591416000228568794576910811136) := by
  show endpointBQ (389 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_390]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_392 : endpointBQ 392 =
    (22672764389837461922168264634627533280027197750942700292441824971688056485233648486950154643704772689705043419631349369566220678950578263306877648946631720516974468283913405020287703067722378131071013708025030045975483194821861469275 / 794889263257962974796277498092801308291525640763748664903194643469338087775424965801409745320266996710649718116931109481559848982586784968419475084821084743272680947722675151641735826243378403750534655587182832000457137589153821622272) := by
  show endpointBQ (390 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_391]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_393 : endpointBQ 393 =
    (362301520760055769082811249161497113433903996714043557734325488833300984243631566638407573184098714613041816276966256252456138604455158778965004063779849738056959360536820329201740234735237185237318443538440786244873537582561582253925 / 12718228212127407596740439969484820932664410252219978638451114295509409404406799452822555925124271947370395489870897751704957583721388559494711601357137355892362895163562802426267773219894054460008554489394925312007314201426461145956352) := by
  show endpointBQ (391 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_392]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_394 : endpointBQ 394 =
    (723681154698839131628516108376018407240749713538229498273398241053794586847966360842620725062385473209256554141014023303252083472003306975795237124852880520037437908451409563418234311112369441250114448289251952168513300260332931474125 / 25436456424254815193480879938969641865328820504439957276902228591018818808813598905645111850248543894740790979741795503409915167442777118989423202714274711784725790327125604852535546439788108920017108978789850624014628402852922291912704) := by
  show endpointBQ (392 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_393]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_395 : endpointBQ 395 =
    (2891051110395870033460112575085921251261269160175566574320631551824042334260657492300215789970037398049161970096335209845986749707952297410918028514006177508982048903305884905635281232717942894740304927937265412977766331496863030812875 / 101745825697019260773923519755878567461315282017759829107608914364075275235254395622580447400994175578963163918967182013639660669771108475957692810857098847138903161308502419410142185759152435680068435915159402496058513611411689167650816) := by
  show endpointBQ (393 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_394]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_396 : endpointBQ 396 =
    (5774783104056560649113997017070359157582636373110182347187286821238403548687743699809798122243948119141237454192426533084768469669808513056238796196331326720473004011919856178598068082568245427721773640867094710985968697597531471674325 / 203491651394038521547847039511757134922630564035519658215217828728150550470508791245160894801988351157926327837934364027279321339542216951915385621714197694277806322617004838820284371518304871360136871830318804992117027222823378335301632) := by
  show endpointBQ (394 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_395]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_397 : endpointBQ 397 =
    (46139933689987267408577491318208627208564296678082366026516604804036133404161669359086366815100635982229483093598074622929816762715338725530150381730283630665597436095238446841121937912237193265938615655816888044342436765653003980751425 / 1627933211152308172382776316094057079381044512284157265721742629825204403764070329961287158415906809263410622703474912218234570716337735615323084973713581554222450580936038710562274972146438970881094974642550439936936217782587026682413056) := by
  show endpointBQ (395 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_396]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_398 : endpointBQ 398 =
    (92163645884533760843833628754003630671011302936320695866568432265996609041562226200895437995906308145863929705852073491141926178421318915227731115143866295007100168321219366108336767668524166901484438828873532038195345982777914752483325 / 3255866422304616344765552632188114158762089024568314531443485259650408807528140659922574316831813618526821245406949824436469141432675471230646169947427163108444901161872077421124549944292877941762189949285100879873872435565174053364826112) := by
  show endpointBQ (396 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_397]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_399 : endpointBQ 399 =
    (368191449639217788295717260600165258208311486604899262381517103776217608985135526782471724657012638070159920181670343846521765386155520289477619279092330173520827305604871336965465981389330214505930295823891748594800502795519810192081625 / 13023465689218465379062210528752456635048356098273258125773941038601635230112562639690297267327254474107284981627799297745876565730701884922584679789708652433779604647488309684498199777171511767048759797140403519495489742260696213459304448) := by
  show endpointBQ (397 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_398]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_400 : endpointBQ 400 =
    (735460113690367361583174578191307545844672317854899027864834916565527404413917330440175349753481384816835730287697403623252749405428445290009179361996459018285963314704467307171620017963148323211093849051733643183097746185537064468894875 / 26046931378436930758124421057504913270096712196546516251547882077203270460225125279380594534654508948214569963255598595491753131461403769845169359579417304867559209294976619368996399554343023534097519594280807038990979484521392426918608896) := by
  show endpointBQ (398 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_399]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_401 : endpointBQ 401 =
    (23505305233544140876198259518994189165195727278642572930560123933434255845068797880868004178121265058746069939994809019799157870997493111468693372409406830224419387537954775137204975774102220409826559415693407236131803968089764580425880205 / 833501804109981784259981473840157224643094790289488520049532226470504654727204008940179025108944286342866238824179155055736100206764920635045419506541353755761894697439251819807884785738976753091120627016985825247711343504684557661395484672) := by
  show endpointBQ (399 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_400]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_402 : endpointBQ 402 =
    (46951993745807623046969590710010836711525629800979304033363240076510820279052636166023120565274646663480304294104344201643704375733147087996068307481134341670224262887535598216711186022583238274990209705661893257210910170673070895065162205 / 1667003608219963568519962947680314449286189580578977040099064452941009309454408017880358050217888572685732477648358310111472200413529841270090839013082707511523789394878503639615769571477953506182241254033971650495422687009369115322790969344) := by
  show endpointBQ (400 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_401]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_403 : endpointBQ 403 =
    (187574382974544882122968066368849263081368560846698413625824287469841734746663019111027690616495230202859126110277554198606440864247348814233049009489307842592985488053189479442881006846439504153319096485803484007663486900748636461379727615 / 6668014432879854274079851790721257797144758322315908160396257811764037237817632071521432200871554290742929910593433240445888801654119365080363356052330830046095157579514014558463078285911814024728965016135886601981690748037476461291163877376) := by
  show endpointBQ (401 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_402]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_404 : endpointBQ 404 =
    (374683320830046228558286087907999148338713874644149436647117993581197509853756154799943649990765906484619346200430350198208895522876217854733509808036954871680777463729075759184911192335939952465066681565934999072379918002736110053128240025 / 13336028865759708548159703581442515594289516644631816320792515623528074475635264143042864401743108581485859821186866480891777603308238730160726712104661660092190315159028029116926156571823628049457930032271773203963381496074952922582327754752) := by
  show endpointBQ (402 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_403]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_405 : endpointBQ 405 =
    (2993756830790567390559771019225300125835070265721075201724992285346795945069120959639153718243050361713740716670765273365886917692684235730395469456295273083627598150785783541210132002129738036032760515086233111400104889388198423889846432675 / 106688230926077668385277628651540124754316133157054530566340124988224595805082113144342915213944868651886878569494931847134220826465909841285813696837293280737522521272224232935409252574589024395663440258174185631707051968599623380658622038016) := by
  show endpointBQ (403 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_404]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_406 : endpointBQ 406 =
    (5980121669406343256698406801366093337779189740662592193075354960112488690273873719377963847058340105250410468609010138649388929415756905446641814296649076357172165195026416999602461209192489064569143843715463178080703346950746975128112997615 / 213376461852155336770555257303080249508632266314109061132680249976449191610164226288685830427889737303773757138989863694268441652931819682571627393674586561475045042544448465870818505149178048791326880516348371263414103937199246761317244076032) := by
  show endpointBQ (404 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_405]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_407 : endpointBQ 407 =
    (23891027950189873798928117812354195551423265417129863392039964889907528708434047223721816157459674016542280246511858238643617841163442612400130598002868970077175497404760710279199980495837973553525003237700692795189410908261358605068471138255 / 853505847408621347082221029212320998034529065256436244530720999905796766440656905154743321711558949215095028555959454777073766611727278730286509574698346245900180170177793863483274020596712195165307522065393485053656415748796987045268976304128) := by
  show endpointBQ (405 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_406]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_408 : endpointBQ 408 =
    (47723355586005816704001375384383196519182100206699211149210052716203491007265062390382890751878906573584456610354154172032583058638522957939327214192463077820009040270443384415207823447460128990210878703318582905378356433455735985063063969045 / 1707011694817242694164442058424641996069058130512872489061441999811593532881313810309486643423117898430190057111918909554147533223454557460573019149396692491800360340355587726966548041193424390330615044130786970107312831497593974090537952608256) := by
  show endpointBQ (406 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_407]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_409 : endpointBQ 409 =
    (762637937305779227720806292907300101237910032714899158560905744386389120998451487218863842407476644264143767400757561768755984172360710014128464305232498204378575839615908986243026982542745198569056198886365589566340401828753427996596022250425 / 27312187117075883106631072934794271937104930088205959824983071996985496526101020964951786294769886374883040913790702552866360531575272919369168306390347079868805765445689403631464768659094790245289840706092591521717005303961503585448607241732096) := by
  show endpointBQ (407 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_408]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_410 : endpointBQ 410 =
    (1523411234178047992782148511748812182668392412538074847296479200889192938522579132170688897914201511891944885003469261528297406036231540541669817450794501303122974232191192278143161478575605934549923996308461336615403687760615038320828729043025 / 54624374234151766213262145869588543874209860176411919649966143993970993052202041929903572589539772749766081827581405105732721063150545838738336612780694159737611530891378807262929537318189580490579681412185183043434010607923007170897214483464192) := by
  show endpointBQ (408 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_409]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_411 : endpointBQ 411 =
    (6086213662399128322383315273767205744416650662774064877735690075747556178780450289013630279959663601168306638135811342398417441676456740017695514596100958864671784859339446223410971955870347611689696355983560169209832294028993738462237702859695 / 218497496936607064853048583478354175496839440705647678599864575975883972208808167719614290358159090999064327310325620422930884252602183354953346451122776638950446123565515229051718149272758321962318725648740732173736042431692028683588857933856768) := by
  show endpointBQ (409 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_410]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_412 : endpointBQ 412 =
    (12157619019050326892157425400882909771693601445590042006377132730386237525009123326715791873106773276299707420704382267905354548944941565826102232319705321722373565375955438806375688505522032577122240166088814839224506845250131044470795995250145 / 436994993873214129706097166956708350993678881411295357199729151951767944417616335439228580716318181998128654620651240845861768505204366709906692902245553277900892247131030458103436298545516643924637451297481464347472084863384057367177715867713536) := by
  show endpointBQ (410 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_411]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_413 : endpointBQ 413 =
    (97142917016295330410151078688608104292270232909908782245129905214639548379441830076573754481231790353346205895531132101806862075550358336649341137855509512403043148586517729491720307184899347679335957831952374880405525569328716986402573826124945 / 3495959950985713037648777335653666807949431051290362857597833215614143555340930683513828645730545455985029236965209926766894148041634933679253543217964426223207137977048243664827490388364133151397099610379851714779776678907072458937421726941708288) := by
  show endpointBQ (411 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_412]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_414 : endpointBQ 414 =
    (194050621158459195129236416266590038840491385352723354363758285235054787925035132719548056772436385088403437926908435796587557414840304183379434476345751447294214521994859871260700371495258987495041562255110676213885129769240173156857441662356125 / 6991919901971426075297554671307333615898862102580725715195666431228287110681861367027657291461090911970058473930419853533788296083269867358507086435928852446414275954096487329654980776728266302794199220759703429559553357814144917874843453883416576) := by
  show endpointBQ (412 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_413]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_415 : endpointBQ 415 =
    (775265042019544707110524233103719623773364133752184608979845902847296181710164515744281366912100920135795377611368485042405362232236384346158416965883750951267224201399754171655068633944826969364248173840466324777212571590152769085609199298398625 / 27967679607885704301190218685229334463595448410322902860782665724913148442727445468110629165844363647880233895721679414135153184333079469434028345743715409785657103816385949318619923106913065211176796883038813718238213431256579671499373815533666304) := by
  show endpointBQ (413 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_414]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_416 : endpointBQ 416 =
    (1548661975504102559505119492151767633995467149109785640588656032434719360572834659161468079928028103114637031421263793012419386242226415958952596782452119370121756296290111345306149150699425440007136713527100200579058365899365411016795243899692675 / 55935359215771408602380437370458668927190896820645805721565331449826296885454890936221258331688727295760467791443358828270306368666158938868056691487430819571314207632771898637239846213826130422353593766077627436476426862513159342998747631067332608) := by
  show endpointBQ (414 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_415]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_417 : endpointBQ 417 =
    (98995238587993017457596484459855300296171784685402451333013320227173214510463507827936921109245488745251028700851554768716962305176165512453046763555208553582398421709006348303800764940863272357379277610847712821630577081720973581150526744664970225 / 3579862989809370150552347991709354811340217396521331566180181212788883000669113019918160533228078546928669938652374965009299607594634172087555628255195572452564109288497401512783350157684872347030630001028968155934491319200842197951919848388309286912) := by
  show endpointBQ (415 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_416]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_418 : endpointBQ 418 =
    (197753078522297802259419356247145000351825171805612091032134522180420354165985856164679748882497583033079393064290995497221174101227208325835462719523953777300090851999046254525338218694817999697114959831741354389492255897058923244840260859246811025 / 7159725979618740301104695983418709622680434793042663132360362425577766001338226039836321066456157093857339877304749930018599215189268344175111256510391144905128218576994803025566700315369744694061260002057936311868982638401684395903839696776618573824) := by
  show endpointBQ (416 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_417]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_419 : endpointBQ 419 =
    (790066127110615621467058193618976436812315877787971751252786248902636343199034401423481293382227185802015756979344407847749666863754636134318714692834934947586487375211500586261518720622837462904741585930641296245100639588728234016467070896990847875 / 28638903918474961204418783933674838490721739172170652529441449702311064005352904159345284265824628375429359509218999720074396860757073376700445026041564579620512874307979212102266801261478978776245040008231745247475930553606737583615358787106474295296) := by
  show endpointBQ (417 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_418]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_420 : endpointBQ 420 =
    (1578246654872518556486700973888026915541547469471437603337904750194526537607617646757646402293375070444599495445611621404693248603729428268316859660865967902457971200601494011219310666256121614442168752801782255267659272877722033106880521099716801125 / 57277807836949922408837567867349676981443478344341305058882899404622128010705808318690568531649256750858719018437999440148793721514146753400890052083129159241025748615958424204533602522957957552490080016463490494951861107213475167230717574212948590592) := by
  show endpointBQ (418 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_419]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_421 : endpointBQ 421 =
    (12610942318457553037069924924686234115612936446538439516195257956316264429074201958377765062134682705743037873132077622462263195985990383972550907194919495906307027021949080718219063323703676519209329367625669639710153618518178912158788163834879963275 / 458222462695599379270700542938797415851547826754730440471063195236977024085646466549524548253194054006869752147503995521190349772113174027207120416665033273928205988927667393636268820183663660419920640131707923959614888857707801337845740593703588724736) := by
  show endpointBQ (419 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_420]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_422 : endpointBQ 422 =
    (25191929904567225900655123186843522306960759029783438558480313399672157683732550705452970112245292530949869005472867649621765671791491479622126634087713292297397172744558614926418603931674090148824337287822299684076577655994746948041664716829297028775 / 916444925391198758541401085877594831703095653509460880942126390473954048171292933099049096506388108013739504295007991042380699544226348054414240833330066547856411977855334787272537640367327320839841280263415847919229777715415602675691481187407177449472) := by
  show endpointBQ (420 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_421]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_423 : endpointBQ 423 =
    (100648326585545836181290373680137864003639430626101605236013763961723359845433840022259970638022661628392130671154632363180798394882593920954752381686930357377752685420203376222610820447399326992696285941394306320741966654045363399047977991881978176575 / 3665779701564795034165604343510379326812382614037843523768505561895816192685171732396196386025552432054958017180031964169522798176905392217656963333320266191425647911421339149090150561469309283359365121053663391676919110861662410702765924749628709797888) := by
  show endpointBQ (421 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_422]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_424 : endpointBQ 424 =
    (201058713864742864239220722836209208234220612007224246866268630136303165648679893188675355057042905617000828409280530370893084264008964215618831589894695394761704537068727784652733199238894636663896835982217940522522368375102439886987095515698041511125 / 7331559403129590068331208687020758653624765228075687047537011123791632385370343464792392772051104864109916034360063928339045596353810784435313926666640532382851295822842678298180301122938618566718730242107326783353838221723324821405531849499257419595776) := by
  show endpointBQ (422 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_423]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_425 : endpointBQ 425 =
    (3213145861196928415294716080042815082535563365473942209353387353310354364234563576052981617609723416181126446465294513663140422105954579068474535030958622629493655526362498747186132448214033155741898492017709351369366905919089935552416413241438512451375 / 117304950450073441093299338992332138457996243649210992760592177980666118165925495436678284352817677825758656549761022853424729541660972550965022826666248518125620733165482852770884817967017897067499683873717228533661411547573197142488509591988118713532416) := by
  show endpointBQ (423 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_424]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_426 : endpointBQ 426 =
    (6418731379191040528435797534014941188406337170087945731155354971671743188788575237809367984354482777265356124821258922588249925571659853245023247626550283793976737745604144556143591643608739174646757222877729974853158830883076130080003611392897169579335 / 234609900900146882186598677984664276915992487298421985521184355961332236331850990873356568705635355651517313099522045706849459083321945101930045653332497036251241466330965705541769635934035794134999367747434457067322823095146394284977019183976237427064832) := by
  show endpointBQ (424 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_425]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_427 : endpointBQ 427 =
    (25644790627659978824877294372989272071989638177205830127761535591045321378681115151998930303688567340154075409497142455974651111086772465312275979953963809899878891180794023555296697130098765434856292942107738068544780117753510735671751517818570381746545 / 938439603600587528746394711938657107663969949193687942084737423845328945327403963493426274822541422606069252398088182827397836333287780407720182613329988145004965865323862822167078543736143176539997470989737828269291292380585577139908076735904949708259328) := by
  show endpointBQ (425 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_426]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_428 : endpointBQ 428 =
    (51229523197643938963982042389133136012663141370390100934380772503891473386451970081159455618375522110424886005388905187228050111843130943586349908432625596825753382148049887804843284899237112215298402528379158249341211804317903179222491907960750668922255 / 1876879207201175057492789423877314215327939898387375884169474847690657890654807926986852549645082845212138504796176365654795672666575560815440365226659976290009931730647725644334157087472286353079994941979475656538582584761171154279816153471809899416518656) := by
  show endpointBQ (426 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_427]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_429 : endpointBQ 429 =
    (409357404990519325366398563015970385895579307211995666344818322344179530330994714199919014520664218732834369482313214346541895753512868754825506277662569021364664876042828542739635594288296550879253590296861498160623701800858011385375986741181699270360075 / 15015033657609400459942315391018513722623519187099007073355798781525263125238463415894820397160662761697108038369410925238365381332604486523522921813279810320079453845181805154673256699778290824639959535835805252308660678089369234238529227774479195332149248) := by
  show endpointBQ (427 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_428]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_430 : endpointBQ 430 =
    (817760596915792684939402257586682099562963790864056610856665040207370297188024405756015373995825723669088705469329661293674602938835730822576827226006577275779761768691617858106917725652844158749464631432191850637889306394721015751205642510938732575054975 / 30030067315218800919884630782037027445247038374198014146711597563050526250476926831789640794321325523394216076738821850476730762665208973047045843626559620640158907690363610309346513399556581649279919071671610504617321356178738468477058455548958390664298496) := by
  show endpointBQ (428 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_429]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_431 : endpointBQ 431 =
    (3267238850003097285409053671009115923370166959777788970818024509479679466439595183927521889592624635496498595340251995587285971741673919891132532963440231999510769113051626698203917796910665731933907527443036277664869368339838848978072776357657540846382435 / 120120269260875203679538523128148109780988153496792056586846390252202105001907707327158563177285302093576864306955287401906923050660835892188183374506238482560635630761454441237386053598226326597119676286686442018469285424714953873908233822195833562657193984) := by
  show endpointBQ (429 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_430]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_432 : endpointBQ 432 =
    (6526897099426140980828759189649301183345043508976047108757120887846877077968657664412056489418213018938480952640271387936550398305292911893886568170584779005983230177117054726574415830951469130383049608186668758861838807750814962807704548593835597839292985 / 240240538521750407359077046256296219561976306993584113173692780504404210003815414654317126354570604187153728613910574803813846101321671784376366749012476965121271261522908882474772107196452653194239352573372884036938570849429907747816467644391667125314387968) := by
  show endpointBQ (430 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_431]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_433 : endpointBQ 433 =
    (208618970252028135794637747432123960045436020305419579809533160230068700677294502384726101865478438346070706004761266955157147916202510480163855864119061640080130653438963638112360031930041402204465622661670190329546921892183456033446260201351115590196660965 / 7687697232696013035490465480201479025983241823794691621558168976140934720122093268938148043346259333988919315645138393722043075242293497100043735968399262883880680368733084239192707430286484902215659282347932289182034267181757047930126964620533348010060414976) := by
  show endpointBQ (431 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_432]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_434 : endpointBQ 434 =
    (416756141496545814000835222930224539120790202226761978141446151498867034840322735710826970239350690922289054720827935141364741218279841952290381807073876024640445762643657152349171888266710884311461347811419664284198816251128613092219434351428902968868618325 / 15375394465392026070980930960402958051966483647589383243116337952281869440244186537876296086692518667977838631290276787444086150484586994200087471936798525767761360737466168478385414860572969804431318564695864578364068534363514095860253929241066696020120829952) := by
  show endpointBQ (432 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_433]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_435 : endpointBQ 435 =
    (1665104030771913459625456858435505416671544264196325507136561351841095480214561344982889323490861977095044287755565989712272952240777064390026548510290555361121043669179957378279871092752250399530124371209681331494932597648518467976747693929441745963175539575 / 61501577861568104283923723841611832207865934590357532972465351809127477760976746151505184346770074671911354525161107149776344601938347976800349887747194103071045442949864673913541659442291879217725274258783458313456274137454056383441015716964266784080483319808) := by
  show endpointBQ (433 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_434]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_436 : endpointBQ 436 =
    (3326380236185730566470165540184952200201314863417487047590050148850372350129778870781909935893239214012858588642728379448195851717782227482604760127454005997273992985097432095920018343911966890095811674899340407055394085877155284302974128792379028142527687105 / 123003155723136208567847447683223664415731869180715065944930703618254955521953492303010368693540149343822709050322214299552689203876695953600699775494388206142090885899729347827083318884583758435450548517566916626912548274908112766882031433928533568160966639616) := by
  show endpointBQ (434 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_435]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_437 : endpointBQ 437 =
    (26580524639612580948582698949551315287847204092079185490375538345400681807000343086706821597825792251423851657869875399076867769231085505847236202486352653427758237523118012436204917225204799644710568521443353160965580264211029840622848313561120490937079040995 / 984025245785089668542779581465789315325854953445720527559445628946039644175627938424082949548321194750581672402577714396421513631013567628805598203955105649136727087197834782616666551076670067483604388140535333015300386199264902135056251471428268545287733116928) := by
  show endpointBQ (435 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_436]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_438 : endpointBQ 438 =
    (53100224280049847066619442066266128710047160577540340808004221911978936424510982871155732848745804657878770016751490213716488701461642211909924953708434476984972405852819278848528358667285560846298229563432602538954122587314025288017726722514549630636315795855 / 1968050491570179337085559162931578630651709906891441055118891257892079288351255876848165899096642389501163344805155428792843027262027135257611196407910211298273454174395669565233333102153340134967208776281070666030600772398529804270112502942856537090575466233856) := by
  show endpointBQ (436 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_437]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_439 : endpointBQ 439 =
    (212158430342664914078958958027319007403156463494738804598190384351514015394735662156444138094304014044036181573778785100465422893967748563567051755684384325853200251695054196312613305177510802468086533643851722472990215816893936653038862475800141218295782289375 / 7872201966280717348342236651726314522606839627565764220475565031568317153405023507392663596386569558004653379220621715171372109048108541030444785631640845193093816697582678260933332408613360539868835105124282664122403089594119217080450011771426148362301864935424) := by
  show endpointBQ (437 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_438]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_440 : endpointBQ 440 =
    (423833584078626719014230082437263711828173618416596655199573956893571279045975343305698198425295262680227178223699304175645047558108691321750123894613223357114479773887386173499229769113159393541029362199676447856064736381357590990239367633887753641105697193125 / 15744403932561434696684473303452629045213679255131528440951130063136634306810047014785327192773139116009306758441243430342744218096217082060889571263281690386187633395165356521866664817226721079737670210248565328244806179188238434160900023542852296724603729870848) := by
  show endpointBQ (438 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_439]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_441 : endpointBQ 441 =
    (6773631280092961563881968044770087321762992919785244725825918329262711896025678668467431207560627925380357993793303424916218123701409812214879252788454969652793231295400226300105872128190311034955723806791192684826925514167514954189461893639769735464216506050125 / 251910462920982955146951572855242064723418868082104455055218081010186148908960752236565235084370225856148908135059894885483907489539473312974233140212507046179002134322645704349866637075627537275802723363977045251916898867011814946574400376685636747593659677933568) := by
  show endpointBQ (439 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_440]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_442 : endpointBQ 442 =
    (13531902852067798498367378338871761747104754563108391391049056798368365488432251489614074589253771433696361434312699132315619426260639556828364221556981469986645888370175962291141209398947083949650777038056781758123631242588618309843346776182850650666609391905125 / 503820925841965910293903145710484129446837736164208910110436162020372297817921504473130470168740451712297816270119789770967814979078946625948466280425014092358004268645291408699733274151255074551605446727954090503833797734023629893148800753371273495187319355867136) := by
  show endpointBQ (440 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_441]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_443 : endpointBQ 443 =
    (54066381078623828389404502593772695125309946964817690490028584402530618670975918847643564987832941972642023287321779791107203408996129994024640758528573022616327237243734727163247456557784050350867131785539087296032427091428732885030204540133290156283330737792875 / 2015283703367863641175612582841936517787350944656835640441744648081489191271686017892521880674961806849191265080479159083871259916315786503793865121700056369432017074581165634798933096605020298206421786911816362015335190936094519572595203013485093980749277423468544) := by
  show endpointBQ (441 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_442]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_444 : endpointBQ 444 =
    (108010716150298167324205383285527844663429578022265589353668842429434757390098618916850011318808473241056863677832449469819130963795880462103401966812160553082279017969989240495426634432593418872499800519643549112841304686037084883186751733674857309956541090173125 / 4030567406735727282351225165683873035574701889313671280883489296162978382543372035785043761349923613698382530160958318167742519832631573007587730243400112738864034149162331269597866193210040596412843573823632724030670381872189039145190406026970187961498554846937088) := by
  show endpointBQ (442 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_443]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_445 : endpointBQ 445 =
    (863112659687517787536668243011380164112270591943689889700038407521699367612770044858071712070118160043400343083219663781347469953936450179150608509571048743999833233688112219094084907582976239098264171720034487054867002310944993616095935024951337242625693216068125 / 32244539253885818258809801325470984284597615114509370247067914369303827060346976286280350090799388909587060241287666545341940158661052584060701841947200901910912273193298650156782929545680324771302748590589061792245363054977512313161523248215761503691988438775496704) := by
  show endpointBQ (443 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_444]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_446 : endpointBQ 446 =
    (1724285740364501827236175433791274080664738328624584970659177852329866826534275437929945510180528189390073943822432092363186293907976413953404249359570027715541239875839846657920542658070260396760352468896877885374779247313326065898223115139734244513919643301313625 / 64489078507771636517619602650941968569195230229018740494135828738607654120693952572560700181598777819174120482575333090683880317322105168121403683894401803821824546386597300313565859091360649542605497181178123584490726109955024626323046496431523007383976877550993408) := by
  show endpointBQ (444 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_445]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_447 : endpointBQ 447 =
    (6889410738407045417342745791515808098081981393742175824472320477246239203775961503119199325429823393482313380922811633612551515121107555302615184660882935849987644526337683283440374476863686159253246860031920160847212149579253474059716572150238618214808978392244125 / 257956314031086546070478410603767874276780920916074961976543314954430616482775810290242800726395111276696481930301332362735521269288420672485614735577607215287298185546389201254263436365442598170421988724712494337962904439820098505292185985726092029535907510203973632) := by
  show endpointBQ (445 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_446]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_448 : endpointBQ 448 =
    (13763408924826603037331257252401826916302481844769044767905552989218996888080388416745961963330721007560863197235057693100690163318006816298065682107759422179058090742773045127767906952660563177210625158855715220663446195915600340794914762707299968827347690613588375 / 515912628062173092140956821207535748553561841832149923953086629908861232965551620580485601452790222553392963860602664725471042538576841344971229471155214430574596371092778402508526872730885196340843977449424988675925808879640197010584371971452184059071815020407947264) := by
  show endpointBQ (446 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_447]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_449 : endpointBQ 449 =
    (1759750141102829959773067891557090727155817321581185009610781417907286030690278233283947993882999328823853223075053805046445385167088014369538397926634954692893855887825982198478896674661600577657644216739409303213397763620637472144492673231861924585782311871308799375 / 66036816391958155794042473114564575814855915754515190265995088628334237819590607434302156985957148486834299374157141084860293444937835692156317372307867447113548335499875635521091439709553305131628029113526398550518503536593945217354799612345879559561192322612217249792) := by
  show endpointBQ (447 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_448]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_450 : endpointBQ 450 =
    (3515581016857992146807220264424744726634227477635463148376104525306983451067215089656350446576949661369702318704506153956929867471888527593487623474814152248387057308195781808542472866751571755365048691347995868557723371865727867513607857213764245776050631956712679375 / 132073632783916311588084946229129151629711831509030380531990177256668475639181214868604313971914296973668598748314282169720586889875671384312634744615734894227096670999751271042182879419106610263256058227052797101037007073187890434709599224691759119122384645224434499584) := by
  show endpointBQ (448 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_449]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_451 : endpointBQ 451 =
    (14046699262912599733243071189857091152196313343974583868400524303337680544486339402671373562100789980317166153401560144032355337143234605806868326683812990539110953422524479315020813809820724480325238993430436825926192494699063790643259838378551364234086747240376438925 / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336) := by
  show endpointBQ (449 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_450]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_452 : endpointBQ 452 =
    (28062252851184595032487820714104743077891082755922616553057366734605876209716611533939928114086057144713451672316642327656656671321628336656293486346154111919598600961628726968589253309641846467345987434769010155564300305374404601706379411040077115687166650251838517675 / 1056589062271330492704679569833033213037694652072243044255921418053347805113449718948834511775314375789348789986514257357764695119005371074501077956925879153816773367998010168337463035352852882106048465816422376808296056585503123477676793797534072952979077161795475996672) := by
  show endpointBQ (450 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_451]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_453 : endpointBQ 453 =
    (224249684288669816941030992078199849551642900253080732277971700542912444401540709868564204309908934528108379292937416122778415700915313168147194851067054540384048997065050800465806156978819357168260412863685098853757196245602542967618235470523802083765588364401860012925 / 8452712498170643941637436558664265704301557216577944354047371344426782440907597751590676094202515006314790319892114058862117560952042968596008623655407033230534186943984081346699704282822823056848387726531379014466368452684024987821414350380272583623832617294363807973376) := by
  show endpointBQ (451 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_452]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_454 : endpointBQ 454 =
    (448004336161691356140470304262187337404496301830106098701025141261226848086963228324615021855336833880658020441740312563166592073572535137247707152794005207610517312017375219473630401911327854828423120621710848703422213250044815420959167992989052728052665496211221438625 / 16905424996341287883274873117328531408603114433155888708094742688853564881815195503181352188405030012629580639784228117724235121904085937192017247310814066461068373887968162693399408565645646113696775453062758028932736905368049975642828700760545167247665234588727615946752) := by
  show endpointBQ (452 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_453]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_455 : endpointBQ 455 =
    (1790043757262793215944522317029973193946599761056855645470615872792655291695487436521699668822865675461483808549156226849304400928327265944861984086273844596047309259910834026707413103672133763565549649356351276537462323426390518003568129381678726098430694295434263633625 / 67621699985365151533099492469314125634412457732623554832378970755414259527260782012725408753620120050518322559136912470896940487616343748768068989243256265844273495551872650773597634262582584454787101812251032115730947621472199902571314803042180668990660938354910463787008) := by
  show endpointBQ (453 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_454]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_456 : endpointBQ 456 =
    (3576153352421712161084770958637902490763646555605894025786351271139612439892743032523571426285681096691184136200402220233005935041427438997537458317413021401773635422547138747861623101621911189189196991791040242577040114273821935967567977160320795655985716735274166248275 / 135243399970730303066198984938628251268824915465247109664757941510828519054521564025450817507240240101036645118273824941793880975232687497536137978486512531688546991103745301547195268525165168909574203624502064231461895242944399805142629606084361337981321876709820927574016) := by
  show endpointBQ (454 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_455]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_457 : endpointBQ 457 =
    (57155714106248768048214497251212792440099684423806481710374842245757665486706822853139887181513254019046820141729235484776638716188428016258888149599355482403785646841060410514069099045220370058795762447748029140134799019358803222218498722685127102501806806067276586880325 / 2163894399531684849059183759018052020301198647443953754636127064173256304872345024407213080115843841616586321892381199068702095603722999960578207655784200507016751857659924824755124296402642702553187257992033027703390323887110396882282073697349781407701150027357134841184256) := by
  show endpointBQ (455 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_456]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_458 : endpointBQ 458 =
    (114186361004387582555842091882619867610089741529398944861208382867345182908891311301787126907487091727329861683585978112912628332341432776464693392963263797450013775855335130851958615816818813706084313161474727800750703511322948231696913203088667493619583400305084297202925 / 4327788799063369698118367518036104040602397294887907509272254128346512609744690048814426160231687683233172643784762398137404191207445999921156415311568401014033503715319849649510248592805285405106374515984066055406780647774220793764564147394699562815402300054714269682368512) := by
  show endpointBQ (456 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_457]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_459 : endpointBQ 459 =
    (456246813620151257810460760142345759228087831875109321170330438094414158784434715463472581311575060831907525940965807743733864297346772884127486701141425216885426222304068317596253857958031504546144744728163213701689492195897369572064085505790964002890475158424245117644875 / 17311155196253478792473470072144416162409589179551630037089016513386050438978760195257704640926750732932690575139049592549616764829783999684625661246273604056134014861279398598040994371221141620425498063936264221627122591096883175058256589578798251261609200218857078729474048) := by
  show endpointBQ (457 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_458]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_460 : endpointBQ 460 =
    (911499625467709593490615505556712551660471768691667205911095886127620443584589616732035636302209870986621353568334740089333232158315883953692604150210646892993324282903770473280533306639465990563866516156265069639323015999211084744189033570392840938236526623692881858127125 / 34622310392506957584946940144288832324819178359103260074178033026772100877957520390515409281853501465865381150278099185099233529659567999369251322492547208112268029722558797196081988742442283240850996127872528443254245182193766350116513179157596502523218400437714157458948096) := by
  show endpointBQ (458 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_459]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_461 : endpointBQ 461 =
    (7284070920041957534068483909622772478051943960240366628106931472619853805689024850232528258797659751623521947211301096887802090030367803073421767078639865170964043617291870129954870511318863002853855029109631295639459580028478146781823668271226268019472764931945725457555025 / 276978483140055660679575521154310658598553426872826080593424264214176807023660163124123274254828011726923049202224793480793868237276543994954010579940377664898144237780470377568655909939538265926807969022980227546033961457550130800932105433260772020185747203501713259671584768) := by
  show endpointBQ (459 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_460]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_462 : endpointBQ 462 =
    (14552341252404865268713825771719248269600521447681947211467427085212332657352693898186894851090335425694715213409128655604480965114899667311543270020449708942424911434980070259627843255801893331081129027787354497362130744482057208646550105157916253461896782000698510078976525 / 553956966280111321359151042308621317197106853745652161186848528428353614047320326248246548509656023453846098404449586961587736474553087989908021159880755329796288475560940755137311819879076531853615938045960455092067922915100261601864210866521544040371494407003426519343169536) := by
  show endpointBQ (460 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_461]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_463 : endpointBQ 463 =
    (58146367861340652134298100377908511484161390892685875654478074457363562955569421939508675097646664926044251696868509736462926107363863172850885013977814204995057113655786168180244585822966006686527628106700122082533535398947787028488163407189422952144288873535258548930282825 / 2215827865120445285436604169234485268788427414982608644747394113713414456189281304992986194038624093815384393617798347846350945898212351959632084639523021319185153902243763020549247279516306127414463752183841820368271691660401046407456843466086176161485977628013706077372678144) := by
  show endpointBQ (461 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_462]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_464 : endpointBQ 464 =
    (116167149614989423810422770733402533742655046599858390886376282663199342837800680980659880054693661029354066565018081006972368573027156446840321032245093174126194017562855735565283459797502281177188025915113634830115594479539315337692335100756406545860620319697870751102616875 / 4431655730240890570873208338468970537576854829965217289494788227426828912378562609985972388077248187630768787235596695692701891796424703919264169279046042638370307804487526041098494559032612254828927504367683640736543383320802092814913686932172352322971955256027412154745356288) := by
  show endpointBQ (462 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_463]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_465 : endpointBQ 465 =
    (3713343023899834340422824429995315475153145799933404425919683242371923821056594181692127890024173233593490334681784865291840885075730138835206124030731081807413167388991974719621302318354641884525975862872770327155764002845963631656579125462109960965958449529652627112831925625 / 141812983367708498267942666831007057202459354558886953263833223277658525196114003519551116418471942004184601191539094262166460537485590525416453416929473364427849849743600833315151825889043592154525680139765876503569388266265666970077237981829515274335102568192877188951851401216) := by
  show endpointBQ (463 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_464]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_466 : endpointBQ 466 =
    (7418700363877303445704954613904619519176929995995984326192227380996811246799088160842982386736466524749145206278232558830365983301835051565390299407632634406638349471771063472103634094089166259622863605610330395543451093857849922169810768933978825241667526049564065780259911625 / 283625966735416996535885333662014114404918709117773906527666446555317050392228007039102232836943884008369202383078188524332921074971181050832906833858946728855699699487201666630303651778087184309051360279531753007138776532531333940154475963659030548670205136385754377903702802432) := by
  show endpointBQ (464 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_465]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_467 : endpointBQ 467 =
    (29642961539784418489061428092468672842719836164258632651008427861407859531201506771436981124685194568847442862854225374553951632849821600890035917375562157221374692524544463916431258976811217972999510801816384541849583555286087028069072214066670756652328183485597189877347543875 / 1134503866941667986143541334648056457619674836471095626110665786221268201568912028156408931347775536033476809532312754097331684299884724203331627335435786915422798797948806666521214607112348737236205441118127012028555106130125335760617903854636122194680820545543017511614811209728) := by
  show endpointBQ (465 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_466]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_468 : endpointBQ 468 =
    (59222447787192424947097028715788590497339629852790801420537180288422982746490376483406217107775774160031400837351161187278023283616453005632555697883082425455123315043683051036467590204207422631281677897419029502239103762488049672780394808831271554510968298055807662003351731125 / 2269007733883335972287082669296112915239349672942191252221331572442536403137824056312817862695551072066953619064625508194663368599769448406663254670871573830845597595897613333042429214224697474472410882236254024057110212260250671521235807709272244389361641091086035023229622419456) := by
  show endpointBQ (466 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_467]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_469 : endpointBQ 469 =
    (473273407530127498508852323497968650555662853951789737847882594612611015965542752239186435861285032817344955409601159915426938206678491968089227158296427929919147859537125236915360656760119146668789477214417030637551812119028431145723667916728537636476541527198121059599434774375 / 18152061871066687778296661354368903321914797383537530017770652579540291225102592450502542901564408576535628952517004065557306948798155587253306037366972590646764780767180906664339433713797579795779287057890032192456881698082005372169886461674177955114893128728688280185836979355648) := by
  show endpointBQ (467 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_468]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_470 : endpointBQ 470 =
    (945537703317120396807664450144129265609074827617967983717411494993638639572950018865922580814550268123352288312998479404594970361743596959700652126489878401565547002955834428549451887812860640572826738059506946071185603316694328323119566818709253231084263136427802628666674591875 / 36304123742133375556593322708737806643829594767075060035541305159080582450205184901005085803128817153071257905034008131114613897596311174506612074733945181293529561534361813328678867427595159591558574115780064384913763396164010744339772923348355910229786257457376560371673958711296) := by
  show endpointBQ (468 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_469]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_471 : endpointBQ 471 =
    (3778127248573515117457008164618456937901792609077752922172976143825645457697872628574899163339841284118416164791087541110275221998626542745357073816059556676893823982023525652799724777260749538288869391650540520684439495805855209767699035075608462910587757808960453907736201879875 / 145216494968533502226373290834951226575318379068300240142165220636322329800820739604020343212515268612285031620136032524458455590385244698026448298935780725174118246137447253314715469710380638366234296463120257539655053584656042977359091693393423640919145029829506241486695834845184) := by
  show endpointBQ (469 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_470]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_472 : endpointBQ 472 =
    (7548232995557702177339797628250462799502307526841115710753228346793911625676641493607176460090850633451018282523170650073819498727616935718431011594293084571034157891898381399754864151597378589235299570155326178267638143425286098495551575384602045857458768786054749739235171908625 / 290432989937067004452746581669902453150636758136600480284330441272644659601641479208040686425030537224570063240272065048916911180770489396052896597871561450348236492274894506629430939420761276732468592926240515079310107169312085954718183386786847281838290059659012482973391669690368) := by
  show endpointBQ (470 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_471]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_473 : endpointBQ 473 =
    (120643791776456155139515748532884515592045355895104612122716853068248451915475812346975718675689358429564580346090676661349352327121063904787804134464718283906528998170511417965573506694175051010998093129770721798413267275424487981039070094706436088874298626529654728883029951014125 / 4646927838993072071243945306718439250410188130185607684549287060362314553626263667328650982800488595593121011844353040782670578892327830336846345565944983205571783876398312106070895030732180427719497486819848241268961714708993375275490934188589556509412640954544199727574266715045888) := by
  show endpointBQ (471 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_472]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_474 : endpointBQ 474 =
    (241032522682348978027150914087898239396369685667809425911136207504217308795189519382435632449315948659489489274959174302273018919935317949311786272873485789200147787042565095089782164536988209736560672320577869132136443076693744486431123127901864913290089222136413781806476329193125 / 9293855677986144142487890613436878500820376260371215369098574120724629107252527334657301965600977191186242023688706081565341157784655660673692691131889966411143567752796624212141790061464360855438994973639696482537923429417986750550981868377179113018825281909088399455148533430091776) := by
  show endpointBQ (472 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_473]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_475 : endpointBQ 475 =
    (963113075865757308825788673591728408052160727119896735602725689900817685354618037363571915314355288525470659676735603646635227498644498303790133335068316634483290946537169388396724513993788331732164374209228869485794141745269941049157272582797747142977698284232843254728831576986875 / 37175422711944576569951562453747514003281505041484861476394296482898516429010109338629207862403908764744968094754824326261364631138622642694770764527559865644574271011186496848567160245857443421755979894558785930151693717671947002203927473508716452075301127636353597820594133720367104) := by
  show endpointBQ (473 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_474]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_476 : endpointBQ 476 =
    (1924198545256007760159312528923263703666316905340593688604182483612370491371647405174799468701732986969835065333099132338224907149923429242730182178904910497104511806871102630712613818484431845923839981314859362404249769507918261169790003539105393765654390887867301576289812982232725 / 74350845423889153139903124907495028006563010082969722952788592965797032858020218677258415724807817529489936189509648652522729262277245285389541529055119731289148542022372993697134320491714886843511959789117571860303387435343894004407854947017432904150602255272707195641188267440734208) := by
  show endpointBQ (474 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_475]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_477 : endpointBQ 477 =
    (15377418626373641847995850546269107413333339302343736116492248251389616279785182204380120123826454374859774345645187183644133501677119169830558010522172856157532695196087551275694922196459619205660267413701102971818836393294371986323279776182262432530565762473628603353374891984061525 / 594806763391113225119224999259960224052504080663757783622308743726376262864161749418067325798462540235919489516077189220181834098217962283116332232440957850313188336178983949577074563933719094748095678312940574882427099482751152035262839576139463233204818042181657565129506139525873664) := by
  show endpointBQ (475 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_476]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_478 : endpointBQ 478 =
    (30722599477849225746624833481330103490370382295877527293536923655292042588333917485899904566051595428178962162263864540907461692029967649577613802992936544901737229605600495525654634912423515939191268019407025434262790529999028308105001313840033748850375621881274756804541450861238225 / 1189613526782226450238449998519920448105008161327515567244617487452752525728323498836134651596925080471838979032154378440363668196435924566232664464881915700626376672357967899154149127867438189496191356625881149764854198965502304070525679152278926466409636084363315130259012279051747328) := by
  show endpointBQ (476 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_477]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_479 : endpointBQ 479 =
    (122761851470066989908061573115775099720936046412397650900952979459430546744179461083825978496147588426405476422435107265969146091584180357098833396896461926281000227085140055343096972139600241514341677650768658115987301071753439473808687258231097197289157819651118798110197010763525125 / 4758454107128905800953799994079681792420032645310062268978469949811010102913293995344538606387700321887355916128617513761454672785743698264930657859527662802505506689431871596616596511469752757984765426503524599059416795862009216282102716609115705865638544337453260521036049116206989312) := by
  show endpointBQ (477 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_478]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_480 : endpointBQ 480 =
    (245267415150008579002118842321078852678362831767566914221736954786377939946095499493155451817981716334175450806410015978147124863561713156040884260605248566703376236577200486353536121790391296720720220275126525713987154750872738155396479553501377907736375852622381398312022002715435375 / 9516908214257811601907599988159363584840065290620124537956939899622020205826587990689077212775400643774711832257235027522909345571487396529861315719055325605011013378863743193233193022939505515969530853007049198118833591724018432564205433218231411731277088674906521042072098232413978624) := by
  show endpointBQ (478 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_479]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_481 : endpointBQ 481 =
    (15680763408590548484202131319060974647903330377673111382576382642675762960553705600929071886229631064298283821556480354869539516277045527776213867061362225031235854058502351094202742719799016903678046082923089210647578760405797059401681592787188094234612296177657584065415273373606834975 / 609082125712499942522086399242199269429764178599687970429244153575809293172901631404100941617625641201581557264463041761466198116575193377911124206019540838720704856247279564366924353468128353022049974592451148679605349870337179684109147725966810350801733675194017346692614286874494631936) := by
  show endpointBQ (479 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_480]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_482 : endpointBQ 482 =
    (31328926477454297491306129308976292383856757781588066608432232265304382962769461709964320338184356450708213622693924368044963565784284308093433526498896254168435874740583699379477829009827141880321418473366088838736638646049835704958453244633030683075805439972409435107825525388848582975 / 1218164251424999885044172798484398538859528357199375940858488307151618586345803262808201883235251282403163114528926083522932396233150386755822248412039081677441409712494559128733848706936256706044099949184902297359210699740674359368218295451933620701603467350388034693385228573748989263872) := by
  show endpointBQ (480 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_481]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_483 : endpointBQ 483 =
    (125185710364267587071069720018855475376157915948835303501743733076714194162435649903301412803616328888099625388606843014221161468258364268439736456508037729312048744295361421171938378989475259878628738547101840463499514589817393294087097404902940032373446633582698282194340169914776702925 / 4872657005699999540176691193937594155438113428797503763433953228606474345383213051232807532941005129612652458115704334091729584932601547023288993648156326709765638849978236514935394827745026824176399796739609189436842798962697437472873181807734482806413869401552138773540914294995957055488) := by
  show endpointBQ (481 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_482]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_484 : endpointBQ 484 =
    (250112237063184723651309067946574604012406602258024985257107044345816143616460459951730565953394942809557222567299386146425301898280168776489328531118543289412271300714334930498800281003817030606370046993692082913617042606985061136219563138160118284141565220304976899208153755626831300875 / 9745314011399999080353382387875188310876226857595007526867906457212948690766426102465615065882010259225304916231408668183459169865203094046577987296312653419531277699956473029870789655490053648352799593479218378873685597925394874945746363615468965612827738803104277547081828589991914110976) := by
  show endpointBQ (482 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_483]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_485 : endpointBQ 485 =
    (1998830853223963865874511311606096215537166813086860832591921585804993478323283179944821960966387683444973836550235590112341049054850605015414716442906044304641870642898858494151569187856950980135205251594216894028658514057475653873754690533891193229461930314338121169704832080092114611125 / 77962512091199992642827059103001506487009814860760060214943251657703589526131408819724920527056082073802439329851269345467673358921624752372623898370501227356250221599651784238966317243920429186822396747833747030989484783403158999565970908923751724902621910424834220376654628719935312887808) := by
  show endpointBQ (483 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_484]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_486 : endpointBQ 486 =
    (3993540405719630899035879300920221098671164210064264220168189725041316867000538971889757691085421990223050819829233581069811291822990177855539918006548364806593758047358750269758495965017289690208276059370713753224268247673595687842615041499671270596595073143492040027719551104348987748825 / 155925024182399985285654118206003012974019629721520120429886503315407179052262817639449841054112164147604878659702538690935346717843249504745247796741002454712500443199303568477932634487840858373644793495667494061978969566806317999131941817847503449805243820849668440753309257439870625775616) := by
  show endpointBQ (484 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_485]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_487 : endpointBQ 487 =
    (15957727300221241164460241980220307353126339292067492007338733428045755875956886179855780732691130668751367679235332539995007260741248817686128643557030708753919913843561096756936212271735754276511259480036884997451705631650458489280572861301155570984748214083665723732163309145361593021025 / 623700096729599941142616472824012051896078518886080481719546013261628716209051270557799364216448656590419514638810154763741386871372998018980991186964009818850001772797214273911730537951363433494579173982669976247915878267225271996527767271390013799220975283398673763013237029759482503102464) := by
  show endpointBQ (485 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_486]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_488 : endpointBQ 488 =
    (31882687193255169718726520424546938510455704581481868014662397588272115949293737685830954112748398646191130907383939551160455985012803079278445934663225625498078185153562519803899249569607574766007095429313940662259773264057281540184799577096559282480821380499808519900194866115886714598475 / 1247400193459199882285232945648024103792157037772160963439092026523257432418102541115598728432897313180839029277620309527482773742745996037961982373928019637700003545594428547823461075902726866989158347965339952495831756534450543993055534542780027598441950566797347526026474059518965006204928) := by
  show endpointBQ (486 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_487]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_489 : endpointBQ 489 =
    (509600328088914597963251760884151886027775606015488874004849797517464148369858922027625905900486699672727092372120345284941714514548901676991553873715491555092233287290548472275438825087989924538638000714444133536119326761571303306232452256871234433095095835857595195126065482999828634975625 / 19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848) := by
  show endpointBQ (487 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_488]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_490 : endpointBQ 490 =
    (1018158528717524667096312822870790169016639605474708854606826691563522439585587253212659529784816984826696051631005270640875368263219380242169219089202526072239492682378048788165856302885411362524027252961169567412655587415245732781572813609331689245672614788615277107644511200185751689920625 / 39916806190694396233127454260736771321349025208709150830050944848744237837379281315699159309852714021786848936883849904879448759767871873214783435965696628406400113459021713530350754428887259743653067134890878479866616209102417407777777105368960883150142418137515120832847169904606880198557696) := by
  show endpointBQ (488 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_489]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_491 : endpointBQ 491 =
    (4068478365773292445254245933022463573335878260243836606775850330778320278997101717939566039425860523042185447129608816152722389917109278600341491789099073570295768718563713320874993144999256015963357880199938802028529877875614581196570549075656015393932611747160637911771332510130003691560375 / 159667224762777584932509817042947085285396100834836603320203779394976951349517125262796637239410856087147395747535399619517795039071487492859133743862786513625600453836086854121403017715549038974612268539563513919466464836409669631111108421475843532600569672550060483331388679618427520794230784) := by
  show endpointBQ (489 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_490]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_492 : endpointBQ 492 =
    (8128670624895315455793106436446103391939911554580862955696760029518395506509484287777422168384458601027258500273210282374380172115446440543655811497161285483625558274767826410953906874224582793604998127242647586130321405694456016606590037969895216092561898419479808129221338477469518577231625 / 319334449525555169865019634085894170570792201669673206640407558789953902699034250525593274478821712174294791495070799239035590078142974985718267487725573027251200907672173708242806035431098077949224537079127027838932929672819339262222216842951687065201139345100120966662777359236855041588461568) := by
  show endpointBQ (490 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_491]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_493 : endpointBQ 493 =
    (64963278246114594252395314040866013286804333806121855979267602512329941324380675242969154402617258575689391103809477297349721212922632935401737095135849948214666047025177019202989353311892397448078968773004248594846389770712603774994130140848837377390149155661371149520525005880914933019664125 / 2554675596204441358920157072687153364566337613357385653123260470319631221592274004204746195830573697394358331960566393912284720625143799885746139901804584218009607261377389665942448283448784623593796296633016222711463437382554714097777734743613496521609114760800967733302218873894840332707692544) := by
  show endpointBQ (491 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_492]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_494 : endpointBQ 494 =
    (129794785136760396224359805943718099568970119267809387707055960394817428406724067169015450479874238736417951799700476953122668143466112457141401701234913182538430134522919602261550736333091301189366702315231612304104855829922747907442633242872423563345429854617546820035937384975053162321235625 / 5109351192408882717840314145374306729132675226714771306246520940639262443184548008409492391661147394788716663921132787824569441250287599771492279803609168436019214522754779331884896566897569247187592593266032445422926874765109428195555469487226993043218229521601935466604437747789680665415385088) := by
  show endpointBQ (492 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_493]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_495 : endpointBQ 495 =
    (518653655586973729042279872333804713662240921932501480432648716233541707843873094315053642200954953979127604964795023290413252864781591073678394652303074134272998148883083592842714885671097628639291235567342515563366367223213571597756595185081303874582750066832059560224575704333512029194573125 / 20437404769635530871361256581497226916530700906859085224986083762557049772738192033637969566644589579154866655684531151298277765001150399085969119214436673744076858091019117327539586267590276988750370373064129781691707499060437712782221877948907972172872918086407741866417750991158722661661540352) := by
  show endpointBQ (493 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_494]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_496 : endpointBQ 496 =
    (1036259526011145490955181401491177498610012670285341341712908243141359089005233313692097075023726160576479194566024804109532741582361603175490772345712606704638374079283575097619080852381243544897492993891114642206402701381329742040770247753627089963560282456761428091034556306234027064390773375 / 40874809539271061742722513162994453833061401813718170449972167525114099545476384067275939133289179158309733311369062302596555530002300798171938238428873347488153716182038234655079172535180553977500740746128259563383414998120875425564443755897815944345745836172815483732835501982317445323323080704) := by
  show endpointBQ (494 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_495]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_497 : endpointBQ 497 =
    (33126877105711134888276928028314738745887824395250750633467486095260866361425361737705425849952020165525512316610663899114417642197430604739075980471006233686988022986129771669048681442252011386884372804712729368598228292545089495561397274962724069480265803698405652845653074176707123251976013375 / 1307993905256673975767120421215822522657964858038981454399109360803651185455244290152830052265253733065911465963809993683089776960073625541502023629723947119620918917825223508962533521125777727280023703876104306028269279939868013618062200188730110219063866757530095479450736063434158250346338582528) := by
  show endpointBQ (495 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_496]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_498 : endpointBQ 498 =
    (66187100535153233287845049360395443812206457996949688891414916886507123333793529588614663720326672081220993421316678575091784142257643039247288628989354507145229591197639563918240122076773133414841412867363662501042335401402965531373174032269587527150712159099631415041717309169960107422962135375 / 2615987810513347951534240842431645045315929716077962908798218721607302370910488580305660104530507466131822931927619987366179553920147251083004047259447894239241837835650447017925067042251555454560047407752208612056538559879736027236124400377460220438127733515060190958901472126868316500692677165056) := by
  show endpointBQ (496 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_497]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_499 : endpointBQ 499 =
    (264482590491877377997613751460214725273676408461706588140392940972187099265560489721572652215763207714116017888393956555085643460025521381731133276483565199234953587315868940155216552073852480914727734148702185496133027005606227725768305871920640921746821679936278144443810131020523320826696083125 / 10463951242053391806136963369726580181263718864311851635192874886429209483641954321222640418122029864527291727710479949464718215680589004332016189037791576956967351342601788071700268169006221818240189631008834448226154239518944108944497601509840881752510934060240763835605888507473266002770708660224) := by
  show endpointBQ (497 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_498]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_500 : endpointBQ 500 =
    (528435155752308107943128076564797757711133024521686309370684894086714504945418453411639146811855547276500340350157865101042858776844578792757394542393015037349195844797437541753007820476214275494957015924360879638566388626431681448078158225059877753470102635063064749519997396047017536802036061875 / 20927902484106783612273926739453160362527437728623703270385749772858418967283908642445280836244059729054583455420959898929436431361178008664032378075583153913934702685203576143400536338012443636480379262017668896452308479037888217888995203019681763505021868120481527671211777014946532005541417320448) := by
  show endpointBQ (498 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_499]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_501 : endpointBQ 501 =
    (4223253764772446398681479587905863679627375131977316984490513673541022323523784279665820061320349533833790720078461657887534527344541873711717097182804976178494773191621120833690038501245904489755696471267492150071422577902441998133040640534678543005733060259424013478163819189207764154121872206505 / 167423219872854268898191413915625282900219501828989626163085998182867351738271269139562246689952477832436667643367679191435491450889424069312259024604665231311477621481628609147204290704099549091843034096141351171618467832303105743111961624157454108040174944963852221369694216119572256044331338563584) := by
  show endpointBQ (499 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_500]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_502 : endpointBQ 502 =
    (8438077881311814062036249635716106872868268477264060481986036301825475740214187752386199364035269228278691638320439360370103915911948933304249130299376808691962610708209065777492472135223853082326251831813891501440107785389909062138071219910605232632213160318729416150982002012768407022506974209005 / 334846439745708537796382827831250565800439003657979252326171996365734703476542538279124493379904955664873335286735358382870982901778848138624518049209330462622955242963257218294408581408199098183686068192282702343236935664606211486223923248314908216080349889927704442739388432239144512088662677127168) := by
  show endpointBQ (500 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_501]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_503 : endpointBQ 503 =
    (33718693685082667347499435795311773679230570847393835312478065381398215806513268189814175147917828828539951048746616248809618436891174422725744532630577446685412344782205948106872308970635556340929205527128817434041546249984377646711097344901741228406811951393169738643167123580903236030177271440765 / 1339385758982834151185531311325002263201756014631917009304687985462938813906170153116497973519619822659493341146941433531483931607115392554498072196837321850491820971853028873177634325632796392734744272769130809372947742658424845944895692993259632864321399559710817770957553728956578048354650708508672) := by
  show endpointBQ (501 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_502]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_504 : endpointBQ 504 =
    (67370352193853043109814976092024517987329470579782911509026750911143552456353547774877228675263256406923759053658746183009277393788529413199549215295686548546400410548940313811941690885663487321339665118816026881136687835455863886569886345181411400693530837276611505638932324450910044155721983693775 / 2678771517965668302371062622650004526403512029263834018609375970925877627812340306232995947039239645318986682293882867062967863214230785108996144393674643700983641943706057746355268651265592785469488545538261618745895485316849691889791385986519265728642799119421635541915107457913156096709301417017344) := by
  show endpointBQ (502 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_503]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_505 : endpointBQ 505 =
    (1076856264431904990660058427375693485924456775775260188723649812182881862278540041417482051999842844472575005825942181052227656119762684430030889838138989752162304974964807873152782265426398916390302266264249826496899121433397697361521834120598115563466437351389647399657219852731212928012889485390975 / 42860344287450692837937001962400072422456192468221344297750015534814042044997444899727935152627834325103786916702125873007485811427692561743938310298794299215738271099296923941684298420249484567511816728612185899934327765069595070236662175784308251658284785910746168670641719326610497547348822672277504) := by
  show endpointBQ (503 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_504]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_506 : endpointBQ 506 =
    (2151580140221370565497027630142722232272825518331163426578539921767381780275340399584632456371963227866986496788862694419203376286812967504754787815212357742439140039088101275269618427356903973540227696357679356307665769359006488391634714114224749709975515420895354903473534319615433355178228694573255 / 85720688574901385675874003924800144844912384936442688595500031069628084089994889799455870305255668650207573833404251746014971622855385123487876620597588598431476542198593847883368596840498969135023633457224371799868655530139190140473324351568616503316569571821492337341283438653220995094697645344555008) := by
  show endpointBQ (504 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_505]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_507 : endpointBQ 507 =
    (8597816291556544038409070885669139038845164423054570056406734628090209406554818750909341554909307602266890704559447367817449064924774348408328420874228038251406998338016088495247368498252292163040198422994521064138537916292314465470129233080953446469506901543577880661706494850320960956858455376338185 / 342882754299605542703496015699200579379649539745770754382000124278512336359979559197823481221022674600830295333617006984059886491421540493951506482390354393725906168794375391533474387361995876540094533828897487199474622120556760561893297406274466013266278287285969349365133754612883980378790581378220032) := by
  show endpointBQ (505 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_506]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_508 : endpointBQ 508 =
    (17178674365575501204947512440202835988856314715097198160039491475848879938540495847477639043635362132339961111871242965678650695796442633013090119024838269721253036127042007190701349681912370732070455626219822165625915008292139158819015607714015466022900377245846929211654199769970677414788195850553415 / 685765508599211085406992031398401158759299079491541508764000248557024672719959118395646962442045349201660590667234013968119772982843080987903012964780708787451812337588750783066948774723991753080189067657794974398949244241113521123786594812548932026532556574571938698730267509225767960757581162756440064) := by
  show endpointBQ (506 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_507]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_509 : endpointBQ 509 =
    (137294129772119163173399410447290382115662672723020914428662077543201678248965380198344910466849547750591027783852847324124649261680230492191232053623707431236786076133445962980802125410559498370484350083567870063860659318240324773238589305745871637899558133106571914565582777689135728944960777860722175 / 5486124068793688683255936251187209270074392635932332070112001988456197381759672947165175699536362793613284725337872111744958183862744647903224103718245670299614498700710006264535590197791934024641512541262359795191593953928908168990292758500391456212260452596575509589842140073806143686060649302051520512) := by
  show endpointBQ (507 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_508]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_510 : endpointBQ 510 =
    (274318526479853023472194892779753081751726794026153772050981007586318480902156761614374801463233772224658301092688302020893454418720617702472461686709843728031063731685097336643370847824241669632185823251450930952743203392240491737492426962561004824644107311138278265448325510628391034060953066963368275 / 10972248137587377366511872502374418540148785271864664140224003976912394763519345894330351399072725587226569450675744223489916367725489295806448207436491340599228997401420012529071180395583868049283025082524719590383187907857816337980585517000782912424520905193151019179684280147612287372121298604103041024) := by
  show endpointBQ (508 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_509]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_511 : endpointBQ 511 =
    (1096198346992040121247712140166934863941214129853532132235096653844935419761951921902148716435432211360497289464507371605060510010495331132625248857871885328877074284655349749174881936991773573941950407424425484866060095124286514041195227744508485946322922941372178637222916452275805740031808530335969695 / 43888992550349509466047490009497674160595141087458656560896015907649579054077383577321405596290902348906277802702976893959665470901957183225792829745965362396915989605680050116284721582335472197132100330098878361532751631431265351922342068003131649698083620772604076718737120590449149488485194416412164096) := by
  show endpointBQ (509 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_510]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_512 : endpointBQ 512 =
    (2190251491739477424254235019785597839694676372955883183976582551028726151813997871354391075304454574949251922785248583970189394756782256529178824038918189668852236486561863197470752363343641524451529091938039960955474280081989297135147411990495428867310575974835605457151854594468879961981363032236839645 / 87777985100699018932094980018995348321190282174917313121792031815299158108154767154642811192581804697812555605405953787919330941803914366451585659491930724793831979211360100232569443164670944394264200660197756723065503262862530703844684136006263299396167241545208153437474241180898298976970388832824328192) := by
  show endpointBQ (510 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_511]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_513 : endpointBQ 513 =
    (2240627276049485405012082425240666590007653929533868497208043949702386853305719822395542070036457030173084717009309301401503750836188248429349936991813308031235837925752786051012579667700545279513914261052614880057450188523875050969255802466276823731258719222256824382666347250141664201106934381978286956835 / 89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608) := by
  show endpointBQ (511 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_512]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_514 : endpointBQ 514 =
    (4476886857603747641593342077722579443972407948873713858943947462855646246858407052544699067811634417012498703576105329310996773113241626978720634340367720725178818467634708971321431109927990080900121086898499516683989168103259117433698240795192484063431164138037514604742701620653422624044069671594043139875 / 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216) := by
  show endpointBQ (512 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_513]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_515 : endpointBQ 515 =
    (17890127637194742521075339742494510073773007640051767055001688888532096091531455420091073706780344538022708827130973436585189439639296307031696853959368284765597846561326249469054901750568271646242896327800618691184657103665552971223377794928648564720403912722819173148135231768136439824487391255747401963625 / 719077253944926363091722076315609893447190791576922629093720324630930703222003852530833909289630144084480455519485573430635159075257666489971389722557896497511071573699461941105208878404984376477812331808340023075352602729369851525895652442163308948653402042738345192959788983753918865219341425318496896548864) := by
  show endpointBQ (513 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_514]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_516 : endpointBQ 516 =
    (35745517162472602046964125427236603623130922061384986989508228866601023064438577917036339503450435979855082297316061487856621229881234757156536044124640708784078027401174195541082512429776216551425126837489003171318470212955056325026904370838018200188923546003458114892099327163907566173587428353716653632175 / 1438154507889852726183444152631219786894381583153845258187440649261861406444007705061667818579260288168960911038971146861270318150515332979942779445115792995022143147398923882210417756809968752955624663616680046150705205458739703051791304884326617897306804085476690385919577967507837730438682850636993793097728) := by
  show endpointBQ (514 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_515]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_517 : endpointBQ 517 =
    (285687040267513586902480723375821227406573493374324973536302201251671742476249409553988108744631003838996820531262475922326949519438395617274330709244221478731662374035741051184930777636428521430382215267063273407979401469431496675215026405689897398409148650616785398866313227178206982364097973896758681354825 / 11505236063118821809467553221049758295155052665230762065499525194094891251552061640493342548634082305351687288311769174890162545204122663839542235560926343960177145179191391057683342054479750023644997308933440369205641643669917624414330439074612943178454432683813523087356623740062701843509462805095950344781824) := by
  show endpointBQ (515 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_516]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_518 : endpointBQ 518 =
    (570821494383639333211339627170644734837505645368815662791102850856821876166277833789689973565191154672502351274263322297415355616208631861981399656961858389806203544253231152560993217211664724637494832438832420561784761543370862795932538253535133486569923706164679530036560084477926136909309878211512026768925 / 23010472126237643618935106442099516590310105330461524130999050388189782503104123280986685097268164610703374576623538349780325090408245327679084471121852687920354290358382782115366684108959500047289994617866880738411283287339835248828660878149225886356908865367627046174713247480125403687018925610191900689563648) := by
  show endpointBQ (516 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_517]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_519 : endpointBQ 519 =
    (2281082033540798107620604301627866025315900938056850235477959268867994756108484779815942558455493610370810554319932581381563293678671559757338797856971132947681160881475267347106671736733872548261803674031627626569294317364435687234711108464899085554439656509190900824663473696658894022012107042273802886895125 / 92041888504950574475740425768398066361240421321846096523996201552759130012416493123946740389072658442813498306494153399121300361632981310716337884487410751681417161433531128461466736435838000189159978471467522953645133149359340995314643512596903545427635461470508184698852989920501614748075702440767602758254592) := by
  show endpointBQ (517 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_518]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_520 : endpointBQ 520 =
    (4557768918654735332567565820400957742297859870452704613084092026620636921164737411693896788281978562532814151887803635631370203361815814004547848511905712652688562300751160383332598441219702952885337976822346529387973424098111382779181925776686612177175190366148293169895996576946576302170626209707001143950375 / 184083777009901148951480851536796132722480842643692193047992403105518260024832986247893480778145316885626996612988306798242600723265962621432675768974821503362834322867062256922933472871676000378319956942935045907290266298718681990629287025193807090855270922941016369397705979841003229496151404881535205516509184) := by
  show endpointBQ (518 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_519]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_521 : endpointBQ 521 =
    (72854183176650307854426167498409155296115021621544001430682640240905257862925571857691673277307318868793752366329661191092209866045025088472695609290308237632975634315083932896654919698881097969967171660283354523601605963660580410885692628953498308493615735237355024669568314514576811968542778952085756747145225 / 2945340432158418383223693624588738123559693482299075088767878449688292160397327779966295692450325070170031945807812908771881611572255401942922812303597144053805349165872996110766935565946816006053119311086960734516644260779498911850068592403100913453684334767056261910363295677456051671938422478104563288264146944) := by
  show endpointBQ (519 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_520]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_522 : endpointBQ 522 =
    (145568531068892457728325605308721555975538843585465077714665313801885553618628637819303324149091974937455462981476347984504780173805894658541412916067583254080475307719774230605408390415614631452467995582255224681514917098216246080099819629060636735397032591904196891902150893300718735622366665814052346974622225 / 5890680864316836766447387249177476247119386964598150177535756899376584320794655559932591384900650140340063891615625817543763223144510803885845624607194288107610698331745992221533871131893632012106238622173921469033288521558997823700137184806201826907368669534112523820726591354912103343876844956209126576528293888) := by
  show endpointBQ (520 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_521]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_523 : endpointBQ 523 =
    (581716390440056832990971671789258938247076681454559678376995870863473687449155820864112517576639578006766467010267551524285385905285625014784266940453982122628106306328446446442302495032513642164460227556675093267509802810113197936950620203487525344900785415157384514382924834148082916682484415494469723733835175 / 23562723457267347065789548996709904988477547858392600710143027597506337283178622239730365539602600561360255566462503270175052892578043215543382498428777152430442793326983968886135484527574528048424954488695685876133154086235991294800548739224807307629474678136450095282906365419648413375507379824836506306113175552) := by
  show endpointBQ (521 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_522]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_524 : endpointBQ 524 =
    (1162320512447149886186549516290201893820640787992380236910058671228164442417529317022939925177033191237229365249960977711048237611899575794358621324616465235461512600598903511533854889692116168378319192727964574502003334486746255916086803274654806855490097053230338083231656695381924757042440180098892660232997625 / 47125446914534694131579097993419809976955095716785201420286055195012674566357244479460731079205201122720511132925006540350105785156086431086764996857554304860885586653967937772270969055149056096849908977391371752266308172471982589601097478449614615258949356272900190565812730839296826751014759649673012612226351104) := by
  show endpointBQ (522 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_523]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_525 : endpointBQ 525 =
    (9289691423909663594177994988975888418551228282656657313319323883785405887108039655900901539392013368132665232188619417278377899081365311883156309365446100011665677044481312798289664652730119299939696143405945874073263291661246793466739565103538799829756729883451633382775149313472329928423166935599546681404187125 / 377003575316277553052632783947358479815640765734281611362288441560101396530857955835685848633641608981764089063400052322800846281248691448694119974860434438887084693231743502178167752441192448774799271819130974018130465379775860716808779827596916922071594850183201524526501846714374614008118077197384100897810808832) := by
  show endpointBQ (523 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_524]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_526 : endpointBQ 526 =
    (18561688197488070686271841416068013240114739940013016231756134769696934810621587807695325171089946710802220625839736702333368411688289927934154225760672302689975800418401708810296872801359800277403316675110166136957815605624091212088780578654499430516980589805220501749583107866347569704601718315131284702462842465 / 754007150632555106105265567894716959631281531468563222724576883120202793061715911671371697267283217963528178126800104645601692562497382897388239949720868877774169386463487004356335504882384897549598543638261948036260930759551721433617559655193833844143189700366403049053003693428749228016236154394768201795621617664) := by
  show endpointBQ (524 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_525]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_527 : endpointBQ 527 =
    (74176176028745103769093936609458106142055481661420836728424705866735659642445964965352801349108494270164007139762598000579354375225827810869947115112040266643211278478099604409209176099730608713121238880383211444648913313729733322833872198349349435259873003366109305470767476682628500986830440871494221377522613805 / 3016028602530220424421062271578867838525126125874252890898307532480811172246863646685486789069132871854112712507200418582406770249989531589552959798883475511096677545853948017425342019529539590198394174553047792145043723038206885734470238620775335376572758801465612196212014773714996912064944617579072807182486470656) := by
  show endpointBQ (525 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_526]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_528 : endpointBQ 528 =
    (148211600300319913223635512807892572614012186317791539041804962576228936629023911021852940836074467678335293203358663557134839007804168282440330763212482733918978133277872644104169378430771026517868433664219206169289005160070985178261987523457049251098000517162263944327738430639104006715621355289721850304613495895 / 6032057205060440848842124543157735677050252251748505781796615064961622344493727293370973578138265743708225425014400837164813540499979063179105919597766951022193355091707896034850684039059079180396788349106095584290087446076413771468940477241550670753145517602931224392424029547429993824129889235158145614364972941312) := by
  show endpointBQ (526 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_527]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_529 : endpointBQ 529 =
    (4738279948995076013664711091282626185084328986826365869366795015694591761927885640244086441880562527292234373622526971296280459188890834484077241066338463160137028200247140591815111946801922211404581742901553409351512134662875435244436267795369301815405774109278438220174668009825900820756985752444137941556582974825 / 193025830561934107162947985381047541665608072055952185017491682078771915023799273387871154500424503798663213600460826789274033295999330021731389427128542432710187362934652673115221889249890533772697227171395058697282798274445240687006095271729621464100656563293799180557568945517759802372156455525060659659679134121984) := by
  show endpointBQ (527 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_528]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_530 : endpointBQ 530 =
    (9467602847046872110479394373318971413297042985019789648243293632493730609371975655459356085194243083833443729525540659092946021479503992532456793586237723176304043114671507760961386252872649862863219096875126566511433509146804036017711030358611251453466735791129128920084355550824153435803655841840177323677331199225 / 386051661123868214325895970762095083331216144111904370034983364157543830047598546775742309000849007597326427200921653578548066591998660043462778854257084865420374725869305346230443778499781067545394454342790117394565596548890481374012190543459242928201313126587598361115137891035519604744312911050121319319358268243968) := by
  show endpointBQ (528 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_529]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_531 : endpointBQ 531 =
    (37834684584991085150934636382433172553515352909947008443357162101173059303112914034458332431021522361432516639877537954639357874516206521101402809086134901297003704371460855542860785063366551716121317070153807675228709759194209336387758419433091755808382163029455651042903141616312371654777628439655652021789787698035 / 1544206644495472857303583883048380333324864576447617480139933456630175320190394187102969236003396030389305708803686614314192266367994640173851115417028339461681498903477221384921775113999124270181577817371160469578262386195561925496048762173836971712805252506350393444460551564142078418977251644200485277277433072975872) := by
  show endpointBQ (529 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_530]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_532 : endpointBQ 532 =
    (75598117409935106111377870436462516156835761652455321955559225968633928287387573993522204725638107769265348690979411995993142570361007756852332166554405141762939605156534779154379082772564804841440145784243295561991828727881461593045973037699642849176447222173733419503804582400955605133180911063040766092502758470085 / 3088413288990945714607167766096760666649729152895234960279866913260350640380788374205938472006792060778611417607373228628384532735989280347702230834056678923362997806954442769843550227998248540363155634742320939156524772391123850992097524347673943425610505012700786888921103128284156837954503288400970554554866145951744) := by
  show endpointBQ (530 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_531]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_533 : endpointBQ 533 =
    (604216532381661787942817114841801914847491839372631633374131257177878689996187903421910553559047432772398989913617405652185793626268806357398714985318290719503795490837567445421841842009296146965796052395869347236070029607052584010585483752441506381011754865944952067161987000693351941778731642556483716964890468072935 / 24707306311927565716857342128774085333197833223161879682238935306082805123046306993647507776054336486228891340858985829027076261887914242781617846672453431386903982455635542158748401823985988322905245077938567513252198179128990807936780194781391547404884040101606295111368825026273254703636026307207764436438929167613952) := by
  show endpointBQ (531 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_532]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_534 : endpointBQ 534 =
    (1207299450256040908366041702263637972443862680922800543233489284980189127290694403647907578875019729648414492041280557259996004150049303509624074032577822919834037894450298929407620190881614252380061530584616988379764693304898690377623902807411265095267390116756799158588210423524239808619792118804231066730972511252675 / 49414612623855131433714684257548170666395666446323759364477870612165610246092613987295015552108672972457782681717971658054152523775828485563235693344906862773807964911271084317496803647971976645810490155877135026504396358257981615873560389562783094809768080203212590222737650052546509407272052614415528872877858335227904) := by
  show endpointBQ (532 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_533]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_535 : endpointBQ 535 =
    (4824676080236687824818601109795137515346822024511716028577277404771017973105509096225907815204666859681117089917776608975339836809373059343703696602099389720834900499544827556846182560564353585354028663422420698880932313694108249561515746425122920811424364249361440832260751018353422755795199216344998307872463181672675 / 197658450495420525734858737030192682665582665785295037457911482448662440984370455949180062208434691889831130726871886632216610095103313942252942773379627451095231859645084337269987214591887906583241960623508540106017585433031926463494241558251132379239072320812850360890950600210186037629088210457662115491511433340911616) := by
  show endpointBQ (533 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_534]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_536 : endpointBQ 536 =
    (9640334074342092120992681469852340194216360269538363429063756160187323763083718175449524213932315650465633960975893822419884645886392150352185517135783640395462632960772748893959942349987465388305526432146855564679844193157012558469645482109264303453107748378630617289134098763775343786813211144435146151618061946183345 / 395316900990841051469717474060385365331165331570590074915822964897324881968740911898360124416869383779662261453743773264433220190206627884505885546759254902190463719290168674539974429183775813166483921247017080212035170866063852926988483116502264758478144641625700721781901200420372075258176420915324230983022866681823232) := by
  show endpointBQ (534 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_535]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_537 : endpointBQ 537 =
    (154101459606274338232584505286744124597100326099635630336228102202397369406905405461290155718231493457443193615002720653905917249915313328764040132125735505425977311955039015901956690400545901953361474758646004623464375087629260449567019572224209985048931321097214792786009250388110346204133569189403604901237975288990485 / 6325070415853456823515479584966165845298645305129441198653167438357198111499854590373761990669910140474596183259900372230931523043306046152094168748148078435047419508642698792639590866940413010663742739952273283392562733857021646831815729864036236135650314266011211548510419206725953204130822734645187695728365866909171712) := by
  show endpointBQ (535 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_536]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_538 : endpointBQ 538 =
    (307915951876224143246858797342041798310407169282884602142966021719129194364263501042764128651140395679397666199065026557990780650203223839411201232348071130953582226681111478701675100185820768707554678614575722459920436627609304399227955309118393508300751038244527882047277328987788457126695195046983366962808840754351565 / 12650140831706913647030959169932331690597290610258882397306334876714396222999709180747523981339820280949192366519800744461863046086612092304188337496296156870094839017285397585279181733880826021327485479904546566785125467714043293663631459728072472271300628532022423097020838413451906408261645469290375391456731733818343424) := by
  show endpointBQ (536 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_537]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_539 : endpointBQ 539 =
    (1230519138538813955354547238448680049009991475758739581054603990141501427292131091527774863568683737380492532208159492750334904085384630585007588567933741508457624140082508697413757370631068127734651596693936437339830741169814134680929561179562353239491848944657499900374807169746738258034190835224933529684087374761813875 / 50600563326827654588123836679729326762389162441035529589225339506857584891998836722990095925359281123796769466079202977847452184346448369216753349985184627480379356069141590341116726935523304085309941919618186267140501870856173174654525838912289889085202514128089692388083353653807625633046581877161501565826926935273373696) := by
  show endpointBQ (537 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_538]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_540 : endpointBQ 540 =
    (2458755310215774823593408860499496127613656436720153114648995356924669827817486429638986137409039675619277286063428151562357498515694336066889003502160741381463564376380077675537322241502152826660890110648180970343223948497012658722376878275303626046257367928378715014292518222295430619485757939772269780092323010423884125 / 101201126653655309176247673359458653524778324882071059178450679013715169783997673445980191850718562247593538932158405955694904368692896738433506699970369254960758712138283180682233453871046608170619883839236372534281003741712346349309051677824579778170405028256179384776166707307615251266093163754323003131653853870546747392) := by
  show endpointBQ (538 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_539]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_541 : endpointBQ 541 =
    (19651829479428303960424356744288565345889891075711446005231599926827546253444947093188637350106324518468149567869918337302101784432845841601283220583936592226660636756400768977072375545043132592348892069551016792595101040209456731566256678955945277806753333294226914817937978976716812136482465311216882168293455764795340525 / 809609013229242473409981386875669228198226599056568473427605432109721358271981387567841534805748497980748311457267247645559234949543173907468053599762954039686069697106265445457867630968372865364959070713890980274248029933698770794472413422596638225363240226049435078209333658460922010128745310034584025053230830964373979136) := by
  show endpointBQ (539 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_540]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_542 : endpointBQ 542 =
    (39267333950576703477298945731193972530327120615238582498438742182810679297548960827609828050766981154277393129144883036272776393663412855399236897322061841399297871226745344296146465737877312998759985817346856104982078048921298940523333585862064409074122649336523650495731895145713260479736682072875137937015204587326734025 / 1619218026458484946819962773751338456396453198113136946855210864219442716543962775135683069611496995961496622914534495291118469899086347814936107199525908079372139394212530890915735261936745730729918141427781960548496059867397541588944826845193276450726480452098870156418667316921844020257490620069168050106461661928747958272) := by
  show endpointBQ (540 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_541]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_543 : endpointBQ 543 =
    (156924437891050073305958517442372960333373696038019870279738589608796921325629241978972117265611219889603013870346525196617774296448251374160050036161597690905681160658912206172422960863915608773642304945338174028397013014692866245707639385566847804528689406758136950136079861412573657193929249759866326146817219808394291325 / 6476872105833939787279851095005353825585812792452547787420843456877770866175851100542732278445987983845986491658137981164473879596345391259744428798103632317488557576850123563662941047746982922919672565711127842193984239469590166355779307380773105802905921808395480625674669267687376081029962480276672200425846647714991833088) := by
  show endpointBQ (541 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_542]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_544 : endpointBQ 544 =
    (313559880500532835243029450138074883907385746226982613726549483840782061949001339865901928606239730350311731214228323827495921015923301548736011582385512881459786481242946120989095603199536713663723574338290826557662539817572301798513423081657513568901709035603275489682590514977242022201497672172108589077894444736846788375 / 12953744211667879574559702190010707651171625584905095574841686913755541732351702201085464556891975967691972983316275962328947759192690782519488857596207264634977115153700247127325882095493965845839345131422255684387968478939180332711558614761546211605811843616790961251349338535374752162059924960553344400851693295429983666176) := by
  show endpointBQ (542 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_543]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_545 : endpointBQ 545 =
    (20049387653181128935833706605887494047489900361690005948279958172642947137562615084366788023234269817105226578227422823558121537900507575498590858238414853067458112065357790206773348275170376926615736782689536968716422398923593650293181817044806897023303395394162379840292699398838945772531057038298943313392427142879556409625 / 829039629546744292771820940160685289674984037433926116789867962480354670870508940869469731641086461932286270932241661589052656588332210081247286886157264936638535369836815816148856454111613814133718088411024363800829982652107541293539751344738957542771957991474621520086357666263984138371835197475414041654508370907518954635264) := by
  show endpointBQ (543 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_544]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_546 : endpointBQ 546 =
    (40061987439108714515821846777635744986635782557578745830599769633042512720744381333716389279453430882252461915026905421751916247291105962785257696553456467872407126677384648688396653709468881601989976800640194053086576132895033917741788988553751763042894307494023544304731650725386443938140038742582659207861198456139150330425 / 1658079259093488585543641880321370579349968074867852233579735924960709341741017881738939463282172923864572541864483323178105313176664420162494573772314529873277070739673631632297712908223227628267436176822048727601659965304215082587079502689477915085543915982949243040172715332527968276743670394950828083309016741815037909270528) := by
  show endpointBQ (544 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_545]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_547 : endpointBQ 547 =
    (160101202549698196105353973752383142052819189634865976927415196592122276111106666795181614299940267738232366114631332656158756871042478408053905300145864492486432876208888834135680399989122893142018551976184804805558441615342424924015720829714810159266658203208716801598762750701086484749123744572006158226287793097611036668475 / 6632317036373954342174567521285482317399872299471408934318943699842837366964071526955757853128691695458290167457933292712421252706657680649978295089258119493108282958694526529190851632892910513069744707288194910406639861216860330348318010757911660342175663931796972160690861330111873106974681579803312333236066967260151637082112) := by
  show endpointBQ (545 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_546]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_548 : endpointBQ 548 =
    (319909715515210472290954101117650409988539989526340974006699835238006668719267983194028344478674063323378384210771565983878466654569339853753050261534606746412561487561819919031624638369490534194197947550219363167231035988243638833545124071075479897766832570579757704108679500029776102067261888148451062049968113081698104348525 / 13264634072747908684349135042570964634799744598942817868637887399685674733928143053911515706257383390916580334915866585424842505413315361299956590178516238986216565917389053058381703265785821026139489414576389820813279722433720660696636021515823320684351327863593944321381722660223746213949363159606624666472133934520303274164224) := by
  show endpointBQ (546 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_547]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_549 : endpointBQ 549 =
    (2556942616709163993858355771706767875455848821396666909031651967778228483559112712390226548935387586416783435845217990893043218881411876933281679097667112316217188531972210301749116635143008284252896004142264253051956090562969230092933655896552193343464829669962296978094920091478867385136144288485794984997920319886565140595875 / 106117072581983269474793080340567717078397956791542542949103099197485397871425144431292125650059067127332642679326932683398740043306522890399652721428129911889732527339112424467053626126286568209115915316611118566506237779469765285573088172126586565474810622908751554571053781281789969711594905276852997331777071476162426193313792) := by
  show endpointBQ (547 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_548]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_550 : endpointBQ 550 =
    (5109227778743083608857224556579825791211413765158731510396579615032270758587152359730561974830820004187998960149734309671527160497101692159945358779855778161913034279733177961782843258200145879463437006455489773402542497900869299475315520070159847172642838156554899426175095337618064702175501428905131327035917287642189361081375 / 212234145163966538949586160681135434156795913583085085898206198394970795742850288862584251300118134254665285358653865366797480086613045780799305442856259823779465054678224848934107252252573136418231830633222237133012475558939530571146176344253173130949621245817503109142107562563579939423189810553705994663554142952324852386627584) := by
  show endpointBQ (548 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_549]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_551 : endpointBQ 551 =
    (20418332104867814131396690137022649252877613556034348836093967261528965686135565248523227673960258853100403117107483659378212179586599126122836179269314546181608816994279136654543071784588946623746608254889393676252342564338383127721351842025838807428125378669286670797696108276517284027966822074060870285136265814977331301194295 / 848936580655866155798344642724541736627183654332340343592824793579883182971401155450337005200472537018661141434615461467189920346452183123197221771425039295117860218712899395736429009010292545672927322532888948532049902235758122284584705377012692523798484983270012436568430250254319757692759242214823978654216571809299409546510336) := by
  show endpointBQ (549 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_550]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_552 : endpointBQ 552 =
    (40799607345661458001211898077789359033426955581114007383919161442728477714038579561931168183357976401567230185000616168739404010389919487951438536071715635836572245935937077053814740535086080277214184552873361955633083781010090423994933535518055402864548170444436705169262096574311306197443686213323082003511848751887553108194045 / 1697873161311732311596689285449083473254367308664680687185649587159766365942802310900674010400945074037322282869230922934379840692904366246394443542850078590235720437425798791472858018020585091345854645065777897064099804471516244569169410754025385047596969966540024873136860500508639515385518484429647957308433143618598819093020672) := by
  show endpointBQ (550 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_551]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_553 : endpointBQ 553 =
    (652202418873399828628068457678284971215506260956068842673374421323616100269341351547972152264403593781574708609502603393037139470435959350875894279523222410546944743004907188266053026234781833996626747272743742566134658122523619386469734632991523324052125101452372257995595543789353199069280954975295064490921292367130015628087415 / 27165970580987716985547028567185335572069876938634890994970393394556261855084836974410784166415121184597156525907694766950077451086469859942311096685601257443771526998812780663565728288329361461533674321052446353025596871544259913106710572064406160761551519464640397970189768008138232246168295750874367316934930297897581105488330752) := by
  show endpointBQ (551 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_552]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_554 : endpointBQ 554 =
    (1303225448200916474925887243642865991307657176051457633190015796677388410122282447487358459768835390829367184472875907322434067115428092373811687484399929048199591213418485430441209030722303664676803898257471673662891134223125857906056160523427908269579743647567579285868233410284331437561583101713745110782039833753487644247805775 / 54331941161975433971094057134370671144139753877269781989940786789112523710169673948821568332830242369194313051815389533900154902172939719884622193371202514887543053997625561327131456576658722923067348642104892706051193743088519826213421144128812321523103038929280795940379536016276464492336591501748734633869860595795162210976661504) := by
  show endpointBQ (552 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_553]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_555 : endpointBQ 555 =
    (5208197007792110244559412197518601633132045104292287364409196703689057653448977145734678032361374648549131672243587109768716650890898549667182447816717405979627969217524416503604398545160975295296830019389968024349532438935019222750917580142363517886010022447138304221863301029547851629533113695296447067276960635253107661308018025 / 217327764647901735884376228537482684576559015509079127959763147156450094840678695795286273331320969476777252207261558135600619608691758879538488773484810059550172215990502245308525826306634891692269394568419570824204774972354079304853684576515249286092412155717123183761518144065105857969346366006994938535479442383180648843906646016) := by
  show endpointBQ (553 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_554]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_556 : endpointBQ 556 =
    (10407009876831441912101600228915548128186374812000264301134773233137234121936784963278843131331107180614391035167816404925237415924336020866496098430161447263797149301323563788283383759609948833304836921627882052258795450052137509965347020500686741145198405214191674562245767282465887310184185744295062698396665485577831344847913495 / 434655529295803471768752457074965369153118031018158255919526294312900189681357391590572546662641938953554504414523116271201239217383517759076977546969620119100344431981004490617051652613269783384538789136839141648409549944708158609707369153030498572184824311434246367523036288130211715938692732013989877070958884766361297687813292032) := by
  show endpointBQ (554 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_555]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_557 : endpointBQ 557 =
    (83181208439998071685934373052699093312338578533325853514825417712341489996199770461890609488552950199011427626413266373179415604977966325055231405438196891439414624991154527832970067316019087437422113812435805468054113273438307723535975106304050139656945526568107557112626240653378423033198779582099386028192052909906263482921092755 / 3477244234366427774150019656599722953224944248145266047356210354503201517450859132724580373301135511628436035316184930169609913739068142072615820375756960952802755455848035924936413220906158267076310313094713133187276399557665268877658953224243988577478594491473970940184290305041693727509541856111919016567671078130890381502506336256) := by
  show endpointBQ (555 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_556]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_558 : endpointBQ 558 =
    (166213078983335464607621108092736249293775292473234604958708599486240715198869559289199727757198264939855868847752182178363895095763871669275534208712231849501020606131337503551338752105438499672981710364885191177637752375829149903582657618162312038488654167092107201196324965614380942254847830655074715708039057250853987893161896295 / 6954488468732855548300039313199445906449888496290532094712420709006403034901718265449160746602271023256872070632369860339219827478136284145231640751513921905605510911696071849872826441812316534152620626189426266374552799115330537755317906448487977154957188982947941880368580610083387455019083712223838033135342156261780763005012672512) := by
  show endpointBQ (556 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_557]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_559 : endpointBQ 559 =
    (664256570130534204435475037718282860080858247697693851358279886835693180812686589990887800893462600028456250054636857092744598680203286420223013056323077104636695253894054897705170998557576799768367767228842251480523634046772409112884097649645082160985123284256987560336567514910518819405574663729062035894134583636925435487009012075 / 27817953874931422193200157252797783625799553985162128378849682836025612139606873061796642986409084093027488282529479441356879309912545136580926563006055687622422043646784287399491305767249266136610482504757705065498211196461322151021271625793951908619828755931791767521474322440333549820076334848895352132541368625047123052020050690048) := by
  show endpointBQ (557 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_558]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_560 : endpointBQ 560 =
    (1327324845860119331582156739054243210573020863467484851461893798918549701194581254060503888368511134582800771576081161668328652461157550861161190668896023481000337385688120430655949920194657039966488007146004999827808406494176710159376631618342677591807482483926753318239617019955365869903447047201005892833181269986486066974935718225 / 55635907749862844386400314505595567251599107970324256757699365672051224279213746123593285972818168186054976565058958882713758619825090273161853126012111375244844087293568574798982611534498532273220965009515410130996422392922644302042543251587903817239657511863583535042948644880667099640152669697790704265082737250094246104040101380096) := by
  show endpointBQ (558 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_559]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_561 : endpointBQ 561 =
    (42436471500499243772583811171477090075177438463431872822453118885424489018192469236962967173838970274232973239818137711624564631543865697532553495956990007863982215273857336054400227448509177934928573714182274137351931624770963961952641450883584463578073511414686770374575184152287268812055921309083588402295138317567940255570087676965 / 1780349047995611020364810064179058152051171455050376216246379701505639176934839875954985151130181381953759250081886684246840275834402888741179300032387564007835010793394194393567443569103953032743070880304493124191885516573524617665361384050812922151669040379634673121374356636181347188484885430329302536482647592003015875329283244163072) := by
  show endpointBQ (559 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_560]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_562 : endpointBQ 562 =
    (84797298666772998697088150308780424196566681849388822520445537024172642048830228190081080573749528836747171126267615641231973176400487427689826147892666308049062501465230077926885302976432778012575634819248358837738886544328432444472212239644381789074902685019365186434757186158135522884696413168418364704051426121200821794107073593365 / 3560698095991222040729620128358116304102342910100752432492759403011278353869679751909970302260362763907518500163773368493680551668805777482358600064775128015670021586788388787134887138207906065486141760608986248383771033147049235330722768101625844303338080759269346242748713272362694376969770860658605072965295184006031750658566488326144) := by
  show endpointBQ (560 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_561]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_563 : endpointBQ 563 =
    (338887424920946895148861184330108243319375031020867073631531452235394580145325075649327592470892245137605242614941396317094326964760666837351155744069267843199634125072787820327018488407594340598300490754505007027689571492102596566342684502208685939968383328387000371410079430802797837008946875402611471753201962754834600977872753186295 / 14242792383964888162918480513432465216409371640403009729971037612045113415478719007639881209041451055630074000655093473974722206675223109929434400259100512062680086347153555148539548552831624261944567042435944993535084132588196941322891072406503377213352323037077384970994853089450777507879083442634420291861180736024127002634265953304576) := by
  show endpointBQ (561 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_562]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_564 : endpointBQ 564 =
    (677172918358908094213976611672063541268733410121626035231745797095593077555045666261977871278425889484557545189714157827231115160489787197193694870475890450443318633582391292838180816089775547376710572111577500721404561152070019781768241678480944373826698480347025608945540603291558732921963116923513154036149570336037168916708432210625 / 28485584767929776325836961026864930432818743280806019459942075224090226830957438015279762418082902111260148001310186947949444413350446219858868800518201024125360172694307110297079097105663248523889134084871889987070168265176393882645782144813006754426704646074154769941989706178901555015758166885268840583722361472048254005268531906609152) := by
  show endpointBQ (562 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_563]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_565 : endpointBQ 565 =
    (5412580702060208667937245683364649723474202505014698877348776690260520556060542311186163552700609769142527329282325218945315367275687873554874426376073252040068227659910319056940636735696291077259239821062041441936332910768673136837253960082610101484416235371284381994905136595103451716333705196970207975877592665026339640915818461711875 / 227884678143438210606695688214919443462549946246448155679536601792721814647659504122238099344663216890081184010481495583595555306803569758870950404145608193002881381554456882376632776845305988191113072678975119896561346121411151061166257158504054035413637168593238159535917649431212440126065335082150724669778891776386032042148255252873216) := by
  show endpointBQ (563 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_564]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_566 : endpointBQ 566 =
    (10815581615267213426727699781449008031508627660463000057569502448325889748305048264299431240706174211260023636742911809184532831246463025209651729873604781510154033677944690646523856415223208188010056208812468651232070542049260126529663222890737707213992795989699234110173272948445658385381864013060822663302304635070331778042405386323375 / 455769356286876421213391376429838886925099892492896311359073203585443629295319008244476198689326433780162368020962991167191110613607139517741900808291216386005762763108913764753265553690611976382226145357950239793122692242822302122332514317008108070827274337186476319071835298862424880252130670164301449339557783552772064084296510505746432) := by
  show endpointBQ (564 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_565]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_567 : endpointBQ 567 =
    (43224108858188050832611407960490558599421405950472272314880237699846577050646676985592426619217961247120447820340046841652673611801235623717724757904759745187223364274754223043174846662959181839715100961720501924181879092076725099311127579821287444731540114008303299571045836412339362663840594341949789513056206863125601558183605978557375 / 1823077425147505684853565505719355547700399569971585245436292814341774517181276032977904794757305735120649472083851964668764442454428558070967603233164865544023051052435655059013062214762447905528904581431800959172490768971289208489330057268032432283309097348745905276287341195449699521008522680657205797358231134211088256337186042022985728) := by
  show endpointBQ (565 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_566]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_568 : endpointBQ 568 =
    (86371984720153547783683818728810939846815613654118314872591374451368909697323959479146771357273280587279483916129229403161338980900881766617605204067183053434081255243909232289095416700410499161194372821215747231213525593162133223138461283840420943352442591131230402846551909444762782889120623261779738127500321650654861667410979847805125 / 3646154850295011369707131011438711095400799139943170490872585628683549034362552065955809589514611470241298944167703929337528884908857116141935206466329731088046102104871310118026124429524895811057809162863601918344981537942578416978660114536064864566618194697491810552574682390899399042017045361314411594716462268422176512674372084045971456) := by
  show endpointBQ (566 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_567]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_569 : endpointBQ 569 =
    (1380735248695412348372973721932400235579376359118651934935087464821179049386798507166642049162044696712143862602910920740677742863697194438182843755158489657009608798617422234480609830351632627435994551437744691653906359834352411383973993762801095362042568182168260665223048129856419134917632498621408489784688240471736168908612142637448125 / 58338477604720181915314096183019377526412786239090727853961370058936784549800833055292953432233783523860783106683262869400462158541713858270963303461275697408737633677940961888417990872398332976924946605817630693519704607081254671658561832577037833065891115159868968841194918254390384672272725781030585515463396294754824202789953344735543296) := by
  show endpointBQ (567 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_568]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_570 : endpointBQ 570 =
    (2759043897656737856063393887235745286210458559433931898104032420916837573203497192703817240592697399229714537398083860952812994087915131944136895166283308857680009145919172373645788008980327411941521625632189304763605502867589967914900581561168445389529701270870496267765563661945076549035761249442076367109297942735261905182938499435463125 / 116676955209440363830628192366038755052825572478181455707922740117873569099601666110585906864467567047721566213366525738800924317083427716541926606922551394817475267355881923776835981744796665953849893211635261387039409214162509343317123665154075666131782230319737937682389836508780769344545451562061171030926792589509648405579906689471086592) := by
  show endpointBQ (568 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_569]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_571 : endpointBQ 571 =
    (11026494734845699712477914517759697828048113330509643620843834833067642090802748429788238024684499430605771431917254447807908772863632755383761135418935750136482562867375218714324745762205589200706642567000223221493847957074333240193234254028669681749734490342180685084157814073527867331058708993384298182938562655352502842117077020550850875 / 466707820837761455322512769464155020211302289912725822831690960471494276398406664442343627457870268190886264853466102955203697268333710866167706427690205579269901069423527695107343926979186663815399572846541045548157636856650037373268494660616302664527128921278951750729559346035123077378181806248244684123707170358038593622319626757884346368) := by
  show endpointBQ (569 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_570]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_572 : endpointBQ 572 =
    (22033678620768727446475132162458520528551483905624349161791270655919754160430710960399964248975505867462671110013287784498815954181094525206429869549922400885685821771760288183965910533584198385299963518296418031041121749600375178739895418295467787874688359860644766516679624970044302320031500808146207052071628703602812159116610999034187125 / 933415641675522910645025538928310040422604579825451645663381920942988552796813328884687254915740536381772529706932205910407394536667421732335412855380411158539802138847055390214687853958373327630799145693082091096315273713300074746536989321232605329054257842557903501459118692070246154756363612496489368247414340716077187244639253515768692736) := by
  show endpointBQ (570 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_571]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_573 : endpointBQ 573 =
    (176115347297473115184063468962867754993946476252647769873618338179834118918687430963196917039014008437131699851364950613161864584818119176999645740528400728757614645350503562197713536642564606674110897212676963702657357760791809995102800441340697073711669897347671105794159519865459003858713324641336466157467633623902197887204799803469062125 / 7467325133404183285160204311426480323380836638603613165307055367543908422374506631077498039325924291054180237655457647283259156293339373858683302843043289268318417110776443121717502831666986621046393165544656728770522189706400597972295914569860842632434062740463228011672949536561969238050908899971914945979314725728617497957114028126149541888) := by
  show endpointBQ (571 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_572]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_574 : endpointBQ 574 =
    (351923337967900029469027350719866630834325855688100691981314131266858754209244517369739040156493961013116573001418618590000584554304967639903306060916263236348113034775439055351452006030953707926451967379607545269707983658126740740650447653289874606282481732047265996744001134809686840171425404388010914049389948515476468727486031020893675625 / 14934650266808366570320408622852960646761673277207226330614110735087816844749013262154996078651848582108360475310915294566518312586678747717366605686086578536636834221552886243435005663333973242092786331089313457541044379412801195944591829139721685264868125480926456023345899073123938476101817799943829891958629451457234995914228056252299083776) := by
  show endpointBQ (572 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_573]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_575 : endpointBQ 575 =
    (1406467138150457609062628471343857231940668141025266528580373897432358853930325649557807244109751126418274248197307162100106865797170027466791261504776842968959183452569437618425489376019177362340210475903867088586602986954255650277094297764193331614655075075464160621133690946434532423960365640533270099005750072986939057945736855682805038125 / 59738601067233466281281634491411842587046693108828905322456442940351267378996053048619984314607394328433441901243661178266073250346714990869466422744346314146547336886211544973740022653335892968371145324357253830164177517651204783778367316558886741059472501923705824093383596292495753904407271199775319567834517805828939983656912225009196335104) := by
  show endpointBQ (573 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_574]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_576 : endpointBQ 576 =
    (2810488246495436161413843675781029494782309033109619550154521057651791866375555080594644388664528772616690628136879876961778763132084107059727233859110595776233220499134406649688499640080060503180698846632249190932185794800764768988489301097492413956936836976884035745534975473831787400226887166909091032621924928455639961008089821181813893575 / 119477202134466932562563268982823685174093386217657810644912885880702534757992106097239968629214788656866883802487322356532146500693429981738932845488692628293094673772423089947480045306671785936742290648714507660328355035302409567556734633117773482118945003847411648186767192584991507808814542399550639135669035611657879967313824450018392670208) := by
  show endpointBQ (574 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_575]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_577 : endpointBQ 577 =
    (359430219079583002420814896758218327610493077456574678025317081928579159799807099751603965705874735253534545887283193153667484040558756358416227352426255082049381866055966894865718120636905515462331596941524313195882872201742249900639020618134863162714922151154836127012306307820043033073460792123595975394203954739160177235590153797807532389425 / 15293081873211767368008098429801431702283953435860199762548849392729924449022989580446715984539492948078961126718377261636114752088759037662583404222552656421516118242870155513277445799253988599903013203035456980522029444518708424647262033039075005711224960492468690967906200650878912999528261427142481809365636558292208635816169529602354261786624) := by
  show endpointBQ (575 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_576]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_578 : endpointBQ 578 =
    (718237508836671060296706370818415479609876114917557372206569489538391284660619733125822135977250554154809933116182879906722026167702332896453917049129067780940965843262616689393714026160055562093705946747967994999745150170899157947030833228266026389272626066345799054497728202628266234200520439026873760189804436419846939952574432112429956403825 / 30586163746423534736016196859602863404567906871720399525097698785459848898045979160893431969078985896157922253436754523272229504177518075325166808445105312843032236485740311026554891598507977199806026406070913961044058889037416849294524066078150011422449920984937381935812401301757825999056522854284963618731273116584417271632339059204708523573248) := by
  show endpointBQ (576 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_577]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_579 : endpointBQ 579 =
    (2870464784451055621601023731125501311243622535397158356050476679643051673989674019931918917140914844459534507782668603087418478282685794101744893397038315871926697401274471544116746367525481571689378437695166208389984942724527776570313537642378063943286792756503106947906145584898434257791007290920550840896969287421879638910807851521995154485875 / 122344654985694138944064787438411453618271627486881598100390795141839395592183916643573727876315943584631689013747018093088918016710072301300667233780421251372128945942961244106219566394031908799224105624283655844176235556149667397178096264312600045689799683939749527743249605207031303996226091417139854474925092466337669086529356236818834094292992) := by
  show endpointBQ (577 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_578]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_580 : endpointBQ 580 =
    (5735971944058499748173375573250785867200123097503475333247671016143369234552768291988307749796266796268879836795418952974340551594244324310395236028278638106768892734498382688330009580702905316830070556845090333518501863095472603612871784200745112232094679135188419237871175201601879855378575881856782941136085432723859658410716207618218296615125 / 244689309971388277888129574876822907236543254973763196200781590283678791184367833287147455752631887169263378027494036186177836033420144602601334467560842502744257891885922488212439132788063817598448211248567311688352471112299334794356192528625200091379599367879499055486499210414062607992452182834279708949850184932675338173058712473637668188585984) := by
  show endpointBQ (578 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_579]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_581 : endpointBQ 581 =
    (45848217125267594538847877857914902207482363241424330422303797984208034088597644485616887462164642875004356764454417699981108271018821875005159162460516838384449287443335348522582628303687360429007253623334204803778921788466570673015988950956300586737915400811609502735811669370045370706094961703944906405356710458806574786882897135375965557082275 / 1957514479771106223105036599014583257892346039790105569606252722269430329474942666297179646021055097354107024219952289489422688267361156820810675740486740021954063135087379905699513062304510540787585689988538493506819768898394678354849540229001600731036794943035992443891993683312500863939617462674237671598801479461402705384469699789101345508687872) := by
  show endpointBQ (579 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_580]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_582 : endpointBQ 582 =
    (91617521656515795627542833378724959488617941003947758382607073080319324572911988378315329334893546261411459902808225386709237009729521853495679496758451031608168025338575455481443083408917427638687472386731517688790582093648345183083585494079629916011565886991873722334384420204169837159683735866230699374559622792899196777230711831620475063291775 / 3915028959542212446210073198029166515784692079580211139212505444538860658949885332594359292042110194708214048439904578978845376534722313641621351480973480043908126270174759811399026124609021081575171379977076987013639537796789356709699080458003201462073589886071984887783987366625001727879234925348475343197602958922805410768939399578202691017375744) := by
  show endpointBQ (580 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_581]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_583 : endpointBQ 583 =
    (366155249781882715858530292850368137062758300301000835048013835025468640818888805786875354008526440900417621535965519329013204956410425826857303280859376459657386300579942456099375622008834942762177080363466512275132120188704554803870137215170479698699144764850684326717831892431098008992138092138922004716882616179181325951612776151802792091437575 / 15660115838168849784840292792116666063138768318320844556850021778155442635799541330377437168168440778832856193759618315915381506138889254566485405923893920175632505080699039245596104498436084326300685519908307948054558151187157426838796321832012805848294359544287939551135949466500006911516939701393901372790411835691221643075757598312810764069502976) := by
  show endpointBQ (581 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_582]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_584 : endpointBQ 584 =
    (731682445962081241809927600635812829636558181562034258715156291260156031825052244839982482710005666636340530170497135537393454158178638230340923365696695669812787375944481923423280616878718196085654028513616615438300034339349582069483207299611678986251292711922894066254329596367460000816193614651533680094628212433527006404166182190137654865394125 / 31320231676337699569680585584233332126277536636641689113700043556310885271599082660754874336336881557665712387519236631830763012277778509132970811847787840351265010161398078491192208996872168652601371039816615896109116302374314853677592643664025611696588719088575879102271898933000013823033879402787802745580823671382443286151515196625621528139005952) := by
  show endpointBQ (582 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_583]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_585 : endpointBQ 585 =
    (11696896088188339851947746711534158523094019149080739450966950573980850536162136571619993935925707026912457516561235029755317274008143435819285720106411559543445518735989183625136554519143344312766551387334117674198577261287958387329957574228038758588428199928959142127654830670696244122636958195867668557129193478218164609228245679669734838738560875 / 501123706821403193114889369347733314020440586186267025819200696900974164345585322572077989381390104922651398200307786109292208196444456146127532989564605445620240162582369255859075343949954698441621936637065854337745860837989037658841482298624409787145419505417214065636350382928000221168542070444604843929293178742119092578424243146009944450224095232) := by
  show endpointBQ (583 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_584]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_586 : endpointBQ 586 =
    (23373797482208836387909257958604156091447706641496383620821137129886520131236816499527816942046412845231902285230912392793104091137640472602982917614350620694509079320292915654332704671587298293374527473151424890834421911872860435536274195337738989384397548234108097687570080434263092956175391676870606056895772950490657142201400341083623976898081475 / 1002247413642806386229778738695466628040881172372534051638401393801948328691170645144155978762780209845302796400615572218584416392888912292255065979129210891240480325164738511718150687899909396883243873274131708675491721675978075317682964597248819574290839010834428131272700765856000442337084140889209687858586357484238185156848486292019888900448190464) := by
  show endpointBQ (584 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_585]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_587 : endpointBQ 587 =
    (93415415875995042355773860305547668201656192754922406894134988324563532674670007238727213785448291610124769883977468982801108842055211581631716711694213572809795671959259400106565178056070738230517309457543749307737570166563548020522106084438540466106244126218909837515851754909631678674680490285377063797354778583701568305521637540644790706305984325 / 4008989654571225544919114954781866512163524689490136206553605575207793314764682580576623915051120839381211185602462288874337665571555649169020263916516843564961921300658954046872602751599637587532975493096526834701966886703912301270731858388995278297163356043337712525090803063424001769348336563556838751434345429936952740627393945168079555601792761856) := by
  show endpointBQ (585 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_586]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_588 : endpointBQ 588 =
    (186671691350157043753531070082465783305864930326275951084872813125575849791120815146553699779098545244763807621644925241611074398178472206565594042278215538170170908361518358304941999761108987980233056207323369570657870196557141104041619143179570641810262964318196319260807680594545075102896448219330998014134847152780135642890768032668380747013491675 / 8017979309142451089838229909563733024327049378980272413107211150415586629529365161153247830102241678762422371204924577748675331143111298338040527833033687129923842601317908093745205503199275175065950986193053669403933773407824602541463716777990556594326712086675425050181606126848003538696673127113677502868690859873905481254787890336159111203585523712) := by
  show endpointBQ (586 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_587]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_589 : endpointBQ 589 =
    (1492103655349894737485707532972090444791777504308668316494731669541167506833788828552385015241093814031275333030155014686347023250746291447037911562427913315305787872957714768763992174961245312086896877847652783983149642727582590457475527164870717715150061109346127041710537582983608593509546439848394031745635683023922852927868383934594199848577229375 / 64143834473139608718705839276509864194616395031842179304857689203324693036234921289225982640817933430099378969639396621989402649144890386704324222664269497039390740810543264749961644025594201400527607889544429355231470187262596820331709734223924452754613696693403400401452849014784028309573385016909420022949526878991243850038303122689272889628684189696) := by
  show endpointBQ (587 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_588]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_590 : endpointBQ 590 =
    (2981674027753524797997755121066469360814808357506456041620202334550007055251900596275309274938484582537879570418493127819746088906839363383978984565327086540093229756317878239109030203615255912268722623474851148978212443956476585684972318290412283108203093252462464394046354389086090517081046111547639686527356874226073341079967891156226440104881831875 / 128287668946279217437411678553019728389232790063684358609715378406649386072469842578451965281635866860198757939278793243978805298289780773408648445328538994078781481621086529499923288051188402801055215779088858710462940374525193640663419468447848905509227393386806800802905698029568056619146770033818840045899053757982487700076606245378545779257368379392) := by
  show endpointBQ (588 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_589]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_591 : endpointBQ 591 =
    (11916588741428494023184248433008025004747996791525802281593961194693079044549121366130812322550757026481898350926791178642307250241232574338004145093290288239898026721012808284439141051058938035812962620599489846255296513304019981432482587336935870456174396422553374646036107880449154981825604628863278611578826287161154132655193707366749060622561626375 / 513150675785116869749646714212078913556931160254737434438861513626597544289879370313807861126543467440795031757115172975915221193159123093634593781314155976315125926484346117999693152204753611204220863116355434841851761498100774562653677873791395622036909573547227203211622792118272226476587080135275360183596215031929950800306424981514183117029473517568) := by
  show endpointBQ (589 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_590]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_592 : endpointBQ 592 =
    (23813014050130374689307271403354445906273069730612474610088778631019503133016095318782553896670802112140646281632048023649009919686794704387788317013833892404940050012717642273980753944671075838062789940656510166544002000358794582185722395338276248745756281176033054918728669047056602425610895205901069442088991277728126955441258491370779425711074925125 / 1026301351570233739499293428424157827113862320509474868877723027253195088579758740627615722253086934881590063514230345951830442386318246187269187562628311952630251852968692235999386304409507222408441726232710869683703522996201549125307355747582791244073819147094454406423245584236544452953174160270550720367192430063859901600612849963028366234058947035136) := by
  show endpointBQ (590 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_591]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_593 : endpointBQ 593 =
    (761372854629844142093256812707251608300568688954447499019865543797191140712379480057290844858420510774659041923532778702075100945661571224074421054793662019325515653109323535408627889636375208552115689183693284514096063957417675425019178207707589250438640017060732539698811229261296234310748352123809868918683153555469572656405643115990055692329773957375 / 32841643250247479663977389709573050467643594256303195804087136872102242834552279700083703112098781916210882032455371070458574156362183877992614002004105982484168059294998151551980361741104231117070135239446747829878512735878449572009835383922649319810362212707022541005543858695569422494501573128657623051750157762043516851219611198816907719489886305124352) := by
  show endpointBQ (591 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_592]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_594 : endpointBQ 594 =
    (1521461775272116877538801556590376316755773855667825103437673978751553965841770124566424369573740818327101120875862298080875201721094370827197620488921567441653855057225208076659737013860210155369742144490179666356161611786745270453031578711860865534181767993620519493327304058473247955578814160652132706017941883580491473183542474017619251257016496019375 / 65683286500494959327954779419146100935287188512606391608174273744204485669104559400167406224197563832421764064910742140917148312724367755985228004008211964968336118589996303103960723482208462234140270478893495659757025471756899144019670767845298639620724425414045082011087717391138844989003146257315246103500315524087033702439222397633815438979772610248704) := by
  show endpointBQ (592 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_593]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_595 : endpointBQ 595 =
    (6080724334168359372520395446709685818145129854133698309025316541340385715333943225119009180754310947320771146396123056639726816306191980376712375489393604556374161457664383794596322678289796142841360018551660821430181256534904498409927555323161102320113665348240931443028652920564799068256068716141688626408407460639876695854764029154592765124843706313125 / 262733146001979837311819117676584403741148754050425566432697094976817942676418237600669624896790255329687056259642968563668593250897471023940912016032847859873344474359985212415842893928833848936561081915573982639028101887027596576078683071381194558482897701656180328044350869564555379956012585029260984414001262096348134809756889590535261755919090440994816) := by
  show endpointBQ (593 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_594]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_596 : endpointBQ 596 =
    (12151228963573410578028151573340867962646318313554566872993447676728938849633711755742020026751051624141843517756286242596025520316071033055312629339309236668115761299433533330714332209221122040064499263962898683496614309277313359007401450889476555728764954788333558799598434155548816961607505384020954246722010875127417464489604085150942517199057423203875 / 525466292003959674623638235353168807482297508100851132865394189953635885352836475201339249793580510659374112519285937127337186501794942047881824032065695719746688948719970424831685787857667697873122163831147965278056203774055193152157366142762389116965795403312360656088701739129110759912025170058521968828002524192696269619513779181070523511838180881989632) := by
  show endpointBQ (594 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_595]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_597 : endpointBQ 597 =
    (97128279836348536902225023649993112372562181955996571447887222704591719261166112087843931891681224727200910266092194059945412044942554364891794238544411415246482360453861330180407850075049371474609520962280619678150789545968323560924933745029305891764825913777887708257192852880930476518621066525966151059368556726689625504745761512850822402577700610978625 / 4203730336031677396989105882825350459858380064806809062923153519629087082822691801610713998348644085274992900154287497018697492014359536383054592256525565757973511589759763398653486302861341582984977310649183722224449630192441545217258929142099112935726363226498885248709613913032886079296201360468175750624020193541570156956110233448564188094705447055917056) := by
  show endpointBQ (595 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_596]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_598 : endpointBQ 598 =
    (194093865736622788147997409069416722044332802468180753328860061451554306664273319465322966075001174371106676628891101362671485041233613663845746275684225826447325721978989224296861918156673199613415675892798625252988093682311909561446308137051862527429543241435544448828862769659882845036373421047701203038235658584490323663587426272748795856407364872525125 / 8407460672063354793978211765650700919716760129613618125846307039258174165645383603221427996697288170549985800308574994037394984028719072766109184513051131515947023179519526797306972605722683165969954621298367444448899260384883090434517858284198225871452726452997770497419227826065772158592402720936351501248040387083140313912220466897128376189410894111834112) := by
  show endpointBQ (596 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_597]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_599 : endpointBQ 599 =
    (775726319582823517849019745277434725227350163710622074341096232222767212253533835321274061737880947737366149068645037218703761285197887385604236787433611580617238253394288036905518368552590212501778370207004539054584521573119504768991097738384534181532789877978179318897963243289498327152060997163889423514018769259083400595274161859313749325775254256413125 / 33629842688253419175912847062602803678867040518454472503385228157032696662581534412885711986789152682199943201234299976149579936114876291064436738052204526063788092718078107189227890422890732663879818485193469777795597041539532361738071433136792903485810905811991081989676911304263088634369610883745406004992161548332561255648881867588513504757643576447336448) := by
  show endpointBQ (597 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_598]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_600 : endpointBQ 600 =
    (1550157603573689066553049474285624985137125452356618736204160584258184228827178632520141989816767102573668247804955107764254427810320319199613140959195380737894547895347183272413865587908932361209730733118171007092383426248788058778768520856170763631543822176861236468649185312550132717197023395000293221947045854429253473309754877705506774529136860342114375 / 67259685376506838351825694125205607357734081036908945006770456314065393325163068825771423973578305364399886402468599952299159872229752582128873476104409052127576185436156214378455780845781465327759636970386939555591194083079064723476142866273585806971621811623982163979353822608526177268739221767490812009984323096665122511297763735177027009515287152894672896) := by
  show endpointBQ (598 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_599]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_601 : endpointBQ 601 =
    (24781852889131375877294750928912858095725512231674478196117180540340838538183829071888669943870716746477709721575215656124547452594320836271148746801003486729807505686950303248322997865370798681206228653449160500050236374297291766343246086753983274589613903867421633678804975863301455038923080674738020974860106392808998859978614644918701635472467940669268475 / 1076154966024109413629211106003289717723745296590543120108327301025046293202609101212342783577252885830398182439497599236786557955676041314061975617670544834041218966978499430055292493532503445244154191526191032889459105329265035575618285860377372911545948985983714623669661161736418836299827548279852992159749169546641960180764219762832432152244594446314766336) := by
  show endpointBQ (599 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_600]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_602 : endpointBQ 602 =
    (49522471414054546470267879976080436893454808968787102019195896553992258043858200857468040936087738456771596298854965063237240416914774250185773119647263207258733468103206845592738636333295056931994476893165460500100389160617383379997069135094066410619178533352368356153485484212687267057814675358336710800011626918075886240988878849496440373048975036179353475 / 2152309932048218827258422212006579435447490593181086240216654602050092586405218202424685567154505771660796364878995198473573115911352082628123951235341089668082437933956998860110584987065006890488308383052382065778918210658530071151236571720754745823091897971967429247339322323472837672599655096559705984319498339093283920361528439525664864304489188892629532672) := by
  show endpointBQ (600 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_601]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_603 : endpointBQ 603 =
    (197925359173115014630339732927657028514372542157644131990341074931736499756682443958584894505360629114605416436951903558386711699496589445094634760583580193794871634977268555641410563152670941824549354493282554756215176612035588724705894250890903295597580649909963895191505107999544127144687888558402202964830522200814920757174821448319660361388428466856352925 / 8609239728192875309033688848026317741789962372724344960866618408200370345620872809698742268618023086643185459515980793894292463645408330512495804941364358672329751735827995440442339948260027561953233532209528263115672842634120284604946286883018983292367591887869716989357289293891350690398620386238823937277993356373135681446113758102659457217956755570518130688) := by
  show endpointBQ (601 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_602]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_604 : endpointBQ 604 =
    (395522483919740617959468288852117279203679789883849384823152562674531479613270887180920062817511704947097059380641863661452715751066982224442843924549277170021260895767178456961691092203927835652706421499843247895919216944449227882704150202858272754884054200898020719246705895753649540977361369341417337599702784829157511629180198748300482148379861198278449875 / 17218479456385750618067377696052635483579924745448689921733236816400740691241745619397484537236046173286370919031961587788584927290816661024991609882728717344659503471655990880884679896520055123906467064419056526231345685268240569209892573766037966584735183775739433978714578587782701380797240772477647874555986712746271362892227516205318914435913511141036261376) := by
  show endpointBQ (602 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_603]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_605 : endpointBQ 605 =
    (3161560517159780966073365726122553350985705340329842433652616842040791363531244773691195469011500846828782454784335956552141906698926142681473593489609122809375244378748241043395769193974443030680904971856362915300493343390398795062409995330132021292351347155522589457819695471355331099070696508576759778032061333038365010174970197941713125517182069313391317875 / 137747835651086004944539021568421083868639397963589519373865894531205925529933964955179876297888369386290967352255692702308679418326533288199932879061829738757276027773247927047077439172160440991251736515352452209850765482145924553679140590128303732677881470205915471829716628702261611046377926179821182996447893701970170903137820129642551315487308089128290091008) := by
  show endpointBQ (603 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_604]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_606 : endpointBQ 606 =
    (6317895314456487914020990351871350415440855795799635540968617788474903733073181704781248466173395907133880971626879622267007545783473895044465412444524676820718463560176237060273528852091077064616882828056764900162473474642962220215625924552280353293310378034755058933064482355154702973184251370031905077092168845691542640167833007126497799587228300495686121175 / 275495671302172009889078043136842167737278795927179038747731789062411851059867929910359752595776738772581934704511385404617358836653066576399865758123659477514552055546495854094154878344320881982503473030704904419701530964291849107358281180256607465355762940411830943659433257404523222092755852359642365992895787403940341806275640259285102630974616178256580182016) := by
  show endpointBQ (604 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_605]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_607 : endpointBQ 607 =
    (25250730118174280078809964739657443409567248741628246337006587926874945283008656912508554100778819945673695896502149249390581313345831309897186846436697635742211417067239020065977701121723743647693218167580007571276420388754545375185224404728750850951151378878179459960201610997004439935729796729731475407124146772714383291231834229802603416832123669637874233475 / 1101982685208688039556312172547368670949115183708716154990927156249647404239471719641439010383106955090327738818045541618469435346612266305599463032494637910058208222185983416376619513377283527930013892122819617678806123857167396429433124721026429861423051761647323774637733029618092888371023409438569463971583149615761367225102561037140410523898464713026320728064) := by
  show endpointBQ (605 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_606]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_608 : endpointBQ 608 =
    (50459861010453709613832763145312156269860086859299938726176262199834116356325372050861410418854544636082690481807425106278047995203448729662747355399858702068043573150841732026410134202060792495307864311819685640787970233211307314826486331031259937732696248071221886213714257231246104846853778308343129602704431689131049311802660495470441424410817152011106170025 / 2203965370417376079112624345094737341898230367417432309981854312499294808478943439282878020766213910180655477636091083236938870693224532611198926064989275820116416444371966832753239026754567055860027784245639235357612247714334792858866249442052859722846103523294647549275466059236185776742046818877138927943166299231522734450205122074280821047796929426052641456128) := by
  show endpointBQ (606 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_607]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_609 : endpointBQ 609 =
    (3226775322510592483200358274818645782520000291265759239594955714357813230154490896936663876784645880675814154494527447585675174430115274028433580884780438053298575862014352863794121739763361204305213428361100950187230728071144125658641099589630569702380312705607083776298043291366527230996175823401942235120309710647064469149485921157715070034691728404920736662125 / 141053783706712069063207958086063189881486743514715667838838675999954867742652380114104193329037690251561950568709829327164087724366370087116731268159313652487450652439805877296207297712292291575041778191720911062887183853717426742967439964291383022262150625490857443153629827791115889711490996408136891388362643150817455004813127812753972547059003483267369053192192) := by
  show endpointBQ (607 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_608]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_610 : endpointBQ 610 =
    (6448252163375026358053917931780446498073629481889045968123253044948208047779992482055697763623832572713408581313366015947071736094335449084735086924101466520302736985339026987253606169609212784301222893785648368436551389265324139452489685058424307599009590414981643605508569270267756387721421965648873070839765053953164957233044936040951133386239463823954903970125 / 282107567413424138126415916172126379762973487029431335677677351999909735485304760228208386658075380503123901137419658654328175448732740174233462536318627304974901304879611754592414595424584583150083556383441822125774367707434853485934879928582766044524301250981714886307259655582231779422981992816273782776725286301634910009626255625507945094118006966534738106384384) := by
  show endpointBQ (608 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_609]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_611 : endpointBQ 611 =
    (25771866843128384034320412979804473052956571601386055852925394956694641345061674870904575651991645593893918231544239912916329332127852171915711708067146517010652578311895979991679166953290591423158002319753132331554610306604688937680606315036784363813746526937254503459393265378545557497155453692216315650339913445143960927433055006668588300320740676725905009637975 / 1128430269653696552505663664688505519051893948117725342710709407999638941941219040912833546632301522012495604549678634617312701794930960696933850145274509219899605219518447018369658381698338332600334225533767288503097470829739413943739519714331064178097205003926859545229038622328927117691927971265095131106901145206539640038505022502031780376472027866138952425537536) := by
  show endpointBQ (609 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_610]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_612 : endpointBQ 612 =
    (51501553871456230615229499588119904415155440139594720452409013489564905208380204611087539887204254124622707300680060447906445359293138300996864149836310797495919473189566270981735291080143718703233912982681791451437281807470253998212799199116061715575424728953171438173353808555162235194806561306376630784067159274174756616032340692540664999495293561836874004530225 / 2256860539307393105011327329377011038103787896235450685421418815999277883882438081825667093264603044024991209099357269234625403589861921393867700290549018439799210439036894036739316763396676665200668451067534577006194941659478827887479039428662128356194410007853719090458077244657854235383855942530190262213802290413079280077010045004063560752944055732277904851075072) := by
  show endpointBQ (610 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_611]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_613 : endpointBQ 613 =
    (411675819508437712695592666642291784965588910396891131459452441161685484116660066923921969163730737218389353128965450508428644930820314654373626504900706570833395527521827120331125888830168418131078925345227653235998664382589023789635643271365643648031009434704108946967396783418061527080055061945742610777216573805985146022271586058674727414266300824356188938172975 / 18054884314459144840090618635016088304830303169883605483371350527994223071059504654605336746116824352199929672794858153877003228718895371150941602324392147518393683512295152293914534107173413321605347608540276616049559533275830623099832315429297026849555280062829752723664617957262833883070847540241522097710418323304634240616080360032508486023552445858223238808600576) := by
  show endpointBQ (611 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_612]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_614 : endpointBQ 614 =
    (822680063454871448698370337091039863919814706747457807565789951750513406269018893934428078671403186121577418569302898650611892398458214439816790323822782298973751258098267899519786645704659563149382844286955750757093578904847559775373022850608341710991821464131375954380197487254690653626537440266777647964258242923869174351195257621332040917579475546225663049366875 / 36109768628918289680181237270032176609660606339767210966742701055988446142119009309210673492233648704399859345589716307754006457437790742301883204648784295036787367024590304587829068214346826643210695217080553232099119066551661246199664630858594053699110560125659505447329235914525667766141695080483044195420836646609268481232160720065016972047104891716446477617201152) := by
  show endpointBQ (612 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_613]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_615 : endpointBQ 615 =
    (3288040514199111620693486656712397110845643795371761335124509025400260421798326328526199519641080486551060236431708979297396716524131039471189582173715159220979781086926953461598626105145333172587272801107800345859784434254879334997989247679792948792791416731235173602685675299223144729640916740089042912221970241262499924849891143652685388292736210082146216812941875 / 144439074515673158720724949080128706438642425359068843866970804223953784568476037236842693968934594817599437382358865231016025829751162969207532818595137180147149468098361218351316272857387306572842780868322212928396476266206644984798658523434376214796442240502638021789316943658102671064566780321932176781683346586437073924928642880260067888188419566865785910468804608) := by
  show endpointBQ (613 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_614]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_616 : endpointBQ 616 =
    (6570734621058062084280154635934204958096416625222592977021173320677918794130313915054795462827460029221549643210683472449594413997003329284702433319505578345665286107045895616755628428005877185544322394408921341563699300323978378394355748615391112302992928719817932288944219419097959142648271013934038600196425083758719362017099537478293239368736263725134472297732625 / 288878149031346317441449898160257412877284850718137687733941608447907569136952074473685387937869189635198874764717730462032051659502325938415065637190274360294298936196722436702632545714774613145685561736644425856792952532413289969597317046868752429592884481005276043578633887316205342129133560643864353563366693172874147849857285760520135776376839133731571820937609216) := by
  show endpointBQ (614 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_615]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_617 : endpointBQ 617 =
    (105046419721071096438297017621233848096320634618818337074195641009798935526940473109512379412215627220412046893407160449161697709484559718824268771640407362902778794776279188366573747985392659940325465811914054174869010892192433555888986059033070899285510327975271099320653689674150489670130150885101318400542847767623162787572071826438688021596290138255071888292322875 / 4622050384501541079063198370564118606036557611490203003743065735166521106191233191578966207005907034163181996235483687392512826552037215014641050195044389764708782979147558987242120731436393810330968987786310813708687240518612639513557072749900038873486151696084416697258142197059285474066136970301829657013867090765986365597716572168322172422029426139705149135001747456) := by
  show endpointBQ (615 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_616]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_618 : endpointBQ 618 =
    (209922585925576437452869080594783362565256632876828216551836669959614404383659000557583085600100272873205921911784487575067055552341105564522404206535854584212522291667993904790900212748766855277830306881831489137136937487963161384783014280045018507000055485240695730084871960078164592809190398770388858327178818958637536008227495238247815770872326969965159867527445875 / 9244100769003082158126396741128237212073115222980406007486131470333042212382466383157932414011814068326363992470967374785025653104074430029282100390088779529417565958295117974484241462872787620661937975572621627417374481037225279027114145499800077746972303392168833394516284394118570948132273940603659314027734181531972731195433144336644344844058852279410298270003494912) := by
  show endpointBQ (616 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_617]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_619 : endpointBQ 619 =
    (839010982582805502441078687814101788893501429135543195603619053074834269947633869542443724000400766985143409582698518301643409731848755249790191569811587092240987152783082435005701497555751023521425336566543330370110413584577683851802662251959863612119962861722521769109439710992017061874919554956084919204096574155072352654242578055780105103648297112967548337852413125 / 36976403076012328632505586964512948848292460891921624029944525881332168849529865532631729656047256273305455969883869499140102612416297720117128401560355118117670263833180471897936965851491150482647751902290486509669497924148901116108456581999200310987889213568675333578065137576474283792529095762414637256110936726127890924781732577346577379376235409117641193080013979648) := by
  show endpointBQ (617 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_618]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_620 : endpointBQ 620 =
    (1676666535468385147850750140268245416577158752569736563750689448551809356906660899231022433907101371180326975208074421872589495699995008471713193815600861442814379819051167967854689422417550914533123006999699676361593831347532463529369779007551456039083027560502034617751820553307148797317084797222418489588800423634611470489980725452342471749940134941423032785013626875 / 73952806152024657265011173929025897696584921783843248059889051762664337699059731065263459312094512546610911939767738998280205224832595440234256803120710236235340527666360943795873931702982300965295503804580973019338995848297802232216913163998400621975778427137350667156130275152948567585058191524829274512221873452255781849563465154693154758752470818235282386160027959296) := by
  show endpointBQ (618 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_619]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_621 : endpointBQ 621 =
    (13402515080292446439916641443821652071865159318928410338626478882294785762628082929982172874909023218660807240534220701291215388208347196751307400887286885984819461908415465239819098028228036020042189714016954187174288755094146595567026814131330671176928200951367876718674230100306821676618503637152106507100153063763120077013458831196466596762424691564020242713754088375 / 591622449216197258120089391432207181572679374270745984479112414101314701592477848522107674496756100372887295518141911986241641798660763521874054424965681889882724221330887550366991453623858407722364030436647784154711966786382417857735305311987204975806227417098805337249042201223588540680465532198634196097774987618046254796507721237545238070019766545882259089280223674368) := by
  show endpointBQ (619 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_620]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_622 : endpointBQ 622 =
    (26783448010697143368657893770986586507543740281465631610685121244650288456395251072637482347442991649529890153788998213047340252442123786100438783415657045905251130802485655978446860954961340903176098929299581556011742906717932246535717031138456301015407242158852713378220160313173535749893016125130055032707391227262531426044609355096320525897212628391222417403814530875 / 1183244898432394516240178782864414363145358748541491968958224828202629403184955697044215348993512200745774591036283823972483283597321527043748108849931363779765448442661775100733982907247716815444728060873295568309423933572764835715470610623974409951612454834197610674498084402447177081360931064397268392195549975236092509593015442475090476140039533091764518178560447348736) := by
  show endpointBQ (620 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_621]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_623 : endpointBQ 623 =
    (107047671631178614814282192788862787874202151671581286469715773977814496949515424705107365137850928039760943605015192214848372777445530116150628320854217710804588924718616303476557711147964458979575212119354919209397416183441767789208669677508363929781836662390527082730314016943005482112916459947063210307573271046583043609560930637893010976495933431158487025186306951375 / 4732979593729578064960715131457657452581434994165967875832899312810517612739822788176861395974048802983098364145135295889933134389286108174992435399725455119061793770647100402935931628990867261778912243493182273237695734291059342861882442495897639806449819336790442697992337609788708325443724257589073568782199900944370038372061769900361904560158132367058072714241789394944) := by
  show endpointBQ (621 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_622]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_624 : endpointBQ 624 =
    (213923517144169141964336003245801237405107028621378333314279516215696707387073360767028362113361806435798354395255079145242735325713780087652539742317016131543680916973799836000504575247537321716807606883783105001123247429189407540232413721505478479259047583749929723915314528240837600691141240183135949972598270390041555848962052398357622256400380612828758180348237808125 / 9465959187459156129921430262915314905162869988331935751665798625621035225479645576353722791948097605966196728290270591779866268778572216349984870799450910238123587541294200805871863257981734523557824486986364546475391468582118685723764884991795279612899638673580885395984675219577416650887448515178147137564399801888740076744123539800723809120316264734116145428483578789888) := by
  show endpointBQ (622 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_623]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_625 : endpointBQ 625 =
    (6840067330225100513577615283269593411388934992073302093407860428742917797735396945550881219368260836549757639253412402413274126952950865879556847658187669641922310345290471679298184752145616414893822712412244408625658706261517723145379997710700811888103393254773393992881979915803192001585977602778731528611026748112354362657837931814152691121314733953781062843442372993125 / 302910693998692996157485768413290076965211839626621944053305556019873127215348658443319129342339123390918295305288658936955720600914310923199515865582429127619954801321414425787899624255415504753850383583563665487212526994627797943160476319737448947612788437554588332671509607026477332828398352485700708402060793660439682455811953273623161891850120471491716653711474521276416) := by
  show endpointBQ (623 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_624]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_626 : endpointBQ 626 =
    (13669190552721840866333506382085955473319647688159286903466268280799846926994417255988881028785532455761035666284019344982687015302777010373706404360122239012417544994028478603909492408687799843523815308484629226197516358593017017933727387425064502477185821080339150555375348663741098895969417641393017086776275853427728958335423322937402737936835364333236075986335238189461 / 605821387997385992314971536826580153930423679253243888106611112039746254430697316886638258684678246781836590610577317873911441201828621846399031731164858255239909602642828851575799248510831009507700767167127330974425053989255595886320952639474897895225576875109176665343019214052954665656796704971401416804121587320879364911623906547246323783700240942983433307422949042552832) := by
  show endpointBQ (624 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_625]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_627 : endpointBQ 627 =
    (54633090675575153111128487169295623952469262804751654684461027537637726855175769927291022897797767099543308685371591695122496664996083194816315373337101984040045842771660149308277236432167532281943427958192559622917229918849406675511479110762797739932777834413751684807586457438786309005935276260008512381971632883827760149768736667714667173031888309204084124788835089377047 / 2423285551989543969259886147306320615721694717012975552426444448158985017722789267546553034738712987127346362442309271495645764807314487385596126924659433020959638410571315406303196994043324038030803068668509323897700215957022383545283810557899591580902307500436706661372076856211818662627186819885605667216486349283517459646495626188985295134800963771933733229691796170211328) := by
  show endpointBQ (625 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_626]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_628 : endpointBQ 628 =
    (109179047235240298003578938473887427133084507646497325868627858859106972487297033044490672553334293741192608903940357885149104180606207724250148584994240488041750304613859915603303631976883441705382958902097730793485309550746900421715922369674299151731691589346779682717553159762040263452052473929490695398102800643438889103126358922881145084224810289366375451930479054209633 / 4846571103979087938519772294612641231443389434025951104852888896317970035445578535093106069477425974254692724884618542991291529614628974771192253849318866041919276821142630812606393988086648076061606137337018647795400431914044767090567621115799183161804615000873413322744153712423637325254373639771211334432972698567034919292991252377970590269601927543867466459383592340422656) := by
  show endpointBQ (626 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_627]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_629 : endpointBQ 629 =
    (872736969937748878945806164233940898420516287237924483854318234829167200455782015737807605442258207931189325951879930865363858258985927986840359708074979697403800205671300599249337949878909040383793716064539185642191487173167898275499889005995193856199190730128716572041587359881277265174050030455482947290566973296279017989959111135132720259249279701622937529762746579828595 / 38772568831832703508158178356901129851547115472207608838823111170543760283564628280744848555819407794037541799076948343930332236917031798169538030794550928335354214569141046500851151904693184608492849098696149182363203455312358136724540968926393465294436920006987306581953229699389098602034989118169690675463781588536279354343930019023764722156815420350939731675068738723381248) := by
  show endpointBQ (627 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_628]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_630 : endpointBQ 630 =
    (1744086440718204039483113431545411302566914106610605844522858539237302338589694743692248267155673398043728112434837954050496613404682530174019605966693560380980249377629292294525306523048948591037247537508943968763489188198206753787445724134397390583851164940813667298976590320144301307351003002039017591008334952994312759321746586163532320136528369769380019832928096106271135 / 77545137663665407016316356713802259703094230944415217677646222341087520567129256561489697111638815588075083598153896687860664473834063596339076061589101856670708429138282093001702303809386369216985698197392298364726406910624716273449081937852786930588873840013974613163906459398778197204069978236339381350927563177072558708687860038047529444313630840701879463350137477446762496) := by
  show endpointBQ (628 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_629]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_631 : endpointBQ 631 =
    (6970808980521329795902348604176739142640459873723024629378663177459567124712462483519176407457120025831916487477653917935159480242842239647906933054181563554457568147413584123197971150852781828939348094361144306899152025211245406407600529159385126174821005271379070252100086390671985225253691363705152847871408589904253219003425244380594257307584817586188714189385628564429711 / 310180550654661628065265426855209038812376923777660870710584889364350082268517026245958788446555262352300334392615586751442657895336254385356304246356407426682833716553128372006809215237545476867942792789569193458905627642498865093796327751411147722355495360055898452655625837595112788816279912945357525403710252708290234834751440152190117777254523362807517853400549909787049984) := by
  show endpointBQ (629 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_630]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_632 : endpointBQ 632 =
    (13930570720186048926518005689170947795355974486156472357601417221515870276168645311755438113793071874126856879095596815398155474780069832323313221206533996263345472953864547669338576261846842925978633830411098210776276868132140186180640677131512906666322167428223466858792724149979989491354841219702373599311959163025773865552011463017320694873002305825965084933146240284858741 / 620361101309323256130530853710418077624753847555321741421169778728700164537034052491917576893110524704600668785231173502885315790672508770712608492712814853365667433106256744013618430475090953735885585579138386917811255284997730187592655502822295444710990720111796905311251675190225577632559825890715050807420505416580469669502880304380235554509046725615035706801099819574099968) := by
  show endpointBQ (630 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_631]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_633 : endpointBQ 633 =
    (222712795184746579673319508676239329943475895898931956805703670262968913402544291503128080224312022493952154915161250352504688160091496180054994916251296674438042181528239540587020529350791931841911576301382494179878958031023962723368976901482288621766644271668939729653863425334490211741533727347899972859886131935462688508761904782162987818032935598204986104690679765566792277 / 9925777620949172098088493659366689241996061560885147862738716459659202632592544839870681230289768395273610700563698776046165052650760140331401735883405037653850678929700107904217894887601455259774169369266214190684980084559963683001482488045156727115375851521788750484980026803043609242120957214251440812918728086665287514712046084870083768872144747609840571308817597113185599488) := by
  show endpointBQ (631 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_632]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_634 : endpointBQ 634 =
    (445073753410275550216033457307176544041859412815401145907132927144795695820250440365650902817937928048735349080061582458006999245680478148135179413993507572139215418061963694853998372241314050205399911565953957563265216286327508444015411975316106013483104271186743693542080936884881702769415742646277196947481764452385941490653727566249888767474981882668732104950568567838850285 / 19851555241898344196176987318733378483992123121770295725477432919318405265185089679741362460579536790547221401127397552092330105301520280662803471766810075307701357859400215808435789775202910519548338738532428381369960169119927366002964976090313454230751703043577500969960053606087218484241914428502881625837456173330575029424092169740167537744289495219681142617635194226371198976) := by
  show endpointBQ (632 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_633]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_635 : endpointBQ 635 =
    (1778890995491542971999099023369693000949639987498779974335449270323205509792609804237475374985259794440844439383085252284841855029265507298698019929116006605363993484809173505930649645519700005079626775880327016506804507996141808197373902122162480501839410446667521324030967025341151789933279955624079522184414497038400592645609693458796874032778555348079758917893912856314900035 / 79406220967593376784707949274933513935968492487081182901909731677273621060740358718965449842318147162188885604509590208369320421206081122651213887067240301230805431437600863233743159100811642078193354954129713525479840676479709464011859904361253816923006812174310003879840214424348873936967657714011526503349824693322300117696368678960670150977157980878724570470540776905484795904) := by
  show endpointBQ (633 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_634]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_636 : endpointBQ 636 =
    (3554980587840579577113160095521480973551327786040868956585330904000232743191845419806860237568967998654222982011236512046400494538799887814248483921335767531034500365705261699253534488448030403852041541089976352672653418341895991499948790225234941349345215522552889071173696307335309640039893328640877029373262986994850948137446773227107453775741711396398762309932874668761587629 / 158812441935186753569415898549867027871936984974162365803819463354547242121480717437930899684636294324377771209019180416738640842412162245302427774134480602461610862875201726467486318201623284156386709908259427050959681352959418928023719808722507633846013624348620007759680428848697747873935315428023053006699649386644600235392737357921340301954315961757449140941081553810969591808) := by
  show endpointBQ (634 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_635]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_637 : endpointBQ 637 =
    (28417486334247651839690732587470454826312815195332983923395947037637080607527267475311442527988417146474952265008060420194811500369903505735281906063004783219778930596298035344347436068034255618213489300159496504697751539072640284254307625008010128647910496409841018927432503186309299072268581262280218266247907273399091541400596533155053922949482485439137276074998010716955835701 / 1270499535481494028555327188398936222975495879793298926430555706836377936971845739503447197477090354595022169672153443333909126739297297962419422193075844819692886903001613811739890545612986273251093679266075416407677450823675351424189758469780061070768108994788960062077443430789581982991482523424184424053597195093156801883141898863370722415634527694059593127528652430487756734464) := by
  show endpointBQ (635 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_636]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_638 : endpointBQ 638 =
    (56790361229980001243212405940109715845990916395068898798246531521054950727444602034649083733326930969329064730542010855428563642026510459656222710232661050296355696466385241747808926396558253378313613624965524412056888083578447538235060606962632486293234006169117138296109225362906966591833444186629070412768580783417650756990517090590869142723220100414476848419893983740478459729 / 2540999070962988057110654376797872445950991759586597852861111413672755873943691479006894394954180709190044339344306886667818253478594595924838844386151689639385773806003227623479781091225972546502187358532150832815354901647350702848379516939560122141536217989577920124154886861579163965982965046848368848107194390186313603766283797726741444831269055388119186255057304860975513468928) := by
  show endpointBQ (636 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_637]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_639 : endpointBQ 639 =
    (226983418709167716567698487691661089980057737942673498331549616581019003691197077097735366018783188043556606681633428967622002017504077855992739672560008900087315087757495872189518436224488316794200179849000136756653706290164641414575869197107700376250386701773117088801063518300020007537892292595461018107460628523064278103958963293113975413705660275951278939609294135639843373525 / 10163996283851952228442617507191489783803967038346391411444445654691023495774765916027577579816722836760177357377227546671273013914378383699355377544606758557543095224012910493919124364903890186008749434128603331261419606589402811393518067758240488566144871958311680496619547446316655863931860187393475392428777560745254415065135190906965779325076221552476745020229219443902053875712) := by
  show endpointBQ (637 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_638]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_640 : endpointBQ 640 =
    (453611620800637205096949872898671693121336042805624502925491174294149088753769432635067390306707560456372123211965397170036457865966678281850905417619923889532865989149174066957770020436105759853198168493228755302420630567355629243213434999540740814509771233433913180593048689936033723984175990053839937595034777189284950138897646518476598753211468188403416597622955573101846616575 / 20327992567703904456885235014382979567607934076692782822888891309382046991549531832055155159633445673520354714754455093342546027828756767398710755089213517115086190448025820987838248729807780372017498868257206662522839213178805622787036135516480977132289743916623360993239094892633311727863720374786950784857555121490508830130270381813931558650152443104953490040458438887804107751424) := by
  show endpointBQ (638 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_639]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_641 : endpointBQ 641 =
    (116033852600802997063799777487480219100437759749678747848340642384443336903214220868050238440455793964739989117620748596095325922114276304497461605827176530942507120024358726327797571227555853370448091500567915606359197299129569960413996672882521500351599481512394991595701854885637426595152218255772256036809896005019090245530017979426313961071493562593593965671952035599452364519885 / 5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092421210806977140503895691783124161732454069953302838660381462064754694610172886591674830791775236479710273844905605846838573774239433481250692219130145866174442655580414269208292514127802333112415945459400923534111101570260513349217744366479014439025434868093450357360355277851584364544) := by
  show endpointBQ (639 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_640]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_642 : endpointBQ 642 =
    (231886685150746707080698151265931607905867036254818215278821158961734656120151976492936591953547382322670711481547861078936212958234614580438764925217805204582451826444935301756487813950856549403344781922351793902880080717917284117457612695729344839236191787546611519865981397985181815083291718542346739443297155666816621847931283980725597791158476214793126162286693537602025708190285 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088) := by
  show endpointBQ (640 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_641]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_643 : endpointBQ 643 =
    (926824352175725935154316909888443155586378216557419844868310115102509544554999955889213855066670690093415958974535531975935081699112182263872072894250604602739207767379601221662223879435978046369131947683418540739548733835164721254511268188849686693894187113465117071613875805654169061532284345451186500640966513148055220656996378028881439146592912721431716094124074170540183749558055 / 41631728778657596327700961309456342154461048989066819221276449401614432238693441192048957766929296739369686455817124031165534264993293859632559626422709283051696518037556881383092733398646334201891837682190759244846774708590193915467850005537753041166929395541244643314153666340113022418664899327563675207388272888812562084106793741954931832115512203478944747602858882842222812674916352) := by
  show endpointBQ (641 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_642]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_644 : endpointBQ 644 =
    (1852207297893946853302172984769283755720833605406352256074305595500349556381298512158071234464497413328210742274149546794831384110978466888142478490065360675769645382710400575172562496228976344610162601513519167729891326560165889287786904545368347436475941587562481239539394106167351857027971048063413146693066826431183450302084519077935690985026271923856539939268173109088858659692225 / 83263457557315192655401922618912684308922097978133638442552898803228864477386882384097915533858593478739372911634248062331068529986587719265119252845418566103393036075113762766185466797292668403783675364381518489693549417180387830935700011075506082333858791082489286628307332680226044837329798655127350414776545777625124168213587483909863664231024406957889495205717765684445625349832704) := by
  show endpointBQ (642 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_643]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_645 : endpointBQ 645 =
    (14806153989996954038508674729180547786414365528931523935202678890738819124613237174828805458110609757474579039172860041769863300315709856428815961594497634718730022407132208324516074115817966183312293590980740179306646815421947201946470472980677410874189669709272753759547827420107961739099371048805047949030913078366044102725358857473933132284029887987598552185330054604952553385241575 / 666107660458521541243215380951301474471376783825069107540423190425830915819095059072783324270868747829914983293073984498648548239892701754120954022763348528827144288600910102129483734378341347230269402915052147917548395337443102647485600088604048658670870328659914293026458661441808358698638389241018803318212366221000993345708699871278909313848195255663115961645742125475565002798661632) := by
  show endpointBQ (643 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_644]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_646 : endpointBQ 646 =
    (29589352702490036830446018179711203250679251421384084267405043550639283490893740648611364706208644926177879661230723401304424486987519387498827557357065815740221703694253358961707317108975749473317126261665386187792663170664945648541085952979989430413690673263957487745825038053518081677052851599860010552404413888393536199089903205091317531029634923435681447700605333931447815990040915 / 1332215320917043082486430761902602948942753567650138215080846380851661831638190118145566648541737495659829966586147968997297096479785403508241908045526697057654288577201820204258967468756682694460538805830104295835096790674886205294971200177208097317341740657319828586052917322883616717397276778482037606636424732442001986691417399742557818627696390511326231923291484250951130005597323264) := by
  show endpointBQ (644 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_645]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_647 : endpointBQ 647 =
    (118265802906856462997231608266276047667575583854510380152383626080109334324284269898938922091998020432494249667643541520383938119816989254677976397981337362602557955013254137521870422252903072972298482983931930552446836388013761090608489056647573853449147551652535964953127319278922115929025484258264005025244886470328344374690603832114213413496156923081934207373007696921049939452454555 / 5328861283668172329945723047610411795771014270600552860323385523406647326552760472582266594166949982639319866344591875989188385919141614032967632182106788230617154308807280817035869875026730777842155223320417183340387162699544821179884800708832389269366962629279314344211669291534466869589107113928150426545698929768007946765669598970231274510785562045304927693165937003804520022389293056) := by
  show endpointBQ (645 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_646]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_648 : endpointBQ 648 =
    (236348814773671416778084187771707773777705146713882413503913490759785733046830851590924306437331438051337039907670941554646726412555436022099881735069349628817785835907476970348962064873266883080652146055987613917022812132460267527290226198215321472194355153457077283901690299579051461972534700380116473721239008046575810319126662681489455863447497529435766507161203944542376463233421545 / 10657722567336344659891446095220823591542028541201105720646771046813294653105520945164533188333899965278639732689183751978376771838283228065935264364213576461234308617614561634071739750053461555684310446640834366680774325399089642359769601417664778538733925258558628688423338583068933739178214227856300853091397859536015893531339197940462549021571124090609855386331874007609040044778586112) := by
  show endpointBQ (646 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_647]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_649 : endpointBQ 649 =
    (3778663149776598576884185471164957617804051419684910191204542846097808941921554972966012059707953237981252675067084806336635934620485057390362306752034663818753489598767687365455628074208402636906722582006221728673389403846124030220257320082578287734465307700332284971020851085862612879684351073978405351469191548398958942756407755216405498063759374081719970700910606273856512591200998775 / 170523561077381514558263137523533177464672456659217691530348336749012714449688335122632531013342399444458235723026940031654028349412531649054964229827417223379748937881832986145147836000855384890948967146253349866892389206385434277756313622682636456619742804136938059014773417329102939826851427645700813649462365752576254296501427167047400784345137985449757686181309984121744640716457377792) := by
  show endpointBQ (647 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_648]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_650 : endpointBQ 650 =
    (7551504014268487448719242767489907596751702143807902184887969293357254541867884129332692821943321031836186008570121716207421890913357657065177059872710260358895648705087350559315792931045143636468442509802880712002135680721760966403195291443919937121111716621465290612348295621515884291141145366640973406557074635244144451086380367512600818164400474859770110938491612229879656133725262575 / 341047122154763029116526275047066354929344913318435383060696673498025428899376670245265062026684798888916471446053880063308056698825063298109928459654834446759497875763665972290295672001710769781897934292506699733784778412770868555512627245365272913239485608273876118029546834658205879653702855291401627298924731505152508593002854334094801568690275970899515372362619968243489281432914755584) := by
  show endpointBQ (648 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_649]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_651 : endpointBQ 651 =
    (30182780660106969833496296476828892209786034107096815194367606498680226615035019950778978386782689293400632692715655721087510880912158758546661540845078856019093685132026056543234507745931204873146174831489052445817766920792515370331540564878929225600997291973179730785970572345689642135976454865435767554208122926714288129111409530458056808601711436439511920335694167035734379439104972569 / 1364188488619052116466105100188265419717379653273741532242786693992101715597506680981060248106739195555665885784215520253232226795300253192439713838619337787037991503054663889161182688006843079127591737170026798935139113651083474222050508981461091652957942433095504472118187338632823518614811421165606509195698926020610034372011417336379206274761103883598061489450479872973957125731659022336) := by
  show endpointBQ (649 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_650]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_652 : endpointBQ 652 =
    (60319197601842039559721477290866956628159186441371669075072589945903187136959387029129724855920551107087900358253560818947544786584821113470363540152761277543534384572605068452762050042175879477670005308398244596019838347083045309986688594327936900932254188720594208529259162245379761012143422088989145296505019858149445247271803070853966064502037755465138261684697559621337062442819614919 / 2728376977238104232932210200376530839434759306547483064485573387984203431195013361962120496213478391111331771568431040506464453590600506384879427677238675574075983006109327778322365376013686158255183474340053597870278227302166948444101017962922183305915884866191008944236374677265647037229622842331213018391397852041220068744022834672758412549522207767196122978900959745947914251463318044672) := by
  show endpointBQ (650 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_651]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_653 : endpointBQ 653 =
    (482183524387731150590902361411040763720806257258326900643064936806821183064160007969055407897328086457273215747266194767415035932024674299704807931405202114351075479129474872355515038067209637787754705011306212936281284455516613735660461585333139766348019680386099716034507290832698334962103552036520590928503318252568878265000977922225262466540829419454448803528594602371792591184012013739 / 21827015817904833863457681603012246715478074452379864515884587103873627449560106895696963969707827128890654172547448324051715628724804051079035421417909404592607864048874622226578923008109489266041467794720428782962225818417335587552808143703377466447327078929528071553890997418125176297836982738649704147131182816329760549952182677382067300396177662137568983831207677967583314011706544357376) := by
  show endpointBQ (651 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_652]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_654 : endpointBQ 654 =
    (963628636027548470935876847842891572213862428364650237885451366819144937057777657579812109197569912445239734380064906847590538884061561961890925498443780642003297856453238450878938935187915126053629234364095877307575920695940552718280095511270669824018630448551087487634045964068409383040651049628881119696319801408273179381050958941047423459166588656030713152534174511631224091110468113215 / 43654031635809667726915363206024493430956148904759729031769174207747254899120213791393927939415654257781308345094896648103431257449608102158070842835818809185215728097749244453157846016218978532082935589440857565924451636834671175105616287406754932894654157859056143107781994836250352595673965477299408294262365632659521099904365354764134600792355324275137967662415355935166628023413088714752) := by
  show endpointBQ (652 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_653]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_655 : endpointBQ 655 =
    (3851567667547418506156547523335349495056630562301522510447354545665512026711056264393927910462458335064001017843256370794497964285836273651961589071761533024765474918606674786846401187433043026764811649277900035599393664677658417133920748725476346972453669713321930722745254052102174506526394256467729735299969359145605643581142517846938784284803459857590648594379712803370060816762635547315 / 174616126543238670907661452824097973723824595619038916127076696830989019596480855165575711757662617031125233380379586592413725029798432408632283371343275236740862912390996977812631384064875914128331742357763430263697806547338684700422465149627019731578616631436224572431127979345001410382695861909197633177049462530638084399617461419056538403169421297100551870649661423740666512093652354859008) := by
  show endpointBQ (653 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_654]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_656 : endpointBQ 656 =
    (7697255079113848587112856042818278609204777719164416742252804733246038538877515496323132266863141924578286003598202426519080664504060583527355297854863888136516040715200209612186166647862371484023112135732475032976498178722221172562293526842211508682353975045402148574158072601834727372584809285062989654210167772704729446485061917346019646761538517486391082458080983297116655891820289971657 / 349232253086477341815322905648195947447649191238077832254153393661978039192961710331151423515325234062250466760759173184827450059596864817264566742686550473481725824781993955625262768129751828256663484715526860527395613094677369400844930299254039463157233262872449144862255958690002820765391723818395266354098925061276168799234922838113076806338842594201103741299322847481333024187304709718016) := by
  show endpointBQ (654 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_655]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_657 : endpointBQ 657 =
    (246124424602884280431828152978896664796767404629867081685205536714281866450449336967795765898965343002978852456518131247963774418654229878155190133846989203584695838478718897599416206715794366233031707559640848005663149080605657493394312529027787509330879543524932116602956906853788477694114267627258035040720242683314641569315028625381262363521390156698992904940101685427315509126253662264447 / 11175432098767274938090332980742270318324774119618490632132908597183297254174774730596845552490407489992014936344293541914478401907099674152466135765969615151415226393023806580008408580152058504213231510896859536876659619029675820827037769576129262821031464411918372635592190678080090264492535162188648523331165601960837401575517530819618457802842963014435319721578331119402656773993750710976512) := by
  show endpointBQ (655 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_656]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_658 : endpointBQ 658 =
    (491874230599067062719924451843670199205716289617983985163888690572073197335525082859537048135984011206866412900164849815184833807751908417074223205085383294226340389532051617272501490742523596444399744331519685588182214220449358126068085769579124809362929742234757791628131535310539225589607356764976864548654000978983446545678283995624958117661469217269068012460203216082291116412132509213423 / 22350864197534549876180665961484540636649548239236981264265817194366594508349549461193691104980814979984029872688587083828956803814199348304932271531939230302830452786047613160016817160304117008426463021793719073753319238059351641654075539152258525642062928823836745271184381356160180528985070324377297046662331203921674803151035061639236915605685926028870639443156662238805313547987501421953024) := by
  show endpointBQ (656 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_657]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_659 : endpointBQ 659 =
    (1966001863944599354032524784724700036338957206223856961977245070219684664122235513557116165042002962726532926941388381480146068258947597472500314634307839002758776936883428196697080426524068478189622078407137953034831646504227677616351163486311699465994688787351691477176270422289845232979737611385849777755258392970708912485005907155765410105546601886652961812720873036924659021525696807342405 / 89403456790138199504722663845938162546598192956947925057063268777466378033398197844774764419923259919936119490754348335315827215256797393219729086127756921211321811144190452640067268641216468033705852087174876295013276952237406566616302156609034102568251715295346981084737525424640722115940281297509188186649324815686699212604140246556947662422743704115482557772626648955221254191950005687812096) := by
  show endpointBQ (657 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_658]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_660 : endpointBQ 660 =
    (3929020417018266083855592020458922530892878058568770286682900997692450231637305267609593307071802582565772177210635050697044570405210904205285150794208534092008056488430159233763361034494989659750731831960850810541537600069905692595955208363387721087579673949836384939971393241510965359384392161145924366166426864252539662735588436607197337039461114847833005625725932912943514311607500296312515 / 178806913580276399009445327691876325093196385913895850114126537554932756066796395689549528839846519839872238981508696670631654430513594786439458172255513842422643622288380905280134537282432936067411704174349752590026553904474813133232604313218068205136503430590693962169475050849281444231880562595018376373298649631373398425208280493113895324845487408230965115545253297910442508383900011375624192) := by
  show endpointBQ (658 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_659]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_661 : endpointBQ 661 =
    (31408351091194502815791065909001932231804279753043684897786341914886920336543064533194264072895197614571233343883803829511525990087716258465279478167036705862779554595390181995962867906053887037643729008220377085480533906013367324448878302007929721906167211756570859004983440518502807933503110670008934781657678993630907970595400896272080530636661881722980208608075790982863608345516926611128529 / 1430455308642211192075562621535010600745571087311166800913012300439462048534371165516396230718772158718977911852069573365053235444108758291515665378044110739381148978307047242241076298259463488539293633394798020720212431235798505065860834505744545641092027444725551697355800406794251553855044500760147010986389197050987187401666243944911162598763899265847720924362026383283540067071200091004993536) := by
  show endpointBQ (659 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_660]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_662 : endpointBQ 662 =
    (62769185766214732556217848813602953824831245920984429273790858804183996618114051812934376460354850300829953475447057275014713816801623566463894388288434929568429336793510484745335776859148539752991476580724838320604818895376184925260163747280597825473595895204886694017523638313074446717333750673346146515234181468360710180267056859266896189063585999630948344283310317531562521368272102955069269 / 2860910617284422384151125243070021201491142174622333601826024600878924097068742331032792461437544317437955823704139146730106470888217516583031330756088221478762297956614094484482152596518926977078587266789596041440424862471597010131721669011489091282184054889451103394711600813588503107710089001520294021972778394101974374803332487889822325197527798531695441848724052766567080134142400182009987072) := by
  show endpointBQ (660 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_661]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_663 : endpointBQ 663 =
    (250887108062544082090260465197573135680518846989312386493127813286813980440377312835384229779605640326278031565004401132460623503409510508857197207569786742655685838603668795522897984243666217804252941136854867366042825977591216483743796488375320009370294167238867360076083907819327773435143662056909220059380127137888880871581015784924784465652943436591373593615769033517393401118501487037935477 / 11443642469137689536604500972280084805964568698489334407304098403515696388274969324131169845750177269751823294816556586920425883552870066332125323024352885915049191826456377937928610386075707908314349067158384165761699449886388040526886676045956365128736219557804413578846403254354012430840356006081176087891113576407897499213329951559289300790111194126781767394896211066268320536569600728039948288) := by
  show endpointBQ (661 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_662]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_664 : endpointBQ 664 =
    (501395804197392019260324459105255512483691511705639384771333865165955541604072306948543143978849884513300741815431118401976359188563501394020793816033133384643716042458312449574419048450765819895377295635494267360492827179952280303107888909649018118273966472988686654752354717738475565311561617232887958640540978065916692541244111485709410885354675797109457030981740527014398576895949427338257175 / 22887284938275379073209001944560169611929137396978668814608196807031392776549938648262339691500354539503646589633113173840851767105740132664250646048705771830098383652912755875857220772151415816628698134316768331523398899772776081053773352091912730257472439115608827157692806508708024861680712012162352175782227152815794998426659903118578601580222388253563534789792422132536641073139201456079896576) := by
  show endpointBQ (662 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_663]
  norm_num (config := { maxSteps := 2000000000 })

theorem endpointB_at_665 : endpointBQ 665 =
    (8016291953854689271788560930514145362239260675101005585440482398496662695284384955671286169396792731917470896253940893005091911364141763251392691492481542185809773353520248440786193702339352325315249051907239672137035923708393686291857452808484904131922331441638399889835839884806711749017376699614967724289131058957487361472661878813691424636935599792340355182081562401784420620974998675636955075 / 366196559012406065171344031112962713790866198351658701033731148912502284424799018372197435064005672632058345434129810781453628273691842122628010336779292349281574138446604094013715532354422653066059170149068293304374382396364417296860373633470603684119559025849741234523084904139328397786891392194597634812515634445052719974826558449897257625283558212057016556636678754120586257170227223297278345216) := by
  show endpointBQ (663 + 1 + 1) = _
  rw [endpointBQ_step]
  rw [endpointB_at_664]
  norm_num (config := { maxSteps := 2000000000 })


end C1ConcreteClassMomentCertificate
end Source
end ConnesWeilRH
