/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1ConcreteClassMomentEndpointB

/-!
# Record 1145 RED-9: isolated momentB rational value certificates.
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

theorem momentBQ_step (n : ℕ) :
    momentBQ (n + 1 + 1) = endpointBQ (n + 1 + 1) - endpointBQ (n + 1) := by
  rw [momentBQ]

theorem momentB_at_0 : momentBQ 0 =
    0 := by
  norm_num (config := { maxSteps := 2000000000 })
    [momentBQ, endpointBQ, rationalRadiusQ]

theorem momentB_at_1 : momentBQ 1 =
    1 := by
  norm_num (config := { maxSteps := 2000000000 })
    [momentBQ, endpointBQ, rationalRadiusQ]

theorem momentB_at_2 : momentBQ 2 =
    (-1 / 2) := by
  show momentBQ (0 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_2, endpointB_at_1]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_3 : momentBQ 3 =
    (-1 / 8) := by
  show momentBQ (1 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_3, endpointB_at_2]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_4 : momentBQ 4 =
    (-1 / 16) := by
  show momentBQ (2 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_4, endpointB_at_3]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_5 : momentBQ 5 =
    (-5 / 128) := by
  show momentBQ (3 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_5, endpointB_at_4]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_6 : momentBQ 6 =
    (-7 / 256) := by
  show momentBQ (4 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_6, endpointB_at_5]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_7 : momentBQ 7 =
    (-21 / 1024) := by
  show momentBQ (5 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_7, endpointB_at_6]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_8 : momentBQ 8 =
    (-33 / 2048) := by
  show momentBQ (6 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_8, endpointB_at_7]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_9 : momentBQ 9 =
    (-429 / 32768) := by
  show momentBQ (7 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_9, endpointB_at_8]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_10 : momentBQ 10 =
    (-715 / 65536) := by
  show momentBQ (8 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_10, endpointB_at_9]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_11 : momentBQ 11 =
    (-2431 / 262144) := by
  show momentBQ (9 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_11, endpointB_at_10]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_12 : momentBQ 12 =
    (-4199 / 524288) := by
  show momentBQ (10 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_12, endpointB_at_11]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_13 : momentBQ 13 =
    (-29393 / 4194304) := by
  show momentBQ (11 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_13, endpointB_at_12]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_14 : momentBQ 14 =
    (-52003 / 8388608) := by
  show momentBQ (12 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_14, endpointB_at_13]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_15 : momentBQ 15 =
    (-185725 / 33554432) := by
  show momentBQ (13 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_15, endpointB_at_14]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_16 : momentBQ 16 =
    (-334305 / 67108864) := by
  show momentBQ (14 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_16, endpointB_at_15]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_17 : momentBQ 17 =
    (-9694845 / 2147483648) := by
  show momentBQ (15 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_17, endpointB_at_16]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_18 : momentBQ 18 =
    (-17678835 / 4294967296) := by
  show momentBQ (16 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_18, endpointB_at_17]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_19 : momentBQ 19 =
    (-64822395 / 17179869184) := by
  show momentBQ (17 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_19, endpointB_at_18]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_20 : momentBQ 20 =
    (-119409675 / 34359738368) := by
  show momentBQ (18 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_20, endpointB_at_19]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_21 : momentBQ 21 =
    (-883631595 / 274877906944) := by
  show momentBQ (19 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_21, endpointB_at_20]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_22 : momentBQ 22 =
    (-1641030105 / 549755813888) := by
  show momentBQ (20 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_22, endpointB_at_21]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_23 : momentBQ 23 =
    (-6116566755 / 2199023255552) := by
  show momentBQ (21 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_23, endpointB_at_22]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_24 : momentBQ 24 =
    (-11435320455 / 4398046511104) := by
  show momentBQ (22 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_24, endpointB_at_23]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_25 : momentBQ 25 =
    (-171529806825 / 70368744177664) := by
  show momentBQ (23 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_25, endpointB_at_24]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_26 : momentBQ 26 =
    (-322476036831 / 140737488355328) := by
  show momentBQ (24 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_26, endpointB_at_25]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_27 : momentBQ 27 =
    (-1215486600363 / 562949953421312) := by
  show momentBQ (25 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_27, endpointB_at_26]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_28 : momentBQ 28 =
    (-2295919134019 / 1125899906842624) := by
  show momentBQ (26 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_28, endpointB_at_27]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_29 : momentBQ 29 =
    (-17383387729001 / 9007199254740992) := by
  show momentBQ (27 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_29, endpointB_at_28]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_30 : momentBQ 30 =
    (-32968493968795 / 18014398509481984) := by
  show momentBQ (28 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_30, endpointB_at_29]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_31 : momentBQ 31 =
    (-125280277081421 / 72057594037927936) := by
  show momentBQ (29 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_31, endpointB_at_30]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_32 : momentBQ 32 =
    (-238436656380769 / 144115188075855872) := by
  show momentBQ (30 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_32, endpointB_at_31]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_33 : momentBQ 33 =
    (-14544636039226909 / 9223372036854775808) := by
  show momentBQ (31 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_33, endpointB_at_32]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_34 : momentBQ 34 =
    (-27767032438524099 / 18446744073709551616) := by
  show momentBQ (32 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_34, endpointB_at_33]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_35 : momentBQ 35 =
    (-106168065206121555 / 73786976294838206464) := by
  show momentBQ (33 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_35, endpointB_at_34]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_36 : momentBQ 36 =
    (-203236010537432691 / 147573952589676412928) := by
  show momentBQ (34 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_36, endpointB_at_35]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_37 : momentBQ 37 =
    (-1558142747453650631 / 1180591620717411303424) := by
  show momentBQ (35 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_37, endpointB_at_36]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_38 : momentBQ 38 =
    (-2989949596465113373 / 2361183241434822606848) := by
  show momentBQ (36 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_38, endpointB_at_37]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_39 : momentBQ 39 =
    (-11487701081155435591 / 9444732965739290427392) := by
  show momentBQ (37 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_39, endpointB_at_38]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_40 : momentBQ 40 =
    (-22091732848375837675 / 18889465931478580854784) := by
  show momentBQ (38 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_40, endpointB_at_39]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_41 : momentBQ 41 =
    (-340212685864987900195 / 302231454903657293676544) := by
  show momentBQ (39 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_41, endpointB_at_40]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_42 : momentBQ 42 =
    (-655531760569123027205 / 604462909807314587353088) := by
  show momentBQ (40 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_42, endpointB_at_41]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_43 : momentBQ 43 =
    (-2528479647909474533505 / 2417851639229258349412352) := by
  show momentBQ (41 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_43, endpointB_at_42]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_44 : momentBQ 44 =
    (-4880553738988055494905 / 4835703278458516698824704) := by
  show momentBQ (42 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_44, endpointB_at_43]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_45 : momentBQ 45 =
    (-37713369801271337915175 / 38685626227668133590597632) := by
  show momentBQ (43 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_45, endpointB_at_44]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_46 : momentBQ 46 =
    (-72912514949124586636005 / 77371252455336267181195264) := by
  show momentBQ (44 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_46, endpointB_at_45]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_47 : momentBQ 47 =
    (-282139731759656009156715 / 309485009821345068724781056) := by
  show momentBQ (45 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_47, endpointB_at_46]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_48 : momentBQ 48 =
    (-546270544470823336877895 / 618970019642690137449562112) := by
  show momentBQ (46 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_48, endpointB_at_47]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_49 : momentBQ 49 =
    (-16934386878595523443214745 / 19807040628566084398385987584) := by
  show momentBQ (47 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_49, endpointB_at_48]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_50 : momentBQ 50 =
    (-32831974560542341369497975 / 39614081257132168796771975168) := by
  show momentBQ (48 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_50, endpointB_at_49]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_51 : momentBQ 51 =
    (-127388061294904284513652143 / 158456325028528675187087900672) := by
  show momentBQ (49 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_51, endpointB_at_50]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_52 : momentBQ 52 =
    (-247282707219520081702971807 / 316912650057057350374175801344) := by
  show momentBQ (50 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_52, endpointB_at_51]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_53 : momentBQ 53 =
    (-1921196417628579096307704039 / 2535301200456458802993406410752) := by
  show momentBQ (51 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_53, endpointB_at_52]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_54 : momentBQ 54 =
    (-3733645868221578243767802189 / 5070602400912917605986812821504) := by
  show momentBQ (52 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_54, endpointB_at_53]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_55 : momentBQ 55 =
    (-14519733931972804281319230735 / 20282409603651670423947251286016) := by
  show momentBQ (53 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_55, endpointB_at_54]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_56 : momentBQ 56 =
    (-28247482376747091965475594339 / 40564819207303340847894502572032) := by
  show momentBQ (54 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_56, endpointB_at_55]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_57 : momentBQ 57 =
    (-439853654152204717748119968993 / 649037107316853453566312041152512) := by
  show momentBQ (55 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_57, endpointB_at_56]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_58 : momentBQ 58 =
    (-856557115980609187193707308039 / 1298074214633706907132624082305024) := by
  show momentBQ (56 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_58, endpointB_at_57]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_59 : momentBQ 59 =
    (-3337619107096856488030652614083 / 5192296858534827628530496329220096) := by
  show momentBQ (57 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_59, endpointB_at_58]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_60 : momentBQ 60 =
    (-6505528768070144002093644925755 / 10384593717069655257060992658440192) := by
  show momentBQ (58 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_60, endpointB_at_59]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_61 : momentBQ 61 =
    (-50743124390947123216330430420889 / 83076749736557242056487941267521536) := by
  show momentBQ (59 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_61, endpointB_at_60]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_62 : momentBQ 62 =
    (-98990685287257502667923298689931 / 166153499473114484112975882535043072) := by
  show momentBQ (60 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_62, endpointB_at_61]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_63 : momentBQ 63 =
    (-386382997411553478155442552951021 / 664613997892457936451903530140172288) := by
  show momentBQ (61 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_63, endpointB_at_62]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_64 : momentBQ 64 =
    (-754366804470175838303483079571041 / 1329227995784915872903807060280344576) := by
  show momentBQ (62 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_64, endpointB_at_63]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_65 : momentBQ 65 =
    (-94295850558771979787935384946380125 / 170141183460469231731687303715884105728) := by
  show momentBQ (63 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_65, endpointB_at_64]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_66 : momentBQ 66 =
    (-184239584937908329739504521356773475 / 340282366920938463463374607431768211456) := by
  show momentBQ (64 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_66, endpointB_at_65]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_67 : momentBQ 67 =
    (-720209286575459834436244947121932675 / 1361129467683753853853498429727072845824) := by
  show momentBQ (65 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_67, endpointB_at_66]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_68 : momentBQ 68 =
    (-1408170396140078183748478926462286275 / 2722258935367507707706996859454145691648) := by
  show momentBQ (66 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_68, endpointB_at_67]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_69 : momentBQ 69 =
    (-11016862510978258731679276307028474975 / 21778071482940061661655974875633165533184) := by
  show momentBQ (67 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_69, endpointB_at_68]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_70 : momentBQ 70 =
    (-21554730999740071431546410165925277125 / 43556142965880123323311949751266331066368) := by
  show momentBQ (68 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_70, endpointB_at_69]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_71 : momentBQ 71 =
    (-84371375627553993889195948363764656175 / 174224571863520493293247799005065324265472) := by
  show momentBQ (69 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_71, endpointB_at_70]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_72 : momentBQ 72 =
    (-165177763552535283811242772148778693075 / 348449143727040986586495598010130648530944) := by
  show momentBQ (70 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_72, endpointB_at_71]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_73 : momentBQ 73 =
    (-2587784962323052779709470096997532858175 / 5575186299632655785383929568162090376495104) := by
  show momentBQ (71 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_73, endpointB_at_72]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_74 : momentBQ 74 =
    (-5069222597427349965732249642063660256425 / 11150372599265311570767859136324180752990208) := by
  show momentBQ (72 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_74, endpointB_at_73]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_75 : momentBQ 75 =
    (-19865872341269344460302059408087317221125 / 44601490397061246283071436545296723011960832) := by
  show momentBQ (73 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_75, endpointB_at_74]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_76 : momentBQ 76 =
    (-38937109788887915142192036439851141753405 / 89202980794122492566142873090593446023921664) := by
  show momentBQ (74 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_76, endpointB_at_75]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_77 : momentBQ 77 =
    (-305348913607594702957190180501990532697755 / 713623846352979940529142984724747568191373312) := by
  show momentBQ (75 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_77, endpointB_at_76]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_78 : momentBQ 78 =
    (-598801116295412988916048276049358057628065 / 1427247692705959881058285969449495136382746624) := by
  show momentBQ (76 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_78, endpointB_at_77]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_79 : momentBQ 79 =
    (-2349142840851235571901420159885943149156255 / 5708990770823839524233143877797980545530986496) := by
  show momentBQ (77 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_79, endpointB_at_78]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_80 : momentBQ 80 =
    (-4609077725720778653730634490915458077458475 / 11417981541647679048466287755595961091061972992) := by
  show momentBQ (78 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_80, endpointB_at_79]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_81 : momentBQ 81 =
    (-144725040587632449727141923014745383632196115 / 365375409332725729550921208179070754913983135744) := by
  show momentBQ (79 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_81, endpointB_at_80]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_82 : momentBQ 82 =
    (-284089894486834067982908219251166864166903485 / 730750818665451459101842416358141509827966271488) := by
  show momentBQ (80 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_82, endpointB_at_81]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_83 : momentBQ 83 =
    (-1115572512497080120615810324376533295874913685 / 2923003274661805836407369665432566039311865085952) := by
  show momentBQ (81 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_83, endpointB_at_82]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_84 : momentBQ 84 =
    (-2190823126952097104341892564739456954549529285 / 5846006549323611672814739330865132078623730171904) := by
  show momentBQ (82 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_84, endpointB_at_83]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_85 : momentBQ 85 =
    (-17213610283195048676972013008667161785746301525 / 46768052394588893382517914646921056628989841375232) := by
  show momentBQ (83 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_85, endpointB_at_84]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_86 : momentBQ 86 =
    (-33819681379924389753580307911146070802583910055 / 93536104789177786765035829293842113257979682750464) := by
  show momentBQ (84 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_86, endpointB_at_85]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_87 : momentBQ 87 =
    (-132919212865284229496629582255434557340387925565 / 374144419156711147060143317175368453031918731001856) := by
  show momentBQ (85 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_87, endpointB_at_86]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_88 : momentBQ 88 =
    (-261255004597282795907168489260681716151796957145 / 748288838313422294120286634350736906063837462003712) := by
  show momentBQ (86 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_88, endpointB_at_87]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_89 : momentBQ 89 =
    (-4108828708666356699267286240190721535841897598735 / 11972621413014756705924586149611790497021399392059392) := by
  show momentBQ (87 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_89, endpointB_at_88]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_90 : momentBQ 90 =
    (-8079157573220364296312079685768272682835191907625 / 23945242826029513411849172299223580994042798784118784) := by
  show momentBQ (88 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_90, endpointB_at_89]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_91 : momentBQ 91 =
    (-31778019788000099565494180097355205885818421503325 / 95780971304118053647396689196894323976171195136475136) := by
  show momentBQ (89 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_91, endpointB_at_90]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_92 : momentBQ 92 =
    (-62508412550022173870587453158533866522653818121925 / 191561942608236107294793378393788647952342390272950272) := by
  show momentBQ (90 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_92, endpointB_at_91]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_93 : momentBQ 93 =
    (-491914029198000585677231696595418688721753960002975 / 1532495540865888858358347027150309183618739122183602176) := by
  show momentBQ (91 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_93, endpointB_at_92]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_94 : momentBQ 94 =
    (-967959863905743087945520435236146452000870695489725 / 3064991081731777716716694054300618367237478244367204352) := by
  show momentBQ (92 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_94, endpointB_at_93]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_95 : momentBQ 95 =
    (-3810054783458775984466410223801853055748108056714875 / 12259964326927110866866776217202473468949912977468817408) := by
  show momentBQ (93 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_95, endpointB_at_94]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_96 : momentBQ 96 =
    (-7499792047439906411528618019483647593946275859007175 / 24519928653854221733733552434404946937899825954937634816) := by
  show momentBQ (94 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_96, endpointB_at_95]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_97 : momentBQ 97 =
    (-472486898988714103926302935227469798418615379117452025 / 1569275433846670190958947355801916604025588861116008628224) := by
  show momentBQ (95 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_97, endpointB_at_96]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_98 : momentBQ 98 =
    (-930360801101488596390967635344811664927376674344673575 / 3138550867693340381917894711603833208051177722232017256448) := by
  show momentBQ (96 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_98, endpointB_at_97]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_99 : momentBQ 99 =
    (-3664482339032393859254219461664258190428238737724938775 / 12554203470773361527671578846415332832204710888928069025792) := by
  show momentBQ (97 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_99, endpointB_at_98]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_100 : momentBQ 100 =
    (-7217919758700169722773462576005357041752591453094576375 / 25108406941546723055343157692830665664409421777856138051584) := by
  show momentBQ (98 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_100, endpointB_at_99]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_101 : momentBQ 101 =
    (-56877207698557337415454885098922213489010420650385261835 / 200867255532373784442745261542645325315275374222849104412672) := by
  show momentBQ (99 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_101, endpointB_at_100]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_102 : momentBQ 102 =
    (-112064993386266437085896258759262579052604690192343238665 / 401734511064747568885490523085290650630550748445698208825344) := by
  show momentBQ (100 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_102, endpointB_at_101]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_103 : momentBQ 103 =
    (-441667915110579487338532313933564282148500837816882175915 / 1606938044258990275541962092341162602522202993782792835301376) := by
  show momentBQ (101 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_103, endpointB_at_102]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_104 : momentBQ 104 =
    (-870471716188811999317689900276830575496559903658515356415 / 3213876088517980551083924184682325205044405987565585670602752) := by
  show momentBQ (102 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_104, endpointB_at_103]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_105 : momentBQ 105 =
    (-13726669370669727681548186888980789844368829249999665235775 / 51422017416287688817342786954917203280710495801049370729644032) := by
  show momentBQ (103 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_105, endpointB_at_104]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_106 : momentBQ 106 =
    (-27061148187891748857909282723990699978898549092856482893385 / 102844034832575377634685573909834406561420991602098741459288064) := by
  show momentBQ (104 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_106, endpointB_at_105]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_107 : momentBQ 107 =
    (-106712829646591990779302643194604835765845221894471791032405 / 411376139330301510538742295639337626245683966408394965837152256) := by
  show momentBQ (105 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_107, endpointB_at_106]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_108 : momentBQ 108 =
    (-210433710798419720134886520692164676136386372147042503811565 / 822752278660603021077484591278675252491367932816789931674304512) := by
  show momentBQ (106 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_108, endpointB_at_107]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_109 : momentBQ 109 =
    (-1660088162965311125508549218793743556187048046937779752291235 / 6582018229284824168619876730229402019930943462534319453394436096) := by
  show momentBQ (107 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_109, endpointB_at_108]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_110 : momentBQ 110 =
    (-3274485826032494421874661303125273986974452569647914190299225 / 13164036458569648337239753460458804039861886925068638906788872192) := by
  show momentBQ (108 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_110, endpointB_at_109]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_111 : momentBQ 111 =
    (-12919334986346387082669118232330626457699203774792679623544215 / 52656145834278593348959013841835216159447547700274555627155488768) := by
  show momentBQ (109 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_111, endpointB_at_110]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_112 : momentBQ 112 =
    (-25489498756845574514455287323246911659784915555672043581587235 / 105312291668557186697918027683670432318895095400549111254310977536) := by
  show momentBQ (110 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_112, endpointB_at_111]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_113 : momentBQ 113 =
    (-804739889323267423956374071205366782401780905400503090218682705 / 3369993333393829974333376885877453834204643052817571560137951281152) := by
  show momentBQ (111 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_113, endpointB_at_112]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_114 : momentBQ 114 =
    (-1588115002823793234887357680343334446686700370834621142643949055 / 6739986666787659948666753771754907668409286105635143120275902562304) := by
  show momentBQ (112 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_114, endpointB_at_113]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_115 : momentBQ 115 =
    (-6268875011146552242976411896092109657973817253294557142015588375 / 26959946667150639794667015087019630673637144422540572481103610249216) := by
  show momentBQ (113 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_115, endpointB_at_114]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_116 : momentBQ 116 =
    (-12374214152437107470918656525329642542261361013024908445543813575 / 53919893334301279589334030174039261347274288845081144962207220498432) := by
  show momentBQ (114 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_116, endpointB_at_115]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_117 : momentBQ 117 =
    (-97713622100279227960012839458637522144063850758024277035501148575 / 431359146674410236714672241392314090778194310760649159697657763987456) := by
  show momentBQ (115 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_117, endpointB_at_116]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_118 : momentBQ 118 =
    (-192921766710807706485153554828592030899818372009432546967527908725 / 862718293348820473429344482784628181556388621521298319395315527974912) := by
  show momentBQ (116 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_118, endpointB_at_117]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_119 : momentBQ 119 =
    (-761877485485054162898996241950202427112842045393182770227694961575 / 3450873173395281893717377931138512726225554486085193277581262111899648) := by
  show momentBQ (117 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_119, endpointB_at_118]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_120 : momentBQ 120 =
    (-1504547975537712002363564007212584624970738493003344126079901814875 / 6901746346790563787434755862277025452451108972170386555162524223799296) := by
  show momentBQ (118 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_120, endpointB_at_119]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_121 : momentBQ 121 =
    (-23771858013495849637344311313958837074537668189452837192062448675025 / 110427941548649020598956093796432407239217743554726184882600387580788736) := by
  show momentBQ (119 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_121, endpointB_at_120]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_122 : momentBQ 122 =
    (-46954331117566182341531325653191421990202501630406843709941530853975 / 220855883097298041197912187592864814478435487109452369765200775161577472) := by
  show momentBQ (120 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_122, endpointB_at_121]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_123 : momentBQ 123 =
    (-185508095071040163021459827580641519666209883490623759575342769439475 / 883423532389192164791648750371459257913741948437809479060803100646309888) := by
  show momentBQ (121 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_123, endpointB_at_122]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_124 : momentBQ 124 =
    (-366491602457420809871664537415413733974707330798549378673238154258475 / 1766847064778384329583297500742918515827483896875618958121606201292619776) := by
  show momentBQ (122 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_124, endpointB_at_123]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_125 : momentBQ 125 =
    (-2896465890389293497372832634412140800767848259536922508869140251397625 / 14134776518227074636666380005943348126619871175004951664972849610340958208) := by
  show momentBQ (123 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_125, endpointB_at_124]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_126 : momentBQ 126 =
    (-5723416599409243950808717285598390222317268160844958877525421136761707 / 28269553036454149273332760011886696253239742350009903329945699220681916416) := by
  show momentBQ (124 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_126, endpointB_at_125]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_127 : momentBQ 127 =
    (-22621122750046059424624930224031732783444440826196742230219521635772461 / 113078212145816597093331040047546785012958969400039613319782796882727665664) := by
  show momentBQ (125 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_127, endpointB_at_126]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_128 : momentBQ 128 =
    (-44707888269776070201424074694739881327909879113191986612481101815581793 / 226156424291633194186662080095093570025917938800079226639565593765455331328) := by
  show momentBQ (126 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_128, endpointB_at_127]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_129 : momentBQ 129 =
    (-11311095732253345760960290897769189975961199415637572612957718759342193629 / 57896044618658097711785492504343953926634992332820282019728792003956564819968) := by
  show momentBQ (127 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_129, endpointB_at_128]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_130 : momentBQ 130 =
    (-22359142726547311387944761076985608092016324426260317955846653361490382755 / 115792089237316195423570985008687907853269984665640564039457584007913129639936) := by
  show momentBQ (128 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_130, endpointB_at_129]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_131 : momentBQ 131 =
    (-88404610472656292718489286104389250456126082731521564840809075598508128739 / 463168356949264781694283940034751631413079938662562256157830336031652518559744) := by
  show momentBQ (129 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_131, endpointB_at_130]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_132 : momentBQ 132 =
    (-174784687881053281023578054206387907390356148301252559494424050229111491171 / 926336713898529563388567880069503262826159877325124512315660672063305037119488) := by
  show momentBQ (130 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_132, endpointB_at_131]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_133 : momentBQ 133 =
    (-1382387985968330495368299155995977085723725900200815697819535669993881793807 / 7410693711188236507108543040556026102609279018600996098525285376506440296955904) := by
  show momentBQ (131 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_133, endpointB_at_132]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_134 : momentBQ 134 =
    (-2733594288042638498359869759601067470265713622201612996440134445175871517077 / 14821387422376473014217086081112052205218558037201992197050570753012880593911808) := by
  show momentBQ (132 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_134, endpointB_at_133]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_135 : momentBQ 135 =
    (-10811977407929838836796499795437057904782300147513842448606501910023969433215 / 59285549689505892056868344324448208820874232148807968788202283012051522375647232) := by
  show momentBQ (133 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_135, endpointB_at_134]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_136 : momentBQ 136 =
    (-21383688651239014588330855150975514522791660291749599509466192666491850656803 / 118571099379011784113736688648896417641748464297615937576404566024103044751294464) := by
  show momentBQ (134 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_136, endpointB_at_135]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_137 : momentBQ 137 =
    (-338365426304899701427117649153671376860644506969449545179200342781547519216471 / 1897137590064188545819787018382342682267975428761855001222473056385648716020711424) := by
  show momentBQ (135 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_137, endpointB_at_136]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_138 : momentBQ 138 =
    (-669321390719911088224444400880620022841128915246137421485863451779557501515793 / 3794275180128377091639574036764685364535950857523710002444946112771297432041422848) := by
  show momentBQ (136 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_138, endpointB_at_137]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_139 : momentBQ 139 =
    (-2648184632848343870801062629571148786023597012495587189357111917910423158171181 / 15177100720513508366558296147058741458143803430094840009779784451085189728165691392) := by
  show momentBQ (137 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_139, endpointB_at_138]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_140 : momentBQ 140 =
    (-5239214201678378161656778583683927454363231499541629331461912067808391140266725 / 30354201441027016733116592294117482916287606860189680019559568902170379456331382784) := by
  show momentBQ (138 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_140, endpointB_at_139]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_141 : momentBQ 141 =
    (-41464638110426021450826504790869940138817575010658037851855704079512124167253795 / 242833611528216133864932738352939863330300854881517440156476551217363035650651062272) := by
  show momentBQ (139 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_141, endpointB_at_140]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_142 : momentBQ 142 =
    (-82047049878077021168656700969168179423617754808323351494097457008396330799034105 / 485667223056432267729865476705879726660601709763034880312953102434726071301302124544) := by
  show momentBQ (140 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_142, endpointB_at_141]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_143 : momentBQ 143 =
    (-324721422756896379554824408061074062225867452128716362955512470695202379641247655 / 1942668892225729070919461906823518906642406839052139521251812409738904285205208498176) := by
  show momentBQ (141 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_143, endpointB_at_142]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_144 : momentBQ 144 =
    (-642630507973438289608498653715272444824618803863123991023846358089106807262049555 / 3885337784451458141838923813647037813284813678104279042503624819477808570410416996352) := by
  show momentBQ (142 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_144, endpointB_at_143]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_145 : momentBQ 145 =
    (-20349966085825545837602457367650294086112928788998926382421801339488382229964902575 / 124330809102446660538845562036705210025114037699336929360115994223289874253133343883264) := by
  show momentBQ (143 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_145, endpointB_at_144]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_146 : momentBQ 146 =
    (-40278898390565045899254519065625064846306279740984081874172806789194246206896048545 / 248661618204893321077691124073410420050228075398673858720231988446579748506266687766528) := by
  show momentBQ (144 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_146, endpointB_at_145]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_147 : momentBQ 147 =
    (-159460296368127373491569260410488270418938559522526022762136180302426536353328192185 / 994646472819573284310764496293641680200912301594695434880927953786318994025066751066112) := by
  show momentBQ (145 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_147, endpointB_at_146]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_148 : momentBQ 148 =
    (-315666300973639902626167719588109433278306944360918861386269581415007633189241523305 / 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224) := by
  show momentBQ (146 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_148, endpointB_at_147]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_149 : momentBQ 149 =
    (-2499735842845310580255868698359893620284971208047276388815594252826952338498588279145 / 15914343565113172548972231940698266883214596825515126958094847260581103904401068017057792) := by
  show momentBQ (147 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_149, endpointB_at_148]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_150 : momentBQ 150 =
    (-4949141433821252491110612523598447100564204740764741843628189963650677448705258673475 / 31828687130226345097944463881396533766429193651030253916189694521162207808802136034115584) := by
  show momentBQ (148 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_150, endpointB_at_149]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_151 : momentBQ 151 =
    (-19598600077932159864798025593449850518234250773428377700767632256056682696872824346961 / 127314748520905380391777855525586135065716774604121015664758778084648831235208544136462336) := by
  show momentBQ (149 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_151, endpointB_at_150]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_152 : momentBQ 152 =
    (-38807823995375601321686156638685465595708880670563476374367695659344027326920360792989 / 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672) := by
  show momentBQ (150 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_152, endpointB_at_151]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_153 : momentBQ 153 =
    (-614797632768845052517238586749701323384651214833663494141298757550660643442264663088931 / 4074071952668972172536891376818756322102936787331872501272280898708762599526673412366794752) := by
  show momentBQ (151 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_153, endpointB_at_152]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_154 : momentBQ 154 =
    (-1217540409993202947141982299249408503173524954866666919770023029659151470346445705332981 / 8148143905337944345073782753637512644205873574663745002544561797417525199053346824733589504) := by
  show momentBQ (152 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_154, endpointB_at_153]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_155 : momentBQ 155 =
    (-4822725000622427258159800016507397317765261184861472864024117195403132447476181040604665 / 32592575621351777380295131014550050576823494298654980010178247189670100796213387298934358016) := by
  show momentBQ (153 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_155, endpointB_at_154]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_156 : momentBQ 156 =
    (-9552106936716678504871345839146909526154420540338530124228412767669430073388306964294401 / 65185151242703554760590262029100101153646988597309960020356494379340201592426774597868716032) := by
  show momentBQ (154 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_156, endpointB_at_155]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_157 : momentBQ 157 =
    (-75682078037062914307826817033240898553377331973451430984271270389996253658384278255563331 / 521481209941628438084722096232800809229175908778479680162851955034721612739414196782949728256) := by
  show momentBQ (155 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_157, endpointB_at_156]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_158 : momentBQ 158 =
    (-149918001716729721972828917817438977389174205374161751822346274466807865527117901512612713 / 1042962419883256876169444192465601618458351817556959360325703910069443225478828393565899456512) := by
  show momentBQ (156 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_158, endpointB_at_157]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_159 : momentBQ 159 =
    (-593978918194131683259436092112131644592550965596362383802460555798871669746682318651237711 / 4171849679533027504677776769862406473833407270227837441302815640277772901915313574263597826048) := by
  show momentBQ (157 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_159, endpointB_at_158]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_160 : momentBQ 160 =
    (-1176750686988374089476241314561770239287129271464491515080346384129840100441540442610942635 / 8343699359066055009355553539724812947666814540455674882605631280555545803830627148527195652096) := by
  show momentBQ (158 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_160, endpointB_at_159]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_161 : momentBQ 161 =
    (-74605993555062917272793699343216233170803995810848762056093960753831862367993664061533763059 / 533996758980227520598755426542388028650676130589163192486760401955554931445160137505740521734144) := by
  show momentBQ (159 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_161, endpointB_at_160]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_162 : momentBQ 162 =
    (-147821813317174351615038447766993654543394252569321460222943934661319031648384961711983046061 / 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288) := by
  show momentBQ (160 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_162, endpointB_at_161]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_163 : momentBQ 163 =
    (-585812371293987245289226441150678556894192037959903564587222259583745792088044107525266145501 / 4271974071841820164790043412339104229205409044713305539894083215644439451561281100045924173873152) := by
  show momentBQ (161 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_163, endpointB_at_162]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_164 : momentBQ 164 =
    (-1160842919803422578088467119580792477771926553748765959274066195371471722972013783623686901821 / 8543948143683640329580086824678208458410818089426611079788166431288878903122562200091848347746304) := by
  show momentBQ (162 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_164, endpointB_at_163]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_165 : momentBQ 165 =
    (-9201803632588105801920775947896525738436003169959730164977353987700690486973279992138981538825 / 68351585149469122636640694597425667667286544715412888638305331450311031224980497600734786781970432) := by
  show momentBQ (163 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_165, endpointB_at_164]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_166 : momentBQ 166 =
    (-18236301744583700589261174151285841917991351736829283417864210630170459328728863984420890686035 / 136703170298938245273281389194851335334573089430825777276610662900622062449960995201469573563940864) := by
  show momentBQ (164 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_166, endpointB_at_165]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_167 : momentBQ 167 =
    (-72286063541783584263456943322566770976134394233937761981654521654531097821105978926198470309705 / 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456) := by
  show momentBQ (165 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_167, endpointB_at_166]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_168 : momentBQ 168 =
    (-143273575043894409528169151136344917323954996954691013269027824357184391489737000147135890254565 / 1093625362391505962186251113558810682676584715446606218212885303204976499599687961611756588511526912) := by
  show momentBQ (166 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_168, endpointB_at_167]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_169 : momentBQ 169 =
    (-2271909547124611351089539396590612260422714951710100353266012643378209636480115288047440545465245 / 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592) := by
  show momentBQ (167 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_169, endpointB_at_168]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_170 : momentBQ 170 =
    (-4503489338974821317248495253596775782494730821437181173633812044566273539768275866839601081247675 / 34996011596528190789960035633881941845650710894291398982812329702559247987190014771576210832368861184) := by
  show momentBQ (168 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_170, endpointB_at_169]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_171 : momentBQ 171 =
    (-17855010673347232751914622358377805161184991609698000653112878341398049210610693730881712522123135 / 139984046386112763159840142535527767382602843577165595931249318810236991948760059086304843329475444736) := by
  show momentBQ (169 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_171, endpointB_at_170]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_172 : momentBQ 172 =
    (-35396775545407671946778110991170034793226386875366211821083425483824202821035234940169009035086215 / 279968092772225526319680285071055534765205687154331191862498637620473983897520118172609686658950889472) := by
  show momentBQ (170 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_172, endpointB_at_171]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_173 : momentBQ 173 =
    (-280704661883349212415147345302069345685818556383718098395103443953117515394721281734828653045683705 / 2239744742177804210557442280568444278121645497234649534899989100963791871180160945380877493271607115776) := by
  show momentBQ (171 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_173, endpointB_at_172]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_174 : momentBQ 174 =
    (-556541612866987166811534910049767546648761646471764784679309140323232992950227743555180508639708155 / 4479489484355608421114884561136888556243290994469299069799978201927583742360321890761754986543214231552) := by
  show momentBQ (172 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_174, endpointB_at_173]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_175 : momentBQ 175 =
    (-2206975361369087040804362574335285098779572046353550008211053487488682558250903120994681327364359925 / 17917957937422433684459538244547554224973163977877196279199912807710334969441287563047019946172856926208) := by
  show momentBQ (173 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_175, endpointB_at_174]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_176 : momentBQ 176 =
    (-4376116859400418303766364647396251024437208571912467730567060343763273415503219331343739546259616537 / 35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416) := by
  show momentBQ (174 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_176, endpointB_at_175]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_177 : momentBQ 177 =
    (-138842253084613271637678296540117418866235071963404657997082187270307492910056686058087736513146015583 / 1146749307995035755805410447651043470398282494584140561868794419693461438044242404035009276555062843277312) := by
  show momentBQ (175 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_177, endpointB_at_176]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_178 : momentBQ 178 =
    (-275331247642368691213701028732097254361855990164717711621332473061457231702993767267733308000645488529 / 2293498615990071511610820895302086940796564989168281123737588839386922876088484808070018553110125686554624) := by
  show momentBQ (176 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_178, endpointB_at_177]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_179 : momentBQ 179 =
    (-1092044161997260089870072619577868885277923196945453395531801831356116885293896627477638850834020870233 / 9173994463960286046443283581208347763186259956673124494950355357547691504353939232280074212440502746218496) := by
  show momentBQ (177 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_179, endpointB_at_178]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_180 : momentBQ 180 =
    (-2165785907871661072088691508101360079741132597294055616836813687885036280890130182986378726514398932585 / 18347988927920572092886567162416695526372519913346248989900710715095383008707878464560148424881005492436992) := by
  show momentBQ (178 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_180, endpointB_at_179]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_181 : momentBQ 181 =
    (-17181901535781844505236952630937456632612985271866174560238721923887954495061699451691937897014231531841 / 146783911423364576743092537299333564210980159306769991919205685720763064069663027716481187399048043939495936) := by
  show momentBQ (179 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_181, endpointB_at_180]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_182 : momentBQ 182 =
    (-34079020173180564515911966820478159840376031561325727442683431882186605876945580680427655828884580773099 / 293567822846729153486185074598667128421960318613539983838411371441526128139326055432962374798096087878991872) := by
  show momentBQ (180 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_182, endpointB_at_181]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_183 : momentBQ 183 =
    (-135192596511188832859826593650468304421711509820204259415480427576586425511839061820158063233267402847129 / 1174271291386916613944740298394668513687841274454159935353645485766104512557304221731849499192384351515967488) := by
  show momentBQ (181 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_183, endpointB_at_182]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_184 : momentBQ 184 =
    (-268168920948423750426869144782076472705362175217126481791362815356835368638238139020313535265989438434469 / 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976) := by
  show momentBQ (182 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_184, endpointB_at_183]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_185 : momentBQ 185 =
    (-4255724180268463865469879906324257066845964954532659384949888156749778676215518293148453929221136740373095 / 37576681324381331646231689548629392438010920782533117931316655544515344401833735095419183974156299248510959616) := by
  show momentBQ (183 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_185, endpointB_at_184]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_186 : momentBQ 186 =
    (-8442436617073114803391599597951364019094427774667491860954642992038750130654568722083689686617065857929329 / 75153362648762663292463379097258784876021841565066235862633311089030688803667470190838367948312598497021919232) := by
  show momentBQ (184 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_186, endpointB_at_185]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_187 : momentBQ 187 =
    (-33497409803225584542489250017677992720923052138196822545078099613573105357113288800525607466254809694364757 / 300613450595050653169853516389035139504087366260264943450533244356122755214669880763353471793250393988087676928) := by
  show momentBQ (185 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_187, endpointB_at_186]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_188 : momentBQ 188 =
    (-66457428005329903022799528109938691440975680980058936707080079982008674264647220026711231925029595703793181 / 601226901190101306339707032778070279008174732520529886901066488712245510429339761526706943586500787976175353856) := by
  show momentBQ (186 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_188, endpointB_at_187]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_189 : momentBQ 189 =
    (-527417460552937315478813276276747487393275085224723050888103613474239053206668363190708287405022110585422479 / 4809815209520810450717656262224562232065397860164239095208531909697964083434718092213655548692006303809402830848) := by
  show momentBQ (187 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_189, endpointB_at_188]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_190 : momentBQ 190 =
    (-1046463215382812133886534278326879935304117232588736212079570661655236216679897546013310094057583552748854125 / 9619630419041620901435312524449124464130795720328478190417063819395928166869436184427311097384012607618805661696) := by
  show momentBQ (188 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_190, endpointB_at_189]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_191 : momentBQ 191 =
    (-4152806654729686047107614978202460374838444175641616336357875152042358459877067103652820057470621046171768475 / 38478521676166483605741250097796497856523182881313912761668255277583712667477744737709244389536050430475222646784) := by
  show momentBQ (189 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_191, endpointB_at_190]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_192 : momentBQ 192 =
    (-8240385979803931999234482077166138649548535824964254405652537605361538514625175038138318333933850138738744775 / 76957043352332967211482500195592995713046365762627825523336510555167425334955489475418488779072100860950445293568) := by
  show momentBQ (190 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_192, endpointB_at_191]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_193 : momentBQ 193 =
    (-1046529019435099363902779223800099608492664049770460309517872275880915391357397229843566428409598967619820586425 / 9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704) := by
  show momentBQ (191 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_193, endpointB_at_192]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_194 : momentBQ 194 =
    (-2076790748412658323185307993344239119443991352653296883654637728820676657460534399119616280211794842478711319175 / 19701003098197239606139520050071806902539869635232723333974146702122860885748605305707133127442457820403313995153408) := by
  show momentBQ (192 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_194, endpointB_at_193]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_195 : momentBQ 195 =
    (-8242932351947149014704572963273526401916872894551745362959129129855263021879440656299507916304546539735091318375 / 78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632) := by
  show momentBQ (193 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_195, endpointB_at_194]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_196 : momentBQ 196 =
    (-16359050360018188044567537111727460089958101590725771566488117811558906612653043764040561864665946209628104308775 / 157608024785577916849116160400574455220318957081861786671793173616982887085988842445657065019539662563226511961227264) := by
  show momentBQ (194 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_196, endpointB_at_195]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_197 : momentBQ 197 =
    (-129870828368307656108913712989020040305993908546782145701303629157069687190245592330852623782756185215210868900275 / 1260864198284623334792929283204595641762551656654894293374345388935863096687910739565256520156317300505812095689818112) := by
  show momentBQ (195 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_197, endpointB_at_196]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_198 : momentBQ 198 =
    (-257763928385828901211092699384298658678394001227369639437612786804133237012111810159204953802323189944910912385825 / 2521728396569246669585858566409191283525103313309788586748690777871726193375821479130513040312634601011624191379636224) := by
  show momentBQ (196 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_198, endpointB_at_197]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_199 : momentBQ 199 =
    (-1023244685410411698747064958161912857177867095781376447464462880949741031775352943359268149942555693417676652198275 / 10086913586276986678343434265636765134100413253239154346994763111486904773503285916522052161250538404046496765518544896) := by
  show momentBQ (197 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_199, endpointB_at_198]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_200 : momentBQ 200 =
    (-2031063571543279502538144012431937580830439712731877873107853457161546269101831219230708136820650748241116972956375 / 20173827172553973356686868531273530268200826506478308693989526222973809547006571833044104322501076808092993531037089792) := by
  show momentBQ (198 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_200, endpointB_at_199]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_201 : momentBQ 201 =
    (-32253289516107278500305726917419168783587382638182220624952712899725354753337079761383645212711933882068937530547235 / 322781234760863573706989896500376484291213224103652939103832419567580952752105149328705669160017228929487896496593436672) := by
  show momentBQ (199 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_201, endpointB_at_200]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_202 : momentBQ 202 =
    (-64025186651377134933442711642041036540554058072809482733115086800947346002893009078567534526726674721121920769593765 / 645562469521727147413979793000752968582426448207305878207664839135161905504210298657411338320034457858975792993186873344) := by
  show momentBQ (200 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_202, endpointB_at_201]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_203 : momentBQ 203 =
    (-254199008388140902062480468994638174779823537496996065108704453536434512348119768717877043021954421417523665629773265 / 2582249878086908589655919172003011874329705792829223512830659356540647622016841194629645353280137831435903171972747493376) := by
  show momentBQ (201 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_203, endpointB_at_202]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_204 : momentBQ 204 =
    (-504641381184338835128963689679010760769797466065465094772452683621591667370897865976869203634717398183556833737924265 / 5164499756173817179311838344006023748659411585658447025661318713081295244033682389259290706560275662871806343945494986752) := by
  show momentBQ (202 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_204, endpointB_at_203]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_205 : momentBQ 205 =
    (-4007446262346220161318241065098026629642509289343399282016536016994992652651247759228078970040402867928245444389398575 / 41315998049390537434494706752048189989275292685267576205290549704650361952269459114074325652482205302974450751563959894016) := by
  show momentBQ (203 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_205, endpointB_at_204]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_206 : momentBQ 206 =
    (-7956246969633715149544020065828765064704884296403724428198683702033961022580769941491844589299726669496565345690171805 / 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032) := by
  show momentBQ (204 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_206, endpointB_at_205]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_207 : momentBQ 207 =
    (-31593252529904752389936934047805484577323278419700226127507394506134854934325581612331693563335807842952380838711458915 / 330527984395124299475957654016385519914202341482140609642324397637202895618155672912594605219857642423795606012511679152128) := by
  show momentBQ (205 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_207, endpointB_at_206]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_208 : momentBQ 208 =
    (-62728631834738421411903767602164512856424480340564217093746565903485146753660937404194811857637763398325741665267679295 / 661055968790248598951915308032771039828404682964281219284648795274405791236311345825189210439715284847591212025023358304256) := by
  show momentBQ (206 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_208, endpointB_at_207]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_209 : momentBQ 209 =
    (-1992840380595920618701250463053380293054100798511770896901333209087643508404766703687112099784953560269887023673503965295 / 21153791001287955166461289857048673274508949854856999017108761448780985319561963066406054734070889115122918784800747465736192) := by
  show momentBQ (207 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_209, endpointB_at_208]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_210 : momentBQ 210 =
    (-3957075396877067257229755704149056562762927422882224508201211874504172516688890823110772829716534581397144090069397825825 / 42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384) := by
  show momentBQ (208 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_210, endpointB_at_209]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_211 : momentBQ 211 =
    (-15715242290454638535855315510763396063544197479446548761141955730173713709135880697497069238017094480405800814847037079705 / 169230328010303641331690318856389386196071598838855992136870091590247882556495704531248437872567112920983350278405979725889536) := by
  show momentBQ (209 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_211, endpointB_at_210]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_212 : momentBQ 212 =
    (-31207045117063950457456763976350061377369757080038407255537817303046379356056559299769061662223519371042798774506675527945 / 338460656020607282663380637712778772392143197677711984273740183180495765112991409062496875745134225841966700556811959451779072) := by
  show momentBQ (210 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_212, endpointB_at_211]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_213 : momentBQ 213 =
    (-247889924420451380048854672340441053582503164730116404803423039331745768092449272928354244524454748211490911020137932023865 / 2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576) := by
  show momentBQ (211 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_213, endpointB_at_212]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_214 : momentBQ 214 =
    (-492288441454699219533640969014115331762435862351357930665952796419382440859652781449266879971100274617186175406189414300915 / 5415370496329716522614090203404460358274291162843391748379842930887932241807862544999950011922147613471467208908991351228465152) := by
  show momentBQ (212 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_214, endpointB_at_213]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_215 : momentBQ 215 =
    (-1955351286151842694409321605897187065411544313077823556383457368955491003414508711363910504558108567404711444370378514746625 / 21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608) := by
  show momentBQ (213 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_215, endpointB_at_214]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_216 : momentBQ 216 =
    (-3883418600869008514012931747526041288049904286903398411980168821134858876548814975592510629982848178054938543005356399054925 / 43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216) := by
  show momentBQ (214 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_216, endpointB_at_215]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_217 : momentBQ 217 =
    (-61703206658252024167094359988469322687904034780798441434796015713587202149608949056636557787505254384650690183307329451650475 / 693167423530203714894603546035770925859109268843954143792619895153655326951406405759993601526034894524347802740350892957243539456) := by
  show momentBQ (215 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_217, endpointB_at_216]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_218 : momentBQ 218 =
    (-122553373593118075649851009931015106352472990739742526536392086509475042057518235223089200029561127372278559765002115178162925 / 1386334847060407429789207092071541851718218537687908287585239790307310653902812811519987203052069789048695605480701785914487078912) := by
  show momentBQ (216 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_218, endpointB_at_217]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_219 : momentBQ 219 =
    (-486840465741469052810876030276417807803860596241362513672089664757822873494544916069702968924770350020152443837118494239858225 / 5545339388241629719156828368286167406872874150751633150340959161229242615611251246079948812208279156194782421922807143657948315648) := by
  show momentBQ (217 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_219, endpointB_at_218]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_220 : momentBQ 220 =
    (-967011884007027570651740060138090166185750499383528280581547964244990639133000175754889458823173982916741155566879200887389625 / 11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296) := by
  show momentBQ (218 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_220, endpointB_at_219]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_221 : momentBQ 221 =
    (-7683348969292200879542007386915370956784963058738215611166117461364743805474928669179758063740491464265743363322294741596168475 / 88725430211866075506509253892578678509965986412026130405455346579667881849780019937279180995332466499116518750764914298527173050368) := by
  show momentBQ (219 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_221, endpointB_at_220]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_222 : momentBQ 222 =
    (-15262399083797629801443173044596596606464247885909849109963464097462092898658342469547121221638351822681725504518042495749855025 / 177450860423732151013018507785157357019931972824052260810910693159335763699560039874558361990664932998233037501529828597054346100736) := by
  show momentBQ (220 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_222, endpointB_at_221]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_223 : momentBQ 223 =
    (-60637099062655448130058011825829721652709309168344535653098087089916963678453414676308832961644262646870639166598709375006180775 / 709803441694928604052074031140629428079727891296209043243642772637343054798240159498233447962659731992932150006119314388217384402944) := by
  show momentBQ (221 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_223, endpointB_at_222]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_224 : momentBQ 224 =
    (-120458452398010598751639906900639312520853022249222552889338352380418004078721357406299609874477167500285619510328377816716314275 / 1419606883389857208104148062281258856159455782592418086487285545274686109596480318996466895925319463985864300012238628776434768805888) := by
  show momentBQ (222 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_224, endpointB_at_223]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_225 : momentBQ 225 =
    (-7657715902444959492068536938683499153111370700129148005107938115612287402147286292257618056306048505375300097442304018348394264625 / 90854840536950861318665475986000566794205170085914757535186274897579911014174740415773881339220445695095315200783272241691825203576832) := by
  show momentBQ (223 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_225, endpointB_at_224]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_226 : momentBQ 226 =
    (-15213328926190652857576160051517884984181256457589907370147770389683077638932608767285134538528016364012262860252043983118809939055 / 181709681073901722637330951972001133588410340171829515070372549795159822028349480831547762678440891390190630401566544483383650407153664) := by
  show momentBQ (224 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_226, endpointB_at_225]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_227 : momentBQ 227 =
    (-60449422016456664894262795248951596087587470349184676187578308893519485485670277314256862015921056172048725878346617242657926218015 / 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656) := by
  show momentBQ (225 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_227, endpointB_at_226]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_228 : momentBQ 228 =
    (-120099952993048263732654276023247444209259687786265590134792146744393339004569581800572003388459895742704737317772354081227862221695 / 1453677448591213781098647615776009068707282721374636120562980398361278576226795846652382101427527131121525043212532355867069203257229312) := by
  show momentBQ (226 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_228, endpointB_at_227]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_229 : momentBQ 229 =
    (-954478573786857253875305035763703372399905939775058111071242850442283904720526676415072237455654960902548175525453971908705641867155 / 11629419588729710248789180926208072549658261770997088964503843186890228609814366773219056811420217048972200345700258846936553626057834496) := by
  show momentBQ (227 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_229, endpointB_at_228]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_230 : momentBQ 230 =
    (-1896453061454236028442199961888580936427760710033412404093517453935542256104103221698069292761235839347857728664111603574065794976225 / 23258839177459420497578361852416145099316523541994177929007686373780457219628733546438113622840434097944400691400517693873107252115668992) := by
  show momentBQ (228 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_230, endpointB_at_229]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_231 : momentBQ 231 =
    (-7536339557257268391287698978983317286499883865089299727571630229987328791648479759269718841668563292017138973908686981159548420035955 / 93035356709837681990313447409664580397266094167976711716030745495121828878514934185752454491361736391777602765602070775492429008462675968) := by
  show momentBQ (229 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_231, endpointB_at_230]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_232 : momentBQ 232 =
    (-14974804574809896933337895373823994088759509498164452705434537989455341624963862378808662113964807580241847571532845559966375432019495 / 186070713419675363980626894819329160794532188335953423432061490990243657757029868371504908982723472783555205531204141550984858016925351936) := by
  show momentBQ (230 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_232, endpointB_at_231]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_233 : momentBQ 233 =
    (-238047755482322844354095509218374526721314961332890093007080069418583189279597950228648042570268148085913507947470407004982726695206455 / 2977131414714805823690030317109266572712515013375254774912983855843898524112477893944078543723575564536883288499266264815757728270805630976) := by
  show momentBQ (231 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_233, endpointB_at_232]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_234 : momentBQ 234 =
    (-473030518404787454660713393854538222626475652777373875803768549960532260242291205819158985879974903707201520084458362417626619999487505 / 5954262829429611647380060634218533145425030026750509549825967711687797048224955787888157087447151129073766576998532529631515456541611261952) := by
  show momentBQ (232 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_234, endpointB_at_233]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_235 : momentBQ 235 =
    (-1879993085967745012113091693524446782233428876422896173066259621638012829168080433383836995164002822426057323412590927557234002562065725 / 23817051317718446589520242536874132581700120107002038199303870846751188192899823151552628349788604516295066307994130118526061826166445047808) := by
  show momentBQ (233 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_235, endpointB_at_234]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_236 : momentBQ 236 =
    (-3735986260199731577263037535642198499161750150168053246050822311935965920091461967618093092517401353501994766100765800720120337006317845 / 47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616) := by
  show momentBQ (234 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_236, endpointB_at_235]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_237 : momentBQ 237 =
    (-29697924678536849317565501766376120272997641024217236820302299394880813839371112929031960345604427708346365174597612890470109119592594395 / 381072821083495145432323880589986121307201921712032611188861933548019011086397170424842053596617672260721060927906081896416989218663120764928) := by
  show momentBQ (235 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_237, endpointB_at_236]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_238 : momentBQ 238 =
    (-59019926259877029656427642750899378264058603048127926339081784873370731301028667466557187015948039876080751043187661060807685212354902785 / 762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235344521442121855812163792833978437326241529856) := by
  show momentBQ (236 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_238, endpointB_at_237]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_239 : momentBQ 239 =
    (-234591807738838949810842647236768116965543859174491673599879699538692066431819829509928987046583385389799960028804736821529706768435874095 / 3048582568667961163458591044719888970457615373696260889510895468384152088691177363398736428772941378085768487423248655171335913749304966119424) := by
  show momentBQ (237 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_239, endpointB_at_238]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_240 : momentBQ 240 =
    (-466238948434930967197281411872237889366666665723362112803108189459743646674118908021825392665803799414874397546787656862872848179945774875 / 6097165137335922326917182089439777940915230747392521779021790936768304177382354726797472857545882756171536974846497310342671827498609932238848) := by
  show momentBQ (238 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_240, endpointB_at_239]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_241 : momentBQ 241 =
    (-14826398560230804756873548897537164881859999970002915187138840424819847964236981275094047486772560821393005841987847488239356572122275641025 / 195109284394749514461349826862072894109287383916560696928697309976585733676235351257519131441468248197489183195087913930965498479955517831643136) := by
  show momentBQ (239 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_241, endpointB_at_240]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_242 : momentBQ 242 =
    (-29468236142533425222167759012117435595066141019217412342902508562193805704852755314398542515203554495631741901710286086583617419280373576975 / 390218568789499028922699653724145788218574767833121393857394619953171467352470702515038262882936496394978366390175827861930996959911035663286272) := by
  show momentBQ (240 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_242, endpointB_at_241]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_243 : momentBQ 243 =
    (-117142327145112211007129686651475095216750527522674176338314930730704302016811366167154536775313303408255106237377252955758016352676526367975 / 1560874275157996115690798614896583152874299071332485575429578479812685869409882810060153051531745985579913465560703311447723987839644142653145088) := by
  show momentBQ (241 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_243, endpointB_at_242]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_244 : momentBQ 244 =
    (-232838452720531678668492340134413460862923888038895585067514862316585094132180616702615807664511627762087309928614045998481983120752107965975 / 3121748550315992231381597229793166305748598142664971150859156959625371738819765620120306103063491971159826931121406622895447975679288285306290176) := by
  show momentBQ (242 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_244, endpointB_at_243]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_245 : momentBQ 245 =
    (-1851256550318981379577357130576893910139640749161710799307290298746619191050944247553584700283412122370694185497996923102684619894504464975375 / 24973988402527937851052777838345330445988785141319769206873255677002973910558124960962448824507935769278615448971252983163583805434306282450321408) := by
  show momentBQ (243 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_245, endpointB_at_244]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_246 : momentBQ 246 =
    (-3679844653083036456547644582003866670359204264660216976582246430569810392007387136973860200155190626916441095255202047146969019953566018134725 / 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642816) := by
  show momentBQ (244 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_246, endpointB_at_245]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_247 : momentBQ 247 =
    (-14629626303720364449201611386990982128501226710722326028851369955679977899931807398213151527446245663106826793331656919145267079327591730633175 / 199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571264) := by
  show momentBQ (245 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_247, endpointB_at_246]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_248 : momentBQ 248 =
    (-29081564838569631354485794295597458401190697631435878867068917604205947971119503775395374088972091581317619253141066993118729295343512306643275 / 399583814440447005616844445413525287135820562261116307309972090832047582568929999375399181192126972308457847183540047730617340886948900519205142528) := by
  show momentBQ (246 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_248, endpointB_at_247]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_249 : momentBQ 249 =
    (-462490692432736395411661180249340225541516578461222202627902463834630075798771463266771594382685198373857622316082129922823662664656502166939825 / 6393341031047152089869511126616404594173128996177860916959553453312761321102879990006386899074031556935325554936640763689877454191182408307282280448) := by
  show momentBQ (247 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_249, endpointB_at_248]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_250 : momentBQ 250 =
    (-919409207848210906541254153507724544751207655977128475103661524490529668756593872759244735821000695562488044363295800448986799273112323584880375 / 12786682062094304179739022253232809188346257992355721833919106906625522642205759980012773798148063113870651109873281527379754908382364816614564560896) := by
  show momentBQ (248 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_250, endpointB_at_249]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_251 : momentBQ 251 =
    (-3655571010404486564408026514346712789930801640165062817012158221374345962976217238090757069624298765556452464388464102585171513909894598573484371 / 51146728248377216718956089012931236753385031969422887335676427626502090568823039920051095192592252455482604439493126109519019633529459266458258243584) := by
  show momentBQ (249 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_251, endpointB_at_250]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_252 : momentBQ 252 =
    (-7267449937019278070277311675932309490738924376264407751749270726955373049900925903614692341603685593675975218047185606334663687016085277642106379 / 102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168) := by
  show momentBQ (250 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_252, endpointB_at_251]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_253 : momentBQ 253 =
    (-57793530451534258939824335708604556426352398611245528311529914828645109492069267900173981954657880673518469591137142678947087415794582922201512633 / 818347651974035467503297424206899788054160511510766197370822842024033449101168638720817523081476039287721671031890017752304314136471348263332131897344) := by
  show momentBQ (251 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_253, endpointB_at_252]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_254 : momentBQ 254 =
    (-114901762123010799394196208938450956057135401191527670911855917623748972626525066220504003648983849718497194483565149278697173795038241936234627883 / 1636695303948070935006594848413799576108321023021532394741645684048066898202337277441635046162952078575443342063780035504608628272942696526664263794688) := by
  show momentBQ (252 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_254, endpointB_at_253]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_255 : momentBQ 255 =
    (-456892833638743729874559728456045140227191949619854124492025499212545127373190223947673400336510583526307741844097640832614746192868599825184937645 / 6546781215792283740026379393655198304433284092086129578966582736192267592809349109766540184651808314301773368255120142018434513091770786106657055178752) := by
  show momentBQ (253 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_255, endpointB_at_254]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_256 : momentBQ 256 =
    (-908410457469972827632948165989077984687005170420651141637085992552001488541989974672432995963179866069953039666500015302492848312879922005367699553 / 13093562431584567480052758787310396608866568184172259157933165472384535185618698219533080369303616628603546736510240284036869026183541572213314110357504) := by
  show momentBQ (254 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_256, endpointB_at_255]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_257 : momentBQ 257 =
    (-462380922852216169265170616488440694205685631744111431093276770208968757667872897108268394945258551829606097190248507788968859791255880300732159072477 / 6703903964971298549787012499102923063739682910296196688861780721860882015036773488400937149083451713845015929093243025426876941405973284973216824503042048) := by
  show momentBQ (255 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_257, endpointB_at_256]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_258 : momentBQ 258 =
    (-919364403025223589472771147959506594315585049888097047815814901076976790538066344055739882556525758696220683518354036887794114215298656940366277377571 / 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096) := by
  show momentBQ (256 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_258, endpointB_at_257]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_259 : momentBQ 259 =
    (-3656077044588679855810322472118037851813140547229409190151263908934023980976961507756546974817811738071017136782291635065413803042234193879131010036387 / 53631231719770388398296099992823384509917463282369573510894245774887056120294187907207497192667613710760127432745944203415015531247786279785734596024336384) := by
  show momentBQ (257 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_259, endpointB_at_258]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_260 : momentBQ 260 =
    (-7269805706421506276997359355755943991057016918236083910918536344019391313525618442064176417108776235932717472752433173971768758944983049605221892543395 / 107262463439540776796592199985646769019834926564739147021788491549774112240588375814414994385335227421520254865491888406830031062495572559571469192048672768) := by
  show momentBQ (258 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_260, endpointB_at_259]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_261 : momentBQ 261 =
    (-57822916157229519157040535183474200667330426872739313568382819843969620139888380531495064733003650984264845129430891552975453051916249794552303360691311 / 858099707516326214372737599885174152158679412517913176174307932398192897924707006515319955082681819372162038923935107254640248499964580476571753536389382144) := by
  show momentBQ (259 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_261, endpointB_at_260]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_262 : momentBQ 262 =
    (-114981201094260997864000144675184330062622572976826451118738250954100509013801032551133864354133696784802508130937290099594866413580588671925844613788469 / 1716199415032652428745475199770348304317358825035826352348615864796385795849414013030639910165363638744324077847870214509280496999929160953143507072778764288) := by
  show momentBQ (260 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_262, endpointB_at_261]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_263 : momentBQ 263 =
    (-457291647100076182344611262410465923378827179549057870479867395015926451879315556940005674263386687212840509436781130854113934362408295405140191173922079 / 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057152) := by
  show momentBQ (261 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_263, endpointB_at_262]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_264 : momentBQ 264 =
    (-909367039670493701012287795591915125198200056669799491486580409100112297843657932622140561367875427423253180362876545386698051983040070330373840243198659 / 13729595320261219429963801598162786434538870600286610818788926918371086366795312104245119281322909109954592622782961716074243975999433287625148056582230114304) := by
  show momentBQ (262 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_264, endpointB_at_263]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_265 : momentBQ 265 =
    (-14467202903848763425195487657144104264516819083383173728195597417501786556603648928079508930852563618097209687591217767515650827002910209801402003869069575 / 219673525124179510879420825570604582952621929604585773100622830693937381868724993667921908501166545759273481964527387457187903615990932602002368905315681828864) := by
  show momentBQ (263 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_265, endpointB_at_264]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_266 : momentBQ 266 =
    (-28770626152182257830483101869112992254340994931860122848147471090654496284264615038105287571921890666932941529662534956531124474832202568171090022788677985 / 439347050248359021758841651141209165905243859209171546201245661387874763737449987335843817002333091518546963929054774914375807231981865204004737810631363657728) := by
  show momentBQ (264 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_266, endpointB_at_265]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_267 : momentBQ 267 =
    (-114433543116574544303199705930532127086814934728977481102782046668843823566736701918478925755990076412086662174372037533871916144257407207236891895151959805 / 1757388200993436087035366604564836663620975436836686184804982645551499054949799949343375268009332366074187855716219099657503228927927460816018951242525454630912) := by
  show momentBQ (265 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_267, endpointB_at_266]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_268 : momentBQ 268 =
    (-227581316085771846535576943255103219037822960078977687136993508543655694059689845388435616391126331740891451740043265657250889410489450288549773769010077365 / 3514776401986872174070733209129673327241950873673372369609965291102998109899599898686750536018664732148375711432438199315006457855854921632037902485050909261824) := by
  show momentBQ (266 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_268, endpointB_at_267]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_269 : momentBQ 269 =
    (-1810460320503229764230783742611492772345666234658135929015187164981619178116637128239346022932393056983509608618553143213652597847625029907418349535557779635 / 28118211215894977392565865673037386617935606989386978956879722328823984879196799189494004288149317857187005691459505594520051662846839373056303219880407274094592) := by
  show momentBQ (267 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_269, endpointB_at_268]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_270 : momentBQ 270 =
    (-3600729633714601947447841272480106443141009054059861420160316480539651525250560831256691904345093998089879704873330600815257025459031193310293000005663242025 / 56236422431789954785131731346074773235871213978773957913759444657647969758393598378988008576298635714374011382919011189040103325693678746112606439760814548189184) := by
  show momentBQ (268 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_270, endpointB_at_269]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_271 : momentBQ 271 =
    (-14322902320775861079848079728309756740494236015038115426859925555924391622663341973221063352839373903513077048273915056576244612381479635612054377800304896055 / 224945689727159819140526925384299092943484855915095831655037778630591879033574393515952034305194542857496045531676044756160413302774714984450425759043258192756736) := by
  show momentBQ (269 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_271, endpointB_at_270]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_272 : momentBQ 272 =
    (-28487248527299590856229206544498003258768978642455882712463099168425265994891296396923074343839197542411618188264355038725445926470913371198883061381418224995 / 449891379454319638281053850768598185886969711830191663310075557261183758067148787031904068610389085714992091063352089512320826605549429968900851518086516385513472) := by
  show momentBQ (270 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_272, endpointB_at_271]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_273 : momentBQ 273 =
    (-906564791368769332542352984739612927234942202680507796908384508830474641366834785337375483530412110026157967050059769173556838012986125518740925659255721160135 / 14396524142538228424993723224595141948383030778566133225922417832357880258148761185020930195532450742879746914027266864394266451377581759004827248578768524336431104) := by
  show momentBQ (271 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_273, endpointB_at_272]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_274 : momentBQ 274 =
    (-1803167332282936804287537255361208129994775150386504519125468088992482528432935122484230357351698812249830681714954046378173490992862513394418764223354786043785 / 28793048285076456849987446449190283896766061557132266451844835664715760516297522370041860391064901485759493828054533728788532902755163518009654497157537048672862208) := by
  show momentBQ (272 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_274, endpointB_at_273]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_275 : momentBQ 275 =
    (-7173183913096354440413925577896776867497463189493758853455329259130678671503282056597850691654568267709180449158028870628500383876715837955899463516265389736225 / 115172193140305827399949785796761135587064246228529065807379342658863042065190089480167441564259605943037975312218134915154131611020654072038617988630148194691448832) := by
  show momentBQ (273 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_275, endpointB_at_274]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_276 : momentBQ 276 =
    (-14268114910777112286932426513125588896440408598738494883054782199070840848408346490760088466672904881588806202507061062668326218111140230406825478339626066129873 / 230344386280611654799899571593522271174128492457058131614758685317726084130380178960334883128519211886075950624436269830308263222041308144077235977260296389382897664) := by
  show momentBQ (274 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_276, endpointB_at_275]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_277 : momentBQ 277 =
    (-113524566464009197761244958778347076871678033633441067982566310540433211967770756861265051713093112753510936306904007585578421648449507050628220110267459569642033 / 1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312) := by
  show momentBQ (275 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_277, endpointB_at_276]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_278 : momentBQ 278 =
    (-225819624987974974608108203201694004896370384592151727286621072591258844022533166175296185898607599737128252364996780431962853170742521245112452277102419577157979 / 3685510180489786476798393145496356338786055879312930105836138965083617346086082863365358130056307390177215209990980317284932211552660930305235775636164742230126362624) := by
  show momentBQ (276 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_278, endpointB_at_277]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_279 : momentBQ 279 =
    (-898404695096044323440890909140552407969013112801869821507204698870260005355833387733372595697338148594474270200310932222125595708061973011130835318256388677470233 / 14742040721959145907193572581985425355144223517251720423344555860334469384344331453461432520225229560708860839963921269139728846210643721220943102544658968920505450496) := by
  show momentBQ (277 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_279, endpointB_at_278]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_280 : momentBQ 280 =
    (-1787149124653421503618976539688195650260940063100493730955192142913958075170206201405096023699005994515889677280188413560142314042918978570529081009434751670236485 / 29484081443918291814387145163970850710288447034503440846689111720668938768688662906922865040450459121417721679927842538279457692421287442441886205089317937841010900992) := by
  show momentBQ (278 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_280, endpointB_at_279]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_281 : momentBQ 281 =
    (-28441201783770165071879140931609285062724103289913571661201200674373561367708710119503956720009895398438587149858998467228550540625882030393848517778718762294906347 / 471745303102692669030194322623533611364615152552055053547025787530703020299018606510765840647207345942683546878845480612471323078740599079070179281429087005456174415872) := by
  show momentBQ (279 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_281, endpointB_at_280]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_282 : momentBQ 282 =
    (-56578760843870186032670604202027011921931579142568279568012352942970892542879604828479401446567727856680321056125196239077436840604512651210538510456597110757482733 / 943490606205385338060388645247067222729230305104110107094051575061406040598037213021531681294414691885367093757690961224942646157481198158140358562858174010912348831744) := by
  show momentBQ (280 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_282, endpointB_at_281]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_283 : momentBQ 283 =
    (-225111239953270740172540489059128749561727772333197197430176808517777806500393321338843575968258832110621702925434291419308099770064763101624908541603907653439346193 / 3773962424821541352241554580988268890916921220416440428376206300245624162392148852086126725177658767541468375030763844899770584629924792632561434251432696043649395326976) := by
  show momentBQ (281 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_283, endpointB_at_282]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_284 : momentBQ 284 =
    (-447836141673821295820283729117630692590999066514452375099609693270349487843538656939112838410352376248339288858726169855372650779316118820547079536830388723980042073 / 7547924849643082704483109161976537781833842440832880856752412600491248324784297704172253450355317535082936750061527689799541169259849585265122868502865392087298790653952) := by
  show momentBQ (282 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_284, endpointB_at_283]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_285 : momentBQ 285 =
    (-3563766479517028621668455027485371004421330599727684393398302488700668459599990720712658502842944965919883073312398393919514756201600100473367604764917882099277799595 / 60383398797144661635864873295812302254670739526663046854019300803929986598274381633378027602842540280663494000492221518396329354078796682120982948022923136698390325231616) := by
  show momentBQ (283 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_285, endpointB_at_284]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_286 : momentBQ 286 =
    (-7090019627670720099950926317839317050901384035247708951076622845941329882783139433838867968813858932198504219537297857376718830758972831468068182111257681229089517089 / 120766797594289323271729746591624604509341479053326093708038601607859973196548763266756055205685080561326988000984443036792658708157593364241965896045846273396780650463232) := by
  show momentBQ (284 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_286, endpointB_at_285]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_287 : momentBQ 287 =
    (-28211336840172305852252287236717282531209003608782841910227960834549767155969275089890320798986613513433209097319737628303167934978010776960355214135004339995468078487 / 483067190377157293086918986366498418037365916213304374832154406431439892786195053067024220822740322245307952003937772147170634832630373456967863584183385093587122601852928) := by
  show momentBQ (285 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_287, endpointB_at_286]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_288 : momentBQ 288 =
    (-56127781657625040563191832795001980227597007179843215089686988280585076815534690161419418732478593436133666880033345594986442128475415169492553405125740341942203041171 / 966134380754314586173837972732996836074731832426608749664308812862879785572390106134048441645480644490615904007875544294341269665260746913935727168366770187174245203705856) := by
  show momentBQ (286 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_288, endpointB_at_287]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_289 : momentBQ 289 =
    (-3573468765535460915856546687948459407823676123783351360710071587197249890589041940277036325967803782100510124695456336214136815512934765791025900126338801770320260287887 / 61832600368276133515125630254911797508782837275302959978515764023224306276632966792579100265310761247399417856504034834837841258576687802491886538775473291979151693037174784) := by
  show momentBQ (287 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_289, endpointB_at_288]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_290 : momentBQ 290 =
    (-7109842699594775178607316074637938268161293325866529523904121670029130405151208012661923485922100950545997652940786828107711657162413461348926963919186197293889791230225 / 123665200736552267030251260509823595017565674550605919957031528046448612553265933585158200530621522494798835713008069669675682517153375604983773077550946583958303386074349568) := by
  show momentBQ (288 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_290, endpointB_at_289]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_291 : momentBQ 291 =
    (-28292270604594381227975319828042002625717698269137845070983987611081436163946531195213309319841739644586487212047131033228618111604914256540212815043934040266030410619585 / 494660802946209068121005042039294380070262698202423679828126112185794450213063734340632802122486089979195342852032278678702730068613502419935092310203786335833213544297398272) := by
  show momentBQ (289 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_291, endpointB_at_290]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_292 : momentBQ 292 =
    (-56292868316357892546383883781568108317149647071583547409277418648852754429295675470888337100303667540259711669330889581578590675667509809404753333025559482178802775768865 / 989321605892418136242010084078588760140525396404847359656252224371588900426127468681265604244972179958390685704064557357405460137227004839870184620407572671666427088594796544) := by
  show momentBQ (290 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_292, endpointB_at_291]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_293 : momentBQ 293 =
    (-448029540983615555745877212014946177154300615734110151298495619657307538676997088336796217195567545765628664107962285573933714829627715058413173787504795330765539900297405 / 7914572847139345089936080672628710081124203171238778877250017794972711203409019749450124833959777439667125485632516458859243681097816038718961476963260581373331416708758372352) := by
  show momentBQ (291 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_293, endpointB_at_292]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_294 : momentBQ 294 =
    (-891471748783098529009714725613357069218284160317359106508610738089454931906789428328847080631453512564373758276252602353595070804344566140119045454318415282717780757247055 / 15829145694278690179872161345257420162248406342477557754500035589945422406818039498900249667919554879334250971265032917718487362195632077437922953926521162746662833417516744704) := by
  show momentBQ (292 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_294, endpointB_at_293]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_295 : momentBQ 295 =
    (-3547693694136820676671313703971523030562559413507857668758757018927422688200488541308677157614968060205160874772841988958184465445861028516800282930450836329183005054350525 / 63316582777114760719488645381029680648993625369910231018000142359781689627272157995600998671678219517337003885060131670873949448782528309751691815706084650986651333670066978816) := by
  show momentBQ (293 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_295, endpointB_at_294]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_296 : momentBQ 296 =
    (-7059309147316317753240885234682318708271940256708855768004713119018295315165039911010825394983004241831964181327655076333743326158374317760548359593812342119425165989504265 / 126633165554229521438977290762059361297987250739820462036000284719563379254544315991201997343356439034674007770120263341747898897565056619503383631412169301973302667340133957632) := by
  show momentBQ (294 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_296, endpointB_at_295]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_297 : momentBQ 297 =
    (-112376569939711112342131929816969884301950616518959893171750703435183133530600229934739896152567283741595321697351049728664184300196823598944945508128526202928146561292378705 / 2026130648867672343023636652192949780767796011837127392576004555513014068072709055859231957493703024554784124321924213467966382361040905912054138102594708831572842677442143322112) := by
  show momentBQ (295 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_297, endpointB_at_296]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_298 : momentBQ 298 =
    (-223618023011344334660605961352960274823073449032677767220554430067990679853820659567108682242987423202972508832102593904513578859987618676688426920215350120978231036107056615 / 4052261297735344686047273304385899561535592023674254785152009111026028136145418111718463914987406049109568248643848426935932764722081811824108276205189417663145685354884286644224) := by
  show momentBQ (296 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_298, endpointB_at_297]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_299 : momentBQ 299 =
    (-889969715743135506400935134780573442752231914606563194374421322351130692304131886733526500470413033284313407633804283123332565530017838089102262843541628333826114123567010555 / 16209045190941378744189093217543598246142368094697019140608036444104112544581672446873855659949624196438272994575393707743731058888327247296433104820757670652582741419537146576896) := by
  show momentBQ (297 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_299, endpointB_at_298]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_300 : momentBQ 300 =
    (-1771009969455403432470088311687094309155779228063227761380537414043219939534978169252335343745470751853399590441851332636732028395854895194032931076612939326510160212449402275 / 32418090381882757488378186435087196492284736189394038281216072888208225089163344893747711319899248392876545989150787415487462117776654494592866209641515341305165482839074293153792) := by
  show momentBQ (298 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_300, endpointB_at_299]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_301 : momentBQ 301 =
    (-14097239356865011322461902961029270700880002655383292980589077815784030718698426227248589336213947184753060739917136607788386946031004965744502131369838997039020875291097242109 / 259344723055062059907025491480697571938277889515152306249728583105665800713306759149981690559193987143012367913206299323899696942213235956742929677132122730441323862712594345230336) := by
  show momentBQ (299 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_301, endpointB_at_300]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_302 : momentBQ 302 =
    (-28053974666983859741377673998858914119026982028487018257052683095198120931894874784458156187349350045405592635250381488588849769676318852096201915915393884473001675413180225991 / 518689446110124119814050982961395143876555779030304612499457166211331601426613518299963381118387974286024735826412598647799393884426471913485859354264245460882647725425188690460672) := by
  show momentBQ (300 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_302, endpointB_at_301]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_303 : momentBQ 303 =
    (-111658534932829799367999881280226538977054411914706609089328890994795170066680925466618224295344101836349411746923703805575488156128924702714022195133455129591218588896167654441 / 2074757784440496479256203931845580575506223116121218449997828664845326405706454073199853524473551897144098943305650394591197575537705887653943437417056981843530590901700754761842688) := by
  show momentBQ (301 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_303, endpointB_at_302]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_304 : momentBQ 304 =
    (-222211539816819699732356199379460735984038978166891370563911951385681477063394713057329337459051133357487443179521430345749238805761523418272460012097272089582524122456729688541 / 4149515568880992958512407863691161151012446232242436899995657329690652811412908146399707048947103794288197886611300789182395151075411775307886874834113963687061181803401509523685376) := by
  show momentBQ (302 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_304, endpointB_at_303]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_305 : momentBQ 305 =
    (-7075683241535574649372394769714407645807556936366804167956143715175647032808094810509697324353996614804205427558445545219909972499248508844991489858886821799864583899280076924595 / 132784498204191774672397051638117156832398279431757980799861034550100889965213060684790625566307321417222332371561625253836644834413176809852379994691646837985957817708848304757932032) := by
  show momentBQ (303 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_305, endpointB_at_304]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_306 : momentBQ 306 =
    (-14081769598728176433341126640054575216410449378277541409670095852824976225949224754030774675025822771102139982058939167044214273137848671701343719161784592893500991563485267846653 / 265568996408383549344794103276234313664796558863515961599722069100201779930426121369581251132614642834444664743123250507673289668826353619704759989383293675971915635417696609515864064) := by
  show momentBQ (304 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_306, endpointB_at_305]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_307 : momentBQ 307 =
    (-56050965265525878744475464861393701351594533799810606003196656041636670075837110295455828608436118088896753261920875508038735244058495693242603431173377889360405907595833517115109 / 1062275985633534197379176413104937254659186235454063846398888276400807119721704485478325004530458571337778658972493002030693158675305414478819039957533174703887662541670786438063456256) := by
  show momentBQ (305 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_307, endpointB_at_306]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_308 : momentBQ 308 =
    (-111554201228782774960503286743685835589004104728613290775091716095895783115102522444701991139265368574318945417047735945966342782148993057235279141520957297717289933358482993346357 / 2124551971267068394758352826209874509318372470908127692797776552801614239443408970956650009060917142675557317944986004061386317350610828957638079915066349407775325083341572876126912512) := by
  show momentBQ (306 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_308, endpointB_at_307]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_309 : momentBQ 309 =
    (-888087342249920013646604087972459963844928781800518795391314570997196299344907094267562604784021700468279396631821586167238547083861464208899040438342166538970113365568182791185933 / 16996415770136547158066822609678996074546979767265021542382212422412913915547271767653200072487337141404458543559888032491090538804886631661104639320530795262202600666732583009015300096) := by
  show momentBQ (307 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_309, endpointB_at_308]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_310 : momentBQ 310 =
    (-1767552477293530124248095514896643617361266022030158767526402786936167391900057808979129456123538335883468702034208011303727205361083496726449546503496545053290031455742499730030255 / 33992831540273094316133645219357992149093959534530043084764424844825827831094543535306400144974674282808917087119776064982181077609773263322209278641061590524405201333465166018030600192) := by
  show momentBQ (308 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_310, endpointB_at_309]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_311 : momentBQ 311 =
    (-7035999216065213462329515694782123302657426681242631997185745287352356650337649471871760480182084859613549607452298986931610875534119467614318517371983021276644834891568531183410757 / 135971326161092377264534580877431968596375838138120172339057699379303311324378174141225600579898697131235668348479104259928724310439093053288837114564246362097620805333860664072122400768) := by
  show momentBQ (309 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_311, endpointB_at_310]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_312 : momentBQ 312 =
    (-14004127057055842871967749887685319370884074326974884907581917469038934940704196215719034524864020990677772369816633674953913607574340676698595377020120547171199848224697494541901153 / 271942652322184754529069161754863937192751676276240344678115398758606622648756348282451201159797394262471336696958208519857448620878186106577674229128492724195241610667721328144244801536) := by
  show momentBQ (310 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_312, endpointB_at_311]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_313 : momentBQ 313 =
    (-222988792370043036499794171288527777674846414283369321220727455083927656363520662819526165126680949620792221580926397747343085905222193852046864849474227174187566814039413951551810667 / 4351082437154956072465106588077822995084026820419845514849846380137705962380101572519219218556758308199541387151331336317719177934050977705242787666055883587123865770683541250307916824576) := by
  show momentBQ (311 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_313, endpointB_at_312]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_314 : momentBQ 314 =
    (-443840311969766171691283606111031327448655961976163217637422378649479009311416526953881152951828216018381961804847111171229209325729797986661970610934324375459597843918705724654242957 / 8702164874309912144930213176155645990168053640839691029699692760275411924760203145038438437113516616399082774302662672635438355868101955410485575332111767174247731541367082500615833649152) := by
  show momentBQ (312 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_314, endpointB_at_313]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_315 : momentBQ 315 =
    (-1766880222809578708962116266365570571053566727612114719894197367235187138978568976727233889139443535105023733299550601796294623111981679883208481731426450539249991416873828521712750625 / 34808659497239648579720852704622583960672214563358764118798771041101647699040812580153753748454066465596331097210650690541753423472407821641942301328447068696990926165468330002463334596608) := by
  show momentBQ (313 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_315, endpointB_at_314]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_316 : momentBQ 316 =
    (-3516933014925732858791259996860992850954242343532685490075116664306229638538294439390398884096606655589999621520057864527862630765754010434195930303505982501935697201206001533694903625 / 69617318994479297159441705409245167921344429126717528237597542082203295398081625160307507496908132931192662194421301381083506846944815643283884602656894137393981852330936660004926669193216) := by
  show momentBQ (314 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_316, endpointB_at_315]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_317 : momentBQ 317 =
    (-28001909701117543901008892886399550674053397899772900927306941542387575223298572181981783520212222612229237492862232870734501199388092057760876457732978012578703209361500948920178409875 / 556938551955834377275533643273961343370755433013740225900780336657626363184653001282460059975265063449541297555370411048668054775558525146271076821255153099151854818647493280039413353545728) := by
  show momentBQ (315 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_317, endpointB_at_316]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_318 : momentBQ 318 =
    (-55738817102224511676771644830656518849614176891976973139213501934531734908206306141421152685343572455257567375381920950894227939475981351568179952143561911473696293713271604948367749625 / 1113877103911668754551067286547922686741510866027480451801560673315252726369306002564920119950530126899082595110740822097336109551117050292542153642510306198303709637294986560078826707091456) := by
  show momentBQ (316 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_318, endpointB_at_317]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_319 : momentBQ 319 =
    (-221903592614516452147147491684311801457897949513342289290076394494079171049651520676223834275613090340742390871803496615824190476027020097752565469854557798508489018367930351775577267375 / 4455508415646675018204269146191690746966043464109921807206242693261010905477224010259680479802120507596330380442963288389344438204468201170168614570041224793214838549179946240315306828365824) := by
  show momentBQ (317 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_319, endpointB_at_318]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_320 : momentBQ 320 =
    (-441720317586890116343067890970338538952241999814960356423819782143386437669369014512232397382490007418092220073966207997016805493031842514335044117108602514272384096124250073283672616875 / 8911016831293350036408538292383381493932086928219843614412485386522021810954448020519360959604241015192660760885926576778688876408936402340337229140082449586429677098359892480630613656731648) := by
  show momentBQ (318 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_320, endpointB_at_319]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_321 : momentBQ 321 =
    (-56275168460569800822106849309621129862515630776425949408394640245067432159077612448858407426529226945064948837423294898819941019812256736326284620519635960318301733846229459336339891389875 / 1140610154405548804660292901425072831223307126812139982644798129474818791802169346626478202829342849944660577393398601827672176180343859499563165329930553547062998668590066237520718548061650944) := by
  show momentBQ (319 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_321, endpointB_at_320]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_322 : momentBQ 322 =
    (-112024400767302500701951017784572903371175975283913338541944470768218346260593751884176082073371264853260131797861325359333153618878604531191575926828808033156993171114456774192900905290125 / 2281220308811097609320585802850145662446614253624279965289596258949637583604338693252956405658685699889321154786797203655344352360687718999126330659861107094125997337180132475041437096123301888) := by
  show momentBQ (320 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_322, endpointB_at_321]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_323 : momentBQ 323 =
    (-446010191874788217080438524223051124602011181099307142890598793555453167410190030793520923037459507894035680015087636989643176830442145990644721547187987262444923122263147777997822858950125 / 9124881235244390437282343211400582649786457014497119861158385035798550334417354773011825622634742799557284619147188814621377409442750875996505322639444428376503989348720529900165748384493207552) := by
  show momentBQ (321 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_323, endpointB_at_322]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_324 : momentBQ 324 =
    (-887877874227519577655485978561677625755706468875710504268281808842589432336694086068835769390360568346331090556350930601673568736762538303357758374123454519356302066920136288707740242430125 / 18249762470488780874564686422801165299572914028994239722316770071597100668834709546023651245269485599114569238294377629242754818885501751993010645278888856753007978697441059800331496768986415104) := by
  show momentBQ (322 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_324, endpointB_at_323]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_325 : momentBQ 325 =
    (-7070138628108026266515906866324469982869514474380657719173355144487286220458860314992581126626945266461525350726498151087400639940886879082293261127279360061540923866215900076746820448980625 / 145998099763910246996517491382409322396583312231953917778534160572776805350677676368189209962155884792916553906355021033942038551084014015944085162231110854024063829579528478402651974151891320832) := by
  show momentBQ (323 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_325, endpointB_at_324]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_326 : momentBQ 326 =
    (-14075014438110439982879359207729021781281771892074724751708187010717766721959638842462153812085026422771098159753982473087840658590011725434596122921076141414821469973666730306631362555355275 / 291996199527820493993034982764818644793166624463907835557068321145553610701355352736378419924311769585833107812710042067884077102168028031888170324462221708048127659159056956805303948303782641664) := by
  show momentBQ (324 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_326, endpointB_at_325]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_327 : momentBQ 327 =
    (-56041008406955064717108614268810645006453189926113474624899468527336384064735003734711274994129951830542593286382421012478580290950414784092348980219499483301957877379814159319041437413653825 / 1167984798111281975972139931059274579172666497855631342228273284582214442805421410945513679697247078343332431250840168271536308408672112127552681297848886832192510636636227827221215793215130566656) := by
  show momentBQ (325 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_327, endpointB_at_326]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_328 : momentBQ 328 =
    (-111567879122103202234977699966347797856883873522629577922964996976440324238967851471856391502075225203924245349953994125760109386571009249064584667042489797032338159554308922681027448795989725 / 2335969596222563951944279862118549158345332995711262684456546569164428885610842821891027359394494156686664862501680336543072616817344224255105362595697773664385021273272455654442431586430261133312) := by
  show momentBQ (326 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_328, endpointB_at_327]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_329 : momentBQ 329 =
    (-1776922562603253440474157026293295414647443156348222302041369342088183700684048951490785942703783464833232493012681906441984181205630952186321311892164532621027239468023505524651485952775153425 / 37375513539561023231108477793896786533525327931380202951304745106630862169773485150256437750311906506986637800026885384689161869077507588081685801531164378630160340372359290471078905382884178132992) := by
  show momentBQ (327 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_329, endpointB_at_328]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_330 : momentBQ 330 =
    (-3537642183906173262950069459641667162899924824948588473668987595950639282516875572116914262829720879835158914660506531062308932187502351617144253159172549747029914442417617381904934039719530375 / 74751027079122046462216955587793573067050655862760405902609490213261724339546970300512875500623813013973275600053770769378323738155015176163371603062328757260320680744718580942157810765768356265984) := by
  show momentBQ (328 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_330, endpointB_at_329]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_331 : momentBQ 331 =
    (-14086247968644580810655731121118638339546973393886197740609241518421636415839922732610985882903797685161814587466380550957193748164782090984628935306523425356355477507081058302494191903610493675 / 299004108316488185848867822351174292268202623451041623610437960853046897358187881202051502002495252055893102400215083077513294952620060704653486412249315029041282722978874323768631243063073425063936) := by
  show momentBQ (329 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_331, endpointB_at_330]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_332 : momentBQ 332 =
    (-28044826016123198653239053803073059413176602618039287948826254261751838060539302358884107845418739197950561369004062788763718066587889419815318635549845732053892023193856245985932545209907297075 / 598008216632976371697735644702348584536405246902083247220875921706093794716375762404103004004990504111786204800430166155026589905240121409306972824498630058082565445957748647537262486126146850127872) := by
  show momentBQ (330 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_332, endpointB_at_331]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_333 : momentBQ 333 =
    (-223344939718764268792662826070256533398912461813541799206917518879734517566463600713522834768937188070425554998935969920154429421862589234914766483113831673344850931700469621647004968478900281525 / 4784065733063810973581885157618788676291241975216665977767007373648750357731006099232824032039924032894289638403441329240212719241920971274455782595989040464660523567661989180298099889009174801022976) := by
  show momentBQ (331 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_333, endpointB_at_332]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_334 : momentBQ 334 =
    (-444677762863485616244851212266006251181618505052186825448006952003795751190886988808004923278694761833910339232115759931118278398483173161406877412325736935218126629782016093549442324629161821775 / 9568131466127621947163770315237577352582483950433331955534014747297500715462012198465648064079848065788579276806882658480425438483841942548911565191978080929321047135323978360596199778018349602045952) := by
  show momentBQ (332 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_334, endpointB_at_333]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_335 : momentBQ 335 =
    (-1770722828168969669478000336268827287639379077004216999538470796901342362526585913516905832217556985745810632271598684755650629550846168576859721432315060251018288675479285641978318238792770128625 / 38272525864510487788655081260950309410329935801733327822136058989190002861848048793862592256319392263154317107227530633921701753935367770195646260767912323717284188541295913442384799112073398408183808) := by
  show momentBQ (333 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_335, endpointB_at_334]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_336 : momentBQ 336 =
    (-3525588436981202297139779774003903883150644311527799219976597079203568226284277027808287134594359729828225945448227829050802895254968341614225176702549687126654324019536368725968770941118739330725 / 76545051729020975577310162521900618820659871603466655644272117978380005723696097587725184512638784526308634214455061267843403507870735540391292521535824647434568377082591826884769598224146796816367616) := by
  show momentBQ (334 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_336, endpointB_at_335]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_337 : momentBQ 337 =
    (-112315174492401158894595841371838652277513383067242746579254449808913673494484825314464004430648888535956340833564972268332720805979705739996030629238368604177702036622372889413005131409925552964525 / 2449441655328671218473925200700819802261115891310932980616707775308160183158275122807205904404441104841876294862561960570988912251863537292521360689146388717906188066642938460312627143172697498123763712) := by
  show momentBQ (335 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_337, endpointB_at_336]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_338 : momentBQ 338 =
    (-223630510636205274831673025402088236433861958570088673456022954960774703011273940017820020691292000616102981303626398789469601367395793921475776119344051434430973491316356702659128911501661857683075 / 4898883310657342436947850401401639604522231782621865961233415550616320366316550245614411808808882209683752589725123921141977824503727074585042721378292777435812376133285876920625254286345394996247527424) := by
  show momentBQ (336 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_338, endpointB_at_337]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_339 : momentBQ 339 =
    (-890552270166663609240922757962162030295793479986211107904754134252079142760871962319484461096091813104362759865920511155698471717499226681379865848038737369065355974295313969760909807340937456927275 / 19595533242629369747791401605606558418088927130487463844933662202465281465266200982457647235235528838735010358900495684567911298014908298340170885513171109743249504533143507682501017145381579984990109696) := by
  show momentBQ (337 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_339, endpointB_at_338]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_340 : momentBQ 340 =
    (-1773223546792029310435465668508729706341181707937146011314775931032900947975187535591893838465669539367093990883470044336567753419799345162039555892112530159643407913419872948638979704882397591226875 / 39191066485258739495582803211213116836177854260974927689867324404930562930532401964915294470471057677470020717800991369135822596029816596680341771026342219486499009066287015365002034290763159969980219392) := by
  show momentBQ (338 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_340, endpointB_at_339]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_341 : momentBQ 341 =
    (-14123204013861221684291885383298941308152706073805268819530627121285575785637670136420142689897156213547325080330696706068898459590637137349420933399531563742101025381002988073277520708298625520712875 / 313528531882069915964662425689704934689422834087799421518938595239444503444259215719322355763768461419760165742407930953086580768238532773442734168210737755891992072530296122920016274326105279759841755136) := by
  show momentBQ (339 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_341, endpointB_at_340]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_342 : momentBQ 342 =
    (-28122156966016919424147185264692026827670637607371781608390896819216733015976475139675298787214572049849365775790448866336604264111561924516882151842469008155092657576835861881980752378107820318369625 / 627057063764139831929324851379409869378845668175598843037877190478889006888518431438644711527536922839520331484815861906173161536477065546885468336421475511783984145060592245840032548652210559519683510272) := by
  show momentBQ (340 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_342, endpointB_at_341]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_343 : momentBQ 343 =
    (-111995256689225275601428264124299826138267276085498147808854975051968392888187015029934961836801892198522912826393541976463318736023237839742671025758604646512386548595469134161572469997025880917015875 / 2508228255056559327717299405517639477515382672702395372151508761915556027554073725754578846110147691358081325939263447624692646145908262187541873345685902047135936580242368983360130194608842238078734041088) := by
  show momentBQ (341 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_343, endpointB_at_342]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_344 : momentBQ 344 =
    (-223010963028399018180103511361215105692234838385991938639789935744881668637410295234535215552582193503181193762177227900654363547241607710041528602312323538099008783354826293388787163288538415936798375 / 5016456510113118655434598811035278955030765345404790744303017523831112055108147451509157692220295382716162651878526895249385292291816524375083746691371804094271873160484737966720260389217684476157468082176) := by
  show momentBQ (342 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_344, endpointB_at_343]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_345 : momentBQ 345 =
    (-3552616504057054126822579192614705753469322425451266929494328046168463791084326796178060991942297733713467854118404677022052070461872122822754583548463758688321418990652465371426028066340670114342020625 / 80263304161809898486953580976564463280492245526476651908848280381297792881730359224146523075524726123458602430056430323990164676669064390001339947061948865508349970567755807467524166227482951618519489314816) := by
  show momentBQ (343 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_345, endpointB_at_344]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_346 : momentBQ 346 =
    (-7074340690687525174281483783554501022125868134159479363949574978891984418767920315867617105693792878438122944287953661200434122919727966316615648979114789040222651729212300609187481975582725705950632375 / 160526608323619796973907161953128926560984491052953303817696560762595585763460718448293046151049452246917204860112860647980329353338128780002679894123897731016699941135511614935048332454965903237038978629632) := by
  show momentBQ (344 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_346, endpointB_at_345]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_347 : momentBQ 347 =
    (-28174686334587889277918741773809544533206492164369255963937902661598712511740445651056579108803602851120616812800000419463000639836373230012417237841676818778690214112296387975318931105066462493641535875 / 642106433294479187895628647812515706243937964211813215270786243050382343053842873793172184604197808987668819440451442591921317413352515120010719576495590924066799764542046459740193329819863612948155914518528) := by
  show momentBQ (345 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_347, endpointB_at_346]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_348 : momentBQ 348 =
    (-56105787484726891905019742264272032485434253848931284931069425761281586010411089178328807389577203372116271520590202564406148248204420466681787640774059601660158322627080127063243174044959439720767438875 / 1284212866588958375791257295625031412487875928423626430541572486100764686107685747586344369208395617975337638880902885183842634826705030240021439152991181848133599529084092919480386659639727225896311829037056) := by
  show momentBQ (346 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_348, endpointB_at_347]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_349 : momentBQ 349 =
    (-446911617550755587243433119415408258763286642727694028244035770719174012703619365523929465758356344102029611077804716978545525701214521648396308448924405792534364569891569287986523213944332088810250978625 / 10273702932711667006330058365000251299903007427389011444332579888806117488861485980690754953667164943802701111047223081470741078613640241920171513223929454785068796232672743355843093277117817807170494632296448) := by
  show momentBQ (347 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_349, endpointB_at_348]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_350 : momentBQ 350 =
    (-889981587959241069152395467030684068310843027781511030457320517621277761687723378335618850149162347137279597991616843266731061210154992967436774704878114687138634315400116490402961701121234388891474011875 / 20547405865423334012660116730000502599806014854778022888665159777612234977722971961381509907334329887605402222094446162941482157227280483840343026447858909570137592465345486711686186554235635614340989264592896) := by
  show momentBQ (348 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_350, endpointB_at_349]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_351 : momentBQ 351 =
    (-3544669524614805858281255088687924546358043373506932504164299433040174856550532541142436220308378034026765027429468227182351712362731600561733896967428833925346446387622178250347796032465716394613470778725 / 82189623461693336050640466920002010399224059419112091554660639110448939910891887845526039629337319550421608888377784651765928628909121935361372105791435638280550369861381946846744746216942542457363957058371584) := by
  show momentBQ (349 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_351, endpointB_at_350]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_352 : momentBQ 352 =
    (-7059042728506408247688311415934071959841231675445429687780186050413339671592086171676817430186769931010566251205693136183657683594157802828068358918042036791501897506974081472914841671491554871324262320025 / 164379246923386672101280933840004020798448118838224183109321278220897879821783775691052079258674639100843217776755569303531857257818243870722744211582871276561100739722763893693489492433885084914727914116743168) := by
  show momentBQ (350 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_352, endpointB_at_351]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_353 : momentBQ 353 =
    (-449853541152999289239046027506344040349882127680658746466719129212704646344186582395040819869175065603491540190471898951340366927227692707497810872867951617349348195671711919319391273792325451345300716939775 / 10520271803096747014481979765760257331100679605646347718996561806137464308594161644227333072555176902453965937712356435426038864500367607726255629541303761699910447342256889196383327515768645434542586503471562752) := by
  show momentBQ (351 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_353, endpointB_at_352]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_354 : momentBQ 354 =
    (-895883964392516998116287131266175241829935228780462036164599285655896222039555715081341916056742411102704115450146586296861977195017189726263345732652039623219806746621001357738051176985849269959621541101025 / 21040543606193494028963959531520514662201359211292695437993123612274928617188323288454666145110353804907931875424712870852077729000735215452511259082607523399820894684513778392766655031537290869085173006943125504) := by
  show momentBQ (352 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_354, endpointB_at_353]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_355 : momentBQ 355 =
    (-3568351383597313467073347048263579353051436928193365737265776815748061223377891407527378818192109603544668934420075386097670587132695586197828580460563208668756857380609073204549864857486009804076458680656625 / 84162174424773976115855838126082058648805436845170781751972494449099714468753293153818664580441415219631727501698851483408310916002940861810045036330430093599283578738055113571066620126149163476340692027772502016) := by
  show momentBQ (353 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_355, endpointB_at_354]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_356 : momentBQ 356 =
    (-7106547685079720059777060177809438317203847628824534017596913264039096577262448521470019223836116872411495596154910698510008746768495153357365651790473770503693234276311590860892266068289039243611426161195025 / 168324348849547952231711676252164117297610873690341563503944988898199428937506586307637329160882830439263455003397702966816621832005881723620090072660860187198567157476110227142133240252298326952681384055545004032) := by
  show momentBQ (354 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_356, endpointB_at_355]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_357 : momentBQ 357 =
    (-56612834929455298004291411978279682774129527739737018185125971957345162621113213502497119434829290590334273906447547025208946083807450154273845473252201160529421383167470987869355243173223919367646080317834525 / 1346594790796383617853693410017312938380886989522732508031559911185595431500052690461098633287062643514107640027181623734532974656047053788960720581286881497588537259808881817137065922018386615621451072444360032256) := by
  show momentBQ (355 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_357, endpointB_at_356]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_358 : momentBQ 358 =
    (-112749931750259711151403904528170460650997462809392212688023994570510954127763290757074095008861696385791789208639232310710253965229963752629423337485476260886326620257904404412077249008857721765816143154006575 / 2693189581592767235707386820034625876761773979045465016063119822371190863000105380922197266574125287028215280054363247469065949312094107577921441162573762995177074519617763634274131844036773231242902144888720064512) := by
  show momentBQ (356 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_358, endpointB_at_357]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_359 : momentBQ 359 =
    (-449110063340419966765089295690422002481347435659757808081346972786448660855280593909462735985018935883070087741674707472270452945301475729747367819146059072692463018122267264501737868957070143123055363512886525 / 10772758326371068942829547280138503507047095916181860064252479289484763452000421523688789066296501148112861120217452989876263797248376430311685764650295051980708298078471054537096527376147092924971608579554880258048) := by
  show momentBQ (357 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_359, endpointB_at_358]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_360 : momentBQ 360 =
    (-894467117794986841885902079160589782100733750687261372641122800953511956856617338844751688660970861159874965836483052486555358930057256676237793845931566119707830245006743994759728624803078418754831712845999625 / 21545516652742137885659094560277007014094191832363720128504958578969526904000843047377578132593002296225722240434905979752527594496752860623371529300590103961416596156942109074193054752294185849943217159109760516096) := by
  show momentBQ (358 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_360, endpointB_at_359]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_361 : momentBQ 361 =
    (-14251842743533457014048706461292063861471691094283697870748556628525957179248769598926376905998135721147341122327963302952448718952245623041388848611842953507344761903774120983171676088529049472160318624679594025 / 344728266443874206170545512964432112225507069317819522056079337263512430464013488758041250121488036739611555846958495676040441511948045769973944468809441663382665538511073745187088876036706973599091474545756168257536) := by
  show momentBQ (359 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_361, endpointB_at_360]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_362 : momentBQ 362 =
    (-28385249120777162307759058021243750460936692234875287448942416110554468730969156070991869793386868652368250046963450456572882628605719121791575019811399123467537074262641531819668795312056472494413487787104232975 / 689456532887748412341091025928864224451014138635639044112158674527024860928026977516082500242976073479223111693916991352080883023896091539947888937618883326765331077022147490374177752073413947198182949091512336515072) := by
  show momentBQ (360 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_362, endpointB_at_361]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_363 : momentBQ 363 =
    (-113070522740775326098863430018324552941079309952182774865676696219391005276401997387763194038850454687058056816909656238613526934943223684042682813723860596796100721234058256585531499557970810323050412676807469475 / 2757826131550993649364364103715456897804056554542556176448634698108099443712107910064330000971904293916892446775667965408323532095584366159791555750475533307061324308088589961496711008293655788792731796366049346060288) := by
  show momentBQ (361 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_363, endpointB_at_362]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_364 : momentBQ 364 =
    (-225206578351461599915918071358811712882645567756000402831637056106390349352172573309511816226140161814718939610539067384345950341498486841770963290144218213453390692705851568901761085896454258577315284752980166475 / 5515652263101987298728728207430913795608113109085112352897269396216198887424215820128660001943808587833784893551335930816647064191168732319583111500951066614122648616177179922993422016587311577585463592732098692120576) := by
  show momentBQ (362 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_364, endpointB_at_363]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_365 : momentBQ 365 =
    (-1794228234118787471857589030056466943295802600253849363219086436012450585498078193949407327076391399073310233160888174215943010962487944618504927311588551700590200573755410851140404255768454257896193202702314513125 / 44125218104815898389829825659447310364864904872680898823178155169729591099393726561029280015550468702670279148410687446533176513529349858556664892007608532912981188929417439383947376132698492620683708741856789536964608) := by
  show momentBQ (363 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_365, endpointB_at_364]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_366 : momentBQ 366 =
    (-3573709386861256142576622533838497171989173946259036950850070791728908426457816019181422265163113827743278190432782746999974161560900645856583786727465416674874180320877215585696092860119633549289130022916664797375 / 88250436209631796779659651318894620729729809745361797646356310339459182198787453122058560031100937405340558296821374893066353027058699717113329784015217065825962377858834878767894752265396985241367417483713579073929216) := by
  show momentBQ (364 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_366, endpointB_at_365]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_367 : momentBQ 367 =
    (-14236252147660413813870807798733685455629004408867966869779790203116799141463103158378452630076010821993714758609282090508093791136046835133604265160231086098269275704478088316789353524738868073397681894569664684625 / 353001744838527187118638605275578482918919238981447190585425241357836728795149812488234240124403749621362233187285499572265412108234798868453319136060868263303849511435339515071579009061587940965469669934854316295716864) := by
  show momentBQ (365 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_367, endpointB_at_366]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_368 : momentBQ 368 =
    (-28356131661961205716456568122273362583282839844366440822367919995853896927546398933990868862630964334815818769872984218423478368720572851451402500904983443972302017820091233132351546121482595535841159304987533745125 / 706003489677054374237277210551156965837838477962894381170850482715673457590299624976468480248807499242724466374570999144530824216469597736906638272121736526607699022870679030143158018123175881930939339869708632591433728) := by
  show momentBQ (366 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_368, endpointB_at_367]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_369 : momentBQ 369 =
    (-903697587313807121311420192766364120588970504605243527078073276389604628169196105157187255491673776409565006883343366613235201924877386961472957963624037583986842567918559734174507969871597501207459555241559227616375 / 22592111669665739975592870737637022906810831294812620197467215446901550642889587999246991367961839975767182923986271972624986374927027127581012424707895568851446368731861728964581056579941628221790058875830676242925879296) := by
  show momentBQ (367 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_369, endpointB_at_368]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_370 : momentBQ 370 =
    (-1800048039771404428628438595347635849953640436002314342553885794434578324402057282630169736548455896100353062491212396912541662370690730126511176431608855350217694545854041746932963029419035673136809683204731794845625 / 45184223339331479951185741475274045813621662589625240394934430893803101285779175998493982735923679951534365847972543945249972749854054255162024849415791137702892737463723457929162113159883256443580117751661352485851758592) := by
  show momentBQ (368 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_370, endpointB_at_369]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_371 : momentBQ 371 =
    (-7171002190873108453508968890655176331977475682884895516011966651342076892347655228640189707222767542843028146248775873105638946849724692449939119081598521043840220974564479824268074338820698870820695873091282880006625 / 180736893357325919804742965901096183254486650358500961579737723575212405143116703993975930943694719806137463391890175780999890999416217020648099397663164550811570949854893831716648452639533025774320471006645409943407034368) := by
  show momentBQ (369 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_371, endpointB_at_370]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_372 : momentBQ 372 =
    (-14284017841119210639199805957396698946984783098792285138363459178818853971549642086159299713308962841404306738754300189285895368522766974987884121297308105259832677359038141752383037564389478343764135445321989348584625 / 361473786714651839609485931802192366508973300717001923159475447150424810286233407987951861887389439612274926783780351561999781998832434041296198795326329101623141899709787663433296905279066051548640942013290819886814068736) := by
  show momentBQ (370 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_372, endpointB_at_371]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_373 : momentBQ 373 =
    (-113811367959885323480075873273451117416298110496828852554057239263492159063637470815527323522171413607318185950719746669471488904036240091032496063239841999973505526054271645575439041238845198416443272741759076422593625 / 2891790293717214716875887454417538932071786405736015385275803577203398482289867263903614895099115516898199414270242812495998255990659472330369590362610632812985135197678301307466375242232528412389127536106326559094512549888) := by
  show momentBQ (371 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_373, endpointB_at_372]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_374 : momentBQ 374 =
    (-226707362987117413795432637646579571689837791150519671441459862661594300762151852053449869643360215308947485687358637467606745993830901843531218699697594117909690632327945932071182862306868585585569307364951725957069875 / 5783580587434429433751774908835077864143572811472030770551607154406796964579734527807229790198231033796398828540485624991996511981318944660739180725221265625970270395356602614932750484465056824778255072212653118189025099776) := by
  show momentBQ (372 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_374, endpointB_at_373]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_375 : momentBQ 375 =
    (-903192435429959750147579224848672625181439328380412594780147581191913123357235988127380496707504601097143726401509010231909228692000116970217956851736404373490478722376041280176637606516668963963899112229353132823620625 / 23134322349737717735007099635340311456574291245888123082206428617627187858318938111228919160792924135185595314161942499967986047925275778642956722900885062503881081581426410459731001937860227299113020288850612472756100399104) := by
  show momentBQ (373 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_375, endpointB_at_374]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_376 : momentBQ 376 =
    (-1799159331376479822293977815898555869361427142133781888802053981734290941727614088349741949441349165385510302991805948381963183554464233004674170048658917511993033614973074230111862112181204576216087031560871440584652285 / 46268644699475435470014199270680622913148582491776246164412857235254375716637876222457838321585848270371190628323884999935972095850551557285913445801770125007762163162852820919462003875720454598226040577701224945512200798208) := by
  show momentBQ (374 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_376, endpointB_at_375]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_377 : momentBQ 377 =
    (-28671709344701774189323178385276986088334232541663885844951881538701785433063467067530994045352564359015898232784311815704051584729653415329807518435011259925165578247124097837314568553696217608209557162533887425487331095 / 740298315191606967520227188330889966610377319868419938630605715764070011466206019559325413145373572325939050053182159998975553533608824916574615132828322000124194610605645134711392062011527273571616649243219599128195212771328) := by
  show momentBQ (375 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_377, endpointB_at_376]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_378 : momentBQ 378 =
    (-57115261851116796859898426969079619502225487105542647929864358184522654801672848190227523947108158709869866240904557489638574907511856007725956091099982642450396151892812194896082867331103075394603123154013128531938953985 / 1480596630383213935040454376661779933220754639736839877261211431528140022932412039118650826290747144651878100106364319997951107067217649833149230265656644000248389221211290269422784124023054547143233298486439198256390425542656) := by
  show momentBQ (376 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_378, endpointB_at_377]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_379 : momentBQ 379 =
    (-227554455946512952568801669352999753889819004182400073498348474671669624686029918980112833503557902161545022642334030633321941298182156475225634585176121321508721176588823189189155550795347173397545776375512623198677419845 / 5922386521532855740161817506647119732883018558947359509044845726112560091729648156474603305162988578607512400425457279991804428268870599332596921062626576000993556884845161077691136496092218188572933193945756793025561702170624) := by
  show momentBQ (377 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_379, endpointB_at_378]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_380 : momentBQ 380 =
    (-453307689286589127148932085386582623184204084848844473591696829491056904057922397968298652493895029371943250910190483187752152190310100630066897392633170442583336380803592368965204329420810332229939475365467098984172696525 / 11844773043065711480323635013294239465766037117894719018089691452225120183459296312949206610325977157215024800850914559983608856537741198665193842125253152001987113769690322155382272992184436377145866387891513586051123404341248) := by
  show momentBQ (378 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_380, endpointB_at_379]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_381 : momentBQ 381 =
    (-3612146534631031255281490406712032060530973602427108068514889472891895540756286897494758736188195128784853062515938902875035570611207854494322540276034842368795638318613888666385891340753193910505938766859564146642302434415 / 94758184344525691842589080106353915726128296943157752144717531617800961467674370503593652882607817257720198406807316479868870852301929589321550737002025216015896910157522577243058183937475491017166931103132108688408987234729984) := by
  show momentBQ (379 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_381, endpointB_at_380]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_382 : momentBQ 382 =
    (-7195850970564180374694622621245229222947530089874475128616275879068106864656225079261212285477270610886360825327027893129007869012878639268217344014463111175632255863065463248784492198508331176047263842641493929925216660685 / 189516368689051383685178160212707831452256593886315504289435063235601922935348741007187305765215634515440396813614632959737741704603859178643101474004050432031793820315045154486116367874950982034333862206264217376817974469459968) := by
  show momentBQ (380 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_382, endpointB_at_381]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_383 : momentBQ 383 =
    (-28670380045022729136872292223914237898759530881646468967942334785187588083787367985956976697634570339709531874732294380477355959784296567974415700497415851333278255035564489698036641691438953010324438660995690474728219260635 / 758065474756205534740712640850831325809026375545262017157740252942407691741394964028749223060862538061761587254458531838950966818415436714572405896016201728127175281260180617944465471499803928137335448825056869507271897877839872) := by
  show momentBQ (381 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_383, endpointB_at_382]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_384 : momentBQ 384 =
    (-57116187922590972144735140905604604482385175098423644445274155198689633702166479825809851750117956055348231907103761389828257434243911961787151904646287975371517777002965288876245320132031125709863046209764260658531674401735 / 1516130949512411069481425281701662651618052751090524034315480505884815383482789928057498446121725076123523174508917063677901933636830873429144811792032403456254350562520361235888930942999607856274670897650113739014543795755679744) := by
  show momentBQ (382 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_384, endpointB_at_383]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_385 : momentBQ 385 =
    (-14564627920260697896907460930929174143008219650098029333544909575665856594052452355581512196280078794113799136311459154406205645732197550255723735684803433719737033135756148663442556633667937056015076783489886467925576972442425 / 388129523075177233787244872115625638814221504279174152784763009506512738171594221582719602207161619487621932674282768301542895011028703597861071818760295284801113744005212476387566321407899611206315749798429117187723211713454014464) := by
  show momentBQ (383 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_385, endpointB_at_384]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_386 : momentBQ 386 =
    (-29015765233350533212800058529929030045941050575649840256698560115677174045813586900600051570251481649572166071560751094622233065653494859860104169533101905618281310169155755908728418020839760316788477643991540054282902695748935 / 776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928) := by
  show momentBQ (384 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_386, endpointB_at_385]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_387 : momentBQ 387 =
    (-115612038675888912127685207303188725934345429495723974908814470098216304876842737443323521541571965743632102119327552288935218795272215270634301069279561478862478380933061017066384214808423708205234918695489607781054674471662855 / 3105036184601417870297958976925005110513772034233393222278104076052101905372753772661756817657292955900975461394262146412343160088229628782888574550082362278408909952041699811100530571263196889650525998387432937501785693707632115712) := by
  show momentBQ (385 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_387, endpointB_at_386]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_388 : momentBQ 388 =
    (-230327859997701166021822467262941880349819964189155515903607122598772018243012275371582519660341048031887211198970394870204273103759374608938103680657731008276410417827881251054734443455541806269343985308068443408767839838894215 / 6210072369202835740595917953850010221027544068466786444556208152104203810745507545323513635314585911801950922788524292824686320176459257565777149100164724556817819904083399622201061142526393779301051996774865875003571387415264231424) := by
  show momentBQ (386 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_388, endpointB_at_387]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_389 : momentBQ 389 =
    (-1835499337919824756029574919528392510416606518744507358695755729575781135070602977961167914406635362151018703678392940563586629991814397656795403558231196591728507762690228938817626028774575425218586604568421719123479795829538435 / 49680578953622685924767343630800081768220352547734291556449665216833630485964060362588109082516687294415607382308194342597490561411674060526217192801317796454542559232667196977608489140211150234408415974198927000028571099322113851392) := by
  show momentBQ (387 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_389, endpointB_at_388]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_390 : momentBQ 390 =
    (-3656843153953378369981800932222375824094781624748054506398999204167687351361741151465051757493939346187762198845127323744934802682920715126006266729123849250872991043920121921808895044473768520679703389564336329873256662642396625 / 99361157907245371849534687261600163536440705095468583112899330433667260971928120725176218165033374588831214764616388685194981122823348121052434385602635592909085118465334393955216978280422300468816831948397854000057142198644227702784) := by
  show momentBQ (388 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_390, endpointB_at_389]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_391 : momentBQ 391 =
    (-14571113490368076889619791406855312899085360627842247956266781444298938830810630126606898541398927548655852453859815028460586367613484080271317278197585799322709302775004793503823135638749323797785279659956355529802668855759703475 / 397444631628981487398138749046400654145762820381874332451597321734669043887712482900704872660133498355324859058465554740779924491293392484209737542410542371636340473861337575820867913121689201875267327793591416000228568794576910811136) := by
  show momentBQ (389 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_391, endpointB_at_390]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_392 : momentBQ 392 =
    (-29030428156001871859370377253044216747794107235522023421820518529690213169313250303393283794756431100774703482242444775372881791229933755834670485206954827806625439544063258668742257449068345878452002186971869457074882451756544775 / 794889263257962974796277498092801308291525640763748664903194643469338087775424965801409745320266996710649718116931109481559848982586784968419475084821084743272680947722675151641735826243378403750534655587182832000457137589153821622272) := by
  show momentBQ (390 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_392, endpointB_at_391]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_393 : momentBQ 393 =
    (-462709477343621671880984992543419046531167301039646944743710713707919520106809152794901115177648422238878437135333660603392258754093433945038319366257790214632132005794151122863014348320864859817775789959694490734193534588201254475 / 12718228212127407596740439969484820932664410252219978638451114295509409404406799452822555925124271947370395489870897751704957583721388559494711601357137355892362895163562802426267773219894054460008554489394925312007314201426461145956352) := by
  show momentBQ (391 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_393, endpointB_at_392]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_394 : momentBQ 394 =
    (-921886821272406537106389946975819627058279889857617195252736612807381639296772434194421305811956016827078412918489201660193736907010582134771002706818956076480812622231094985246158358104929224522438787629620321233774904790233033725 / 25436456424254815193480879938969641865328820504439957276902228591018818808813598905645111850248543894740790979741795503409915167442777118989423202714274711784725790327125604852535546439788108920017108978789850624014628402852922291912704) := by
  show momentBQ (392 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_394, endpointB_at_393]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_395 : momentBQ 395 =
    (-3673508399486493053951858418152377701729693977351418772961412391136013131207951070267110279504494787864246467720883367021584180060930492262919985405344571167702730499753348037656011731534870260152865219742395696286869544468695083625 / 101745825697019260773923519755878567461315282017759829107608914364075275235254395622580447400994175578963163918967182013639660669771108475957692810857098847138903161308502419410142185759152435680068435915159402496058513611411689167650816) := by
  show momentBQ (393 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_395, endpointB_at_394]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_396 : momentBQ 396 =
    (-7319116735179417806228133101483344939901947240950801453976282409681119833571284790633457696126676957086486000243886607205029746096081765597260831681028297491093794691913632672494382867640361758836215007436114969563965396194589951425 / 203491651394038521547847039511757134922630564035519658215217828728150550470508791245160894801988351157926327837934364027279321339542216951915385621714197694277806322617004838820284371518304871360136871830318804992117027222823378335301632) := by
  show momentBQ (394 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_396, endpointB_at_395]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_397 : momentBQ 397 =
    (-58331142465217784334484818354246052096794306799092750981689765871094985340280239392018162850948970900416539941337641748330994643129378919759987840366983098186596000120402587662606748308770155835573471119869643545312815127247792643175 / 1627933211152308172382776316094057079381044512284157265721742629825204403764070329961287158415906809263410622703474912218234570716337735615323084973713581554222450580936038710562274972146438970881094974642550439936936217782587026682413056) := by
  show momentBQ (395 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_397, endpointB_at_396]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_398 : momentBQ 398 =
    (-116221495440773973321353882413623746117290419844036186464777342075657766761112517277295634294963818595036481344075754717707347009358535832569648316700966324094703869257527573907108155950219630392792482760244050489527548528093209019525 / 3255866422304616344765552632188114158762089024568314531443485259650408807528140659922574316831813618526821245406949824436469141432675471230646169947427163108444901161872077421124549944292877941762189949285100879873872435565174053364826112) := by
  show momentBQ (396 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_398, endpointB_at_397]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_399 : momentBQ 399 =
    (-463133898917255079617254415849264475733725140383521084756625287768827181113378021110027326612594513295798641737950118045939327529755371433305181483135006507573367680006127467881089284766453100007459491602379557980881135591848817851675 / 13023465689218465379062210528752456635048356098273258125773941038601635230112562639690297267327254474107284981627799297745876565730701884922584679789708652433779604647488309684498199777171511767048759797140403519495489742260696213459304448) := by
  show momentBQ (397 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_399, endpointB_at_398]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_400 : momentBQ 400 =
    (-922785588068215008259943009022970571950655354899496898199290986907813556353723124768099560543891323484110075643284069790781366882595288946059196188201328755691296505275366759311944815512105800766742596049854006503259405502555915268375 / 26046931378436930758124421057504913270096712196546516251547882077203270460225125279380594534654508948214569963255598595491753131461403769845169359579417304867559209294976619368996399554343023534097519594280807038990979484521392426918608896) := by
  show momentBQ (398 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_400, endpointB_at_399]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_401 : momentBQ 401 =
    (-29418404547614694463326983127652301833786892714195961114593396662621096176556693217607013990139255392673429211507896144930109976217137811600367174479858360731438532588178692286864800718525932928443753962069345727323909847421482578755795 / 833501804109981784259981473840157224643094790289488520049532226470504654727204008940179025108944286342866238824179155055736100206764920635045419506541353755761894697439251819807884785738976753091120627016985825247711343504684557661395484672) := by
  show momentBQ (399 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_401, endpointB_at_400]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_402 : momentBQ 402 =
    (-58616721280658705426928327977541618865824756305841827757007790357691411084959595712887790967883454011835585885273837954611366261839134941318437337679318778614512188373952057698765525621202544662909125724921215052697765506458265786598205 / 1667003608219963568519962947680314449286189580578977040099064452941009309454408017880358050217888572685732477648358310111472200413529841270090839013082707511523789394878503639615769571477953506182241254033971650495422687009369115322790969344) := by
  show momentBQ (400 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_402, endpointB_at_401]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_403 : momentBQ 403 =
    (-233592008685610064910296471194083764733958357218802507628672836201546369547525553064791644603356451062091066139822607968376638685239537751224220435229524087911563496952913423963737243893448946641742336844089021180153781943647118880921205 / 6668014432879854274079851790721257797144758322315908160396257811764037237817632071521432200871554290742929910593433240445888801654119365080363356052330830046095157579514014558463078285911814024728965016135886601981690748037476461291163877376) := by
  show momentBQ (401 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_403, endpointB_at_402]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_404 : momentBQ 404 =
    (-465445119043535687650044829699377824023247049247390604530581358485959639569883422111731242224553921098906020124758199003986205618479773732588210941660813505193512377303199700850821356939055841571511405671968942947055798761162869631215205 / 13336028865759708548159703581442515594289516644631816320792515623528074475635264143042864401743108581485859821186866480891777603308238730160726712104661660092190315159028029116926156571823628049457930032271773203963381496074952922582327754752) := by
  show momentBQ (402 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_404, endpointB_at_403]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_405 : momentBQ 405 =
    (-3709735849802437906517684038693060874640731432120291451951663302784133760928278760395481683076890163214052932677528219784246490325507107472609008000365889818621559046822532269157536557781583687772937441246881178934454633690456535179487525 / 106688230926077668385277628651540124754316133157054530566340124988224595805082113144342915213944868651886878569494931847134220826465909841285813696837293280737522521272224232935409252574589024395663440258174185631707051968599623380658622038016) := by
  show momentBQ (403 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_405, endpointB_at_404]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_406 : momentBQ 406 =
    (-7391992174791524421135237084506913890950790779558210374629610581103199864368199900343589427760618177070964732520408082384905969611566014149124615941469810083031106545150082817802795066987007496377186457003044719506431825649872651579867735 / 213376461852155336770555257303080249508632266314109061132680249976449191610164226288685830427889737303773757138989863694268441652931819682571627393674586561475045042544448465870818505149178048791326880516348371263414103937199246761317244076032) := by
  show momentBQ (404 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_406, endpointB_at_405]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_407 : momentBQ 407 =
    (-29458727435499227865509393110177799693493545520505380261454950542426052661447653790039230773686404459361627924182315953937876499585009386436659183727335351513163375344957719209864340931982704751572137161159917133402479541629295443980852205 / 853505847408621347082221029212320998034529065256436244530720999905796766440656905154743321711558949215095028555959454777073766611727278730286509574698346245900180170177793863483274020596712195165307522065393485053656415748796987045268976304128) := by
  show momentBQ (405 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_407, endpointB_at_406]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_408 : momentBQ 408 =
    (-58700314373930893854860240325194583664430627560515634869877063611566409603032057060741563040441459500103882669562305254652623688362266860933981813274862334341954539078036143192137544215818116839127772082802685000465383066981225073878307465 / 1707011694817242694164442058424641996069058130512872489061441999811593532881313810309486643423117898430190057111918909554147533223454557460573019149396692491800360340355587726966548041193424390330615044130786970107312831497593974090537952608256) := by
  show momentBQ (406 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_408, endpointB_at_407]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_409 : momentBQ 409 =
    (-935752070313839543215713242831043069003570592288219826455099072866735117789511027262409622585860913207538364908904983765344765855657312900771121846911040741568804711185164400298192616616865274317860366731736919713301106538347764413001254295 / 27312187117075883106631072934794271937104930088205959824983071996985496526101020964951786294769886374883040913790702552866360531575272919369168306390347079868805765445689403631464768659094790245289840706092591521717005303961503585448607241732096) := by
  show momentBQ (407 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_409, endpointB_at_408]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_410 : momentBQ 410 =
    (-1864640433510462659464074065788019807427652891723469825332287883585303474323842267038786900751776636342649798045862009214562308489879486587111159670495105634177447040625694342892486509884462588188401464269842517277115896891817672363315457825 / 54624374234151766213262145869588543874209860176411919649966143993970993052202041929903572589539772749766081827581405105732721063150545838738336612780694159737611530891378807262929537318189580490579681412185183043434010607923007170897214483464192) := by
  show momentBQ (408 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_410, endpointB_at_409]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_411 : momentBQ 411 =
    (-7431274313063648745278773228042986256918987378234511450226727809215575309866239669125311697142446399472901878065703714772182468469422148983755207077046347820112069425322889161673958432076126509999629250285177251782457013466414821077213312405 / 218497496936607064853048583478354175496839440705647678599864575975883972208808167719614290358159090999064327310325620422930884252602183354953346451122776638950446123565515229051718149272758321962318725648740732173736042431692028683588857933856768) := by
  show momentBQ (409 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_411, endpointB_at_410]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_412 : momentBQ 412 =
    (-14808305747929752609205146651501717139699879958087749094247421108874832551777251311468686812553926036905855567240416891480334407971914209288796872496596006970004342723453640446255406218662646257152545878305499195157742807856432453679410469245 / 436994993873214129706097166956708350993678881411295357199729151951767944417616335439228580716318181998128654620651240845861768505204366709906692902245553277900892247131030458103436298545516643924637451297481464347472084863384057367177715867713536) := by
  show momentBQ (410 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_412, endpointB_at_411]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_413 : momentBQ 413 =
    (-118035136107284727108324518455173881278578654811553805887156628450351820631156537152580503622395857051453470103926041435974316009174189959476720702133061375945374421125780959285200859276912937641963496758143833390529192672331369363794135876215 / 3495959950985713037648777335653666807949431051290362857597833215614143555340930683513828645730545455985029236965209926766894148041634933679253543217964426223207137977048243664827490388364133151397099610379851714779776678907072458937421726941708288) := by
  show momentBQ (411 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_413, endpointB_at_412]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_414 : momentBQ 414 =
    (-235212874131465691065741110626169744049080467094210126501525194224308833848527433599452190027195618288973864153828407026166736260412489919247799365267577511871775178175587722740242874539707863630353408794073546925921369417260815947705989893765 / 6991919901971426075297554671307333615898862102580725715195666431228287110681861367027657291461090911970058473930419853533788296083269867358507086435928852446414275954096487329654980776728266302794199220759703429559553357814144917874843453883416576) := by
  show momentBQ (412 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_414, endpointB_at_413]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_415 : momentBQ 415 =
    (-937442614292073406421431962640531588601407658708808475187238092922969989976015133910860177644620217818374096265258143944867427124832387359320939499254837909633886579685313387732852036208980615918075179976380078327947486807923541820567351025875 / 27967679607885704301190218685229334463595448410322902860782665724913148442727445468110629165844363647880233895721679414135153184333079469434028345743715409785657103816385949318619923106913065211176796883038813718238213431256579671499373815533666304) := by
  show momentBQ (413 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_415, endpointB_at_414]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_416 : momentBQ 416 =
    (-1868108534986854715928974055671613551261118394583577371035773259873002847494372327094653896173737156953723801473177072391338222246352733364237149315382532412692106509396998003988117190228498721359634153832448975366777280940127154423154697104575 / 55935359215771408602380437370458668927190896820645805721565331449826296885454890936221258331688727295760467791443358828270306368666158938868056691487430819571314207632771898637239846213826130422353593766077627436476426862513159342998747631067332608) := by
  show momentBQ (414 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_416, endpointB_at_415]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_417 : momentBQ 417 =
    (-119127844269546350731163037857828279538112857623829664660665848648824566197910358397036006148309854085741310109327984077878414326325108919919430521727086105393981253560777795792780703899955803077472054886700015429158335838412723924368864915360975 / 3579862989809370150552347991709354811340217396521331566180181212788883000669113019918160533228078546928669938652374965009299607594634172087555628255195572452564109288497401512783350157684872347030630001028968155934491319200842197951919848388309286912) := by
  show momentBQ (415 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_417, endpointB_at_416]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_418 : momentBQ 418 =
    (-237398653688232655773612672565600240518397565192811633892118273926074854941159491194093335993394457422664337412114040212750509125122699070630807586463329864705991418966442082263311186908545017643595389954071253768898266383023917460792630083129425 / 7159725979618740301104695983418709622680434793042663132360362425577766001338226039836321066456157093857339877304749930018599215189268344175111256510391144905128218576994803025566700315369744694061260002057936311868982638401684395903839696776618573824) := by
  show momentBQ (416 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_418, endpointB_at_417]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_419 : momentBQ 419 =
    (-946186978575587570619231369603564594984809434476612875751839819045073464909023235237702147763146330301815277819574141135029541154197169023136185260880161613876032784684431839834154156434535883718253396324121312868383999507458962893972539996396225 / 28638903918474961204418783933674838490721739172170652529441449702311064005352904159345284265824628375429359509218999720074396860757073376700445026041564579620512874307979212102266801261478978776245040008231745247475930553606737583615358787106474295296) := by
  show momentBQ (417 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_419, endpointB_at_418]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_420 : momentBQ 420 =
    (-1885599348712686447415413349925958083084286104505899167667747610746148790451156089316184471079301159432018513077194290806085123779844000320569724803901992715003549821507161303726774989553311367314419059500337222542006299734434926053620694264894625 / 57277807836949922408837567867349676981443478344341305058882899404622128010705808318690568531649256750858719018437999440148793721514146753400890052083129159241025748615958424204533602522957957552490080016463490494951861107213475167230717574212948590592) := by
  show momentBQ (418 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_420, endpointB_at_419]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_421 : momentBQ 421 =
    (-15030920522595414823682866417981208719443309233061310507980045239947871786739215683406156212317857813758090432815348775282792843845042173983970092008247313356742582862871371535422006345296396328020654788588402431120564503597352696256004962854445725 / 458222462695599379270700542938797415851547826754730440471063195236977024085646466549524548253194054006869752147503995521190349772113174027207120416665033273928205988927667393636268820183663660419920640131707923959614888857707801337845740593703588724736) := by
  show momentBQ (419 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_421, endpointB_at_420]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_422 : momentBQ 422 =
    (-29954732347880173484726662528945924265113863293440473910202512960371174415853211302560012024072880536206740791287595302760720180489288322975180302125699515216881299339546510019522715733262889594321447429039595343729581041610876275911610840462897775 / 916444925391198758541401085877594831703095653509460880942126390473954048171292933099049096506388108013739504295007991042380699544226348054414240833330066547856411977855334787272537640367327320839841280263415847919229777715415602675691481187407177449472) := by
  show momentBQ (420 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_422, endpointB_at_421]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_423 : momentBQ 423 =
    (-119393032723067421330119067236225224203605493032148997907489636965270889496362799551909810958508495407345350736838235306264292283371997533754154663922811811836005558031083483063595279297033602601063209894892415564343969933624393118680875435209938525 / 3665779701564795034165604343510379326812382614037843523768505561895816192685171732396196386025552432054958017180031964169522798176905392217656963333320266191425647911421339149090150561469309283359365121053663391676919110861662410702765924749628709797888) := by
  show momentBQ (421 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_423, endpointB_at_422]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_424 : momentBQ 424 =
    (-237939306348808123360024524066519773058249244978963605758897787143554042187786855844586219002417639783432933028734355468512525756223626290673173479165319993800833771678967792488441655904017321495735900570672118961564932988286911108860468065914842025 / 7331559403129590068331208687020758653624765228075687047537011123791632385370343464792392772051104864109916034360063928339045596353810784435313926666640532382851295822842678298180301122938618566718730242107326783353838221723324821405531849499257419595776) := by
  show momentBQ (422 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_424, endpointB_at_423]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_425 : momentBQ 425 =
    (-3793560638957412532815485336532249211966426641645740506910728870496286144314714965824063302963073690886808083193972271148926118188848381426770407356503686693617066737145807257598739608281030880450883697777696990990988082549102639377115009730151726625 / 117304950450073441093299338992332138457996243649210992760592177980666118165925495436678284352817677825758656549761022853424729541660972550965022826666248518125620733165482852770884817967017897067499683873717228533661411547573197142488509591988118713532416) := by
  show momentBQ (423 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_425, endpointB_at_424]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_426 : momentBQ 426 =
    (-7560343202816302153634626070688976664789560859938687551419734948965539680551914296595250864964055096896768109330104738030918640249304891925822435366961465010573307120852938228673252819327136837039761157688727885574980955103741024829215089979855323415 / 234609900900146882186598677984664276915992487298421985521184355961332236331850990873356568705635355651517313099522045706849459083321945101930045653332497036251241466330965705541769635934035794134999367747434457067322823095146394284977019183976237427064832) := by
  show momentBQ (424 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_426, endpointB_at_425]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_427 : momentBQ 427 =
    (-30134889104183288865895763070492681635710503145952796859884295641651376473185799238541633729363768907349089787893234378348591199866947667817010552237325276028059801622554669277669444336191263730735949403181830867855205778793784648262927753018296570795 / 938439603600587528746394711938657107663969949193687942084737423845328945327403963493426274822541422606069252398088182827397836333287780407720182613329988145004965865323862822167078543736143176539997470989737828269291292380585577139908076735904949708259328) := by
  show momentBQ (425 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_427, endpointB_at_426]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_428 : momentBQ 428 =
    (-60058057676018685772546356845408131316134984021559321142298678199169370910260222838404989001612569883264813605379724721252110330413987038202051475302022974004400213538159305750109360960418654414183355836317887748348431189118292121011127676390094570835 / 1876879207201175057492789423877314215327939898387375884169474847690657890654807926986852549645082845212138504796176365654795672666575560815440365226659976290009931730647725644334157087472286353079994941979475656538582584761171154279816153471809899416518656) := by
  show momentBQ (426 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_428, endpointB_at_427]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_429 : momentBQ 429 =
    (-478780590632186345457776097094702205725823751125141130227857686952256760621046449356630426339958150564718560798027151282505141232178793865292989798435753241362181141570559699110684905600346843133629930171767834105992633685214048403948522504306081017965 / 15015033657609400459942315391018513722623519187099007073355798781525263125238463415894820397160662761697108038369410925238365381332604486523522921813279810320079453845181805154673256699778290824639959535835805252308660678089369234238529227774479195332149248) := by
  show momentBQ (427 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_429, endpointB_at_428]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_430 : momentBQ 430 =
    (-954213065245965793394868445258672228194823559934721832971604480988763473965022643822655045502713796580033495296767399409188568190006687074185329318560766949567983394039227372353462923748943009042549161531145683358097206995007019546330971424665965665175 / 30030067315218800919884630782037027445247038374198014146711597563050526250476926831789640794321325523394216076738821850476730762665208973047045843626559620640158907690363610309346513399556581649279919071671610504617321356178738468477058455548958390664298496) := by
  show momentBQ (428 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_430, endpointB_at_429]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_431 : momentBQ 431 =
    (-3803537660073454348555359337612474881688203678437472608635651349801722312502439096539606390678259179856226537066649587412440013669003399174775940586077103608277961714844734223753105700710903063950998285731124886687857239045214026749793686097389453837465 / 120120269260875203679538523128148109780988153496792056586846390252202105001907707327158563177285302093576864306955287401906923050660835892188183374506238482560635630761454441237386053598226326597119676286686442018469285424714953873908233822195833562657193984) := by
  show momentBQ (429 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_431, endpointB_at_430]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_432 : momentBQ 432 =
    (-7580600580053589989348152368930663395290410579530832878928131112481854910532703442987289767036252054516238040232603238021545178054927888378497756295684993038308048986198669833419762869862333484765446699403796467899928928862735148441004121479483853471885 / 240240538521750407359077046256296219561976306993584113173692780504404210003815414654317126354570604187153728613910574803813846101321671784376366749012476965121271261522908882474772107196452653194239352573372884036938570849429907747816467644391667125314387968) := by
  show momentBQ (430 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_432, endpointB_at_431]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_433 : momentBQ 433 =
    (-241736929608375591882546636653677821605371981813927670694708181031365817702542876459705795904378259960684479727417458812464829566862700440514317339651288111332712228782113138021274660405609967791964800303209954031919955842622776400285353651623540660714555 / 7687697232696013035490465480201479025983241823794691621558168976140934720122093268938148043346259333988919315645138393722043075242293497100043735968399262883880680368733084239192707430286484902215659282347932289182034267181757047930126964620533348010060414976) := by
  show momentBQ (431 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_433, endpointB_at_432]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_434 : momentBQ 434 =
    (-481799007510457588440271934023380970081838384077181477620168961270366514266269058625233491606185769852357288694598768949554614125179008037329921164247255519815544234270123875548175593371920097469897511920716374895027533238298974673086051273328211524703605 / 15375394465392026070980930960402958051966483647589383243116337952281869440244186537876296086692518667977838631290276787444086150484586994200087471936798525767761360737466168478385414860572969804431318564695864578364068534363514095860253929241066696020120829952) := by
  show momentBQ (432 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_434, endpointB_at_433]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_435 : momentBQ 435 =
    (-1920535214269796377884033285392739811616544710722405429223254154372659146729597860418557466540786594111931127745750853186012632342303419134978718004948737440739381394671231116816460314593137715721020035997325641862667355995984392130043476273865912298933725 / 61501577861568104283923723841611832207865934590357532972465351809127477760976746151505184346770074671911354525161107149776344601938347976800349887747194103071045442949864673913541659442291879217725274258783458313456274137454056383441015716964266784080483319808) := by
  show momentBQ (433 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_435, endpointB_at_434]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_436 : momentBQ 436 =
    (-3827825358096352780748176686058633141773664975163966683072554831818610299343819183868711088484740177229986868403599976350052763771901297448336893127104724968094353262482660639723841592533908964437067520022255934471109419881651650521259066504463783823392045 / 123003155723136208567847447683223664415731869180715065944930703618254955521953492303010368693540149343822709050322214299552689203876695953600699775494388206142090885899729347827083318884583758435450548517566916626912548274908112766882031433928533568160966639616) := by
  show momentBQ (434 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_436, endpointB_at_435]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_437 : momentBQ 437 =
    (-30517249873263583178625371928302313763314815260710890344862845402296994037887879548457889320121460679017051271951636508699044511172314013601878533279394550433706357661444331155229526090935476055924877751370095477572422806212433800944716777911734203142455845 / 984025245785089668542779581465789315325854953445720527559445628946039644175627938424082949548321194750581672402577714396421513631013567628805598203955105649136727087197834782616666551076670067483604388140535333015300386199264902135056251471428268545287733116928) := by
  show momentBQ (435 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_437, endpointB_at_436]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_438 : momentBQ 438 =
    (-60824999175314830545955832836501865647247606618030172746854778822427189489703302257910346905779844968933298988260584437246837000528799784547451264270829870544069193416746023881475783124038443122907479454103782977037941108034393227969904607691351237842286135 / 1968050491570179337085559162931578630651709906891441055118891257892079288351255876848165899096642389501163344805155428792843027262027135257611196407910211298273454174395669565233333102153340134967208776281070666030600772398529804270112502942856537090575466233856) := by
  show momentBQ (436 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_438, endpointB_at_437]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_439 : momentBQ 439 =
    (-242466777534474187518810237745507437032178815422558633826503296401730303308269328178793300679204587478898493227175754400531911878820284072648059149353582086689371716222919081500129491631440917106384609878687682826274532362164499032044414258057304249480894045 / 7872201966280717348342236651726314522606839627565764220475565031568317153405023507392663596386569558004653379220621715171372109048108541030444785631640845193093816697582678260933332408613360539868835105124282664122403089594119217080450011771426148362301864935424) := by
  show momentBQ (437 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_439, endpointB_at_438]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_440 : momentBQ 440 =
    (-483276606703109143687833617374302978139308572880953996806811809456751743495981007190077763312765407845184923858266025285798229826805805383979616755545294591920729502722219125996841241862211395143705088026997089915695252430282315838357317712528795485867385625 / 15744403932561434696684473303452629045213679255131528440951130063136634306810047014785327192773139116009306758441243430342744218096217082060889571263281690386187633395165356521866664817226721079737670210248565328244806179188238434160900023542852296724603729870848) := by
  show momentBQ (438 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_440, endpointB_at_439]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_441 : momentBQ 441 =
    (-7706065165065940345713274226132067487784974880301757367264981034428568709926824423739967244096277503276857785885441894102637228329248933122729525356604061038445086797952475881804177620239261700745988403630480870110267934206501654367988502434322793474649039875 / 251910462920982955146951572855242064723418868082104455055218081010186148908960752236565235084370225856148908135059894885483907489539473312974233140212507046179002134322645704349866637075627537275802723363977045251916898867011814946574400376685636747593659677933568) := by
  show momentBQ (439 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_441, endpointB_at_440]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_442 : momentBQ 442 =
    (-15359708118124629396557750668412896421231276462098060602779860157058303619105847320787825867484417064354553273907717516816821142180067601394284019928469318940574220624490309070534857433538120260670575525603611530219785746411598535577011096688820261823620195125 / 503820925841965910293903145710484129446837736164208910110436162020372297817921504473130470168740451712297816270119789770967814979078946625948466280425014092358004268645291408699733274151255074551605446727954090503833797734023629893148800753371273495187319355867136) := by
  show momentBQ (440 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_442, endpointB_at_441]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_443 : momentBQ 443 =
    (-61230329647365604065010761714351863109071287615875074167642790942843282753087110812733369182143762143422449929016738155274296046428233288816127699352857330256316236969122001317381038004285447735976366688039736462097878925740354343182564598112446383106829827625 / 2015283703367863641175612582841936517787350944656835640441744648081489191271686017892521880674961806849191265080479159083871259916315786503793865121700056369432017074581165634798933096605020298206421786911816362015335190936094519572595203013485093980749277423468544) := by
  show momentBQ (441 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_443, endpointB_at_442]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_444 : momentBQ 444 =
    (-122046006949489454603621902017545587190315907369791626388326375626479951853218778437118656857410704227182896811110112395275854196379525945879550244985492150375456517480213831068278682974681829234463051434625479223549496820380886873657346591723002610120385412625 / 4030567406735727282351225165683873035574701889313671280883489296162978382543372035785043761349923613698382530160958318167742519832631573007587730243400112738864034149162331269597866193210040596412843573823632724030670381872189039145190406026970187961498554846937088) := by
  show momentBQ (442 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_444, endpointB_at_443]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_445 : momentBQ 445 =
    (-973069514867551056974823272842593195166032234434825129312331913778691508018906476728378480349625885054566339439931977205577756430593517676607224926235680658398910071801704869328167877771111881734232437113905847863435177351685449398078844447521237026635505316875 / 32244539253885818258809801325470984284597615114509370247067914369303827060346976286280350090799388909587060241287666545341940158661052584060701841947200901910912273193298650156782929545680324771302748590589061792245363054977512313161523248215761503691988438775496704) := by
  show momentBQ (443 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_445, endpointB_at_444]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_446 : momentBQ 446 =
    (-1939579010533747837161052231486247559802855262794808740898962713531908691264651786197913959708130696726742344007235199508645999896486404896967659572069772458426591536377780267627157095692081436175874543191088734954757308563921333968754910168429971331743130822625 / 64489078507771636517619602650941968569195230229018740494135828738607654120693952572560700181598777819174120482575333090683880317322105168121403683894401803821824546386597300313565859091360649542605497181178123584490726109955024626323046496431523007383976877550993408) := by
  show momentBQ (444 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_446, endpointB_at_445]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_447 : momentBQ 447 =
    (-7732223050961891601955943649288224576971920756164058164390932073228102361140248600582715292289364077982394366916735840193660510798100511001812777397175012177314977021703348241796155417355427788163015555591380651904839674050789533175888408698359840869594813010375 / 257956314031086546070478410603767874276780920916074961976543314954430616482775810290242800726395111276696481930301332362735521269288420672485614735577607215287298185546389201254263436365442598170421988724712494337962904439820098505292185985726092029535907510203973632) := by
  show momentBQ (445 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_447, endpointB_at_446]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_448 : momentBQ 448 =
    (-15412551987487797354234330629789279861480942715306881039087965273481519471534589492436687528925779403763564610565574124412866924208294307164687214006449520917198309902321439112842001066809141295868561208125101030978103242906607324518381593177267602270266170899875 / 515912628062173092140956821207535748553561841832149923953086629908861232965551620580485601452790222553392963860602664725471042538576841344971229471155214430574596371092778402508526872730885196340843977449424988675925808879640197010584371971452184059071815020407947264) := by
  show momentBQ (446 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_448, endpointB_at_447]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_449 : momentBQ 449 =
    (-1966201274975229005333036750343118130900354549252720681129364712745570984011484059535137423332960143937266171033579670442955737616858116614009383158251346025579727248967577875395415278951509025315803594122245031523349456559371477256416394672471424118192527230512625 / 66036816391958155794042473114564575814855915754515190265995088628334237819590607434302156985957148486834299374157141084860293444937835692156317372307867447113548335499875635521091439709553305131628029113526398550518503536593945217354799612345879559561192322612217249792) := by
  show momentBQ (447 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_449, endpointB_at_448]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_450 : momentBQ 450 =
    (-3919265347667772738915518689436727677407165526906870845458310507588610313341376911545541189048996278004127445601456135960902862287501145589172378455757137400654467456182588415320482571629399950239742130822737869072155375547076775377489249959603395513991785904919375 / 132073632783916311588084946229129151629711831509030380531990177256668475639181214868604313971914296973668598748314282169720586889875671384312634744615734894227096670999751271042182879419106610263256058227052797101037007073187890434709599224691759119122384645224434499584) := by
  show momentBQ (448 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_450, endpointB_at_449]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_451 : momentBQ 451 =
    (-15624804519368853985809867841887754340596566567268725103893797890253259782520955954028224207008665161643121416464471795364132744319504567082167215443618454437275810258647919149077657185562541134955771961546648304700992763847679411171590476505618870115780586474278575 / 528294531135665246352339784916516606518847326036121522127960709026673902556724859474417255887657187894674394993257128678882347559502685537250538978462939576908386683999005084168731517676426441053024232908211188404148028292751561738838396898767036476489538580897737998336) := by
  show momentBQ (449 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_451, endpointB_at_450]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_452 : momentBQ 452 =
    (-31145674640604433998321665609439226501543932026551183743681872069484879256067271402819010115522815920880634486477960408054002964840874957443167021471869158623305883420231661452374309999602493304490552091863496288084684023722979580140265717025612781006844228914360175 / 1056589062271330492704679569833033213037694652072243044255921418053347805113449718948834511775314375789348789986514257357764695119005371074501077956925879153816773367998010168337463035352852882106048465816422376808296056585503123477676793797534072952979077161795475996672) := by
  show momentBQ (450 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_452, endpointB_at_451]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_453 : momentBQ 453 =
    (-248338520806943318871573634638095071485761794300200146487233333934565276192182402955220602779522629599234085595722498474837669657713525103153039702178354972739810627979015282907869498315414570507486614466982390757206197392693846032799817796814841731744837612848128475 / 8452712498170643941637436558664265704301557216577944354047371344426782440907597751590676094202515006314790319892114058862117560952042968596008623655407033230534186943984081346699704282822823056848387726531379014466368452684024987821414350380272583623832617294363807973376) := by
  show momentBQ (451 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_453, endpointB_at_452]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_454 : momentBQ 454 =
    (-495032415648277741591679894212361698789498676055365854918259824598040716118191412513386764481035175558738144134519682390239328258091199046682549340103873157580682112726381457981912046310859508097705105659349004092179241160270514277302948058551439478511232592498587225 / 16905424996341287883274873117328531408603114433155888708094742688853564881815195503181352188405030012629580639784228117724235121904085937192017247310814066461068373887968162693399408565645646113696775453062758028932736905368049975642828700760545167247665234588727615946752) := by
  show momentBQ (452 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_454, endpointB_at_453]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_455 : momentBQ 455 =
    (-1973587383972208617358900018776155671385446263568749333484692252252100652365476776760418598481660061148273217805023403361967365962874604128844524902176234394759988158666851187108503973177655748142833130492118276226529573788743680268542590277484813779967689410622120875 / 67621699985365151533099492469314125634412457732623554832378970755414259527260782012725408753620120050518322559136912470896940487616343748768068989243256265844273495551872650773597634262582584454787101812251032115730947621472199902571314803042180668990660938354910463787008) := by
  show momentBQ (453 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_455, endpointB_at_454]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_456 : momentBQ 456 =
    (-3934162103874270804273675422043897129552966507817265154880474445698143498231840519827911360050254231783480897910233465602866815227092892186509855134667790320983097274529305553203105722356337941902306921662310497884532578959100039568281603036656540875671855594361018975 / 135243399970730303066198984938628251268824915465247109664757941510828519054521564025450817507240240101036645118273824941793880975232687497536137978486512531688546991103745301547195268525165168909574203624502064231461895242944399805142629606084361337981321876709820927574016) := by
  show momentBQ (454 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_456, endpointB_at_455]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_457 : momentBQ 457 =
    (-62739532498626529141838086993647412118660465887822702206778092476133551577065667237255639057643528012126037477200038951456244474411007701711183479252860024592519919693809451716870580730208968231389420908614741097842809022347753262588911880005627993964661697110073092075 / 2163894399531684849059183759018052020301198647443953754636127064173256304872345024407213080115843841616586321892381199068702095603722999960578207655784200507016751857659924824755124296402642702553187257992033027703390323887110396882282073697349781407701150027357134841184256) := by
  show momentBQ (455 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_457, endpointB_at_456]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_458 : momentBQ 458 =
    (-125067208109953540586902619805717270109627318214018559541301624170148064522334404492647455539416310763778599872492856640649100035423256053082906235447167357557517826785690176179582273621926411507211734021330479518894527394658212740084242281586711384030211829468876557725 / 4327788799063369698118367518036104040602397294887907509272254128346512609744690048814426160231687683233172643784762398137404191207445999921156415311568401014033503715319849649510248592805285405106374515984066055406780647774220793764564147394699562815402300054714269682368512) := by
  show momentBQ (456 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_458, endpointB_at_457]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_459 : momentBQ 459 =
    (-498630397399072412907607388133711212271134242486458274503093374966572851130529743675926318373306077411920793378104707916649032018958221731286870711629972914628881117272205811580605309243750278192507917735697501313321849394423354723567306563705971587858442796092071166825 / 17311155196253478792473470072144416162409589179551630037089016513386050438978760195257704640926750732932690575139049592549616764829783999684625661246273604056134014861279398598040994371221141620425498063936264221627122591096883175058256589578798251261609200218857078729474048) := by
  show momentBQ (457 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_459, endpointB_at_458]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_460 : momentBQ 460 =
    (-994001772592922130306014727978966795703895058551436429564990061207873984279814194909526320940250677193698313596875398134496436377661814562369252072203540777528161704366161911974409276597018528422973300061357764055968392583654399939137441189087067544423693155608377162625 / 34622310392506957584946940144288832324819178359103260074178033026772100877957520390515409281853501465865381150278099185099233529659567999369251322492547208112268029722558797196081988742442283240850996127872528443254245182193766350116513179157596502523218400437714157458948096) := by
  show momentBQ (458 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_460, endpointB_at_459]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_461 : momentBQ 461 =
    (-7926083699719213856440134830927935231830189292971019181835616401109742987692083623756831620019216269448881335376823826863767236159268556119066123045309972982550645938293656289395941796864921657077100140489261475124547965210531171688600291916459486419448057597329407461975 / 276978483140055660679575521154310658598553426872826080593424264214176807023660163124123274254828011726923049202224793480793868237276543994954010579940377664898144237780470377568655909939538265926807969022980227546033961457550130800932105433260772020185747203501713259671584768) := by
  show momentBQ (459 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_461, endpointB_at_460]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_462 : momentBQ 462 =
    (-15800587679049799423142047526296686503366472798786044746435860027374954025355802278161666504984077552328681013473538171123214945835938835300264136830021399503175799603670000281897766835832674626581030431908093916788415574899084917097231384536282577048747863192940836133525 / 553956966280111321359151042308621317197106853745652161186848528428353614047320326248246548509656023453846098404449586961587736474553087989908021159880755329796288475560940755137311819879076531853615938045960455092067922915100261601864210866521544040371494407003426519343169536) := by
  show momentBQ (460 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_462, endpointB_at_461]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_463 : momentBQ 463 =
    (-62997148278808940557202708968481594240694898041913191391633883485767673841353653238904306714676776734609156768004885954997753095735496395288066103984630774642532084134112858266787200241566637796888004449295906914987578980441806098037013442242061703298254467535491385623275 / 2215827865120445285436604169234485268788427414982608644747394113713414456189281304992986194038624093815384393617798347846350945898212351959632084639523021319185153902243763020549247279516306127414463752183841820368271691660401046407456843466086176161485977628013706077372678144) := by
  show momentBQ (461 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_463, endpointB_at_462]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_464 : momentBQ 464 =
    (-125586107691880458173430022414489225667735185513360422579866251527783073338162898357470140599668822734436828718938465953483641700569898861448995710535235863920209748716600795205711848429732195867230298286609334951476318356258719283991713622439358427957427372646346757948775 / 4431655730240890570873208338468970537576854829965217289494788227426828912378562609985972388077248187630768787235596695692701891796424703919264169279046042638370307804487526041098494559032612254828927504367683640736543383320802092814913686932172352322971955256027412154745356288) := by
  show momentBQ (462 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_464, endpointB_at_463]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_465 : momentBQ 465 =
    (-4005763779827221510704233473565604611815691262064082444357802850455149753027609688988271726023919345839795398793726931274909261138867463684149001111899764625041173019408818467768395165431113144040966410865987407935020499294459149575597762095048501581400700679236922451814375 / 141812983367708498267942666831007057202459354558886953263833223277658525196114003519551116418471942004184601191539094262166460537485590525416453416929473364427849849743600833315151825889043592154525680139765876503569388266265666970077237981829515274335102568192877188951851401216) := by
  show momentBQ (463 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_465, endpointB_at_464]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_466 : momentBQ 466 =
    (-7985683922365235140694246086011431129361603870824525647139103747036395314100202541273393311879942437835463085337171753315786849625226105021948653829529208187985306212885967138970542620117509429088120135210258768076911834077341143347481990241096690249373009741188445403939625 / 283625966735416996535885333662014114404918709117773906527666446555317050392228007039102232836943884008369202383078188524332921074971181050832906833858946728855699699487201666630303651778087184309051360279531753007138776532531333940154475963659030548670205136385754377903702802432) := by
  show momentBQ (464 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_466, endpointB_at_465]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_467 : momentBQ 467 =
    (-31839915724795293758390363149805233987883819725304653760481662579385455994845871934948422260671530149137962258704860767512300357518605371525280254968380405178705362539789971983277399545447065491943620624937040324220820145312660610170861669244544314341920712659073243692102625 / 1134503866941667986143541334648056457619674836471095626110665786221268201568912028156408931347775536033476809532312754097331684299884724203331627335435786915422798797948806666521214607112348737236205441118127012028555106130125335760617903854636122194680820545543017511614811209728) := by
  show momentBQ (465 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_467, endpointB_at_466]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_468 : momentBQ 468 =
    (-63475292376412031025827469148755188100042475726463881479675434392736315912637059467745141594614977663484888357289561829879982083190196147516136868041888987626070005405876796394927749415013314717343706213739581460063348084124383357749619302069958793688068915386717751343356625 / 2269007733883335972287082669296112915239349672942191252221331572442536403137824056312817862695551072066953619064625508194663368599769448406663254670871573830845597595897613333042429214224697474472410882236254024057110212260250671521235807709272244389361641091086035023229622419456) := by
  show momentBQ (466 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_468, endpointB_at_467]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_469 : momentBQ 469 =
    (-506174767411901067923906228340073423054184870536673516414847694772846006380259628063301000921160462906251289208129582797248062253132076971218424768231473721838660812339171376380064873540234381463945964935205380361017980875966236519490553921634799611204857248340236427379074625 / 18152061871066687778296661354368903321914797383537530017770652579540291225102592450502542901564408576535628952517004065557306948798155587253306037366972590646764780767180906664339433713797579795779287057890032192456881698082005372169886461674177955114893128728688280185836979355648) := by
  show momentBQ (467 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_469, endpointB_at_468]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_470 : momentBQ 470 =
    (-1009111743134600210040196851808035502250880285611491978353694231583392358135485612450290908019797511337622506203840426258906051613386976477802190102977458272748716118416045281269425707377652764752216369327115203918020921362533968327769014747822041868819917968439490532194956875 / 36304123742133375556593322708737806643829594767075060035541305159080582450205184901005085803128817153071257905034008131114613897596311174506612074733945181293529561534361813328678867427595159591558574115780064384913763396164010744339772923348355910229786257457376560371673958711296) := by
  show momentBQ (468 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_470, endpointB_at_469]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_471 : momentBQ 471 =
    (-4023564694966469773649635958060124534506701394119012696669836148909100593927446888791159918359788374992988460906376508104659448347845093445534689899956929368364029799812061398082773990693024002437560587487263600302917460922103524779232199228550013749294736750756606930496487625 / 145216494968533502226373290834951226575318379068300240142165220636322329800820739604020343212515268612285031620136032524458455590385244698026448298935780725174118246137447253314715469710380638366234296463120257539655053584656042977359091693393423640919145029829506241486695834845184) := by
  show momentBQ (469 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_471, endpointB_at_470]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_472 : momentBQ 472 =
    (-8021501589328057574218700986451076301277691314390133592723940857379289719103763542621866588831934785814047059004432146730945269636149772283136037826028782753490072148669905844585402924120487342439213145754863101240848186424321039846494766614879963716746831866158076237231851125 / 290432989937067004452746581669902453150636758136600480284330441272644659601641479208040686425030537224570063240272065048916911180770489396052896597871561450348236492274894506629430939420761276732468592926240515079310107169312085954718183386786847281838290059659012482973391669690368) := by
  show momentBQ (470 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_472, endpointB_at_471]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_473 : momentBQ 473 =
    (-127936152467079697921013519122889199991564534353239249334800480454134095350451550739104685764251705651712174280053739831759652520807066707092051043971069230017528099862684430504319731383006416766699992714497053868943019380089594889755111447196644845041674047221266944732799523875 / 4646927838993072071243945306718439250410188130185607684549287060362314553626263667328650982800488595593121011844353040782670578892327830336846345565944983205571783876398312106070895030732180427719497486819848241268961714708993375275490934188589556509412640954544199727574266715045888) := by
  show momentBQ (471 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_473, endpointB_at_472]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_474 : momentBQ 474 =
    (-255060870563332251880582977870791787721026122399798334297498632279595035762105311515804902062768199639671417222179020425685734306809860263821996055950778612910209298457740841364848851361892285435513938963574464690091474155231475647017061511007264458508030922895675959583572835125 / 9293855677986144142487890613436878500820376260371215369098574120724629107252527334657301965600977191186242023688706081565341157784655660673692691131889966411143567752796624212141790061464360855438994973639696482537923429417986750550981868377179113018825281909088399455148533430091776) := by
  show momentBQ (472 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_474, endpointB_at_473]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_475 : momentBQ 475 =
    (-1017014863638603282814982759864549533318015551340968041819140116051549826140040166170614482908506112487297423101093562456848181096773493457011756425626522317300201633090991962404144154164507214078315073082607042751630561505036896567219928809712510182658604312811872497073739785625 / 37175422711944576569951562453747514003281505041484861476394296482898516429010109338629207862403908764744968094754824326261364631138622642694770764527559865644574271011186496848567160245857443421755979894558785930151693717671947002203927473508716452075301127636353597820594133720367104) := by
  show momentBQ (473 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_475, endpointB_at_474]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_476 : momentBQ 476 =
    (-2027606475506857492264818260193112438004548899199782601268896189264879337588669552344361926977590081106254020372074955045547847365567364850084491231722771862070086203236146080835209503144817540488767103598376567338513982621620928524541626490100520301005680598384933167850171741025 / 74350845423889153139903124907495028006563010082969722952788592965797032858020218677258415724807817529489936189509648652522729262277245285389541529055119731289148542022372993697134320491714886843511959789117571860303387435343894004407854947017432904150602255272707195641188267440734208) := by
  show momentBQ (474 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_476, endpointB_at_475]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_477 : momentBQ 477 =
    (-16169735674420233278649685117002215997195940381013392341211617509347651187997037018275625787409520898906177019605875061665755522268264111283446909066427819303399258881269770005988351415835561730452436817771927415161762768974103035040252130580717594669364629309809256943611873800275 / 594806763391113225119224999259960224052504080663757783622308743726376262864161749418067325798462540235919489516077189220181834098217962283116332232440957850313188336178983949577074563933719094748095678312940574882427099482751152035262839576139463233204818042181657565129506139525873664) := by
  show momentBQ (475 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_477, endpointB_at_476]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_478 : momentBQ 478 =
    (-32237774898057949366867611208111336296296308809944939447572847487189971236446922860335681601313321540586529026509826380805311324270690083502218051409167413328160786574607025735209480495722472129266807995180509374882256589715664541558238524491116210755903065982449902208333106884825 / 1189613526782226450238449998519920448105008161327515567244617487452752525728323498836134651596925080471838979032154378440363668196435924566232664464881915700626376672357967899154149127867438189496191356625881149764854198965502304070525679152278926466409636084363315130259012279051747328) := by
  show momentBQ (476 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_478, endpointB_at_477]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_479 : momentBQ 479 =
    (-128546441329913078437760809545314240545482771112458273194715161737623609156208859773639768058793286310372226620350897660700676535690241211621815075284253325948691337261926759521567510093822242423394426859443621063861048242673758611317997129037798112344667873980229107968792681427775 / 4758454107128905800953799994079681792420032645310062268978469949811010102913293995344538606387700321887355916128617513761454672785743698264930657859527662802505506689431871596616596511469752757984765426503524599059416795862009216282102716609115705865638544337453260521036049116206989312) := by
  show momentBQ (477 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_479, endpointB_at_478]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_480 : momentBQ 480 =
    (-256287790125400814004303910471346763509261057228387580169004132483153542263422674496505174313460518635502038460198553791167319606647558156782533187675285858624217593079624332657822488809186307963135026410790517987447392634140792220894962960816486841939786679856197908372018811614875 / 9516908214257811601907599988159363584840065290620124537956939899622020205826587990689077212775400643774711832257235027522909345571487396529861315719055325605011013378863743193233193022939505515969530853007049198118833591724018432564205433218231411731277088674906521042072098232413978624) := by
  show momentBQ (478 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_480, endpointB_at_479]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_481 : momentBQ 481 =
    (-16351161010000571933474589488071923511890855451171127614782463652425195996406366632877030121198781088945030053760667731876474990904114210402725617373683237780225082438480032423569074786026086448048014685008435047599143650058182543693098636900091860515758390174825426554134800181029025 / 609082125712499942522086399242199269429764178599687970429244153575809293172901631404100941617625641201581557264463041761466198116575193377911124206019540838720704856247279564366924353468128353022049974592451148679605349870337179684109147725966810350801733675194017346692614286874494631936) := by
  show momentBQ (479 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_481, endpointB_at_480]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_482 : momentBQ 482 =
    (-32600339726799477098133329145656911949902973758156156720533020047142958337949491893823434274905677888354020419036341694115466769806747458994207623828195894035833376421002808927656429770891927034673692480089582558518874761758413844909940941345505393419152382905733023005021358365086975 / 1218164251424999885044172798484398538859528357199375940858488307151618586345803262808201883235251282403163114528926083522932396233150386755822248412039081677441409712494559128733848706936256706044099949184902297359210699740674359368218295451933620701603467350388034693385228573748989263872) := by
  show momentBQ (480 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_482, endpointB_at_481]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_483 : momentBQ 483 =
    (-129995545549602894154797217049694159269115177516962931985195984503337688642196936555868549121096914733229102168854457958692794878772963933997649487547287361694754666973376345972937049833307642656935346362514891447039994381949525746715573629182699929775126306939458236961931640617628975 / 4872657005699999540176691193937594155438113428797503763433953228606474345383213051232807532941005129612652458115704334091729584932601547023288993648156326709765638849978236514935394827745026824176399796739609189436842798962697437472873181807734482806413869401552138773540914294995957055488) := by
  show momentBQ (481 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_483, endpointB_at_482]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_484 : momentBQ 484 =
    (-259183665350450490830372091136346739909229639645621746380421807612244708410839854872259653837714966642028209914299882017021038236559760390144381897532169211826187876387911845076476975133489150887430100511598013381986572649725451954631671645761780605328046860419665180526584202722104975 / 9745314011399999080353382387875188310876226857595007526867906457212948690766426102465615065882010259225304916231408668183459169865203094046577987296312653419531277699956473029870789655490053648352799593479218378873685597925394874945746363615468965612827738803104277547081828589991914110976) := by
  show momentBQ (482 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_484, endpointB_at_483]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_485 : momentBQ 485 =
    (-2067043281513923335961231966500616562086004977339049464934768961535670608400499669022566660771859031483943988159499059061366131390745196499911806042302010656299762815820949838833060173585264715755124355319769280277826798404835216001814571389753043670591448101694023960397964922535795875 / 77962512091199992642827059103001506487009814860760060214943251657703589526131408819724920527056082073802439329851269345467673358921624752372623898370501227356250221599651784238966317243920429186822396747833747030989484783403158999565970908923751724902621910424834220376654628719935312887808) := by
  show momentBQ (483 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_485, endpointB_at_484]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_486 : momentBQ 486 =
    (-4121300728296832713143322291971332403169416109457445015653446568670089646027387999886230847353376666896853271237599154870806286711032175289514879263723802689983238438966718544642410696612270062134443817720034833048780441355619904894339568111115862328787485184202311690113055835241473425 / 155925024182399985285654118206003012974019629721520120429886503315407179052262817639449841054112164147604878659702538690935346717843249504745247796741002454712500443199303568477932634487840858373644793495667494061978969566806317999131941817847503449805243820849668440753309257439870625775616) := by
  show momentBQ (484 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_486, endpointB_at_485]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_487 : momentBQ 487 =
    (-16434322657282431683275223460577041558317548189564873334025472119511592045269707703250031650557292140835600081601784284237906550711893736031028469162750472455118345873904322097771588333404484321844757445970015445367359043924262089887304697529511401632078490302436378714895272034357974275 / 623700096729599941142616472824012051896078518886080481719546013261628716209051270557799364216448656590419514638810154763741386871372998018980991186964009818850001772797214273911730537951363433494579173982669976247915878267225271996527767271390013799220975283398673763013237029759482503102464) := by
  show momentBQ (485 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_487, endpointB_at_486]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_488 : momentBQ 488 =
    (-32767407187312610193963535893676195796974002653116000015069267819395802620034673880607352633862691311604451086725528829558536469694556093811352450835792009761642533559673709973174973863933787015423530759829332643637999243635438376346145505751859488675047667522927564131752174836471443575 / 1247400193459199882285232945648024103792157037772160963439092026523257432418102541115598728432897313180839029277620309527482773742745996037961982373928019637700003545594428547823461075902726866989158347965339952495831756534450543993055534542780027598441950566797347526026474059518965006204928) := by
  show momentBQ (486 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_488, endpointB_at_487]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_489 : momentBQ 489 =
    (-522667003168117536372565908599130139515667288221014229748563894889706818840880945669359903487678666331002146022687533625581245655947591463581080896118452877017675166451844586949168025731271717475526154578917060037045463345201336724340976673714086598046252139341123277052374854358798599975 / 19958403095347198116563727130368385660674512604354575415025472424372118918689640657849579654926357010893424468441924952439724379883935936607391717982848314203200056729510856765175377214443629871826533567445439239933308104551208703888888552684480441575071209068757560416423584952303440099278848) := by
  show momentBQ (487 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_489, endpointB_at_488]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_490 : momentBQ 490 =
    (-1042127460304528830190698897513603038911606556268893402872903471405857154130590842592282016156414518758133113235419929008060765878423111813888658228457037944973892203048156385021347290568486553248748467718699659583066107896873830892090904410779620517576883099913282607619765813905580030625 / 39916806190694396233127454260736771321349025208709150830050944848744237837379281315699159309852714021786848936883849904879448759767871873214783435965696628406400113459021713530350754428887259743653067134890878479866616209102417407777777105368960883150142418137515120832847169904606880198557696) := by
  show momentBQ (488 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_490, endpointB_at_489]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_491 : momentBQ 491 =
    (-4155749096806223131005358460697102730680161654998811651456435475769479345247294911072079713407416264598759394412266410779083135768242368335384567711030718662202010948481831788432066542389434132751131644739467622092471785368349929720705361670741588757847407300470518806712290613003068122125 / 159667224762777584932509817042947085285396100834836603320203779394976951349517125262796637239410856087147395747535399619517795039071487492859133743862786513625600453836086854121403017715549038974612268539563513919466464836409669631111108421475843532600569672550060483331388679618427520794230784) := by
  show momentBQ (489 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_491, endpointB_at_490]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_492 : momentBQ 492 =
    (-8286106651269434715385429598823754731844965906810257854940632038245051484719148101709910467262445057112393986007349931064607718772116657027172081036861656965979162359600230796079415773929238321717633157230017926738350056773145786551060181416814695303325074841467694321326542790488805889125 / 319334449525555169865019634085894170570792201669673206640407558789953902699034250525593274478821712174294791495070799239035590078142974985718267487725573027251200907672173708242806035431098077949224537079127027838932929672819339262222216842951687065201139345100120966662777359236855041588461568) := by
  show momentBQ (490 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_492, endpointB_at_491]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_493 : momentBQ 493 =
    (-66086753047929393949537450702813848714958630525047666306477723817222727695199059250222944458410232528676898376204961645320164000938588947509396841440335654338419172965592084641901681904264900761016244936932094196181474843044357858590162910324351350346031694467315513245701938841215598188875 / 2554675596204441358920157072687153364566337613357385653123260470319631221592274004204746195830573697394358331960566393912284720625143799885746139901804584218009607261377389665942448283448784623593796296633016222711463437382554714097777734743613496521609114760800967733302218873894840332707692544) := by
  show momentBQ (491 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_493, endpointB_at_492]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_494 : momentBQ 494 =
    (-131771355468792280430822138013927004638548344434324251479244629842454242037283316922858325360278414960830407918477641576774282379153413662072489036786713890901959527434436144427970290693493706791235230776884885587923711502459642545627038825251191434868456705195479005112626786776703718092625 / 5109351192408882717840314145374306729132675226714771306246520940639262443184548008409492391661147394788716663921132787824569441250287599771492279803609168436019214522754779331884896566897569247187592593266032445422926874765109428195555469487226993043218229521601935466604437747789680665415385088) := by
  show momentBQ (492 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_494, endpointB_at_493]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_495 : momentBQ 495 =
    (-525484960067855855159351441067684613639555138736070395575125345728005783023174361008159718542000966544202234006884522077419709082858754887212152636578595880722389208594816203488059661267576118175573693583933653053056096477420032013937786408390378798969351638127719919173835566700620090369375 / 20437404769635530871361256581497226916530700906859085224986083762557049772738192033637969566644589579154866655684531151298277765001150399085969119214436673744076858091019117327539586267590276988750370373064129781691707499060437712782221877948907972172872918086407741866417750991158722661661540352) := by
  show momentBQ (493 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_495, endpointB_at_494]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_496 : momentBQ 496 =
    (-1047785162801967129378343176431928714469173579661619152389189325724326682512874938010209378183747381776015363565242471293764147201578971866016958893541563907622218482592088066348918960951712381089477243570388920330033065097401154742942616535517785605217676902691029414595102432996993998372875 / 40874809539271061742722513162994453833061401813718170449972167525114099545476384067275939133289179158309733311369062302596555530002300798171938238428873347488153716182038234655079172535180553977500740746128259563383414998120875425564443755897815944345745836172815483732835501982317445323323080704) := by
  show momentBQ (494 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_496, endpointB_at_495]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_497 : momentBQ 497 =
    (-33427726645520822288876819402941209632581053880172301345577685262624486742104300441680550807216972921821909502129832390630088438140696876628734591797180861439947550944631454761905833947782049835402999802939182006658151657462249743250653153342809353663234917960046067452727622781742808528734625 / 1307993905256673975767120421215822522657964858038981454399109360803651185455244290152830052265253733065911465963809993683089776960073625541502023629723947119620918917825223508962533521125777727280023703876104306028269279939868013618062200188730110219063866757530095479450736063434158250346338582528) := by
  show momentBQ (495 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_497, endpointB_at_496]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_498 : momentBQ 498 =
    (-66653676269036488708806696234033679569190793551812375520055304014609389057193886796187979577368249830031211904649223137051142137218170230863331952657960228746454774619979419857240807730889358927332742061796236154121183687213459749620517655860611809819448297179890649588839183454139080989891375 / 2615987810513347951534240842431645045315929716077962908798218721607302370910488580305660104530507466131822931927619987366179553920147251083004047259447894239241837835650447017925067042251555454560047407752208612056538559879736027236124400377460220438127733515060190958901472126868316500692677165056) := by
  show momentBQ (496 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_498, endpointB_at_497]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_499 : momentBQ 499 =
    (-265811648735555153766445981367049975149423526092167425266726573841394069613628632886002665543480610767955796872757745281493109005050775258021239473852829345964777474689315517743936233240052744637917320752464508036314600005634399724390257157709186856026956462247515723059105659317108865152458375 / 10463951242053391806136963369726580181263718864311851635192874886429209483641954321222640418122029864527291727710479949464718215680589004332016189037791576956967351342601788071700268169006221818240189631008834448226154239518944108944497601509840881752510934060240763835605888507473266002770708660224) := by
  show momentBQ (497 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_499, endpointB_at_498]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_500 : momentBQ 500 =
    (-530025231446648052099426355631692836219792401726866910100987857659693585702526031506157619670868151731695426630048009128428143206463970704872010574115361120711329834300338557425283671490686334498452373043491353699665384780774003458453518781404090023540724809491539367622865994029104851356104375 / 20927902484106783612273926739453160362527437728623703270385749772858418967283908642445280836244059729054583455420959898929436431361178008664032378075583153913934702685203576143400536338012443636480379262017668896452308479037888217888995203019681763505021868120481527671211777014946532005541417320448) := by
  show momentBQ (498 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_500, endpointB_at_499]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_501 : momentBQ 501 =
    (-4227481246018464863545024612518382061689064196173490474965479152693716039563347627293113174494844378212002722801262920808342870214756630342059156339144120298793566758379500334024062563809714203959656127394887037108531109011453451584625265800479022027760821080504517996159979168376140294416288495 / 167423219872854268898191413915625282900219501828989626163085998182867351738271269139562246689952477832436667643367679191435491450889424069312259024604665231311477621481628609147204290704099549091843034096141351171618467832303105743111961624157454108040174944963852221369694216119572256044331338563584) := by
  show momentBQ (499 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_501, endpointB_at_500]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_502 : momentBQ 502 =
    (-8429648233078735326709540095620486386481786690573486994991045256568906833380806945440758605429839388889801836483955404965138777134814119185064066233143665026935675033175889887604867267955897185141110721092798702737370414974934128010061158751853379252960200118610805345636365647121285736770204005 / 334846439745708537796382827831250565800439003657979252326171996365734703476542538279124493379904955664873335286735358382870982901778848138624518049209330462622955242963257218294408581408199098183686068192282702343236935664606211486223923248314908216080349889927704442739388432239144512088662677127168) := by
  show momentBQ (500 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_502, endpointB_at_501]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_503 : momentBQ 503 =
    (-33617840164588900645562747552653812242503061662406615466079825903687154343482819730622308223248084574815504535141192670797226756621310491251988566929788082438098050630315003097579570259855988375801800126748571718884891575258601841187534740679702122040689881747925960760884470170392059850625395255 / 1339385758982834151185531311325002263201756014631917009304687985462938813906170153116497973519619822659493341146941433531483931607115392554498072196837321850491820971853028873177634325632796392734744272769130809372947742658424845944895692993259632864321399559710817770957553728956578048354650708508672) := by
  show momentBQ (501 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_503, endpointB_at_502]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_504 : momentBQ 504 =
    (-67035176312291585183895498599029371131671115004759115929379851652879156672988604751121620572401250156143043834486314609959479993819432251939849965468344824424279015471582401802927055607625360518745935441607986946404664512891406852308344622071056120093065509727971647401922710896427904632559187755 / 2678771517965668302371062622650004526403512029263834018609375970925877627812340306232995947039239645318986682293882867062967863214230785108996144393674643700983641943706057746355268651265592785469488545538261618745895485316849691889791385986519265728642799119421635541915107457913156096709301417017344) := by
  show momentBQ (502 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_504, endpointB_at_503]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_505 : momentBQ 505 =
    (-1069370669743699096981190096698801872814753501266395420778202395414977023116722980553606804369258038205139032597757875920782180853786181161897606591995024580101593818237147838284788744216880751132375636806603601287883933896124823596347402304466847630056045036136690565697338483347778478662253709425 / 42860344287450692837937001962400072422456192468221344297750015534814042044997444899727935152627834325103786916702125873007485811427692561743938310298794299215738271099296923941684298420249484567511816728612185899934327765069595070236662175784308251658284785910746168670641719326610497547348822672277504) := by
  show momentBQ (503 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_505, endpointB_at_504]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_506 : momentBQ 506 =
    (-2132388642439415823089224608664739576088033219356950868759702598381944281739683250331647627722461078163514863021667685251935952712401355306991861065621761885469910841514471035946103495893859240376836170820296686132473507788906331408954126971481416957359281883939895840905385846992500847550276208695 / 85720688574901385675874003924800144844912384936442688595500031069628084089994889799455870305255668650207573833404251746014971622855385123487876620597588598431476542198593847883368596840498969135023633457224371799868655530139190140473324351568616503316569571821492337341283438653220995094697645344555008) := by
  show momentBQ (504 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_506, endpointB_at_505]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_507 : momentBQ 507 =
    (-8504269328938223579039634901749890246137650270083649907425058979317714546542847429188270578545309201055282596003409859364440222477521610690730386621392718349561818336316605831105211175323731120712362436196361092125161143711488096409623375945552370395160140003538952187642428140772463854459401954835 / 342882754299605542703496015699200579379649539745770754382000124278512336359979559197823481221022674600830295333617006984059886491421540493951506482390354393725906168794375391533474387361995876540094533828897487199474622120556760561893297406274466013266278287285969349365133754612883980378790581378220032) := by
  show momentBQ (505 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_507, endpointB_at_506]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_508 : momentBQ 508 =
    (-16958217537586871870629331135442088834014131011941952773977780331538874569141654341044066183253072193820297247651769956247434053106063803566722723617806781560960548990169799793387314592213594009941219769219962651160824292489772121242858447891426916113425841308832111758789930671244498928714902122955 / 685765508599211085406992031398401158759299079491541508764000248557024672719959118395646962442045349201660590667234013968119772982843080987903012964780708787451812337588750783066948774723991753080189067657794974398949244241113521123786594812548932026532556574571938698730267509225767960757581162756440064) := by
  show momentBQ (506 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_508, endpointB_at_507]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_509 : momentBQ 509 =
    (-135265152484846466180689074332305795187844997756670851653854263589361259358586581476201882233349308128661111117096401304556304691310571913488898574998726533238212882890094544808672044739467486079294926190707261146660748096788497313535555966252090283644884860203519127650820470629690373344788943705145 / 5486124068793688683255936251187209270074392635932332070112001988456197381759672947165175699536362793613284725337872111744958183862744647903224103718245670299614498700710006264535590197791934024641512541262359795191593953928908168990292758500391456212260452596575509589842140073806143686060649302051520512) := by
  show momentBQ (507 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_509, endpointB_at_508]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_510 : momentBQ 510 =
    (-269733064385302874603928114827682479598551419888056806343147500084875595773998782315019470465323276523754475017392627355844104639843281910002420537571134442508420581794589318233402996877327108782876915684809174978115244240157808984751648930738451155008955074865563682840044749880423828968488758076075 / 10972248137587377366511872502374418540148785271864664140224003976912394763519345894330351399072725587226569450675744223489916367725489295806448207436491340599228997401420012529071180395583868049283025082524719590383187907857816337980585517000782912424520905193151019179684280147612287372121298604103041024) := by
  show momentBQ (508 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_510, endpointB_at_509]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_511 : momentBQ 511 =
    (-1075758927371972641067430952077463065693046251082955968827376500338503846675124555350489417502877538135914906245836478513307664387139677264597888967489583247180642085039597398601454305193104586792885581378238944912718444675452908774480105735533352253506303180934424570385590237758396212003737517503405 / 43888992550349509466047490009497674160595141087458656560896015907649579054077383577321405596290902348906277802702976893959665470901957183225792829745965362396915989605680050116284721582335472197132100330098878361532751631431265351922342068003131649698083620772604076718737120590449149488485194416412164096) := by
  show momentBQ (509 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_511, endpointB_at_510]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_512 : momentBQ 512 =
    (-2145202244602818241189260548271888187751886751181080493610756661144687709905972449906357566409847771742656143766159239931625264208405736071673676825580988901912082748836300879011510639905623432371722910811008776645910166583730947243043498521543025335269907908751817293978310082731518082254028435099745 / 87777985100699018932094980018995348321190282174917313121792031815299158108154767154642811192581804697812555605405953787919330941803914366451585659491930724793831979211360100232569443164670944394264200660197756723065503262862530703844684136006263299396167241545208153437474241180898298976970388832824328192) := by
  show momentBQ (510 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_512, endpointB_at_511]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_513 : momentBQ 513 =
    (-2190251491739477424254235019785597839694676372955883183976582551028726151813997871354391075304454574949251922785248583970189394756782256529178824038918189668852236486561863197470752363343641524451529091938039960955474280081989297135147411990495428867310575974835605457151854594468879961981363032236839645 / 89884656743115795386465259539451236680898848947115328636715040578866337902750481566354238661203768010560056939935696678829394884407208311246423715319737062188883946712432742638151109800623047059726541476042502884419075341171231440736956555270413618581675255342293149119973622969239858152417678164812112068608) := by
  show momentBQ (511 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_513, endpointB_at_512]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_514 : momentBQ 514 =
    (-4367694495223168430822772758753736042899910194023135472140436549127459753032592246385072261279643333670730442513273492010728559134869879979239643258895337292857383870863130703728225473100478127707435206730243430911208944490984504813364137361163399086274306476134160589992879629905778169799092362530773795 / 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216) := by
  show momentBQ (512 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_514, endpointB_at_513]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_515 : momentBQ 515 =
    (-17419793220248045298028568395807702116624155443088380774100962890488895902172790087722564466193130027285987173447880658797652813670200883185683402102598135117427309212586416230822689143688677357588019793379375551299568747483498511415168252121371533320743829330885270835574714477250671688887430628770595875 / 719077253944926363091722076315609893447190791576922629093720324630930703222003852530833909289630144084480455519485573430635159075257666489971389722557896497511071573699461941105208878404984376477812331808340023075352602729369851525895652442163308948653402042738345192959788983753918865219341425318496896548864) := by
  show momentBQ (513 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_515, endpointB_at_514]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_516 : momentBQ 516 =
    (-34738111916882995186554057752416524415093218718547120495148910463169118624332923145807910110253096190335356945885385313757649397357856906857663794095860747117665721478303397027291071360326741060665818112234211050843994376049617419851219019278929251884279442180231404171136372365313475387354157778150295075 / 1438154507889852726183444152631219786894381583153845258187440649261861406444007705061667818579260288168960911038971146861270318150515332979942779445115792995022143147398923882210417756809968752955624663616680046150705205458739703051791304884326617897306804085476690385919577967507837730438682850636993793097728) := by
  show momentBQ (514 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_516, endpointB_at_515]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_517 : momentBQ 517 =
    (-277097032267229473232280042071601578473883116754922379763629681136442039259213782302607282972483999843837847266015980526020319611482439977957643752904191540961845173652513143729321801781210981018799432848751962568360234208953925000208561014248203102239717410879520270481390133053547024601452932974547702575 / 11505236063118821809467553221049758295155052665230762065499525194094891251552061640493342548634082305351687288311769174890162545204122663839542235560926343960177145179191391057683342054479750023644997308933440369205641643669917624414330439074612943178454432683813523087356623740062701843509462805095950344781824) := by
  show momentBQ (515 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_517, endpointB_at_516]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_518 : momentBQ 518 =
    (-552586151387840593621819580997719975641341379834284281501551646521608786220985318286243924070853005491289788261629547238543422668159372567261761526584567657121203818250949808868338061192318223269598095294126254174041395492130554497514557844661310248373595068891267696066369878487827818886069582005335940725 / 23010472126237643618935106442099516590310105330461524130999050388189782503104123280986685097268164610703374576623538349780325090408245327679084471121852687920354290358382782115366684108959500047289994617866880738411283287339835248828660878149225886356908865367627046174713247480125403687018925610191900689563648) := by
  show momentBQ (516 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_518, endpointB_at_517]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_519 : momentBQ 519 =
    (-2203943993759225224754207054712914034121643418412415686452134559292748556626555342817335805271008319198850777120707808098128786162967690586800770876300611543653295537657263137301132112786350288175655723702055677844728809047763949019044549241448391840038315467817295482766641252810525625132470572245220180575 / 92041888504950574475740425768398066361240421321846096523996201552759130012416493123946740389072658442813498306494153399121300361632981310716337884487410751681417161433531128461466736435838000189159978471467522953645133149359340995314643512596903545427635461470508184698852989920501614748075702440767602758254592) := by
  show momentBQ (517 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_519, endpointB_at_518]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_520 : momentBQ 520 =
    (-4395148426860882673642782854774308333942005660995857871826511115352591052232147937988328629008658208806956752061527131756383995527305510129747202036553242673759462199374310880745032248042143638269371240908723750615210630759991690240291153111558931704122652233508479430950816371211741853587874840604629839875 / 184083777009901148951480851536796132722480842643692193047992403105518260024832986247893480778145316885626996612988306798242600723265962621432675768974821503362834322867062256922933472871676000378319956942935045907290266298718681990629287025193807090855270922941016369397705979841003229496151404881535205516509184) := by
  show momentBQ (518 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_520, endpointB_at_519]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_521 : momentBQ 521 =
    (-70119521825457466654885628006168580650736305699272378662832185024932875710226729410675335204338131731274063875196979009713387744027935600069966900183164810041362496934633236666655360634149276198235968874189946605968821909201713581218183473487486341187310621017666048767630716568408866187240403226261556060775 / 2945340432158418383223693624588738123559693482299075088767878449688292160397327779966295692450325070170031945807812908771881611572255401942922812303597144053805349165872996110766935565946816006053119311086960734516644260779498911850068592403100913453684334767056261910363295677456051671938422478104563288264146944) := by
  show momentBQ (519 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_521, endpointB_at_520]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_522 : momentBQ 522 =
    (-139835284408157980526729688096754616691199657622925146699966679924962107222505896080022405522662800132041751182974397679639558284155518403978302513033221185475960910393635187901448982147564487466347738311484365688294829104914741671565628846359881590198878570513157436985735728434888314718892090119166519668225 / 5890680864316836766447387249177476247119386964598150177535756899376584320794655559932591384900650140340063891615625817543763223144510803885845624607194288107610698331745992221533871131893632012106238622173921469033288521558997823700137184806201826907368669534112523820726591354912103343876844956209126576528293888) := by
  show momentBQ (520 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_522, endpointB_at_521]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_523 : momentBQ 523 =
    (-557733835512997922330749445627285655078692887300632481665384344068527025358730413100779019728321743055384915637840413733734789937953619381384723816350893693794924550650475979331066629944883645411754772345805458549865582751786383448658312755021596687344952459403053225678739054792025806982247761739664164653725 / 23562723457267347065789548996709904988477547858392600710143027597506337283178622239730365539602600561360255566462503270175052892578043215543382498428777152430442793326983968886135484527574528048424954488695685876133154086235991294800548739224807307629474678136450095282906365419648413375507379824836506306113175552) := by
  show momentBQ (521 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_523, endpointB_at_522]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_524 : momentBQ 524 =
    (-1112268432963779795393827288315982673512574916739119843933070498782932480782324705285109976245964776303568770574125337522534198671674235209912556291499009794700012057989381350750100372911115950601262385385612033016271133480139957814437132320243834311473777084430945534192972914241076322528650890046787234672725 / 47125446914534694131579097993419809976955095716785201420286055195012674566357244479460731079205201122720511132925006540350105785156086431086764996857554304860885586653967937772270969055149056096849908977391371752266308172471982589601097478449614615258949356272900190565812730839296826751014759649673012612226351104) := by
  show momentBQ (522 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_524, endpointB_at_523]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_525 : momentBQ 525 =
    (-8872675667535495314401141345726732013898021282384581961145486039909652232194880282617862024252161765169689811068404410008001813831294471712661231485621872026423760309915293981174464806810047086857398417770721942763384232723253861954861093699655014164046542391071283078104249583068127916354505191594600459793875 / 377003575316277553052632783947358479815640765734281611362288441560101396530857955835685848633641608981764089063400052322800846281248691448694119974860434438887084693231743502178167752441192448774799271819130974018130465379775860716808779827596916922071594850183201524526501846714374614008118077197384100897810808832) := by
  show momentBQ (523 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_525, endpointB_at_524]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_526 : momentBQ 526 =
    (-17694650331256502084148561883763596987716625300298394882512997873876963594491504106477907694080025463109838537502132223387386474440695832158392970219897333355553670560916786282456504100438322476075611701725611188710977698402374844698551552578169142532869961682765015967190760597090152244615556067808660345531785 / 754007150632555106105265567894716959631281531468563222724576883120202793061715911671371697267283217963528178126800104645601692562497382897388239949720868877774169386463487004356335504882384897549598543638261948036260930759551721433617559655193833844143189700366403049053003693428749228016236154394768201795621617664) := by
  show momentBQ (524 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_526, endpointB_at_525]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_527 : momentBQ 527 =
    (-70576761207178975993429054813946818403478098631228198599833212052079600040386265428499335251292573044875363596348808754119271527331900866669787930648944116691923195507230831978315105708592396492027820057453103182349108766631525521250116268648286808049355854772701527564954782761777831576432389030917432328756055 / 3016028602530220424421062271578867838525126125874252890898307532480811172246863646685486789069132871854112712507200418582406770249989531589552959798883475511096677545853948017425342019529539590198394174553047792145043723038206885734470238620775335376572758801465612196212014773714996912064944617579072807182486470656) := by
  show momentBQ (525 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_527, endpointB_at_526]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_528 : momentBQ 528 =
    (-140751757170294314552360411023639670098777005050134415044449157242382655868018908852661862142520861992721076166532444023869742647487339299563467011597799367444423678326564714248973768690190908374044096547216720008821467388481467405756873241649619421745489569954666613796522726152995258039526453266592450431731715 / 6032057205060440848842124543157735677050252251748505781796615064961622344493727293370973578138265743708225425014400837164813540499979063179105919597766951022193355091707896034850684039059079180396788349106095584290087446076413771468940477241550670753145517602931224392424029547429993824129889235158145614364972941312) := by
  show momentBQ (526 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_528, endpointB_at_527]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_529 : momentBQ 529 =
    (-4491260615161209491625318569936138564060975342963379970963786744734210200879512455207664873820438414495008884950262532034389060842550554013343356460984325270272064644784019518308162982750637167208134353461188065736030459396090459947332955256274219730242439914007998312961770625427394142897616826961268191048893815 / 193025830561934107162947985381047541665608072055952185017491682078771915023799273387871154500424503798663213600460826789274033295999330021731389427128542432710187362934652673115221889249890533772697227171395058697282798274445240687006095271729621464100656563293799180557568945517759802372156455525060659659679134121984) := by
  show momentBQ (527 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_529, endpointB_at_528]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_530 : momentBQ 530 =
    (-8957050943279916850027809246280956871614988632942090490296398895452914483795625028816798566881970751025017719513283499614896898277676435697688546439203143970013285822773422668837640731194559945944388927980252191590760178946834471161505232127352177344812427427747520264980468827648205710315663048098559435834750425 / 386051661123868214325895970762095083331216144111904370034983364157543830047598546775742309000849007597326427200921653578548066591998660043462778854257084865420374725869305346230443778499781067545394454342790117394565596548890481374012190543459242928201313126587598361115137891035519604744312911050121319319358268243968) := by
  show momentBQ (528 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_530, endpointB_at_529]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_531 : momentBQ 531 =
    (-35726803196403290982941110842713099672819030132150149616012428801863134374988587379091909755449973901258278224624681732426211401809449028424365258815991408212468087225175500984759948124047735331559317346698590817024277393006807683085702001353250005484780135060864637434280586984242088436994927705057272919537098865 / 1544206644495472857303583883048380333324864576447617480139933456630175320190394187102969236003396030389305708803686614314192266367994640173851115417028339461681498903477221384921775113999124270181577817371160469578262386195561925496048762173836971712805252506350393444460551564142078418977251644200485277277433072975872) := by
  show momentBQ (529 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_531, endpointB_at_530]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_532 : momentBQ 532 =
    (-71251760047064190491402328403828950194944167438694931155098233712190318838254075394460136404936953599684588775663913285573178671405285350473451617864660831067803586386931931342487354168298590802488356064319788465590790506957079729543801166540662440317103885177882582001700831669138176374345816270537951076816925985 / 3088413288990945714607167766096760666649729152895234960279866913260350640380788374205938472006792060778611417607373228628384532735989280347702230834056678923362997806954442769843550227998248540363155634742320939156524772391123850992097524347673943425610505012700786888921103128284156837954503288400970554554866145951744) := by
  show momentBQ (530 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_532, endpointB_at_531]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_533 : momentBQ 533 =
    (-568406897819060948205848649898214407194253847010942270342550571192736302912688526267084246057429381723799614217890315759346936619255697419942347116950414599721350414710787813190820171222291765725113878077017259864600215999108733782300549155636412399822911444915288868449658514292899286715645947842411775131599687745 / 24707306311927565716857342128774085333197833223161879682238935306082805123046306993647507776054336486228891340858985829027076261887914242781617846672453431386903982455635542158748401823985988322905245077938567513252198179128990807936780194781391547404884040101606295111368825026273254703636026307207764436438929167613952) := by
  show momentBQ (531 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_533, endpointB_at_532]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_534 : momentBQ 534 =
    (-1133614507282667519592527419965857251120997822462723514773229375568252701681403195913528243075135896383487785954254044375583102488309205173355938058758519173553087224835961436063493136978041551530574207121706092375365909206477643547064697471747666756119615133104975735763577862464074937671166308736367198808424893195 / 49414612623855131433714684257548170666395666446323759364477870612165610246092613987295015552108672972457782681717971658054152523775828485563235693344906862773807964911271084317496803647971976645810490155877135026504396358257981615873560389562783094809768080203212590222737650052546509407272052614415528872877858335227904) := by
  show momentBQ (532 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_534, endpointB_at_533]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_535 : momentBQ 535 =
    (-4521720787475808645565699259414374428628699179486144356679735149738536057268518365722500295412058912540878247345620064644179790824154694792599528211901958501251078256368160784298202962103424166217458916047254638126459525486511948979864804522139569645196217665755802092090675743536478683969258871925959051426863338025 / 197658450495420525734858737030192682665582665785295037457911482448662440984370455949180062208434691889831130726871886632216610095103313942252942773379627451095231859645084337269987214591887906583241960623508540106017585433031926463494241558251132379239072320812850360890950600210186037629088210457662115491511433340911616) := by
  show momentBQ (533 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_535, endpointB_at_534]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_536 : momentBQ 536 =
    (-9018086131283528644520749737934836477283779485068628090798649354712183127300017002291416477018068896600218859659395530795027732353968335221876068415139046207168038316906219732422771141241782402530894697985833082020434231203940653386010740981538169740980120092264375387403272931501724777187288254850464126864417162005 / 395316900990841051469717474060385365331165331570590074915822964897324881968740911898360124416869383779662261453743773264433220190206627884505885546759254902190463719290168674539974429183775813166483921247017080212035170866063852926988483116502264758478144641625700721781901200420372075258176420915324230983022866681823232) := by
  show momentBQ (534 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_536, endpointB_at_535]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_537 : momentBQ 537 =
    (-143885583199135703298398230893318510361438212978184528791996360599810802434085345902231704685556950006949760611580504812237084266961076870928142046802740901424815417324966401402387199253544259526948155703684411413132002882940485947308141524018870200792652960875083840136329832295154384877809121558733524651015849943035 / 6325070415853456823515479584966165845298645305129441198653167438357198111499854590373761990669910140474596183259900372230931523043306046152094168748148078435047419508642698792639590866940413010663742739952273283392562733857021646831815729864036236135650314266011211548510419206725953204130822734645187695728365866909171712) := by
  show momentBQ (535 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_537, endpointB_at_536]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_538 : momentBQ 538 =
    (-286967336324533218310213231446450883793482916386658529490182685665544449547309879816182785322591235488721030940414749821053849627402818116879031903399879898372397228966553102238280615271035199168270902716286787008313547649216499906083835330026461797111603949901703524741171788432235281571943331823842839667109823629405 / 12650140831706913647030959169932331690597290610258882397306334876714396222999709180747523981339820280949192366519800744461863046086612092304188337496296156870094839017285397585279181733880826021327485479904546566785125467714043293663631459728072472271300628532022423097020838413451906408261645469290375391456731733818343424) := by
  show momentBQ (536 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_538, endpointB_at_537]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_539 : momentBQ 539 =
    (-1144668966082617632887950919487144231637201372798827517260096735015350164922912643281651035877845337098132588100613481628218515428264772637216361458543015356704766641937217392943030112214947095567117764366452499851005340623082915982260056911220793711155208320611627814302146204415570472589944962999938167147988255592385 / 50600563326827654588123836679729326762389162441035529589225339506857584891998836722990095925359281123796769466079202977847452184346448369216753349985184627480379356069141590341116726935523304085309941919618186267140501870856173174654525838912289889085202514128089692388083353653807625633046581877161501565826926935273373696) := by
  show momentBQ (537 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_539, endpointB_at_538]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_540 : momentBQ 540 =
    (-2282966861853087115685616397863970406326514797326047460212623358333026766775753416563589728327799141707778352890833938312309655074925103126173633706741635451683903784939719290192499759983428808413082739691904336437533842615610639482244083821080432726329960936284786457096117198045896582623730677597279275851739099743625 / 101201126653655309176247673359458653524778324882071059178450679013715169783997673445980191850718562247593538932158405955694904368692896738433506699970369254960758712138283180682233453871046608170619883839236372534281003741712346349309051677824579778170405028256179384776166707307615251266093163754323003131653853870546747392) := by
  show momentBQ (538 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_540, endpointB_at_539]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_541 : momentBQ 541 =
    (-18213002297894628322914139707403675019360418049778911960362928569812369094944343923251749165992886486068720637506875196758203692708846933828807433349338825047878254639852427226202386974090020938228815634430970150690547766644538212758347246483730563305610132802805296402166801646632819403598206961276072445128318595732475 / 809609013229242473409981386875669228198226599056568473427605432109721358271981387567841534805748497980748311457267247645559234949543173907468053599762954039686069697106265445457867630968372865364959070713890980274248029933698770794472413422596638225363240226049435078209333658460922010128745310034584025053230830964373979136) := by
  show momentBQ (539 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_541, endpointB_at_540]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_542 : momentBQ 542 =
    (-36325008279904443549767757383158161452661536184309512024457670844413209340933358767446649445667882658906006594953638331427175202278827803329543845811343054023402286056193657998285352208952185937798321755177480208124031497614522609179772049826146539384017251930179140144062807720363793228248549558626399571706942263947025 / 1619218026458484946819962773751338456396453198113136946855210864219442716543962775135683069611496995961496622914534495291118469899086347814936107199525908079372139394212530890915735261936745730729918141427781960548496059867397541588944826845193276450726480452098870156418667316921844020257490620069168050106461661928747958272) := by
  show momentBQ (540 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_542, endpointB_at_541]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_543 : momentBQ 543 =
    (-144897911256740603237265482402929787934786422934459714016379122445795864566601331467194937456704727506558646233006948473331278205400047436897553126649674691510324248069171012162902087593643221397638324049250391531299180992329516385694957881409831767801190587957651846847719170279384725017478531634225601243598540912644775 / 6476872105833939787279851095005353825585812792452547787420843456877770866175851100542732278445987983845986491658137981164473879596345391259744428798103632317488557576850123563662941047746982922919672565711127842193984239469590166355779307380773105802905921808395480625674669267687376081029962480276672200425846647714991833088) := by
  show momentBQ (541 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_543, endpointB_at_542]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_544 : momentBQ 544 =
    (-288995281567311368887584746671036759361645849057126832927695376811780702257144092042305924982709428894296526464726565739627576973201199584088489937682500351575840074878291355750318528294503883561035552385521499131486211813430692901855689476182040155669777912998410589569207847905292186360827347624063215739994879941794275 / 12953744211667879574559702190010707651171625584905095574841686913755541732351702201085464556891975967691972983316275962328947759192690782519488857596207264634977115153700247127325882095493965845839345131422255684387968478939180332711558614761546211605811843616790961251349338535374752162059924960553344400851693295429983666176) := by
  show momentBQ (542 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_544, endpointB_at_543]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_545 : momentBQ 545 =
    (-18444698852972519720178202949298522582787396836881330219208793167104827173470667050935407565072925314724219483189901401617407118583723620513883034257971345968222734190761536528770329599972747862571974961075930973980149401033664811677260181273971386405982884447251499393093559704543648364793980716006387592817320278638046375 / 829039629546744292771820940160685289674984037433926116789867962480354670870508940869469731641086461932286270932241661589052656588332210081247286886157264936638535369836815816148856454111613814133718088411024363800829982652107541293539751344738957542771957991474621520086357666263984138371835197475414041654508370907518954635264) := by
  show momentBQ (543 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_545, endpointB_at_544]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_546 : momentBQ 546 =
    (-36787867253543355845566434139243108344018165801266065960146712243381554380848835017186767015108751957991241427940225364326828509909188211924019923373238262509097453330931725150042840871872251241496764738879884346268664952153382844574645535862031003712483294301215375853748072291447606922075334015227418923655829619962488825 / 1658079259093488585543641880321370579349968074867852233579735924960709341741017881738939463282172923864572541864483323178105313176664420162494573772314529873277070739673631632297712908223227628267436176822048727601659965304215082587079502689477915085543915982949243040172715332527968276743670394950828083309016741815037909270528) := by
  show momentBQ (544 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_546, endpointB_at_545]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_547 : momentBQ 547 =
    (-146747206736661957933413358159837893723940595449006394983881940047774771870858539683942817873455790777481545476289030848908118121945443087125486067961379003195630500649760617906214848752633265941355226375971406787862916237710746951435124500196892904919026767377375620163852200459291003436410398324478605157000726945564653225 / 6632317036373954342174567521285482317399872299471408934318943699842837366964071526955757853128691695458290167457933292712421252706657680649978295089258119493108282958694526529190851632892910513069744707288194910406639861216860330348318010757911660342175663931796972160690861330111873106974681579803312333236066967260151637082112) := by
  show momentBQ (545 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_547, endpointB_at_546]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_548 : momentBQ 548 =
    (-292689584185919919753846387115874117098389743390979848130557946237883502945350396334884121206472153086348018491099328439047087515616962354760338757122238560304264855957749239736161608755252089839156402150246443885847242441211014486317588354140420766483835837675899088846001372396867430985600995561254402607473113523968988425 / 13264634072747908684349135042570964634799744598942817868637887399685674733928143053911515706257383390916580334915866585424842505413315361299956590178516238986216565917389053058381703265785821026139489414576389820813279722433720660696636021515823320684351327863593944321381722660223746213949363159606624666472133934520303274164224) := by
  show momentBQ (546 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_548, endpointB_at_547]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_549 : momentBQ 549 =
    (-2335107412519784469277037234435404452471094814060883021946714125824866195031153162000206894004920170243637840954536977984514355142841896742722994609741655083303368522349050503880471812915989300687576259490652285892197342979880575427336672051645838669830894675764654774515908759341431401950816701813511401824584767019694192325 / 106117072581983269474793080340567717078397956791542542949103099197485397871425144431292125650059067127332642679326932683398740043306522890399652721428129911889732527339112424467053626126286568209115915316611118566506237779469765285573088172126586565474810622908751554571053781281789969711594905276852997331777071476162426193313792) := by
  show momentBQ (547 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_549, endpointB_at_548]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_550 : momentBQ 550 =
    (-4657454675244378859486986833709959700283877634602307666724320524186208531073065049891123039955168645567911540701672114559277265722061706617999415478446470521342784211242641715390012085870689042355001829038732701369683225069160710551791722944539514286821183369694530014744845339670068096787148066458642959923352130940920110375 / 212234145163966538949586160681135434156795913583085085898206198394970795742850288862584251300118134254665285358653865366797480086613045780799305442856259823779465054678224848934107252252573136418231830633222237133012475558939530571146176344253173130949621245817503109142107562563579939423189810553705994663554142952324852386627584) := by
  show momentBQ (548 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_550, endpointB_at_549]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_551 : momentBQ 551 =
    (-18579010104520304032208089296653911968041504600577205492351198600117348213044190399020225363021163651592723491453579307896462401807642516945255850108566466043320124653575192588301248211636894107139770932565417357827427265094070179910238254800581262445973956932926907004273073954974780735183641559655023007403335591426143131205 / 848936580655866155798344642724541736627183654332340343592824793579883182971401155450337005200472537018661141434615461467189920346452183123197221771425039295117860218712899395736429009010292545672927322532888948532049902235758122284584705377012692523798484983270012436568430250254319757692759242214823978654216571809299409546510336) := by
  show momentBQ (549 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_551, endpointB_at_550]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_552 : momentBQ 552 =
    (-37056864074170261581482196255939472328271530954690288268773080329453658232550935115287164562541304633576049214351150017020348783278764294233822466913456526645388052621196255271403034091812970279031956905425396871601347666675831447770148533622211991702586894136636426130119978723261858489957934798658566760682878067109494194545 / 1697873161311732311596689285449083473254367308664680687185649587159766365942802310900674010400945074037322282869230922934379840692904366246394443542850078590235720437425798791472858018020585091345854645065777897064099804471516244569169410754025385047596969966540024873136860500508639515385518484429647957308433143618598819093020672) := by
  show momentBQ (550 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_552, endpointB_at_551]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_553 : momentBQ 553 =
    (-591298657183499391321911566344773319325028341755275469332161760039543155275921442926538669324028643500974350507255306793324695802752456347122297624227762838211191970086044594982822326595450438800205573230048723994682373637827397449201935297363121780645625658615024712598001399627700089818024437874247565268287663070834103017305 / 27165970580987716985547028567185335572069876938634890994970393394556261855084836974410784166415121184597156525907694766950077451086469859942311096685601257443771526998812780663565728288329361461533674321052446353025596871544259913106710572064406160761551519464640397970189768008138232246168295750874367316934930297897581105488330752) := by
  show momentBQ (551 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_553, endpointB_at_552]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_554 : momentBQ 554 =
    (-1179389545883182330249671713703951123355345860680052156733045969843790416400255608585844759971796733782232746129299463640211825443826327940101074646515772894298272591328946090897021747260003316449596288015811469378182021921380866883308742555138378524506555337165230122957677294374960576978808236845018199802750980772387008369055 / 54331941161975433971094057134370671144139753877269781989940786789112523710169673948821568332830242369194313051815389533900154902172939719884622193371202514887543053997625561327131456576658722923067348642104892706051193743088519826213421144128812321523103038929280795940379536016276464492336591501748734633869860595795162210976661504) := by
  show momentBQ (552 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_554, endpointB_at_553]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_555 : momentBQ 555 =
    (-4704785011555655144136777052862332098583599913543168350866483020495987040152644214755806713966914768337065647916519521019617570813819828064302120882310213170395636149525218160437577728239363410385573639918670302032097957484208873307061951348115192308952143132012921609632611589474120713218711558533375851198699760842915683205075 / 217327764647901735884376228537482684576559015509079127959763147156450094840678695795286273331320969476777252207261558135600619608691758879538488773484810059550172215990502245308525826306634891692269394568419570824204774972354079304853684576515249286092412155717123183761518144065105857969346366006994938535479442383180648843906646016) := by
  show momentBQ (553 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_555, endpointB_at_554]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_556 : momentBQ 556 =
    (-9384138752778577017224166121655138077715396584310427683620174240881184961169328190512933391642116483872309319357814612195885857461078467868797203273364695458789133725269218925413330712001757288823117152053996440269427817900935536488139784040294626821639680084933881480834776629815948882041646297831436157255784928383977768122555 / 434655529295803471768752457074965369153118031018158255919526294312900189681357391590572546662641938953554504414523116271201239217383517759076977546969620119100344431981004490617051652613269783384538789136839141648409549944708158609707369153030498572184824311434246367523036288130211715938692732013989877070958884766361297687813292032) := by
  show momentBQ (554 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_556, endpointB_at_555]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_557 : momentBQ 557 =
    (-74870574653463610878428778625291713152419962676260894252768152756382979294509244340135562095907245903700654929264866222483722416721841876737382003094686670962569419433982473297002760860503229016581560587250950016250326978792356186801057701443789504641715145425839385339897606348675448274706372261115558981270974716387275862215205 / 3477244234366427774150019656599722953224944248145266047356210354503201517450859132724580373301135511628436035316184930169609913739068142072615820375756960952802755455848035924936413220906158267076310313094713133187276399557665268877658953224243988577478594491473970940184290305041693727509541856111919016567671078130890381502506336256) := by
  show momentBQ (555 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_557, endpointB_at_556]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_558 : momentBQ 558 =
    (-149337896660678764247638012661937330901864593417102070942235938442264793529981634581491219907635458166986405074350567994936114192060980834928602164161933377808643850971552114601382526599675201862517259986419758470474171047465543489292594445788240825236886044107913028927515692375903811549728509124056348345048568958539072680289215 / 6954488468732855548300039313199445906449888496290532094712420709006403034901718265449160746602271023256872070632369860339219827478136284145231640751513921905605510911696071849872826441812316534152620626189426266374552799115330537755317906448487977154957188982947941880368580610083387455019083712223838033135342156261780763005012672512) := by
  show momentBQ (556 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_558, endpointB_at_557]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_559 : momentBQ 559 =
    (-595745802807653995009394652662137094242922195244568476554511109269679982791647165911110135330459730967225336371871620710981702852200256879123778525850293367387170631295116500184009864177198923559074230698513230027375456544190501446532823004165992969493384111441244448732347547004949613816658891236826938021645366490516085638573105 / 27817953874931422193200157252797783625799553985162128378849682836025612139606873061796642986409084093027488282529479441356879309912545136580926563006055687622422043646784287399491305767249266136610482504757705065498211196461322151021271625793951908619828755931791767521474322440333549820076334848895352132541368625047123052020050690048) := by
  show momentBQ (557 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_559, endpointB_at_558]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_560 : momentBQ 560 =
    (-1188294400949077288793336382322509588695631927902851254665974752836660430791925921271713418414065474111728533192552517160544899249021979284835443750130728273053122099989364754392076920496559570247527311679503133238861599368108066391563680947486730162764084587221802433518009865671768907702280257118178955087897287364803999082305925 / 55635907749862844386400314505595567251599107970324256757699365672051224279213746123593285972818168186054976565058958882713758619825090273161853126012111375244844087293568574798982611534498532273220965009515410130996422392922644302042543251587903817239657511863583535042948644880667099640152669697790704265082737250094246104040101380096) := by
  show momentBQ (558 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_560, endpointB_at_559]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_561 : momentBQ 561 =
    (-37923567024574838045204478258692663159229167527642424327482679969101420034130892973157253953386032416651450616459461761952247213175930024604605447682743528028581068162517726590169997719847343999042514489885857137937383042690763147410760903381219359765928070969335809092560486284439024854384201348600168366662321999613887627855306235 / 1780349047995611020364810064179058152051171455050376216246379701505639176934839875954985151130181381953759250081886684246840275834402888741179300032387564007835010793394194393567443569103953032743070880304493124191885516573524617665361384050812922151669040379634673121374356636181347188484885430329302536482647592003015875329283244163072) := by
  show momentBQ (559 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_561, endpointB_at_560]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_562 : momentBQ 562 =
    (-75644334225488848079472034173755953788195077474923124460700746676335987554710283844853773928411711718775353368659782017156086687243967375280844021313707678901929082484594181915151920585577857281512609116189436964976705213495479433070662122787138081244337810008354314393182146439014739415429449748812100538850513935058717033101760565 / 3560698095991222040729620128358116304102342910100752432492759403011278353869679751909970302260362763907518500163773368493680551668805777482358600064775128015670021586788388787134887138207906065486141760608986248383771033147049235330722768101625844303338080759269346242748713272362694376969770860658605072965295184006031750658566488326144) := by
  show momentBQ (560 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_562, endpointB_at_561]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_563 : momentBQ 563 =
    (-301769746145099639491416905013453466891696376688216450250695861295988049995837110996729824105870209383441890129066247833565740841282873408148847501397388996615880788132491380522723498136771452002048522488428323265974685211133211546164456368841216331227411690460374328949313829744254529838777271061987063003741729968686198555541187165 / 14242792383964888162918480513432465216409371640403009729971037612045113415478719007639881209041451055630074000655093473974722206675223109929434400259100512062680086347153555148539548552831624261944567042435944993535084132588196941322891072406503377213352323037077384970994853089450777507879083442634420291861180736024127002634265953304576) := by
  show momentBQ (561 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_563, endpointB_at_562]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_564 : momentBQ 564 =
    (-601931482985696083745756988152945370016651920108112031317107375196082735604485036677313663358600790652940040168634806957538769031546477508616617662645235955949616563184347815856160725413133819890409397432513333974581832135173350917127325936427506110068176426975133874618258314036941095930633881709789470254355173632033039037074161965 / 28485584767929776325836961026864930432818743280806019459942075224090226830957438015279762418082902111260148001310186947949444413350446219858868800518201024125360172694307110297079097105663248523889134084871889987070168265176393882645782144813006754426704646074154769941989706178901555015758166885268840583722361472048254005268531906609152) := by
  show momentBQ (562 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_564, endpointB_at_563]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_565 : momentBQ 565 =
    (-4802644811056085774567210011858606675664775958309404505189686504224064379823018909659417526797346733933032235388043672533554008230424022675132587733871563478321408748811285764809793021913301754444755830578563834903578447887021416891973345237453506197352471491822876659188231229018147041999738417897256411603897661957710417848995973125 / 227884678143438210606695688214919443462549946246448155679536601792721814647659504122238099344663216890081184010481495583595555306803569758870950404145608193002881381554456882376632776845305988191113072678975119896561346121411151061166257158504054035413637168593238159535917649431212440126065335082150724669778891776386032042148255252873216) := by
  show momentBQ (563 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_565, endpointB_at_564]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_566 : momentBQ 566 =
    (-9579788853203909146791585280291415439777349566397697128050932195151363816036358072895864695045327025031021821738628706097903304912721900097122878541722569982421641875947467357417056169373966508423433311614232640595279488086147144844697274482495754839674752869529879637000241761245047285546380879593288452880694982347503789231537100375 / 455769356286876421213391376429838886925099892492896311359073203585443629295319008244476198689326433780162368020962991167191110613607139517741900808291216386005762763108913764753265553690611976382226145357950239793122692242822302122332514317008108070827274337186476319071835298862424880252130670164301449339557783552772064084296510505746432) := by
  show momentBQ (564 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_566, endpointB_at_565]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_567 : momentBQ 567 =
    (-38217602880802874299391165305473526613104691379727915397772093456981942573516071605298343606735597919646726631600395085457713184616477120882161589659380853392770437024539542920578997933650912325123873529372680746403076120315406807525311741663384124431069950493636869647255381443270877686861710293501140153011677155725553986015566736125 / 1823077425147505684853565505719355547700399569971585245436292814341774517181276032977904794757305735120649472083851964668764442454428558070967603233164865544023051052435655059013062214762447905528904581431800959172490768971289208489330057268032432283309097348745905276287341195449699521008522680657205797358231134211088256337186042022985728) := by
  show momentBQ (565 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_567, endpointB_at_566]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_568 : momentBQ 568 =
    (-76232996222553881538997192170177352027198246826229757169100948324244403969394492038081881162641906961411724550864280144008242701589480817844311742336436940365473305599213797254276625507864518235829102225256617150232590991316975483793875802153946110637636885376196295539763379915942438560565422119840898612092075596341448956232109309625 / 3646154850295011369707131011438711095400799139943170490872585628683549034362552065955809589514611470241298944167703929337528884908857116141935206466329731088046102104871310118026124429524895811057809162863601918344981537942578416978660114536064864566618194697491810552574682390899399042017045361314411594716462268422176512674372084045971456) := by
  show momentBQ (566 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_568, endpointB_at_567]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_569 : momentBQ 569 =
    (-1216506827044416165967377728574801969673459347241103026374526400723505770384844499706292554327792684327880055156749709903680830716913827698839509916439197935691285285125482144916836854935359143115413701707264045510049656241720186241386778645639731596513275931425780321782421259785391308297473567067320255316905938741617769963534927433875 / 58338477604720181915314096183019377526412786239090727853961370058936784549800833055292953432233783523860783106683262869400462158541713858270963303461275697408737633677940961888417990872398332976924946605817630693519704607081254671658561832577037833065891115159868968841194918254390384672272725781030585515463396294754824202789953344735543296) := by
  show momentBQ (567 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_569, endpointB_at_568]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_570 : momentBQ 570 =
    (-2426599734086840682553556629055184948294158803371971766142508725520525570099821629466857731391994194573187807737980528542491639479256932228792344033670456339208451315672095315431651722937842930467477243300078544207216801114854853047405964433745334555435093466025062680532597767761720799503747800740612460078538208210432634285785839433125 / 116676955209440363830628192366038755052825572478181455707922740117873569099601666110585906864467567047721566213366525738800924317083427716541926606922551394817475267355881923776835981744796665953849893211635261387039409214162509343317123665154075666131782230319737937682389836508780769344545451562061171030926792589509648405579906689471086592) := by
  show momentBQ (568 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_570, endpointB_at_569]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_571 : momentBQ 571 =
    (-9680855781251711775661031183283316793720907226083971572294850599708202011240341027030937686290166313086717675080996003343203488027772392786445246197485294237473716301470780258406273715720447059443935528533997560574054396026631466368072216004099808384314741301299986904440574252438865084336004384007285498629115588544778614676977191001625 / 466707820837761455322512769464155020211302289912725822831690960471494276398406664442343627457870268190886264853466102955203697268333710866167706427690205579269901069423527695107343926979186663815399572846541045548157636856650037373268494660616302664527128921278951750729559346035123077378181806248244684123707170358038593622319626757884346368) := by
  show momentBQ (569 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_571, endpointB_at_570]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_572 : momentBQ 572 =
    (-19310848922671978480696873060875127544742755394938079896399010215530021174785899176511800393492993748871753821221111117001591546170985561092401287949099387279303962990149244683580990826980016113321615704028411946574164548291301646573089761871575624780620823716603651636003177011432342085917178622389313805496607102193525117543042067514625 / 933415641675522910645025538928310040422604579825451645663381920942988552796813328884687254915740536381772529706932205910407394536667421732335412855380411158539802138847055390214687853958373327630799145693082091096315273713300074746536989321232605329054257842557903501459118692070246154756363612496489368247414340716077187244639253515768692736) := by
  show momentBQ (570 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_572, endpointB_at_571]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_573 : momentBQ 573 =
    (-154081668676704387737588336800409234465394992347023420711827067523914364758256720002796952790038502569669028741351662828663048630637024651793215870978478327871928823578743274013747626108980408288810933694380545671616236011191434816362905023045229285836981537487026339277479894895414701538681823833190259105396004920299385728088188804434875 / 7467325133404183285160204311426480323380836638603613165307055367543908422374506631077498039325924291054180237655457647283259156293339373858683302843043289268318417110776443121717502831666986621046393165544656728770522189706400597972295914569860842632434062740463228011672949536561969238050908899971914945979314725728617497957114028126149541888) := by
  show momentBQ (571 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_573, endpointB_at_572]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_574 : momentBQ 574 =
    (-307356627046200899099587205868879153567096817194847765922545092809483628130344556654793921534055861146826701311282636323144615331270714095985420140538221167116255925568069043975067254175505421769827045746382135606731863456879249555153229391519541140858062648076214844317904921231167546001244894662018265545318732327927046923568586044448625 / 14934650266808366570320408622852960646761673277207226330614110735087816844749013262154996078651848582108360475310915294566518312586678747717366605686086578536636834221552886243435005663333973242092786331089313457541044379412801195944591829139721685264868125480926456023345899073123938476101817799943829891958629451457234995914228056252299083776) := by
  show momentBQ (572 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_574, endpointB_at_573]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_575 : momentBQ 575 =
    (-1226213721142508813480931535609291396635281727136239344882627635076162906652419921148916516224717634192043808367312259895472420049843092821962738888209976433268686532318602980318648104637469365597393614563092492228947678251312685507492848966166810474851852724903365842313592804214936725335977018773557191809721074966816964207268400769664375 / 59738601067233466281281634491411842587046693108828905322456442940351267378996053048619984314607394328433441901243661178266073250346714990869466422744346314146547336886211544973740022653335892968371145324357253830164177517651204783778367316558886741059472501923705824093383596292495753904407271199775319567834517805828939983656912225009196335104) := by
  show momentBQ (573 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_575, endpointB_at_574]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_576 : momentBQ 576 =
    (-2446029805479056711413266906684969099027248940913507006226737212925841485096218520970099554973480219857868257734447238434968462255947873855289150443090161685146406004468587162479111958294221499722105175484986241020179107746531565699294430894249272373313174044285496732406419037277447693844114157449165389575217518238154883383890183796182675 / 119477202134466932562563268982823685174093386217657810644912885880702534757992106097239968629214788656866883802487322356532146500693429981738932845488692628293094673772423089947480045306671785936742290648714507660328355035302409567556734633117773482118945003847411648186767192584991507808814542399550639135669035611657879967313824450018392670208) := by
  show momentBQ (574 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_576, endpointB_at_575]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_577 : momentBQ 577 =
    (-312276471832826240157093741753447721642478781456624394461613450850199096263950564510516043184947641401854514237431097440197640348009345228858581539901177308470357833237156294409833293342228944797855427403583243436909532755640529887609922344165823772992981886320448416170552830425754155580765240767676781402436103161737773445343313464645988175 / 15293081873211767368008098429801431702283953435860199762548849392729924449022989580446715984539492948078961126718377261636114752088759037662583404222552656421516118242870155513277445799253988599903013203035456980522029444518708424647262033039075005711224960492468690967906200650878912999528261427142481809365636558292208635816169529602354261786624) := by
  show momentBQ (575 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_577, endpointB_at_576]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_578 : momentBQ 578 =
    (-622929322494944544923422698021175611110039995591983844064674318767034938994466377385795434498916352259158658383506400612941913415179820378537655723442383157797888849317100337722215113755468830957247135080631392020594232585341854247208008003699936157218235963873199526884413011819831946401145220318190598603473058473414518605875483185108375025 / 30586163746423534736016196859602863404567906871720399525097698785459848898045979160893431969078985896157922253436754523272229504177518075325166808445105312843032236485740311026554891598507977199806026406070913961044058889037416849294524066078150011422449920984937381935812401301757825999056522854284963618731273116584417271632339059204708523573248) := by
  show momentBQ (576 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_578, endpointB_at_577]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_579 : momentBQ 579 =
    (-2485250895628619585801752148160607195881924273071132775801278510513464652804912571369626768087372159705224682062916539469626388123537484070774799477955251837165971775995213458109737114740676685445349296705771608995657959068855217809795270686041613803711508880089270084767225614630679011074465186944199862248458257508120899489876927724671129425 / 122344654985694138944064787438411453618271627486881598100390795141839395592183916643573727876315943584631689013747018093088918016710072301300667233780421251372128945942961244106219566394031908799224105624283655844176235556149667397178096264312600045689799683939749527743249605207031303996226091417139854474925092466337669086529356236818834094292992) := by
  show momentBQ (577 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_579, endpointB_at_578]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_580 : momentBQ 580 =
    (-4957624843611495028671889000216755287121973290841378853282343142734113426579747875530084485562892650189178769918253200496404971127263893094550765797993637084502068050560399903483154348057826548686318545242083261468022353582949527755291084011015654478906377817794657941115968194988660203438699984318740657853142119899619410899495425772012356625 / 244689309971388277888129574876822907236543254973763196200781590283678791184367833287147455752631887169263378027494036186177836033420144602601334467560842502744257891885922488212439132788063817598448211248567311688352471112299334794356192528625200091379599367879499055486499210414062607992452182834279708949850184932675338173058712473637668188585984) := by
  show momentBQ (578 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_580, endpointB_at_579]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_581 : momentBQ 581 =
    (-39558427200403446539126728091384730118621538603472243677570144938919787824501850289574536205491495146681929908933923813616141735132719478002725765712266469701854432651712984057448341935882105633310831426517864369093116297210155886985322649660311118842032269897851167157732242769668136933645350909357123731973002984302480402832525569780815838725 / 1957514479771106223105036599014583257892346039790105569606252722269430329474942666297179646021055097354107024219952289489422688267361156820810675740486740021954063135087379905699513062304510540787585689988538493506819768898394678354849540229001600731036794943035992443891993683312500863939617462674237671598801479461402705384469699789101345508687872) := by
  show momentBQ (579 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_581, endpointB_at_580]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_582 : momentBQ 582 =
    (-78912594019393450152922337104844926346785478900902462000522888096743604283300592918445589435739488597253626100610013252979532308121896514638828162582645160730549548095241563722173198457293219327034859936891918767261483284796162948392407832971257464264914631345283137238918535920904252506187541659113436153798124713952796535082439131456050872775 / 3915028959542212446210073198029166515784692079580211139212505444538860658949885332594359292042110194708214048439904578978845376534722313641621351480973480043908126270174759811399026124609021081575171379977076987013639537796789356709699080458003201462073589886071984887783987366625001727879234925348475343197602958922805410768939399578202691017375744) := by
  show momentBQ (580 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_582, endpointB_at_581]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_583 : momentBQ 583 =
    (-314836844180466651641040664531700891713463714790198482414457295808657472759147726385963331047744145228218075267382217823743082507661587125414706174427666775285800774359365826396711626834767792572809183459558480030208185888825928464204761148039965347118783116810562619705788385581339646596851326000792781355874992415461157310071174679108161729525 / 15660115838168849784840292792116666063138768318320844556850021778155442635799541330377437168168440778832856193759618315915381506138889254566485405923893920175632505080699039245596104498436084326300685519908307948054558151187157426838796321832012805848294359544287939551135949466500006911516939701393901372790411835691221643075757598312810764069502976) := by
  show momentBQ (581 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_583, endpointB_at_582]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_584 : momentBQ 584 =
    (-628053601684189907132985064923444488958419039967411380871378790781249812725366733768225307047215164494712901433903120632955754642213423373683196022057249501985225215402988775470627138951689438700132213316409111964206038059527538257067130729280411146996817778474587181334188494736017168082569626310329339137019924835645499059370113467929317481025 / 31320231676337699569680585584233332126277536636641689113700043556310885271599082660754874336336881557665712387519236631830763012277778509132970811847787840351265010161398078491192208996872168652601371039816615896109116302374314853677592643664025611696588719088575879102271898933000013823033879402787802745580823671382443286151515196625621528139005952) := by
  show momentBQ (582 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_584, endpointB_at_583]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_585 : momentBQ 585 =
    (-10023047204960017011094898638846751090911755911808688475550086181645973038699345819725787434383639268990966166719138842977992522714775866169053744735571173559079279122527149635935350916146824603913068883748172814223288141634925781773742565748105191592483461807162932414442871183115890422139638556870324384857920718267493238413235372467639107745125 / 501123706821403193114889369347733314020440586186267025819200696900974164345585322572077989381390104922651398200307786109292208196444456146127532989564605445620240162582369255859075343949954698441621936637065854337745860837989037658841482298624409787145419505417214065636350382928000221168542070444604843929293178742119092578424243146009944450224095232) := by
  show momentBQ (583 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_585, endpointB_at_584]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_586 : momentBQ 586 =
    (-19994694167843315986235464464160954740331656665095281112764018075180941087456643712170929805001208593012747891557666717530456878646399035588522598472498392381958151685451595940404366699390332158575301516810457562732610703056339123640953118338527792458851623810186567739580907129395289098524714864731057362614005945672076255091018255845700579040275 / 1002247413642806386229778738695466628040881172372534051638401393801948328691170645144155978762780209845302796400615572218584416392888912292255065979129210891240480325164738511718150687899909396883243873274131708675491721675978075317682964597248819574290839010834428131272700765856000442337084140889209687858586357484238185156848486292019888900448190464) := by
  show momentBQ (584 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_586, endpointB_at_585]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_587 : momentBQ 587 =
    (-79774052840303195863171528868956164134633811063127589149560194982547850277258759384053982737359770802839256946180588371307522495350308780214958763188909968240645321912262510765640630278454942980800435061950255600117480927893721622990696912415491431346066717522553234428566827420693150021076422105360430228313218261060263283963823689705201286341575 / 4008989654571225544919114954781866512163524689490136206553605575207793314764682580576623915051120839381211185602462288874337665571555649169020263916516843564961921300658954046872602751599637587532975493096526834701966886703912301270731858388995278297163356043337712525090803063424001769348336563556838751434345429936952740627393945168079555601792761856) := by
  show momentBQ (585 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_587, endpointB_at_586]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_588 : momentBQ 588 =
    (-159140401833040958016650528629553097447455183568862703397163523551215558219199330900727791798037975485732146310012723991143285931950956697839381110211607449420435557000441908188356351032488480801562707764129044817270136569954937002593025697510290402225288119623355770895829224718282246464532351423129580574710014623000968152507048621200665598476975 / 8017979309142451089838229909563733024327049378980272413107211150415586629529365161153247830102241678762422371204924577748675331143111298338040527833033687129923842601317908093745205503199275175065950986193053669403933773407824602541463716777990556594326712086675425050181606126848003538696673127113677502868690859873905481254787890336159111203585523712) := by
  show momentBQ (586 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_588, endpointB_at_587]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_589 : momentBQ 589 =
    (-1269875451361612542541027687635821655141938301539292184250835463439291495177692620044582991694547926835127943004387246541571934681486205486840775797810990055579393934432097675543823127626591754967571810934172582113318844874538374857425980565847419332042605199443512375923861772752007313625145906253952367443094198318232215257760326752846127530704025 / 64143834473139608718705839276509864194616395031842179304857689203324693036234921289225982640817933430099378969639396621989402649144890386704324222664269497039390740810543264749961644025594201400527607889544429355231470187262596820331709734223924452754613696693403400401452849014784028309573385016909420022949526878991243850038303122689272889628684189696) := by
  show momentBQ (587 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_589, endpointB_at_588]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_590 : momentBQ 590 =
    (-2533282946264676973659944877711528768746651110880591369261004532327958415677060829460755543703045524671095641816901552947957594653219510096838559528740090518345989597551298418954146307234711905071132220454418988086841498688595229978736039329152322097028966229789689374720776881126669938046768149148376963914491821772364775768876712961959592272626875 / 128287668946279217437411678553019728389232790063684358609715378406649386072469842578451965281635866860198757939278793243978805298289780773408648445328538994078781481621086529499923288051188402801055215779088858710462940374525193640663419468447848905509227393386806800802905698029568056619146770033818840045899053757982487700076606245378545779257368379392) := by
  show momentBQ (588 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_590, endpointB_at_589]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_591 : momentBQ 591 =
    (-10107369585605168806772051257852438511236638500021884886848143506949176458481018970424777203181303669619930747181332636677105386124879197911793168018057920474892304258704671996979763402085613261927873299914749657553262521886361307406685824713261976637976587296482930149309675895207086498579817327280134530601209743139231664677857258156699796965701125 / 513150675785116869749646714212078913556931160254737434438861513626597544289879370313807861126543467440795031757115172975915221193159123093634593781314155976315125926484346117999693152204753611204220863116355434841851761498100774562653677873791395622036909573547227203211622792118272226476587080135275360183596215031929950800306424981514183117029473517568) := by
  show momentBQ (589 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_591, endpointB_at_590]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_592 : momentBQ 592 =
    (-20163432726613357061225462661604103222923852439129953099143758366654956082147413479070748430711940823150420221534333635604580795670444288219973172746684074856003429307974294897528157446800233563135300542469525966591026249245380679242779335595492166592511669073694373343546713841707538040314051825487781068661296594181309869128923362718695534048327625 / 1026301351570233739499293428424157827113862320509474868877723027253195088579758740627615722253086934881590063514230345951830442386318246187269187562628311952630251852968692235999386304409507222408441726232710869683703522996201549125307355747582791244073819147094454406423245584236544452953174160270550720367192430063859901600612849963028366234058947035136) := by
  show momentBQ (590 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_592, endpointB_at_591]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_593 : momentBQ 593 =
    (-643594974327847964575872200090660700169542425151688502975372395432959544135570143750879835045156813841639088692758054693216484315859316334805089649022537632565947297641017358756236593099218265893588917315040815312000054063751204923938443117250709425560980572325217700506180244515043308800294465024353228164567331830489917714628607874885930424623646625 / 32841643250247479663977389709573050467643594256303195804087136872102242834552279700083703112098781916210882032455371070458574156362183877992614002004105982484168059294998151551980361741104231117070135239446747829878512735878449572009835383922649319810362212707022541005543858695569422494501573128657623051750157762043516851219611198816907719489886305124352) := by
  show momentBQ (591 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_593, endpointB_at_592]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_594 : momentBQ 594 =
    (-1283933987571406647712068824126899845363522241069894602057108842828315582988835548157320143100203222216962971203259323275000170228771620951221620665756596997176248993438994157518765412540261734489233877206902672030516128090080397006777703554312966695512040500945586070318400049344513042682543595487031819424423530447672129268812214360860127643051895375 / 65683286500494959327954779419146100935287188512606391608174273744204485669104559400167406224197563832421764064910742140917148312724367755985228004008211964968336118589996303103960723482208462234140270478893495659757025471756899144019670767845298639620724425414045082011087717391138844989003146257315246103500315524087033702439222397633815438979772610248704) := by
  show momentBQ (592 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_594, endpointB_at_593]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_595 : momentBQ 595 =
    (-5122766920108137634810779651819448877965568537602104725379373665830148033137273146688297540652325987633337107326135683773990578185502932078106466292665210241258771236448512042625377151044478637608559409057843994465190612076583402198759524282359816613406626241146530280563313328192754059187926466842197663360073682089196879405866915884239903222277764375 / 262733146001979837311819117676584403741148754050425566432697094976817942676418237600669624896790255329687056259642968563668593250897471023940912016032847859873344474359985212415842893928833848936561081915573982639028101887027596576078683071381194558482897701656180328044350869564555379956012585029260984414001262096348134809756889590535261755919090440994816) := by
  show momentBQ (593 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_595, endpointB_at_594]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_596 : momentBQ 596 =
    (-10219704763308167012639320078503673643941394712829745057185405951832581034174694495998334757570270499698775035959870683428112296312927698112121639477972444632561615895234258478313147358470245618220773140422959363748203792495637812453659756845648911462375908148304086458871685580781174904632048262423006094804046152335927219923973158243013050629989422375 / 525466292003959674623638235353168807482297508100851132865394189953635885352836475201339249793580510659374112519285937127337186501794942047881824032065695719746688948719970424831685787857667697873122163831147965278056203774055193152157366142762389116965795403312360656088701739129110759912025170058521968828002524192696269619513779181070523511838180881989632) := by
  show momentBQ (594 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_596, endpointB_at_595]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_597 : momentBQ 597 =
    (-81551872238747722000188936733831328608364552439963536060358709239791535903581958092228322327188265933837875958095880822792117586013899550706796170062478098443729941606936465306807598719604845906473149422569789822124928250183311134277862086506554065293724528780762139594620363460059174238976546201482914407530274329714211171071168356717735014758774652375 / 4203730336031677396989105882825350459858380064806809062923153519629087082822691801610713998348644085274992900154287497018697492014359536383054592256525565757973511589759763398653486302861341582984977310649183722224449630192441545217258929142099112935726363226498885248709613913032886079296201360468175750624020193541570156956110233448564188094705447055917056) := by
  show momentBQ (595 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_597, endpointB_at_596]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_598 : momentBQ 598 =
    (-162693936074285656452638230569502700791561443812389566914383957629131858058904710364897708361275083295143903293286757219339048651495065937842201404597004045638998928733436063953781993425543335803366031762614103313485409624737560403559353006749256100108586120230967685522936101978108000868712004231099080501454868888927345904096752952848948748036349432125 / 8407460672063354793978211765650700919716760129613618125846307039258174165645383603221427996697288170549985800308574994037394984028719072766109184513051131515947023179519526797306972605722683165969954621298367444448899260384883090434517858284198225871452726452997770497419227826065772158592402720936351501248040387083140313912220466897128376189410894111834112) := by
  show momentBQ (596 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_598, endpointB_at_597]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_599 : momentBQ 599 =
    (-649143363667634742969891000232162949981046162100938974344013583450014403559442540017802562123749747060557446919368231982178879736567269778748315303291725172064634521668860281929304074102585951884333364189961957367853156128133476794134809822915928185383087763998476417487835350033052993432687026915388638923865078877894059075543231681434099854205233687375 / 33629842688253419175912847062602803678867040518454472503385228157032696662581534412885711986789152682199943201234299976149579936114876291064436738052204526063788092718078107189227890422890732663879818485193469777795597041539532361738071433136792903485810905811991081989676911304263088634369610883745406004992161548332561255648881867588513504757643576447336448) := by
  show momentBQ (597 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_599, endpointB_at_598]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_600 : momentBQ 600 =
    (-1295035591957969144990016269244465317574875064625412478031880187350195679889038122406133658994792901064050332334966673153094760075455571595332615671842423339928611441392801397171149196248063793826007295838071016785616897450950759213674620598304731521757579095122169146741174028863937107098599327485625080991684088913327880793446013120724122413648170711875 / 67259685376506838351825694125205607357734081036908945006770456314065393325163068825771423973578305364399886402468599952299159872229752582128873476104409052127576185436156214378455780845781465327759636970386939555591194083079064723476142866273585806971621811623982163979353822608526177268739221767490812009984323096665122511297763735177027009515287152894672896) := by
  show momentBQ (598 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_600, endpointB_at_599]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_601 : momentBQ 601 =
    (-20668768047649187554040659657141666468495006031421583149388807790109123051029048433601893197556894700982243304066068103523392370804270922661508546122605076505260638604629110298851541172119098149463076441575613427898445683317174117050246944748943515087250962358149819581989137500668436229293645266670576292627278059056712977463398369406756993721824804561525 / 1076154966024109413629211106003289717723745296590543120108327301025046293202609101212342783577252885830398182439497599236786557955676041314061975617670544834041218966978499430055292493532503445244154191526191032889459105329265035575618285860377372911545948985983714623669661161736418836299827548279852992159749169546641960180764219762832432152244594446314766336) := by
  show momentBQ (599 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_601, endpointB_at_600]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_602 : momentBQ 602 =
    (-41234364208205284321621881745279297996215494561854373038464526689419032509457286309298951653695036183823144295466249011854488273867422356524373954743766200881543270693760903907359397446540430417980413732860500000083587977200152689423038413900138560049274382474911204124467513915643020031485991139331149708585867542111478968350440340962897895960845159183475 / 2152309932048218827258422212006579435447490593181086240216654602050092586405218202424685567154505771660796364878995198473573115911352082628123951235341089668082437933956998860110584987065006890488308383052382065778918210658530071151236571720754745823091897971967429247339322323472837672599655096559705984319498339093283920361528439525664864304489188892629532672) := by
  show momentBQ (600 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_602, endpointB_at_601]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_603 : momentBQ 603 =
    (-164526483103171250731786976664719059446693717504276086442511284232532418750359471287269238990324712480968758467956694562249968162507555648457718005472635240062237435558826729543982180509285903428553079379287244186380030433944795282382289485362346879133483499509529422436828851204941086570812874944640235215985471488624206780693949666101130807471677861060975 / 8609239728192875309033688848026317741789962372724344960866618408200370345620872809698742268618023086643185459515980793894292463645408330512495804941364358672329751735827995440442339948260027561953233532209528263115672842634120284604946286883018983292367591887869716989357289293891350690398620386238823937277993356373135681446113758102659457217956755570518130688) := by
  show momentBQ (601 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_603, endpointB_at_602]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_604 : momentBQ 604 =
    (-328234426489411301211177003196777825065294431438879157529587188941519900094000736249726193209553282113773493261943455320707647926196665746425596617883217568482374187358654321130034101414047996392287486721861616511136279621949566707638298923533836311107098921907071136304320245438713312014407775387068329958259572472329885169444148338838574396995735434255975 / 17218479456385750618067377696052635483579924745448689921733236816400740691241745619397484537236046173286370919031961587788584927290816661024991609882728717344659503471655990880884679896520055123906467064419056526231345685268240569209892573766037966584735183775739433978714578587782701380797240772477647874555986712746271362892227516205318914435913511141036261376) := by
  show momentBQ (602 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_604, endpointB_at_603]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_605 : momentBQ 605 =
    (-2619354198143977602380584694384882643732978740952644932603659355460473374922323756165033528592792747994020260798952739479819309609715114069157906785094550794842787389186612297759543656979654540746400142383067866860392165195027999223206292734160746721086451661576296153951694673865228748194446154578922765560945594895082858471392044690731669856820272836281125 / 137747835651086004944539021568421083868639397963589519373865894531205925529933964955179876297888369386290967352255692702308679418326533288199932879061829738757276027773247927047077439172160440991251736515352452209850765482145924553679140590128303732677881470205915471829716628702261611046377926179821182996447893701970170903137820129642551315487308089128290091008) := by
  show momentBQ (603 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_605, endpointB_at_604]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_606 : momentBQ 606 =
    (-5225719863074018125741100373756286530554884860049326336615895606678993989307842601142471849605786523683937941792290837276267614378390318481774534693568798032025197320245026518009535857808996744927115655960930438513212137835369909194066107983689291392316276290119982574908587555959224957141647121614478971953820385187380182107388756928451447135838131096514575 / 275495671302172009889078043136842167737278795927179038747731789062411851059867929910359752595776738772581934704511385404617358836653066576399865758123659477514552055546495854094154878344320881982503473030704904419701530964291849107358281180256607465355762940411830943659433257404523222092755852359642365992895787403940341806275640259285102630974616178256580182016) := by
  show momentBQ (604 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_606, endpointB_at_605]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_607 : momentBQ 607 =
    (-20851139651671577273996667827958252196174441570295826867883227024669649284069906616439763914763682861827990005369239677448869788064270280674803341401071540662437173465928175116414286640564610774313144647052029373473509817303505677279293480370562222090133260840775772056318423614371957007208750396144901244528610051787269439497798703387781516789532344870251225 / 1101982685208688039556312172547368670949115183708716154990927156249647404239471719641439010383106955090327738818045541618469435346612266305599463032494637910058208222185983416376619513377283527930013892122819617678806123857167396429433124721026429861423051761647323774637733029618092888371023409438569463971583149615761367225102561037140410523898464713026320728064) := by
  show momentBQ (605 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_607, endpointB_at_606]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_608 : momentBQ 608 =
    (-41599225894850543787166334002730549274410623956553947836913653915774209691941774155697782703095255264701311196873392503114631488213890131626337473536569416379260983636308105545268041386694800078572023340329501764870544297783435543962478426241764169606509685137033706688964762762775024605815151119821211543861856297717270661007964134765409253430187264642296925 / 2203965370417376079112624345094737341898230367417432309981854312499294808478943439282878020766213910180655477636091083236938870693224532611198926064989275820116416444371966832753239026754567055860027784245639235357612247714334792858866249442052859722846103523294647549275466059236185776742046818877138927943166299231522734450205122074280821047796929426052641456128) := by
  show momentBQ (606 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_608, endpointB_at_607]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_609 : momentBQ 609 =
    (-2655782158444932084938566481332218751045267729436838880325066431570216650332914318466390022044976033478036341147759216119897262905444669982249860810518879056212819639517985896126849168529515394489887595358930823199366854379542490254025596370066312512247170951116941379669171433223479202465988332018059452773917457322686805884350552393181127600569323790058219475 / 141053783706712069063207958086063189881486743514715667838838675999954867742652380114104193329037690251561950568709829327164087724366370087116731268159313652487450652439805877296207297712292291575041778191720911062887183853717426742967439964291383022262150625490857443153629827791115889711490996408136891388362643150817455004813127812753972547059003483267369053192192) := by
  show momentBQ (607 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_609, endpointB_at_608]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_610 : momentBQ 610 =
    (-5298481646158608346798617856845066966371100642472511066658383767418412528989311817629989945459188638219727675688879224278612765895098972132074845459409586294414738689678740334637309917509624309203962936553531937910066876964111864792514120836831805751034996232523947087517312465298074270929681155011399400854367340963981065926906274479006683143992985886569354125 / 282107567413424138126415916172126379762973487029431335677677351999909735485304760228208386658075380503123901137419658654328175448732740174233462536318627304974901304879611754592414595424584583150083556383441822125774367707434853485934879928582766044524301250981714886307259655582231779422981992816273782776725286301634910009626255625507945094118006966534738106384384) := by
  show momentBQ (608 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_610, endpointB_at_609]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_611 : momentBQ 611 =
    (-21141810371721397895258747317312939337946326170128019567617223098190846058295057318215402503684696959716093709224150871957612249489624423228639629259349070558369629460127957335257725146259714046889255389461142191595250456607620129352425196912866582291834722672070962641011702525468053730234170379176633019146770668698901499124737495216233224217178569914606242525 / 1128430269653696552505663664688505519051893948117725342710709407999638941941219040912833546632301522012495604549678634617312701794930960696933850145274509219899605219518447018369658381698338332600334225533767288503097470829739413943739519714331064178097205003926859545229038622328927117691927971265095131106901145206539640038505022502031780376472027866138952425537536) := by
  show momentBQ (609 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_611, endpointB_at_610]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_612 : momentBQ 612 =
    (-42179814800537453411326371489041690757703063177391253441776423824377481743145130721611416779037063165129162408419377926213304962566042834559266297982236525385683434225689001623042826437464143082091656824473211671938805739123877148413430957507012052068324921337568745432722201928879799504346078056000516612667616113165238833769320796511601146187791614936014745725 / 2256860539307393105011327329377011038103787896235450685421418815999277883882438081825667093264603044024991209099357269234625403589861921393867700290549018439799210439036894036739316763396676665200668451067534577006194941659478827887479039428662128356194410007853719090458077244657854235383855942530190262213802290413079280077010045004063560752944055732277904851075072) := by
  show momentBQ (610 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_612, endpointB_at_611]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_613 : momentBQ 613 =
    (-336611463212132226243330062667450355654610719866632159819666754833757550381569964778349933903295778592305276475033074822917943524791753601286693789779809133960257994703047522756439810981331494792378516226678375499590077173008196066750321562850076572388396921262558419433685023236354478397428505270435495320700387412906905987139481650592581696047670338803098068825 / 18054884314459144840090618635016088304830303169883605483371350527994223071059504654605336746116824352199929672794858153877003228718895371150941602324392147518393683512295152293914534107173413321605347608540276616049559533275830623099832315429297026849555280062829752723664617957262833883070847540241522097710418323304634240616080360032508486023552445858223238808600576) := by
  show momentBQ (611 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_613, endpointB_at_612]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_614 : momentBQ 614 =
    (-671575562003976692814996193543706011363114046324455353114930572857561964301239913415859656058288315201287688628002366245397463182414868930462685978630842693039796945386341142465131955677273112775006403499555714903749860330487803898263692122945585070197405276841939554596079581432400533572683624707573590174904688101117693347914496017413910953126102486714826979075 / 36109768628918289680181237270032176609660606339767210966742701055988446142119009309210673492233648704399859345589716307754006457437790742301883204648784295036787367024590304587829068214346826643210695217080553232099119066551661246199664630858594053699110560125659505447329235914525667766141695080483044195420836646609268481232160720065016972047104891716446477617201152) := by
  show momentBQ (612 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_614, endpointB_at_613]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_615 : momentBQ 615 =
    (-2679739620374174099994691651762344833615031618069895138650781601793203277749247211512795044532257935249437845502615305050853069701818288077579121575969974915223945466118136480520477673305080010258576040022657168589881364510904103502843722640418051175869125290330214835114649795617884865233020978067679635062730432976772554889886832642775377581692102756435384525625 / 144439074515673158720724949080128706438642425359068843866970804223953784568476037236842693968934594817599437382358865231016025829751162969207532818595137180147149468098361218351316272857387306572842780868322212928396476266206644984798658523434376214796442240502638021789316943658102671064566780321932176781683346586437073924928642880260067888188419566865785910468804608) := by
  show momentBQ (613 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_615, endpointB_at_614]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_616 : momentBQ 616 =
    (-5346407340161157106818677490589263594870965520929693227844730122602049466338741997603576454700943880570829652734486145199019051258749657676731027924740096294276066808011306441623782284789159630223207806679350155869568185780291601622746744194785282589904742652414916427131179348330316633562466244047224247515398766280487682682749827077537216736156439157961328151125 / 288878149031346317441449898160257412877284850718137687733941608447907569136952074473685387937869189635198874764717730462032051659502325938415065637190274360294298936196722436702632545714774613145685561736644425856792952532413289969597317046868752429592884481005276043578633887316205342129133560643864353563366693172874147849857285760520135776376839133731571820937609216) := by
  show momentBQ (614 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_616, endpointB_at_615]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_617 : momentBQ 617 =
    (-85334215857896910185456553713431233222031384743150558143132121047765179144549531364347993023733247132747397963775110031812914467493549730970161471681890627865782936455141501516306862701375028383692498628687290150177912991220498420705918813186897562376531541815817302453821031416856612242185337843299202599953572516347004701520773214003808303490081347079668471399125 / 4622050384501541079063198370564118606036557611490203003743065735166521106191233191578966207005907034163181996235483687392512826552037215014641050195044389764708782979147558987242120731436393810330968987786310813708687240518612639513557072749900038873486151696084416697258142197059285474066136970301829657013867090765986365597716572168322172422029426139705149135001747456) := by
  show momentBQ (615 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_617, endpointB_at_616]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_618 : momentBQ 618 =
    (-170253516565755423724954647684333627384636360808457596554612059983466670221945661441673224330981567618171875029833323256339866628013873126133336744960141593035297884564471942247283222018464602820624741996619212601084296421705726994957838021123291570965170709846468556435419270136386531069902999813778473906876576608789566916648414629560272320253306544983909057199875 / 9244100769003082158126396741128237212073115222980406007486131470333042212382466383157932414011814068326363992470967374785025653104074430029282100390088779529417565958295117974484241462872787620661937975572621627417374481037225279027114145499800077746972303392168833394516284394118570948132273940603659314027734181531972731195433144336644344844058852279410298270003494912) := by
  show momentBQ (616 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_618, endpointB_at_617]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_619 : momentBQ 619 =
    (-679361119500247370397634565031661367525102371769670603727626763623347587002132687888618400000324507680278064439431998624812477515667008299425256331831244609102013888893184157899353439316397589895890960782626178437336367274961687329394868220210415880259079240261151230048129320641309361842040125470514104618701679477791378667402897211157979841010766893091132257370375 / 36976403076012328632505586964512948848292460891921624029944525881332168849529865532631729656047256273305455969883869499140102612416297720117128401560355118117670263833180471897936965851491150482647751902290486509669497924148901116108456581999200310987889213568675333578065137576474283792529095762414637256110936726127890924781732577346577379376235409117641193080013979648) := by
  show momentBQ (617 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_619, endpointB_at_618]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_620 : momentBQ 620 =
    (-1355429697225857031407235359958161209844105701349827456548657597859182988606839853865014093700162789959843957322614730697323763702502027867189324022312741667594486514996902156713572693951132509727666133386984378626995821622904174235545496368271185156898162943008920467058868676885326432754312689751348819392724675533234818504430659217738457356459284512063890691199375 / 73952806152024657265011173929025897696584921783843248059889051762664337699059731065263459312094512546610911939767738998280205224832595440234256803120710236235340527666360943795873931702982300965295503804580973019338995848297802232216913163998400621975778427137350667156130275152948567585058191524829274512221873452255781849563465154693154758752470818235282386160027959296) := by
  show momentBQ (618 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_620, endpointB_at_619]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_621 : momentBQ 621 =
    (-10817203454634742889359678324311260752110701629482171379036706119689092625204263866006596347787750781808561130374673689500577391612871022398149637520005557695576643993878503018417351112371296222794341980643223718461895686113112667931417929080977135736019532648400223340334326150368701918174740627241409610250325313771686906386972422273177237096387967364019566354926625 / 591622449216197258120089391432207181572679374270745984479112414101314701592477848522107674496756100372887295518141911986241641798660763521874054424965681889882724221330887550366991453623858407722364030436647784154711966786382417857735305311987204975806227417098805337249042201223588540680465532198634196097774987618046254796507721237545238070019766545882259089280223674368) := by
  show momentBQ (619 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_621, endpointB_at_620]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_622 : momentBQ 622 =
    (-21582149887749511175389116656717636186578356391189066567836519939283068860914787326863402375054787791724327279443189535090523974570607402176018358916726064387793014345274501191335101494731136908280498734326818336834603470360944598336597124205041338449159743883040059128299887440107603343991149174157981492914900263708727982308307296612667627636754736818068023693645875 / 1183244898432394516240178782864414363145358748541491968958224828202629403184955697044215348993512200745774591036283823972483283597321527043748108849931363779765448442661775100733982907247716815444728060873295568309423933572764835715470610623974409951612454834197610674498084402447177081360931064397268392195549975236092509593015442475090476140039533091764518178560447348736) := by
  show momentBQ (620 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_622, endpointB_at_621]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_623 : momentBQ 623 =
    (-86120411609958660349382295083558155972809454281239973024711000786656876065579585442564251921038558358617010140800637340988232322965028251126812808410472816415598491326320437229732671880904633129183597843407014649555443429961196934198447045461274279792306244883770782566624309688660886655604553457009823256293862467082094617506782492271127092917082406402644428951172125 / 4732979593729578064960715131457657452581434994165967875832899312810517612739822788176861395974048802983098364145135295889933134389286108174992435399725455119061793770647100402935931628990867261778912243493182273237695734291059342861882442495897639806449819336790442697992337609788708325443724257589073568782199900944370038372061769900361904560158132367058072714241789394944) := by
  show momentBQ (621 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_623, endpointB_at_622]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_624 : momentBQ 624 =
    (-171826118188087664228382331924338343297274721784239625152031739932286511957488643186368162340049643723532814775305284454010229177280144648716899391419290065496932463432770952610847048391596242342817354926733417671584937694128038184925633511249380304625741031124441545313505645173363534691679710990470642548271703124531370159808877428399696591486249488215870024376094625 / 9465959187459156129921430262915314905162869988331935751665798625621035225479645576353722791948097605966196728290270591779866268778572216349984870799450910238123587541294200805871863257981734523557824486986364546475391468582118685723764884991795279612899638673580885395984675219577416650887448515178147137564399801888740076744123539800723809120316264734116145428483578789888) := by
  show momentBQ (622 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_624, endpointB_at_623]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_625 : momentBQ 625 =
    (-5485218388312029281136820596046185574489923810804572649084090159376838650950598994026368259316969395789701394750130234493403469890096925324424095956846567475478997871123072717961655775577880044020707868814951410285211472543318142057241377474499448186129425224357172408084987903611220530542083081618870512117904368975424508947744933291221083497445656739198927701236866875 / 302910693998692996157485768413290076965211839626621944053305556019873127215348658443319129342339123390918295305288658936955720600914310923199515865582429127619954801321414425787899624255415504753850383583563665487212526994627797943160476319737448947612788437554588332671509607026477332828398352485700708402060793660439682455811953273623161891850120471491716653711474521276416) := by
  show momentBQ (623 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_625, endpointB_at_624]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_626 : momentBQ 626 =
    (-10944107728360160821724184453231349458222295987317283349452576685988668476376635112881409950989217338479612222805459843861238603124721385407290956253100271427075696552464754686877095603432986263830116339859591053801053930018428357032607996337121299020965429207637430388611167865285107202537564164445970445777642796979766980252540690902644305794103574326049700549507796789 / 605821387997385992314971536826580153930423679253243888106611112039746254430697316886638258684678246781836590610577317873911441201828621846399031731164858255239909602642828851575799248510831009507700767167127330974425053989255595886320952639474897895225576875109176665343019214052954665656796704971401416804121587320879364911623906547246323783700240942983433307422949042552832) := by
  show momentBQ (624 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_626, endpointB_at_625]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_627 : momentBQ 627 =
    (-43671535312210354205538359048197940809327947885492929404045585561660852801899096664501217344362723500833979764485684808251396215024846678510244103386972009624337204453765107360733202583667092151833275745957281872835515522661396223430438937460269975965449907604917413914937216178086577942394305563555965133470529883155683572956624034943778715453148128860179156505863380797 / 2423285551989543969259886147306320615721694717012975552426444448158985017722789267546553034738712987127346362442309271495645764807314487385596126924659433020959638410571315406303196994043324038030803068668509323897700215957022383545283810557899591580902307500436706661372076856211818662627186819885605667216486349283517459646495626188985295134800963771933733229691796170211328) := by
  show momentBQ (625 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_627, endpointB_at_626]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_628 : momentBQ 628 =
    (-87134115910008218678035864703820771854017963005983500294196216168481223054506810091373242261240457894008466802825505095889149385958665382482161679963480038341380929460383013250840887451622858503897014287388452349150286951912929307035851851296328133864079480723686897619755115532354559818078590526329365840465124216631196411114412548189261838966329041792797647191124544461 / 4846571103979087938519772294612641231443389434025951104852888896317970035445578535093106069477425974254692724884618542991291529614628974771192253849318866041919276821142630812606393988086648076061606137337018647795400431914044767090567621115799183161804615000873413322744153712423637325254373639771211334432972698567034919292991252377970590269601927543867466459383592340422656) := by
  show momentBQ (626 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_628, endpointB_at_627]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_629 : momentBQ 629 =
    (-695407944173505082825343557158518644159773934054123094704636043688579442594248618117774984416141998351545279642932215828975185863733807160828971878944206930202231239578725577091105936158493259269955152242660705690989232807305098227489951399199357654341984645520889698837918215044842442369760980442615894255431851232094835051760247916440414549202613308066085681085853848469 / 38772568831832703508158178356901129851547115472207608838823111170543760283564628280744848555819407794037541799076948343930332236917031798169538030794550928335354214569141046500851151904693184608492849098696149182363203455312358136724540968926393465294436920006987306581953229699389098602034989118169690675463781588536279354343930019023764722156815420350939731675068738723381248) := by
  show momentBQ (627 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_629, endpointB_at_628]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_630 : momentBQ 630 =
    (-1387499157293718408498896922470494274118467865243123185777930421032062321869287783366943728843017818650539468921907680231103113289325799661113449456399013827351033713308903973369376708869489730339894620134402520893786148129042763554053877592997128547216519443765845106584399618253222997097058871948303572798993598245276658171636106733120381970189633865855226597397053386055 / 77545137663665407016316356713802259703094230944415217677646222341087520567129256561489697111638815588075083598153896687860664473834063596339076061589101856670708429138282093001702303809386369216985698197392298364726406910624716273449081937852786930588873840013974613163906459398778197204069978236339381350927563177072558708687860038047529444313630840701879463350137477446762496) := by
  show momentBQ (628 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_630, endpointB_at_629]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_631 : momentBQ 631 =
    (-5536782351486362030105122004906067627196552719398748712770979489642229646316491249816661165573566342995962261697898266826973375887881048171490812592677969463429363103585054903254941343012535209642055674631568154804727581581608742182367378204436160583654491875598943806274889905220004150320644450917516161931222072997818283561100273535023238528661491331365142326755860654829 / 310180550654661628065265426855209038812376923777660870710584889364350082268517026245958788446555262352300334392615586751442657895336254385356304246356407426682833716553128372006809215237545476867942792789569193458905627642498865093796327751411147722355495360055898452655625837595112788816279912945357525403710252708290234834751440152190117777254523362807517853400549909787049984) := by
  show momentBQ (629 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_631, endpointB_at_630]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_632 : momentBQ 632 =
    (-11047240856610665286691519182530489924945261289576901155909133403263973256279655282914701121168177536976095859711020472163485705614646972500644901829130845569663340962620577057366039858720731900062358311190403022027182290350626634560381187257345683319843114534673645407448631363980959152541507707932096430858016782732572454839025743867819742167329346412343445625016844000681 / 620361101309323256130530853710418077624753847555321741421169778728700164537034052491917576893110524704600668785231173502885315790672508770712608492712814853365667433106256744013618430475090953735885585579138386917811255284997730187592655502822295444710990720111796905311251675190225577632559825890715050807420505416580469669502880304380235554509046725615035706801099819574099968) := by
  show momentBQ (630 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_632, endpointB_at_631]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_633 : momentBQ 633 =
    (-176336338230203150968582350495834782219695879571600915919005281285011016154033484958929596377127492077555150368298693865799436389621137118016623053247265775485385733593222122396690838757554973746564985195077192541471859090280255521273932621917884894510407182635740086820161065189620120143732167338004729105214672949693340070278626114143299935101295010455254239660078990947579 / 9925777620949172098088493659366689241996061560885147862738716459659202632592544839870681230289768395273610700563698776046165052650760140331401735883405037653850678929700107904217894887601455259774169369266214190684980084559963683001482488045156727115375851521788750484980026803043609242120957214251440812918728086665287514712046084870083768872144747609840571308817597113185599488) := by
  show momentBQ (631 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_633, endpointB_at_632]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_634 : momentBQ 634 =
    (-351836959217609130605560045302115845092378982462767704274413381142130984838142640605257630686116939168960750260918247002377074502514211974810418509085776736868944994515386320042686460269813478423241036811030796492699775720417002722541827648471230050184272151135765765645913784098720713651712049522748772290499418539435526870081998076086868590889313741240104430790963294734269 / 19851555241898344196176987318733378483992123121770295725477432919318405265185089679741362460579536790547221401127397552092330105301520280662803471766810075307701357859400215808435789775202910519548338738532428381369960169119927366002964976090313454230751703043577500969960053606087218484241914428502881625837456173330575029424092169740167537744289495219681142617635194226371198976) := by
  show momentBQ (632 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_634, endpointB_at_633]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_635 : momentBQ 635 =
    (-1404018149559228865034805859013175217797663762824609293082438255977273488391957225128236286491917754096956937161077547186141953456405293842697726858023683192868187438681273485343843445556195741972870383488813746256357149168225578687745779101943552093006638079453450137356722198375021144383014961029265605512560771143173317005216806202681037121372182595169501908361415040501105 / 79406220967593376784707949274933513935968492487081182901909731677273621060740358718965449842318147162188885604509590208369320421206081122651213887067240301230805431437600863233743159100811642078193354954129713525479840676479709464011859904361253816923006812174310003879840214424348873936967657714011526503349824693322300117696368678960670150977157980878724570470540776905484795904) := by
  show momentBQ (633 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_635, endpointB_at_634]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_636 : momentBQ 636 =
    (-2801403142506366885037951217905028347952188956690992085567636646178276393374188668090512401551590227465896754933992523283215519731126783147555936896245679693486603913085312607764802591369606307212010670677680340955597650387624894799014019090019654333605370782153576888237743346993939826666582607282014995566007081950237153772613690486294289815399299760755525854951043868212441 / 158812441935186753569415898549867027871936984974162365803819463354547242121480717437930899684636294324377771209019180416738640842412162245302427774134480602461610862875201726467486318201623284156386709908259427050959681352959418928023719808722507633846013624348620007759680428848697747873935315428023053006699649386644600235392737357921340301954315961757449140941081553810969591808) := by
  show momentBQ (634 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_636, endpointB_at_635]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_637 : momentBQ 637 =
    (-22358368476984777214548176701392962097807092993967729286700194364781338007495883143439372563326842758831591081831676176392455940495596778705965307681357028497072329344058249680839839549987612602843028560314316683475807662527647745282696793869402146851227770582093641957067272373178048050565366846797968738196622559716043698977652661805707256451205732052822404464986633136865331 / 1270499535481494028555327188398936222975495879793298926430555706836377936971845739503447197477090354595022169672153443333909126739297297962419422193075844819692886903001613811739890545612986273251093679266075416407677450823675351424189758469780061070768108994788960062077443430789581982991482523424184424053597195093156801883141898863370722415634527694059593127528652430487756734464) := by
  show momentBQ (635 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_637, endpointB_at_636]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_638 : momentBQ 638 =
    (-44611438515302436169059234831193806634713995597069048545362554219210487609932915973801322649903323620839799474109984961059358713296551814341101893348516143202164726210828940885945739510257858113364975353468597338614994566833030273554643053387771002586986650564899558755781009711631552703718337931366119727233763380532325810675975719238703175744870463797703730102037693433211673 / 2540999070962988057110654376797872445950991759586597852861111413672755873943691479006894394954180709190044339344306886667818253478594595924838844386151689639385773806003227623479781091225972546502187358532150832815354901647350702848379516939560122141536217989577920124154886861579163965982965046848368848107194390186313603766283797726741444831269055388119186255057304860975513468928) := by
  show momentBQ (636 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_638, endpointB_at_637]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_639 : momentBQ 639 =
    (-178026210752288405151136068777773403905927637602096861436509503200799218581331040860968914524535833759652240534614454092252550601963982632151168370635301098107698108045094801717269361744696719054274650861960891573846044149148738364373230742829568922549322903351464383373383151607858829441484151055263543613694610606324924003105069249501157187220125706628454070281799322070465391 / 10163996283851952228442617507191489783803967038346391411444445654691023495774765916027577579816722836760177357377227546671273013914378383699355377544606758557543095224012910493919124364903890186008749434128603331261419606589402811393518067758240488566144871958311680496619547446316655863931860187393475392428777560745254415065135190906965779325076221552476745020229219443902053875712) := by
  show momentBQ (637 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_639, endpointB_at_638]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_640 : momentBQ 640 =
    (-355216617698228038447102484650486838779433079722493737608058867888918628624721560403341730858815630741090151301460765207546169041477430134573927500093910641764186365817677421266852012870873735202191204771518210886782012973653585938303394674659937991002170112320997009078346664006291091608595137082098619886479856843606069020280067751352074199852363499141281595632698177840130475 / 20327992567703904456885235014382979567607934076692782822888891309382046991549531832055155159633445673520354714754455093342546027828756767398710755089213517115086190448025820987838248729807780372017498868257206662522839213178805622787036135516480977132289743916623360993239094892633311727863720374786950784857555121490508830130270381813931558650152443104953490040458438887804107751424) := by
  show momentBQ (638 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_640, endpointB_at_639]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_641 : momentBQ 641 =
    (-90722324160127441019389974579734338624267208561124900585098234858829817750753886527013478061341512091274424642393079434007291573193335656370181083523984777906573197829834813391554004087221151970639633698645751060484126113471125848642686999908148162901954246686782636118609737987206744796835198010767987519006955437856990027779529303695319750642293637680683319524591114620369323315 / 5203966097332199540962620163682042769307631123633352402659556175201804029836680149006119720866162092421210806977140503895691783124161732454069953302838660381462064754694610172886591674830791775236479710273844905605846838573774239433481250692219130145866174442655580414269208292514127802333112415945459400923534111101570260513349217744366479014439025434868093450357360355277851584364544) := by
  show momentBQ (639 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_641, endpointB_at_640]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_642 : momentBQ 642 =
    (-181020050859287046901403709028830295008483244539280417860125807152017686276465243163884927364205606809266753693636113254438885993938028556158286436547857302562413603782150899107328504255157337551401078784037309838313880341855803370380650035698161467007175478178463325422311786093038107012717969197772630322636343221558643128751978127030130984510910394061769057210533596879020849485 / 10407932194664399081925240327364085538615262247266704805319112350403608059673360298012239441732324184842421613954281007791383566248323464908139906605677320762924129509389220345773183349661583550472959420547689811211693677147548478866962501384438260291732348885311160828538416585028255604666224831890918801847068222203140521026698435488732958028878050869736186900714720710555703168729088) := by
  show momentBQ (640 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_642, endpointB_at_641]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_643 : momentBQ 643 =
    (-722388427260893168475695175283276037089928461853016246974520744429079925607950082532512747518839197266886951655912339809770133826276057882986806620616215590599538400139985363727376367448151244247180005988634871971589036504415215319182594067692663050580036721329007850049786286558198800882528718200457132222109519211266734728757894020952018040992137740788555022699979867919083203085 / 41631728778657596327700961309456342154461048989066819221276449401614432238693441192048957766929296739369686455817124031165534264993293859632559626422709283051696518037556881383092733398646334201891837682190759244846774708590193915467850005537753041166929395541244643314153666340113022418664899327563675207388272888812562084106793741954931832115512203478944747602858882842222812674916352) := by
  show momentBQ (641 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_643, endpointB_at_642]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_644 : momentBQ 644 =
    (-1441406457505017006460835007602555451922827708487433662314634704669532728701399620356475668843966858621175674921517157038779287245897639601667298435848529708770152048801868151885262642979748128101293853317913749206141110163553221235631832331025951312432639367752903688357505140986266036597642838959854588866199864926991011908236979827187308159553519006892248979975231991508839423885 / 83263457557315192655401922618912684308922097978133638442552898803228864477386882384097915533858593478739372911634248062331068529986587719265119252845418566103393036075113762766185466797292668403783675364381518489693549417180387830935700011075506082333858791082489286628307332680226044837329798655127350414776545777625124168213587483909863664231024406957889495205717765684445625349832704) := by
  show momentBQ (642 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_644, endpointB_at_643]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_645 : momentBQ 645 =
    (-11504393154620787908709148973722259352303314319294113391765873263977326437150922435764417605369549151106899020336332588787772572117878676323866326025250687427140654550996276864425854013844573569007221127413162532483797059379912355824763382269368617617862991227096156767325429230853117124397335702257224513621533083423499691317295149552395596180287403253767328815330267758315892296225 / 666107660458521541243215380951301474471376783825069107540423190425830915819095059072783324270868747829914983293073984498648548239892701754120954022763348528827144288600910102129483734378341347230269402915052147917548395337443102647485600088604048658670870328659914293026458661441808358698638389241018803318212366221000993345708699871278909313848195255663115961645742125475565002798661632) := by
  show momentBQ (643 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_645, endpointB_at_644]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_646 : momentBQ 646 =
    (-22955277503871246571331278649892322149479636478963603000314230838354758332733701046246210012574588771278417114996682235302113643900325358804365831929453697238341120011057687324831122660182893307460920296094170820630460178948755351854992981365391334688666154588019773270616786697841801145890497750085345657412268338552006360814509856548733538424852539515656670054775278457290780442235 / 1332215320917043082486430761902602948942753567650138215080846380851661831638190118145566648541737495659829966586147968997297096479785403508241908045526697057654288577201820204258967468756682694460538805830104295835096790674886205294971200177208097317341740657319828586052917322883616717397276778482037606636424732442001986691417399742557818627696390511326231923291484250951130005597323264) := by
  show momentBQ (644 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_646, endpointB_at_645]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_647 : momentBQ 647 =
    (-91607903103684324552464452568765335141421831025956917236548122447799639290692695506536732836559272217268977279352084833759828133088295317333831446925900358328859763759298324958846182999924920970022062729614198723816294646021503555854755272383868205615141403293986030172832935150210779185922141176037184372769083245800421669008988251056710622382770660791583429413638804741324507709105 / 5328861283668172329945723047610411795771014270600552860323385523406647326552760472582266594166949982639319866344591875989188385919141614032967632182106788230617154308807280817035869875026730777842155223320417183340387162699544821179884800708832389269366962629279314344211669291534466869589107113928150426545698929768007946765669598970231274510785562045304927693165937003804520022389293056) := by
  show momentBQ (645 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_647, endpointB_at_646]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_648 : momentBQ 648 =
    (-182791040041509216379028760844321557446020995138346800853761400432935601737688206953537746664602813651459427616141486121149827078542487256071060893325096387330074119031304694778779632539262863944819911876247187870860643567254653926751915079826234703939949847994646004564338978792769885516268136411536329250764894080878430254544982738970963544816316728101907584811449299723415671487565 / 10657722567336344659891446095220823591542028541201105720646771046813294653105520945164533188333899965278639732689183751978376771838283228065935264364213576461234308617614561634071739750053461555684310446640834366680774325399089642359769601417664778538733925258558628688423338583068933739178214227856300853091397859536015893531339197940462549021571124090609855386331874007609040044778586112) := by
  show momentBQ (646 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_648, endpointB_at_647]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_649 : momentBQ 649 =
    (-2917886602144091565161533182366762639230927737208424858073006058762786827738652488776843289349770840139963455650258537711687980401918963235801009074930242331083775751944160127764963763867492383711754889580093998975590273240250216386299088866855820644374754980951571406193707402210511876204132103458228070632580346254022349618847687425795751400586389252293413668656838821510820533745945 / 170523561077381514558263137523533177464672456659217691530348336749012714449688335122632531013342399444458235723026940031654028349412531649054964229827417223379748937881832986145147836000855384890948967146253349866892389206385434277756313622682636456619742804136938059014773417329102939826851427645700813649462365752576254296501427167047400784345137985449757686181309984121744640716457377792) := by
  show momentBQ (647 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_649, endpointB_at_648]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_650 : momentBQ 650 =
    (-5822285284709705049128174840007638856400695561918197521116398838363341975225816599331297472585444126319341564047896465849978327612457715547553631359067278611330492448024171595463217371661637345002654209562745344643126970487094037319348721236638347818898779199279329693406550209341468227556781315837296381308461553773434426435142920210177963118273303669830463329600317833369048676734975 / 341047122154763029116526275047066354929344913318435383060696673498025428899376670245265062026684798888916471446053880063308056698825063298109928459654834446759497875763665972290295672001710769781897934292506699733784778412770868555512627245365272913239485608273876118029546834658205879653702855291401627298924731505152508593002854334094801568690275970899515372362619968243489281432914755584) := by
  show momentBQ (648 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_650, endpointB_at_649]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_651 : momentBQ 651 =
    (-23235396966979961380674593130738177220774468134793545184270674748791552436516566551792900990594833944111341564831143742176682741271869714046698645762185416488909688323345694028663978249369672727595207722470402190775802094528495281240600896750522883449574512681431663422610140373895028588126601128126072020175614262289675234111939592346464055890462999568523418272281883784245095796077731 / 1364188488619052116466105100188265419717379653273741532242786693992101715597506680981060248106739195555665885784215520253232226795300253192439713838619337787037991503054663889161182688006843079127591737170026798935139113651083474222050508981461091652957942433095504472118187338632823518614811421165606509195698926020610034372011417336379206274761103883598061489450479872973957125731659022336) := by
  show momentBQ (649 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_651, endpointB_at_650]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_652 : momentBQ 652 =
    (-46363718371900107271115662790827791412881772821961313662623051457266093110652872428231917644827479713365027177750623227476975239496403622959541537396434494652985691447044633706965449686530268622344354579860295615695494501985430676392535429921550269740395225765253042681982445999523259809487641882389811911225995279131010951015990062147552701385117413885578986690774450131696435390330219 / 2728376977238104232932210200376530839434759306547483064485573387984203431195013361962120496213478391111331771568431040506464453590600506384879427677238675574075983006109327778322365376013686158255183474340053597870278227302166948444101017962922183305915884866191008944236374677265647037229622842331213018391397852041220068744022834672758412549522207767196122978900959745947914251463318044672) := by
  show momentBQ (650 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_652, endpointB_at_651]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_653 : momentBQ 653 =
    (-370056427005165886869456915894889304467234272646451957515782760404314031515088263982390950036322399429987118762291784165322360653894608058100389816888105997199597451365675266581362270197398033605337455879743831877422321147748744233047169290355441110013829378653952199566007130339753135043824675392571443536840612626683713173446644606466049475472624266657289948985874598903908358544905613 / 21827015817904833863457681603012246715478074452379864515884587103873627449560106895696963969707827128890654172547448324051715628724804051079035421417909404592607864048874622226578923008109489266041467794720428782962225818417335587552808143703377466447327078929528071553890997418125176297836982738649704147131182816329760549952182677382067300396177662137568983831207677967583314011706544357376) := by
  show momentBQ (651 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_653, endpointB_at_652]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_654 : momentBQ 654 =
    (-738412747913830245927874979189955227750086152003563400678506794497429070542358358298706597086260469306697114467482687239532979987786637518690364366623586698853101805711293832091140946504149521880175658516548564986648215092674753040827659395609708677408912221111944434968617596987286883556054444160062160686835096864577148950996903403101473915070182878184454523014693112361091257555914263 / 43654031635809667726915363206024493430956148904759729031769174207747254899120213791393927939415654257781308345094896648103431257449608102158070842835818809185215728097749244453157846016218978532082935589440857565924451636834671175105616287406754932894654157859056143107781994836250352595673965477299408294262365632659521099904365354764134600792355324275137967662415355935166628023413088714752) := by
  show momentBQ (652 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_654, endpointB_at_653]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_655 : momentBQ 655 =
    (-2946876562775377586959868036216793798819151157078441094450921611067721520054365925320526327821314716957919677003256595864191250409974195602112922013589543247716507206279016669354553318617477449705288178483473630910018106103793739199633319606332323620852080882419227790929804171463025636209942047794743485309846487487073943061317917250909551862894766532204015756985243154835547679236905545 / 174616126543238670907661452824097973723824595619038916127076696830989019596480855165575711757662617031125233380379586592413725029798432408632283371343275236740862912390996977812631384064875914128331742357763430263697806547338684700422465149627019731578616631436224572431127979345001410382695861909197633177049462530638084399617461419056538403169421297100551870649661423740666512093652354859008) := by
  show momentBQ (653 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_655, endpointB_at_654]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_656 : momentBQ 656 =
    (-5880255980988425200239003852420380908483405438628278641904358084985514544597032464723554061774745549716032088310315069915264067611963776567880288659177913014909122013139961506635727003714569506511162823325038222289150633095661705547970608741185262553364381241712871332435502369621640467979227872469816389770945586481840677223118347857921808068402228790214730678442309623465741704981122973 / 349232253086477341815322905648195947447649191238077832254153393661978039192961710331151423515325234062250466760759173184827450059596864817264566742686550473481725824781993955625262768129751828256663484715526860527395613094677369400844930299254039463157233262872449144862255958690002820765391723818395266354098925061276168799234922838113076806338842594201103741299322847481333024187304709718016) := by
  show momentBQ (654 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_656, endpointB_at_655]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_657 : momentBQ 657 =
    (-187737928758874355783240391288250697785482383394254066884214749591366793631158914544466640655198583526299658624346400646806845475708794720179397508655216783817464407687809990541126015801521255707880783798353049584792638505420028599080329922980768504447657927936637770101416404922798228599629494757633894005126043236700718206952729691366332847842402865521733718489780080417479411995616828577 / 11175432098767274938090332980742270318324774119618490632132908597183297254174774730596845552490407489992014936344293541914478401907099674152466135765969615151415226393023806580008408580152058504213231510896859536876659619029675820827037769576129262821031464411918372635592190678080090264492535162188648523331165601960837401575517530819618457802842963014435319721578331119402656773993750710976512) := by
  show momentBQ (655 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_657, endpointB_at_656]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_658 : momentBQ 658 =
    (-374618606701498143731854114123130387818519641750178206522382856490535565373591076054483661946674799091292012871412680742715029556551339236157062608595112943051287425386177926330922689065136021663670787762010423144083940761956860720539288476450209298829344815106441577782278397037729798621178489539205532786484387645836592951773255137566609381311096128917797420000154772339901840374815315471 / 22350864197534549876180665961484540636649548239236981264265817194366594508349549461193691104980814979984029872688587083828956803814199348304932271531939230302830452786047613160016817160304117008426463021793719073753319238059351641654075539152258525642062928823836745271184381356160180528985070324377297046662331203921674803151035061639236915605685926028870639443156662238805313547987501421953024) := by
  show momentBQ (656 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_658, endpointB_at_657]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_659 : momentBQ 659 =
    (-1495058451668896847173022649980760483907952248078978678309692068608125219864817881032027501933082100932724659271017780593266972060036195796578186033694174146584621244778272392925536446025907587976898918940789317897210377569754887921179592004799771457030181587339689336255718952311669378691815674057680439357610945224873697707228826734422365099274982423310237119939827404505444122833229511287 / 89403456790138199504722663845938162546598192956947925057063268777466378033398197844774764419923259919936119490754348335315827215256797393219729086127756921211321811144190452640067268641216468033705852087174876295013276952237406566616302156609034102568251715295346981084737525424640722115940281297509188186649324815686699212604140246556947662422743704115482557772626648955221254191950005687812096) := by
  show momentBQ (657 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_659, endpointB_at_658]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_660 : momentBQ 660 =
    (-2983310870932624209457548990477541785036353878943637271589142746919096607165759504639023012203342887293676672141712263247566112684290739715478474407143913509497385336697159630799818553147296628512324853425095528125692938549662636747118609235677844409703624866998014381147603068725106575083061625775189344089921688878162234423377704333483171632088925472917999715813160905803731443893318372295 / 178806913580276399009445327691876325093196385913895850114126537554932756066796395689549528839846519839872238981508696670631654430513594786439458172255513842422643622288380905280134537282432936067411704174349752590026553904474813133232604313218068205136503430590693962169475050849281444231880562595018376373298649631373398425208280493113895324845487408230965115545253297910442508383900011375624192) := by
  show momentBQ (658 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_660, endpointB_at_659]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_661 : momentBQ 661 =
    (-23812244951625855053670254669448015338744715506477395676866066652681516555377607682482383679223045954944073801276576064830573153970975177001728186631566873284897312051091874144020369906030240362125647466429398851766894545878216318763364899172046794470179842120220514787705413584914941572026619158460147673735920389409331289306596585498165679027037059683836397731672320684506147343075759371591 / 1430455308642211192075562621535010600745571087311166800913012300439462048534371165516396230718772158718977911852069573365053235444108758291515665378044110739381148978307047242241076298259463488539293633394798020720212431235798505065860834505744545641092027444725551697355800406794251553855044500760147010986389197050987187401666243944911162598763899265847720924362026383283540067071200091004993536) := by
  show momentBQ (659 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_661, endpointB_at_660]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_662 : momentBQ 662 =
    (-47516416174273075364283004400910638777313585102940521781825025589844054972077253454151685435544928312513212320550384008338163373808950466664568045638482157129772397269879246589958952959234322295981435715915850356248916650549723637592856735261618338738528308255023992443242723931169149672470666671723048081176518901105760923744933277264872209737763815012072932841264434164695322761750267187789 / 2860910617284422384151125243070021201491142174622333601826024600878924097068742331032792461437544317437955823704139146730106470888217516583031330756088221478762297956614094484482152596518926977078587266789596041440424862471597010131721669011489091282184054889451103394711600813588503107710089001520294021972778394101974374803332487889822325197527798531695441848724052766567080134142400182009987072) := by
  show momentBQ (660 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_662, endpointB_at_661]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_663 : momentBQ 663 =
    (-189635002314848134610930056838679618806136694625330602035621929922006032078894416353276061813760877041782336783827967598231763796983756998380345583952975618031508570373143458445123192927941207712965186044485916376449603913523217296858500747071292524089413580679415994010645432970013434191340636475366001556598735553959849487211652142800290601400561932419783517472236608856684354586924782341599 / 11443642469137689536604500972280084805964568698489334407304098403515696388274969324131169845750177269751823294816556586920425883552870066332125323024352885915049191826456377937928610386075707908314349067158384165761699449886388040526886676045956365128736219557804413578846403254354012430840356006081176087891113576407897499213329951559289300790111194126781767394896211066268320536569600728039948288) := by
  show momentBQ (661 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_663, endpointB_at_662]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_664 : momentBQ 664 =
    (-378411927696144920196471289890758877346182272985388214921761407672419276682318722225315580361396139255321314577683862944887818255519623693600599106440100667655634749025141471376920036566615713128586638215467371592824775230152664379704067101621900466621861489048065399813097900179981558725706880930481478219276209861069201917920084140158045951211076073290156249797540020388225341053546737613779 / 22887284938275379073209001944560169611929137396978668814608196807031392776549938648262339691500354539503646589633113173840851767105740132664250646048705771830098383652912755875857220772151415816628698134316768331523398899772776081053773352091912730257472439115608827157692806508708024861680712012162352175782227152815794998426659903118578601580222388253563534789792422132536641073139201456079896576) := by
  show momentBQ (662 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_664, endpointB_at_663]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []

theorem momentB_at_665 : momentBQ 665 =
    (-6040913303583036376630415169942837499803512189224570900859444158625970380771955505404134264805420295340972792957001426529835652874259052940009564048591968489683325812750752404511072872900793010787678260668605630849311170842798557868769745899385760461132126180586586201835599008897295967609176111239613959524590097179719187243904957659149528739212961410957313626286030445956609360192161775159725 / 366196559012406065171344031112962713790866198351658701033731148912502284424799018372197435064005672632058345434129810781453628273691842122628010336779292349281574138446604094013715532354422653066059170149068293304374382396364417296860373633470603684119559025849741234523084904139328397786891392194597634812515634445052719974826558449897257625283558212057016556636678754120586257170227223297278345216) := by
  show momentBQ (663 + 1 + 1) = _
  rw [momentBQ_step]
  rw [endpointB_at_665, endpointB_at_664]
  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num
    []


end C1ConcreteClassMomentCertificate
end Source
end ConnesWeilRH
