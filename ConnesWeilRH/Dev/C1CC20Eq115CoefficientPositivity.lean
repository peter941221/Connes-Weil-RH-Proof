/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20Eq115Table
import Mathlib.Tactic.IntervalCases

/-!
# Positivity of every extracted equation-(115) coefficient

The published equation-(115) coefficient table `cc20Eq115CoefficientQ` is a
machine-transcribed 1732-branch rational `ite` chain.  This leaf is generated
from that chain: for each branch index it records the branch value as a
definitional equation (kernel `rfl` descends the ite chain and never inspects
the subtype bound proof), and the quantified positivity then follows from a
single `interval_cases` sweep that rewrites the matching branch equation and
closes the resulting rational literal comparison with `norm_num`.

Three routes were rejected by measurement (companion record docs/proofs/1047):
`norm_num [cc20Eq115CoefficientQ]` per case blows the whnf heartbeat budget
(measured failure after 1613 s); kernel `decide` cannot evaluate ANY
comparison of rational division literals in this toolchain
(`Rat.instDecidableLt` is stuck at the externalized `Rat.blt`); and per-case
`simp only [cc20Eq115CoefficientQ]` rebuilds the whole 1732-node chain in
every goal, which is quadratic in the chain length (measured > 45 min and
killed for the full sweep).  Case GENERATION itself (`interval_cases` on the
decomposed `ℕ`) was measured at 0.3 s for all 1732 cases, so the assembly
sweep is cheap; only the per-case chain rebuild had to go.

This feeds the (gamma) Bessel-coercivity brick, whose perturbed summands
only lower the defect form when the coefficients `d_n` are nonnegative.

Reference: equation (115) of <https://arxiv.org/html/2006.13771>; companion
records docs/proofs/1046, docs/proofs/1047.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20Eq115CoefficientPositivity

open C1CC20Eq115Table

-- The machine-generated ite chain nests far deeper than the defaults sized
-- for hand-written proofs.
set_option maxRecDepth 30000
-- The assembly sweep rewrites through 1732 branch equations per goal.
set_option maxHeartbeats 20000000

/-- Branch 0 of the coefficient chain is the literal 11711069251401751/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_0 : ∀ (p : 0 < 1732), cc20Eq115CoefficientQ ⟨0, p⟩ = (11711069251401751 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1 of the coefficient chain is the literal 5622132307574491/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1 : ∀ (p : 1 < 1732), cc20Eq115CoefficientQ ⟨1, p⟩ = (5622132307574491 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 2 of the coefficient chain is the literal 5295208362794117/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_2 : ∀ (p : 2 < 1732), cc20Eq115CoefficientQ ⟨2, p⟩ = (5295208362794117 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 3 of the coefficient chain is the literal 10324772632349877/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_3 : ∀ (p : 3 < 1732), cc20Eq115CoefficientQ ⟨3, p⟩ = (10324772632349877 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 4 of the coefficient chain is the literal 10205222761838721/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_4 : ∀ (p : 4 < 1732), cc20Eq115CoefficientQ ⟨4, p⟩ = (10205222761838721 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 5 of the coefficient chain is the literal 253534857793871/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_5 : ∀ (p : 5 < 1732), cc20Eq115CoefficientQ ⟨5, p⟩ = (253534857793871 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 6 of the coefficient chain is the literal 101032896319221/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_6 : ∀ (p : 6 < 1732), cc20Eq115CoefficientQ ⟨6, p⟩ = (101032896319221 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 7 of the coefficient chain is the literal 5039355298099669/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_7 : ∀ (p : 7 < 1732), cc20Eq115CoefficientQ ⟨7, p⟩ = (5039355298099669 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 8 of the coefficient chain is the literal 5030963976844801/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_8 : ∀ (p : 8 < 1732), cc20Eq115CoefficientQ ⟨8, p⟩ = (5030963976844801 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 9 of the coefficient chain is the literal 10049957439156967/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_9 : ∀ (p : 9 < 1732), cc20Eq115CoefficientQ ⟨9, p⟩ = (10049957439156967 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 10 of the coefficient chain is the literal 627569922803619/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_10 : ∀ (p : 10 < 1732), cc20Eq115CoefficientQ ⟨10, p⟩ = (627569922803619 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 11 of the coefficient chain is the literal 5017203259452633/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_11 : ∀ (p : 11 < 1732), cc20Eq115CoefficientQ ⟨11, p⟩ = (5017203259452633 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 12 of the coefficient chain is the literal 1002918894401601/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_12 : ∀ (p : 12 < 1732), cc20Eq115CoefficientQ ⟨12, p⟩ = (1002918894401601 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 13 of the coefficient chain is the literal 1253131595715953/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_13 : ∀ (p : 13 < 1732), cc20Eq115CoefficientQ ⟨13, p⟩ = (1253131595715953 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 14 of the coefficient chain is the literal 5010859179065419/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_14 : ∀ (p : 14 < 1732), cc20Eq115CoefficientQ ⟨14, p⟩ = (5010859179065419 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 15 of the coefficient chain is the literal 2504747753744867/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_15 : ∀ (p : 15 < 1732), cc20Eq115CoefficientQ ⟨15, p⟩ = (2504747753744867 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 16 of the coefficient chain is the literal 5008365883323993/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_16 : ∀ (p : 16 < 1732), cc20Eq115CoefficientQ ⟨16, p⟩ = (5008365883323993 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 17 of the coefficient chain is the literal 10014839266273063/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_17 : ∀ (p : 17 < 1732), cc20Eq115CoefficientQ ⟨17, p⟩ = (10014839266273063 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 18 of the coefficient chain is the literal 5006619096239957/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_18 : ∀ (p : 18 < 1732), cc20Eq115CoefficientQ ⟨18, p⟩ = (5006619096239957 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 19 of the coefficient chain is the literal 1251483952464407/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_19 : ∀ (p : 19 < 1732), cc20Eq115CoefficientQ ⟨19, p⟩ = (1251483952464407 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 20 of the coefficient chain is the literal 500534793851289/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_20 : ∀ (p : 20 < 1732), cc20Eq115CoefficientQ ⟨20, p⟩ = (500534793851289 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 21 of the coefficient chain is the literal 5004838504406467/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_21 : ∀ (p : 21 < 1732), cc20Eq115CoefficientQ ⟨21, p⟩ = (5004838504406467 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 22 of the coefficient chain is the literal 50043941456589/ 50000000000000. -/
theorem cc20Eq115CoefficientQ_branch_22 : ∀ (p : 22 < 1732), cc20Eq115CoefficientQ ⟨22, p⟩ = (50043941456589 : ℚ) /  50000000000000 :=
  fun p => by rfl

/-- Branch 23 of the coefficient chain is the literal 1000800845962133/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_23 : ∀ (p : 23 < 1732), cc20Eq115CoefficientQ ⟨23, p⟩ = (1000800845962133 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 24 of the coefficient chain is the literal 1250915052737383/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_24 : ∀ (p : 24 < 1732), cc20Eq115CoefficientQ ⟨24, p⟩ = (1250915052737383 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 25 of the coefficient chain is the literal 100067103137077/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_25 : ∀ (p : 25 < 1732), cc20Eq115CoefficientQ ⟨25, p⟩ = (100067103137077 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 26 of the coefficient chain is the literal 10006166793221927/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_26 : ∀ (p : 26 < 1732), cc20Eq115CoefficientQ ⟨26, p⟩ = (10006166793221927 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 27 of the coefficient chain is the literal 2501420127431777/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_27 : ∀ (p : 27 < 1732), cc20Eq115CoefficientQ ⟨27, p⟩ = (2501420127431777 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 28 of the coefficient chain is the literal 5002621849180121/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_28 : ∀ (p : 28 < 1732), cc20Eq115CoefficientQ ⟨28, p⟩ = (5002621849180121 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 29 of the coefficient chain is the literal 500242493396017/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_29 : ∀ (p : 29 < 1732), cc20Eq115CoefficientQ ⟨29, p⟩ = (500242493396017 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 30 of the coefficient chain is the literal 2000898711618087/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_30 : ∀ (p : 30 < 1732), cc20Eq115CoefficientQ ⟨30, p⟩ = (2000898711618087 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 31 of the coefficient chain is the literal 1000417014909133/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_31 : ∀ (p : 31 < 1732), cc20Eq115CoefficientQ ⟨31, p⟩ = (1000417014909133 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 32 of the coefficient chain is the literal 62524223193143/ 62500000000000. -/
theorem cc20Eq115CoefficientQ_branch_32 : ∀ (p : 32 < 1732), cc20Eq115CoefficientQ ⟨32, p⟩ = (62524223193143 : ℚ) /  62500000000000 :=
  fun p => by rfl

/-- Branch 33 of the coefficient chain is the literal 500180344168953/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_33 : ∀ (p : 33 < 1732), cc20Eq115CoefficientQ ⟨33, p⟩ = (500180344168953 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 34 of the coefficient chain is the literal 1250420097477451/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_34 : ∀ (p : 34 < 1732), cc20Eq115CoefficientQ ⟨34, p⟩ = (1250420097477451 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 35 of the coefficient chain is the literal 1250391863639691/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_35 : ∀ (p : 35 < 1732), cc20Eq115CoefficientQ ⟨35, p⟩ = (1250391863639691 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 36 of the coefficient chain is the literal 10002927112442217/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_36 : ∀ (p : 36 < 1732), cc20Eq115CoefficientQ ⟨36, p⟩ = (10002927112442217 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 37 of the coefficient chain is the literal 10002735511425191/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_37 : ∀ (p : 37 < 1732), cc20Eq115CoefficientQ ⟨37, p⟩ = (10002735511425191 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 38 of the coefficient chain is the literal 10002558465548843/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_38 : ∀ (p : 38 < 1732), cc20Eq115CoefficientQ ⟨38, p⟩ = (10002558465548843 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 39 of the coefficient chain is the literal 10002394536891361/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_39 : ∀ (p : 39 < 1732), cc20Eq115CoefficientQ ⟨39, p⟩ = (10002394536891361 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 40 of the coefficient chain is the literal 10002242460828317/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_40 : ∀ (p : 40 < 1732), cc20Eq115CoefficientQ ⟨40, p⟩ = (10002242460828317 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 41 of the coefficient chain is the literal 10002101121556803/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_41 : ∀ (p : 41 < 1732), cc20Eq115CoefficientQ ⟨41, p⟩ = (10002101121556803 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 42 of the coefficient chain is the literal 1000196953156289/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_42 : ∀ (p : 42 < 1732), cc20Eq115CoefficientQ ⟨42, p⟩ = (1000196953156289 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 43 of the coefficient chain is the literal 625115425894881/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_43 : ∀ (p : 43 < 1732), cc20Eq115CoefficientQ ⟨43, p⟩ = (625115425894881 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 44 of the coefficient chain is the literal 10001732189639299/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_44 : ∀ (p : 44 < 1732), cc20Eq115CoefficientQ ⟨44, p⟩ = (10001732189639299 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 45 of the coefficient chain is the literal 1250203120157117/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_45 : ∀ (p : 45 < 1732), cc20Eq115CoefficientQ ⟨45, p⟩ = (1250203120157117 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 46 of the coefficient chain is the literal 5000762253101173/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_46 : ∀ (p : 46 < 1732), cc20Eq115CoefficientQ ⟨46, p⟩ = (5000762253101173 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 47 of the coefficient chain is the literal 2000286053151053/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_47 : ∀ (p : 47 < 1732), cc20Eq115CoefficientQ ⟨47, p⟩ = (2000286053151053 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 48 of the coefficient chain is the literal 10001341737636449/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_48 : ∀ (p : 48 < 1732), cc20Eq115CoefficientQ ⟨48, p⟩ = (10001341737636449 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 49 of the coefficient chain is the literal 1250157308660613/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_49 : ∀ (p : 49 < 1732), cc20Eq115CoefficientQ ⟨49, p⟩ = (1250157308660613 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 50 of the coefficient chain is the literal 125014750652103/ 125000000000000. -/
theorem cc20Eq115CoefficientQ_branch_50 : ∀ (p : 50 < 1732), cc20Eq115CoefficientQ ⟨50, p⟩ = (125014750652103 : ℚ) /  125000000000000 :=
  fun p => by rfl

/-- Branch 51 of the coefficient chain is the literal 10001106116565077/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_51 : ∀ (p : 51 < 1732), cc20Eq115CoefficientQ ⟨51, p⟩ = (10001106116565077 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 52 of the coefficient chain is the literal 5000518163684101/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_52 : ∀ (p : 52 < 1732), cc20Eq115CoefficientQ ⟨52, p⟩ = (5000518163684101 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 53 of the coefficient chain is the literal 1000097038021409/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_53 : ∀ (p : 53 < 1732), cc20Eq115CoefficientQ ⟨53, p⟩ = (1000097038021409 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 54 of the coefficient chain is the literal 10000907998162287/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_54 : ∀ (p : 54 < 1732), cc20Eq115CoefficientQ ⟨54, p⟩ = (10000907998162287 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 55 of the coefficient chain is the literal 781316322561/ 781250000000. -/
theorem cc20Eq115CoefficientQ_branch_55 : ∀ (p : 55 < 1732), cc20Eq115CoefficientQ ⟨55, p⟩ = (781316322561 : ℚ) /  781250000000 :=
  fun p => by rfl

/-- Branch 56 of the coefficient chain is the literal 5000396470792199/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_56 : ∀ (p : 56 < 1732), cc20Eq115CoefficientQ ⟨56, p⟩ = (5000396470792199 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 57 of the coefficient chain is the literal 2000147965163423/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_57 : ∀ (p : 57 < 1732), cc20Eq115CoefficientQ ⟨57, p⟩ = (2000147965163423 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 58 of the coefficient chain is the literal 1250086173551189/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_58 : ∀ (p : 58 < 1732), cc20Eq115CoefficientQ ⟨58, p⟩ = (1250086173551189 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 59 of the coefficient chain is the literal 5000320726130437/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_59 : ∀ (p : 59 < 1732), cc20Eq115CoefficientQ ⟨59, p⟩ = (5000320726130437 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 60 of the coefficient chain is the literal 2500148963667141/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_60 : ∀ (p : 60 < 1732), cc20Eq115CoefficientQ ⟨60, p⟩ = (2500148963667141 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 61 of the coefficient chain is the literal 10000552445949253/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_61 : ∀ (p : 61 < 1732), cc20Eq115CoefficientQ ⟨61, p⟩ = (10000552445949253 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 62 of the coefficient chain is the literal 5000255544102997/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_62 : ∀ (p : 62 < 1732), cc20Eq115CoefficientQ ⟨62, p⟩ = (5000255544102997 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 63 of the coefficient chain is the literal 40001886616943/ 40000000000000. -/
theorem cc20Eq115CoefficientQ_branch_63 : ∀ (p : 63 < 1732), cc20Eq115CoefficientQ ⟨63, p⟩ = (40001886616943 : ℚ) /  40000000000000 :=
  fun p => by rfl

/-- Branch 64 of the coefficient chain is the literal 5000217013271979/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_64 : ∀ (p : 64 < 1732), cc20Eq115CoefficientQ ⟨64, p⟩ = (5000217013271979 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 65 of the coefficient chain is the literal 10000398096472227/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_65 : ∀ (p : 65 < 1732), cc20Eq115CoefficientQ ⟨65, p⟩ = (10000398096472227 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 66 of the coefficient chain is the literal 5000181881706033/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_66 : ∀ (p : 66 < 1732), cc20Eq115CoefficientQ ⟨66, p⟩ = (5000181881706033 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 67 of the coefficient chain is the literal 62502068338107/ 62500000000000. -/
theorem cc20Eq115CoefficientQ_branch_67 : ∀ (p : 67 < 1732), cc20Eq115CoefficientQ ⟨67, p⟩ = (62502068338107 : ℚ) /  62500000000000 :=
  fun p => by rfl

/-- Branch 68 of the coefficient chain is the literal 10000299521968743/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_68 : ∀ (p : 68 < 1732), cc20Eq115CoefficientQ ⟨68, p⟩ = (10000299521968743 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 69 of the coefficient chain is the literal 2000053889324823/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_69 : ∀ (p : 69 < 1732), cc20Eq115CoefficientQ ⟨69, p⟩ = (2000053889324823 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 70 of the coefficient chain is the literal 10000240633265953/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_70 : ∀ (p : 70 < 1732), cc20Eq115CoefficientQ ⟨70, p⟩ = (10000240633265953 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 71 of the coefficient chain is the literal 10000213012273123/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_71 : ∀ (p : 71 < 1732), cc20Eq115CoefficientQ ⟨71, p⟩ = (10000213012273123 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 72 of the coefficient chain is the literal 10000186518707739/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_72 : ∀ (p : 72 < 1732), cc20Eq115CoefficientQ ⟨72, p⟩ = (10000186518707739 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 73 of the coefficient chain is the literal 10000161092084943/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_73 : ∀ (p : 73 < 1732), cc20Eq115CoefficientQ ⟨73, p⟩ = (10000161092084943 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 74 of the coefficient chain is the literal 10000136675848021/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_74 : ∀ (p : 74 < 1732), cc20Eq115CoefficientQ ⟨74, p⟩ = (10000136675848021 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 75 of the coefficient chain is the literal 2000022643433653/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_75 : ∀ (p : 75 < 1732), cc20Eq115CoefficientQ ⟨75, p⟩ = (2000022643433653 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 76 of the coefficient chain is the literal 1000009066661823/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_76 : ∀ (p : 76 < 1732), cc20Eq115CoefficientQ ⟨76, p⟩ = (1000009066661823 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 77 of the coefficient chain is the literal 2000013795583869/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_77 : ∀ (p : 77 < 1732), cc20Eq115CoefficientQ ⟨77, p⟩ = (2000013795583869 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 78 of the coefficient chain is the literal 312501503366061/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_78 : ∀ (p : 78 < 1732), cc20Eq115CoefficientQ ⟨78, p⟩ = (312501503366061 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 79 of the coefficient chain is the literal 10000028015307587/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_79 : ∀ (p : 79 < 1732), cc20Eq115CoefficientQ ⟨79, p⟩ = (10000028015307587 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 80 of the coefficient chain is the literal 5000004331273551/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_80 : ∀ (p : 80 < 1732), cc20Eq115CoefficientQ ⟨80, p⟩ = (5000004331273551 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 81 of the coefficient chain is the literal 9999990013557537/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_81 : ∀ (p : 81 < 1732), cc20Eq115CoefficientQ ⟨81, p⟩ = (9999990013557537 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 82 of the coefficient chain is the literal 199999440692541/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_82 : ∀ (p : 82 < 1732), cc20Eq115CoefficientQ ⟨82, p⟩ = (199999440692541 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 83 of the coefficient chain is the literal 9999954694031823/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_83 : ∀ (p : 83 < 1732), cc20Eq115CoefficientQ ⟨83, p⟩ = (9999954694031823 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 84 of the coefficient chain is the literal 9999937961906407/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_84 : ∀ (p : 84 < 1732), cc20Eq115CoefficientQ ⟨84, p⟩ = (9999937961906407 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 85 of the coefficient chain is the literal 1249990226264391/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_85 : ∀ (p : 85 < 1732), cc20Eq115CoefficientQ ⟨85, p⟩ = (1249990226264391 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 86 of the coefficient chain is the literal 9999906212124677/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_86 : ∀ (p : 86 < 1732), cc20Eq115CoefficientQ ⟨86, p⟩ = (9999906212124677 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 87 of the coefficient chain is the literal 9999891142904191/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_87 : ∀ (p : 87 < 1732), cc20Eq115CoefficientQ ⟨87, p⟩ = (9999891142904191 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 88 of the coefficient chain is the literal 499993828941051/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_88 : ∀ (p : 88 < 1732), cc20Eq115CoefficientQ ⟨88, p⟩ = (499993828941051 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 89 of the coefficient chain is the literal 4999931248772337/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_89 : ∀ (p : 89 < 1732), cc20Eq115CoefficientQ ⟨89, p⟩ = (4999931248772337 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 90 of the coefficient chain is the literal 2499962219492403/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_90 : ∀ (p : 90 < 1732), cc20Eq115CoefficientQ ⟨90, p⟩ = (2499962219492403 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 91 of the coefficient chain is the literal 9999835700130131/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_91 : ∀ (p : 91 < 1732), cc20Eq115CoefficientQ ⟨91, p⟩ = (9999835700130131 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 92 of the coefficient chain is the literal 4999911472565017/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_92 : ∀ (p : 92 < 1732), cc20Eq115CoefficientQ ⟨92, p⟩ = (4999911472565017 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 93 of the coefficient chain is the literal 9999810595062919/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_93 : ∀ (p : 93 < 1732), cc20Eq115CoefficientQ ⟨93, p⟩ = (9999810595062919 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 94 of the coefficient chain is the literal 4999899316485971/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_94 : ∀ (p : 94 < 1732), cc20Eq115CoefficientQ ⟨94, p⟩ = (4999899316485971 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 95 of the coefficient chain is the literal 1999957408555187/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_95 : ∀ (p : 95 < 1732), cc20Eq115CoefficientQ ⟨95, p⟩ = (1999957408555187 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 96 of the coefficient chain is the literal 4999887904607519/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_96 : ∀ (p : 96 < 1732), cc20Eq115CoefficientQ ⟨96, p⟩ = (4999887904607519 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 97 of the coefficient chain is the literal 9999764917807649/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_97 : ∀ (p : 97 < 1732), cc20Eq115CoefficientQ ⟨97, p⟩ = (9999764917807649 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 98 of the coefficient chain is the literal 4999877177397797/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_98 : ∀ (p : 98 < 1732), cc20Eq115CoefficientQ ⟨98, p⟩ = (4999877177397797 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 99 of the coefficient chain is the literal 9999744107110987/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_99 : ∀ (p : 99 < 1732), cc20Eq115CoefficientQ ⟨99, p⟩ = (9999744107110987 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 100 of the coefficient chain is the literal 9999734162327519/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_100 : ∀ (p : 100 < 1732), cc20Eq115CoefficientQ ⟨100, p⟩ = (9999734162327519 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 101 of the coefficient chain is the literal 4999862254309441/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_101 : ∀ (p : 101 < 1732), cc20Eq115CoefficientQ ⟨101, p⟩ = (4999862254309441 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 102 of the coefficient chain is the literal 9999715134724831/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_102 : ∀ (p : 102 < 1732), cc20Eq115CoefficientQ ⟨102, p⟩ = (9999715134724831 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 103 of the coefficient chain is the literal 1999941205992847/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_103 : ∀ (p : 103 < 1732), cc20Eq115CoefficientQ ⟨103, p⟩ = (1999941205992847 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 104 of the coefficient chain is the literal 9999697184112483/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_104 : ∀ (p : 104 < 1732), cc20Eq115CoefficientQ ⟨104, p⟩ = (9999697184112483 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 105 of the coefficient chain is the literal 9999688587449317/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_105 : ∀ (p : 105 < 1732), cc20Eq115CoefficientQ ⟨105, p⟩ = (9999688587449317 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 106 of the coefficient chain is the literal 9999680230701629/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_106 : ∀ (p : 106 < 1732), cc20Eq115CoefficientQ ⟨106, p⟩ = (9999680230701629 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 107 of the coefficient chain is the literal 9999672105023153/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_107 : ∀ (p : 107 < 1732), cc20Eq115CoefficientQ ⟨107, p⟩ = (9999672105023153 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 108 of the coefficient chain is the literal 9999664201975021/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_108 : ∀ (p : 108 < 1732), cc20Eq115CoefficientQ ⟨108, p⟩ = (9999664201975021 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 109 of the coefficient chain is the literal 9999656513498743/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_109 : ∀ (p : 109 < 1732), cc20Eq115CoefficientQ ⟨109, p⟩ = (9999656513498743 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 110 of the coefficient chain is the literal 1999929806378483/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_110 : ∀ (p : 110 < 1732), cc20Eq115CoefficientQ ⟨110, p⟩ = (1999929806378483 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 111 of the coefficient chain is the literal 4999820874900953/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_111 : ∀ (p : 111 < 1732), cc20Eq115CoefficientQ ⟨111, p⟩ = (4999820874900953 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 112 of the coefficient chain is the literal 2499908665049759/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_112 : ∀ (p : 112 < 1732), cc20Eq115CoefficientQ ⟨112, p⟩ = (2499908665049759 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 113 of the coefficient chain is the literal 4999813878176089/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_113 : ∀ (p : 113 < 1732), cc20Eq115CoefficientQ ⟨113, p⟩ = (4999813878176089 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 114 of the coefficient chain is the literal 2499905257958871/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_114 : ∀ (p : 114 < 1732), cc20Eq115CoefficientQ ⟨114, p⟩ = (2499905257958871 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 115 of the coefficient chain is the literal 1999922896097349/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_115 : ∀ (p : 115 < 1732), cc20Eq115CoefficientQ ⟨115, p⟩ = (1999922896097349 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 116 of the coefficient chain is the literal 4999804048206627/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_116 : ∀ (p : 116 < 1732), cc20Eq115CoefficientQ ⟨116, p⟩ = (4999804048206627 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 117 of the coefficient chain is the literal 624975117123003/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_117 : ∀ (p : 117 < 1732), cc20Eq115CoefficientQ ⟨117, p⟩ = (624975117123003 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 118 of the coefficient chain is the literal 4999797903869691/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_118 : ∀ (p : 118 < 1732), cc20Eq115CoefficientQ ⟨118, p⟩ = (4999797903869691 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 119 of the coefficient chain is the literal 9999589892554259/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_119 : ∀ (p : 119 < 1732), cc20Eq115CoefficientQ ⟨119, p⟩ = (9999589892554259 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 120 of the coefficient chain is the literal 2499896030850557/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_120 : ∀ (p : 120 < 1732), cc20Eq115CoefficientQ ⟨120, p⟩ = (2499896030850557 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 121 of the coefficient chain is the literal 4999789247776737/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_121 : ∀ (p : 121 < 1732), cc20Eq115CoefficientQ ⟨121, p⟩ = (4999789247776737 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 122 of the coefficient chain is the literal 9999573004422099/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_122 : ∀ (p : 122 < 1732), cc20Eq115CoefficientQ ⟨122, p⟩ = (9999573004422099 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 123 of the coefficient chain is the literal 1999913529121953/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_123 : ∀ (p : 123 < 1732), cc20Eq115CoefficientQ ⟨123, p⟩ = (1999913529121953 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 124 of the coefficient chain is the literal 999956241489983/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_124 : ∀ (p : 124 < 1732), cc20Eq115CoefficientQ ⟨124, p⟩ = (999956241489983 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 125 of the coefficient chain is the literal 2499889327060661/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_125 : ∀ (p : 125 < 1732), cc20Eq115CoefficientQ ⟨125, p⟩ = (2499889327060661 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 126 of the coefficient chain is the literal 2499888080436999/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_126 : ∀ (p : 126 < 1732), cc20Eq115CoefficientQ ⟨126, p⟩ = (2499888080436999 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 127 of the coefficient chain is the literal 2499886862917691/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_127 : ∀ (p : 127 < 1732), cc20Eq115CoefficientQ ⟨127, p⟩ = (2499886862917691 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 128 of the coefficient chain is the literal 4999771347210671/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_128 : ∀ (p : 128 < 1732), cc20Eq115CoefficientQ ⟨128, p⟩ = (4999771347210671 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 129 of the coefficient chain is the literal 2499884511633937/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_129 : ∀ (p : 129 < 1732), cc20Eq115CoefficientQ ⟨129, p⟩ = (2499884511633937 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 130 of the coefficient chain is the literal 2499883376171999/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_130 : ∀ (p : 130 < 1732), cc20Eq115CoefficientQ ⟨130, p⟩ = (2499883376171999 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 131 of the coefficient chain is the literal 9999529065682109/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_131 : ∀ (p : 131 < 1732), cc20Eq115CoefficientQ ⟨131, p⟩ = (9999529065682109 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 132 of the coefficient chain is the literal 624970295401891/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_132 : ∀ (p : 132 < 1732), cc20Eq115CoefficientQ ⟨132, p⟩ = (624970295401891 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 133 of the coefficient chain is the literal 1999904096793759/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_133 : ∀ (p : 133 < 1732), cc20Eq115CoefficientQ ⟨133, p⟩ = (1999904096793759 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 134 of the coefficient chain is the literal 1249939541929913/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_134 : ∀ (p : 134 < 1732), cc20Eq115CoefficientQ ⟨134, p⟩ = (1249939541929913 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 135 of the coefficient chain is the literal 9999512278091109/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_135 : ∀ (p : 135 < 1732), cc20Eq115CoefficientQ ⟨135, p⟩ = (9999512278091109 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 136 of the coefficient chain is the literal 9999508309270173/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_136 : ∀ (p : 136 < 1732), cc20Eq115CoefficientQ ⟨136, p⟩ = (9999508309270173 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 137 of the coefficient chain is the literal 9999504426418457/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_137 : ∀ (p : 137 < 1732), cc20Eq115CoefficientQ ⟨137, p⟩ = (9999504426418457 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 138 of the coefficient chain is the literal 4999750313536253/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_138 : ∀ (p : 138 < 1732), cc20Eq115CoefficientQ ⟨138, p⟩ = (4999750313536253 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 139 of the coefficient chain is the literal 9999496908855457/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_139 : ∀ (p : 139 < 1732), cc20Eq115CoefficientQ ⟨139, p⟩ = (9999496908855457 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 140 of the coefficient chain is the literal 4999746634735579/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_140 : ∀ (p : 140 < 1732), cc20Eq115CoefficientQ ⟨140, p⟩ = (4999746634735579 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 141 of the coefficient chain is the literal 2499872426679989/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_141 : ∀ (p : 141 < 1732), cc20Eq115CoefficientQ ⟨141, p⟩ = (2499872426679989 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 142 of the coefficient chain is the literal 4999743109216933/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_142 : ∀ (p : 142 < 1732), cc20Eq115CoefficientQ ⟨142, p⟩ = (4999743109216933 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 143 of the coefficient chain is the literal 2499870700645401/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_143 : ∀ (p : 143 < 1732), cc20Eq115CoefficientQ ⟨143, p⟩ = (2499870700645401 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 144 of the coefficient chain is the literal 1249934932145207/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_144 : ∀ (p : 144 < 1732), cc20Eq115CoefficientQ ⟨144, p⟩ = (1249934932145207 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 145 of the coefficient chain is the literal 9999476180252383/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_145 : ∀ (p : 145 < 1732), cc20Eq115CoefficientQ ⟨145, p⟩ = (9999476180252383 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 146 of the coefficient chain is the literal 9999472969994877/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_146 : ∀ (p : 146 < 1732), cc20Eq115CoefficientQ ⟨146, p⟩ = (9999472969994877 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 147 of the coefficient chain is the literal 1249933728074083/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_147 : ∀ (p : 147 < 1732), cc20Eq115CoefficientQ ⟨147, p⟩ = (1249933728074083 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 148 of the coefficient chain is the literal 9999466742314341/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_148 : ∀ (p : 148 < 1732), cc20Eq115CoefficientQ ⟨148, p⟩ = (9999466742314341 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 149 of the coefficient chain is the literal 999946372147767/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_149 : ∀ (p : 149 < 1732), cc20Eq115CoefficientQ ⟨149, p⟩ = (999946372147767 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 150 of the coefficient chain is the literal 9999460760461093/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_150 : ∀ (p : 150 < 1732), cc20Eq115CoefficientQ ⟨150, p⟩ = (9999460760461093 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 151 of the coefficient chain is the literal 9999457857694469/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_151 : ∀ (p : 151 < 1732), cc20Eq115CoefficientQ ⟨151, p⟩ = (9999457857694469 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 152 of the coefficient chain is the literal 9999455011660777/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_152 : ∀ (p : 152 < 1732), cc20Eq115CoefficientQ ⟨152, p⟩ = (9999455011660777 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 153 of the coefficient chain is the literal 999945222091901/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_153 : ∀ (p : 153 < 1732), cc20Eq115CoefficientQ ⟨153, p⟩ = (999945222091901 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 154 of the coefficient chain is the literal 9999449483994297/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_154 : ∀ (p : 154 < 1732), cc20Eq115CoefficientQ ⟨154, p⟩ = (9999449483994297 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 155 of the coefficient chain is the literal 9999446799538201/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_155 : ∀ (p : 155 < 1732), cc20Eq115CoefficientQ ⟨155, p⟩ = (9999446799538201 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 156 of the coefficient chain is the literal 624965260388783/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_156 : ∀ (p : 156 < 1732), cc20Eq115CoefficientQ ⟨156, p⟩ = (624965260388783 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 157 of the coefficient chain is the literal 9999441582746459/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_157 : ∀ (p : 157 < 1732), cc20Eq115CoefficientQ ⟨157, p⟩ = (9999441582746459 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 158 of the coefficient chain is the literal 4999719523933971/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_158 : ∀ (p : 158 < 1732), cc20Eq115CoefficientQ ⟨158, p⟩ = (4999719523933971 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 159 of the coefficient chain is the literal 4999718280186471/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_159 : ∀ (p : 159 < 1732), cc20Eq115CoefficientQ ⟨159, p⟩ = (4999718280186471 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 160 of the coefficient chain is the literal 1999886823817327/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_160 : ∀ (p : 160 < 1732), cc20Eq115CoefficientQ ⟨160, p⟩ = (1999886823817327 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 161 of the coefficient chain is the literal 4999715861436503/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_161 : ∀ (p : 161 < 1732), cc20Eq115CoefficientQ ⟨161, p⟩ = (4999715861436503 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 162 of the coefficient chain is the literal 249985734265729/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_162 : ∀ (p : 162 < 1732), cc20Eq115CoefficientQ ⟨162, p⟩ = (249985734265729 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 163 of the coefficient chain is the literal 2499856765321683/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_163 : ∀ (p : 163 < 1732), cc20Eq115CoefficientQ ⟨163, p⟩ = (2499856765321683 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 164 of the coefficient chain is the literal 9999424793804271/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_164 : ∀ (p : 164 < 1732), cc20Eq115CoefficientQ ⟨164, p⟩ = (9999424793804271 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 165 of the coefficient chain is the literal 9999422567180947/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_165 : ∀ (p : 165 < 1732), cc20Eq115CoefficientQ ⟨165, p⟩ = (9999422567180947 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 166 of the coefficient chain is the literal 4999710190221569/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_166 : ∀ (p : 166 < 1732), cc20Eq115CoefficientQ ⟨166, p⟩ = (4999710190221569 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 167 of the coefficient chain is the literal 9999418232644403/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_167 : ∀ (p : 167 < 1732), cc20Eq115CoefficientQ ⟨167, p⟩ = (9999418232644403 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 168 of the coefficient chain is the literal 9999416122855159/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_168 : ∀ (p : 168 < 1732), cc20Eq115CoefficientQ ⟨168, p⟩ = (9999416122855159 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 169 of the coefficient chain is the literal 9999414050191779/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_169 : ∀ (p : 169 < 1732), cc20Eq115CoefficientQ ⟨169, p⟩ = (9999414050191779 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 170 of the coefficient chain is the literal 2499853003442817/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_170 : ∀ (p : 170 < 1732), cc20Eq115CoefficientQ ⟨170, p⟩ = (2499853003442817 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 171 of the coefficient chain is the literal 2499852503198693/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_171 : ∀ (p : 171 < 1732), cc20Eq115CoefficientQ ⟨171, p⟩ = (2499852503198693 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 172 of the coefficient chain is the literal 1999881609282327/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_172 : ∀ (p : 172 < 1732), cc20Eq115CoefficientQ ⟨172, p⟩ = (1999881609282327 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 173 of the coefficient chain is the literal 2499851528458747/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_173 : ∀ (p : 173 < 1732), cc20Eq115CoefficientQ ⟨173, p⟩ = (2499851528458747 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 174 of the coefficient chain is the literal 2499851053573493/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_174 : ∀ (p : 174 < 1732), cc20Eq115CoefficientQ ⟨174, p⟩ = (2499851053573493 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 175 of the coefficient chain is the literal 9999402347044689/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_175 : ∀ (p : 175 < 1732), cc20Eq115CoefficientQ ⟨175, p⟩ = (9999402347044689 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 176 of the coefficient chain is the literal 4999700255677413/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_176 : ∀ (p : 176 < 1732), cc20Eq115CoefficientQ ⟨176, p⟩ = (4999700255677413 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 177 of the coefficient chain is the literal 39060151197341/ 39062500000000. -/
theorem cc20Eq115CoefficientQ_branch_177 : ∀ (p : 177 < 1732), cc20Eq115CoefficientQ ⟨177, p⟩ = (39060151197341 : ℚ) /  39062500000000 :=
  fun p => by rfl

/-- Branch 178 of the coefficient chain is the literal 1249924616481093/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_178 : ∀ (p : 178 < 1732), cc20Eq115CoefficientQ ⟨178, p⟩ = (1249924616481093 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 179 of the coefficient chain is the literal 9999395186677721/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_179 : ∀ (p : 179 < 1732), cc20Eq115CoefficientQ ⟨179, p⟩ = (9999395186677721 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 180 of the coefficient chain is the literal 499969673517763/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_180 : ∀ (p : 180 < 1732), cc20Eq115CoefficientQ ⟨180, p⟩ = (499969673517763 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 181 of the coefficient chain is the literal 9999391782248271/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_181 : ∀ (p : 181 < 1732), cc20Eq115CoefficientQ ⟨181, p⟩ = (9999391782248271 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 182 of the coefficient chain is the literal 78120235326099/ 78125000000000. -/
theorem cc20Eq115CoefficientQ_branch_182 : ∀ (p : 182 < 1732), cc20Eq115CoefficientQ ⟨182, p⟩ = (78120235326099 : ℚ) /  78125000000000 :=
  fun p => by rfl

/-- Branch 183 of the coefficient chain is the literal 4999694244118021/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_183 : ∀ (p : 183 < 1732), cc20Eq115CoefficientQ ⟨183, p⟩ = (4999694244118021 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 184 of the coefficient chain is the literal 999938688114971/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_184 : ∀ (p : 184 < 1732), cc20Eq115CoefficientQ ⟨184, p⟩ = (999938688114971 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 185 of the coefficient chain is the literal 999938529991507/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_185 : ∀ (p : 185 < 1732), cc20Eq115CoefficientQ ⟨185, p⟩ = (999938529991507 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 186 of the coefficient chain is the literal 4999691871998897/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_186 : ∀ (p : 186 < 1732), cc20Eq115CoefficientQ ⟨186, p⟩ = (4999691871998897 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 187 of the coefficient chain is the literal 4999691106413681/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_187 : ∀ (p : 187 < 1732), cc20Eq115CoefficientQ ⟨187, p⟩ = (4999691106413681 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 188 of the coefficient chain is the literal 9999380705925559/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_188 : ∀ (p : 188 < 1732), cc20Eq115CoefficientQ ⟨188, p⟩ = (9999380705925559 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 189 of the coefficient chain is the literal 9999379222725979/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_189 : ∀ (p : 189 < 1732), cc20Eq115CoefficientQ ⟨189, p⟩ = (9999379222725979 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 190 of the coefficient chain is the literal 312480555086523/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_190 : ∀ (p : 190 < 1732), cc20Eq115CoefficientQ ⟨190, p⟩ = (312480555086523 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 191 of the coefficient chain is the literal 9999376325565833/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_191 : ∀ (p : 191 < 1732), cc20Eq115CoefficientQ ⟨191, p⟩ = (9999376325565833 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 192 of the coefficient chain is the literal 9999374910669623/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_192 : ∀ (p : 192 < 1732), cc20Eq115CoefficientQ ⟨192, p⟩ = (9999374910669623 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 193 of the coefficient chain is the literal 1999874703515457/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_193 : ∀ (p : 193 < 1732), cc20Eq115CoefficientQ ⟨193, p⟩ = (1999874703515457 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 194 of the coefficient chain is the literal 9999372145865473/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_194 : ∀ (p : 194 < 1732), cc20Eq115CoefficientQ ⟨194, p⟩ = (9999372145865473 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 195 of the coefficient chain is the literal 99993707951/ 100000000000. -/
theorem cc20Eq115CoefficientQ_branch_195 : ∀ (p : 195 < 1732), cc20Eq115CoefficientQ ⟨195, p⟩ = (99993707951 : ℚ) /  100000000000 :=
  fun p => by rfl

/-- Branch 196 of the coefficient chain is the literal 39997477859413/ 40000000000000. -/
theorem cc20Eq115CoefficientQ_branch_196 : ∀ (p : 196 < 1732), cc20Eq115CoefficientQ ⟨196, p⟩ = (39997477859413 : ℚ) /  40000000000000 :=
  fun p => by rfl

/-- Branch 197 of the coefficient chain is the literal 78120063708699/ 78125000000000. -/
theorem cc20Eq115CoefficientQ_branch_197 : ∀ (p : 197 < 1732), cc20Eq115CoefficientQ ⟨197, p⟩ = (78120063708699 : ℚ) /  78125000000000 :=
  fun p => by rfl

/-- Branch 198 of the coefficient chain is the literal 9999366864288829/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_198 : ∀ (p : 198 < 1732), cc20Eq115CoefficientQ ⟨198, p⟩ = (9999366864288829 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 199 of the coefficient chain is the literal 9999365593164093/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_199 : ∀ (p : 199 < 1732), cc20Eq115CoefficientQ ⟨199, p⟩ = (9999365593164093 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 200 of the coefficient chain is the literal 624960271310237/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_200 : ∀ (p : 200 < 1732), cc20Eq115CoefficientQ ⟨200, p⟩ = (624960271310237 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 201 of the coefficient chain is the literal 1249920388414831/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_201 : ∀ (p : 201 < 1732), cc20Eq115CoefficientQ ⟨201, p⟩ = (1249920388414831 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 202 of the coefficient chain is the literal 9999361891863161/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_202 : ∀ (p : 202 < 1732), cc20Eq115CoefficientQ ⟨202, p⟩ = (9999361891863161 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 203 of the coefficient chain is the literal 1249920086780017/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_203 : ∀ (p : 203 < 1732), cc20Eq115CoefficientQ ⟨203, p⟩ = (1249920086780017 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 204 of the coefficient chain is the literal 2499839878525197/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_204 : ∀ (p : 204 < 1732), cc20Eq115CoefficientQ ⟨204, p⟩ = (2499839878525197 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 205 of the coefficient chain is the literal 4999679175555193/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_205 : ∀ (p : 205 < 1732), cc20Eq115CoefficientQ ⟨205, p⟩ = (4999679175555193 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 206 of the coefficient chain is the literal 999935720493553/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_206 : ∀ (p : 206 < 1732), cc20Eq115CoefficientQ ⟨206, p⟩ = (999935720493553 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 207 of the coefficient chain is the literal 9999356075254897/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_207 : ∀ (p : 207 < 1732), cc20Eq115CoefficientQ ⟨207, p⟩ = (9999356075254897 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 208 of the coefficient chain is the literal 4999677480876779/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_208 : ∀ (p : 208 < 1732), cc20Eq115CoefficientQ ⟨208, p⟩ = (4999677480876779 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 209 of the coefficient chain is the literal 9999353864123901/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_209 : ∀ (p : 209 < 1732), cc20Eq115CoefficientQ ⟨209, p⟩ = (9999353864123901 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 210 of the coefficient chain is the literal 9999352782062427/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_210 : ∀ (p : 210 < 1732), cc20Eq115CoefficientQ ⟨210, p⟩ = (9999352782062427 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 211 of the coefficient chain is the literal 4999675857640377/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_211 : ∀ (p : 211 < 1732), cc20Eq115CoefficientQ ⟨211, p⟩ = (4999675857640377 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 212 of the coefficient chain is the literal 99993506634911/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_212 : ∀ (p : 212 < 1732), cc20Eq115CoefficientQ ⟨212, p⟩ = (99993506634911 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 213 of the coefficient chain is the literal 399973985056567/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_213 : ∀ (p : 213 < 1732), cc20Eq115CoefficientQ ⟨213, p⟩ = (399973985056567 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 214 of the coefficient chain is the literal 9999348603775007/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_214 : ∀ (p : 214 < 1732), cc20Eq115CoefficientQ ⟨214, p⟩ = (9999348603775007 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 215 of the coefficient chain is the literal 9999347595310417/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_215 : ∀ (p : 215 < 1732), cc20Eq115CoefficientQ ⟨215, p⟩ = (9999347595310417 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 216 of the coefficient chain is the literal 2499836650189449/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_216 : ∀ (p : 216 < 1732), cc20Eq115CoefficientQ ⟨216, p⟩ = (2499836650189449 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 217 of the coefficient chain is the literal 499967280993047/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_217 : ∀ (p : 217 < 1732), cc20Eq115CoefficientQ ⟨217, p⟩ = (499967280993047 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 218 of the coefficient chain is the literal 199986893047431/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_218 : ∀ (p : 218 < 1732), cc20Eq115CoefficientQ ⟨218, p⟩ = (199986893047431 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 219 of the coefficient chain is the literal 9999343698049229/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_219 : ∀ (p : 219 < 1732), cc20Eq115CoefficientQ ⟨219, p⟩ = (9999343698049229 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 220 of the coefficient chain is the literal 4999671378326551/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_220 : ∀ (p : 220 < 1732), cc20Eq115CoefficientQ ⟨220, p⟩ = (4999671378326551 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 221 of the coefficient chain is the literal 1999868365590651/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_221 : ∀ (p : 221 < 1732), cc20Eq115CoefficientQ ⟨221, p⟩ = (1999868365590651 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 222 of the coefficient chain is the literal 499967045585707/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_222 : ∀ (p : 222 < 1732), cc20Eq115CoefficientQ ⟨222, p⟩ = (499967045585707 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 223 of the coefficient chain is the literal 1249917500966039/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_223 : ∀ (p : 223 < 1732), cc20Eq115CoefficientQ ⟨223, p⟩ = (1249917500966039 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 224 of the coefficient chain is the literal 9999339115772597/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_224 : ∀ (p : 224 < 1732), cc20Eq115CoefficientQ ⟨224, p⟩ = (9999339115772597 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 225 of the coefficient chain is the literal 2499834558906581/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_225 : ∀ (p : 225 < 1732), cc20Eq115CoefficientQ ⟨225, p⟩ = (2499834558906581 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 226 of the coefficient chain is the literal 4999668683544937/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_226 : ∀ (p : 226 < 1732), cc20Eq115CoefficientQ ⟨226, p⟩ = (4999668683544937 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 227 of the coefficient chain is the literal 624958531872379/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_227 : ∀ (p : 227 < 1732), cc20Eq115CoefficientQ ⟨227, p⟩ = (624958531872379 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 228 of the coefficient chain is the literal 9999335664032987/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_228 : ∀ (p : 228 < 1732), cc20Eq115CoefficientQ ⟨228, p⟩ = (9999335664032987 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 229 of the coefficient chain is the literal 1999866965824749/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_229 : ∀ (p : 229 < 1732), cc20Eq115CoefficientQ ⟨229, p⟩ = (1999866965824749 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 230 of the coefficient chain is the literal 9999334005034413/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_230 : ∀ (p : 230 < 1732), cc20Eq115CoefficientQ ⟨230, p⟩ = (9999334005034413 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 231 of the coefficient chain is the literal 31247916223681/ 31250000000000. -/
theorem cc20Eq115CoefficientQ_branch_231 : ∀ (p : 231 < 1732), cc20Eq115CoefficientQ ⟨231, p⟩ = (31247916223681 : ℚ) /  31250000000000 :=
  fun p => by rfl

/-- Branch 232 of the coefficient chain is the literal 1999866477715031/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_232 : ∀ (p : 232 < 1732), cc20Eq115CoefficientQ ⟨232, p⟩ = (1999866477715031 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 233 of the coefficient chain is the literal 4999665797923733/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_233 : ∀ (p : 233 < 1732), cc20Eq115CoefficientQ ⟨233, p⟩ = (4999665797923733 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 234 of the coefficient chain is the literal 1249916351652479/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_234 : ∀ (p : 234 < 1732), cc20Eq115CoefficientQ ⟨234, p⟩ = (1249916351652479 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 235 of the coefficient chain is the literal 9999330040523507/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_235 : ∀ (p : 235 < 1732), cc20Eq115CoefficientQ ⟨235, p⟩ = (9999330040523507 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 236 of the coefficient chain is the literal 2499832319396873/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_236 : ∀ (p : 236 < 1732), cc20Eq115CoefficientQ ⟨236, p⟩ = (2499832319396873 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 237 of the coefficient chain is the literal 1249916065531383/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_237 : ∀ (p : 237 < 1732), cc20Eq115CoefficientQ ⟨237, p⟩ = (1249916065531383 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 238 of the coefficient chain is the literal 9999327780351863/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_238 : ∀ (p : 238 < 1732), cc20Eq115CoefficientQ ⟨238, p⟩ = (9999327780351863 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 239 of the coefficient chain is the literal 9999327045734447/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_239 : ∀ (p : 239 < 1732), cc20Eq115CoefficientQ ⟨239, p⟩ = (9999327045734447 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 240 of the coefficient chain is the literal 9999326320246277/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_240 : ∀ (p : 240 < 1732), cc20Eq115CoefficientQ ⟨240, p⟩ = (9999326320246277 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 241 of the coefficient chain is the literal 4999662801866381/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_241 : ∀ (p : 241 < 1732), cc20Eq115CoefficientQ ⟨241, p⟩ = (4999662801866381 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 242 of the coefficient chain is the literal 4999662448025187/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_242 : ∀ (p : 242 < 1732), cc20Eq115CoefficientQ ⟨242, p⟩ = (4999662448025187 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 243 of the coefficient chain is the literal 2499831049262817/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_243 : ∀ (p : 243 < 1732), cc20Eq115CoefficientQ ⟨243, p⟩ = (2499831049262817 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 244 of the coefficient chain is the literal 9999323506598411/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_244 : ∀ (p : 244 < 1732), cc20Eq115CoefficientQ ⟨244, p⟩ = (9999323506598411 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 245 of the coefficient chain is the literal 9999322824542011/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_245 : ∀ (p : 245 < 1732), cc20Eq115CoefficientQ ⟨245, p⟩ = (9999322824542011 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 246 of the coefficient chain is the literal 9999322150765307/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_246 : ∀ (p : 246 < 1732), cc20Eq115CoefficientQ ⟨246, p⟩ = (9999322150765307 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 247 of the coefficient chain is the literal 9999321485121941/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_247 : ∀ (p : 247 < 1732), cc20Eq115CoefficientQ ⟨247, p⟩ = (9999321485121941 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 248 of the coefficient chain is the literal 399972833099403/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_248 : ∀ (p : 248 < 1732), cc20Eq115CoefficientQ ⟨248, p⟩ = (399972833099403 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 249 of the coefficient chain is the literal 4999660088862279/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_249 : ∀ (p : 249 < 1732), cc20Eq115CoefficientQ ⟨249, p⟩ = (4999660088862279 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 250 of the coefficient chain is the literal 4999659767857633/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_250 : ∀ (p : 250 < 1732), cc20Eq115CoefficientQ ⟨250, p⟩ = (4999659767857633 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 251 of the coefficient chain is the literal 1999863780267413/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_251 : ∀ (p : 251 < 1732), cc20Eq115CoefficientQ ⟨251, p⟩ = (1999863780267413 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 252 of the coefficient chain is the literal 9999318274468527/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_252 : ∀ (p : 252 < 1732), cc20Eq115CoefficientQ ⟨252, p⟩ = (9999318274468527 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 253 of the coefficient chain is the literal 9999317654991179/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_253 : ∀ (p : 253 < 1732), cc20Eq115CoefficientQ ⟨253, p⟩ = (9999317654991179 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 254 of the coefficient chain is the literal 9999317042789623/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_254 : ∀ (p : 254 < 1732), cc20Eq115CoefficientQ ⟨254, p⟩ = (9999317042789623 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 255 of the coefficient chain is the literal 9999316437749411/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_255 : ∀ (p : 255 < 1732), cc20Eq115CoefficientQ ⟨255, p⟩ = (9999316437749411 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 256 of the coefficient chain is the literal 9999315839757751/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_256 : ∀ (p : 256 < 1732), cc20Eq115CoefficientQ ⟨256, p⟩ = (9999315839757751 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 257 of the coefficient chain is the literal 499965762435589/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_257 : ∀ (p : 257 < 1732), cc20Eq115CoefficientQ ⟨257, p⟩ = (499965762435589 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 258 of the coefficient chain is the literal 9999314664496949/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_258 : ∀ (p : 258 < 1732), cc20Eq115CoefficientQ ⟨258, p⟩ = (9999314664496949 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 259 of the coefficient chain is the literal 2499828521754037/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_259 : ∀ (p : 259 < 1732), cc20Eq115CoefficientQ ⟨259, p⟩ = (2499828521754037 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 260 of the coefficient chain is the literal 9999313516159359/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_260 : ∀ (p : 260 < 1732), cc20Eq115CoefficientQ ⟨260, p⟩ = (9999313516159359 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 261 of the coefficient chain is the literal 2499828237957861/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_261 : ∀ (p : 261 < 1732), cc20Eq115CoefficientQ ⟨261, p⟩ = (2499828237957861 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 262 of the coefficient chain is the literal 9999312393928473/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_262 : ∀ (p : 262 < 1732), cc20Eq115CoefficientQ ⟨262, p⟩ = (9999312393928473 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 263 of the coefficient chain is the literal 2499827960588657/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_263 : ∀ (p : 263 < 1732), cc20Eq115CoefficientQ ⟨263, p⟩ = (2499827960588657 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 264 of the coefficient chain is the literal 2499827824254161/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_264 : ∀ (p : 264 < 1732), cc20Eq115CoefficientQ ⟨264, p⟩ = (2499827824254161 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 265 of the coefficient chain is the literal 9999310757816611/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_265 : ∀ (p : 265 < 1732), cc20Eq115CoefficientQ ⟨265, p⟩ = (9999310757816611 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 266 of the coefficient chain is the literal 4999655112334287/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_266 : ∀ (p : 266 < 1732), cc20Eq115CoefficientQ ⟨266, p⟩ = (4999655112334287 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 267 of the coefficient chain is the literal 39997238789917/ 40000000000000. -/
theorem cc20Eq115CoefficientQ_branch_267 : ∀ (p : 267 < 1732), cc20Eq115CoefficientQ ⟨267, p⟩ = (39997238789917 : ℚ) /  40000000000000 :=
  fun p => by rfl

/-- Branch 268 of the coefficient chain is the literal 9999309176158693/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_268 : ∀ (p : 268 < 1732), cc20Eq115CoefficientQ ⟨268, p⟩ = (9999309176158693 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 269 of the coefficient chain is the literal 9999308660622837/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_269 : ∀ (p : 269 < 1732), cc20Eq115CoefficientQ ⟨269, p⟩ = (9999308660622837 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 270 of the coefficient chain is the literal 4999654075392053/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_270 : ∀ (p : 270 < 1732), cc20Eq115CoefficientQ ⟨270, p⟩ = (4999654075392053 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 271 of the coefficient chain is the literal 9999307646562691/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_271 : ∀ (p : 271 < 1732), cc20Eq115CoefficientQ ⟨271, p⟩ = (9999307646562691 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 272 of the coefficient chain is the literal 1999861429574741/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_272 : ∀ (p : 272 < 1732), cc20Eq115CoefficientQ ⟨272, p⟩ = (1999861429574741 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 273 of the coefficient chain is the literal 156239166478717/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_273 : ∀ (p : 273 < 1732), cc20Eq115CoefficientQ ⟨273, p⟩ = (156239166478717 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 274 of the coefficient chain is the literal 9999306166770097/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_274 : ∀ (p : 274 < 1732), cc20Eq115CoefficientQ ⟨274, p⟩ = (9999306166770097 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 275 of the coefficient chain is the literal 1249913210523991/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_275 : ∀ (p : 275 < 1732), cc20Eq115CoefficientQ ⟨275, p⟩ = (1249913210523991 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 276 of the coefficient chain is the literal 9999305206843969/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_276 : ∀ (p : 276 < 1732), cc20Eq115CoefficientQ ⟨276, p⟩ = (9999305206843969 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 277 of the coefficient chain is the literal 156239136478699/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_277 : ∀ (p : 277 < 1732), cc20Eq115CoefficientQ ⟨277, p⟩ = (156239136478699 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 278 of the coefficient chain is the literal 399972170699967/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_278 : ∀ (p : 278 < 1732), cc20Eq115CoefficientQ ⟨278, p⟩ = (399972170699967 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 279 of the coefficient chain is the literal 2499825951340227/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_279 : ∀ (p : 279 < 1732), cc20Eq115CoefficientQ ⟨279, p⟩ = (2499825951340227 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 280 of the coefficient chain is the literal 1249912918518527/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_280 : ∀ (p : 280 < 1732), cc20Eq115CoefficientQ ⟨280, p⟩ = (1249912918518527 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 281 of the coefficient chain is the literal 9999302895792839/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_281 : ∀ (p : 281 < 1732), cc20Eq115CoefficientQ ⟨281, p⟩ = (9999302895792839 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 282 of the coefficient chain is the literal 4999651224113027/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_282 : ∀ (p : 282 < 1732), cc20Eq115CoefficientQ ⟨282, p⟩ = (4999651224113027 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 283 of the coefficient chain is the literal 9999302005382861/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_283 : ∀ (p : 283 < 1732), cc20Eq115CoefficientQ ⟨283, p⟩ = (9999302005382861 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 284 of the coefficient chain is the literal 2499825391798499/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_284 : ∀ (p : 284 < 1732), cc20Eq115CoefficientQ ⟨284, p⟩ = (2499825391798499 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 285 of the coefficient chain is the literal 2499825283398503/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_285 : ∀ (p : 285 < 1732), cc20Eq115CoefficientQ ⟨285, p⟩ = (2499825283398503 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 286 of the coefficient chain is the literal 4999650352261247/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_286 : ∀ (p : 286 < 1732), cc20Eq115CoefficientQ ⟨286, p⟩ = (4999650352261247 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 287 of the coefficient chain is the literal 2499825069978307/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_287 : ∀ (p : 287 < 1732), cc20Eq115CoefficientQ ⟨287, p⟩ = (2499825069978307 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 288 of the coefficient chain is the literal 2499824964925899/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_288 : ∀ (p : 288 < 1732), cc20Eq115CoefficientQ ⟨288, p⟩ = (2499824964925899 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 289 of the coefficient chain is the literal 2499824860959833/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_289 : ∀ (p : 289 < 1732), cc20Eq115CoefficientQ ⟨289, p⟩ = (2499824860959833 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 290 of the coefficient chain is the literal 1999859806450987/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_290 : ∀ (p : 290 < 1732), cc20Eq115CoefficientQ ⟨290, p⟩ = (1999859806450987 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 291 of the coefficient chain is the literal 4999649312447383/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_291 : ∀ (p : 291 < 1732), cc20Eq115CoefficientQ ⟨291, p⟩ = (4999649312447383 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 292 of the coefficient chain is the literal 2499824555424451/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_292 : ∀ (p : 292 < 1732), cc20Eq115CoefficientQ ⟨292, p⟩ = (2499824555424451 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 293 of the coefficient chain is the literal 9999297822613203/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_293 : ∀ (p : 293 < 1732), cc20Eq115CoefficientQ ⟨293, p⟩ = (9999297822613203 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 294 of the coefficient chain is the literal 999929742757911/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_294 : ∀ (p : 294 < 1732), cc20Eq115CoefficientQ ⟨294, p⟩ = (999929742757911 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 295 of the coefficient chain is the literal 1999859407309499/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_295 : ∀ (p : 295 < 1732), cc20Eq115CoefficientQ ⟨295, p⟩ = (1999859407309499 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 296 of the coefficient chain is the literal 1999859329891849/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_296 : ∀ (p : 296 < 1732), cc20Eq115CoefficientQ ⟨296, p⟩ = (1999859329891849 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 297 of the coefficient chain is the literal 499964813313051/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_297 : ∀ (p : 297 < 1732), cc20Eq115CoefficientQ ⟨297, p⟩ = (499964813313051 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 298 of the coefficient chain is the literal 2499823971726427/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_298 : ∀ (p : 298 < 1732), cc20Eq115CoefficientQ ⟨298, p⟩ = (2499823971726427 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 299 of the coefficient chain is the literal 4999647755668523/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_299 : ∀ (p : 299 < 1732), cc20Eq115CoefficientQ ⟨299, p⟩ = (4999647755668523 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 300 of the coefficient chain is the literal 1999859027901671/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_300 : ∀ (p : 300 < 1732), cc20Eq115CoefficientQ ⟨300, p⟩ = (1999859027901671 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 301 of the coefficient chain is the literal 4999647385686833/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_301 : ∀ (p : 301 < 1732), cc20Eq115CoefficientQ ⟨301, p⟩ = (4999647385686833 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 302 of the coefficient chain is the literal 4999647203437349/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_302 : ∀ (p : 302 < 1732), cc20Eq115CoefficientQ ⟨302, p⟩ = (4999647203437349 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 303 of the coefficient chain is the literal 4999647022984247/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_303 : ∀ (p : 303 < 1732), cc20Eq115CoefficientQ ⟨303, p⟩ = (4999647022984247 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 304 of the coefficient chain is the literal 9999293688610833/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_304 : ∀ (p : 304 < 1732), cc20Eq115CoefficientQ ⟨304, p⟩ = (9999293688610833 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 305 of the coefficient chain is the literal 9999293334752579/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_305 : ∀ (p : 305 < 1732), cc20Eq115CoefficientQ ⟨305, p⟩ = (9999293334752579 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 306 of the coefficient chain is the literal 9999292984345601/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_306 : ∀ (p : 306 < 1732), cc20Eq115CoefficientQ ⟨306, p⟩ = (9999292984345601 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 307 of the coefficient chain is the literal 9999292637351063/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_307 : ∀ (p : 307 < 1732), cc20Eq115CoefficientQ ⟨307, p⟩ = (9999292637351063 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 308 of the coefficient chain is the literal 1249911536714923/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_308 : ∀ (p : 308 < 1732), cc20Eq115CoefficientQ ⟨308, p⟩ = (1249911536714923 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 309 of the coefficient chain is the literal 9999291953412377/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_309 : ∀ (p : 309 < 1732), cc20Eq115CoefficientQ ⟨309, p⟩ = (9999291953412377 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 310 of the coefficient chain is the literal 9999291616382667/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_310 : ∀ (p : 310 < 1732), cc20Eq115CoefficientQ ⟨310, p⟩ = (9999291616382667 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 311 of the coefficient chain is the literal 499964564129577/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_311 : ∀ (p : 311 < 1732), cc20Eq115CoefficientQ ⟨311, p⟩ = (499964564129577 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 312 of the coefficient chain is the literal 1249911368999633/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_312 : ∀ (p : 312 < 1732), cc20Eq115CoefficientQ ⟨312, p⟩ = (1249911368999633 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 313 of the coefficient chain is the literal 4999645312278257/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_313 : ∀ (p : 313 < 1732), cc20Eq115CoefficientQ ⟨313, p⟩ = (4999645312278257 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 314 of the coefficient chain is the literal 1999858060046287/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_314 : ∀ (p : 314 < 1732), cc20Eq115CoefficientQ ⟨314, p⟩ = (1999858060046287 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 315 of the coefficient chain is the literal 9999289978984413/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_315 : ∀ (p : 315 < 1732), cc20Eq115CoefficientQ ⟨315, p⟩ = (9999289978984413 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 316 of the coefficient chain is the literal 62495560379823/ 62500000000000. -/
theorem cc20Eq115CoefficientQ_branch_316 : ∀ (p : 316 < 1732), cc20Eq115CoefficientQ ⟨316, p⟩ = (62495560379823 : ℚ) /  62500000000000 :=
  fun p => by rfl

/-- Branch 317 of the coefficient chain is the literal 4999644672779967/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_317 : ∀ (p : 317 < 1732), cc20Eq115CoefficientQ ⟨317, p⟩ = (4999644672779967 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 318 of the coefficient chain is the literal 9999289033309219/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_318 : ∀ (p : 318 < 1732), cc20Eq115CoefficientQ ⟨318, p⟩ = (9999289033309219 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 319 of the coefficient chain is the literal 4999644361991243/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_319 : ∀ (p : 319 < 1732), cc20Eq115CoefficientQ ⟨319, p⟩ = (4999644361991243 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 320 of the coefficient chain is the literal 999928841754553/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_320 : ∀ (p : 320 < 1732), cc20Eq115CoefficientQ ⟨320, p⟩ = (999928841754553 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 321 of the coefficient chain is the literal 2499822028490081/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_321 : ∀ (p : 321 < 1732), cc20Eq115CoefficientQ ⟨321, p⟩ = (2499822028490081 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 322 of the coefficient chain is the literal 9999287813193389/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_322 : ∀ (p : 322 < 1732), cc20Eq115CoefficientQ ⟨322, p⟩ = (9999287813193389 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 323 of the coefficient chain is the literal 9999287515209063/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_323 : ∀ (p : 323 < 1732), cc20Eq115CoefficientQ ⟨323, p⟩ = (9999287515209063 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 324 of the coefficient chain is the literal 1999857443994087/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_324 : ∀ (p : 324 < 1732), cc20Eq115CoefficientQ ⟨324, p⟩ = (1999857443994087 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 325 of the coefficient chain is the literal 399971477097917/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_325 : ∀ (p : 325 < 1732), cc20Eq115CoefficientQ ⟨325, p⟩ = (399971477097917 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 326 of the coefficient chain is the literal 9999286637606147/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_326 : ∀ (p : 326 < 1732), cc20Eq115CoefficientQ ⟨326, p⟩ = (9999286637606147 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 327 of the coefficient chain is the literal 1999857270083401/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_327 : ∀ (p : 327 < 1732), cc20Eq115CoefficientQ ⟨327, p⟩ = (1999857270083401 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 328 of the coefficient chain is the literal 9999286065841679/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_328 : ∀ (p : 328 < 1732), cc20Eq115CoefficientQ ⟨328, p⟩ = (9999286065841679 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 329 of the coefficient chain is the literal 4999642891927081/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_329 : ∀ (p : 329 < 1732), cc20Eq115CoefficientQ ⟨329, p⟩ = (4999642891927081 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 330 of the coefficient chain is the literal 9999285504410289/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_330 : ∀ (p : 330 < 1732), cc20Eq115CoefficientQ ⟨330, p⟩ = (9999285504410289 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 331 of the coefficient chain is the literal 9999285227494893/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_331 : ∀ (p : 331 < 1732), cc20Eq115CoefficientQ ⟨331, p⟩ = (9999285227494893 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 332 of the coefficient chain is the literal 624955309567283/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_332 : ∀ (p : 332 < 1732), cc20Eq115CoefficientQ ⟨332, p⟩ = (624955309567283 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 333 of the coefficient chain is the literal 4999642340559621/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_333 : ∀ (p : 333 < 1732), cc20Eq115CoefficientQ ⟨333, p⟩ = (4999642340559621 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 334 of the coefficient chain is the literal 4999642205798789/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_334 : ∀ (p : 334 < 1732), cc20Eq115CoefficientQ ⟨334, p⟩ = (4999642205798789 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 335 of the coefficient chain is the literal 9999284144476619/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_335 : ∀ (p : 335 < 1732), cc20Eq115CoefficientQ ⟨335, p⟩ = (9999284144476619 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 336 of the coefficient chain is the literal 9999283879734537/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_336 : ∀ (p : 336 < 1732), cc20Eq115CoefficientQ ⟨336, p⟩ = (9999283879734537 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 337 of the coefficient chain is the literal 2499820904335057/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_337 : ∀ (p : 337 < 1732), cc20Eq115CoefficientQ ⟨337, p⟩ = (2499820904335057 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 338 of the coefficient chain is the literal 9999283357267459/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_338 : ∀ (p : 338 < 1732), cc20Eq115CoefficientQ ⟨338, p⟩ = (9999283357267459 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 339 of the coefficient chain is the literal 9999283099484109/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_339 : ∀ (p : 339 < 1732), cc20Eq115CoefficientQ ⟨339, p⟩ = (9999283099484109 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 340 of the coefficient chain is the literal 2499820710993251/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_340 : ∀ (p : 340 < 1732), cc20Eq115CoefficientQ ⟨340, p⟩ = (2499820710993251 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 341 of the coefficient chain is the literal 124991032383719/ 125000000000000. -/
theorem cc20Eq115CoefficientQ_branch_341 : ∀ (p : 341 < 1732), cc20Eq115CoefficientQ ⟨341, p⟩ = (124991032383719 : ℚ) /  125000000000000 :=
  fun p => by rfl

/-- Branch 342 of the coefficient chain is the literal 9999282339638801/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_342 : ∀ (p : 342 < 1732), cc20Eq115CoefficientQ ⟨342, p⟩ = (9999282339638801 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 343 of the coefficient chain is the literal 9999282090765541/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_343 : ∀ (p : 343 < 1732), cc20Eq115CoefficientQ ⟨343, p⟩ = (9999282090765541 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 344 of the coefficient chain is the literal 9999281844056531/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_344 : ∀ (p : 344 < 1732), cc20Eq115CoefficientQ ⟨344, p⟩ = (9999281844056531 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 345 of the coefficient chain is the literal 2499820399871193/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_345 : ∀ (p : 345 < 1732), cc20Eq115CoefficientQ ⟨345, p⟩ = (2499820399871193 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 346 of the coefficient chain is the literal 999928135702787/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_346 : ∀ (p : 346 < 1732), cc20Eq115CoefficientQ ⟨346, p⟩ = (999928135702787 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 347 of the coefficient chain is the literal 624955069791067/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_347 : ∀ (p : 347 < 1732), cc20Eq115CoefficientQ ⟨347, p⟩ = (624955069791067 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 348 of the coefficient chain is the literal 9999280878353299/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_348 : ∀ (p : 348 < 1732), cc20Eq115CoefficientQ ⟨348, p⟩ = (9999280878353299 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 349 of the coefficient chain is the literal 4999640321045369/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_349 : ∀ (p : 349 < 1732), cc20Eq115CoefficientQ ⟨349, p⟩ = (4999640321045369 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 350 of the coefficient chain is the literal 1999856081569691/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_350 : ∀ (p : 350 < 1732), cc20Eq115CoefficientQ ⟨350, p⟩ = (1999856081569691 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 351 of the coefficient chain is the literal 1999856035120101/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_351 : ∀ (p : 351 < 1732), cc20Eq115CoefficientQ ⟨351, p⟩ = (1999856035120101 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 352 of the coefficient chain is the literal 1249909993165513/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_352 : ∀ (p : 352 < 1732), cc20Eq115CoefficientQ ⟨352, p⟩ = (1249909993165513 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 353 of the coefficient chain is the literal 2499819929249843/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_353 : ∀ (p : 353 < 1732), cc20Eq115CoefficientQ ⟨353, p⟩ = (2499819929249843 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 354 of the coefficient chain is the literal 1999855898121051/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_354 : ∀ (p : 354 < 1732), cc20Eq115CoefficientQ ⟨354, p⟩ = (1999855898121051 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 355 of the coefficient chain is the literal 624954954132349/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_355 : ∀ (p : 355 < 1732), cc20Eq115CoefficientQ ⟨355, p⟩ = (624954954132349 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 356 of the coefficient chain is the literal 9999279043516471/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_356 : ∀ (p : 356 < 1732), cc20Eq115CoefficientQ ⟨356, p⟩ = (9999279043516471 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 357 of the coefficient chain is the literal 4999639411386133/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_357 : ∀ (p : 357 < 1732), cc20Eq115CoefficientQ ⟨357, p⟩ = (4999639411386133 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 358 of the coefficient chain is the literal 9999278603877889/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_358 : ∀ (p : 358 < 1732), cc20Eq115CoefficientQ ⟨358, p⟩ = (9999278603877889 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 359 of the coefficient chain is the literal 2499819596701839/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_359 : ∀ (p : 359 < 1732), cc20Eq115CoefficientQ ⟨359, p⟩ = (2499819596701839 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 360 of the coefficient chain is the literal 4999639085771591/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_360 : ∀ (p : 360 < 1732), cc20Eq115CoefficientQ ⟨360, p⟩ = (4999639085771591 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 361 of the coefficient chain is the literal 9999277958052019/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_361 : ∀ (p : 361 < 1732), cc20Eq115CoefficientQ ⟨361, p⟩ = (9999277958052019 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 362 of the coefficient chain is the literal 2499819436582979/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_362 : ∀ (p : 362 < 1732), cc20Eq115CoefficientQ ⟨362, p⟩ = (2499819436582979 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 363 of the coefficient chain is the literal 4999638768178311/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_363 : ∀ (p : 363 < 1732), cc20Eq115CoefficientQ ⟨363, p⟩ = (4999638768178311 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 364 of the coefficient chain is the literal 9999277328104933/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_364 : ∀ (p : 364 < 1732), cc20Eq115CoefficientQ ⟨364, p⟩ = (9999277328104933 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 365 of the coefficient chain is the literal 9999277121561763/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_365 : ∀ (p : 365 < 1732), cc20Eq115CoefficientQ ⟨365, p⟩ = (9999277121561763 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 366 of the coefficient chain is the literal 2499819229176089/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_366 : ∀ (p : 366 < 1732), cc20Eq115CoefficientQ ⟨366, p⟩ = (2499819229176089 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 367 of the coefficient chain is the literal 2499819178379823/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_367 : ∀ (p : 367 < 1732), cc20Eq115CoefficientQ ⟨367, p⟩ = (2499819178379823 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 368 of the coefficient chain is the literal 4999638255991961/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_368 : ∀ (p : 368 < 1732), cc20Eq115CoefficientQ ⟨368, p⟩ = (4999638255991961 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 369 of the coefficient chain is the literal 9999276312081767/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_369 : ∀ (p : 369 < 1732), cc20Eq115CoefficientQ ⟨369, p⟩ = (9999276312081767 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 370 of the coefficient chain is the literal 2499819028449697/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_370 : ∀ (p : 370 < 1732), cc20Eq115CoefficientQ ⟨370, p⟩ = (2499819028449697 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 371 of the coefficient chain is the literal 199985518342207/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_371 : ∀ (p : 371 < 1732), cc20Eq115CoefficientQ ⟨371, p⟩ = (199985518342207 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 372 of the coefficient chain is the literal 4999637861003711/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_372 : ∀ (p : 372 < 1732), cc20Eq115CoefficientQ ⟨372, p⟩ = (4999637861003711 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 373 of the coefficient chain is the literal 2499818882117143/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_373 : ∀ (p : 373 < 1732), cc20Eq115CoefficientQ ⟨373, p⟩ = (2499818882117143 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 374 of the coefficient chain is the literal 9999275336495783/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_374 : ∀ (p : 374 < 1732), cc20Eq115CoefficientQ ⟨374, p⟩ = (9999275336495783 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 375 of the coefficient chain is the literal 1999855029203627/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_375 : ∀ (p : 375 < 1732), cc20Eq115CoefficientQ ⟨375, p⟩ = (1999855029203627 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 376 of the coefficient chain is the literal 1249909369634139/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_376 : ∀ (p : 376 < 1732), cc20Eq115CoefficientQ ⟨376, p⟩ = (1249909369634139 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 377 of the coefficient chain is the literal 9999274769628039/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_377 : ∀ (p : 377 < 1732), cc20Eq115CoefficientQ ⟨377, p⟩ = (9999274769628039 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 378 of the coefficient chain is the literal 2499818645916897/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_378 : ∀ (p : 378 < 1732), cc20Eq115CoefficientQ ⟨378, p⟩ = (2499818645916897 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 379 of the coefficient chain is the literal 1999854879834761/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_379 : ∀ (p : 379 < 1732), cc20Eq115CoefficientQ ⟨379, p⟩ = (1999854879834761 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 380 of the coefficient chain is the literal 1249909277016777/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_380 : ∀ (p : 380 < 1732), cc20Eq115CoefficientQ ⟨380, p⟩ = (1249909277016777 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 381 of the coefficient chain is the literal 4999637017265253/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_381 : ∀ (p : 381 < 1732), cc20Eq115CoefficientQ ⟨381, p⟩ = (4999637017265253 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 382 of the coefficient chain is the literal 1249909231793597/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_382 : ∀ (p : 382 < 1732), cc20Eq115CoefficientQ ⟨382, p⟩ = (1249909231793597 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 383 of the coefficient chain is the literal 1999854735115521/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_383 : ∀ (p : 383 < 1732), cc20Eq115CoefficientQ ⟨383, p⟩ = (1999854735115521 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 384 of the coefficient chain is the literal 4999636749099511/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_384 : ∀ (p : 384 < 1732), cc20Eq115CoefficientQ ⟨384, p⟩ = (4999636749099511 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 385 of the coefficient chain is the literal 9999273322198079/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_385 : ∀ (p : 385 < 1732), cc20Eq115CoefficientQ ⟨385, p⟩ = (9999273322198079 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 386 of the coefficient chain is the literal 1999854629512649/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_386 : ∀ (p : 386 < 1732), cc20Eq115CoefficientQ ⟨386, p⟩ = (1999854629512649 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 387 of the coefficient chain is the literal 4999636487136207/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_387 : ∀ (p : 387 < 1732), cc20Eq115CoefficientQ ⟨387, p⟩ = (4999636487136207 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 388 of the coefficient chain is the literal 4999636401160027/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_388 : ∀ (p : 388 < 1732), cc20Eq115CoefficientQ ⟨388, p⟩ = (4999636401160027 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 389 of the coefficient chain is the literal 4999636315851053/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_389 : ∀ (p : 389 < 1732), cc20Eq115CoefficientQ ⟨389, p⟩ = (4999636315851053 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 390 of the coefficient chain is the literal 9999272462383599/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_390 : ∀ (p : 390 < 1732), cc20Eq115CoefficientQ ⟨390, p⟩ = (9999272462383599 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 391 of the coefficient chain is the literal 499963614718703/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_391 : ∀ (p : 391 < 1732), cc20Eq115CoefficientQ ⟨391, p⟩ = (499963614718703 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 392 of the coefficient chain is the literal 999927212763223/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_392 : ∀ (p : 392 < 1732), cc20Eq115CoefficientQ ⟨392, p⟩ = (999927212763223 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 393 of the coefficient chain is the literal 9999271962161143/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_393 : ∀ (p : 393 < 1732), cc20Eq115CoefficientQ ⟨393, p⟩ = (9999271962161143 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 394 of the coefficient chain is the literal 4999635898975573/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_394 : ∀ (p : 394 < 1732), cc20Eq115CoefficientQ ⟨394, p⟩ = (4999635898975573 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 395 of the coefficient chain is the literal 4999635817492703/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_395 : ∀ (p : 395 < 1732), cc20Eq115CoefficientQ ⟨395, p⟩ = (4999635817492703 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 396 of the coefficient chain is the literal 9999271473250163/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_396 : ∀ (p : 396 < 1732), cc20Eq115CoefficientQ ⟨396, p⟩ = (9999271473250163 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 397 of the coefficient chain is the literal 31247722852293/ 31250000000000. -/
theorem cc20Eq115CoefficientQ_branch_397 : ∀ (p : 397 < 1732), cc20Eq115CoefficientQ ⟨397, p⟩ = (31247722852293 : ℚ) /  31250000000000 :=
  fun p => by rfl

/-- Branch 398 of the coefficient chain is the literal 9999271153427883/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_398 : ∀ (p : 398 < 1732), cc20Eq115CoefficientQ ⟨398, p⟩ = (9999271153427883 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 399 of the coefficient chain is the literal 4999635497656877/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_399 : ∀ (p : 399 < 1732), cc20Eq115CoefficientQ ⟨399, p⟩ = (4999635497656877 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 400 of the coefficient chain is the literal 4999635419192599/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_400 : ∀ (p : 400 < 1732), cc20Eq115CoefficientQ ⟨400, p⟩ = (4999635419192599 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 401 of the coefficient chain is the literal 9999270682630357/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_401 : ∀ (p : 401 < 1732), cc20Eq115CoefficientQ ⟨401, p⟩ = (9999270682630357 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 402 of the coefficient chain is the literal 9999270528036057/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_402 : ∀ (p : 402 < 1732), cc20Eq115CoefficientQ ⟨402, p⟩ = (9999270528036057 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 403 of the coefficient chain is the literal 9999270374580351/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_403 : ∀ (p : 403 < 1732), cc20Eq115CoefficientQ ⟨403, p⟩ = (9999270374580351 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 404 of the coefficient chain is the literal 9999270222270343/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_404 : ∀ (p : 404 < 1732), cc20Eq115CoefficientQ ⟨404, p⟩ = (9999270222270343 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 405 of the coefficient chain is the literal 9999270071084867/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_405 : ∀ (p : 405 < 1732), cc20Eq115CoefficientQ ⟨405, p⟩ = (9999270071084867 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 406 of the coefficient chain is the literal 9999269921013211/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_406 : ∀ (p : 406 < 1732), cc20Eq115CoefficientQ ⟨406, p⟩ = (9999269921013211 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 407 of the coefficient chain is the literal 9999269772046829/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_407 : ∀ (p : 407 < 1732), cc20Eq115CoefficientQ ⟨407, p⟩ = (9999269772046829 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 408 of the coefficient chain is the literal 1999853924830041/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_408 : ∀ (p : 408 < 1732), cc20Eq115CoefficientQ ⟨408, p⟩ = (1999853924830041 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 409 of the coefficient chain is the literal 4999634738687657/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_409 : ∀ (p : 409 < 1732), cc20Eq115CoefficientQ ⟨409, p⟩ = (4999634738687657 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 410 of the coefficient chain is the literal 4999634665829639/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_410 : ∀ (p : 410 < 1732), cc20Eq115CoefficientQ ⟨410, p⟩ = (4999634665829639 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 411 of the coefficient chain is the literal 9999269187003389/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_411 : ∀ (p : 411 < 1732), cc20Eq115CoefficientQ ⟨411, p⟩ = (9999269187003389 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 412 of the coefficient chain is the literal 9999269043396711/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_412 : ∀ (p : 412 < 1732), cc20Eq115CoefficientQ ⟨412, p⟩ = (9999269043396711 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 413 of the coefficient chain is the literal 9999268900834589/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_413 : ∀ (p : 413 < 1732), cc20Eq115CoefficientQ ⟨413, p⟩ = (9999268900834589 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 414 of the coefficient chain is the literal 499963437964953/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_414 : ∀ (p : 414 < 1732), cc20Eq115CoefficientQ ⟨414, p⟩ = (499963437964953 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 415 of the coefficient chain is the literal 249981715469449/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_415 : ∀ (p : 415 < 1732), cc20Eq115CoefficientQ ⟨415, p⟩ = (249981715469449 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 416 of the coefficient chain is the literal 9999268479295671/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_416 : ∀ (p : 416 < 1732), cc20Eq115CoefficientQ ⟨416, p⟩ = (9999268479295671 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 417 of the coefficient chain is the literal 4999634170397269/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_417 : ∀ (p : 417 < 1732), cc20Eq115CoefficientQ ⟨417, p⟩ = (4999634170397269 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 418 of the coefficient chain is the literal 4999634101643829/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_418 : ∀ (p : 418 < 1732), cc20Eq115CoefficientQ ⟨418, p⟩ = (4999634101643829 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 419 of the coefficient chain is the literal 9999268066763609/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_419 : ∀ (p : 419 < 1732), cc20Eq115CoefficientQ ⟨419, p⟩ = (9999268066763609 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 420 of the coefficient chain is the literal 2499816982803491/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_420 : ∀ (p : 420 < 1732), cc20Eq115CoefficientQ ⟨420, p⟩ = (2499816982803491 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 421 of the coefficient chain is the literal 9999267796630311/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_421 : ∀ (p : 421 < 1732), cc20Eq115CoefficientQ ⟨421, p⟩ = (9999267796630311 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 422 of the coefficient chain is the literal 9999267663000343/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_422 : ∀ (p : 422 < 1732), cc20Eq115CoefficientQ ⟨422, p⟩ = (9999267663000343 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 423 of the coefficient chain is the literal 1999853506063687/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_423 : ∀ (p : 423 < 1732), cc20Eq115CoefficientQ ⟨423, p⟩ = (1999853506063687 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 424 of the coefficient chain is the literal 999926739856767/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_424 : ∀ (p : 424 < 1732), cc20Eq115CoefficientQ ⟨424, p⟩ = (999926739856767 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 425 of the coefficient chain is the literal 9999267267753299/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_425 : ∀ (p : 425 < 1732), cc20Eq115CoefficientQ ⟨425, p⟩ = (9999267267753299 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 426 of the coefficient chain is the literal 4999633568928521/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_426 : ∀ (p : 426 < 1732), cc20Eq115CoefficientQ ⟨426, p⟩ = (4999633568928521 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 427 of the coefficient chain is the literal 4999633504435661/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_427 : ∀ (p : 427 < 1732), cc20Eq115CoefficientQ ⟨427, p⟩ = (4999633504435661 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 428 of the coefficient chain is the literal 9999266880787587/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_428 : ∀ (p : 428 < 1732), cc20Eq115CoefficientQ ⟨428, p⟩ = (9999266880787587 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 429 of the coefficient chain is the literal 9999266753599617/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_429 : ∀ (p : 429 < 1732), cc20Eq115CoefficientQ ⟨429, p⟩ = (9999266753599617 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 430 of the coefficient chain is the literal 9999266627298223/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_430 : ∀ (p : 430 < 1732), cc20Eq115CoefficientQ ⟨430, p⟩ = (9999266627298223 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 431 of the coefficient chain is the literal 9999266501873669/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_431 : ∀ (p : 431 < 1732), cc20Eq115CoefficientQ ⟨431, p⟩ = (9999266501873669 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 432 of the coefficient chain is the literal 999926637732357/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_432 : ∀ (p : 432 < 1732), cc20Eq115CoefficientQ ⟨432, p⟩ = (999926637732357 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 433 of the coefficient chain is the literal 9999266253625081/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_433 : ∀ (p : 433 < 1732), cc20Eq115CoefficientQ ⟨433, p⟩ = (9999266253625081 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 434 of the coefficient chain is the literal 399970645230717/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_434 : ∀ (p : 434 < 1732), cc20Eq115CoefficientQ ⟨434, p⟩ = (399970645230717 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 435 of the coefficient chain is the literal 9999266008799019/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_435 : ∀ (p : 435 < 1732), cc20Eq115CoefficientQ ⟨435, p⟩ = (9999266008799019 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 436 of the coefficient chain is the literal 31247705898883/ 31250000000000. -/
theorem cc20Eq115CoefficientQ_branch_436 : ∀ (p : 436 < 1732), cc20Eq115CoefficientQ ⟨436, p⟩ = (31247705898883 : ℚ) /  31250000000000 :=
  fun p => by rfl

/-- Branch 437 of the coefficient chain is the literal 9999265767318333/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_437 : ∀ (p : 437 < 1732), cc20Eq115CoefficientQ ⟨437, p⟩ = (9999265767318333 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 438 of the coefficient chain is the literal 9999265647830973/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_438 : ∀ (p : 438 < 1732), cc20Eq115CoefficientQ ⟨438, p⟩ = (9999265647830973 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 439 of the coefficient chain is the literal 2499816382285583/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_439 : ∀ (p : 439 < 1732), cc20Eq115CoefficientQ ⟨439, p⟩ = (2499816382285583 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 440 of the coefficient chain is the literal 499963270563237/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_440 : ∀ (p : 440 < 1732), cc20Eq115CoefficientQ ⟨440, p⟩ = (499963270563237 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 441 of the coefficient chain is the literal 9999265294190853/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_441 : ∀ (p : 441 < 1732), cc20Eq115CoefficientQ ⟨441, p⟩ = (9999265294190853 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 442 of the coefficient chain is the literal 9999265177913971/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_442 : ∀ (p : 442 < 1732), cc20Eq115CoefficientQ ⟨442, p⟩ = (9999265177913971 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 443 of the coefficient chain is the literal 9999265062418223/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_443 : ∀ (p : 443 < 1732), cc20Eq115CoefficientQ ⟨443, p⟩ = (9999265062418223 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 444 of the coefficient chain is the literal 4999632473853197/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_444 : ∀ (p : 444 < 1732), cc20Eq115CoefficientQ ⟨444, p⟩ = (4999632473853197 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 445 of the coefficient chain is the literal 1999852966752741/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_445 : ∀ (p : 445 < 1732), cc20Eq115CoefficientQ ⟨445, p⟩ = (1999852966752741 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 446 of the coefficient chain is the literal 4999632360293927/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_446 : ∀ (p : 446 < 1732), cc20Eq115CoefficientQ ⟨446, p⟩ = (4999632360293927 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 447 of the coefficient chain is the literal 1999852921634489/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_447 : ∀ (p : 447 < 1732), cc20Eq115CoefficientQ ⟨447, p⟩ = (1999852921634489 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 448 of the coefficient chain is the literal 624954031031777/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_448 : ∀ (p : 448 < 1732), cc20Eq115CoefficientQ ⟨448, p⟩ = (624954031031777 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 449 of the coefficient chain is the literal 199985287711421/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_449 : ∀ (p : 449 < 1732), cc20Eq115CoefficientQ ⟨449, p⟩ = (199985287711421 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 450 of the coefficient chain is the literal 9999264275402913/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_450 : ∀ (p : 450 < 1732), cc20Eq115CoefficientQ ⟨450, p⟩ = (9999264275402913 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 451 of the coefficient chain is the literal 1999852833193757/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_451 : ∀ (p : 451 < 1732), cc20Eq115CoefficientQ ⟨451, p⟩ = (1999852833193757 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 452 of the coefficient chain is the literal 1249908007155637/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_452 : ∀ (p : 452 < 1732), cc20Eq115CoefficientQ ⟨452, p⟩ = (1249908007155637 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 453 of the coefficient chain is the literal 999926394924231/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_453 : ∀ (p : 453 < 1732), cc20Eq115CoefficientQ ⟨453, p⟩ = (999926394924231 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 454 of the coefficient chain is the literal 1249907980244091/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_454 : ∀ (p : 454 < 1732), cc20Eq115CoefficientQ ⟨454, p⟩ = (1249907980244091 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 455 of the coefficient chain is the literal 9999263735371443/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_455 : ∀ (p : 455 < 1732), cc20Eq115CoefficientQ ⟨455, p⟩ = (9999263735371443 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 456 of the coefficient chain is the literal 1999852725898081/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_456 : ∀ (p : 456 < 1732), cc20Eq115CoefficientQ ⟨456, p⟩ = (1999852725898081 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 457 of the coefficient chain is the literal 1249907940538061/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_457 : ∀ (p : 457 < 1732), cc20Eq115CoefficientQ ⟨457, p⟩ = (1249907940538061 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 458 of the coefficient chain is the literal 2499815854951927/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_458 : ∀ (p : 458 < 1732), cc20Eq115CoefficientQ ⟨458, p⟩ = (2499815854951927 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 459 of the coefficient chain is the literal 9999263315994227/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_459 : ∀ (p : 459 < 1732), cc20Eq115CoefficientQ ⟨459, p⟩ = (9999263315994227 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 460 of the coefficient chain is the literal 1999852642570719/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_460 : ∀ (p : 460 < 1732), cc20Eq115CoefficientQ ⟨460, p⟩ = (1999852642570719 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 461 of the coefficient chain is the literal 9999263110390757/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_461 : ∀ (p : 461 < 1732), cc20Eq115CoefficientQ ⟨461, p⟩ = (9999263110390757 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 462 of the coefficient chain is the literal 2499815752147611/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_462 : ∀ (p : 462 < 1732), cc20Eq115CoefficientQ ⟨462, p⟩ = (2499815752147611 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 463 of the coefficient chain is the literal 499963145372389/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_463 : ∀ (p : 463 < 1732), cc20Eq115CoefficientQ ⟨463, p⟩ = (499963145372389 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 464 of the coefficient chain is the literal 312476962717507/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_464 : ∀ (p : 464 < 1732), cc20Eq115CoefficientQ ⟨464, p⟩ = (312476962717507 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 465 of the coefficient chain is the literal 9999262707121479/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_465 : ∀ (p : 465 < 1732), cc20Eq115CoefficientQ ⟨465, p⟩ = (9999262707121479 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 466 of the coefficient chain is the literal 62495391299519/ 62500000000000. -/
theorem cc20Eq115CoefficientQ_branch_466 : ∀ (p : 466 < 1732), cc20Eq115CoefficientQ ⟨466, p⟩ = (62495391299519 : ℚ) /  62500000000000 :=
  fun p => by rfl

/-- Branch 467 of the coefficient chain is the literal 9999262509364553/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_467 : ∀ (p : 467 < 1732), cc20Eq115CoefficientQ ⟨467, p⟩ = (9999262509364553 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 468 of the coefficient chain is the literal 4999631205718893/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_468 : ∀ (p : 468 < 1732), cc20Eq115CoefficientQ ⟨468, p⟩ = (4999631205718893 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 469 of the coefficient chain is the literal 99992623141433/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_469 : ∀ (p : 469 < 1732), cc20Eq115CoefficientQ ⟨469, p⟩ = (99992623141433 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 470 of the coefficient chain is the literal 9999262217451779/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_470 : ∀ (p : 470 < 1732), cc20Eq115CoefficientQ ⟨470, p⟩ = (9999262217451779 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 471 of the coefficient chain is the literal 999926212138583/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_471 : ∀ (p : 471 < 1732), cc20Eq115CoefficientQ ⟨471, p⟩ = (999926212138583 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 472 of the coefficient chain is the literal 9999262025932817/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_472 : ∀ (p : 472 < 1732), cc20Eq115CoefficientQ ⟨472, p⟩ = (9999262025932817 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 473 of the coefficient chain is the literal 9999261931084219/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_473 : ∀ (p : 473 < 1732), cc20Eq115CoefficientQ ⟨473, p⟩ = (9999261931084219 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 474 of the coefficient chain is the literal 999926183683527/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_474 : ∀ (p : 474 < 1732), cc20Eq115CoefficientQ ⟨474, p⟩ = (999926183683527 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 475 of the coefficient chain is the literal 9999261743182727/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_475 : ∀ (p : 475 < 1732), cc20Eq115CoefficientQ ⟨475, p⟩ = (9999261743182727 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 476 of the coefficient chain is the literal 9999261650119771/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_476 : ∀ (p : 476 < 1732), cc20Eq115CoefficientQ ⟨476, p⟩ = (9999261650119771 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 477 of the coefficient chain is the literal 9999261557634553/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_477 : ∀ (p : 477 < 1732), cc20Eq115CoefficientQ ⟨477, p⟩ = (9999261557634553 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 478 of the coefficient chain is the literal 9999261465750229/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_478 : ∀ (p : 478 < 1732), cc20Eq115CoefficientQ ⟨478, p⟩ = (9999261465750229 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 479 of the coefficient chain is the literal 624953835901709/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_479 : ∀ (p : 479 < 1732), cc20Eq115CoefficientQ ⟨479, p⟩ = (624953835901709 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 480 of the coefficient chain is the literal 9999261283678119/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_480 : ∀ (p : 480 < 1732), cc20Eq115CoefficientQ ⟨480, p⟩ = (9999261283678119 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 481 of the coefficient chain is the literal 2499815298373543/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_481 : ∀ (p : 481 < 1732), cc20Eq115CoefficientQ ⟨481, p⟩ = (2499815298373543 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 482 of the coefficient chain is the literal 9999261103869699/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_482 : ∀ (p : 482 < 1732), cc20Eq115CoefficientQ ⟨482, p⟩ = (9999261103869699 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 483 of the coefficient chain is the literal 9999261014806607/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_483 : ∀ (p : 483 < 1732), cc20Eq115CoefficientQ ⟨483, p⟩ = (9999261014806607 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 484 of the coefficient chain is the literal 9999260926293307/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_484 : ∀ (p : 484 < 1732), cc20Eq115CoefficientQ ⟨484, p⟩ = (9999260926293307 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 485 of the coefficient chain is the literal 9999260838328669/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_485 : ∀ (p : 485 < 1732), cc20Eq115CoefficientQ ⟨485, p⟩ = (9999260838328669 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 486 of the coefficient chain is the literal 9999260750905539/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_486 : ∀ (p : 486 < 1732), cc20Eq115CoefficientQ ⟨486, p⟩ = (9999260750905539 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 487 of the coefficient chain is the literal 4999630332012331/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_487 : ∀ (p : 487 < 1732), cc20Eq115CoefficientQ ⟨487, p⟩ = (4999630332012331 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 488 of the coefficient chain is the literal 9999260577676157/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_488 : ∀ (p : 488 < 1732), cc20Eq115CoefficientQ ⟨488, p⟩ = (9999260577676157 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 489 of the coefficient chain is the literal 1249907561482273/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_489 : ∀ (p : 489 < 1732), cc20Eq115CoefficientQ ⟨489, p⟩ = (1249907561482273 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 490 of the coefficient chain is the literal 199985208131259/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_490 : ∀ (p : 490 < 1732), cc20Eq115CoefficientQ ⟨490, p⟩ = (199985208131259 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 491 of the coefficient chain is the literal 9999260321792851/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_491 : ∀ (p : 491 < 1732), cc20Eq115CoefficientQ ⟨491, p⟩ = (9999260321792851 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 492 of the coefficient chain is the literal 2499815059385243/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_492 : ∀ (p : 492 < 1732), cc20Eq115CoefficientQ ⟨492, p⟩ = (2499815059385243 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 493 of the coefficient chain is the literal 9999260153798903/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_493 : ∀ (p : 493 < 1732), cc20Eq115CoefficientQ ⟨493, p⟩ = (9999260153798903 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 494 of the coefficient chain is the literal 9999260070567687/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_494 : ∀ (p : 494 < 1732), cc20Eq115CoefficientQ ⟨494, p⟩ = (9999260070567687 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 495 of the coefficient chain is the literal 4999629993920967/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_495 : ∀ (p : 495 < 1732), cc20Eq115CoefficientQ ⟨495, p⟩ = (4999629993920967 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 496 of the coefficient chain is the literal 1249907488201929/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_496 : ∀ (p : 496 < 1732), cc20Eq115CoefficientQ ⟨496, p⟩ = (1249907488201929 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 497 of the coefficient chain is the literal 9999259823887583/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_497 : ∀ (p : 497 < 1732), cc20Eq115CoefficientQ ⟨497, p⟩ = (9999259823887583 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 498 of the coefficient chain is the literal 9999259742651967/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_498 : ∀ (p : 498 < 1732), cc20Eq115CoefficientQ ⟨498, p⟩ = (9999259742651967 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 499 of the coefficient chain is the literal 1999851932380819/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_499 : ∀ (p : 499 < 1732), cc20Eq115CoefficientQ ⟨499, p⟩ = (1999851932380819 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 500 of the coefficient chain is the literal 9999259581642831/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_500 : ∀ (p : 500 < 1732), cc20Eq115CoefficientQ ⟨500, p⟩ = (9999259581642831 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 501 of the coefficient chain is the literal 9999259501859851/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_501 : ∀ (p : 501 < 1732), cc20Eq115CoefficientQ ⟨501, p⟩ = (9999259501859851 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 502 of the coefficient chain is the literal 9999259422561059/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_502 : ∀ (p : 502 < 1732), cc20Eq115CoefficientQ ⟨502, p⟩ = (9999259422561059 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 503 of the coefficient chain is the literal 499962967186619/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_503 : ∀ (p : 503 < 1732), cc20Eq115CoefficientQ ⟨503, p⟩ = (499962967186619 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 504 of the coefficient chain is the literal 9999259265372101/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_504 : ∀ (p : 504 < 1732), cc20Eq115CoefficientQ ⟨504, p⟩ = (9999259265372101 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 505 of the coefficient chain is the literal 9999259187477553/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_505 : ∀ (p : 505 < 1732), cc20Eq115CoefficientQ ⟨505, p⟩ = (9999259187477553 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 506 of the coefficient chain is the literal 1249907388755141/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_506 : ∀ (p : 506 < 1732), cc20Eq115CoefficientQ ⟨506, p⟩ = (1249907388755141 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 507 of the coefficient chain is the literal 2499814758267707/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_507 : ∀ (p : 507 < 1732), cc20Eq115CoefficientQ ⟨507, p⟩ = (2499814758267707 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 508 of the coefficient chain is the literal 2499814739138237/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_508 : ∀ (p : 508 < 1732), cc20Eq115CoefficientQ ⟨508, p⟩ = (2499814739138237 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 509 of the coefficient chain is the literal 1999851776097483/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_509 : ∀ (p : 509 < 1732), cc20Eq115CoefficientQ ⟨509, p⟩ = (1999851776097483 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 510 of the coefficient chain is the literal 4999629402434919/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_510 : ∀ (p : 510 < 1732), cc20Eq115CoefficientQ ⟨510, p⟩ = (4999629402434919 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 511 of the coefficient chain is the literal 4999629364849331/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_511 : ∀ (p : 511 < 1732), cc20Eq115CoefficientQ ⟨511, p⟩ = (4999629364849331 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 512 of the coefficient chain is the literal 99992586549659/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_512 : ∀ (p : 512 < 1732), cc20Eq115CoefficientQ ⟨512, p⟩ = (99992586549659 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 513 of the coefficient chain is the literal 9999258580669589/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_513 : ∀ (p : 513 < 1732), cc20Eq115CoefficientQ ⟨513, p⟩ = (9999258580669589 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 514 of the coefficient chain is the literal 15623841416893/ 15625000000000. -/
theorem cc20Eq115CoefficientQ_branch_514 : ∀ (p : 514 < 1732), cc20Eq115CoefficientQ ⟨514, p⟩ = (15623841416893 : ℚ) /  15625000000000 :=
  fun p => by rfl

/-- Branch 515 of the coefficient chain is the literal 199985168667657/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_515 : ∀ (p : 515 < 1732), cc20Eq115CoefficientQ ⟨515, p⟩ = (199985168667657 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 516 of the coefficient chain is the literal 4999629180190271/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_516 : ∀ (p : 516 < 1732), cc20Eq115CoefficientQ ⟨516, p⟩ = (4999629180190271 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 517 of the coefficient chain is the literal 9999258287803253/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_517 : ∀ (p : 517 < 1732), cc20Eq115CoefficientQ ⟨517, p⟩ = (9999258287803253 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 518 of the coefficient chain is the literal 999925821564863/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_518 : ∀ (p : 518 < 1732), cc20Eq115CoefficientQ ⟨518, p⟩ = (999925821564863 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 519 of the coefficient chain is the literal 4999629071955751/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_519 : ∀ (p : 519 < 1732), cc20Eq115CoefficientQ ⟨519, p⟩ = (4999629071955751 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 520 of the coefficient chain is the literal 1999851614517611/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_520 : ∀ (p : 520 < 1732), cc20Eq115CoefficientQ ⟨520, p⟩ = (1999851614517611 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 521 of the coefficient chain is the literal 9999258001675179/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_521 : ∀ (p : 521 < 1732), cc20Eq115CoefficientQ ⟨521, p⟩ = (9999258001675179 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 522 of the coefficient chain is the literal 499962896558577/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_522 : ∀ (p : 522 < 1732), cc20Eq115CoefficientQ ⟨522, p⟩ = (499962896558577 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 523 of the coefficient chain is the literal 499962893055393/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_523 : ∀ (p : 523 < 1732), cc20Eq115CoefficientQ ⟨523, p⟩ = (499962893055393 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 524 of the coefficient chain is the literal 1249907223923403/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_524 : ∀ (p : 524 < 1732), cc20Eq115CoefficientQ ⟨524, p⟩ = (1249907223923403 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 525 of the coefficient chain is the literal 1999851544417609/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_525 : ∀ (p : 525 < 1732), cc20Eq115CoefficientQ ⟨525, p⟩ = (1999851544417609 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 526 of the coefficient chain is the literal 9999257653188143/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_526 : ∀ (p : 526 < 1732), cc20Eq115CoefficientQ ⟨526, p⟩ = (9999257653188143 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 527 of the coefficient chain is the literal 2499814396169991/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_527 : ∀ (p : 527 < 1732), cc20Eq115CoefficientQ ⟨527, p⟩ = (2499814396169991 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 528 of the coefficient chain is the literal 9999257516561997/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_528 : ∀ (p : 528 < 1732), cc20Eq115CoefficientQ ⟨528, p⟩ = (9999257516561997 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 529 of the coefficient chain is the literal 9999257448838373/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_529 : ∀ (p : 529 < 1732), cc20Eq115CoefficientQ ⟨529, p⟩ = (9999257448838373 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 530 of the coefficient chain is the literal 2499814345370417/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_530 : ∀ (p : 530 < 1732), cc20Eq115CoefficientQ ⟨530, p⟩ = (2499814345370417 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 531 of the coefficient chain is the literal 2499814328630873/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_531 : ∀ (p : 531 < 1732), cc20Eq115CoefficientQ ⟨531, p⟩ = (2499814328630873 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 532 of the coefficient chain is the literal 999925724793751/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_532 : ∀ (p : 532 < 1732), cc20Eq115CoefficientQ ⟨532, p⟩ = (999925724793751 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 533 of the coefficient chain is the literal 1249907147716023/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_533 : ∀ (p : 533 < 1732), cc20Eq115CoefficientQ ⟨533, p⟩ = (1249907147716023 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 534 of the coefficient chain is the literal 4999628557945383/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_534 : ∀ (p : 534 < 1732), cc20Eq115CoefficientQ ⟨534, p⟩ = (4999628557945383 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 535 of the coefficient chain is the literal 4999628525213767/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_535 : ∀ (p : 535 < 1732), cc20Eq115CoefficientQ ⟨535, p⟩ = (4999628525213767 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 536 of the coefficient chain is the literal 9999256985326263/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_536 : ∀ (p : 536 < 1732), cc20Eq115CoefficientQ ⟨536, p⟩ = (9999256985326263 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 537 of the coefficient chain is the literal 9999256920591781/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_537 : ∀ (p : 537 < 1732), cc20Eq115CoefficientQ ⟨537, p⟩ = (9999256920591781 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 538 of the coefficient chain is the literal 9999256856218537/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_538 : ∀ (p : 538 < 1732), cc20Eq115CoefficientQ ⟨538, p⟩ = (9999256856218537 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 539 of the coefficient chain is the literal 2499814198053463/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_539 : ∀ (p : 539 < 1732), cc20Eq115CoefficientQ ⟨539, p⟩ = (2499814198053463 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 540 of the coefficient chain is the literal 399970269142033/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_540 : ∀ (p : 540 < 1732), cc20Eq115CoefficientQ ⟨540, p⟩ = (399970269142033 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 541 of the coefficient chain is the literal 9999256665249201/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_541 : ∀ (p : 541 < 1732), cc20Eq115CoefficientQ ⟨541, p⟩ = (9999256665249201 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 542 of the coefficient chain is the literal 31247676882181/ 31250000000000. -/
theorem cc20Eq115CoefficientQ_branch_542 : ∀ (p : 542 < 1732), cc20Eq115CoefficientQ ⟨542, p⟩ = (31247676882181 : ℚ) /  31250000000000 :=
  fun p => by rfl

/-- Branch 543 of the coefficient chain is the literal 9999256539694407/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_543 : ∀ (p : 543 < 1732), cc20Eq115CoefficientQ ⟨543, p⟩ = (9999256539694407 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 544 of the coefficient chain is the literal 4999628238720927/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_544 : ∀ (p : 544 < 1732), cc20Eq115CoefficientQ ⟨544, p⟩ = (4999628238720927 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 545 of the coefficient chain is the literal 2499814103881951/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_545 : ∀ (p : 545 < 1732), cc20Eq115CoefficientQ ⟨545, p⟩ = (2499814103881951 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 546 of the coefficient chain is the literal 2499814088490003/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_546 : ∀ (p : 546 < 1732), cc20Eq115CoefficientQ ⟨546, p⟩ = (2499814088490003 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 547 of the coefficient chain is the literal 9999256292728843/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_547 : ∀ (p : 547 < 1732), cc20Eq115CoefficientQ ⟨547, p⟩ = (9999256292728843 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 548 of the coefficient chain is the literal 9999256231830289/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_548 : ∀ (p : 548 < 1732), cc20Eq115CoefficientQ ⟨548, p⟩ = (9999256231830289 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 549 of the coefficient chain is the literal 624953510704327/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_549 : ∀ (p : 549 < 1732), cc20Eq115CoefficientQ ⟨549, p⟩ = (624953510704327 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 550 of the coefficient chain is the literal 399970244441617/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_550 : ∀ (p : 550 < 1732), cc20Eq115CoefficientQ ⟨550, p⟩ = (399970244441617 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 551 of the coefficient chain is the literal 1249907006392373/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_551 : ∀ (p : 551 < 1732), cc20Eq115CoefficientQ ⟨551, p⟩ = (1249907006392373 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 552 of the coefficient chain is the literal 9999255991565039/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_552 : ∀ (p : 552 < 1732), cc20Eq115CoefficientQ ⟨552, p⟩ = (9999255991565039 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 553 of the coefficient chain is the literal 4999627966157173/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_553 : ∀ (p : 553 < 1732), cc20Eq115CoefficientQ ⟨553, p⟩ = (4999627966157173 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 554 of the coefficient chain is the literal 1999851174677233/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_554 : ∀ (p : 554 < 1732), cc20Eq115CoefficientQ ⟨554, p⟩ = (1999851174677233 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 555 of the coefficient chain is the literal 4999627907388793/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_555 : ∀ (p : 555 < 1732), cc20Eq115CoefficientQ ⟨555, p⟩ = (4999627907388793 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 556 of the coefficient chain is the literal 49996278782441/ 50000000000000. -/
theorem cc20Eq115CoefficientQ_branch_556 : ∀ (p : 556 < 1732), cc20Eq115CoefficientQ ⟨556, p⟩ = (49996278782441 : ℚ) /  50000000000000 :=
  fun p => by rfl

/-- Branch 557 of the coefficient chain is the literal 1999851139702263/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_557 : ∀ (p : 557 < 1732), cc20Eq115CoefficientQ ⟨557, p⟩ = (1999851139702263 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 558 of the coefficient chain is the literal 9999255640848209/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_558 : ∀ (p : 558 < 1732), cc20Eq115CoefficientQ ⟨558, p⟩ = (9999255640848209 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 559 of the coefficient chain is the literal 4999627791748697/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_559 : ∀ (p : 559 < 1732), cc20Eq115CoefficientQ ⟨559, p⟩ = (4999627791748697 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 560 of the coefficient chain is the literal 19529795950101/ 19531250000000. -/
theorem cc20Eq115CoefficientQ_branch_560 : ∀ (p : 560 < 1732), cc20Eq115CoefficientQ ⟨560, p⟩ = (19529795950101 : ℚ) /  19531250000000 :=
  fun p => by rfl

/-- Branch 561 of the coefficient chain is the literal 4999627734858089/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_561 : ∀ (p : 561 < 1732), cc20Eq115CoefficientQ ⟨561, p⟩ = (4999627734858089 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 562 of the coefficient chain is the literal 1999851082656731/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_562 : ∀ (p : 562 < 1732), cc20Eq115CoefficientQ ⟨562, p⟩ = (1999851082656731 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 563 of the coefficient chain is the literal 9999255357152503/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_563 : ∀ (p : 563 < 1732), cc20Eq115CoefficientQ ⟨563, p⟩ = (9999255357152503 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 564 of the coefficient chain is the literal 9999255301320709/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_564 : ∀ (p : 564 < 1732), cc20Eq115CoefficientQ ⟨564, p⟩ = (9999255301320709 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 565 of the coefficient chain is the literal 9999255245788121/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_565 : ∀ (p : 565 < 1732), cc20Eq115CoefficientQ ⟨565, p⟩ = (9999255245788121 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 566 of the coefficient chain is the literal 4999627595274903/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_566 : ∀ (p : 566 < 1732), cc20Eq115CoefficientQ ⟨566, p⟩ = (4999627595274903 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 567 of the coefficient chain is the literal 1999851027121281/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_567 : ∀ (p : 567 < 1732), cc20Eq115CoefficientQ ⟨567, p⟩ = (1999851027121281 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 568 of the coefficient chain is the literal 2499813770238371/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_568 : ∀ (p : 568 < 1732), cc20Eq115CoefficientQ ⟨568, p⟩ = (2499813770238371 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 569 of the coefficient chain is the literal 9999255026590403/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_569 : ∀ (p : 569 < 1732), cc20Eq115CoefficientQ ⟨569, p⟩ = (9999255026590403 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 570 of the coefficient chain is the literal 1249906871564159/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_570 : ∀ (p : 570 < 1732), cc20Eq115CoefficientQ ⟨570, p⟩ = (1249906871564159 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 571 of the coefficient chain is the literal 2499813729680681/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_571 : ∀ (p : 571 < 1732), cc20Eq115CoefficientQ ⟨571, p⟩ = (2499813729680681 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 572 of the coefficient chain is the literal 124990685815187/ 125000000000000. -/
theorem cc20Eq115CoefficientQ_branch_572 : ∀ (p : 572 < 1732), cc20Eq115CoefficientQ ⟨572, p⟩ = (124990685815187 : ℚ) /  125000000000000 :=
  fun p => by rfl

/-- Branch 573 of the coefficient chain is the literal 4999627405994357/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_573 : ∀ (p : 573 < 1732), cc20Eq115CoefficientQ ⟨573, p⟩ = (4999627405994357 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 574 of the coefficient chain is the literal 9999254759043693/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_574 : ∀ (p : 574 < 1732), cc20Eq115CoefficientQ ⟨574, p⟩ = (9999254759043693 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 575 of the coefficient chain is the literal 4999627353188091/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_575 : ∀ (p : 575 < 1732), cc20Eq115CoefficientQ ⟨575, p⟩ = (4999627353188091 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 576 of the coefficient chain is the literal 4999627326991609/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_576 : ∀ (p : 576 < 1732), cc20Eq115CoefficientQ ⟨576, p⟩ = (4999627326991609 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 577 of the coefficient chain is the literal 9999254601863931/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_577 : ∀ (p : 577 < 1732), cc20Eq115CoefficientQ ⟨577, p⟩ = (9999254601863931 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 578 of the coefficient chain is the literal 9999254550015803/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_578 : ∀ (p : 578 < 1732), cc20Eq115CoefficientQ ⟨578, p⟩ = (9999254550015803 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 579 of the coefficient chain is the literal 9999254498428799/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_579 : ∀ (p : 579 < 1732), cc20Eq115CoefficientQ ⟨579, p⟩ = (9999254498428799 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 580 of the coefficient chain is the literal 39059587684089/ 39062500000000. -/
theorem cc20Eq115CoefficientQ_branch_580 : ∀ (p : 580 < 1732), cc20Eq115CoefficientQ ⟨580, p⟩ = (39059587684089 : ℚ) /  39062500000000 :=
  fun p => by rfl

/-- Branch 581 of the coefficient chain is the literal 2499813599021441/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_581 : ∀ (p : 581 < 1732), cc20Eq115CoefficientQ ⟨581, p⟩ = (2499813599021441 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 582 of the coefficient chain is the literal 9999254345307861/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_582 : ∀ (p : 582 < 1732), cc20Eq115CoefficientQ ⟨582, p⟩ = (9999254345307861 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 583 of the coefficient chain is the literal 4999627147396481/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_583 : ∀ (p : 583 < 1732), cc20Eq115CoefficientQ ⟨583, p⟩ = (4999627147396481 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 584 of the coefficient chain is the literal 499962712226953/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_584 : ∀ (p : 584 < 1732), cc20Eq115CoefficientQ ⟨584, p⟩ = (499962712226953 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 585 of the coefficient chain is the literal 499962709727103/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_585 : ∀ (p : 585 < 1732), cc20Eq115CoefficientQ ⟨585, p⟩ = (499962709727103 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 586 of the coefficient chain is the literal 4999627072402651/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_586 : ∀ (p : 586 < 1732), cc20Eq115CoefficientQ ⟨586, p⟩ = (4999627072402651 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 587 of the coefficient chain is the literal 9999254095322939/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_587 : ∀ (p : 587 < 1732), cc20Eq115CoefficientQ ⟨587, p⟩ = (9999254095322939 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 588 of the coefficient chain is the literal 1999850809218859/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_588 : ∀ (p : 588 < 1732), cc20Eq115CoefficientQ ⟨588, p⟩ = (1999850809218859 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 589 of the coefficient chain is the literal 4999626998558777/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_589 : ∀ (p : 589 < 1732), cc20Eq115CoefficientQ ⟨589, p⟩ = (4999626998558777 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 590 of the coefficient chain is the literal 3999701579357/ 4000000000000. -/
theorem cc20Eq115CoefficientQ_branch_590 : ∀ (p : 590 < 1732), cc20Eq115CoefficientQ ⟨590, p⟩ = (3999701579357 : ℚ) /  4000000000000 :=
  fun p => by rfl

/-- Branch 591 of the coefficient chain is the literal 2499813474978707/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_591 : ∀ (p : 591 < 1732), cc20Eq115CoefficientQ ⟨591, p⟩ = (2499813474978707 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 592 of the coefficient chain is the literal 4999626925843619/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_592 : ∀ (p : 592 < 1732), cc20Eq115CoefficientQ ⟨592, p⟩ = (4999626925843619 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 593 of the coefficient chain is the literal 249981345092513/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_593 : ∀ (p : 593 < 1732), cc20Eq115CoefficientQ ⟨593, p⟩ = (249981345092513 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 594 of the coefficient chain is the literal 9999253755957893/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_594 : ∀ (p : 594 < 1732), cc20Eq115CoefficientQ ⟨594, p⟩ = (9999253755957893 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 595 of the coefficient chain is the literal 78119169597351/ 78125000000000. -/
theorem cc20Eq115CoefficientQ_branch_595 : ∀ (p : 595 < 1732), cc20Eq115CoefficientQ ⟨595, p⟩ = (78119169597351 : ℚ) /  78125000000000 :=
  fun p => by rfl

/-- Branch 596 of the coefficient chain is the literal 999925366120279/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_596 : ∀ (p : 596 < 1732), cc20Eq115CoefficientQ ⟨596, p⟩ = (999925366120279 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 597 of the coefficient chain is the literal 9999253614183209/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_597 : ∀ (p : 597 < 1732), cc20Eq115CoefficientQ ⟨597, p⟩ = (9999253614183209 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 598 of the coefficient chain is the literal 124990669592521/ 125000000000000. -/
theorem cc20Eq115CoefficientQ_branch_598 : ∀ (p : 598 < 1732), cc20Eq115CoefficientQ ⟨598, p⟩ = (124990669592521 : ℚ) /  125000000000000 :=
  fun p => by rfl

/-- Branch 599 of the coefficient chain is the literal 156238336263367/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_599 : ∀ (p : 599 < 1732), cc20Eq115CoefficientQ ⟨599, p⟩ = (156238336263367 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 600 of the coefficient chain is the literal 9999253474543867/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_600 : ∀ (p : 600 < 1732), cc20Eq115CoefficientQ ⟨600, p⟩ = (9999253474543867 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 601 of the coefficient chain is the literal 9999253428466471/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_601 : ∀ (p : 601 < 1732), cc20Eq115CoefficientQ ⟨601, p⟩ = (9999253428466471 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 602 of the coefficient chain is the literal 9999253382617743/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_602 : ∀ (p : 602 < 1732), cc20Eq115CoefficientQ ⟨602, p⟩ = (9999253382617743 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 603 of the coefficient chain is the literal 999925333700033/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_603 : ∀ (p : 603 < 1732), cc20Eq115CoefficientQ ⟨603, p⟩ = (999925333700033 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 604 of the coefficient chain is the literal 9999253291612233/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_604 : ∀ (p : 604 < 1732), cc20Eq115CoefficientQ ⟨604, p⟩ = (9999253291612233 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 605 of the coefficient chain is the literal 999925324644679/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_605 : ∀ (p : 605 < 1732), cc20Eq115CoefficientQ ⟨605, p⟩ = (999925324644679 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 606 of the coefficient chain is the literal 9999253201509697/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_606 : ∀ (p : 606 < 1732), cc20Eq115CoefficientQ ⟨606, p⟩ = (9999253201509697 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 607 of the coefficient chain is the literal 499962657839753/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_607 : ∀ (p : 607 < 1732), cc20Eq115CoefficientQ ⟨607, p⟩ = (499962657839753 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 608 of the coefficient chain is the literal 9999253112298979/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_608 : ∀ (p : 608 < 1732), cc20Eq115CoefficientQ ⟨608, p⟩ = (9999253112298979 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 609 of the coefficient chain is the literal 999925306802763/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_609 : ∀ (p : 609 < 1732), cc20Eq115CoefficientQ ⟨609, p⟩ = (999925306802763 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 610 of the coefficient chain is the literal 1249906627997001/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_610 : ∀ (p : 610 < 1732), cc20Eq115CoefficientQ ⟨610, p⟩ = (1249906627997001 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 611 of the coefficient chain is the literal 1249906622517797/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_611 : ∀ (p : 611 < 1732), cc20Eq115CoefficientQ ⟨611, p⟩ = (1249906622517797 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 612 of the coefficient chain is the literal 999925293652373/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_612 : ∀ (p : 612 < 1732), cc20Eq115CoefficientQ ⟨612, p⟩ = (999925293652373 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 613 of the coefficient chain is the literal 4999626446559821/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_613 : ∀ (p : 613 < 1732), cc20Eq115CoefficientQ ⟨613, p⟩ = (4999626446559821 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 614 of the coefficient chain is the literal 4999626424967187/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_614 : ∀ (p : 614 < 1732), cc20Eq115CoefficientQ ⟨614, p⟩ = (4999626424967187 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 615 of the coefficient chain is the literal 312476650217383/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_615 : ∀ (p : 615 < 1732), cc20Eq115CoefficientQ ⟨615, p⟩ = (312476650217383 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 616 of the coefficient chain is the literal 2499813191047563/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_616 : ∀ (p : 616 < 1732), cc20Eq115CoefficientQ ⟨616, p⟩ = (2499813191047563 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 617 of the coefficient chain is the literal 2499813180408293/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_617 : ∀ (p : 617 < 1732), cc20Eq115CoefficientQ ⟨617, p⟩ = (2499813180408293 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 618 of the coefficient chain is the literal 9999252679285163/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_618 : ∀ (p : 618 < 1732), cc20Eq115CoefficientQ ⟨618, p⟩ = (9999252679285163 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 619 of the coefficient chain is the literal 999925263714407/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_619 : ∀ (p : 619 < 1732), cc20Eq115CoefficientQ ⟨619, p⟩ = (999925263714407 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 620 of the coefficient chain is the literal 624953287200153/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_620 : ∀ (p : 620 < 1732), cc20Eq115CoefficientQ ⟨620, p⟩ = (624953287200153 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 621 of the coefficient chain is the literal 2499813138367983/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_621 : ∀ (p : 621 < 1732), cc20Eq115CoefficientQ ⟨621, p⟩ = (2499813138367983 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 622 of the coefficient chain is the literal 9999252511944009/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_622 : ∀ (p : 622 < 1732), cc20Eq115CoefficientQ ⟨622, p⟩ = (9999252511944009 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 623 of the coefficient chain is the literal 4999626235309071/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_623 : ∀ (p : 623 < 1732), cc20Eq115CoefficientQ ⟨623, p⟩ = (4999626235309071 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 624 of the coefficient chain is the literal 4999626214745791/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_624 : ∀ (p : 624 < 1732), cc20Eq115CoefficientQ ⟨624, p⟩ = (4999626214745791 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 625 of the coefficient chain is the literal 9999252388563861/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_625 : ∀ (p : 625 < 1732), cc20Eq115CoefficientQ ⟨625, p⟩ = (9999252388563861 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 626 of the coefficient chain is the literal 999925234783323/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_626 : ∀ (p : 626 < 1732), cc20Eq115CoefficientQ ⟨626, p⟩ = (999925234783323 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 627 of the coefficient chain is the literal 1999850461460269/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_627 : ∀ (p : 627 < 1732), cc20Eq115CoefficientQ ⟨627, p⟩ = (1999850461460269 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 628 of the coefficient chain is the literal 9999252266963793/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_628 : ∀ (p : 628 < 1732), cc20Eq115CoefficientQ ⟨628, p⟩ = (9999252266963793 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 629 of the coefficient chain is the literal 9999252226821139/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_629 : ∀ (p : 629 < 1732), cc20Eq115CoefficientQ ⟨629, p⟩ = (9999252226821139 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 630 of the coefficient chain is the literal 1249906523359309/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_630 : ∀ (p : 630 < 1732), cc20Eq115CoefficientQ ⟨630, p⟩ = (1249906523359309 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 631 of the coefficient chain is the literal 9999252147098069/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_631 : ∀ (p : 631 < 1732), cc20Eq115CoefficientQ ⟨631, p⟩ = (9999252147098069 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 632 of the coefficient chain is the literal 1999850421504743/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_632 : ∀ (p : 632 < 1732), cc20Eq115CoefficientQ ⟨632, p⟩ = (1999850421504743 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 633 of the coefficient chain is the literal 624953254259431/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_633 : ∀ (p : 633 < 1732), cc20Eq115CoefficientQ ⟨633, p⟩ = (624953254259431 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 634 of the coefficient chain is the literal 2499813007240013/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_634 : ∀ (p : 634 < 1732), cc20Eq115CoefficientQ ⟨634, p⟩ = (2499813007240013 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 635 of the coefficient chain is the literal 1999850397995089/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_635 : ∀ (p : 635 < 1732), cc20Eq115CoefficientQ ⟨635, p⟩ = (1999850397995089 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 636 of the coefficient chain is the literal 9999251951136123/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_636 : ∀ (p : 636 < 1732), cc20Eq115CoefficientQ ⟨636, p⟩ = (9999251951136123 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 637 of the coefficient chain is the literal 9999251912500193/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_637 : ∀ (p : 637 < 1732), cc20Eq115CoefficientQ ⟨637, p⟩ = (9999251912500193 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 638 of the coefficient chain is the literal 4999625937025873/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_638 : ∀ (p : 638 < 1732), cc20Eq115CoefficientQ ⟨638, p⟩ = (4999625937025873 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 639 of the coefficient chain is the literal 2499812958944633/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_639 : ∀ (p : 639 < 1732), cc20Eq115CoefficientQ ⟨639, p⟩ = (2499812958944633 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 640 of the coefficient chain is the literal 9999251797692933/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_640 : ∀ (p : 640 < 1732), cc20Eq115CoefficientQ ⟨640, p⟩ = (9999251797692933 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 641 of the coefficient chain is the literal 999925175978539/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_641 : ∀ (p : 641 < 1732), cc20Eq115CoefficientQ ⟨641, p⟩ = (999925175978539 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 642 of the coefficient chain is the literal 9999251722059471/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_642 : ∀ (p : 642 < 1732), cc20Eq115CoefficientQ ⟨642, p⟩ = (9999251722059471 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 643 of the coefficient chain is the literal 9999251684519987/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_643 : ∀ (p : 643 < 1732), cc20Eq115CoefficientQ ⟨643, p⟩ = (9999251684519987 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 644 of the coefficient chain is the literal 399970065884833/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_644 : ∀ (p : 644 < 1732), cc20Eq115CoefficientQ ⟨644, p⟩ = (399970065884833 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 645 of the coefficient chain is the literal 499962580496131/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_645 : ∀ (p : 645 < 1732), cc20Eq115CoefficientQ ⟨645, p⟩ = (499962580496131 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 646 of the coefficient chain is the literal 4999625786449927/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_646 : ∀ (p : 646 < 1732), cc20Eq115CoefficientQ ⟨646, p⟩ = (4999625786449927 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 647 of the coefficient chain is the literal 4999625768024777/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_647 : ∀ (p : 647 < 1732), cc20Eq115CoefficientQ ⟨647, p⟩ = (4999625768024777 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 648 of the coefficient chain is the literal 2499812874842569/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_648 : ∀ (p : 648 < 1732), cc20Eq115CoefficientQ ⟨648, p⟩ = (2499812874842569 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 649 of the coefficient chain is the literal 4999625731431579/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_649 : ∀ (p : 649 < 1732), cc20Eq115CoefficientQ ⟨649, p⟩ = (4999625731431579 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 650 of the coefficient chain is the literal 9999251426524501/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_650 : ∀ (p : 650 < 1732), cc20Eq115CoefficientQ ⟨650, p⟩ = (9999251426524501 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 651 of the coefficient chain is the literal 249981284758917/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_651 : ∀ (p : 651 < 1732), cc20Eq115CoefficientQ ⟨651, p⟩ = (249981284758917 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 652 of the coefficient chain is the literal 9999251354355159/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_652 : ∀ (p : 652 < 1732), cc20Eq115CoefficientQ ⟨652, p⟩ = (9999251354355159 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 653 of the coefficient chain is the literal 4999625659261289/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_653 : ∀ (p : 653 < 1732), cc20Eq115CoefficientQ ⟨653, p⟩ = (4999625659261289 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 654 of the coefficient chain is the literal 2499812820714039/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_654 : ∀ (p : 654 < 1732), cc20Eq115CoefficientQ ⟨654, p⟩ = (2499812820714039 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 655 of the coefficient chain is the literal 4999625623676651/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_655 : ∀ (p : 655 < 1732), cc20Eq115CoefficientQ ⟨655, p⟩ = (4999625623676651 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 656 of the coefficient chain is the literal 4999625606007689/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_656 : ∀ (p : 656 < 1732), cc20Eq115CoefficientQ ⟨656, p⟩ = (4999625606007689 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 657 of the coefficient chain is the literal 9999251176844589/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_657 : ∀ (p : 657 < 1732), cc20Eq115CoefficientQ ⟨657, p⟩ = (9999251176844589 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 658 of the coefficient chain is the literal 4999625570914547/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_658 : ∀ (p : 658 < 1732), cc20Eq115CoefficientQ ⟨658, p⟩ = (4999625570914547 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 659 of the coefficient chain is the literal 249981277674469/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_659 : ∀ (p : 659 < 1732), cc20Eq115CoefficientQ ⟨659, p⟩ = (249981277674469 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 660 of the coefficient chain is the literal 1999850214457381/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_660 : ∀ (p : 660 < 1732), cc20Eq115CoefficientQ ⟨660, p⟩ = (1999850214457381 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 661 of the coefficient chain is the literal 9999251037755111/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_661 : ∀ (p : 661 < 1732), cc20Eq115CoefficientQ ⟨661, p⟩ = (9999251037755111 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 662 of the coefficient chain is the literal 9999251003380013/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_662 : ∀ (p : 662 < 1732), cc20Eq115CoefficientQ ⟨662, p⟩ = (9999251003380013 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 663 of the coefficient chain is the literal 4999625484583477/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_663 : ∀ (p : 663 < 1732), cc20Eq115CoefficientQ ⟨663, p⟩ = (4999625484583477 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 664 of the coefficient chain is the literal 4999625467552681/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_664 : ∀ (p : 664 < 1732), cc20Eq115CoefficientQ ⟨664, p⟩ = (4999625467552681 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 665 of the coefficient chain is the literal 2499812725300349/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_665 : ∀ (p : 665 < 1732), cc20Eq115CoefficientQ ⟨665, p⟩ = (2499812725300349 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 666 of the coefficient chain is the literal 9999250867451787/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_666 : ∀ (p : 666 < 1732), cc20Eq115CoefficientQ ⟨666, p⟩ = (9999250867451787 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 667 of the coefficient chain is the literal 9999250833855641/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_667 : ∀ (p : 667 < 1732), cc20Eq115CoefficientQ ⟨667, p⟩ = (9999250833855641 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 668 of the coefficient chain is the literal 1249906350051747/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_668 : ∀ (p : 668 < 1732), cc20Eq115CoefficientQ ⟨668, p⟩ = (1249906350051747 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 669 of the coefficient chain is the literal 1999850153424329/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_669 : ∀ (p : 669 < 1732), cc20Eq115CoefficientQ ⟨669, p⟩ = (1999850153424329 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 670 of the coefficient chain is the literal 2499812683495203/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_670 : ∀ (p : 670 < 1732), cc20Eq115CoefficientQ ⟨670, p⟩ = (2499812683495203 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 671 of the coefficient chain is the literal 1999850140197907/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_671 : ∀ (p : 671 < 1732), cc20Eq115CoefficientQ ⟨671, p⟩ = (1999850140197907 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 672 of the coefficient chain is the literal 9999250668147973/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_672 : ∀ (p : 672 < 1732), cc20Eq115CoefficientQ ⟨672, p⟩ = (9999250668147973 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 673 of the coefficient chain is the literal 4999625317726779/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_673 : ∀ (p : 673 < 1732), cc20Eq115CoefficientQ ⟨673, p⟩ = (4999625317726779 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 674 of the coefficient chain is the literal 9999250602908631/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_674 : ∀ (p : 674 < 1732), cc20Eq115CoefficientQ ⟨674, p⟩ = (9999250602908631 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 675 of the coefficient chain is the literal 4999625285252033/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_675 : ∀ (p : 675 < 1732), cc20Eq115CoefficientQ ⟨675, p⟩ = (4999625285252033 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 676 of the coefficient chain is the literal 4999625269128059/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_676 : ∀ (p : 676 < 1732), cc20Eq115CoefficientQ ⟨676, p⟩ = (4999625269128059 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 677 of the coefficient chain is the literal 9999250506147097/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_677 : ∀ (p : 677 < 1732), cc20Eq115CoefficientQ ⟨677, p⟩ = (9999250506147097 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 678 of the coefficient chain is the literal 2499812618543317/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_678 : ∀ (p : 678 < 1732), cc20Eq115CoefficientQ ⟨678, p⟩ = (2499812618543317 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 679 of the coefficient chain is the literal 9999250442352999/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_679 : ∀ (p : 679 < 1732), cc20Eq115CoefficientQ ⟨679, p⟩ = (9999250442352999 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 680 of the coefficient chain is the literal 4999625205338689/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_680 : ∀ (p : 680 < 1732), cc20Eq115CoefficientQ ⟨680, p⟩ = (4999625205338689 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 681 of the coefficient chain is the literal 799940030331/ 800000000000. -/
theorem cc20Eq115CoefficientQ_branch_681 : ∀ (p : 681 < 1732), cc20Eq115CoefficientQ ⟨681, p⟩ = (799940030331 : ℚ) /  800000000000 :=
  fun p => by rfl

/-- Branch 682 of the coefficient chain is the literal 4999625173867399/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_682 : ∀ (p : 682 < 1732), cc20Eq115CoefficientQ ⟨682, p⟩ = (4999625173867399 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 683 of the coefficient chain is the literal 4999625158242137/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_683 : ∀ (p : 683 < 1732), cc20Eq115CoefficientQ ⟨683, p⟩ = (4999625158242137 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 684 of the coefficient chain is the literal 1249906285670907/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_684 : ∀ (p : 684 < 1732), cc20Eq115CoefficientQ ⟨684, p⟩ = (1249906285670907 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 685 of the coefficient chain is the literal 9999250254384173/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_685 : ∀ (p : 685 < 1732), cc20Eq115CoefficientQ ⟨685, p⟩ = (9999250254384173 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 686 of the coefficient chain is the literal 9999250223541503/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_686 : ∀ (p : 686 < 1732), cc20Eq115CoefficientQ ⟨686, p⟩ = (9999250223541503 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 687 of the coefficient chain is the literal 9999250192832491/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_687 : ∀ (p : 687 < 1732), cc20Eq115CoefficientQ ⟨687, p⟩ = (9999250192832491 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 688 of the coefficient chain is the literal 4999625081131821/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_688 : ∀ (p : 688 < 1732), cc20Eq115CoefficientQ ⟨688, p⟩ = (4999625081131821 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 689 of the coefficient chain is the literal 1249906266478287/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_689 : ∀ (p : 689 < 1732), cc20Eq115CoefficientQ ⟨689, p⟩ = (1249906266478287 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 690 of the coefficient chain is the literal 9999250101525947/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_690 : ∀ (p : 690 < 1732), cc20Eq115CoefficientQ ⟨690, p⟩ = (9999250101525947 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 691 of the coefficient chain is the literal 4999625035677761/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_691 : ∀ (p : 691 < 1732), cc20Eq115CoefficientQ ⟨691, p⟩ = (4999625035677761 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 692 of the coefficient chain is the literal 2499812510330273/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_692 : ∀ (p : 692 < 1732), cc20Eq115CoefficientQ ⟨692, p⟩ = (2499812510330273 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 693 of the coefficient chain is the literal 2499812502854461/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_693 : ∀ (p : 693 < 1732), cc20Eq115CoefficientQ ⟨693, p⟩ = (2499812502854461 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 694 of the coefficient chain is the literal 9999249981645953/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_694 : ∀ (p : 694 < 1732), cc20Eq115CoefficientQ ⟨694, p⟩ = (9999249981645953 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 695 of the coefficient chain is the literal 9999249952002911/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_695 : ∀ (p : 695 < 1732), cc20Eq115CoefficientQ ⟨695, p⟩ = (9999249952002911 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 696 of the coefficient chain is the literal 2499812480622467/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_696 : ∀ (p : 696 < 1732), cc20Eq115CoefficientQ ⟨696, p⟩ = (2499812480622467 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 697 of the coefficient chain is the literal 2499812473276563/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_697 : ∀ (p : 697 < 1732), cc20Eq115CoefficientQ ⟨697, p⟩ = (2499812473276563 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 698 of the coefficient chain is the literal 249981246596317/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_698 : ∀ (p : 698 < 1732), cc20Eq115CoefficientQ ⟨698, p⟩ = (249981246596317 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 699 of the coefficient chain is the literal 999924983472369/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_699 : ∀ (p : 699 < 1732), cc20Eq115CoefficientQ ⟨699, p⟩ = (999924983472369 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 700 of the coefficient chain is the literal 4999624902861333/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_700 : ∀ (p : 700 < 1732), cc20Eq115CoefficientQ ⟨700, p⟩ = (4999624902861333 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 701 of the coefficient chain is the literal 9999249776847471/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_701 : ∀ (p : 701 < 1732), cc20Eq115CoefficientQ ⟨701, p⟩ = (9999249776847471 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 702 of the coefficient chain is the literal 9999249748098119/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_702 : ∀ (p : 702 < 1732), cc20Eq115CoefficientQ ⟨702, p⟩ = (9999249748098119 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 703 of the coefficient chain is the literal 9999249719472807/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_703 : ∀ (p : 703 < 1732), cc20Eq115CoefficientQ ⟨703, p⟩ = (9999249719472807 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 704 of the coefficient chain is the literal 9999249690971439/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_704 : ∀ (p : 704 < 1732), cc20Eq115CoefficientQ ⟨704, p⟩ = (9999249690971439 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 705 of the coefficient chain is the literal 4999624831297339/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_705 : ∀ (p : 705 < 1732), cc20Eq115CoefficientQ ⟨705, p⟩ = (4999624831297339 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 706 of the coefficient chain is the literal 4999624817169027/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_706 : ∀ (p : 706 < 1732), cc20Eq115CoefficientQ ⟨706, p⟩ = (4999624817169027 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 707 of the coefficient chain is the literal 4999624803102617/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_707 : ∀ (p : 707 < 1732), cc20Eq115CoefficientQ ⟨707, p⟩ = (4999624803102617 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 708 of the coefficient chain is the literal 999924957819163/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_708 : ∀ (p : 708 < 1732), cc20Eq115CoefficientQ ⟨708, p⟩ = (999924957819163 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 709 of the coefficient chain is the literal 4999624775150843/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_709 : ∀ (p : 709 < 1732), cc20Eq115CoefficientQ ⟨709, p⟩ = (4999624775150843 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 710 of the coefficient chain is the literal 1249906190316253/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_710 : ∀ (p : 710 < 1732), cc20Eq115CoefficientQ ⟨710, p⟩ = (1249906190316253 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 711 of the coefficient chain is the literal 9999249494877227/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_711 : ∀ (p : 711 < 1732), cc20Eq115CoefficientQ ⟨711, p⟩ = (9999249494877227 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 712 of the coefficient chain is the literal 9999249467344787/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_712 : ∀ (p : 712 < 1732), cc20Eq115CoefficientQ ⟨712, p⟩ = (9999249467344787 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 713 of the coefficient chain is the literal 9999249439926549/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_713 : ∀ (p : 713 < 1732), cc20Eq115CoefficientQ ⟨713, p⟩ = (9999249439926549 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 714 of the coefficient chain is the literal 999924941262739/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_714 : ∀ (p : 714 < 1732), cc20Eq115CoefficientQ ⟨714, p⟩ = (999924941262739 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 715 of the coefficient chain is the literal 2499812346361027/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_715 : ∀ (p : 715 < 1732), cc20Eq115CoefficientQ ⟨715, p⟩ = (2499812346361027 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 716 of the coefficient chain is the literal 9999249358377371/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_716 : ∀ (p : 716 < 1732), cc20Eq115CoefficientQ ⟨716, p⟩ = (9999249358377371 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 717 of the coefficient chain is the literal 9999249331426289/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_717 : ∀ (p : 717 < 1732), cc20Eq115CoefficientQ ⟨717, p⟩ = (9999249331426289 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 718 of the coefficient chain is the literal 2499812326147541/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_718 : ∀ (p : 718 < 1732), cc20Eq115CoefficientQ ⟨718, p⟩ = (2499812326147541 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 719 of the coefficient chain is the literal 1249906159733149/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_719 : ∀ (p : 719 < 1732), cc20Eq115CoefficientQ ⟨719, p⟩ = (1249906159733149 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 720 of the coefficient chain is the literal 9999249251256443/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_720 : ∀ (p : 720 < 1732), cc20Eq115CoefficientQ ⟨720, p⟩ = (9999249251256443 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 721 of the coefficient chain is the literal 1999849844951641/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_721 : ∀ (p : 721 < 1732), cc20Eq115CoefficientQ ⟨721, p⟩ = (1999849844951641 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 722 of the coefficient chain is the literal 9999249198373663/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_722 : ∀ (p : 722 < 1732), cc20Eq115CoefficientQ ⟨722, p⟩ = (9999249198373663 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 723 of the coefficient chain is the literal 9999249172101103/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_723 : ∀ (p : 723 < 1732), cc20Eq115CoefficientQ ⟨723, p⟩ = (9999249172101103 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 724 of the coefficient chain is the literal 2499812286484759/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_724 : ∀ (p : 724 < 1732), cc20Eq115CoefficientQ ⟨724, p⟩ = (2499812286484759 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 725 of the coefficient chain is the literal 1999849823977193/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_725 : ∀ (p : 725 < 1732), cc20Eq115CoefficientQ ⟨725, p⟩ = (1999849823977193 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 726 of the coefficient chain is the literal 9999249093944631/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_726 : ∀ (p : 726 < 1732), cc20Eq115CoefficientQ ⟨726, p⟩ = (9999249093944631 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 727 of the coefficient chain is the literal 2499812267027311/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_727 : ∀ (p : 727 < 1732), cc20Eq115CoefficientQ ⟨727, p⟩ = (2499812267027311 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 728 of the coefficient chain is the literal 624953065148581/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_728 : ∀ (p : 728 < 1732), cc20Eq115CoefficientQ ⟨728, p⟩ = (624953065148581 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 729 of the coefficient chain is the literal 1249906127096553/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_729 : ∀ (p : 729 < 1732), cc20Eq115CoefficientQ ⟨729, p⟩ = (1249906127096553 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 730 of the coefficient chain is the literal 4999624495624627/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_730 : ∀ (p : 730 < 1732), cc20Eq115CoefficientQ ⟨730, p⟩ = (4999624495624627 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 731 of the coefficient chain is the literal 9999248965850893/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_731 : ∀ (p : 731 < 1732), cc20Eq115CoefficientQ ⟨731, p⟩ = (9999248965850893 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 732 of the coefficient chain is the literal 2499812235139297/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_732 : ∀ (p : 732 < 1732), cc20Eq115CoefficientQ ⟨732, p⟩ = (2499812235139297 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 733 of the coefficient chain is the literal 999924891536667/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_733 : ∀ (p : 733 < 1732), cc20Eq115CoefficientQ ⟨733, p⟩ = (999924891536667 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 734 of the coefficient chain is the literal 4999624445140511/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_734 : ∀ (p : 734 < 1732), cc20Eq115CoefficientQ ⟨734, p⟩ = (4999624445140511 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 735 of the coefficient chain is the literal 9999248865299409/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_735 : ∀ (p : 735 < 1732), cc20Eq115CoefficientQ ⟨735, p⟩ = (9999248865299409 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 736 of the coefficient chain is the literal 4999624420223457/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_736 : ∀ (p : 736 < 1732), cc20Eq115CoefficientQ ⟨736, p⟩ = (4999624420223457 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 737 of the coefficient chain is the literal 1999849763128313/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_737 : ∀ (p : 737 < 1732), cc20Eq115CoefficientQ ⟨737, p⟩ = (1999849763128313 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 738 of the coefficient chain is the literal 999924879097061/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_738 : ∀ (p : 738 < 1732), cc20Eq115CoefficientQ ⟨738, p⟩ = (999924879097061 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 739 of the coefficient chain is the literal 2499812191600267/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_739 : ∀ (p : 739 < 1732), cc20Eq115CoefficientQ ⟨739, p⟩ = (2499812191600267 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 740 of the coefficient chain is the literal 9999248741933081/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_740 : ∀ (p : 740 < 1732), cc20Eq115CoefficientQ ⟨740, p⟩ = (9999248741933081 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 741 of the coefficient chain is the literal 249981217939149/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_741 : ∀ (p : 741 < 1732), cc20Eq115CoefficientQ ⟨741, p⟩ = (249981217939149 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 742 of the coefficient chain is the literal 79993989546367/ 80000000000000. -/
theorem cc20Eq115CoefficientQ_branch_742 : ∀ (p : 742 < 1732), cc20Eq115CoefficientQ ⟨742, p⟩ = (79993989546367 : ℚ) /  80000000000000 :=
  fun p => by rfl

/-- Branch 743 of the coefficient chain is the literal 9999248669127517/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_743 : ∀ (p : 743 < 1732), cc20Eq115CoefficientQ ⟨743, p⟩ = (9999248669127517 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 744 of the coefficient chain is the literal 1249906080630623/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_744 : ∀ (p : 744 < 1732), cc20Eq115CoefficientQ ⟨744, p⟩ = (1249906080630623 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 745 of the coefficient chain is the literal 4999624310552257/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_745 : ∀ (p : 745 < 1732), cc20Eq115CoefficientQ ⟨745, p⟩ = (4999624310552257 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 746 of the coefficient chain is the literal 1249906074653903/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_746 : ∀ (p : 746 < 1732), cc20Eq115CoefficientQ ⟨746, p⟩ = (1249906074653903 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 747 of the coefficient chain is the literal 624953035841121/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_747 : ∀ (p : 747 < 1732), cc20Eq115CoefficientQ ⟨747, p⟩ = (624953035841121 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 748 of the coefficient chain is the literal 4999624274894967/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_748 : ∀ (p : 748 < 1732), cc20Eq115CoefficientQ ⟨748, p⟩ = (4999624274894967 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 749 of the coefficient chain is the literal 49996242631047/ 50000000000000. -/
theorem cc20Eq115CoefficientQ_branch_749 : ∀ (p : 749 < 1732), cc20Eq115CoefficientQ ⟨749, p⟩ = (49996242631047 : ℚ) /  50000000000000 :=
  fun p => by rfl

/-- Branch 750 of the coefficient chain is the literal 9999248502727557/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_750 : ∀ (p : 750 < 1732), cc20Eq115CoefficientQ ⟨750, p⟩ = (9999248502727557 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 751 of the coefficient chain is the literal 9999248479340487/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_751 : ∀ (p : 751 < 1732), cc20Eq115CoefficientQ ⟨751, p⟩ = (9999248479340487 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 752 of the coefficient chain is the literal 1999849691213027/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_752 : ∀ (p : 752 < 1732), cc20Eq115CoefficientQ ⟨752, p⟩ = (1999849691213027 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 753 of the coefficient chain is the literal 312476513526861/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_753 : ∀ (p : 753 < 1732), cc20Eq115CoefficientQ ⟨753, p⟩ = (312476513526861 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 754 of the coefficient chain is the literal 249981210243883/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_754 : ∀ (p : 754 < 1732), cc20Eq115CoefficientQ ⟨754, p⟩ = (249981210243883 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 755 of the coefficient chain is the literal 9999248386742869/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_755 : ∀ (p : 755 < 1732), cc20Eq115CoefficientQ ⟨755, p⟩ = (9999248386742869 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 756 of the coefficient chain is the literal 2499812090961201/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_756 : ∀ (p : 756 < 1732), cc20Eq115CoefficientQ ⟨756, p⟩ = (2499812090961201 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 757 of the coefficient chain is the literal 4999624170511187/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_757 : ∀ (p : 757 < 1732), cc20Eq115CoefficientQ ⟨757, p⟩ = (4999624170511187 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 758 of the coefficient chain is the literal 312476509946683/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_758 : ∀ (p : 758 < 1732), cc20Eq115CoefficientQ ⟨758, p⟩ = (312476509946683 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 759 of the coefficient chain is the literal 2499812073914251/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_759 : ∀ (p : 759 < 1732), cc20Eq115CoefficientQ ⟨759, p⟩ = (2499812073914251 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 760 of the coefficient chain is the literal 9999248273112603/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_760 : ∀ (p : 760 < 1732), cc20Eq115CoefficientQ ⟨760, p⟩ = (9999248273112603 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 761 of the coefficient chain is the literal 9999248250658557/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_761 : ∀ (p : 761 < 1732), cc20Eq115CoefficientQ ⟨761, p⟩ = (9999248250658557 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 762 of the coefficient chain is the literal 1999849645659099/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_762 : ∀ (p : 762 < 1732), cc20Eq115CoefficientQ ⟨762, p⟩ = (1999849645659099 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 763 of the coefficient chain is the literal 999924820602363/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_763 : ∀ (p : 763 < 1732), cc20Eq115CoefficientQ ⟨763, p⟩ = (999924820602363 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 764 of the coefficient chain is the literal 9999248183838981/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_764 : ∀ (p : 764 < 1732), cc20Eq115CoefficientQ ⟨764, p⟩ = (9999248183838981 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 765 of the coefficient chain is the literal 1999849632348689/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_765 : ∀ (p : 765 < 1732), cc20Eq115CoefficientQ ⟨765, p⟩ = (1999849632348689 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 766 of the coefficient chain is the literal 1249906017467261/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_766 : ∀ (p : 766 < 1732), cc20Eq115CoefficientQ ⟨766, p⟩ = (1249906017467261 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 767 of the coefficient chain is the literal 999924811782403/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_767 : ∀ (p : 767 < 1732), cc20Eq115CoefficientQ ⟨767, p⟩ = (999924811782403 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 768 of the coefficient chain is the literal 9999248095992901/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_768 : ∀ (p : 768 < 1732), cc20Eq115CoefficientQ ⟨768, p⟩ = (9999248095992901 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 769 of the coefficient chain is the literal 39059562790041/ 39062500000000. -/
theorem cc20Eq115CoefficientQ_branch_769 : ∀ (p : 769 < 1732), cc20Eq115CoefficientQ ⟨769, p⟩ = (39059562790041 : ℚ) /  39062500000000 :=
  fun p => by rfl

/-- Branch 770 of the coefficient chain is the literal 4999624026297171/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_770 : ∀ (p : 770 < 1732), cc20Eq115CoefficientQ ⟨770, p⟩ = (4999624026297171 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 771 of the coefficient chain is the literal 499962401551277/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_771 : ∀ (p : 771 < 1732), cc20Eq115CoefficientQ ⟨771, p⟩ = (499962401551277 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 772 of the coefficient chain is the literal 4999624004771259/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_772 : ∀ (p : 772 < 1732), cc20Eq115CoefficientQ ⟨772, p⟩ = (4999624004771259 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 773 of the coefficient chain is the literal 1999849597627821/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_773 : ∀ (p : 773 < 1732), cc20Eq115CoefficientQ ⟨773, p⟩ = (1999849597627821 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 774 of the coefficient chain is the literal 624952997927103/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_774 : ∀ (p : 774 < 1732), cc20Eq115CoefficientQ ⟨774, p⟩ = (624952997927103 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 775 of the coefficient chain is the literal 499962397280241/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_775 : ∀ (p : 775 < 1732), cc20Eq115CoefficientQ ⟨775, p⟩ = (499962397280241 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 776 of the coefficient chain is the literal 4999623962230243/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_776 : ∀ (p : 776 < 1732), cc20Eq115CoefficientQ ⟨776, p⟩ = (4999623962230243 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 777 of the coefficient chain is the literal 9999247903403257/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_777 : ∀ (p : 777 < 1732), cc20Eq115CoefficientQ ⟨777, p⟩ = (9999247903403257 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 778 of the coefficient chain is the literal 9999247882425633/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_778 : ∀ (p : 778 < 1732), cc20Eq115CoefficientQ ⟨778, p⟩ = (9999247882425633 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 779 of the coefficient chain is the literal 2499811965382811/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_779 : ∀ (p : 779 < 1732), cc20Eq115CoefficientQ ⟨779, p⟩ = (2499811965382811 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 780 of the coefficient chain is the literal 1999849568144581/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_780 : ∀ (p : 780 < 1732), cc20Eq115CoefficientQ ⟨780, p⟩ = (1999849568144581 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 781 of the coefficient chain is the literal 9999247820014577/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_781 : ∀ (p : 781 < 1732), cc20Eq115CoefficientQ ⟨781, p⟩ = (9999247820014577 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 782 of the coefficient chain is the literal 4999623899673047/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_782 : ∀ (p : 782 < 1732), cc20Eq115CoefficientQ ⟨782, p⟩ = (4999623899673047 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 783 of the coefficient chain is the literal 1999849555755539/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_783 : ∀ (p : 783 < 1732), cc20Eq115CoefficientQ ⟨783, p⟩ = (1999849555755539 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 784 of the coefficient chain is the literal 4999623879146363/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_784 : ∀ (p : 784 < 1732), cc20Eq115CoefficientQ ⟨784, p⟩ = (4999623879146363 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 785 of the coefficient chain is the literal 249981193447167/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_785 : ∀ (p : 785 < 1732), cc20Eq115CoefficientQ ⟨785, p⟩ = (249981193447167 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 786 of the coefficient chain is the literal 9999247717569083/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_786 : ∀ (p : 786 < 1732), cc20Eq115CoefficientQ ⟨786, p⟩ = (9999247717569083 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 787 of the coefficient chain is the literal 9999247697321687/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_787 : ∀ (p : 787 < 1732), cc20Eq115CoefficientQ ⟨787, p⟩ = (9999247697321687 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 788 of the coefficient chain is the literal 1999849535431307/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_788 : ∀ (p : 788 < 1732), cc20Eq115CoefficientQ ⟨788, p⟩ = (1999849535431307 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 789 of the coefficient chain is the literal 9999247657068979/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_789 : ∀ (p : 789 < 1732), cc20Eq115CoefficientQ ⟨789, p⟩ = (9999247657068979 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 790 of the coefficient chain is the literal 9999247637060623/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_790 : ∀ (p : 790 < 1732), cc20Eq115CoefficientQ ⟨790, p⟩ = (9999247637060623 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 791 of the coefficient chain is the literal 2499811904282689/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_791 : ∀ (p : 791 < 1732), cc20Eq115CoefficientQ ⟨791, p⟩ = (2499811904282689 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 792 of the coefficient chain is the literal 9999247597277283/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_792 : ∀ (p : 792 < 1732), cc20Eq115CoefficientQ ⟨792, p⟩ = (9999247597277283 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 793 of the coefficient chain is the literal 9999247577502391/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_793 : ∀ (p : 793 < 1732), cc20Eq115CoefficientQ ⟨793, p⟩ = (9999247577502391 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 794 of the coefficient chain is the literal 9999247557804529/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_794 : ∀ (p : 794 < 1732), cc20Eq115CoefficientQ ⟨794, p⟩ = (9999247557804529 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 795 of the coefficient chain is the literal 9999247538184199/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_795 : ∀ (p : 795 < 1732), cc20Eq115CoefficientQ ⟨795, p⟩ = (9999247538184199 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 796 of the coefficient chain is the literal 9999247518636749/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_796 : ∀ (p : 796 < 1732), cc20Eq115CoefficientQ ⟨796, p⟩ = (9999247518636749 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 797 of the coefficient chain is the literal 4999623749583379/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_797 : ∀ (p : 797 < 1732), cc20Eq115CoefficientQ ⟨797, p⟩ = (4999623749583379 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 798 of the coefficient chain is the literal 312476483742829/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_798 : ∀ (p : 798 < 1732), cc20Eq115CoefficientQ ⟨798, p⟩ = (312476483742829 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 799 of the coefficient chain is the literal 4999623730227667/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_799 : ∀ (p : 799 < 1732), cc20Eq115CoefficientQ ⟨799, p⟩ = (4999623730227667 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 800 of the coefficient chain is the literal 1999849488242983/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_800 : ∀ (p : 800 < 1732), cc20Eq115CoefficientQ ⟨800, p⟩ = (1999849488242983 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 801 of the coefficient chain is the literal 99992474220481/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_801 : ∀ (p : 801 < 1732), cc20Eq115CoefficientQ ⟨801, p⟩ = (99992474220481 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 802 of the coefficient chain is the literal 9999247402930029/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_802 : ∀ (p : 802 < 1732), cc20Eq115CoefficientQ ⟨802, p⟩ = (9999247402930029 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 803 of the coefficient chain is the literal 4999623691957069/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_803 : ∀ (p : 803 < 1732), cc20Eq115CoefficientQ ⟨803, p⟩ = (4999623691957069 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 804 of the coefficient chain is the literal 9999247364963153/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_804 : ∀ (p : 804 < 1732), cc20Eq115CoefficientQ ⟨804, p⟩ = (9999247364963153 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 805 of the coefficient chain is the literal 9999247346087751/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_805 : ∀ (p : 805 < 1732), cc20Eq115CoefficientQ ⟨805, p⟩ = (9999247346087751 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 806 of the coefficient chain is the literal 4999623663641793/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_806 : ∀ (p : 806 < 1732), cc20Eq115CoefficientQ ⟨806, p⟩ = (4999623663641793 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 807 of the coefficient chain is the literal 9999247308551291/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_807 : ∀ (p : 807 < 1732), cc20Eq115CoefficientQ ⟨807, p⟩ = (9999247308551291 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 808 of the coefficient chain is the literal 2499811822473741/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_808 : ∀ (p : 808 < 1732), cc20Eq115CoefficientQ ⟨808, p⟩ = (2499811822473741 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 809 of the coefficient chain is the literal 4999623635651147/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_809 : ∀ (p : 809 < 1732), cc20Eq115CoefficientQ ⟨809, p⟩ = (4999623635651147 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 810 of the coefficient chain is the literal 9999247252783159/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_810 : ∀ (p : 810 < 1732), cc20Eq115CoefficientQ ⟨810, p⟩ = (9999247252783159 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 811 of the coefficient chain is the literal 9999247234336459/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_811 : ∀ (p : 811 < 1732), cc20Eq115CoefficientQ ⟨811, p⟩ = (9999247234336459 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 812 of the coefficient chain is the literal 4999623607979791/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_812 : ∀ (p : 812 < 1732), cc20Eq115CoefficientQ ⟨812, p⟩ = (4999623607979791 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 813 of the coefficient chain is the literal 9999247197652007/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_813 : ∀ (p : 813 < 1732), cc20Eq115CoefficientQ ⟨813, p⟩ = (9999247197652007 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 814 of the coefficient chain is the literal 9999247179415989/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_814 : ∀ (p : 814 < 1732), cc20Eq115CoefficientQ ⟨814, p⟩ = (9999247179415989 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 815 of the coefficient chain is the literal 9999247161246989/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_815 : ∀ (p : 815 < 1732), cc20Eq115CoefficientQ ⟨815, p⟩ = (9999247161246989 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 816 of the coefficient chain is the literal 4999623571573947/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_816 : ∀ (p : 816 < 1732), cc20Eq115CoefficientQ ⟨816, p⟩ = (4999623571573947 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 817 of the coefficient chain is the literal 1999849425023871/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_817 : ∀ (p : 817 < 1732), cc20Eq115CoefficientQ ⟨817, p⟩ = (1999849425023871 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 818 of the coefficient chain is the literal 624952944197427/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_818 : ∀ (p : 818 < 1732), cc20Eq115CoefficientQ ⟨818, p⟩ = (624952944197427 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 819 of the coefficient chain is the literal 2499811772315939/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_819 : ∀ (p : 819 < 1732), cc20Eq115CoefficientQ ⟨819, p⟩ = (2499811772315939 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 820 of the coefficient chain is the literal 9999247071439491/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_820 : ∀ (p : 820 < 1732), cc20Eq115CoefficientQ ⟨820, p⟩ = (9999247071439491 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 821 of the coefficient chain is the literal 2499811763420771/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_821 : ∀ (p : 821 < 1732), cc20Eq115CoefficientQ ⟨821, p⟩ = (2499811763420771 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 822 of the coefficient chain is the literal 49996235179933/ 50000000000000. -/
theorem cc20Eq115CoefficientQ_branch_822 : ∀ (p : 822 < 1732), cc20Eq115CoefficientQ ⟨822, p⟩ = (49996235179933 : ℚ) /  50000000000000 :=
  fun p => by rfl

/-- Branch 823 of the coefficient chain is the literal 9999247018362113/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_823 : ∀ (p : 823 < 1732), cc20Eq115CoefficientQ ⟨823, p⟩ = (9999247018362113 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 824 of the coefficient chain is the literal 2499811750201069/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_824 : ∀ (p : 824 < 1732), cc20Eq115CoefficientQ ⟨824, p⟩ = (2499811750201069 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 825 of the coefficient chain is the literal 1249905872914169/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_825 : ∀ (p : 825 < 1732), cc20Eq115CoefficientQ ⟨825, p⟩ = (1249905872914169 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 826 of the coefficient chain is the literal 9999246965886133/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_826 : ∀ (p : 826 < 1732), cc20Eq115CoefficientQ ⟨826, p⟩ = (9999246965886133 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 827 of the coefficient chain is the literal 4999623474262709/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_827 : ∀ (p : 827 < 1732), cc20Eq115CoefficientQ ⟨827, p⟩ = (4999623474262709 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 828 of the coefficient chain is the literal 4999623465614811/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_828 : ∀ (p : 828 < 1732), cc20Eq115CoefficientQ ⟨828, p⟩ = (4999623465614811 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 829 of the coefficient chain is the literal 9999246913998053/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_829 : ∀ (p : 829 < 1732), cc20Eq115CoefficientQ ⟨829, p⟩ = (9999246913998053 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 830 of the coefficient chain is the literal 9999246896830851/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_830 : ∀ (p : 830 < 1732), cc20Eq115CoefficientQ ⟨830, p⟩ = (9999246896830851 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 831 of the coefficient chain is the literal 9999246879730113/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_831 : ∀ (p : 831 < 1732), cc20Eq115CoefficientQ ⟨831, p⟩ = (9999246879730113 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 832 of the coefficient chain is the literal 2499811715672603/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_832 : ∀ (p : 832 < 1732), cc20Eq115CoefficientQ ⟨832, p⟩ = (2499811715672603 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 833 of the coefficient chain is the literal 1249905855714609/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_833 : ∀ (p : 833 < 1732), cc20Eq115CoefficientQ ⟨833, p⟩ = (1249905855714609 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 834 of the coefficient chain is the literal 1999849365761119/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_834 : ∀ (p : 834 < 1732), cc20Eq115CoefficientQ ⟨834, p⟩ = (1999849365761119 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 835 of the coefficient chain is the literal 9999246811958967/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_835 : ∀ (p : 835 < 1732), cc20Eq115CoefficientQ ⟨835, p⟩ = (9999246811958967 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 836 of the coefficient chain is the literal 9999246795173649/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_836 : ∀ (p : 836 < 1732), cc20Eq115CoefficientQ ⟨836, p⟩ = (9999246795173649 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 837 of the coefficient chain is the literal 9999246778450911/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_837 : ∀ (p : 837 < 1732), cc20Eq115CoefficientQ ⟨837, p⟩ = (9999246778450911 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 838 of the coefficient chain is the literal 9999246761789351/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_838 : ∀ (p : 838 < 1732), cc20Eq115CoefficientQ ⟨838, p⟩ = (9999246761789351 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 839 of the coefficient chain is the literal 312476460787247/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_839 : ∀ (p : 839 < 1732), cc20Eq115CoefficientQ ⟨839, p⟩ = (312476460787247 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 840 of the coefficient chain is the literal 4999623364325503/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_840 : ∀ (p : 840 < 1732), cc20Eq115CoefficientQ ⟨840, p⟩ = (4999623364325503 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 841 of the coefficient chain is the literal 4999623356087897/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_841 : ∀ (p : 841 < 1732), cc20Eq115CoefficientQ ⟨841, p⟩ = (4999623356087897 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 842 of the coefficient chain is the literal 2499811673940559/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_842 : ∀ (p : 842 < 1732), cc20Eq115CoefficientQ ⟨842, p⟩ = (2499811673940559 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 843 of the coefficient chain is the literal 9999246679406577/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_843 : ∀ (p : 843 < 1732), cc20Eq115CoefficientQ ⟨843, p⟩ = (9999246679406577 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 844 of the coefficient chain is the literal 1249905832889257/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_844 : ∀ (p : 844 < 1732), cc20Eq115CoefficientQ ⟨844, p⟩ = (1249905832889257 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 845 of the coefficient chain is the literal 9999246646879667/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_845 : ∀ (p : 845 < 1732), cc20Eq115CoefficientQ ⟨845, p⟩ = (9999246646879667 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 846 of the coefficient chain is the literal 4999623315352709/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_846 : ∀ (p : 846 < 1732), cc20Eq115CoefficientQ ⟨846, p⟩ = (4999623315352709 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 847 of the coefficient chain is the literal 2499811653647943/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_847 : ∀ (p : 847 < 1732), cc20Eq115CoefficientQ ⟨847, p⟩ = (2499811653647943 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 848 of the coefficient chain is the literal 1999849319707099/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_848 : ∀ (p : 848 < 1732), cc20Eq115CoefficientQ ⟨848, p⟩ = (1999849319707099 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 849 of the coefficient chain is the literal 9999246582539479/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_849 : ∀ (p : 849 < 1732), cc20Eq115CoefficientQ ⟨849, p⟩ = (9999246582539479 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 850 of the coefficient chain is the literal 1999849313319747/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_850 : ∀ (p : 850 < 1732), cc20Eq115CoefficientQ ⟨850, p⟩ = (1999849313319747 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 851 of the coefficient chain is the literal 2499811637678053/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_851 : ∀ (p : 851 < 1732), cc20Eq115CoefficientQ ⟨851, p⟩ = (2499811637678053 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 852 of the coefficient chain is the literal 4999623267456459/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_852 : ∀ (p : 852 < 1732), cc20Eq115CoefficientQ ⟨852, p⟩ = (4999623267456459 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 853 of the coefficient chain is the literal 4999623259573517/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_853 : ∀ (p : 853 < 1732), cc20Eq115CoefficientQ ⟨853, p⟩ = (4999623259573517 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 854 of the coefficient chain is the literal 624952906465057/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_854 : ∀ (p : 854 < 1732), cc20Eq115CoefficientQ ⟨854, p⟩ = (624952906465057 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 855 of the coefficient chain is the literal 1999849297558861/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_855 : ∀ (p : 855 < 1732), cc20Eq115CoefficientQ ⟨855, p⟩ = (1999849297558861 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 856 of the coefficient chain is the literal 9999246472203133/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_856 : ∀ (p : 856 < 1732), cc20Eq115CoefficientQ ⟨856, p⟩ = (9999246472203133 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 857 of the coefficient chain is the literal 9999246456669423/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_857 : ∀ (p : 857 < 1732), cc20Eq115CoefficientQ ⟨857, p⟩ = (9999246456669423 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 858 of the coefficient chain is the literal 9999246441193723/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_858 : ∀ (p : 858 < 1732), cc20Eq115CoefficientQ ⟨858, p⟩ = (9999246441193723 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 859 of the coefficient chain is the literal 2499811606443199/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_859 : ∀ (p : 859 < 1732), cc20Eq115CoefficientQ ⟨859, p⟩ = (2499811606443199 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 860 of the coefficient chain is the literal 2499811602601633/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_860 : ∀ (p : 860 < 1732), cc20Eq115CoefficientQ ⟨860, p⟩ = (2499811602601633 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 861 of the coefficient chain is the literal 9999246395103147/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_861 : ∀ (p : 861 < 1732), cc20Eq115CoefficientQ ⟨861, p⟩ = (9999246395103147 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 862 of the coefficient chain is the literal 9999246379852469/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_862 : ∀ (p : 862 < 1732), cc20Eq115CoefficientQ ⟨862, p⟩ = (9999246379852469 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 863 of the coefficient chain is the literal 9999246364654057/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_863 : ∀ (p : 863 < 1732), cc20Eq115CoefficientQ ⟨863, p⟩ = (9999246364654057 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 864 of the coefficient chain is the literal 4999623174756499/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_864 : ∀ (p : 864 < 1732), cc20Eq115CoefficientQ ⟨864, p⟩ = (4999623174756499 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 865 of the coefficient chain is the literal 499962316721263/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_865 : ∀ (p : 865 < 1732), cc20Eq115CoefficientQ ⟨865, p⟩ = (499962316721263 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 866 of the coefficient chain is the literal 624952894962039/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_866 : ∀ (p : 866 < 1732), cc20Eq115CoefficientQ ⟨866, p⟩ = (624952894962039 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 867 of the coefficient chain is the literal 1999849260882489/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_867 : ∀ (p : 867 < 1732), cc20Eq115CoefficientQ ⟨867, p⟩ = (1999849260882489 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 868 of the coefficient chain is the literal 1249905786186159/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_868 : ∀ (p : 868 < 1732), cc20Eq115CoefficientQ ⟨868, p⟩ = (1249905786186159 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 869 of the coefficient chain is the literal 9999246274620063/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_869 : ∀ (p : 869 < 1732), cc20Eq115CoefficientQ ⟨869, p⟩ = (9999246274620063 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 870 of the coefficient chain is the literal 2499811564950897/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_870 : ∀ (p : 870 < 1732), cc20Eq115CoefficientQ ⟨870, p⟩ = (2499811564950897 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 871 of the coefficient chain is the literal 9999246245039379/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_871 : ∀ (p : 871 < 1732), cc20Eq115CoefficientQ ⟨871, p⟩ = (9999246245039379 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 872 of the coefficient chain is the literal 4999623115165147/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_872 : ∀ (p : 872 < 1732), cc20Eq115CoefficientQ ⟨872, p⟩ = (4999623115165147 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 873 of the coefficient chain is the literal 9999246215673477/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_873 : ∀ (p : 873 < 1732), cc20Eq115CoefficientQ ⟨873, p⟩ = (9999246215673477 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 874 of the coefficient chain is the literal 4999623100534409/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_874 : ∀ (p : 874 < 1732), cc20Eq115CoefficientQ ⟨874, p⟩ = (4999623100534409 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 875 of the coefficient chain is the literal 4999623093259291/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_875 : ∀ (p : 875 < 1732), cc20Eq115CoefficientQ ⟨875, p⟩ = (4999623093259291 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 876 of the coefficient chain is the literal 4999623086009089/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_876 : ∀ (p : 876 < 1732), cc20Eq115CoefficientQ ⟨876, p⟩ = (4999623086009089 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 877 of the coefficient chain is the literal 4999623078785389/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_877 : ∀ (p : 877 < 1732), cc20Eq115CoefficientQ ⟨877, p⟩ = (4999623078785389 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 878 of the coefficient chain is the literal 9999246143175379/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_878 : ∀ (p : 878 < 1732), cc20Eq115CoefficientQ ⟨878, p⟩ = (9999246143175379 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 879 of the coefficient chain is the literal 999924612883243/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_879 : ∀ (p : 879 < 1732), cc20Eq115CoefficientQ ⟨879, p⟩ = (999924612883243 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 880 of the coefficient chain is the literal 4999623057268871/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_880 : ∀ (p : 880 < 1732), cc20Eq115CoefficientQ ⟨880, p⟩ = (4999623057268871 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 881 of the coefficient chain is the literal 999924610029547/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_881 : ∀ (p : 881 < 1732), cc20Eq115CoefficientQ ⟨881, p⟩ = (999924610029547 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 882 of the coefficient chain is the literal 9999246086107249/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_882 : ∀ (p : 882 < 1732), cc20Eq115CoefficientQ ⟨882, p⟩ = (9999246086107249 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 883 of the coefficient chain is the literal 399969842878613/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_883 : ∀ (p : 883 < 1732), cc20Eq115CoefficientQ ⟨883, p⟩ = (399969842878613 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 884 of the coefficient chain is the literal 4999623028938729/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_884 : ∀ (p : 884 < 1732), cc20Eq115CoefficientQ ⟨884, p⟩ = (4999623028938729 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 885 of the coefficient chain is the literal 4999623021918219/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_885 : ∀ (p : 885 < 1732), cc20Eq115CoefficientQ ⟨885, p⟩ = (4999623021918219 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 886 of the coefficient chain is the literal 624952876865287/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_886 : ∀ (p : 886 < 1732), cc20Eq115CoefficientQ ⟨886, p⟩ = (624952876865287 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 887 of the coefficient chain is the literal 9999246015904053/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_887 : ∀ (p : 887 < 1732), cc20Eq115CoefficientQ ⟨887, p⟩ = (9999246015904053 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 888 of the coefficient chain is the literal 2499811500503337/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_888 : ∀ (p : 888 < 1732), cc20Eq115CoefficientQ ⟨888, p⟩ = (2499811500503337 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 889 of the coefficient chain is the literal 1999849197637699/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_889 : ∀ (p : 889 < 1732), cc20Eq115CoefficientQ ⟨889, p⟩ = (1999849197637699 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 890 of the coefficient chain is the literal 9999245974382059/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_890 : ∀ (p : 890 < 1732), cc20Eq115CoefficientQ ⟨890, p⟩ = (9999245974382059 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 891 of the coefficient chain is the literal 4999622980319023/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_891 : ∀ (p : 891 < 1732), cc20Eq115CoefficientQ ⟨891, p⟩ = (4999622980319023 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 892 of the coefficient chain is the literal 1249905743367827/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_892 : ∀ (p : 892 < 1732), cc20Eq115CoefficientQ ⟨892, p⟩ = (1249905743367827 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 893 of the coefficient chain is the literal 9999245933296077/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_893 : ∀ (p : 893 < 1732), cc20Eq115CoefficientQ ⟨893, p⟩ = (9999245933296077 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 894 of the coefficient chain is the literal 1999849183939523/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_894 : ∀ (p : 894 < 1732), cc20Eq115CoefficientQ ⟨894, p⟩ = (1999849183939523 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 895 of the coefficient chain is the literal 4999622953074471/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_895 : ∀ (p : 895 < 1732), cc20Eq115CoefficientQ ⟨895, p⟩ = (4999622953074471 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 896 of the coefficient chain is the literal 9999245892646367/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_896 : ∀ (p : 896 < 1732), cc20Eq115CoefficientQ ⟨896, p⟩ = (9999245892646367 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 897 of the coefficient chain is the literal 4999622939582053/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_897 : ∀ (p : 897 < 1732), cc20Eq115CoefficientQ ⟨897, p⟩ = (4999622939582053 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 898 of the coefficient chain is the literal 9999245865785493/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_898 : ∀ (p : 898 < 1732), cc20Eq115CoefficientQ ⟨898, p⟩ = (9999245865785493 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 899 of the coefficient chain is the literal 624952865776563/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_899 : ∀ (p : 899 < 1732), cc20Eq115CoefficientQ ⟨899, p⟩ = (624952865776563 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 900 of the coefficient chain is the literal 2499811459777609/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_900 : ∀ (p : 900 < 1732), cc20Eq115CoefficientQ ⟨900, p⟩ = (2499811459777609 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 901 of the coefficient chain is the literal 4999622912921813/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_901 : ∀ (p : 901 < 1732), cc20Eq115CoefficientQ ⟨901, p⟩ = (4999622912921813 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 902 of the coefficient chain is the literal 4999622906313313/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_902 : ∀ (p : 902 < 1732), cc20Eq115CoefficientQ ⟨902, p⟩ = (4999622906313313 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 903 of the coefficient chain is the literal 9999245799452763/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_903 : ∀ (p : 903 < 1732), cc20Eq115CoefficientQ ⟨903, p⟩ = (9999245799452763 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 904 of the coefficient chain is the literal 2499811446581101/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_904 : ∀ (p : 904 < 1732), cc20Eq115CoefficientQ ⟨904, p⟩ = (2499811446581101 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 905 of the coefficient chain is the literal 499962288662133/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_905 : ∀ (p : 905 < 1732), cc20Eq115CoefficientQ ⟨905, p⟩ = (499962288662133 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 906 of the coefficient chain is the literal 9999245760205321/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_906 : ∀ (p : 906 < 1732), cc20Eq115CoefficientQ ⟨906, p⟩ = (9999245760205321 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 907 of the coefficient chain is the literal 9999245747215453/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_907 : ∀ (p : 907 < 1732), cc20Eq115CoefficientQ ⟨907, p⟩ = (9999245747215453 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 908 of the coefficient chain is the literal 9999245734259807/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_908 : ∀ (p : 908 < 1732), cc20Eq115CoefficientQ ⟨908, p⟩ = (9999245734259807 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 909 of the coefficient chain is the literal 999924572137523/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_909 : ∀ (p : 909 < 1732), cc20Eq115CoefficientQ ⟨909, p⟩ = (999924572137523 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 910 of the coefficient chain is the literal 24998114271299/ 25000000000000. -/
theorem cc20Eq115CoefficientQ_branch_910 : ∀ (p : 910 < 1732), cc20Eq115CoefficientQ ⟨910, p⟩ = (24998114271299 : ℚ) /  25000000000000 :=
  fun p => by rfl

/-- Branch 911 of the coefficient chain is the literal 9999245695710529/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_911 : ∀ (p : 911 < 1732), cc20Eq115CoefficientQ ⟨911, p⟩ = (9999245695710529 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 912 of the coefficient chain is the literal 2499811420735717/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_912 : ∀ (p : 912 < 1732), cc20Eq115CoefficientQ ⟨912, p⟩ = (2499811420735717 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 913 of the coefficient chain is the literal 1999849134044597/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_913 : ∀ (p : 913 < 1732), cc20Eq115CoefficientQ ⟨913, p⟩ = (1999849134044597 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 914 of the coefficient chain is the literal 399969826301927/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_914 : ∀ (p : 914 < 1732), cc20Eq115CoefficientQ ⟨914, p⟩ = (399969826301927 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 915 of the coefficient chain is the literal 156238213201809/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_915 : ∀ (p : 915 < 1732), cc20Eq115CoefficientQ ⟨915, p⟩ = (156238213201809 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 916 of the coefficient chain is the literal 9999245632325771/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_916 : ∀ (p : 916 < 1732), cc20Eq115CoefficientQ ⟨916, p⟩ = (9999245632325771 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 917 of the coefficient chain is the literal 999924561978129/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_917 : ∀ (p : 917 < 1732), cc20Eq115CoefficientQ ⟨917, p⟩ = (999924561978129 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 918 of the coefficient chain is the literal 2499811401819989/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_918 : ∀ (p : 918 < 1732), cc20Eq115CoefficientQ ⟨918, p⟩ = (2499811401819989 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 919 of the coefficient chain is the literal 2499811398705713/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_919 : ∀ (p : 919 < 1732), cc20Eq115CoefficientQ ⟨919, p⟩ = (2499811398705713 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 920 of the coefficient chain is the literal 9999245582405407/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_920 : ∀ (p : 920 < 1732), cc20Eq115CoefficientQ ⟨920, p⟩ = (9999245582405407 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 921 of the coefficient chain is the literal 1999849114006409/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_921 : ∀ (p : 921 < 1732), cc20Eq115CoefficientQ ⟨921, p⟩ = (1999849114006409 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 922 of the coefficient chain is the literal 9999245557703113/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_922 : ∀ (p : 922 < 1732), cc20Eq115CoefficientQ ⟨922, p⟩ = (9999245557703113 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 923 of the coefficient chain is the literal 2499811386354271/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_923 : ∀ (p : 923 < 1732), cc20Eq115CoefficientQ ⟨923, p⟩ = (2499811386354271 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 924 of the coefficient chain is the literal 2499811383293411/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_924 : ∀ (p : 924 < 1732), cc20Eq115CoefficientQ ⟨924, p⟩ = (2499811383293411 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 925 of the coefficient chain is the literal 9999245520971011/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_925 : ∀ (p : 925 < 1732), cc20Eq115CoefficientQ ⟨925, p⟩ = (9999245520971011 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 926 of the coefficient chain is the literal 1999849101761991/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_926 : ∀ (p : 926 < 1732), cc20Eq115CoefficientQ ⟨926, p⟩ = (1999849101761991 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 927 of the coefficient chain is the literal 9999245496692847/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_927 : ∀ (p : 927 < 1732), cc20Eq115CoefficientQ ⟨927, p⟩ = (9999245496692847 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 928 of the coefficient chain is the literal 4999622742307699/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_928 : ∀ (p : 928 < 1732), cc20Eq115CoefficientQ ⟨928, p⟩ = (4999622742307699 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 929 of the coefficient chain is the literal 9999245472580327/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_929 : ∀ (p : 929 < 1732), cc20Eq115CoefficientQ ⟨929, p⟩ = (9999245472580327 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 930 of the coefficient chain is the literal 9999245460585741/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_930 : ∀ (p : 930 < 1732), cc20Eq115CoefficientQ ⟨930, p⟩ = (9999245460585741 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 931 of the coefficient chain is the literal 9999245448630099/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_931 : ∀ (p : 931 < 1732), cc20Eq115CoefficientQ ⟨931, p⟩ = (9999245448630099 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 932 of the coefficient chain is the literal 999924543671001/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_932 : ∀ (p : 932 < 1732), cc20Eq115CoefficientQ ⟨932, p⟩ = (999924543671001 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 933 of the coefficient chain is the literal 624952839053377/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_933 : ∀ (p : 933 < 1732), cc20Eq115CoefficientQ ⟨933, p⟩ = (624952839053377 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 934 of the coefficient chain is the literal 4999622706511027/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_934 : ∀ (p : 934 < 1732), cc20Eq115CoefficientQ ⟨934, p⟩ = (4999622706511027 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 935 of the coefficient chain is the literal 4999622700616941/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_935 : ∀ (p : 935 < 1732), cc20Eq115CoefficientQ ⟨935, p⟩ = (4999622700616941 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 936 of the coefficient chain is the literal 499962269474237/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_936 : ∀ (p : 936 < 1732), cc20Eq115CoefficientQ ⟨936, p⟩ = (499962269474237 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 937 of the coefficient chain is the literal 312476418055447/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_937 : ∀ (p : 937 < 1732), cc20Eq115CoefficientQ ⟨937, p⟩ = (312476418055447 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 938 of the coefficient chain is the literal 999924536610537/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_938 : ∀ (p : 938 < 1732), cc20Eq115CoefficientQ ⟨938, p⟩ = (999924536610537 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 939 of the coefficient chain is the literal 9999245354475067/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_939 : ∀ (p : 939 < 1732), cc20Eq115CoefficientQ ⟨939, p⟩ = (9999245354475067 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 940 of the coefficient chain is the literal 9999245342882509/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_940 : ∀ (p : 940 < 1732), cc20Eq115CoefficientQ ⟨940, p⟩ = (9999245342882509 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 941 of the coefficient chain is the literal 2499811332833089/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_941 : ∀ (p : 941 < 1732), cc20Eq115CoefficientQ ⟨941, p⟩ = (2499811332833089 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 942 of the coefficient chain is the literal 2499811329957679/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_942 : ∀ (p : 942 < 1732), cc20Eq115CoefficientQ ⟨942, p⟩ = (2499811329957679 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 943 of the coefficient chain is the literal 9999245308351689/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_943 : ∀ (p : 943 < 1732), cc20Eq115CoefficientQ ⟨943, p⟩ = (9999245308351689 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 944 of the coefficient chain is the literal 9999245296920619/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_944 : ∀ (p : 944 < 1732), cc20Eq115CoefficientQ ⟨944, p⟩ = (9999245296920619 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 945 of the coefficient chain is the literal 39059551896589/ 39062500000000. -/
theorem cc20Eq115CoefficientQ_branch_945 : ∀ (p : 945 < 1732), cc20Eq115CoefficientQ ⟨945, p⟩ = (39059551896589 : ℚ) /  39062500000000 :=
  fun p => by rfl

/-- Branch 946 of the coefficient chain is the literal 312476414817811/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_946 : ∀ (p : 946 < 1732), cc20Eq115CoefficientQ ⟨946, p⟩ = (312476414817811 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 947 of the coefficient chain is the literal 9999245262849521/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_947 : ∀ (p : 947 < 1732), cc20Eq115CoefficientQ ⟨947, p⟩ = (9999245262849521 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 948 of the coefficient chain is the literal 312476414111817/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_948 : ∀ (p : 948 < 1732), cc20Eq115CoefficientQ ⟨948, p⟩ = (312476414111817 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 949 of the coefficient chain is the literal 9999245240339543/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_949 : ∀ (p : 949 < 1732), cc20Eq115CoefficientQ ⟨949, p⟩ = (9999245240339543 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 950 of the coefficient chain is the literal 4999622614568011/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_950 : ∀ (p : 950 < 1732), cc20Eq115CoefficientQ ⟨950, p⟩ = (4999622614568011 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 951 of the coefficient chain is the literal 9999245217972317/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_951 : ∀ (p : 951 < 1732), cc20Eq115CoefficientQ ⟨951, p⟩ = (9999245217972317 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 952 of the coefficient chain is the literal 9999245206843087/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_952 : ∀ (p : 952 < 1732), cc20Eq115CoefficientQ ⟨952, p⟩ = (9999245206843087 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 953 of the coefficient chain is the literal 9999245195754107/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_953 : ∀ (p : 953 < 1732), cc20Eq115CoefficientQ ⟨953, p⟩ = (9999245195754107 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 954 of the coefficient chain is the literal 1249905648087781/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_954 : ∀ (p : 954 < 1732), cc20Eq115CoefficientQ ⟨954, p⟩ = (1249905648087781 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 955 of the coefficient chain is the literal 9999245173690923/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_955 : ∀ (p : 955 < 1732), cc20Eq115CoefficientQ ⟨955, p⟩ = (9999245173690923 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 956 of the coefficient chain is the literal 199984903254319/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_956 : ∀ (p : 956 < 1732), cc20Eq115CoefficientQ ⟨956, p⟩ = (199984903254319 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 957 of the coefficient chain is the literal 78119102748059/ 78125000000000. -/
theorem cc20Eq115CoefficientQ_branch_957 : ∀ (p : 957 < 1732), cc20Eq115CoefficientQ ⟨957, p⟩ = (78119102748059 : ℚ) /  78125000000000 :=
  fun p => by rfl

/-- Branch 958 of the coefficient chain is the literal 624952821303921/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_958 : ∀ (p : 958 < 1732), cc20Eq115CoefficientQ ⟨958, p⟩ = (624952821303921 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 959 of the coefficient chain is the literal 9999245129999863/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_959 : ∀ (p : 959 < 1732), cc20Eq115CoefficientQ ⟨959, p⟩ = (9999245129999863 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 960 of the coefficient chain is the literal 4999622559584859/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_960 : ∀ (p : 960 < 1732), cc20Eq115CoefficientQ ⟨960, p⟩ = (4999622559584859 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 961 of the coefficient chain is the literal 1999849021674981/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_961 : ∀ (p : 961 < 1732), cc20Eq115CoefficientQ ⟨961, p⟩ = (1999849021674981 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 962 of the coefficient chain is the literal 4999622548808989/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_962 : ∀ (p : 962 < 1732), cc20Eq115CoefficientQ ⟨962, p⟩ = (4999622548808989 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 963 of the coefficient chain is the literal 9999245086901003/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_963 : ∀ (p : 963 < 1732), cc20Eq115CoefficientQ ⟨963, p⟩ = (9999245086901003 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 964 of the coefficient chain is the literal 4999622538105179/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_964 : ∀ (p : 964 < 1732), cc20Eq115CoefficientQ ⟨964, p⟩ = (4999622538105179 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 965 of the coefficient chain is the literal 9999245065563187/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_965 : ∀ (p : 965 < 1732), cc20Eq115CoefficientQ ⟨965, p⟩ = (9999245065563187 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 966 of the coefficient chain is the literal 499962252747387/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_966 : ∀ (p : 966 < 1732), cc20Eq115CoefficientQ ⟨966, p⟩ = (499962252747387 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 967 of the coefficient chain is the literal 9999245044370343/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_967 : ∀ (p : 967 < 1732), cc20Eq115CoefficientQ ⟨967, p⟩ = (9999245044370343 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 968 of the coefficient chain is the literal 4999622516913469/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_968 : ∀ (p : 968 < 1732), cc20Eq115CoefficientQ ⟨968, p⟩ = (4999622516913469 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 969 of the coefficient chain is the literal 9999245023317997/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_969 : ∀ (p : 969 < 1732), cc20Eq115CoefficientQ ⟨969, p⟩ = (9999245023317997 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 970 of the coefficient chain is the literal 9999245012859527/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_970 : ∀ (p : 970 < 1732), cc20Eq115CoefficientQ ⟨970, p⟩ = (9999245012859527 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 971 of the coefficient chain is the literal 624952812651111/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_971 : ∀ (p : 971 < 1732), cc20Eq115CoefficientQ ⟨971, p⟩ = (624952812651111 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 972 of the coefficient chain is the literal 78119101500051/ 78125000000000. -/
theorem cc20Eq115CoefficientQ_branch_972 : ∀ (p : 972 < 1732), cc20Eq115CoefficientQ ⟨972, p⟩ = (78119101500051 : ℚ) /  78125000000000 :=
  fun p => by rfl

/-- Branch 973 of the coefficient chain is the literal 4999622490819701/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_973 : ∀ (p : 973 < 1732), cc20Eq115CoefficientQ ⟨973, p⟩ = (4999622490819701 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 974 of the coefficient chain is the literal 1999848994260971/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_974 : ∀ (p : 974 < 1732), cc20Eq115CoefficientQ ⟨974, p⟩ = (1999848994260971 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 975 of the coefficient chain is the literal 9999244961007121/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_975 : ∀ (p : 975 < 1732), cc20Eq115CoefficientQ ⟨975, p⟩ = (9999244961007121 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 976 of the coefficient chain is the literal 1999848990148427/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_976 : ∀ (p : 976 < 1732), cc20Eq115CoefficientQ ⟨976, p⟩ = (1999848990148427 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 977 of the coefficient chain is the literal 4999622470255101/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_977 : ∀ (p : 977 < 1732), cc20Eq115CoefficientQ ⟨977, p⟩ = (4999622470255101 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 978 of the coefficient chain is the literal 4999622465157609/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_978 : ∀ (p : 978 < 1732), cc20Eq115CoefficientQ ⟨978, p⟩ = (4999622465157609 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 979 of the coefficient chain is the literal 79993959361209/ 80000000000000. -/
theorem cc20Eq115CoefficientQ_branch_979 : ∀ (p : 979 < 1732), cc20Eq115CoefficientQ ⟨979, p⟩ = (79993959361209 : ℚ) /  80000000000000 :=
  fun p => by rfl

/-- Branch 980 of the coefficient chain is the literal 4999622455010657/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_980 : ∀ (p : 980 < 1732), cc20Eq115CoefficientQ ⟨980, p⟩ = (4999622455010657 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 981 of the coefficient chain is the literal 9999244899927549/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_981 : ∀ (p : 981 < 1732), cc20Eq115CoefficientQ ⟨981, p⟩ = (9999244899927549 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 982 of the coefficient chain is the literal 1999848977972899/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_982 : ∀ (p : 982 < 1732), cc20Eq115CoefficientQ ⟨982, p⟩ = (1999848977972899 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 983 of the coefficient chain is the literal 9999244879837113/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_983 : ∀ (p : 983 < 1732), cc20Eq115CoefficientQ ⟨983, p⟩ = (9999244879837113 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 984 of the coefficient chain is the literal 2499811217460721/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_984 : ∀ (p : 984 < 1732), cc20Eq115CoefficientQ ⟨984, p⟩ = (2499811217460721 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 985 of the coefficient chain is the literal 4999622429941263/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_985 : ∀ (p : 985 < 1732), cc20Eq115CoefficientQ ⟨985, p⟩ = (4999622429941263 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 986 of the coefficient chain is the literal 1999848969991191/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_986 : ∀ (p : 986 < 1732), cc20Eq115CoefficientQ ⟨986, p⟩ = (1999848969991191 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 987 of the coefficient chain is the literal 1999848968009007/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_987 : ∀ (p : 987 < 1732), cc20Eq115CoefficientQ ⟨987, p⟩ = (1999848968009007 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 988 of the coefficient chain is the literal 4999622415091711/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_988 : ∀ (p : 988 < 1732), cc20Eq115CoefficientQ ⟨988, p⟩ = (4999622415091711 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 989 of the coefficient chain is the literal 9999244820356031/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_989 : ∀ (p : 989 < 1732), cc20Eq115CoefficientQ ⟨989, p⟩ = (9999244820356031 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 990 of the coefficient chain is the literal 4999622405278717/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_990 : ∀ (p : 990 < 1732), cc20Eq115CoefficientQ ⟨990, p⟩ = (4999622405278717 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 991 of the coefficient chain is the literal 4999622400394987/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_991 : ∀ (p : 991 < 1732), cc20Eq115CoefficientQ ⟨991, p⟩ = (4999622400394987 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 992 of the coefficient chain is the literal 9999244791053619/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_992 : ∀ (p : 992 < 1732), cc20Eq115CoefficientQ ⟨992, p⟩ = (9999244791053619 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 993 of the coefficient chain is the literal 9999244781351313/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_993 : ∀ (p : 993 < 1732), cc20Eq115CoefficientQ ⟨993, p⟩ = (9999244781351313 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 994 of the coefficient chain is the literal 399969790867271/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_994 : ∀ (p : 994 < 1732), cc20Eq115CoefficientQ ⟨994, p⟩ = (399969790867271 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 995 of the coefficient chain is the literal 9999244762045801/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_995 : ∀ (p : 995 < 1732), cc20Eq115CoefficientQ ⟨995, p⟩ = (9999244762045801 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 996 of the coefficient chain is the literal 2499811188109257/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_996 : ∀ (p : 996 < 1732), cc20Eq115CoefficientQ ⟨996, p⟩ = (2499811188109257 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 997 of the coefficient chain is the literal 9999244742862963/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_997 : ∀ (p : 997 < 1732), cc20Eq115CoefficientQ ⟨997, p⟩ = (9999244742862963 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 998 of the coefficient chain is the literal 624952795832319/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_998 : ∀ (p : 998 < 1732), cc20Eq115CoefficientQ ⟨998, p⟩ = (624952795832319 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 999 of the coefficient chain is the literal 2499811180951327/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_999 : ∀ (p : 999 < 1732), cc20Eq115CoefficientQ ⟨999, p⟩ = (2499811180951327 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1000 of the coefficient chain is the literal 4999622357163083/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1000 : ∀ (p : 1000 < 1732), cc20Eq115CoefficientQ ⟨1000, p⟩ = (4999622357163083 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1001 of the coefficient chain is the literal 1999848940974893/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1001 : ∀ (p : 1001 < 1732), cc20Eq115CoefficientQ ⟨1001, p⟩ = (1999848940974893 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1002 of the coefficient chain is the literal 9999244695455713/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1002 : ∀ (p : 1002 < 1732), cc20Eq115CoefficientQ ⟨1002, p⟩ = (9999244695455713 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1003 of the coefficient chain is the literal 4999622343033691/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1003 : ∀ (p : 1003 < 1732), cc20Eq115CoefficientQ ⟨1003, p⟩ = (4999622343033691 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1004 of the coefficient chain is the literal 9999244676709731/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1004 : ∀ (p : 1004 < 1732), cc20Eq115CoefficientQ ⟨1004, p⟩ = (9999244676709731 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1005 of the coefficient chain is the literal 1999848933476349/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1005 : ∀ (p : 1005 < 1732), cc20Eq115CoefficientQ ⟨1005, p⟩ = (1999848933476349 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1006 of the coefficient chain is the literal 624952791130319/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1006 : ∀ (p : 1006 < 1732), cc20Eq115CoefficientQ ⟨1006, p⟩ = (624952791130319 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1007 of the coefficient chain is the literal 9999244648819977/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1007 : ∀ (p : 1007 < 1732), cc20Eq115CoefficientQ ⟨1007, p⟩ = (9999244648819977 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1008 of the coefficient chain is the literal 4999622319791063/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1008 : ∀ (p : 1008 < 1732), cc20Eq115CoefficientQ ⟨1008, p⟩ = (4999622319791063 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1009 of the coefficient chain is the literal 9999244630377259/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1009 : ∀ (p : 1009 < 1732), cc20Eq115CoefficientQ ⟨1009, p⟩ = (9999244630377259 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1010 of the coefficient chain is the literal 1999848924240537/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1010 : ∀ (p : 1010 < 1732), cc20Eq115CoefficientQ ⟨1010, p⟩ = (1999848924240537 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1011 of the coefficient chain is the literal 499962230602819/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1011 : ∀ (p : 1011 < 1732), cc20Eq115CoefficientQ ⟨1011, p⟩ = (499962230602819 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1012 of the coefficient chain is the literal 2499811150735063/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1012 : ∀ (p : 1012 < 1732), cc20Eq115CoefficientQ ⟨1012, p⟩ = (2499811150735063 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1013 of the coefficient chain is the literal 2499811148463861/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1013 : ∀ (p : 1013 < 1732), cc20Eq115CoefficientQ ⟨1013, p⟩ = (2499811148463861 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1014 of the coefficient chain is the literal 1999848916959831/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1014 : ∀ (p : 1014 < 1732), cc20Eq115CoefficientQ ⟨1014, p⟩ = (1999848916959831 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1015 of the coefficient chain is the literal 4999622287887077/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1015 : ∀ (p : 1015 < 1732), cc20Eq115CoefficientQ ⟨1015, p⟩ = (4999622287887077 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1016 of the coefficient chain is the literal 9999244566773/ 10000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1016 : ∀ (p : 1016 < 1732), cc20Eq115CoefficientQ ⟨1016, p⟩ = (9999244566773 : ℚ) /  10000000000000 :=
  fun p => by rfl

/-- Branch 1017 of the coefficient chain is the literal 499962227890237/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1017 : ∀ (p : 1017 < 1732), cc20Eq115CoefficientQ ⟨1017, p⟩ = (499962227890237 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1018 of the coefficient chain is the literal 1249905568608259/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1018 : ∀ (p : 1018 < 1732), cc20Eq115CoefficientQ ⟨1018, p⟩ = (1249905568608259 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1019 of the coefficient chain is the literal 1999848907991227/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1019 : ∀ (p : 1019 < 1732), cc20Eq115CoefficientQ ⟨1019, p⟩ = (1999848907991227 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1020 of the coefficient chain is the literal 999924453107581/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1020 : ∀ (p : 1020 < 1732), cc20Eq115CoefficientQ ⟨1020, p⟩ = (999924453107581 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1021 of the coefficient chain is the literal 9999244522222381/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1021 : ∀ (p : 1021 < 1732), cc20Eq115CoefficientQ ⟨1021, p⟩ = (9999244522222381 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1022 of the coefficient chain is the literal 9999244513398349/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1022 : ∀ (p : 1022 < 1732), cc20Eq115CoefficientQ ⟨1022, p⟩ = (9999244513398349 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1023 of the coefficient chain is the literal 4999622252303351/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1023 : ∀ (p : 1023 < 1732), cc20Eq115CoefficientQ ⟨1023, p⟩ = (4999622252303351 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1024 of the coefficient chain is the literal 9999244495842501/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1024 : ∀ (p : 1024 < 1732), cc20Eq115CoefficientQ ⟨1024, p⟩ = (9999244495842501 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1025 of the coefficient chain is the literal 499962224356081/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1025 : ∀ (p : 1025 < 1732), cc20Eq115CoefficientQ ⟨1025, p⟩ = (499962224356081 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1026 of the coefficient chain is the literal 9999244478382001/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1026 : ∀ (p : 1026 < 1732), cc20Eq115CoefficientQ ⟨1026, p⟩ = (9999244478382001 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1027 of the coefficient chain is the literal 9999244469701497/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1027 : ∀ (p : 1027 < 1732), cc20Eq115CoefficientQ ⟨1027, p⟩ = (9999244469701497 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1028 of the coefficient chain is the literal 1999848892210029/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1028 : ∀ (p : 1028 < 1732), cc20Eq115CoefficientQ ⟨1028, p⟩ = (1999848892210029 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1029 of the coefficient chain is the literal 1999848890479147/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1029 : ∀ (p : 1029 < 1732), cc20Eq115CoefficientQ ⟨1029, p⟩ = (1999848890479147 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1030 of the coefficient chain is the literal 9999244443829047/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1030 : ∀ (p : 1030 < 1732), cc20Eq115CoefficientQ ⟨1030, p⟩ = (9999244443829047 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1031 of the coefficient chain is the literal 15623819430091/ 15625000000000. -/
theorem cc20Eq115CoefficientQ_branch_1031 : ∀ (p : 1031 < 1732), cc20Eq115CoefficientQ ⟨1031, p⟩ = (15623819430091 : ℚ) /  15625000000000 :=
  fun p => by rfl

/-- Branch 1032 of the coefficient chain is the literal 9999244426722681/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1032 : ∀ (p : 1032 < 1732), cc20Eq115CoefficientQ ⟨1032, p⟩ = (9999244426722681 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1033 of the coefficient chain is the literal 9999244418200327/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1033 : ∀ (p : 1033 < 1732), cc20Eq115CoefficientQ ⟨1033, p⟩ = (9999244418200327 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1034 of the coefficient chain is the literal 2499811102428443/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1034 : ∀ (p : 1034 < 1732), cc20Eq115CoefficientQ ⟨1034, p⟩ = (2499811102428443 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1035 of the coefficient chain is the literal 1999848880250791/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1035 : ∀ (p : 1035 < 1732), cc20Eq115CoefficientQ ⟨1035, p⟩ = (1999848880250791 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1036 of the coefficient chain is the literal 9999244392822523/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1036 : ∀ (p : 1036 < 1732), cc20Eq115CoefficientQ ⟨1036, p⟩ = (9999244392822523 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1037 of the coefficient chain is the literal 9999244384416517/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1037 : ∀ (p : 1037 < 1732), cc20Eq115CoefficientQ ⟨1037, p⟩ = (9999244384416517 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1038 of the coefficient chain is the literal 9999244376039467/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1038 : ∀ (p : 1038 < 1732), cc20Eq115CoefficientQ ⟨1038, p⟩ = (9999244376039467 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1039 of the coefficient chain is the literal 9999244367685549/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1039 : ∀ (p : 1039 < 1732), cc20Eq115CoefficientQ ⟨1039, p⟩ = (9999244367685549 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1040 of the coefficient chain is the literal 9999244359361603/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1040 : ∀ (p : 1040 < 1732), cc20Eq115CoefficientQ ⟨1040, p⟩ = (9999244359361603 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1041 of the coefficient chain is the literal 9999244351064741/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1041 : ∀ (p : 1041 < 1732), cc20Eq115CoefficientQ ⟨1041, p⟩ = (9999244351064741 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1042 of the coefficient chain is the literal 1999848868558481/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1042 : ∀ (p : 1042 < 1732), cc20Eq115CoefficientQ ⟨1042, p⟩ = (1999848868558481 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1043 of the coefficient chain is the literal 2499811083637363/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1043 : ∀ (p : 1043 < 1732), cc20Eq115CoefficientQ ⟨1043, p⟩ = (2499811083637363 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1044 of the coefficient chain is the literal 9999244326330833/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1044 : ∀ (p : 1044 < 1732), cc20Eq115CoefficientQ ⟨1044, p⟩ = (9999244326330833 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1045 of the coefficient chain is the literal 9999244318140149/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1045 : ∀ (p : 1045 < 1732), cc20Eq115CoefficientQ ⟨1045, p⟩ = (9999244318140149 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1046 of the coefficient chain is the literal 9999244309964233/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1046 : ∀ (p : 1046 < 1732), cc20Eq115CoefficientQ ⟨1046, p⟩ = (9999244309964233 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1047 of the coefficient chain is the literal 9999244301836313/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1047 : ∀ (p : 1047 < 1732), cc20Eq115CoefficientQ ⟨1047, p⟩ = (9999244301836313 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1048 of the coefficient chain is the literal 999924429372553/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1048 : ∀ (p : 1048 < 1732), cc20Eq115CoefficientQ ⟨1048, p⟩ = (999924429372553 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1049 of the coefficient chain is the literal 9999244285631511/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1049 : ∀ (p : 1049 < 1732), cc20Eq115CoefficientQ ⟨1049, p⟩ = (9999244285631511 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1050 of the coefficient chain is the literal 9999244277571089/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1050 : ∀ (p : 1050 < 1732), cc20Eq115CoefficientQ ⟨1050, p⟩ = (9999244277571089 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1051 of the coefficient chain is the literal 9999244269536529/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1051 : ∀ (p : 1051 < 1732), cc20Eq115CoefficientQ ⟨1051, p⟩ = (9999244269536529 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1052 of the coefficient chain is the literal 999924426152797/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1052 : ∀ (p : 1052 < 1732), cc20Eq115CoefficientQ ⟨1052, p⟩ = (999924426152797 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1053 of the coefficient chain is the literal 624952765846523/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1053 : ∀ (p : 1053 < 1732), cc20Eq115CoefficientQ ⟨1053, p⟩ = (624952765846523 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1054 of the coefficient chain is the literal 999924424558677/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1054 : ∀ (p : 1054 < 1732), cc20Eq115CoefficientQ ⟨1054, p⟩ = (999924424558677 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1055 of the coefficient chain is the literal 3999697695061/ 4000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1055 : ∀ (p : 1055 < 1732), cc20Eq115CoefficientQ ⟨1055, p⟩ = (3999697695061 : ℚ) /  4000000000000 :=
  fun p => by rfl

/-- Branch 1056 of the coefficient chain is the literal 2499811057436001/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1056 : ∀ (p : 1056 < 1732), cc20Eq115CoefficientQ ⟨1056, p⟩ = (2499811057436001 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1057 of the coefficient chain is the literal 9999244221859779/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1057 : ∀ (p : 1057 < 1732), cc20Eq115CoefficientQ ⟨1057, p⟩ = (9999244221859779 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1058 of the coefficient chain is the literal 1249905526750489/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1058 : ∀ (p : 1058 < 1732), cc20Eq115CoefficientQ ⟨1058, p⟩ = (1249905526750489 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1059 of the coefficient chain is the literal 2499811051542907/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1059 : ∀ (p : 1059 < 1732), cc20Eq115CoefficientQ ⟨1059, p⟩ = (2499811051542907 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1060 of the coefficient chain is the literal 4999622099182213/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1060 : ∀ (p : 1060 < 1732), cc20Eq115CoefficientQ ⟨1060, p⟩ = (4999622099182213 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1061 of the coefficient chain is the literal 4999622095293547/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1061 : ∀ (p : 1061 < 1732), cc20Eq115CoefficientQ ⟨1061, p⟩ = (4999622095293547 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1062 of the coefficient chain is the literal 9999244182826507/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1062 : ∀ (p : 1062 < 1732), cc20Eq115CoefficientQ ⟨1062, p⟩ = (9999244182826507 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1063 of the coefficient chain is the literal 9999244175095459/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1063 : ∀ (p : 1063 < 1732), cc20Eq115CoefficientQ ⟨1063, p⟩ = (9999244175095459 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1064 of the coefficient chain is the literal 4999622083692783/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1064 : ∀ (p : 1064 < 1732), cc20Eq115CoefficientQ ⟨1064, p⟩ = (4999622083692783 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1065 of the coefficient chain is the literal 4999622079851221/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1065 : ∀ (p : 1065 < 1732), cc20Eq115CoefficientQ ⟨1065, p⟩ = (4999622079851221 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1066 of the coefficient chain is the literal 4999622076021299/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1066 : ∀ (p : 1066 < 1732), cc20Eq115CoefficientQ ⟨1066, p⟩ = (4999622076021299 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1067 of the coefficient chain is the literal 9999244144409193/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1067 : ∀ (p : 1067 < 1732), cc20Eq115CoefficientQ ⟨1067, p⟩ = (9999244144409193 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1068 of the coefficient chain is the literal 9999244136799653/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1068 : ∀ (p : 1068 < 1732), cc20Eq115CoefficientQ ⟨1068, p⟩ = (9999244136799653 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1069 of the coefficient chain is the literal 4999622064607349/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1069 : ∀ (p : 1069 < 1732), cc20Eq115CoefficientQ ⟨1069, p⟩ = (4999622064607349 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1070 of the coefficient chain is the literal 9999244121650357/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1070 : ∀ (p : 1070 < 1732), cc20Eq115CoefficientQ ⟨1070, p⟩ = (9999244121650357 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1071 of the coefficient chain is the literal 2499811028528539/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1071 : ∀ (p : 1071 < 1732), cc20Eq115CoefficientQ ⟨1071, p⟩ = (2499811028528539 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1072 of the coefficient chain is the literal 1249905513324893/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1072 : ∀ (p : 1072 < 1732), cc20Eq115CoefficientQ ⟨1072, p⟩ = (1249905513324893 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1073 of the coefficient chain is the literal 4999622049554243/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1073 : ∀ (p : 1073 < 1732), cc20Eq115CoefficientQ ⟨1073, p⟩ = (4999622049554243 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1074 of the coefficient chain is the literal 4999622045821643/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1074 : ∀ (p : 1074 < 1732), cc20Eq115CoefficientQ ⟨1074, p⟩ = (4999622045821643 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1075 of the coefficient chain is the literal 9999244084201903/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1075 : ∀ (p : 1075 < 1732), cc20Eq115CoefficientQ ⟨1075, p⟩ = (9999244084201903 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1076 of the coefficient chain is the literal 4999622038391609/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1076 : ∀ (p : 1076 < 1732), cc20Eq115CoefficientQ ⟨1076, p⟩ = (4999622038391609 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1077 of the coefficient chain is the literal 9999244069388419/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1077 : ∀ (p : 1077 < 1732), cc20Eq115CoefficientQ ⟨1077, p⟩ = (9999244069388419 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1078 of the coefficient chain is the literal 624952753875897/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1078 : ∀ (p : 1078 < 1732), cc20Eq115CoefficientQ ⟨1078, p⟩ = (624952753875897 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1079 of the coefficient chain is the literal 4999622027333187/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1079 : ∀ (p : 1079 < 1732), cc20Eq115CoefficientQ ⟨1079, p⟩ = (4999622027333187 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1080 of the coefficient chain is the literal 499962202367001/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1080 : ∀ (p : 1080 < 1732), cc20Eq115CoefficientQ ⟨1080, p⟩ = (499962202367001 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1081 of the coefficient chain is the literal 9999244040039491/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1081 : ∀ (p : 1081 < 1732), cc20Eq115CoefficientQ ⟨1081, p⟩ = (9999244040039491 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1082 of the coefficient chain is the literal 4999622016379179/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1082 : ∀ (p : 1082 < 1732), cc20Eq115CoefficientQ ⟨1082, p⟩ = (4999622016379179 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1083 of the coefficient chain is the literal 1249905503187929/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1083 : ∀ (p : 1083 < 1732), cc20Eq115CoefficientQ ⟨1083, p⟩ = (1249905503187929 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1084 of the coefficient chain is the literal 2499811004567833/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1084 : ∀ (p : 1084 < 1732), cc20Eq115CoefficientQ ⟨1084, p⟩ = (2499811004567833 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1085 of the coefficient chain is the literal 999924401105917/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1085 : ∀ (p : 1085 < 1732), cc20Eq115CoefficientQ ⟨1085, p⟩ = (999924401105917 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1086 of the coefficient chain is the literal 2499811000967951/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1086 : ∀ (p : 1086 < 1732), cc20Eq115CoefficientQ ⟨1086, p⟩ = (2499811000967951 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1087 of the coefficient chain is the literal 4999621998353509/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1087 : ∀ (p : 1087 < 1732), cc20Eq115CoefficientQ ⟨1087, p⟩ = (4999621998353509 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1088 of the coefficient chain is the literal 124990549869397/ 125000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1088 : ∀ (p : 1088 < 1732), cc20Eq115CoefficientQ ⟨1088, p⟩ = (124990549869397 : ℚ) /  125000000000000 :=
  fun p => by rfl

/-- Branch 1089 of the coefficient chain is the literal 9999243982434519/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1089 : ∀ (p : 1089 < 1732), cc20Eq115CoefficientQ ⟨1089, p⟩ = (9999243982434519 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1090 of the coefficient chain is the literal 1249905496920037/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1090 : ∀ (p : 1090 < 1732), cc20Eq115CoefficientQ ⟨1090, p⟩ = (1249905496920037 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1091 of the coefficient chain is the literal 1999848793656861/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1091 : ∀ (p : 1091 < 1732), cc20Eq115CoefficientQ ⟨1091, p⟩ = (1999848793656861 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1092 of the coefficient chain is the literal 499962198061561/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1092 : ∀ (p : 1092 < 1732), cc20Eq115CoefficientQ ⟨1092, p⟩ = (499962198061561 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1093 of the coefficient chain is the literal 2499810988550413/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1093 : ∀ (p : 1093 < 1732), cc20Eq115CoefficientQ ⟨1093, p⟩ = (2499810988550413 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1094 of the coefficient chain is the literal 2499810986798697/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1094 : ∀ (p : 1094 < 1732), cc20Eq115CoefficientQ ⟨1094, p⟩ = (2499810986798697 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1095 of the coefficient chain is the literal 9999243940207251/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1095 : ∀ (p : 1095 < 1732), cc20Eq115CoefficientQ ⟨1095, p⟩ = (9999243940207251 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1096 of the coefficient chain is the literal 9999243933246037/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1096 : ∀ (p : 1096 < 1732), cc20Eq115CoefficientQ ⟨1096, p⟩ = (9999243933246037 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1097 of the coefficient chain is the literal 1999848785260953/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1097 : ∀ (p : 1097 < 1732), cc20Eq115CoefficientQ ⟨1097, p⟩ = (1999848785260953 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1098 of the coefficient chain is the literal 2499810979846023/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1098 : ∀ (p : 1098 < 1732), cc20Eq115CoefficientQ ⟨1098, p⟩ = (2499810979846023 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1099 of the coefficient chain is the literal 4999621956243669/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1099 : ∀ (p : 1099 < 1732), cc20Eq115CoefficientQ ⟨1099, p⟩ = (4999621956243669 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1100 of the coefficient chain is the literal 79993951244889/ 80000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1100 : ∀ (p : 1100 < 1732), cc20Eq115CoefficientQ ⟨1100, p⟩ = (79993951244889 : ℚ) /  80000000000000 :=
  fun p => by rfl

/-- Branch 1101 of the coefficient chain is the literal 4999621949377689/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1101 : ∀ (p : 1101 < 1732), cc20Eq115CoefficientQ ⟨1101, p⟩ = (4999621949377689 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1102 of the coefficient chain is the literal 9999243891924937/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1102 : ∀ (p : 1102 < 1732), cc20Eq115CoefficientQ ⟨1102, p⟩ = (9999243891924937 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1103 of the coefficient chain is the literal 9999243885115637/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1103 : ∀ (p : 1103 < 1732), cc20Eq115CoefficientQ ⟨1103, p⟩ = (9999243885115637 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1104 of the coefficient chain is the literal 312476371197651/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1104 : ∀ (p : 1104 < 1732), cc20Eq115CoefficientQ ⟨1104, p⟩ = (312476371197651 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 1105 of the coefficient chain is the literal 1999848774311437/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1105 : ∀ (p : 1105 < 1732), cc20Eq115CoefficientQ ⟨1105, p⟩ = (1999848774311437 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1106 of the coefficient chain is the literal 1249905483101317/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1106 : ∀ (p : 1106 < 1732), cc20Eq115CoefficientQ ⟨1106, p⟩ = (1249905483101317 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1107 of the coefficient chain is the literal 999924385808781/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1107 : ∀ (p : 1107 < 1732), cc20Eq115CoefficientQ ⟨1107, p⟩ = (999924385808781 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1108 of the coefficient chain is the literal 2499810962846039/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1108 : ∀ (p : 1108 < 1732), cc20Eq115CoefficientQ ⟨1108, p⟩ = (2499810962846039 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1109 of the coefficient chain is the literal 9999243844701041/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1109 : ∀ (p : 1109 < 1732), cc20Eq115CoefficientQ ⟨1109, p⟩ = (9999243844701041 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1110 of the coefficient chain is the literal 4999621919018057/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1110 : ∀ (p : 1110 < 1732), cc20Eq115CoefficientQ ⟨1110, p⟩ = (4999621919018057 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1111 of the coefficient chain is the literal 4999621915698317/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1111 : ∀ (p : 1111 < 1732), cc20Eq115CoefficientQ ⟨1111, p⟩ = (4999621915698317 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1112 of the coefficient chain is the literal 9999243824776869/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1112 : ∀ (p : 1112 < 1732), cc20Eq115CoefficientQ ⟨1112, p⟩ = (9999243824776869 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1113 of the coefficient chain is the literal 1249905477272691/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1113 : ∀ (p : 1113 < 1732), cc20Eq115CoefficientQ ⟨1113, p⟩ = (1249905477272691 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1114 of the coefficient chain is the literal 9999243811601243/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1114 : ∀ (p : 1114 < 1732), cc20Eq115CoefficientQ ⟨1114, p⟩ = (9999243811601243 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1115 of the coefficient chain is the literal 4999621902520817/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1115 : ∀ (p : 1115 < 1732), cc20Eq115CoefficientQ ⟨1115, p⟩ = (4999621902520817 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1116 of the coefficient chain is the literal 9999243798506331/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1116 : ∀ (p : 1116 < 1732), cc20Eq115CoefficientQ ⟨1116, p⟩ = (9999243798506331 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1117 of the coefficient chain is the literal 199984875839803/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1117 : ∀ (p : 1117 < 1732), cc20Eq115CoefficientQ ⟨1117, p⟩ = (199984875839803 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 1118 of the coefficient chain is the literal 9999243785495259/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1118 : ∀ (p : 1118 < 1732), cc20Eq115CoefficientQ ⟨1118, p⟩ = (9999243785495259 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1119 of the coefficient chain is the literal 9999243779024051/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1119 : ∀ (p : 1119 < 1732), cc20Eq115CoefficientQ ⟨1119, p⟩ = (9999243779024051 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1120 of the coefficient chain is the literal 1999848754509589/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1120 : ∀ (p : 1120 < 1732), cc20Eq115CoefficientQ ⟨1120, p⟩ = (1999848754509589 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1121 of the coefficient chain is the literal 999924376611751/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1121 : ∀ (p : 1121 < 1732), cc20Eq115CoefficientQ ⟨1121, p⟩ = (999924376611751 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1122 of the coefficient chain is the literal 2499810939927171/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1122 : ∀ (p : 1122 < 1732), cc20Eq115CoefficientQ ⟨1122, p⟩ = (2499810939927171 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1123 of the coefficient chain is the literal 9999243753313287/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1123 : ∀ (p : 1123 < 1732), cc20Eq115CoefficientQ ⟨1123, p⟩ = (9999243753313287 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1124 of the coefficient chain is the literal 2499810936735753/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1124 : ∀ (p : 1124 < 1732), cc20Eq115CoefficientQ ⟨1124, p⟩ = (2499810936735753 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1125 of the coefficient chain is the literal 4999621870293627/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1125 : ∀ (p : 1125 < 1732), cc20Eq115CoefficientQ ⟨1125, p⟩ = (4999621870293627 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1126 of the coefficient chain is the literal 4999621867125551/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1126 : ∀ (p : 1126 < 1732), cc20Eq115CoefficientQ ⟨1126, p⟩ = (4999621867125551 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1127 of the coefficient chain is the literal 4999621863967561/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1127 : ∀ (p : 1127 < 1732), cc20Eq115CoefficientQ ⟨1127, p⟩ = (4999621863967561 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1128 of the coefficient chain is the literal 9999243721638401/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1128 : ∀ (p : 1128 < 1732), cc20Eq115CoefficientQ ⟨1128, p⟩ = (9999243721638401 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1129 of the coefficient chain is the literal 9999243715367043/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1129 : ∀ (p : 1129 < 1732), cc20Eq115CoefficientQ ⟨1129, p⟩ = (9999243715367043 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1130 of the coefficient chain is the literal 9999243709110801/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1130 : ∀ (p : 1130 < 1732), cc20Eq115CoefficientQ ⟨1130, p⟩ = (9999243709110801 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1131 of the coefficient chain is the literal 499962185143691/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1131 : ∀ (p : 1131 < 1732), cc20Eq115CoefficientQ ⟨1131, p⟩ = (499962185143691 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1132 of the coefficient chain is the literal 9999243696660807/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1132 : ∀ (p : 1132 < 1732), cc20Eq115CoefficientQ ⟨1132, p⟩ = (9999243696660807 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1133 of the coefficient chain is the literal 4999621845231857/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1133 : ∀ (p : 1133 < 1732), cc20Eq115CoefficientQ ⟨1133, p⟩ = (4999621845231857 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1134 of the coefficient chain is the literal 1249905460535623/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1134 : ∀ (p : 1134 < 1732), cc20Eq115CoefficientQ ⟨1134, p⟩ = (1249905460535623 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1135 of the coefficient chain is the literal 9999243678128011/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1135 : ∀ (p : 1135 < 1732), cc20Eq115CoefficientQ ⟨1135, p⟩ = (9999243678128011 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1136 of the coefficient chain is the literal 9999243671988811/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1136 : ∀ (p : 1136 < 1732), cc20Eq115CoefficientQ ⟨1136, p⟩ = (9999243671988811 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1137 of the coefficient chain is the literal 499962183293519/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1137 : ∀ (p : 1137 < 1732), cc20Eq115CoefficientQ ⟨1137, p⟩ = (499962183293519 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1138 of the coefficient chain is the literal 399969746390809/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1138 : ∀ (p : 1138 < 1732), cc20Eq115CoefficientQ ⟨1138, p⟩ = (399969746390809 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1139 of the coefficient chain is the literal 4999621826844989/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1139 : ∀ (p : 1139 < 1732), cc20Eq115CoefficientQ ⟨1139, p⟩ = (4999621826844989 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1140 of the coefficient chain is the literal 9999243647628061/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1140 : ∀ (p : 1140 < 1732), cc20Eq115CoefficientQ ⟨1140, p⟩ = (9999243647628061 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1141 of the coefficient chain is the literal 2499810910396531/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1141 : ∀ (p : 1141 < 1732), cc20Eq115CoefficientQ ⟨1141, p⟩ = (2499810910396531 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1142 of the coefficient chain is the literal 4999621817780287/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1142 : ∀ (p : 1142 < 1732), cc20Eq115CoefficientQ ⟨1142, p⟩ = (4999621817780287 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1143 of the coefficient chain is the literal 999924362955383/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1143 : ∀ (p : 1143 < 1732), cc20Eq115CoefficientQ ⟨1143, p⟩ = (999924362955383 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1144 of the coefficient chain is the literal 9999243623569051/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1144 : ∀ (p : 1144 < 1732), cc20Eq115CoefficientQ ⟨1144, p⟩ = (9999243623569051 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1145 of the coefficient chain is the literal 9999243617600861/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1145 : ∀ (p : 1145 < 1732), cc20Eq115CoefficientQ ⟨1145, p⟩ = (9999243617600861 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1146 of the coefficient chain is the literal 624952725728291/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1146 : ∀ (p : 1146 < 1732), cc20Eq115CoefficientQ ⟨1146, p⟩ = (624952725728291 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1147 of the coefficient chain is the literal 312476362678861/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1147 : ∀ (p : 1147 < 1732), cc20Eq115CoefficientQ ⟨1147, p⟩ = (312476362678861 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 1148 of the coefficient chain is the literal 124990544997663/ 125000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1148 : ∀ (p : 1148 < 1732), cc20Eq115CoefficientQ ⟨1148, p⟩ = (124990544997663 : ℚ) /  125000000000000 :=
  fun p => by rfl

/-- Branch 1149 of the coefficient chain is the literal 999924359391959/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1149 : ∀ (p : 1149 < 1732), cc20Eq115CoefficientQ ⟨1149, p⟩ = (999924359391959 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1150 of the coefficient chain is the literal 156238181063223/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_1150 : ∀ (p : 1150 < 1732), cc20Eq115CoefficientQ ⟨1150, p⟩ = (156238181063223 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 1151 of the coefficient chain is the literal 9999243582188397/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1151 : ∀ (p : 1151 < 1732), cc20Eq115CoefficientQ ⟨1151, p⟩ = (9999243582188397 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1152 of the coefficient chain is the literal 1249905447044063/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1152 : ∀ (p : 1152 < 1732), cc20Eq115CoefficientQ ⟨1152, p⟩ = (1249905447044063 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1153 of the coefficient chain is the literal 9999243570532423/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1153 : ∀ (p : 1153 < 1732), cc20Eq115CoefficientQ ⟨1153, p⟩ = (9999243570532423 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1154 of the coefficient chain is the literal 156238180698933/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_1154 : ∀ (p : 1154 < 1732), cc20Eq115CoefficientQ ⟨1154, p⟩ = (156238180698933 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 1155 of the coefficient chain is the literal 4999621779473921/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1155 : ∀ (p : 1155 < 1732), cc20Eq115CoefficientQ ⟨1155, p⟩ = (4999621779473921 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1156 of the coefficient chain is the literal 624952722073931/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1156 : ∀ (p : 1156 < 1732), cc20Eq115CoefficientQ ⟨1156, p⟩ = (624952722073931 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1157 of the coefficient chain is the literal 2499810886863163/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1157 : ∀ (p : 1157 < 1732), cc20Eq115CoefficientQ ⟨1157, p⟩ = (2499810886863163 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1158 of the coefficient chain is the literal 9999243541708697/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1158 : ∀ (p : 1158 < 1732), cc20Eq115CoefficientQ ⟨1158, p⟩ = (9999243541708697 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1159 of the coefficient chain is the literal 999924353599679/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1159 : ∀ (p : 1159 < 1732), cc20Eq115CoefficientQ ⟨1159, p⟩ = (999924353599679 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1160 of the coefficient chain is the literal 4999621765151819/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1160 : ∀ (p : 1160 < 1732), cc20Eq115CoefficientQ ⟨1160, p⟩ = (4999621765151819 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1161 of the coefficient chain is the literal 4999621762315657/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1161 : ∀ (p : 1161 < 1732), cc20Eq115CoefficientQ ⟨1161, p⟩ = (4999621762315657 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1162 of the coefficient chain is the literal 4999621759487371/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1162 : ∀ (p : 1162 < 1732), cc20Eq115CoefficientQ ⟨1162, p⟩ = (4999621759487371 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1163 of the coefficient chain is the literal 999924351333383/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1163 : ∀ (p : 1163 < 1732), cc20Eq115CoefficientQ ⟨1163, p⟩ = (999924351333383 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1164 of the coefficient chain is the literal 4999621753855991/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1164 : ∀ (p : 1164 < 1732), cc20Eq115CoefficientQ ⟨1164, p⟩ = (4999621753855991 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1165 of the coefficient chain is the literal 4999621751053997/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1165 : ∀ (p : 1165 < 1732), cc20Eq115CoefficientQ ⟨1165, p⟩ = (4999621751053997 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1166 of the coefficient chain is the literal 4999621748261163/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1166 : ∀ (p : 1166 < 1732), cc20Eq115CoefficientQ ⟨1166, p⟩ = (4999621748261163 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1167 of the coefficient chain is the literal 9999243490951657/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1167 : ∀ (p : 1167 < 1732), cc20Eq115CoefficientQ ⟨1167, p⟩ = (9999243490951657 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1168 of the coefficient chain is the literal 9999243485399483/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1168 : ∀ (p : 1168 < 1732), cc20Eq115CoefficientQ ⟨1168, p⟩ = (9999243485399483 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1169 of the coefficient chain is the literal 2499810869966303/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1169 : ∀ (p : 1169 < 1732), cc20Eq115CoefficientQ ⟨1169, p⟩ = (2499810869966303 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1170 of the coefficient chain is the literal 4999621737174601/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1170 : ∀ (p : 1170 < 1732), cc20Eq115CoefficientQ ⟨1170, p⟩ = (4999621737174601 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1171 of the coefficient chain is the literal 9999243468849407/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1171 : ∀ (p : 1171 < 1732), cc20Eq115CoefficientQ ⟨1171, p⟩ = (9999243468849407 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1172 of the coefficient chain is the literal 9999243463366473/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1172 : ∀ (p : 1172 < 1732), cc20Eq115CoefficientQ ⟨1172, p⟩ = (9999243463366473 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1173 of the coefficient chain is the literal 399969738315977/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1173 : ∀ (p : 1173 < 1732), cc20Eq115CoefficientQ ⟨1173, p⟩ = (399969738315977 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1174 of the coefficient chain is the literal 2499810863113253/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1174 : ∀ (p : 1174 < 1732), cc20Eq115CoefficientQ ⟨1174, p⟩ = (2499810863113253 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1175 of the coefficient chain is the literal 1999848689404459/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1175 : ∀ (p : 1175 < 1732), cc20Eq115CoefficientQ ⟨1175, p⟩ = (1999848689404459 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1176 of the coefficient chain is the literal 9999243441609751/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1176 : ∀ (p : 1176 < 1732), cc20Eq115CoefficientQ ⟨1176, p⟩ = (9999243441609751 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1177 of the coefficient chain is the literal 2499810859053101/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1177 : ∀ (p : 1177 < 1732), cc20Eq115CoefficientQ ⟨1177, p⟩ = (2499810859053101 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1178 of the coefficient chain is the literal 1999848686166407/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1178 : ∀ (p : 1178 < 1732), cc20Eq115CoefficientQ ⟨1178, p⟩ = (1999848686166407 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1179 of the coefficient chain is the literal 499962171273487/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1179 : ∀ (p : 1179 < 1732), cc20Eq115CoefficientQ ⟨1179, p⟩ = (499962171273487 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1180 of the coefficient chain is the literal 4999621710061199/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1180 : ∀ (p : 1180 < 1732), cc20Eq115CoefficientQ ⟨1180, p⟩ = (4999621710061199 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1181 of the coefficient chain is the literal 9999243414793287/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1181 : ∀ (p : 1181 < 1732), cc20Eq115CoefficientQ ⟨1181, p⟩ = (9999243414793287 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1182 of the coefficient chain is the literal 1999848681896359/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1182 : ∀ (p : 1182 < 1732), cc20Eq115CoefficientQ ⟨1182, p⟩ = (1999848681896359 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1183 of the coefficient chain is the literal 1999848680837077/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1183 : ∀ (p : 1183 < 1732), cc20Eq115CoefficientQ ⟨1183, p⟩ = (1999848680837077 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1184 of the coefficient chain is the literal 4999621699452679/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1184 : ∀ (p : 1184 < 1732), cc20Eq115CoefficientQ ⟨1184, p⟩ = (4999621699452679 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1185 of the coefficient chain is the literal 78119089012837/ 78125000000000. -/
theorem cc20Eq115CoefficientQ_branch_1185 : ∀ (p : 1185 < 1732), cc20Eq115CoefficientQ ⟨1185, p⟩ = (78119089012837 : ℚ) /  78125000000000 :=
  fun p => by rfl

/-- Branch 1186 of the coefficient chain is the literal 9999243388397353/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1186 : ∀ (p : 1186 < 1732), cc20Eq115CoefficientQ ⟨1186, p⟩ = (9999243388397353 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1187 of the coefficient chain is the literal 9999243383167349/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1187 : ∀ (p : 1187 < 1732), cc20Eq115CoefficientQ ⟨1187, p⟩ = (9999243383167349 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1188 of the coefficient chain is the literal 9999243377955279/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1188 : ∀ (p : 1188 < 1732), cc20Eq115CoefficientQ ⟨1188, p⟩ = (9999243377955279 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1189 of the coefficient chain is the literal 1999848674551753/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1189 : ∀ (p : 1189 < 1732), cc20Eq115CoefficientQ ⟨1189, p⟩ = (1999848674551753 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1190 of the coefficient chain is the literal 4999621683789253/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1190 : ∀ (p : 1190 < 1732), cc20Eq115CoefficientQ ⟨1190, p⟩ = (4999621683789253 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1191 of the coefficient chain is the literal 1249905420302937/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1191 : ∀ (p : 1191 < 1732), cc20Eq115CoefficientQ ⟨1191, p⟩ = (1249905420302937 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1192 of the coefficient chain is the literal 1999848671451501/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1192 : ∀ (p : 1192 < 1732), cc20Eq115CoefficientQ ⟨1192, p⟩ = (1999848671451501 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1193 of the coefficient chain is the literal 9999243352129743/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1193 : ∀ (p : 1193 < 1732), cc20Eq115CoefficientQ ⟨1193, p⟩ = (9999243352129743 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1194 of the coefficient chain is the literal 9999243347015517/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1194 : ∀ (p : 1194 < 1732), cc20Eq115CoefficientQ ⟨1194, p⟩ = (9999243347015517 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1195 of the coefficient chain is the literal 156238177217451/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_1195 : ∀ (p : 1195 < 1732), cc20Eq115CoefficientQ ⟨1195, p⟩ = (156238177217451 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 1196 of the coefficient chain is the literal 9999243336833737/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1196 : ∀ (p : 1196 < 1732), cc20Eq115CoefficientQ ⟨1196, p⟩ = (9999243336833737 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1197 of the coefficient chain is the literal 2499810832941661/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1197 : ∀ (p : 1197 < 1732), cc20Eq115CoefficientQ ⟨1197, p⟩ = (2499810832941661 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1198 of the coefficient chain is the literal 9764886061243/ 9765625000000. -/
theorem cc20Eq115CoefficientQ_branch_1198 : ∀ (p : 1198 < 1732), cc20Eq115CoefficientQ ⟨1198, p⟩ = (9764886061243 : ℚ) /  9765625000000 :=
  fun p => by rfl

/-- Branch 1199 of the coefficient chain is the literal 1999848664335471/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1199 : ∀ (p : 1199 < 1732), cc20Eq115CoefficientQ ⟨1199, p⟩ = (1999848664335471 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1200 of the coefficient chain is the literal 4999621658330613/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1200 : ∀ (p : 1200 < 1732), cc20Eq115CoefficientQ ⟨1200, p⟩ = (4999621658330613 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1201 of the coefficient chain is the literal 1249905413957061/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1201 : ∀ (p : 1201 < 1732), cc20Eq115CoefficientQ ⟨1201, p⟩ = (1249905413957061 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1202 of the coefficient chain is the literal 9999243306666811/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1202 : ∀ (p : 1202 < 1732), cc20Eq115CoefficientQ ⟨1202, p⟩ = (9999243306666811 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1203 of the coefficient chain is the literal 99992433016949/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1203 : ∀ (p : 1203 < 1732), cc20Eq115CoefficientQ ⟨1203, p⟩ = (99992433016949 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 1204 of the coefficient chain is the literal 4999621648367917/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1204 : ∀ (p : 1204 < 1732), cc20Eq115CoefficientQ ⟨1204, p⟩ = (4999621648367917 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1205 of the coefficient chain is the literal 79993946334371/ 80000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1205 : ∀ (p : 1205 < 1732), cc20Eq115CoefficientQ ⟨1205, p⟩ = (79993946334371 : ℚ) /  80000000000000 :=
  fun p => by rfl

/-- Branch 1206 of the coefficient chain is the literal 1249905410858907/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1206 : ∀ (p : 1206 < 1732), cc20Eq115CoefficientQ ⟨1206, p⟩ = (1249905410858907 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1207 of the coefficient chain is the literal 4999621640980671/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1207 : ∀ (p : 1207 < 1732), cc20Eq115CoefficientQ ⟨1207, p⟩ = (4999621640980671 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1208 of the coefficient chain is the literal 9999243277065997/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1208 : ∀ (p : 1208 < 1732), cc20Eq115CoefficientQ ⟨1208, p⟩ = (9999243277065997 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1209 of the coefficient chain is the literal 1249905409023303/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1209 : ∀ (p : 1209 < 1732), cc20Eq115CoefficientQ ⟨1209, p⟩ = (1249905409023303 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1210 of the coefficient chain is the literal 2499810816830483/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1210 : ∀ (p : 1210 < 1732), cc20Eq115CoefficientQ ⟨1210, p⟩ = (2499810816830483 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1211 of the coefficient chain is the literal 9999243262475457/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1211 : ∀ (p : 1211 < 1732), cc20Eq115CoefficientQ ⟨1211, p⟩ = (9999243262475457 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1212 of the coefficient chain is the literal 4999621628820249/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1212 : ∀ (p : 1212 < 1732), cc20Eq115CoefficientQ ⟨1212, p⟩ = (4999621628820249 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1213 of the coefficient chain is the literal 9999243252823143/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1213 : ∀ (p : 1213 < 1732), cc20Eq115CoefficientQ ⟨1213, p⟩ = (9999243252823143 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1214 of the coefficient chain is the literal 9999243248020923/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1214 : ∀ (p : 1214 < 1732), cc20Eq115CoefficientQ ⟨1214, p⟩ = (9999243248020923 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1215 of the coefficient chain is the literal 249981081080819/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1215 : ∀ (p : 1215 < 1732), cc20Eq115CoefficientQ ⟨1215, p⟩ = (249981081080819 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 1216 of the coefficient chain is the literal 99992432384613/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1216 : ∀ (p : 1216 < 1732), cc20Eq115CoefficientQ ⟨1216, p⟩ = (99992432384613 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 1217 of the coefficient chain is the literal 9999243233704967/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1217 : ∀ (p : 1217 < 1732), cc20Eq115CoefficientQ ⟨1217, p⟩ = (9999243233704967 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1218 of the coefficient chain is the literal 999924322896289/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1218 : ∀ (p : 1218 < 1732), cc20Eq115CoefficientQ ⟨1218, p⟩ = (999924322896289 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1219 of the coefficient chain is the literal 2499810806058729/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1219 : ∀ (p : 1219 < 1732), cc20Eq115CoefficientQ ⟨1219, p⟩ = (2499810806058729 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1220 of the coefficient chain is the literal 9999243219523961/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1220 : ∀ (p : 1220 < 1732), cc20Eq115CoefficientQ ⟨1220, p⟩ = (9999243219523961 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1221 of the coefficient chain is the literal 9999243214824957/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1221 : ∀ (p : 1221 < 1732), cc20Eq115CoefficientQ ⟨1221, p⟩ = (9999243214824957 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1222 of the coefficient chain is the literal 249981080253551/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1222 : ∀ (p : 1222 < 1732), cc20Eq115CoefficientQ ⟨1222, p⟩ = (249981080253551 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 1223 of the coefficient chain is the literal 9999243205476813/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1223 : ∀ (p : 1223 < 1732), cc20Eq115CoefficientQ ⟨1223, p⟩ = (9999243205476813 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1224 of the coefficient chain is the literal 4999621600411943/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1224 : ∀ (p : 1224 < 1732), cc20Eq115CoefficientQ ⟨1224, p⟩ = (4999621600411943 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1225 of the coefficient chain is the literal 2499810799045809/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1225 : ∀ (p : 1225 < 1732), cc20Eq115CoefficientQ ⟨1225, p⟩ = (2499810799045809 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1226 of the coefficient chain is the literal 9999243191559881/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1226 : ∀ (p : 1226 < 1732), cc20Eq115CoefficientQ ⟨1226, p⟩ = (9999243191559881 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1227 of the coefficient chain is the literal 9999243186951351/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1227 : ∀ (p : 1227 < 1732), cc20Eq115CoefficientQ ⟨1227, p⟩ = (9999243186951351 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1228 of the coefficient chain is the literal 9999243182350739/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1228 : ∀ (p : 1228 < 1732), cc20Eq115CoefficientQ ⟨1228, p⟩ = (9999243182350739 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1229 of the coefficient chain is the literal 999924317777703/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1229 : ∀ (p : 1229 < 1732), cc20Eq115CoefficientQ ⟨1229, p⟩ = (999924317777703 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1230 of the coefficient chain is the literal 4999621586608091/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1230 : ∀ (p : 1230 < 1732), cc20Eq115CoefficientQ ⟨1230, p⟩ = (4999621586608091 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1231 of the coefficient chain is the literal 1999848633733021/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1231 : ∀ (p : 1231 < 1732), cc20Eq115CoefficientQ ⟨1231, p⟩ = (1999848633733021 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1232 of the coefficient chain is the literal 9999243164129317/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1232 : ∀ (p : 1232 < 1732), cc20Eq115CoefficientQ ⟨1232, p⟩ = (9999243164129317 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1233 of the coefficient chain is the literal 9999243159624787/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1233 : ∀ (p : 1233 < 1732), cc20Eq115CoefficientQ ⟨1233, p⟩ = (9999243159624787 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1234 of the coefficient chain is the literal 4999621577550047/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1234 : ∀ (p : 1234 < 1732), cc20Eq115CoefficientQ ⟨1234, p⟩ = (4999621577550047 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1235 of the coefficient chain is the literal 4999621575302053/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1235 : ∀ (p : 1235 < 1732), cc20Eq115CoefficientQ ⟨1235, p⟩ = (4999621575302053 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1236 of the coefficient chain is the literal 1999848629220693/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1236 : ∀ (p : 1236 < 1732), cc20Eq115CoefficientQ ⟨1236, p⟩ = (1999848629220693 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1237 of the coefficient chain is the literal 4999621570827991/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1237 : ∀ (p : 1237 < 1732), cc20Eq115CoefficientQ ⟨1237, p⟩ = (4999621570827991 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1238 of the coefficient chain is the literal 9999243137199743/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1238 : ∀ (p : 1238 < 1732), cc20Eq115CoefficientQ ⟨1238, p⟩ = (9999243137199743 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1239 of the coefficient chain is the literal 9999243132782221/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1239 : ∀ (p : 1239 < 1732), cc20Eq115CoefficientQ ⟨1239, p⟩ = (9999243132782221 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1240 of the coefficient chain is the literal 2499810782092233/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1240 : ∀ (p : 1240 < 1732), cc20Eq115CoefficientQ ⟨1240, p⟩ = (2499810782092233 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1241 of the coefficient chain is the literal 1999848624791471/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1241 : ∀ (p : 1241 < 1732), cc20Eq115CoefficientQ ⟨1241, p⟩ = (1999848624791471 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1242 of the coefficient chain is the literal 9999243119561531/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1242 : ∀ (p : 1242 < 1732), cc20Eq115CoefficientQ ⟨1242, p⟩ = (9999243119561531 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1243 of the coefficient chain is the literal 9999243115180749/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1243 : ∀ (p : 1243 < 1732), cc20Eq115CoefficientQ ⟨1243, p⟩ = (9999243115180749 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1244 of the coefficient chain is the literal 2499810777704023/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1244 : ∀ (p : 1244 < 1732), cc20Eq115CoefficientQ ⟨1244, p⟩ = (2499810777704023 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1245 of the coefficient chain is the literal 4999621553232077/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1245 : ∀ (p : 1245 < 1732), cc20Eq115CoefficientQ ⟨1245, p⟩ = (4999621553232077 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1246 of the coefficient chain is the literal 2499810775531221/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1246 : ∀ (p : 1246 < 1732), cc20Eq115CoefficientQ ⟨1246, p⟩ = (2499810775531221 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1247 of the coefficient chain is the literal 9999243097803131/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1247 : ∀ (p : 1247 < 1732), cc20Eq115CoefficientQ ⟨1247, p⟩ = (9999243097803131 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1248 of the coefficient chain is the literal 624952693343451/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1248 : ∀ (p : 1248 < 1732), cc20Eq115CoefficientQ ⟨1248, p⟩ = (624952693343451 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1249 of the coefficient chain is the literal 9999243089197297/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1249 : ∀ (p : 1249 < 1732), cc20Eq115CoefficientQ ⟨1249, p⟩ = (9999243089197297 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1250 of the coefficient chain is the literal 9999243084912723/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1250 : ∀ (p : 1250 < 1732), cc20Eq115CoefficientQ ⟨1250, p⟩ = (9999243084912723 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1251 of the coefficient chain is the literal 1999848616128961/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1251 : ∀ (p : 1251 < 1732), cc20Eq115CoefficientQ ⟨1251, p⟩ = (1999848616128961 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1252 of the coefficient chain is the literal 9999243076390121/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1252 : ∀ (p : 1252 < 1732), cc20Eq115CoefficientQ ⟨1252, p⟩ = (9999243076390121 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1253 of the coefficient chain is the literal 1249905384018577/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1253 : ∀ (p : 1253 < 1732), cc20Eq115CoefficientQ ⟨1253, p⟩ = (1249905384018577 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1254 of the coefficient chain is the literal 624952691745097/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1254 : ∀ (p : 1254 < 1732), cc20Eq115CoefficientQ ⟨1254, p⟩ = (624952691745097 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1255 of the coefficient chain is the literal 9999243063689377/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1255 : ∀ (p : 1255 < 1732), cc20Eq115CoefficientQ ⟨1255, p⟩ = (9999243063689377 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1256 of the coefficient chain is the literal 9999243059510041/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1256 : ∀ (p : 1256 < 1732), cc20Eq115CoefficientQ ⟨1256, p⟩ = (9999243059510041 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1257 of the coefficient chain is the literal 1249905381915227/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1257 : ∀ (p : 1257 < 1732), cc20Eq115CoefficientQ ⟨1257, p⟩ = (1249905381915227 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1258 of the coefficient chain is the literal 2499810762785423/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1258 : ∀ (p : 1258 < 1732), cc20Eq115CoefficientQ ⟨1258, p⟩ = (2499810762785423 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1259 of the coefficient chain is the literal 4999621523488041/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1259 : ∀ (p : 1259 < 1732), cc20Eq115CoefficientQ ⟨1259, p⟩ = (4999621523488041 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1260 of the coefficient chain is the literal 2499810760712407/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1260 : ∀ (p : 1260 < 1732), cc20Eq115CoefficientQ ⟨1260, p⟩ = (2499810760712407 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1261 of the coefficient chain is the literal 2499810759677703/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1261 : ∀ (p : 1261 < 1732), cc20Eq115CoefficientQ ⟨1261, p⟩ = (2499810759677703 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1262 of the coefficient chain is the literal 9999243034588139/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1262 : ∀ (p : 1262 < 1732), cc20Eq115CoefficientQ ⟨1262, p⟩ = (9999243034588139 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1263 of the coefficient chain is the literal 624952689405173/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1263 : ∀ (p : 1263 < 1732), cc20Eq115CoefficientQ ⟨1263, p⟩ = (624952689405173 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1264 of the coefficient chain is the literal 9999243026387009/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1264 : ∀ (p : 1264 < 1732), cc20Eq115CoefficientQ ⟨1264, p⟩ = (9999243026387009 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1265 of the coefficient chain is the literal 2499810755576451/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1265 : ∀ (p : 1265 < 1732), cc20Eq115CoefficientQ ⟨1265, p⟩ = (2499810755576451 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1266 of the coefficient chain is the literal 9999243018240253/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1266 : ∀ (p : 1266 < 1732), cc20Eq115CoefficientQ ⟨1266, p⟩ = (9999243018240253 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1267 of the coefficient chain is the literal 9999243014186037/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1267 : ∀ (p : 1267 < 1732), cc20Eq115CoefficientQ ⟨1267, p⟩ = (9999243014186037 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1268 of the coefficient chain is the literal 2499810752536549/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1268 : ∀ (p : 1268 < 1732), cc20Eq115CoefficientQ ⟨1268, p⟩ = (2499810752536549 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1269 of the coefficient chain is the literal 9999243006118093/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1269 : ∀ (p : 1269 < 1732), cc20Eq115CoefficientQ ⟨1269, p⟩ = (9999243006118093 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1270 of the coefficient chain is the literal 9999243002103261/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1270 : ∀ (p : 1270 < 1732), cc20Eq115CoefficientQ ⟨1270, p⟩ = (9999243002103261 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1271 of the coefficient chain is the literal 1249905374762781/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1271 : ∀ (p : 1271 < 1732), cc20Eq115CoefficientQ ⟨1271, p⟩ = (1249905374762781 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1272 of the coefficient chain is the literal 199984859882189/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1272 : ∀ (p : 1272 < 1732), cc20Eq115CoefficientQ ⟨1272, p⟩ = (199984859882189 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 1273 of the coefficient chain is the literal 2499810747533597/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1273 : ∀ (p : 1273 < 1732), cc20Eq115CoefficientQ ⟨1273, p⟩ = (2499810747533597 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1274 of the coefficient chain is the literal 9999242986172047/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1274 : ∀ (p : 1274 < 1732), cc20Eq115CoefficientQ ⟨1274, p⟩ = (9999242986172047 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1275 of the coefficient chain is the literal 9999242982222217/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1275 : ∀ (p : 1275 < 1732), cc20Eq115CoefficientQ ⟨1275, p⟩ = (9999242982222217 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1276 of the coefficient chain is the literal 2499810744570751/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1276 : ∀ (p : 1276 < 1732), cc20Eq115CoefficientQ ⟨1276, p⟩ = (2499810744570751 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1277 of the coefficient chain is the literal 9999242974345397/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1277 : ∀ (p : 1277 < 1732), cc20Eq115CoefficientQ ⟨1277, p⟩ = (9999242974345397 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1278 of the coefficient chain is the literal 999924297045417/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1278 : ∀ (p : 1278 < 1732), cc20Eq115CoefficientQ ⟨1278, p⟩ = (999924297045417 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1279 of the coefficient chain is the literal 999924296655563/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1279 : ∀ (p : 1279 < 1732), cc20Eq115CoefficientQ ⟨1279, p⟩ = (999924296655563 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1280 of the coefficient chain is the literal 4999621481333763/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1280 : ∀ (p : 1280 < 1732), cc20Eq115CoefficientQ ⟨1280, p⟩ = (4999621481333763 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1281 of the coefficient chain is the literal 9999242958794851/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1281 : ∀ (p : 1281 < 1732), cc20Eq115CoefficientQ ⟨1281, p⟩ = (9999242958794851 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1282 of the coefficient chain is the literal 4999621477466499/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1282 : ∀ (p : 1282 < 1732), cc20Eq115CoefficientQ ⟨1282, p⟩ = (4999621477466499 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1283 of the coefficient chain is the literal 2499810737771663/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1283 : ∀ (p : 1283 < 1732), cc20Eq115CoefficientQ ⟨1283, p⟩ = (2499810737771663 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1284 of the coefficient chain is the literal 9999242947263127/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1284 : ∀ (p : 1284 < 1732), cc20Eq115CoefficientQ ⟨1284, p⟩ = (9999242947263127 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1285 of the coefficient chain is the literal 9999242943416703/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1285 : ∀ (p : 1285 < 1732), cc20Eq115CoefficientQ ⟨1285, p⟩ = (9999242943416703 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1286 of the coefficient chain is the literal 4999621469801267/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1286 : ∀ (p : 1286 < 1732), cc20Eq115CoefficientQ ⟨1286, p⟩ = (4999621469801267 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1287 of the coefficient chain is the literal 999924293579989/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1287 : ∀ (p : 1287 < 1732), cc20Eq115CoefficientQ ⟨1287, p⟩ = (999924293579989 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1288 of the coefficient chain is the literal 9999242932036333/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1288 : ∀ (p : 1288 < 1732), cc20Eq115CoefficientQ ⟨1288, p⟩ = (9999242932036333 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1289 of the coefficient chain is the literal 9999242928246059/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1289 : ∀ (p : 1289 < 1732), cc20Eq115CoefficientQ ⟨1289, p⟩ = (9999242928246059 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1290 of the coefficient chain is the literal 9999242924503949/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1290 : ∀ (p : 1290 < 1732), cc20Eq115CoefficientQ ⟨1290, p⟩ = (9999242924503949 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1291 of the coefficient chain is the literal 9999242920740493/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1291 : ∀ (p : 1291 < 1732), cc20Eq115CoefficientQ ⟨1291, p⟩ = (9999242920740493 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1292 of the coefficient chain is the literal 2499810729257761/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1292 : ∀ (p : 1292 < 1732), cc20Eq115CoefficientQ ⟨1292, p⟩ = (2499810729257761 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1293 of the coefficient chain is the literal 2499810728324787/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1293 : ∀ (p : 1293 < 1732), cc20Eq115CoefficientQ ⟨1293, p⟩ = (2499810728324787 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1294 of the coefficient chain is the literal 9999242909583027/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1294 : ∀ (p : 1294 < 1732), cc20Eq115CoefficientQ ⟨1294, p⟩ = (9999242909583027 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1295 of the coefficient chain is the literal 156238170404561/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_1295 : ∀ (p : 1295 < 1732), cc20Eq115CoefficientQ ⟨1295, p⟩ = (156238170404561 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 1296 of the coefficient chain is the literal 2499810725550023/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1296 : ∀ (p : 1296 < 1732), cc20Eq115CoefficientQ ⟨1296, p⟩ = (2499810725550023 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1297 of the coefficient chain is the literal 312476340578879/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1297 : ∀ (p : 1297 < 1732), cc20Eq115CoefficientQ ⟨1297, p⟩ = (312476340578879 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 1298 of the coefficient chain is the literal 1999848578972349/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1298 : ∀ (p : 1298 < 1732), cc20Eq115CoefficientQ ⟨1298, p⟩ = (1999848578972349 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1299 of the coefficient chain is the literal 2499810722802883/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1299 : ∀ (p : 1299 < 1732), cc20Eq115CoefficientQ ⟨1299, p⟩ = (2499810722802883 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1300 of the coefficient chain is the literal 9999242887572299/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1300 : ∀ (p : 1300 < 1732), cc20Eq115CoefficientQ ⟨1300, p⟩ = (9999242887572299 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1301 of the coefficient chain is the literal 1999848576789011/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1301 : ∀ (p : 1301 < 1732), cc20Eq115CoefficientQ ⟨1301, p⟩ = (1999848576789011 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1302 of the coefficient chain is the literal 9999242880331071/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1302 : ∀ (p : 1302 < 1732), cc20Eq115CoefficientQ ⟨1302, p⟩ = (9999242880331071 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1303 of the coefficient chain is the literal 9999242876728297/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1303 : ∀ (p : 1303 < 1732), cc20Eq115CoefficientQ ⟨1303, p⟩ = (9999242876728297 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1304 of the coefficient chain is the literal 4999621436569429/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1304 : ∀ (p : 1304 < 1732), cc20Eq115CoefficientQ ⟨1304, p⟩ = (4999621436569429 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1305 of the coefficient chain is the literal 1999848573912193/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1305 : ∀ (p : 1305 < 1732), cc20Eq115CoefficientQ ⟨1305, p⟩ = (1999848573912193 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1306 of the coefficient chain is the literal 9999242865993683/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1306 : ∀ (p : 1306 < 1732), cc20Eq115CoefficientQ ⟨1306, p⟩ = (9999242865993683 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1307 of the coefficient chain is the literal 4999621431219091/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1307 : ∀ (p : 1307 < 1732), cc20Eq115CoefficientQ ⟨1307, p⟩ = (4999621431219091 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1308 of the coefficient chain is the literal 4999621429447479/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1308 : ∀ (p : 1308 < 1732), cc20Eq115CoefficientQ ⟨1308, p⟩ = (4999621429447479 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1309 of the coefficient chain is the literal 9999242855361781/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1309 : ∀ (p : 1309 < 1732), cc20Eq115CoefficientQ ⟨1309, p⟩ = (9999242855361781 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1310 of the coefficient chain is the literal 9999242851838329/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1310 : ∀ (p : 1310 < 1732), cc20Eq115CoefficientQ ⟨1310, p⟩ = (9999242851838329 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1311 of the coefficient chain is the literal 4999621424168023/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1311 : ∀ (p : 1311 < 1732), cc20Eq115CoefficientQ ⟨1311, p⟩ = (4999621424168023 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1312 of the coefficient chain is the literal 9999242844840763/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1312 : ∀ (p : 1312 < 1732), cc20Eq115CoefficientQ ⟨1312, p⟩ = (9999242844840763 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1313 of the coefficient chain is the literal 9999242841356997/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1313 : ∀ (p : 1313 < 1732), cc20Eq115CoefficientQ ⟨1313, p⟩ = (9999242841356997 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1314 of the coefficient chain is the literal 4999621418941799/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1314 : ∀ (p : 1314 < 1732), cc20Eq115CoefficientQ ⟨1314, p⟩ = (4999621418941799 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1315 of the coefficient chain is the literal 9999242834424853/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1315 : ∀ (p : 1315 < 1732), cc20Eq115CoefficientQ ⟨1315, p⟩ = (9999242834424853 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1316 of the coefficient chain is the literal 1249905353872079/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1316 : ∀ (p : 1316 < 1732), cc20Eq115CoefficientQ ⟨1316, p⟩ = (1249905353872079 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1317 of the coefficient chain is the literal 2499810706885769/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1317 : ∀ (p : 1317 < 1732), cc20Eq115CoefficientQ ⟨1317, p⟩ = (2499810706885769 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1318 of the coefficient chain is the literal 9999242824111837/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1318 : ∀ (p : 1318 < 1732), cc20Eq115CoefficientQ ⟨1318, p⟩ = (9999242824111837 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1319 of the coefficient chain is the literal 9999242820697073/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1319 : ∀ (p : 1319 < 1732), cc20Eq115CoefficientQ ⟨1319, p⟩ = (9999242820697073 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1320 of the coefficient chain is the literal 9999242817294431/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1320 : ∀ (p : 1320 < 1732), cc20Eq115CoefficientQ ⟨1320, p⟩ = (9999242817294431 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1321 of the coefficient chain is the literal 399969712556123/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1321 : ∀ (p : 1321 < 1732), cc20Eq115CoefficientQ ⟨1321, p⟩ = (399969712556123 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1322 of the coefficient chain is the literal 9999242810522483/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1322 : ∀ (p : 1322 < 1732), cc20Eq115CoefficientQ ⟨1322, p⟩ = (9999242810522483 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1323 of the coefficient chain is the literal 1249905350894077/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1323 : ∀ (p : 1323 < 1732), cc20Eq115CoefficientQ ⟨1323, p⟩ = (1249905350894077 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1324 of the coefficient chain is the literal 1249905350474167/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1324 : ∀ (p : 1324 < 1732), cc20Eq115CoefficientQ ⟨1324, p⟩ = (1249905350474167 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1325 of the coefficient chain is the literal 4999621400225911/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1325 : ∀ (p : 1325 < 1732), cc20Eq115CoefficientQ ⟨1325, p⟩ = (4999621400225911 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1326 of the coefficient chain is the literal 9999242797116161/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1326 : ∀ (p : 1326 < 1732), cc20Eq115CoefficientQ ⟨1326, p⟩ = (9999242797116161 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1327 of the coefficient chain is the literal 399969711751721/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1327 : ∀ (p : 1327 < 1732), cc20Eq115CoefficientQ ⟨1327, p⟩ = (399969711751721 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1328 of the coefficient chain is the literal 624952674405091/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1328 : ∀ (p : 1328 < 1732), cc20Eq115CoefficientQ ⟨1328, p⟩ = (624952674405091 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1329 of the coefficient chain is the literal 4999621393590273/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1329 : ∀ (p : 1329 < 1732), cc20Eq115CoefficientQ ⟨1329, p⟩ = (4999621393590273 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1330 of the coefficient chain is the literal 9999242783891947/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1330 : ∀ (p : 1330 < 1732), cc20Eq115CoefficientQ ⟨1330, p⟩ = (9999242783891947 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1331 of the coefficient chain is the literal 999924278061209/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1331 : ∀ (p : 1331 < 1732), cc20Eq115CoefficientQ ⟨1331, p⟩ = (999924278061209 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1332 of the coefficient chain is the literal 9999242777344679/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1332 : ∀ (p : 1332 < 1732), cc20Eq115CoefficientQ ⟨1332, p⟩ = (9999242777344679 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1333 of the coefficient chain is the literal 624952673380573/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1333 : ∀ (p : 1333 < 1732), cc20Eq115CoefficientQ ⟨1333, p⟩ = (624952673380573 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1334 of the coefficient chain is the literal 1999848554168111/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1334 : ∀ (p : 1334 < 1732), cc20Eq115CoefficientQ ⟨1334, p⟩ = (1999848554168111 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1335 of the coefficient chain is the literal 624952672975829/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1335 : ∀ (p : 1335 < 1732), cc20Eq115CoefficientQ ⟨1335, p⟩ = (624952672975829 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1336 of the coefficient chain is the literal 9999242764400053/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1336 : ∀ (p : 1336 < 1732), cc20Eq115CoefficientQ ⟨1336, p⟩ = (9999242764400053 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1337 of the coefficient chain is the literal 4999621380590781/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1337 : ∀ (p : 1337 < 1732), cc20Eq115CoefficientQ ⟨1337, p⟩ = (4999621380590781 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1338 of the coefficient chain is the literal 4999621378990283/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1338 : ∀ (p : 1338 < 1732), cc20Eq115CoefficientQ ⟨1338, p⟩ = (4999621378990283 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1339 of the coefficient chain is the literal 2499810688697241/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1339 : ∀ (p : 1339 < 1732), cc20Eq115CoefficientQ ⟨1339, p⟩ = (2499810688697241 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1340 of the coefficient chain is the literal 9999242751610699/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1340 : ∀ (p : 1340 < 1732), cc20Eq115CoefficientQ ⟨1340, p⟩ = (9999242751610699 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1341 of the coefficient chain is the literal 2499810687110681/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1341 : ∀ (p : 1341 < 1732), cc20Eq115CoefficientQ ⟨1341, p⟩ = (2499810687110681 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1342 of the coefficient chain is the literal 4999621372646457/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1342 : ∀ (p : 1342 < 1732), cc20Eq115CoefficientQ ⟨1342, p⟩ = (4999621372646457 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1343 of the coefficient chain is the literal 4999621371072039/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1343 : ∀ (p : 1343 < 1732), cc20Eq115CoefficientQ ⟨1343, p⟩ = (4999621371072039 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1344 of the coefficient chain is the literal 4999621369503373/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1344 : ∀ (p : 1344 < 1732), cc20Eq115CoefficientQ ⟨1344, p⟩ = (4999621369503373 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1345 of the coefficient chain is the literal 1249905341985563/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1345 : ∀ (p : 1345 < 1732), cc20Eq115CoefficientQ ⟨1345, p⟩ = (1249905341985563 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1346 of the coefficient chain is the literal 9999242732772369/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1346 : ∀ (p : 1346 < 1732), cc20Eq115CoefficientQ ⟨1346, p⟩ = (9999242732772369 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1347 of the coefficient chain is the literal 9999242729668251/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1347 : ∀ (p : 1347 < 1732), cc20Eq115CoefficientQ ⟨1347, p⟩ = (9999242729668251 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1348 of the coefficient chain is the literal 9999242726576691/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1348 : ∀ (p : 1348 < 1732), cc20Eq115CoefficientQ ⟨1348, p⟩ = (9999242726576691 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1349 of the coefficient chain is the literal 9999242723494579/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1349 : ∀ (p : 1349 < 1732), cc20Eq115CoefficientQ ⟨1349, p⟩ = (9999242723494579 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1350 of the coefficient chain is the literal 9999242720424777/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1350 : ∀ (p : 1350 < 1732), cc20Eq115CoefficientQ ⟨1350, p⟩ = (9999242720424777 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1351 of the coefficient chain is the literal 9999242717364747/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1351 : ∀ (p : 1351 < 1732), cc20Eq115CoefficientQ ⟨1351, p⟩ = (9999242717364747 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1352 of the coefficient chain is the literal 1999848542862767/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1352 : ∀ (p : 1352 < 1732), cc20Eq115CoefficientQ ⟨1352, p⟩ = (1999848542862767 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1353 of the coefficient chain is the literal 4999621355639649/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1353 : ∀ (p : 1353 < 1732), cc20Eq115CoefficientQ ⟨1353, p⟩ = (4999621355639649 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1354 of the coefficient chain is the literal 9999242708248731/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1354 : ∀ (p : 1354 < 1732), cc20Eq115CoefficientQ ⟨1354, p⟩ = (9999242708248731 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1355 of the coefficient chain is the literal 1999848541047017/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1355 : ∀ (p : 1355 < 1732), cc20Eq115CoefficientQ ⟨1355, p⟩ = (1999848541047017 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1356 of the coefficient chain is the literal 2499810675557059/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1356 : ∀ (p : 1356 < 1732), cc20Eq115CoefficientQ ⟨1356, p⟩ = (2499810675557059 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1357 of the coefficient chain is the literal 4999621349614893/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1357 : ∀ (p : 1357 < 1732), cc20Eq115CoefficientQ ⟨1357, p⟩ = (4999621349614893 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1358 of the coefficient chain is the literal 9999242696248939/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1358 : ∀ (p : 1358 < 1732), cc20Eq115CoefficientQ ⟨1358, p⟩ = (9999242696248939 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1359 of the coefficient chain is the literal 1249905336659083/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1359 : ∀ (p : 1359 < 1732), cc20Eq115CoefficientQ ⟨1359, p⟩ = (1249905336659083 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1360 of the coefficient chain is the literal 624952668144247/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1360 : ∀ (p : 1360 < 1732), cc20Eq115CoefficientQ ⟨1360, p⟩ = (624952668144247 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1361 of the coefficient chain is the literal 9999242687352643/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1361 : ∀ (p : 1361 < 1732), cc20Eq115CoefficientQ ⟨1361, p⟩ = (9999242687352643 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1362 of the coefficient chain is the literal 9999242684408567/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1362 : ∀ (p : 1362 < 1732), cc20Eq115CoefficientQ ⟨1362, p⟩ = (9999242684408567 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1363 of the coefficient chain is the literal 9999242681484479/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1363 : ∀ (p : 1363 < 1732), cc20Eq115CoefficientQ ⟨1363, p⟩ = (9999242681484479 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1364 of the coefficient chain is the literal 499962133928141/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1364 : ∀ (p : 1364 < 1732), cc20Eq115CoefficientQ ⟨1364, p⟩ = (499962133928141 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1365 of the coefficient chain is the literal 9999242675643903/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1365 : ∀ (p : 1365 < 1732), cc20Eq115CoefficientQ ⟨1365, p⟩ = (9999242675643903 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1366 of the coefficient chain is the literal 1249905334092427/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1366 : ∀ (p : 1366 < 1732), cc20Eq115CoefficientQ ⟨1366, p⟩ = (1249905334092427 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1367 of the coefficient chain is the literal 2499810667459661/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1367 : ∀ (p : 1367 < 1732), cc20Eq115CoefficientQ ⟨1367, p⟩ = (2499810667459661 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1368 of the coefficient chain is the literal 1999848533396337/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1368 : ∀ (p : 1368 < 1732), cc20Eq115CoefficientQ ⟨1368, p⟩ = (1999848533396337 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1369 of the coefficient chain is the literal 4999621332053199/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1369 : ∀ (p : 1369 < 1732), cc20Eq115CoefficientQ ⟨1369, p⟩ = (4999621332053199 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1370 of the coefficient chain is the literal 2499810665311237/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1370 : ∀ (p : 1370 < 1732), cc20Eq115CoefficientQ ⟨1370, p⟩ = (2499810665311237 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1371 of the coefficient chain is the literal 9999242658394951/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1371 : ∀ (p : 1371 < 1732), cc20Eq115CoefficientQ ⟨1371, p⟩ = (9999242658394951 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1372 of the coefficient chain is the literal 9999242655552133/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1372 : ∀ (p : 1372 < 1732), cc20Eq115CoefficientQ ⟨1372, p⟩ = (9999242655552133 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1373 of the coefficient chain is the literal 1999848530545099/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1373 : ∀ (p : 1373 < 1732), cc20Eq115CoefficientQ ⟨1373, p⟩ = (1999848530545099 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1374 of the coefficient chain is the literal 1249905331237557/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1374 : ∀ (p : 1374 < 1732), cc20Eq115CoefficientQ ⟨1374, p⟩ = (1249905331237557 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1375 of the coefficient chain is the literal 4999621323550097/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1375 : ∀ (p : 1375 < 1732), cc20Eq115CoefficientQ ⟨1375, p⟩ = (4999621323550097 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1376 of the coefficient chain is the literal 4999621322149893/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1376 : ∀ (p : 1376 < 1732), cc20Eq115CoefficientQ ⟨1376, p⟩ = (4999621322149893 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1377 of the coefficient chain is the literal 2499810660377161/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1377 : ∀ (p : 1377 < 1732), cc20Eq115CoefficientQ ⟨1377, p⟩ = (2499810660377161 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1378 of the coefficient chain is the literal 2499810659682463/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1378 : ∀ (p : 1378 < 1732), cc20Eq115CoefficientQ ⟨1378, p⟩ = (2499810659682463 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1379 of the coefficient chain is the literal 4999621317980751/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1379 : ∀ (p : 1379 < 1732), cc20Eq115CoefficientQ ⟨1379, p⟩ = (4999621317980751 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1380 of the coefficient chain is the literal 9999242633204497/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1380 : ∀ (p : 1380 < 1732), cc20Eq115CoefficientQ ⟨1380, p⟩ = (9999242633204497 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1381 of the coefficient chain is the literal 9999242630451831/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1381 : ∀ (p : 1381 < 1732), cc20Eq115CoefficientQ ⟨1381, p⟩ = (9999242630451831 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1382 of the coefficient chain is the literal 1999848525543113/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1382 : ∀ (p : 1382 < 1732), cc20Eq115CoefficientQ ⟨1382, p⟩ = (1999848525543113 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1383 of the coefficient chain is the literal 9999242624983287/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1383 : ∀ (p : 1383 < 1732), cc20Eq115CoefficientQ ⟨1383, p⟩ = (9999242624983287 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1384 of the coefficient chain is the literal 4999621311132301/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1384 : ∀ (p : 1384 < 1732), cc20Eq115CoefficientQ ⟨1384, p⟩ = (4999621311132301 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1385 of the coefficient chain is the literal 2499810654888593/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1385 : ∀ (p : 1385 < 1732), cc20Eq115CoefficientQ ⟨1385, p⟩ = (2499810654888593 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1386 of the coefficient chain is the literal 4999621308428589/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1386 : ∀ (p : 1386 < 1732), cc20Eq115CoefficientQ ⟨1386, p⟩ = (4999621308428589 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1387 of the coefficient chain is the literal 9999242614168067/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1387 : ∀ (p : 1387 < 1732), cc20Eq115CoefficientQ ⟨1387, p⟩ = (9999242614168067 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1388 of the coefficient chain is the literal 2499810652871909/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1388 : ∀ (p : 1388 < 1732), cc20Eq115CoefficientQ ⟨1388, p⟩ = (2499810652871909 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1389 of the coefficient chain is the literal 4999621304409419/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1389 : ∀ (p : 1389 < 1732), cc20Eq115CoefficientQ ⟨1389, p⟩ = (4999621304409419 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1390 of the coefficient chain is the literal 9999242606160009/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1390 : ∀ (p : 1390 < 1732), cc20Eq115CoefficientQ ⟨1390, p⟩ = (9999242606160009 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1391 of the coefficient chain is the literal 9999242603511777/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1391 : ∀ (p : 1391 < 1732), cc20Eq115CoefficientQ ⟨1391, p⟩ = (9999242603511777 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1392 of the coefficient chain is the literal 9999242600870187/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1392 : ∀ (p : 1392 < 1732), cc20Eq115CoefficientQ ⟨1392, p⟩ = (9999242600870187 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1393 of the coefficient chain is the literal 9999242598239821/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1393 : ∀ (p : 1393 < 1732), cc20Eq115CoefficientQ ⟨1393, p⟩ = (9999242598239821 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1394 of the coefficient chain is the literal 2499810648904679/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1394 : ∀ (p : 1394 < 1732), cc20Eq115CoefficientQ ⟨1394, p⟩ = (2499810648904679 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1395 of the coefficient chain is the literal 1249905324126249/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1395 : ∀ (p : 1395 < 1732), cc20Eq115CoefficientQ ⟨1395, p⟩ = (1249905324126249 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1396 of the coefficient chain is the literal 9999242590408917/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1396 : ∀ (p : 1396 < 1732), cc20Eq115CoefficientQ ⟨1396, p⟩ = (9999242590408917 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1397 of the coefficient chain is the literal 9999242587817601/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1397 : ∀ (p : 1397 < 1732), cc20Eq115CoefficientQ ⟨1397, p⟩ = (9999242587817601 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1398 of the coefficient chain is the literal 1999848517047159/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1398 : ∀ (p : 1398 < 1732), cc20Eq115CoefficientQ ⟨1398, p⟩ = (1999848517047159 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1399 of the coefficient chain is the literal 1999848516532517/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1399 : ∀ (p : 1399 < 1732), cc20Eq115CoefficientQ ⟨1399, p⟩ = (1999848516532517 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1400 of the coefficient chain is the literal 4999621290050491/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1400 : ∀ (p : 1400 < 1732), cc20Eq115CoefficientQ ⟨1400, p⟩ = (4999621290050491 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1401 of the coefficient chain is the literal 4999621288774139/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1401 : ∀ (p : 1401 < 1732), cc20Eq115CoefficientQ ⟨1401, p⟩ = (4999621288774139 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1402 of the coefficient chain is the literal 9999242575004219/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1402 : ∀ (p : 1402 < 1732), cc20Eq115CoefficientQ ⟨1402, p⟩ = (9999242575004219 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1403 of the coefficient chain is the literal 9999242572470459/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1403 : ∀ (p : 1403 < 1732), cc20Eq115CoefficientQ ⟨1403, p⟩ = (9999242572470459 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1404 of the coefficient chain is the literal 2499810642486519/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1404 : ∀ (p : 1404 < 1732), cc20Eq115CoefficientQ ⟨1404, p⟩ = (2499810642486519 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1405 of the coefficient chain is the literal 4999621283716723/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1405 : ∀ (p : 1405 < 1732), cc20Eq115CoefficientQ ⟨1405, p⟩ = (4999621283716723 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1406 of the coefficient chain is the literal 2499810641232633/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1406 : ∀ (p : 1406 < 1732), cc20Eq115CoefficientQ ⟨1406, p⟩ = (2499810641232633 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1407 of the coefficient chain is the literal 62495266015223/ 62500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1407 : ∀ (p : 1407 < 1732), cc20Eq115CoefficientQ ⟨1407, p⟩ = (62495266015223 : ℚ) /  62500000000000 :=
  fun p => by rfl

/-- Branch 1408 of the coefficient chain is the literal 4999621279974157/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1408 : ∀ (p : 1408 < 1732), cc20Eq115CoefficientQ ⟨1408, p⟩ = (4999621279974157 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1409 of the coefficient chain is the literal 4999621278736111/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1409 : ∀ (p : 1409 < 1732), cc20Eq115CoefficientQ ⟨1409, p⟩ = (4999621278736111 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1410 of the coefficient chain is the literal 2499810638750977/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1410 : ∀ (p : 1410 < 1732), cc20Eq115CoefficientQ ⟨1410, p⟩ = (2499810638750977 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1411 of the coefficient chain is the literal 1249905319068563/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1411 : ∀ (p : 1411 < 1732), cc20Eq115CoefficientQ ⟨1411, p⟩ = (1249905319068563 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1412 of the coefficient chain is the literal 4999621275049051/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1412 : ∀ (p : 1412 < 1732), cc20Eq115CoefficientQ ⟨1412, p⟩ = (4999621275049051 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1413 of the coefficient chain is the literal 9999242547658483/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1413 : ∀ (p : 1413 < 1732), cc20Eq115CoefficientQ ⟨1413, p⟩ = (9999242547658483 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1414 of the coefficient chain is the literal 1249905318153309/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1414 : ∀ (p : 1414 < 1732), cc20Eq115CoefficientQ ⟨1414, p⟩ = (1249905318153309 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1415 of the coefficient chain is the literal 9999242542801613/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1415 : ∀ (p : 1415 < 1732), cc20Eq115CoefficientQ ⟨1415, p⟩ = (9999242542801613 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1416 of the coefficient chain is the literal 4999621270205191/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1416 : ∀ (p : 1416 < 1732), cc20Eq115CoefficientQ ⟨1416, p⟩ = (4999621270205191 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1417 of the coefficient chain is the literal 9999242538008677/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1417 : ∀ (p : 1417 < 1732), cc20Eq115CoefficientQ ⟨1417, p⟩ = (9999242538008677 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1418 of the coefficient chain is the literal 4999621267806967/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1418 : ∀ (p : 1418 < 1732), cc20Eq115CoefficientQ ⟨1418, p⟩ = (4999621267806967 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1419 of the coefficient chain is the literal 2499810633307857/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1419 : ∀ (p : 1419 < 1732), cc20Eq115CoefficientQ ⟨1419, p⟩ = (2499810633307857 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1420 of the coefficient chain is the literal 4999621265429141/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1420 : ∀ (p : 1420 < 1732), cc20Eq115CoefficientQ ⟨1420, p⟩ = (4999621265429141 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1421 of the coefficient chain is the literal 2499810632123057/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1421 : ∀ (p : 1421 < 1732), cc20Eq115CoefficientQ ⟨1421, p⟩ = (2499810632123057 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1422 of the coefficient chain is the literal 9999242526138493/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1422 : ∀ (p : 1422 < 1732), cc20Eq115CoefficientQ ⟨1422, p⟩ = (9999242526138493 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1423 of the coefficient chain is the literal 2499810630948033/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1423 : ∀ (p : 1423 < 1732), cc20Eq115CoefficientQ ⟨1423, p⟩ = (2499810630948033 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1424 of the coefficient chain is the literal 4999621260727697/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1424 : ∀ (p : 1424 < 1732), cc20Eq115CoefficientQ ⟨1424, p⟩ = (4999621260727697 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1425 of the coefficient chain is the literal 2499810629782267/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1425 : ∀ (p : 1425 < 1732), cc20Eq115CoefficientQ ⟨1425, p⟩ = (2499810629782267 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1426 of the coefficient chain is the literal 9999242516808753/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1426 : ∀ (p : 1426 < 1732), cc20Eq115CoefficientQ ⟨1426, p⟩ = (9999242516808753 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1427 of the coefficient chain is the literal 9999242514501703/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1427 : ∀ (p : 1427 < 1732), cc20Eq115CoefficientQ ⟨1427, p⟩ = (9999242514501703 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1428 of the coefficient chain is the literal 9999242512201909/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1428 : ∀ (p : 1428 < 1732), cc20Eq115CoefficientQ ⟨1428, p⟩ = (9999242512201909 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1429 of the coefficient chain is the literal 999924250991217/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1429 : ∀ (p : 1429 < 1732), cc20Eq115CoefficientQ ⟨1429, p⟩ = (999924250991217 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1430 of the coefficient chain is the literal 249981062690783/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1430 : ∀ (p : 1430 < 1732), cc20Eq115CoefficientQ ⟨1430, p⟩ = (249981062690783 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 1431 of the coefficient chain is the literal 499962125268033/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1431 : ∀ (p : 1431 < 1732), cc20Eq115CoefficientQ ⟨1431, p⟩ = (499962125268033 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1432 of the coefficient chain is the literal 4999621251548363/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1432 : ∀ (p : 1432 < 1732), cc20Eq115CoefficientQ ⟨1432, p⟩ = (4999621251548363 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1433 of the coefficient chain is the literal 4999621250419821/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1433 : ∀ (p : 1433 < 1732), cc20Eq115CoefficientQ ⟨1433, p⟩ = (4999621250419821 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1434 of the coefficient chain is the literal 39996969994379/ 40000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1434 : ∀ (p : 1434 < 1732), cc20Eq115CoefficientQ ⟨1434, p⟩ = (39996969994379 : ℚ) /  40000000000000 :=
  fun p => by rfl

/-- Branch 1435 of the coefficient chain is the literal 999924249635999/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1435 : ∀ (p : 1435 < 1732), cc20Eq115CoefficientQ ⟨1435, p⟩ = (999924249635999 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1436 of the coefficient chain is the literal 9999242494133581/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1436 : ∀ (p : 1436 < 1732), cc20Eq115CoefficientQ ⟨1436, p⟩ = (9999242494133581 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1437 of the coefficient chain is the literal 499962124595837/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1437 : ∀ (p : 1437 < 1732), cc20Eq115CoefficientQ ⟨1437, p⟩ = (499962124595837 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1438 of the coefficient chain is the literal 9999242489706587/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1438 : ∀ (p : 1438 < 1732), cc20Eq115CoefficientQ ⟨1438, p⟩ = (9999242489706587 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1439 of the coefficient chain is the literal 9999242487504901/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1439 : ∀ (p : 1439 < 1732), cc20Eq115CoefficientQ ⟨1439, p⟩ = (9999242487504901 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1440 of the coefficient chain is the literal 9999242485318743/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1440 : ∀ (p : 1440 < 1732), cc20Eq115CoefficientQ ⟨1440, p⟩ = (9999242485318743 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1441 of the coefficient chain is the literal 9999242483129241/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1441 : ∀ (p : 1441 < 1732), cc20Eq115CoefficientQ ⟨1441, p⟩ = (9999242483129241 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1442 of the coefficient chain is the literal 9999242480954261/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1442 : ∀ (p : 1442 < 1732), cc20Eq115CoefficientQ ⟨1442, p⟩ = (9999242480954261 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1443 of the coefficient chain is the literal 4999621239396261/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1443 : ∀ (p : 1443 < 1732), cc20Eq115CoefficientQ ⟨1443, p⟩ = (4999621239396261 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1444 of the coefficient chain is the literal 9999242476635131/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1444 : ∀ (p : 1444 < 1732), cc20Eq115CoefficientQ ⟨1444, p⟩ = (9999242476635131 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1445 of the coefficient chain is the literal 2499810618622609/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1445 : ∀ (p : 1445 < 1732), cc20Eq115CoefficientQ ⟨1445, p⟩ = (2499810618622609 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1446 of the coefficient chain is the literal 9999242472351927/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1446 : ∀ (p : 1446 < 1732), cc20Eq115CoefficientQ ⟨1446, p⟩ = (9999242472351927 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1447 of the coefficient chain is the literal 2499810617555551/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1447 : ∀ (p : 1447 < 1732), cc20Eq115CoefficientQ ⟨1447, p⟩ = (2499810617555551 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1448 of the coefficient chain is the literal 199984849362059/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1448 : ∀ (p : 1448 < 1732), cc20Eq115CoefficientQ ⟨1448, p⟩ = (199984849362059 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 1449 of the coefficient chain is the literal 9999242465992099/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1449 : ∀ (p : 1449 < 1732), cc20Eq115CoefficientQ ⟨1449, p⟩ = (9999242465992099 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1450 of the coefficient chain is the literal 312476326996489/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1450 : ∀ (p : 1450 < 1732), cc20Eq115CoefficientQ ⟨1450, p⟩ = (312476326996489 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 1451 of the coefficient chain is the literal 9999242461795429/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1451 : ∀ (p : 1451 < 1732), cc20Eq115CoefficientQ ⟨1451, p⟩ = (9999242461795429 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1452 of the coefficient chain is the literal 9999242459711033/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1452 : ∀ (p : 1452 < 1732), cc20Eq115CoefficientQ ⟨1452, p⟩ = (9999242459711033 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1453 of the coefficient chain is the literal 999924245763343/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1453 : ∀ (p : 1453 < 1732), cc20Eq115CoefficientQ ⟨1453, p⟩ = (999924245763343 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1454 of the coefficient chain is the literal 4999621227781101/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1454 : ∀ (p : 1454 < 1732), cc20Eq115CoefficientQ ⟨1454, p⟩ = (4999621227781101 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1455 of the coefficient chain is the literal 9999242453515201/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1455 : ∀ (p : 1455 < 1732), cc20Eq115CoefficientQ ⟨1455, p⟩ = (9999242453515201 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1456 of the coefficient chain is the literal 4999621225729173/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1456 : ∀ (p : 1456 < 1732), cc20Eq115CoefficientQ ⟨1456, p⟩ = (4999621225729173 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1457 of the coefficient chain is the literal 2499810612354069/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1457 : ∀ (p : 1457 < 1732), cc20Eq115CoefficientQ ⟨1457, p⟩ = (2499810612354069 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1458 of the coefficient chain is the literal 9999242447382307/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1458 : ∀ (p : 1458 < 1732), cc20Eq115CoefficientQ ⟨1458, p⟩ = (9999242447382307 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1459 of the coefficient chain is the literal 9999242445358173/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1459 : ∀ (p : 1459 < 1732), cc20Eq115CoefficientQ ⟨1459, p⟩ = (9999242445358173 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1460 of the coefficient chain is the literal 199984848866829/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1460 : ∀ (p : 1460 < 1732), cc20Eq115CoefficientQ ⟨1460, p⟩ = (199984848866829 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 1461 of the coefficient chain is the literal 999924244133841/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1461 : ∀ (p : 1461 < 1732), cc20Eq115CoefficientQ ⟨1461, p⟩ = (999924244133841 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1462 of the coefficient chain is the literal 9999242439339499/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1462 : ∀ (p : 1462 < 1732), cc20Eq115CoefficientQ ⟨1462, p⟩ = (9999242439339499 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1463 of the coefficient chain is the literal 1249905304668693/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1463 : ∀ (p : 1463 < 1732), cc20Eq115CoefficientQ ⟨1463, p⟩ = (1249905304668693 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1464 of the coefficient chain is the literal 24998106088417/ 25000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1464 : ∀ (p : 1464 < 1732), cc20Eq115CoefficientQ ⟨1464, p⟩ = (24998106088417 : ℚ) /  25000000000000 :=
  fun p => by rfl

/-- Branch 1465 of the coefficient chain is the literal 4999621216697519/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1465 : ∀ (p : 1465 < 1732), cc20Eq115CoefficientQ ⟨1465, p⟩ = (4999621216697519 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1466 of the coefficient chain is the literal 499962121571559/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1466 : ∀ (p : 1466 < 1732), cc20Eq115CoefficientQ ⟨1466, p⟩ = (499962121571559 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1467 of the coefficient chain is the literal 9999242429475117/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1467 : ∀ (p : 1467 < 1732), cc20Eq115CoefficientQ ⟨1467, p⟩ = (9999242429475117 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1468 of the coefficient chain is the literal 499962121376341/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1468 : ∀ (p : 1468 < 1732), cc20Eq115CoefficientQ ⟨1468, p⟩ = (499962121376341 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1469 of the coefficient chain is the literal 9999242425586853/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1469 : ∀ (p : 1469 < 1732), cc20Eq115CoefficientQ ⟨1469, p⟩ = (9999242425586853 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1470 of the coefficient chain is the literal 9999242423658471/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1470 : ∀ (p : 1470 < 1732), cc20Eq115CoefficientQ ⟨1470, p⟩ = (9999242423658471 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1471 of the coefficient chain is the literal 9999242421737781/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1471 : ∀ (p : 1471 < 1732), cc20Eq115CoefficientQ ⟨1471, p⟩ = (9999242421737781 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1472 of the coefficient chain is the literal 1249905302477831/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1472 : ∀ (p : 1472 < 1732), cc20Eq115CoefficientQ ⟨1472, p⟩ = (1249905302477831 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1473 of the coefficient chain is the literal 4999621208958861/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1473 : ∀ (p : 1473 < 1732), cc20Eq115CoefficientQ ⟨1473, p⟩ = (4999621208958861 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1474 of the coefficient chain is the literal 2499810604005571/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1474 : ∀ (p : 1474 < 1732), cc20Eq115CoefficientQ ⟨1474, p⟩ = (2499810604005571 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1475 of the coefficient chain is the literal 4999621207066211/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1475 : ∀ (p : 1475 < 1732), cc20Eq115CoefficientQ ⟨1475, p⟩ = (4999621207066211 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1476 of the coefficient chain is the literal 9999242412255797/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1476 : ∀ (p : 1476 < 1732), cc20Eq115CoefficientQ ⟨1476, p⟩ = (9999242412255797 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1477 of the coefficient chain is the literal 9999242410385403/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1477 : ∀ (p : 1477 < 1732), cc20Eq115CoefficientQ ⟨1477, p⟩ = (9999242410385403 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1478 of the coefficient chain is the literal 9999242408519661/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1478 : ∀ (p : 1478 < 1732), cc20Eq115CoefficientQ ⟨1478, p⟩ = (9999242408519661 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1479 of the coefficient chain is the literal 9999242406665603/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1479 : ∀ (p : 1479 < 1732), cc20Eq115CoefficientQ ⟨1479, p⟩ = (9999242406665603 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1480 of the coefficient chain is the literal 9999242404816471/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1480 : ∀ (p : 1480 < 1732), cc20Eq115CoefficientQ ⟨1480, p⟩ = (9999242404816471 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1481 of the coefficient chain is the literal 2499810600751671/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1481 : ∀ (p : 1481 < 1732), cc20Eq115CoefficientQ ⟨1481, p⟩ = (2499810600751671 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1482 of the coefficient chain is the literal 999924240116219/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1482 : ∀ (p : 1482 < 1732), cc20Eq115CoefficientQ ⟨1482, p⟩ = (999924240116219 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1483 of the coefficient chain is the literal 31247632497931/ 31250000000000. -/
theorem cc20Eq115CoefficientQ_branch_1483 : ∀ (p : 1483 < 1732), cc20Eq115CoefficientQ ⟨1483, p⟩ = (31247632497931 : ℚ) /  31250000000000 :=
  fun p => by rfl

/-- Branch 1484 of the coefficient chain is the literal 9999242397525049/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1484 : ∀ (p : 1484 < 1732), cc20Eq115CoefficientQ ⟨1484, p⟩ = (9999242397525049 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1485 of the coefficient chain is the literal 2499810598930213/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1485 : ∀ (p : 1485 < 1732), cc20Eq115CoefficientQ ⟨1485, p⟩ = (2499810598930213 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1486 of the coefficient chain is the literal 9999242393924017/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1486 : ∀ (p : 1486 < 1732), cc20Eq115CoefficientQ ⟨1486, p⟩ = (9999242393924017 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1487 of the coefficient chain is the literal 1999848478427519/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1487 : ∀ (p : 1487 < 1732), cc20Eq115CoefficientQ ⟨1487, p⟩ = (1999848478427519 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1488 of the coefficient chain is the literal 9999242390354759/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1488 : ∀ (p : 1488 < 1732), cc20Eq115CoefficientQ ⟨1488, p⟩ = (9999242390354759 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1489 of the coefficient chain is the literal 78119081160827/ 78125000000000. -/
theorem cc20Eq115CoefficientQ_branch_1489 : ∀ (p : 1489 < 1732), cc20Eq115CoefficientQ ⟨1489, p⟩ = (78119081160827 : ℚ) /  78125000000000 :=
  fun p => by rfl

/-- Branch 1490 of the coefficient chain is the literal 9999242386821551/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1490 : ∀ (p : 1490 < 1732), cc20Eq115CoefficientQ ⟨1490, p⟩ = (9999242386821551 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1491 of the coefficient chain is the literal 9999242385067997/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1491 : ∀ (p : 1491 < 1732), cc20Eq115CoefficientQ ⟨1491, p⟩ = (9999242385067997 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1492 of the coefficient chain is the literal 9999242383321831/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1492 : ∀ (p : 1492 < 1732), cc20Eq115CoefficientQ ⟨1492, p⟩ = (9999242383321831 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1493 of the coefficient chain is the literal 999924238158289/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1493 : ∀ (p : 1493 < 1732), cc20Eq115CoefficientQ ⟨1493, p⟩ = (999924238158289 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1494 of the coefficient chain is the literal 1249905297481177/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1494 : ∀ (p : 1494 < 1732), cc20Eq115CoefficientQ ⟨1494, p⟩ = (1249905297481177 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1495 of the coefficient chain is the literal 312476324316549/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1495 : ∀ (p : 1495 < 1732), cc20Eq115CoefficientQ ⟨1495, p⟩ = (312476324316549 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 1496 of the coefficient chain is the literal 62495264852623/ 62500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1496 : ∀ (p : 1496 < 1732), cc20Eq115CoefficientQ ⟨1496, p⟩ = (62495264852623 : ℚ) /  62500000000000 :=
  fun p => by rfl

/-- Branch 1497 of the coefficient chain is the literal 9999242374721927/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1497 : ∀ (p : 1497 < 1732), cc20Eq115CoefficientQ ⟨1497, p⟩ = (9999242374721927 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1498 of the coefficient chain is the literal 9999242373007569/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1498 : ∀ (p : 1498 < 1732), cc20Eq115CoefficientQ ⟨1498, p⟩ = (9999242373007569 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1499 of the coefficient chain is the literal 1999848474263727/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1499 : ∀ (p : 1499 < 1732), cc20Eq115CoefficientQ ⟨1499, p⟩ = (1999848474263727 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1500 of the coefficient chain is the literal 1249905296204627/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1500 : ∀ (p : 1500 < 1732), cc20Eq115CoefficientQ ⟨1500, p⟩ = (1249905296204627 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1501 of the coefficient chain is the literal 9999242367967011/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1501 : ∀ (p : 1501 < 1732), cc20Eq115CoefficientQ ⟨1501, p⟩ = (9999242367967011 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1502 of the coefficient chain is the literal 399969694652011/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1502 : ∀ (p : 1502 < 1732), cc20Eq115CoefficientQ ⟨1502, p⟩ = (399969694652011 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1503 of the coefficient chain is the literal 1999848472928251/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1503 : ∀ (p : 1503 < 1732), cc20Eq115CoefficientQ ⟨1503, p⟩ = (1999848472928251 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1504 of the coefficient chain is the literal 1999848472598697/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1504 : ∀ (p : 1504 < 1732), cc20Eq115CoefficientQ ⟨1504, p⟩ = (1999848472598697 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1505 of the coefficient chain is the literal 2499810590338179/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1505 : ∀ (p : 1505 < 1732), cc20Eq115CoefficientQ ⟨1505, p⟩ = (2499810590338179 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1506 of the coefficient chain is the literal 2499810589930471/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1506 : ∀ (p : 1506 < 1732), cc20Eq115CoefficientQ ⟨1506, p⟩ = (2499810589930471 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1507 of the coefficient chain is the literal 9999242358094637/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1507 : ∀ (p : 1507 < 1732), cc20Eq115CoefficientQ ⟨1507, p⟩ = (9999242358094637 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1508 of the coefficient chain is the literal 4999621178238667/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1508 : ∀ (p : 1508 < 1732), cc20Eq115CoefficientQ ⟨1508, p⟩ = (4999621178238667 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1509 of the coefficient chain is the literal 4999621177434113/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1509 : ∀ (p : 1509 < 1732), cc20Eq115CoefficientQ ⟨1509, p⟩ = (4999621177434113 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1510 of the coefficient chain is the literal 624952647079351/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1510 : ∀ (p : 1510 < 1732), cc20Eq115CoefficientQ ⟨1510, p⟩ = (624952647079351 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1511 of the coefficient chain is the literal 9999242351676619/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1511 : ∀ (p : 1511 < 1732), cc20Eq115CoefficientQ ⟨1511, p⟩ = (9999242351676619 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1512 of the coefficient chain is the literal 624952646880593/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1512 : ∀ (p : 1512 < 1732), cc20Eq115CoefficientQ ⟨1512, p⟩ = (624952646880593 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1513 of the coefficient chain is the literal 2499810587127727/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1513 : ∀ (p : 1513 < 1732), cc20Eq115CoefficientQ ⟨1513, p⟩ = (2499810587127727 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1514 of the coefficient chain is the literal 999924234694197/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1514 : ∀ (p : 1514 < 1732), cc20Eq115CoefficientQ ⟨1514, p⟩ = (999924234694197 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1515 of the coefficient chain is the literal 9999242345377657/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1515 : ∀ (p : 1515 < 1732), cc20Eq115CoefficientQ ⟨1515, p⟩ = (9999242345377657 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1516 of the coefficient chain is the literal 9999242343819309/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1516 : ∀ (p : 1516 < 1732), cc20Eq115CoefficientQ ⟨1516, p⟩ = (9999242343819309 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1517 of the coefficient chain is the literal 249981058557237/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1517 : ∀ (p : 1517 < 1732), cc20Eq115CoefficientQ ⟨1517, p⟩ = (249981058557237 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 1518 of the coefficient chain is the literal 4999621170375399/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1518 : ∀ (p : 1518 < 1732), cc20Eq115CoefficientQ ⟨1518, p⟩ = (4999621170375399 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1519 of the coefficient chain is the literal 1249905292402517/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1519 : ∀ (p : 1519 < 1732), cc20Eq115CoefficientQ ⟨1519, p⟩ = (1249905292402517 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1520 of the coefficient chain is the literal 4999621168847563/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1520 : ∀ (p : 1520 < 1732), cc20Eq115CoefficientQ ⟨1520, p⟩ = (4999621168847563 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1521 of the coefficient chain is the literal 9999242336153923/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1521 : ∀ (p : 1521 < 1732), cc20Eq115CoefficientQ ⟨1521, p⟩ = (9999242336153923 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1522 of the coefficient chain is the literal 9999242334683529/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1522 : ∀ (p : 1522 < 1732), cc20Eq115CoefficientQ ⟨1522, p⟩ = (9999242334683529 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1523 of the coefficient chain is the literal 9999242333182369/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1523 : ∀ (p : 1523 < 1732), cc20Eq115CoefficientQ ⟨1523, p⟩ = (9999242333182369 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1524 of the coefficient chain is the literal 4999621165844711/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1524 : ∀ (p : 1524 < 1732), cc20Eq115CoefficientQ ⟨1524, p⟩ = (4999621165844711 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1525 of the coefficient chain is the literal 1249905291276253/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1525 : ∀ (p : 1525 < 1732), cc20Eq115CoefficientQ ⟨1525, p⟩ = (1249905291276253 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1526 of the coefficient chain is the literal 4999621164367747/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1526 : ∀ (p : 1526 < 1732), cc20Eq115CoefficientQ ⟨1526, p⟩ = (4999621164367747 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1527 of the coefficient chain is the literal 2499810581816957/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1527 : ∀ (p : 1527 < 1732), cc20Eq115CoefficientQ ⟨1527, p⟩ = (2499810581816957 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1528 of the coefficient chain is the literal 9999242325808013/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1528 : ∀ (p : 1528 < 1732), cc20Eq115CoefficientQ ⟨1528, p⟩ = (9999242325808013 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1529 of the coefficient chain is the literal 9999242324356241/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1529 : ∀ (p : 1529 < 1732), cc20Eq115CoefficientQ ⟨1529, p⟩ = (9999242324356241 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1530 of the coefficient chain is the literal 999924232291333/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1530 : ∀ (p : 1530 < 1732), cc20Eq115CoefficientQ ⟨1530, p⟩ = (999924232291333 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1531 of the coefficient chain is the literal 9999242321476587/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1531 : ∀ (p : 1531 < 1732), cc20Eq115CoefficientQ ⟨1531, p⟩ = (9999242321476587 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1532 of the coefficient chain is the literal 9999242320054847/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1532 : ∀ (p : 1532 < 1732), cc20Eq115CoefficientQ ⟨1532, p⟩ = (9999242320054847 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1533 of the coefficient chain is the literal 9999242318635183/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1533 : ∀ (p : 1533 < 1732), cc20Eq115CoefficientQ ⟨1533, p⟩ = (9999242318635183 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1534 of the coefficient chain is the literal 9999242317238769/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1534 : ∀ (p : 1534 < 1732), cc20Eq115CoefficientQ ⟨1534, p⟩ = (9999242317238769 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1535 of the coefficient chain is the literal 9999242315810293/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1535 : ∀ (p : 1535 < 1732), cc20Eq115CoefficientQ ⟨1535, p⟩ = (9999242315810293 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1536 of the coefficient chain is the literal 9999242314414817/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1536 : ∀ (p : 1536 < 1732), cc20Eq115CoefficientQ ⟨1536, p⟩ = (9999242314414817 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1537 of the coefficient chain is the literal 1999848462605457/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1537 : ∀ (p : 1537 < 1732), cc20Eq115CoefficientQ ⟨1537, p⟩ = (1999848462605457 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1538 of the coefficient chain is the literal 9999242311652853/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1538 : ∀ (p : 1538 < 1732), cc20Eq115CoefficientQ ⟨1538, p⟩ = (9999242311652853 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1539 of the coefficient chain is the literal 999924231027653/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1539 : ∀ (p : 1539 < 1732), cc20Eq115CoefficientQ ⟨1539, p⟩ = (999924231027653 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1540 of the coefficient chain is the literal 9999242308897571/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1540 : ∀ (p : 1540 < 1732), cc20Eq115CoefficientQ ⟨1540, p⟩ = (9999242308897571 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1541 of the coefficient chain is the literal 1999848461508673/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1541 : ∀ (p : 1541 < 1732), cc20Eq115CoefficientQ ⟨1541, p⟩ = (1999848461508673 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1542 of the coefficient chain is the literal 9999242306195113/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1542 : ∀ (p : 1542 < 1732), cc20Eq115CoefficientQ ⟨1542, p⟩ = (9999242306195113 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1543 of the coefficient chain is the literal 1999848460970689/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1543 : ∀ (p : 1543 < 1732), cc20Eq115CoefficientQ ⟨1543, p⟩ = (1999848460970689 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1544 of the coefficient chain is the literal 4999621151757891/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1544 : ∀ (p : 1544 < 1732), cc20Eq115CoefficientQ ⟨1544, p⟩ = (4999621151757891 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1545 of the coefficient chain is the literal 9999242302189089/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1545 : ∀ (p : 1545 < 1732), cc20Eq115CoefficientQ ⟨1545, p⟩ = (9999242302189089 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1546 of the coefficient chain is the literal 624952643804377/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1546 : ∀ (p : 1546 < 1732), cc20Eq115CoefficientQ ⟨1546, p⟩ = (624952643804377 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1547 of the coefficient chain is the literal 312476321861121/ 312500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1547 : ∀ (p : 1547 < 1732), cc20Eq115CoefficientQ ⟨1547, p⟩ = (312476321861121 : ℚ) /  312500000000000 :=
  fun p => by rfl

/-- Branch 1548 of the coefficient chain is the literal 499962114912477/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1548 : ∀ (p : 1548 < 1732), cc20Eq115CoefficientQ ⟨1548, p⟩ = (499962114912477 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1549 of the coefficient chain is the literal 4999621148477531/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1549 : ∀ (p : 1549 < 1732), cc20Eq115CoefficientQ ⟨1549, p⟩ = (4999621148477531 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1550 of the coefficient chain is the literal 9999242295664951/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1550 : ∀ (p : 1550 < 1732), cc20Eq115CoefficientQ ⟨1550, p⟩ = (9999242295664951 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1551 of the coefficient chain is the literal 9999242294381879/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1551 : ∀ (p : 1551 < 1732), cc20Eq115CoefficientQ ⟨1551, p⟩ = (9999242294381879 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1552 of the coefficient chain is the literal 9999242293112713/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1552 : ∀ (p : 1552 < 1732), cc20Eq115CoefficientQ ⟨1552, p⟩ = (9999242293112713 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1553 of the coefficient chain is the literal 9999242291839473/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1553 : ∀ (p : 1553 < 1732), cc20Eq115CoefficientQ ⟨1553, p⟩ = (9999242291839473 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1554 of the coefficient chain is the literal 1249905286322641/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1554 : ∀ (p : 1554 < 1732), cc20Eq115CoefficientQ ⟨1554, p⟩ = (1249905286322641 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1555 of the coefficient chain is the literal 4999621144672017/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1555 : ∀ (p : 1555 < 1732), cc20Eq115CoefficientQ ⟨1555, p⟩ = (4999621144672017 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1556 of the coefficient chain is the literal 499962114404361/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1556 : ∀ (p : 1556 < 1732), cc20Eq115CoefficientQ ⟨1556, p⟩ = (499962114404361 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1557 of the coefficient chain is the literal 2499810571711991/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1557 : ∀ (p : 1557 < 1732), cc20Eq115CoefficientQ ⟨1557, p⟩ = (2499810571711991 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1558 of the coefficient chain is the literal 9999242285620087/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1558 : ∀ (p : 1558 < 1732), cc20Eq115CoefficientQ ⟨1558, p⟩ = (9999242285620087 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1559 of the coefficient chain is the literal 2499810571099457/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1559 : ∀ (p : 1559 < 1732), cc20Eq115CoefficientQ ⟨1559, p⟩ = (2499810571099457 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1560 of the coefficient chain is the literal 9999242283183477/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1560 : ∀ (p : 1560 < 1732), cc20Eq115CoefficientQ ⟨1560, p⟩ = (9999242283183477 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1561 of the coefficient chain is the literal 9999242281976851/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1561 : ∀ (p : 1561 < 1732), cc20Eq115CoefficientQ ⟨1561, p⟩ = (9999242281976851 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1562 of the coefficient chain is the literal 4999621140388749/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1562 : ∀ (p : 1562 < 1732), cc20Eq115CoefficientQ ⟨1562, p⟩ = (4999621140388749 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1563 of the coefficient chain is the literal 9999242279585039/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1563 : ∀ (p : 1563 < 1732), cc20Eq115CoefficientQ ⟨1563, p⟩ = (9999242279585039 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1564 of the coefficient chain is the literal 9999242278401567/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1564 : ∀ (p : 1564 < 1732), cc20Eq115CoefficientQ ⟨1564, p⟩ = (9999242278401567 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1565 of the coefficient chain is the literal 199984845544587/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1565 : ∀ (p : 1565 < 1732), cc20Eq115CoefficientQ ⟨1565, p⟩ = (199984845544587 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 1566 of the coefficient chain is the literal 4999621138026417/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1566 : ∀ (p : 1566 < 1732), cc20Eq115CoefficientQ ⟨1566, p⟩ = (4999621138026417 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1567 of the coefficient chain is the literal 999924227489291/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1567 : ∀ (p : 1567 < 1732), cc20Eq115CoefficientQ ⟨1567, p⟩ = (999924227489291 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1568 of the coefficient chain is the literal 4999621136869021/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1568 : ∀ (p : 1568 < 1732), cc20Eq115CoefficientQ ⟨1568, p⟩ = (4999621136869021 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1569 of the coefficient chain is the literal 1999848454518469/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1569 : ∀ (p : 1569 < 1732), cc20Eq115CoefficientQ ⟨1569, p⟩ = (1999848454518469 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1570 of the coefficient chain is the literal 999924227145259/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1570 : ∀ (p : 1570 < 1732), cc20Eq115CoefficientQ ⟨1570, p⟩ = (999924227145259 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1571 of the coefficient chain is the literal 999924227032049/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1571 : ∀ (p : 1571 < 1732), cc20Eq115CoefficientQ ⟨1571, p⟩ = (999924227032049 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1572 of the coefficient chain is the literal 4999621134597053/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1572 : ∀ (p : 1572 < 1732), cc20Eq115CoefficientQ ⟨1572, p⟩ = (4999621134597053 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1573 of the coefficient chain is the literal 4999621134039269/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1573 : ∀ (p : 1573 < 1732), cc20Eq115CoefficientQ ⟨1573, p⟩ = (4999621134039269 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1574 of the coefficient chain is the literal 1249905283371107/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1574 : ∀ (p : 1574 < 1732), cc20Eq115CoefficientQ ⟨1574, p⟩ = (1249905283371107 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1575 of the coefficient chain is the literal 156238160403913/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_1575 : ∀ (p : 1575 < 1732), cc20Eq115CoefficientQ ⟨1575, p⟩ = (156238160403913 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 1576 of the coefficient chain is the literal 9999242264761683/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1576 : ∀ (p : 1576 < 1732), cc20Eq115CoefficientQ ⟨1576, p⟩ = (9999242264761683 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1577 of the coefficient chain is the literal 9999242263674267/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1577 : ∀ (p : 1577 < 1732), cc20Eq115CoefficientQ ⟨1577, p⟩ = (9999242263674267 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1578 of the coefficient chain is the literal 9999242262569933/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1578 : ∀ (p : 1578 < 1732), cc20Eq115CoefficientQ ⟨1578, p⟩ = (9999242262569933 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1579 of the coefficient chain is the literal 1249905282690903/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1579 : ∀ (p : 1579 < 1732), cc20Eq115CoefficientQ ⟨1579, p⟩ = (1249905282690903 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1580 of the coefficient chain is the literal 4999621130230577/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1580 : ∀ (p : 1580 < 1732), cc20Eq115CoefficientQ ⟨1580, p⟩ = (4999621130230577 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1581 of the coefficient chain is the literal 9999242259400987/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1581 : ∀ (p : 1581 < 1732), cc20Eq115CoefficientQ ⟨1581, p⟩ = (9999242259400987 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1582 of the coefficient chain is the literal 9999242258352081/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1582 : ∀ (p : 1582 < 1732), cc20Eq115CoefficientQ ⟨1582, p⟩ = (9999242258352081 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1583 of the coefficient chain is the literal 12499052821633/ 12500000000000. -/
theorem cc20Eq115CoefficientQ_branch_1583 : ∀ (p : 1583 < 1732), cc20Eq115CoefficientQ ⟨1583, p⟩ = (12499052821633 : ℚ) /  12500000000000 :=
  fun p => by rfl

/-- Branch 1584 of the coefficient chain is the literal 9999242256267673/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1584 : ∀ (p : 1584 < 1732), cc20Eq115CoefficientQ ⟨1584, p⟩ = (9999242256267673 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1585 of the coefficient chain is the literal 9999242255242393/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1585 : ∀ (p : 1585 < 1732), cc20Eq115CoefficientQ ⟨1585, p⟩ = (9999242255242393 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1586 of the coefficient chain is the literal 1999848450843879/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1586 : ∀ (p : 1586 < 1732), cc20Eq115CoefficientQ ⟨1586, p⟩ = (1999848450843879 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1587 of the coefficient chain is the literal 2499810563301647/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1587 : ∀ (p : 1587 < 1732), cc20Eq115CoefficientQ ⟨1587, p⟩ = (2499810563301647 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1588 of the coefficient chain is the literal 9999242252197761/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1588 : ∀ (p : 1588 < 1732), cc20Eq115CoefficientQ ⟨1588, p⟩ = (9999242252197761 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1589 of the coefficient chain is the literal 499962112559871/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1589 : ∀ (p : 1589 < 1732), cc20Eq115CoefficientQ ⟨1589, p⟩ = (499962112559871 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1590 of the coefficient chain is the literal 999924225020379/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1590 : ∀ (p : 1590 < 1732), cc20Eq115CoefficientQ ⟨1590, p⟩ = (999924225020379 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1591 of the coefficient chain is the literal 399969689968713/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1591 : ∀ (p : 1591 < 1732), cc20Eq115CoefficientQ ⟨1591, p⟩ = (399969689968713 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1592 of the coefficient chain is the literal 399969689929633/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1592 : ∀ (p : 1592 < 1732), cc20Eq115CoefficientQ ⟨1592, p⟩ = (399969689929633 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1593 of the coefficient chain is the literal 79993937978171/ 80000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1593 : ∀ (p : 1593 < 1732), cc20Eq115CoefficientQ ⟨1593, p⟩ = (79993937978171 : ℚ) /  80000000000000 :=
  fun p => by rfl

/-- Branch 1594 of the coefficient chain is the literal 9999242246306369/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1594 : ∀ (p : 1594 < 1732), cc20Eq115CoefficientQ ⟨1594, p⟩ = (9999242246306369 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1595 of the coefficient chain is the literal 4999621122674387/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1595 : ∀ (p : 1595 < 1732), cc20Eq115CoefficientQ ⟨1595, p⟩ = (4999621122674387 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1596 of the coefficient chain is the literal 9999242244400511/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1596 : ∀ (p : 1596 < 1732), cc20Eq115CoefficientQ ⟨1596, p⟩ = (9999242244400511 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1597 of the coefficient chain is the literal 1999848448691937/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1597 : ∀ (p : 1597 < 1732), cc20Eq115CoefficientQ ⟨1597, p⟩ = (1999848448691937 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1598 of the coefficient chain is the literal 9999242242525073/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1598 : ∀ (p : 1598 < 1732), cc20Eq115CoefficientQ ⟨1598, p⟩ = (9999242242525073 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1599 of the coefficient chain is the literal 4999621120803891/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1599 : ∀ (p : 1599 < 1732), cc20Eq115CoefficientQ ⟨1599, p⟩ = (4999621120803891 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1600 of the coefficient chain is the literal 2499810560169021/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1600 : ∀ (p : 1600 < 1732), cc20Eq115CoefficientQ ⟨1600, p⟩ = (2499810560169021 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1601 of the coefficient chain is the literal 9999242239763261/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1601 : ∀ (p : 1601 < 1732), cc20Eq115CoefficientQ ⟨1601, p⟩ = (9999242239763261 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1602 of the coefficient chain is the literal 9999242238855703/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1602 : ∀ (p : 1602 < 1732), cc20Eq115CoefficientQ ⟨1602, p⟩ = (9999242238855703 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1603 of the coefficient chain is the literal 9999242237956729/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1603 : ∀ (p : 1603 < 1732), cc20Eq115CoefficientQ ⟨1603, p⟩ = (9999242237956729 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1604 of the coefficient chain is the literal 9999242237067681/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1604 : ∀ (p : 1604 < 1732), cc20Eq115CoefficientQ ⟨1604, p⟩ = (9999242237067681 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1605 of the coefficient chain is the literal 4999621118091279/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1605 : ∀ (p : 1605 < 1732), cc20Eq115CoefficientQ ⟨1605, p⟩ = (4999621118091279 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1606 of the coefficient chain is the literal 9999242235305201/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1606 : ∀ (p : 1606 < 1732), cc20Eq115CoefficientQ ⟨1606, p⟩ = (9999242235305201 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1607 of the coefficient chain is the literal 4999621117220629/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1607 : ∀ (p : 1607 < 1732), cc20Eq115CoefficientQ ⟨1607, p⟩ = (4999621117220629 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1608 of the coefficient chain is the literal 1249905279196763/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1608 : ∀ (p : 1608 < 1732), cc20Eq115CoefficientQ ⟨1608, p⟩ = (1249905279196763 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1609 of the coefficient chain is the literal 499962111635943/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1609 : ∀ (p : 1609 < 1732), cc20Eq115CoefficientQ ⟨1609, p⟩ = (499962111635943 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1610 of the coefficient chain is the literal 9999242231865987/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1610 : ∀ (p : 1610 < 1732), cc20Eq115CoefficientQ ⟨1610, p⟩ = (9999242231865987 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1611 of the coefficient chain is the literal 249981055775499/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1611 : ∀ (p : 1611 < 1732), cc20Eq115CoefficientQ ⟨1611, p⟩ = (249981055775499 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 1612 of the coefficient chain is the literal 9999242230213193/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1612 : ∀ (p : 1612 < 1732), cc20Eq115CoefficientQ ⟨1612, p⟩ = (9999242230213193 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1613 of the coefficient chain is the literal 1999848445875219/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1613 : ∀ (p : 1613 < 1732), cc20Eq115CoefficientQ ⟨1613, p⟩ = (1999848445875219 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1614 of the coefficient chain is the literal 9999242228552099/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1614 : ∀ (p : 1614 < 1732), cc20Eq115CoefficientQ ⟨1614, p⟩ = (9999242228552099 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1615 of the coefficient chain is the literal 9999242227740017/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1615 : ∀ (p : 1615 < 1732), cc20Eq115CoefficientQ ⟨1615, p⟩ = (9999242227740017 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1616 of the coefficient chain is the literal 9999242226931307/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1616 : ∀ (p : 1616 < 1732), cc20Eq115CoefficientQ ⟨1616, p⟩ = (9999242226931307 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1617 of the coefficient chain is the literal 9999242226132009/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1617 : ∀ (p : 1617 < 1732), cc20Eq115CoefficientQ ⟨1617, p⟩ = (9999242226132009 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1618 of the coefficient chain is the literal 2499810556335517/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1618 : ∀ (p : 1618 < 1732), cc20Eq115CoefficientQ ⟨1618, p⟩ = (2499810556335517 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1619 of the coefficient chain is the literal 4999621112278773/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1619 : ∀ (p : 1619 < 1732), cc20Eq115CoefficientQ ⟨1619, p⟩ = (4999621112278773 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1620 of the coefficient chain is the literal 9999242223780659/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1620 : ∀ (p : 1620 < 1732), cc20Eq115CoefficientQ ⟨1620, p⟩ = (9999242223780659 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1621 of the coefficient chain is the literal 2499810555752267/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1621 : ∀ (p : 1621 < 1732), cc20Eq115CoefficientQ ⟨1621, p⟩ = (2499810555752267 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1622 of the coefficient chain is the literal 1249905277780811/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1622 : ∀ (p : 1622 < 1732), cc20Eq115CoefficientQ ⟨1622, p⟩ = (1249905277780811 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1623 of the coefficient chain is the literal 9999242221499197/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1623 : ∀ (p : 1623 < 1732), cc20Eq115CoefficientQ ⟨1623, p⟩ = (9999242221499197 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1624 of the coefficient chain is the literal 4999621110371137/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1624 : ∀ (p : 1624 < 1732), cc20Eq115CoefficientQ ⟨1624, p⟩ = (4999621110371137 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1625 of the coefficient chain is the literal 9999242220001163/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1625 : ∀ (p : 1625 < 1732), cc20Eq115CoefficientQ ⟨1625, p⟩ = (9999242220001163 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1626 of the coefficient chain is the literal 9999242219266629/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1626 : ∀ (p : 1626 < 1732), cc20Eq115CoefficientQ ⟨1626, p⟩ = (9999242219266629 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1627 of the coefficient chain is the literal 1249905277317237/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1627 : ∀ (p : 1627 < 1732), cc20Eq115CoefficientQ ⟨1627, p⟩ = (1249905277317237 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1628 of the coefficient chain is the literal 9999242217817489/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1628 : ∀ (p : 1628 < 1732), cc20Eq115CoefficientQ ⟨1628, p⟩ = (9999242217817489 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1629 of the coefficient chain is the literal 9999242217107447/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1629 : ∀ (p : 1629 < 1732), cc20Eq115CoefficientQ ⟨1629, p⟩ = (9999242217107447 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1630 of the coefficient chain is the literal 4999621108202151/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1630 : ∀ (p : 1630 < 1732), cc20Eq115CoefficientQ ⟨1630, p⟩ = (4999621108202151 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1631 of the coefficient chain is the literal 4999621107859293/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1631 : ∀ (p : 1631 < 1732), cc20Eq115CoefficientQ ⟨1631, p⟩ = (4999621107859293 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1632 of the coefficient chain is the literal 2499810553749791/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1632 : ∀ (p : 1632 < 1732), cc20Eq115CoefficientQ ⟨1632, p⟩ = (2499810553749791 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1633 of the coefficient chain is the literal 9999242214315829/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1633 : ∀ (p : 1633 < 1732), cc20Eq115CoefficientQ ⟨1633, p⟩ = (9999242214315829 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1634 of the coefficient chain is the literal 9999242213637571/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1634 : ∀ (p : 1634 < 1732), cc20Eq115CoefficientQ ⟨1634, p⟩ = (9999242213637571 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1635 of the coefficient chain is the literal 999924221296907/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1635 : ∀ (p : 1635 < 1732), cc20Eq115CoefficientQ ⟨1635, p⟩ = (999924221296907 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1636 of the coefficient chain is the literal 4999621106152461/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1636 : ∀ (p : 1636 < 1732), cc20Eq115CoefficientQ ⟨1636, p⟩ = (4999621106152461 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1637 of the coefficient chain is the literal 4999621105824537/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1637 : ∀ (p : 1637 < 1732), cc20Eq115CoefficientQ ⟨1637, p⟩ = (4999621105824537 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1638 of the coefficient chain is the literal 9999242210998409/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1638 : ∀ (p : 1638 < 1732), cc20Eq115CoefficientQ ⟨1638, p⟩ = (9999242210998409 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1639 of the coefficient chain is the literal 2499810552589167/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1639 : ∀ (p : 1639 < 1732), cc20Eq115CoefficientQ ⟨1639, p⟩ = (2499810552589167 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1640 of the coefficient chain is the literal 1999848441943547/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1640 : ∀ (p : 1640 < 1732), cc20Eq115CoefficientQ ⟨1640, p⟩ = (1999848441943547 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1641 of the coefficient chain is the literal 99992422090889/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1641 : ∀ (p : 1641 < 1732), cc20Eq115CoefficientQ ⟨1641, p⟩ = (99992422090889 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 1642 of the coefficient chain is the literal 4999621104235437/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1642 : ∀ (p : 1642 < 1732), cc20Eq115CoefficientQ ⟨1642, p⟩ = (4999621104235437 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1643 of the coefficient chain is the literal 9999242207858707/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1643 : ∀ (p : 1643 < 1732), cc20Eq115CoefficientQ ⟨1643, p⟩ = (9999242207858707 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1644 of the coefficient chain is the literal 4999621103625931/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1644 : ∀ (p : 1644 < 1732), cc20Eq115CoefficientQ ⟨1644, p⟩ = (4999621103625931 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1645 of the coefficient chain is the literal 9999242206640339/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1645 : ∀ (p : 1645 < 1732), cc20Eq115CoefficientQ ⟨1645, p⟩ = (9999242206640339 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1646 of the coefficient chain is the literal 2499810551511867/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1646 : ∀ (p : 1646 < 1732), cc20Eq115CoefficientQ ⟨1646, p⟩ = (2499810551511867 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1647 of the coefficient chain is the literal 499962110273057/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1647 : ∀ (p : 1647 < 1732), cc20Eq115CoefficientQ ⟨1647, p⟩ = (499962110273057 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1648 of the coefficient chain is the literal 4999621102441227/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1648 : ∀ (p : 1648 < 1732), cc20Eq115CoefficientQ ⟨1648, p⟩ = (4999621102441227 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1649 of the coefficient chain is the literal 499962110215599/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1649 : ∀ (p : 1649 < 1732), cc20Eq115CoefficientQ ⟨1649, p⟩ = (499962110215599 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1650 of the coefficient chain is the literal 2499810550930213/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1650 : ∀ (p : 1650 < 1732), cc20Eq115CoefficientQ ⟨1650, p⟩ = (2499810550930213 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1651 of the coefficient chain is the literal 9999242203179697/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1651 : ∀ (p : 1651 < 1732), cc20Eq115CoefficientQ ⟨1651, p⟩ = (9999242203179697 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1652 of the coefficient chain is the literal 9999242202628363/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1652 : ∀ (p : 1652 < 1732), cc20Eq115CoefficientQ ⟨1652, p⟩ = (9999242202628363 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1653 of the coefficient chain is the literal 9999242202083203/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1653 : ∀ (p : 1653 < 1732), cc20Eq115CoefficientQ ⟨1653, p⟩ = (9999242202083203 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1654 of the coefficient chain is the literal 2499810550385867/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1654 : ∀ (p : 1654 < 1732), cc20Eq115CoefficientQ ⟨1654, p⟩ = (2499810550385867 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1655 of the coefficient chain is the literal 399969688040471/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1655 : ∀ (p : 1655 < 1732), cc20Eq115CoefficientQ ⟨1655, p⟩ = (399969688040471 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1656 of the coefficient chain is the literal 4999621100244239/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1656 : ∀ (p : 1656 < 1732), cc20Eq115CoefficientQ ⟨1656, p⟩ = (4999621100244239 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1657 of the coefficient chain is the literal 2499810549992881/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1657 : ∀ (p : 1657 < 1732), cc20Eq115CoefficientQ ⟨1657, p⟩ = (2499810549992881 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1658 of the coefficient chain is the literal 9999242199460537/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1658 : ∀ (p : 1658 < 1732), cc20Eq115CoefficientQ ⟨1658, p⟩ = (9999242199460537 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1659 of the coefficient chain is the literal 9999242198957307/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1659 : ∀ (p : 1659 < 1732), cc20Eq115CoefficientQ ⟨1659, p⟩ = (9999242198957307 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1660 of the coefficient chain is the literal 9999242198460909/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1660 : ∀ (p : 1660 < 1732), cc20Eq115CoefficientQ ⟨1660, p⟩ = (9999242198460909 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1661 of the coefficient chain is the literal 1999848439594141/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1661 : ∀ (p : 1661 < 1732), cc20Eq115CoefficientQ ⟨1661, p⟩ = (1999848439594141 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1662 of the coefficient chain is the literal 4999621098744617/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1662 : ∀ (p : 1662 < 1732), cc20Eq115CoefficientQ ⟨1662, p⟩ = (4999621098744617 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1663 of the coefficient chain is the literal 9999242197012247/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1663 : ∀ (p : 1663 < 1732), cc20Eq115CoefficientQ ⟨1663, p⟩ = (9999242197012247 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1664 of the coefficient chain is the literal 4999621098271191/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1664 : ∀ (p : 1664 < 1732), cc20Eq115CoefficientQ ⟨1664, p⟩ = (4999621098271191 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1665 of the coefficient chain is the literal 9999242196081173/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1665 : ∀ (p : 1665 < 1732), cc20Eq115CoefficientQ ⟨1665, p⟩ = (9999242196081173 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1666 of the coefficient chain is the literal 4999621097814681/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1666 : ∀ (p : 1666 < 1732), cc20Eq115CoefficientQ ⟨1666, p⟩ = (4999621097814681 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1667 of the coefficient chain is the literal 4999621097589527/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1667 : ∀ (p : 1667 < 1732), cc20Eq115CoefficientQ ⟨1667, p⟩ = (4999621097589527 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1668 of the coefficient chain is the literal 156238159292747/ 156250000000000. -/
theorem cc20Eq115CoefficientQ_branch_1668 : ∀ (p : 1668 < 1732), cc20Eq115CoefficientQ ⟨1668, p⟩ = (156238159292747 : ℚ) /  156250000000000 :=
  fun p => by rfl

/-- Branch 1669 of the coefficient chain is the literal 999924219430163/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1669 : ∀ (p : 1669 < 1732), cc20Eq115CoefficientQ ⟨1669, p⟩ = (999924219430163 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1670 of the coefficient chain is the literal 9999242193871519/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1670 : ∀ (p : 1670 < 1732), cc20Eq115CoefficientQ ⟨1670, p⟩ = (9999242193871519 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1671 of the coefficient chain is the literal 249981054836341/ 250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1671 : ∀ (p : 1671 < 1732), cc20Eq115CoefficientQ ⟨1671, p⟩ = (249981054836341 : ℚ) /  250000000000000 :=
  fun p => by rfl

/-- Branch 1672 of the coefficient chain is the literal 199984843860773/ 200000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1672 : ∀ (p : 1672 < 1732), cc20Eq115CoefficientQ ⟨1672, p⟩ = (199984843860773 : ℚ) /  200000000000000 :=
  fun p => by rfl

/-- Branch 1673 of the coefficient chain is the literal 399969687705269/ 400000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1673 : ∀ (p : 1673 < 1732), cc20Eq115CoefficientQ ⟨1673, p⟩ = (399969687705269 : ℚ) /  400000000000000 :=
  fun p => by rfl

/-- Branch 1674 of the coefficient chain is the literal 2499810548057837/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1674 : ∀ (p : 1674 < 1732), cc20Eq115CoefficientQ ⟨1674, p⟩ = (2499810548057837 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1675 of the coefficient chain is the literal 9999242191838057/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1675 : ∀ (p : 1675 < 1732), cc20Eq115CoefficientQ ⟨1675, p⟩ = (9999242191838057 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1676 of the coefficient chain is the literal 9999242191439499/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1676 : ∀ (p : 1676 < 1732), cc20Eq115CoefficientQ ⟨1676, p⟩ = (9999242191439499 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1677 of the coefficient chain is the literal 9999242191056591/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1677 : ∀ (p : 1677 < 1732), cc20Eq115CoefficientQ ⟨1677, p⟩ = (9999242191056591 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1678 of the coefficient chain is the literal 4999621095353229/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1678 : ∀ (p : 1678 < 1732), cc20Eq115CoefficientQ ⟨1678, p⟩ = (4999621095353229 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1679 of the coefficient chain is the literal 9999242190339389/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1679 : ∀ (p : 1679 < 1732), cc20Eq115CoefficientQ ⟨1679, p⟩ = (9999242190339389 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1680 of the coefficient chain is the literal 9999242189978127/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1680 : ∀ (p : 1680 < 1732), cc20Eq115CoefficientQ ⟨1680, p⟩ = (9999242189978127 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1681 of the coefficient chain is the literal 2499810547406667/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1681 : ∀ (p : 1681 < 1732), cc20Eq115CoefficientQ ⟨1681, p⟩ = (2499810547406667 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1682 of the coefficient chain is the literal 999924218928157/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1682 : ∀ (p : 1682 < 1732), cc20Eq115CoefficientQ ⟨1682, p⟩ = (999924218928157 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1683 of the coefficient chain is the literal 9999242188943641/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1683 : ∀ (p : 1683 < 1732), cc20Eq115CoefficientQ ⟨1683, p⟩ = (9999242188943641 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1684 of the coefficient chain is the literal 1999848437722517/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1684 : ∀ (p : 1684 < 1732), cc20Eq115CoefficientQ ⟨1684, p⟩ = (1999848437722517 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1685 of the coefficient chain is the literal 2499810547071879/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1685 : ∀ (p : 1685 < 1732), cc20Eq115CoefficientQ ⟨1685, p⟩ = (2499810547071879 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1686 of the coefficient chain is the literal 2499810546992601/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1686 : ∀ (p : 1686 < 1732), cc20Eq115CoefficientQ ⟨1686, p⟩ = (2499810546992601 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1687 of the coefficient chain is the literal 4999621093830279/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1687 : ∀ (p : 1687 < 1732), cc20Eq115CoefficientQ ⟨1687, p⟩ = (4999621093830279 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1688 of the coefficient chain is the literal 9999242187353649/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1688 : ∀ (p : 1688 < 1732), cc20Eq115CoefficientQ ⟨1688, p⟩ = (9999242187353649 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1689 of the coefficient chain is the literal 499962109352933/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1689 : ∀ (p : 1689 < 1732), cc20Eq115CoefficientQ ⟨1689, p⟩ = (499962109352933 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1690 of the coefficient chain is the literal 1999848437353531/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1690 : ∀ (p : 1690 < 1732), cc20Eq115CoefficientQ ⟨1690, p⟩ = (1999848437353531 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1691 of the coefficient chain is the literal 9999242186486463/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1691 : ∀ (p : 1691 < 1732), cc20Eq115CoefficientQ ⟨1691, p⟩ = (9999242186486463 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1692 of the coefficient chain is the literal 4999621093104523/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1692 : ∀ (p : 1692 < 1732), cc20Eq115CoefficientQ ⟨1692, p⟩ = (4999621093104523 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1693 of the coefficient chain is the literal 9999242185939301/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1693 : ∀ (p : 1693 < 1732), cc20Eq115CoefficientQ ⟨1693, p⟩ = (9999242185939301 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1694 of the coefficient chain is the literal 4999621092837533/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1694 : ∀ (p : 1694 < 1732), cc20Eq115CoefficientQ ⟨1694, p⟩ = (4999621092837533 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1695 of the coefficient chain is the literal 1999848437084023/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1695 : ∀ (p : 1695 < 1732), cc20Eq115CoefficientQ ⟨1695, p⟩ = (1999848437084023 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1696 of the coefficient chain is the literal 9999242185172109/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1696 : ∀ (p : 1696 < 1732), cc20Eq115CoefficientQ ⟨1696, p⟩ = (9999242185172109 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1697 of the coefficient chain is the literal 1999848436985769/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1697 : ∀ (p : 1697 < 1732), cc20Eq115CoefficientQ ⟨1697, p⟩ = (1999848436985769 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1698 of the coefficient chain is the literal 1249905273086879/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1698 : ∀ (p : 1698 < 1732), cc20Eq115CoefficientQ ⟨1698, p⟩ = (1249905273086879 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1699 of the coefficient chain is the literal 624952636529103/ 625000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1699 : ∀ (p : 1699 < 1732), cc20Eq115CoefficientQ ⟨1699, p⟩ = (624952636529103 : ℚ) /  625000000000000 :=
  fun p => by rfl

/-- Branch 1700 of the coefficient chain is the literal 9999242184245359/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1700 : ∀ (p : 1700 < 1732), cc20Eq115CoefficientQ ⟨1700, p⟩ = (9999242184245359 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1701 of the coefficient chain is the literal 4999621092014833/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1701 : ∀ (p : 1701 < 1732), cc20Eq115CoefficientQ ⟨1701, p⟩ = (4999621092014833 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1702 of the coefficient chain is the literal 2499810545955029/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1702 : ∀ (p : 1702 < 1732), cc20Eq115CoefficientQ ⟨1702, p⟩ = (2499810545955029 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1703 of the coefficient chain is the literal 9999242183619161/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1703 : ∀ (p : 1703 < 1732), cc20Eq115CoefficientQ ⟨1703, p⟩ = (9999242183619161 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1704 of the coefficient chain is the literal 99992421834257/ 100000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1704 : ∀ (p : 1704 < 1732), cc20Eq115CoefficientQ ⟨1704, p⟩ = (99992421834257 : ℚ) /  100000000000000 :=
  fun p => by rfl

/-- Branch 1705 of the coefficient chain is the literal 9999242183238037/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1705 : ∀ (p : 1705 < 1732), cc20Eq115CoefficientQ ⟨1705, p⟩ = (9999242183238037 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1706 of the coefficient chain is the literal 4999621091528881/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1706 : ∀ (p : 1706 < 1732), cc20Eq115CoefficientQ ⟨1706, p⟩ = (4999621091528881 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1707 of the coefficient chain is the literal 1999848436576311/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1707 : ∀ (p : 1707 < 1732), cc20Eq115CoefficientQ ⟨1707, p⟩ = (1999848436576311 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1708 of the coefficient chain is the literal 1249905272839483/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1708 : ∀ (p : 1708 < 1732), cc20Eq115CoefficientQ ⟨1708, p⟩ = (1249905272839483 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1709 of the coefficient chain is the literal 9999242182556023/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1709 : ∀ (p : 1709 < 1732), cc20Eq115CoefficientQ ⟨1709, p⟩ = (9999242182556023 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1710 of the coefficient chain is the literal 999924218240631/ 1000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1710 : ∀ (p : 1710 < 1732), cc20Eq115CoefficientQ ⟨1710, p⟩ = (999924218240631 : ℚ) /  1000000000000000 :=
  fun p => by rfl

/-- Branch 1711 of the coefficient chain is the literal 4999621091128631/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1711 : ∀ (p : 1711 < 1732), cc20Eq115CoefficientQ ⟨1711, p⟩ = (4999621091128631 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1712 of the coefficient chain is the literal 4999621091058169/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1712 : ∀ (p : 1712 < 1732), cc20Eq115CoefficientQ ⟨1712, p⟩ = (4999621091058169 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1713 of the coefficient chain is the literal 2499810545496071/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1713 : ∀ (p : 1713 < 1732), cc20Eq115CoefficientQ ⟨1713, p⟩ = (2499810545496071 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1714 of the coefficient chain is the literal 9999242181858177/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1714 : ∀ (p : 1714 < 1732), cc20Eq115CoefficientQ ⟨1714, p⟩ = (9999242181858177 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1715 of the coefficient chain is the literal 1249905272717271/ 1250000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1715 : ∀ (p : 1715 < 1732), cc20Eq115CoefficientQ ⟨1715, p⟩ = (1249905272717271 : ℚ) /  1250000000000000 :=
  fun p => by rfl

/-- Branch 1716 of the coefficient chain is the literal 9999242181626109/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1716 : ∀ (p : 1716 < 1732), cc20Eq115CoefficientQ ⟨1716, p⟩ = (9999242181626109 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1717 of the coefficient chain is the literal 9999242181518807/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1717 : ∀ (p : 1717 < 1732), cc20Eq115CoefficientQ ⟨1717, p⟩ = (9999242181518807 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1718 of the coefficient chain is the literal 9999242181420163/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1718 : ∀ (p : 1718 < 1732), cc20Eq115CoefficientQ ⟨1718, p⟩ = (9999242181420163 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1719 of the coefficient chain is the literal 499962109066511/ 500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1719 : ∀ (p : 1719 < 1732), cc20Eq115CoefficientQ ⟨1719, p⟩ = (499962109066511 : ℚ) /  500000000000000 :=
  fun p => by rfl

/-- Branch 1720 of the coefficient chain is the literal 4999621090621933/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1720 : ∀ (p : 1720 < 1732), cc20Eq115CoefficientQ ⟨1720, p⟩ = (4999621090621933 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1721 of the coefficient chain is the literal 9999242181166159/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1721 : ∀ (p : 1721 < 1732), cc20Eq115CoefficientQ ⟨1721, p⟩ = (9999242181166159 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1722 of the coefficient chain is the literal 9999242181095609/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1722 : ∀ (p : 1722 < 1732), cc20Eq115CoefficientQ ⟨1722, p⟩ = (9999242181095609 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1723 of the coefficient chain is the literal 9999242181029819/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1723 : ∀ (p : 1723 < 1732), cc20Eq115CoefficientQ ⟨1723, p⟩ = (9999242181029819 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1724 of the coefficient chain is the literal 4999621090485569/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1724 : ∀ (p : 1724 < 1732), cc20Eq115CoefficientQ ⟨1724, p⟩ = (4999621090485569 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1725 of the coefficient chain is the literal 2499810545229999/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1725 : ∀ (p : 1725 < 1732), cc20Eq115CoefficientQ ⟨1725, p⟩ = (2499810545229999 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1726 of the coefficient chain is the literal 2499810545219323/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1726 : ∀ (p : 1726 < 1732), cc20Eq115CoefficientQ ⟨1726, p⟩ = (2499810545219323 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1727 of the coefficient chain is the literal 2499810545209867/ 2500000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1727 : ∀ (p : 1727 < 1732), cc20Eq115CoefficientQ ⟨1727, p⟩ = (2499810545209867 : ℚ) /  2500000000000000 :=
  fun p => by rfl

/-- Branch 1728 of the coefficient chain is the literal 4999621090403893/ 5000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1728 : ∀ (p : 1728 < 1732), cc20Eq115CoefficientQ ⟨1728, p⟩ = (4999621090403893 : ℚ) /  5000000000000000 :=
  fun p => by rfl

/-- Branch 1729 of the coefficient chain is the literal 9999242180787487/ 10000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1729 : ∀ (p : 1729 < 1732), cc20Eq115CoefficientQ ⟨1729, p⟩ = (9999242180787487 : ℚ) /  10000000000000000 :=
  fun p => by rfl

/-- Branch 1730 of the coefficient chain is the literal 1999848436153629/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1730 : ∀ (p : 1730 < 1732), cc20Eq115CoefficientQ ⟨1730, p⟩ = (1999848436153629 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Branch 1731 of the coefficient chain is the literal 1999848436151939/ 2000000000000000. -/
theorem cc20Eq115CoefficientQ_branch_1731 : ∀ (p : 1731 < 1732), cc20Eq115CoefficientQ ⟨1731, p⟩ = (1999848436151939 : ℚ) /  2000000000000000 :=
  fun p => by rfl

/-- Every branch of the equation-(115) coefficient chain is strictly
positive: 1732 rational literals, each one a positive fraction. -/
theorem cc20Eq115CoefficientQ_pos :
    ∀ n : Fin 1732, (0 : ℚ) < cc20Eq115CoefficientQ n := by
  intro n
  cases n with
  | mk k hk =>
      interval_cases k <;> (simp only [cc20Eq115CoefficientQ_branch_0, cc20Eq115CoefficientQ_branch_1, cc20Eq115CoefficientQ_branch_2, cc20Eq115CoefficientQ_branch_3, cc20Eq115CoefficientQ_branch_4, cc20Eq115CoefficientQ_branch_5, cc20Eq115CoefficientQ_branch_6, cc20Eq115CoefficientQ_branch_7, cc20Eq115CoefficientQ_branch_8, cc20Eq115CoefficientQ_branch_9, cc20Eq115CoefficientQ_branch_10, cc20Eq115CoefficientQ_branch_11, cc20Eq115CoefficientQ_branch_12, cc20Eq115CoefficientQ_branch_13, cc20Eq115CoefficientQ_branch_14, cc20Eq115CoefficientQ_branch_15, cc20Eq115CoefficientQ_branch_16, cc20Eq115CoefficientQ_branch_17, cc20Eq115CoefficientQ_branch_18, cc20Eq115CoefficientQ_branch_19, cc20Eq115CoefficientQ_branch_20, cc20Eq115CoefficientQ_branch_21, cc20Eq115CoefficientQ_branch_22, cc20Eq115CoefficientQ_branch_23, cc20Eq115CoefficientQ_branch_24, cc20Eq115CoefficientQ_branch_25, cc20Eq115CoefficientQ_branch_26, cc20Eq115CoefficientQ_branch_27, cc20Eq115CoefficientQ_branch_28, cc20Eq115CoefficientQ_branch_29, cc20Eq115CoefficientQ_branch_30, cc20Eq115CoefficientQ_branch_31, cc20Eq115CoefficientQ_branch_32, cc20Eq115CoefficientQ_branch_33, cc20Eq115CoefficientQ_branch_34, cc20Eq115CoefficientQ_branch_35, cc20Eq115CoefficientQ_branch_36, cc20Eq115CoefficientQ_branch_37, cc20Eq115CoefficientQ_branch_38, cc20Eq115CoefficientQ_branch_39, cc20Eq115CoefficientQ_branch_40, cc20Eq115CoefficientQ_branch_41, cc20Eq115CoefficientQ_branch_42, cc20Eq115CoefficientQ_branch_43, cc20Eq115CoefficientQ_branch_44, cc20Eq115CoefficientQ_branch_45, cc20Eq115CoefficientQ_branch_46, cc20Eq115CoefficientQ_branch_47, cc20Eq115CoefficientQ_branch_48, cc20Eq115CoefficientQ_branch_49, cc20Eq115CoefficientQ_branch_50, cc20Eq115CoefficientQ_branch_51, cc20Eq115CoefficientQ_branch_52, cc20Eq115CoefficientQ_branch_53, cc20Eq115CoefficientQ_branch_54, cc20Eq115CoefficientQ_branch_55, cc20Eq115CoefficientQ_branch_56, cc20Eq115CoefficientQ_branch_57, cc20Eq115CoefficientQ_branch_58, cc20Eq115CoefficientQ_branch_59, cc20Eq115CoefficientQ_branch_60, cc20Eq115CoefficientQ_branch_61, cc20Eq115CoefficientQ_branch_62, cc20Eq115CoefficientQ_branch_63, cc20Eq115CoefficientQ_branch_64, cc20Eq115CoefficientQ_branch_65, cc20Eq115CoefficientQ_branch_66, cc20Eq115CoefficientQ_branch_67, cc20Eq115CoefficientQ_branch_68, cc20Eq115CoefficientQ_branch_69, cc20Eq115CoefficientQ_branch_70, cc20Eq115CoefficientQ_branch_71, cc20Eq115CoefficientQ_branch_72, cc20Eq115CoefficientQ_branch_73, cc20Eq115CoefficientQ_branch_74, cc20Eq115CoefficientQ_branch_75, cc20Eq115CoefficientQ_branch_76, cc20Eq115CoefficientQ_branch_77, cc20Eq115CoefficientQ_branch_78, cc20Eq115CoefficientQ_branch_79, cc20Eq115CoefficientQ_branch_80, cc20Eq115CoefficientQ_branch_81, cc20Eq115CoefficientQ_branch_82, cc20Eq115CoefficientQ_branch_83, cc20Eq115CoefficientQ_branch_84, cc20Eq115CoefficientQ_branch_85, cc20Eq115CoefficientQ_branch_86, cc20Eq115CoefficientQ_branch_87, cc20Eq115CoefficientQ_branch_88, cc20Eq115CoefficientQ_branch_89, cc20Eq115CoefficientQ_branch_90, cc20Eq115CoefficientQ_branch_91, cc20Eq115CoefficientQ_branch_92, cc20Eq115CoefficientQ_branch_93, cc20Eq115CoefficientQ_branch_94, cc20Eq115CoefficientQ_branch_95, cc20Eq115CoefficientQ_branch_96, cc20Eq115CoefficientQ_branch_97, cc20Eq115CoefficientQ_branch_98, cc20Eq115CoefficientQ_branch_99, cc20Eq115CoefficientQ_branch_100, cc20Eq115CoefficientQ_branch_101, cc20Eq115CoefficientQ_branch_102, cc20Eq115CoefficientQ_branch_103, cc20Eq115CoefficientQ_branch_104, cc20Eq115CoefficientQ_branch_105, cc20Eq115CoefficientQ_branch_106, cc20Eq115CoefficientQ_branch_107, cc20Eq115CoefficientQ_branch_108, cc20Eq115CoefficientQ_branch_109, cc20Eq115CoefficientQ_branch_110, cc20Eq115CoefficientQ_branch_111, cc20Eq115CoefficientQ_branch_112, cc20Eq115CoefficientQ_branch_113, cc20Eq115CoefficientQ_branch_114, cc20Eq115CoefficientQ_branch_115, cc20Eq115CoefficientQ_branch_116, cc20Eq115CoefficientQ_branch_117, cc20Eq115CoefficientQ_branch_118, cc20Eq115CoefficientQ_branch_119, cc20Eq115CoefficientQ_branch_120, cc20Eq115CoefficientQ_branch_121, cc20Eq115CoefficientQ_branch_122, cc20Eq115CoefficientQ_branch_123, cc20Eq115CoefficientQ_branch_124, cc20Eq115CoefficientQ_branch_125, cc20Eq115CoefficientQ_branch_126, cc20Eq115CoefficientQ_branch_127, cc20Eq115CoefficientQ_branch_128, cc20Eq115CoefficientQ_branch_129, cc20Eq115CoefficientQ_branch_130, cc20Eq115CoefficientQ_branch_131, cc20Eq115CoefficientQ_branch_132, cc20Eq115CoefficientQ_branch_133, cc20Eq115CoefficientQ_branch_134, cc20Eq115CoefficientQ_branch_135, cc20Eq115CoefficientQ_branch_136, cc20Eq115CoefficientQ_branch_137, cc20Eq115CoefficientQ_branch_138, cc20Eq115CoefficientQ_branch_139, cc20Eq115CoefficientQ_branch_140, cc20Eq115CoefficientQ_branch_141, cc20Eq115CoefficientQ_branch_142, cc20Eq115CoefficientQ_branch_143, cc20Eq115CoefficientQ_branch_144, cc20Eq115CoefficientQ_branch_145, cc20Eq115CoefficientQ_branch_146, cc20Eq115CoefficientQ_branch_147, cc20Eq115CoefficientQ_branch_148, cc20Eq115CoefficientQ_branch_149, cc20Eq115CoefficientQ_branch_150, cc20Eq115CoefficientQ_branch_151, cc20Eq115CoefficientQ_branch_152, cc20Eq115CoefficientQ_branch_153, cc20Eq115CoefficientQ_branch_154, cc20Eq115CoefficientQ_branch_155, cc20Eq115CoefficientQ_branch_156, cc20Eq115CoefficientQ_branch_157, cc20Eq115CoefficientQ_branch_158, cc20Eq115CoefficientQ_branch_159, cc20Eq115CoefficientQ_branch_160, cc20Eq115CoefficientQ_branch_161, cc20Eq115CoefficientQ_branch_162, cc20Eq115CoefficientQ_branch_163, cc20Eq115CoefficientQ_branch_164, cc20Eq115CoefficientQ_branch_165, cc20Eq115CoefficientQ_branch_166, cc20Eq115CoefficientQ_branch_167, cc20Eq115CoefficientQ_branch_168, cc20Eq115CoefficientQ_branch_169, cc20Eq115CoefficientQ_branch_170, cc20Eq115CoefficientQ_branch_171, cc20Eq115CoefficientQ_branch_172, cc20Eq115CoefficientQ_branch_173, cc20Eq115CoefficientQ_branch_174, cc20Eq115CoefficientQ_branch_175, cc20Eq115CoefficientQ_branch_176, cc20Eq115CoefficientQ_branch_177, cc20Eq115CoefficientQ_branch_178, cc20Eq115CoefficientQ_branch_179, cc20Eq115CoefficientQ_branch_180, cc20Eq115CoefficientQ_branch_181, cc20Eq115CoefficientQ_branch_182, cc20Eq115CoefficientQ_branch_183, cc20Eq115CoefficientQ_branch_184, cc20Eq115CoefficientQ_branch_185, cc20Eq115CoefficientQ_branch_186, cc20Eq115CoefficientQ_branch_187, cc20Eq115CoefficientQ_branch_188, cc20Eq115CoefficientQ_branch_189, cc20Eq115CoefficientQ_branch_190, cc20Eq115CoefficientQ_branch_191, cc20Eq115CoefficientQ_branch_192, cc20Eq115CoefficientQ_branch_193, cc20Eq115CoefficientQ_branch_194, cc20Eq115CoefficientQ_branch_195, cc20Eq115CoefficientQ_branch_196, cc20Eq115CoefficientQ_branch_197, cc20Eq115CoefficientQ_branch_198, cc20Eq115CoefficientQ_branch_199, cc20Eq115CoefficientQ_branch_200, cc20Eq115CoefficientQ_branch_201, cc20Eq115CoefficientQ_branch_202, cc20Eq115CoefficientQ_branch_203, cc20Eq115CoefficientQ_branch_204, cc20Eq115CoefficientQ_branch_205, cc20Eq115CoefficientQ_branch_206, cc20Eq115CoefficientQ_branch_207, cc20Eq115CoefficientQ_branch_208, cc20Eq115CoefficientQ_branch_209, cc20Eq115CoefficientQ_branch_210, cc20Eq115CoefficientQ_branch_211, cc20Eq115CoefficientQ_branch_212, cc20Eq115CoefficientQ_branch_213, cc20Eq115CoefficientQ_branch_214, cc20Eq115CoefficientQ_branch_215, cc20Eq115CoefficientQ_branch_216, cc20Eq115CoefficientQ_branch_217, cc20Eq115CoefficientQ_branch_218, cc20Eq115CoefficientQ_branch_219, cc20Eq115CoefficientQ_branch_220, cc20Eq115CoefficientQ_branch_221, cc20Eq115CoefficientQ_branch_222, cc20Eq115CoefficientQ_branch_223, cc20Eq115CoefficientQ_branch_224, cc20Eq115CoefficientQ_branch_225, cc20Eq115CoefficientQ_branch_226, cc20Eq115CoefficientQ_branch_227, cc20Eq115CoefficientQ_branch_228, cc20Eq115CoefficientQ_branch_229, cc20Eq115CoefficientQ_branch_230, cc20Eq115CoefficientQ_branch_231, cc20Eq115CoefficientQ_branch_232, cc20Eq115CoefficientQ_branch_233, cc20Eq115CoefficientQ_branch_234, cc20Eq115CoefficientQ_branch_235, cc20Eq115CoefficientQ_branch_236, cc20Eq115CoefficientQ_branch_237, cc20Eq115CoefficientQ_branch_238, cc20Eq115CoefficientQ_branch_239, cc20Eq115CoefficientQ_branch_240, cc20Eq115CoefficientQ_branch_241, cc20Eq115CoefficientQ_branch_242, cc20Eq115CoefficientQ_branch_243, cc20Eq115CoefficientQ_branch_244, cc20Eq115CoefficientQ_branch_245, cc20Eq115CoefficientQ_branch_246, cc20Eq115CoefficientQ_branch_247, cc20Eq115CoefficientQ_branch_248, cc20Eq115CoefficientQ_branch_249, cc20Eq115CoefficientQ_branch_250, cc20Eq115CoefficientQ_branch_251, cc20Eq115CoefficientQ_branch_252, cc20Eq115CoefficientQ_branch_253, cc20Eq115CoefficientQ_branch_254, cc20Eq115CoefficientQ_branch_255, cc20Eq115CoefficientQ_branch_256, cc20Eq115CoefficientQ_branch_257, cc20Eq115CoefficientQ_branch_258, cc20Eq115CoefficientQ_branch_259, cc20Eq115CoefficientQ_branch_260, cc20Eq115CoefficientQ_branch_261, cc20Eq115CoefficientQ_branch_262, cc20Eq115CoefficientQ_branch_263, cc20Eq115CoefficientQ_branch_264, cc20Eq115CoefficientQ_branch_265, cc20Eq115CoefficientQ_branch_266, cc20Eq115CoefficientQ_branch_267, cc20Eq115CoefficientQ_branch_268, cc20Eq115CoefficientQ_branch_269, cc20Eq115CoefficientQ_branch_270, cc20Eq115CoefficientQ_branch_271, cc20Eq115CoefficientQ_branch_272, cc20Eq115CoefficientQ_branch_273, cc20Eq115CoefficientQ_branch_274, cc20Eq115CoefficientQ_branch_275, cc20Eq115CoefficientQ_branch_276, cc20Eq115CoefficientQ_branch_277, cc20Eq115CoefficientQ_branch_278, cc20Eq115CoefficientQ_branch_279, cc20Eq115CoefficientQ_branch_280, cc20Eq115CoefficientQ_branch_281, cc20Eq115CoefficientQ_branch_282, cc20Eq115CoefficientQ_branch_283, cc20Eq115CoefficientQ_branch_284, cc20Eq115CoefficientQ_branch_285, cc20Eq115CoefficientQ_branch_286, cc20Eq115CoefficientQ_branch_287, cc20Eq115CoefficientQ_branch_288, cc20Eq115CoefficientQ_branch_289, cc20Eq115CoefficientQ_branch_290, cc20Eq115CoefficientQ_branch_291, cc20Eq115CoefficientQ_branch_292, cc20Eq115CoefficientQ_branch_293, cc20Eq115CoefficientQ_branch_294, cc20Eq115CoefficientQ_branch_295, cc20Eq115CoefficientQ_branch_296, cc20Eq115CoefficientQ_branch_297, cc20Eq115CoefficientQ_branch_298, cc20Eq115CoefficientQ_branch_299, cc20Eq115CoefficientQ_branch_300, cc20Eq115CoefficientQ_branch_301, cc20Eq115CoefficientQ_branch_302, cc20Eq115CoefficientQ_branch_303, cc20Eq115CoefficientQ_branch_304, cc20Eq115CoefficientQ_branch_305, cc20Eq115CoefficientQ_branch_306, cc20Eq115CoefficientQ_branch_307, cc20Eq115CoefficientQ_branch_308, cc20Eq115CoefficientQ_branch_309, cc20Eq115CoefficientQ_branch_310, cc20Eq115CoefficientQ_branch_311, cc20Eq115CoefficientQ_branch_312, cc20Eq115CoefficientQ_branch_313, cc20Eq115CoefficientQ_branch_314, cc20Eq115CoefficientQ_branch_315, cc20Eq115CoefficientQ_branch_316, cc20Eq115CoefficientQ_branch_317, cc20Eq115CoefficientQ_branch_318, cc20Eq115CoefficientQ_branch_319, cc20Eq115CoefficientQ_branch_320, cc20Eq115CoefficientQ_branch_321, cc20Eq115CoefficientQ_branch_322, cc20Eq115CoefficientQ_branch_323, cc20Eq115CoefficientQ_branch_324, cc20Eq115CoefficientQ_branch_325, cc20Eq115CoefficientQ_branch_326, cc20Eq115CoefficientQ_branch_327, cc20Eq115CoefficientQ_branch_328, cc20Eq115CoefficientQ_branch_329, cc20Eq115CoefficientQ_branch_330, cc20Eq115CoefficientQ_branch_331, cc20Eq115CoefficientQ_branch_332, cc20Eq115CoefficientQ_branch_333, cc20Eq115CoefficientQ_branch_334, cc20Eq115CoefficientQ_branch_335, cc20Eq115CoefficientQ_branch_336, cc20Eq115CoefficientQ_branch_337, cc20Eq115CoefficientQ_branch_338, cc20Eq115CoefficientQ_branch_339, cc20Eq115CoefficientQ_branch_340, cc20Eq115CoefficientQ_branch_341, cc20Eq115CoefficientQ_branch_342, cc20Eq115CoefficientQ_branch_343, cc20Eq115CoefficientQ_branch_344, cc20Eq115CoefficientQ_branch_345, cc20Eq115CoefficientQ_branch_346, cc20Eq115CoefficientQ_branch_347, cc20Eq115CoefficientQ_branch_348, cc20Eq115CoefficientQ_branch_349, cc20Eq115CoefficientQ_branch_350, cc20Eq115CoefficientQ_branch_351, cc20Eq115CoefficientQ_branch_352, cc20Eq115CoefficientQ_branch_353, cc20Eq115CoefficientQ_branch_354, cc20Eq115CoefficientQ_branch_355, cc20Eq115CoefficientQ_branch_356, cc20Eq115CoefficientQ_branch_357, cc20Eq115CoefficientQ_branch_358, cc20Eq115CoefficientQ_branch_359, cc20Eq115CoefficientQ_branch_360, cc20Eq115CoefficientQ_branch_361, cc20Eq115CoefficientQ_branch_362, cc20Eq115CoefficientQ_branch_363, cc20Eq115CoefficientQ_branch_364, cc20Eq115CoefficientQ_branch_365, cc20Eq115CoefficientQ_branch_366, cc20Eq115CoefficientQ_branch_367, cc20Eq115CoefficientQ_branch_368, cc20Eq115CoefficientQ_branch_369, cc20Eq115CoefficientQ_branch_370, cc20Eq115CoefficientQ_branch_371, cc20Eq115CoefficientQ_branch_372, cc20Eq115CoefficientQ_branch_373, cc20Eq115CoefficientQ_branch_374, cc20Eq115CoefficientQ_branch_375, cc20Eq115CoefficientQ_branch_376, cc20Eq115CoefficientQ_branch_377, cc20Eq115CoefficientQ_branch_378, cc20Eq115CoefficientQ_branch_379, cc20Eq115CoefficientQ_branch_380, cc20Eq115CoefficientQ_branch_381, cc20Eq115CoefficientQ_branch_382, cc20Eq115CoefficientQ_branch_383, cc20Eq115CoefficientQ_branch_384, cc20Eq115CoefficientQ_branch_385, cc20Eq115CoefficientQ_branch_386, cc20Eq115CoefficientQ_branch_387, cc20Eq115CoefficientQ_branch_388, cc20Eq115CoefficientQ_branch_389, cc20Eq115CoefficientQ_branch_390, cc20Eq115CoefficientQ_branch_391, cc20Eq115CoefficientQ_branch_392, cc20Eq115CoefficientQ_branch_393, cc20Eq115CoefficientQ_branch_394, cc20Eq115CoefficientQ_branch_395, cc20Eq115CoefficientQ_branch_396, cc20Eq115CoefficientQ_branch_397, cc20Eq115CoefficientQ_branch_398, cc20Eq115CoefficientQ_branch_399, cc20Eq115CoefficientQ_branch_400, cc20Eq115CoefficientQ_branch_401, cc20Eq115CoefficientQ_branch_402, cc20Eq115CoefficientQ_branch_403, cc20Eq115CoefficientQ_branch_404, cc20Eq115CoefficientQ_branch_405, cc20Eq115CoefficientQ_branch_406, cc20Eq115CoefficientQ_branch_407, cc20Eq115CoefficientQ_branch_408, cc20Eq115CoefficientQ_branch_409, cc20Eq115CoefficientQ_branch_410, cc20Eq115CoefficientQ_branch_411, cc20Eq115CoefficientQ_branch_412, cc20Eq115CoefficientQ_branch_413, cc20Eq115CoefficientQ_branch_414, cc20Eq115CoefficientQ_branch_415, cc20Eq115CoefficientQ_branch_416, cc20Eq115CoefficientQ_branch_417, cc20Eq115CoefficientQ_branch_418, cc20Eq115CoefficientQ_branch_419, cc20Eq115CoefficientQ_branch_420, cc20Eq115CoefficientQ_branch_421, cc20Eq115CoefficientQ_branch_422, cc20Eq115CoefficientQ_branch_423, cc20Eq115CoefficientQ_branch_424, cc20Eq115CoefficientQ_branch_425, cc20Eq115CoefficientQ_branch_426, cc20Eq115CoefficientQ_branch_427, cc20Eq115CoefficientQ_branch_428, cc20Eq115CoefficientQ_branch_429, cc20Eq115CoefficientQ_branch_430, cc20Eq115CoefficientQ_branch_431, cc20Eq115CoefficientQ_branch_432, cc20Eq115CoefficientQ_branch_433, cc20Eq115CoefficientQ_branch_434, cc20Eq115CoefficientQ_branch_435, cc20Eq115CoefficientQ_branch_436, cc20Eq115CoefficientQ_branch_437, cc20Eq115CoefficientQ_branch_438, cc20Eq115CoefficientQ_branch_439, cc20Eq115CoefficientQ_branch_440, cc20Eq115CoefficientQ_branch_441, cc20Eq115CoefficientQ_branch_442, cc20Eq115CoefficientQ_branch_443, cc20Eq115CoefficientQ_branch_444, cc20Eq115CoefficientQ_branch_445, cc20Eq115CoefficientQ_branch_446, cc20Eq115CoefficientQ_branch_447, cc20Eq115CoefficientQ_branch_448, cc20Eq115CoefficientQ_branch_449, cc20Eq115CoefficientQ_branch_450, cc20Eq115CoefficientQ_branch_451, cc20Eq115CoefficientQ_branch_452, cc20Eq115CoefficientQ_branch_453, cc20Eq115CoefficientQ_branch_454, cc20Eq115CoefficientQ_branch_455, cc20Eq115CoefficientQ_branch_456, cc20Eq115CoefficientQ_branch_457, cc20Eq115CoefficientQ_branch_458, cc20Eq115CoefficientQ_branch_459, cc20Eq115CoefficientQ_branch_460, cc20Eq115CoefficientQ_branch_461, cc20Eq115CoefficientQ_branch_462, cc20Eq115CoefficientQ_branch_463, cc20Eq115CoefficientQ_branch_464, cc20Eq115CoefficientQ_branch_465, cc20Eq115CoefficientQ_branch_466, cc20Eq115CoefficientQ_branch_467, cc20Eq115CoefficientQ_branch_468, cc20Eq115CoefficientQ_branch_469, cc20Eq115CoefficientQ_branch_470, cc20Eq115CoefficientQ_branch_471, cc20Eq115CoefficientQ_branch_472, cc20Eq115CoefficientQ_branch_473, cc20Eq115CoefficientQ_branch_474, cc20Eq115CoefficientQ_branch_475, cc20Eq115CoefficientQ_branch_476, cc20Eq115CoefficientQ_branch_477, cc20Eq115CoefficientQ_branch_478, cc20Eq115CoefficientQ_branch_479, cc20Eq115CoefficientQ_branch_480, cc20Eq115CoefficientQ_branch_481, cc20Eq115CoefficientQ_branch_482, cc20Eq115CoefficientQ_branch_483, cc20Eq115CoefficientQ_branch_484, cc20Eq115CoefficientQ_branch_485, cc20Eq115CoefficientQ_branch_486, cc20Eq115CoefficientQ_branch_487, cc20Eq115CoefficientQ_branch_488, cc20Eq115CoefficientQ_branch_489, cc20Eq115CoefficientQ_branch_490, cc20Eq115CoefficientQ_branch_491, cc20Eq115CoefficientQ_branch_492, cc20Eq115CoefficientQ_branch_493, cc20Eq115CoefficientQ_branch_494, cc20Eq115CoefficientQ_branch_495, cc20Eq115CoefficientQ_branch_496, cc20Eq115CoefficientQ_branch_497, cc20Eq115CoefficientQ_branch_498, cc20Eq115CoefficientQ_branch_499, cc20Eq115CoefficientQ_branch_500, cc20Eq115CoefficientQ_branch_501, cc20Eq115CoefficientQ_branch_502, cc20Eq115CoefficientQ_branch_503, cc20Eq115CoefficientQ_branch_504, cc20Eq115CoefficientQ_branch_505, cc20Eq115CoefficientQ_branch_506, cc20Eq115CoefficientQ_branch_507, cc20Eq115CoefficientQ_branch_508, cc20Eq115CoefficientQ_branch_509, cc20Eq115CoefficientQ_branch_510, cc20Eq115CoefficientQ_branch_511, cc20Eq115CoefficientQ_branch_512, cc20Eq115CoefficientQ_branch_513, cc20Eq115CoefficientQ_branch_514, cc20Eq115CoefficientQ_branch_515, cc20Eq115CoefficientQ_branch_516, cc20Eq115CoefficientQ_branch_517, cc20Eq115CoefficientQ_branch_518, cc20Eq115CoefficientQ_branch_519, cc20Eq115CoefficientQ_branch_520, cc20Eq115CoefficientQ_branch_521, cc20Eq115CoefficientQ_branch_522, cc20Eq115CoefficientQ_branch_523, cc20Eq115CoefficientQ_branch_524, cc20Eq115CoefficientQ_branch_525, cc20Eq115CoefficientQ_branch_526, cc20Eq115CoefficientQ_branch_527, cc20Eq115CoefficientQ_branch_528, cc20Eq115CoefficientQ_branch_529, cc20Eq115CoefficientQ_branch_530, cc20Eq115CoefficientQ_branch_531, cc20Eq115CoefficientQ_branch_532, cc20Eq115CoefficientQ_branch_533, cc20Eq115CoefficientQ_branch_534, cc20Eq115CoefficientQ_branch_535, cc20Eq115CoefficientQ_branch_536, cc20Eq115CoefficientQ_branch_537, cc20Eq115CoefficientQ_branch_538, cc20Eq115CoefficientQ_branch_539, cc20Eq115CoefficientQ_branch_540, cc20Eq115CoefficientQ_branch_541, cc20Eq115CoefficientQ_branch_542, cc20Eq115CoefficientQ_branch_543, cc20Eq115CoefficientQ_branch_544, cc20Eq115CoefficientQ_branch_545, cc20Eq115CoefficientQ_branch_546, cc20Eq115CoefficientQ_branch_547, cc20Eq115CoefficientQ_branch_548, cc20Eq115CoefficientQ_branch_549, cc20Eq115CoefficientQ_branch_550, cc20Eq115CoefficientQ_branch_551, cc20Eq115CoefficientQ_branch_552, cc20Eq115CoefficientQ_branch_553, cc20Eq115CoefficientQ_branch_554, cc20Eq115CoefficientQ_branch_555, cc20Eq115CoefficientQ_branch_556, cc20Eq115CoefficientQ_branch_557, cc20Eq115CoefficientQ_branch_558, cc20Eq115CoefficientQ_branch_559, cc20Eq115CoefficientQ_branch_560, cc20Eq115CoefficientQ_branch_561, cc20Eq115CoefficientQ_branch_562, cc20Eq115CoefficientQ_branch_563, cc20Eq115CoefficientQ_branch_564, cc20Eq115CoefficientQ_branch_565, cc20Eq115CoefficientQ_branch_566, cc20Eq115CoefficientQ_branch_567, cc20Eq115CoefficientQ_branch_568, cc20Eq115CoefficientQ_branch_569, cc20Eq115CoefficientQ_branch_570, cc20Eq115CoefficientQ_branch_571, cc20Eq115CoefficientQ_branch_572, cc20Eq115CoefficientQ_branch_573, cc20Eq115CoefficientQ_branch_574, cc20Eq115CoefficientQ_branch_575, cc20Eq115CoefficientQ_branch_576, cc20Eq115CoefficientQ_branch_577, cc20Eq115CoefficientQ_branch_578, cc20Eq115CoefficientQ_branch_579, cc20Eq115CoefficientQ_branch_580, cc20Eq115CoefficientQ_branch_581, cc20Eq115CoefficientQ_branch_582, cc20Eq115CoefficientQ_branch_583, cc20Eq115CoefficientQ_branch_584, cc20Eq115CoefficientQ_branch_585, cc20Eq115CoefficientQ_branch_586, cc20Eq115CoefficientQ_branch_587, cc20Eq115CoefficientQ_branch_588, cc20Eq115CoefficientQ_branch_589, cc20Eq115CoefficientQ_branch_590, cc20Eq115CoefficientQ_branch_591, cc20Eq115CoefficientQ_branch_592, cc20Eq115CoefficientQ_branch_593, cc20Eq115CoefficientQ_branch_594, cc20Eq115CoefficientQ_branch_595, cc20Eq115CoefficientQ_branch_596, cc20Eq115CoefficientQ_branch_597, cc20Eq115CoefficientQ_branch_598, cc20Eq115CoefficientQ_branch_599, cc20Eq115CoefficientQ_branch_600, cc20Eq115CoefficientQ_branch_601, cc20Eq115CoefficientQ_branch_602, cc20Eq115CoefficientQ_branch_603, cc20Eq115CoefficientQ_branch_604, cc20Eq115CoefficientQ_branch_605, cc20Eq115CoefficientQ_branch_606, cc20Eq115CoefficientQ_branch_607, cc20Eq115CoefficientQ_branch_608, cc20Eq115CoefficientQ_branch_609, cc20Eq115CoefficientQ_branch_610, cc20Eq115CoefficientQ_branch_611, cc20Eq115CoefficientQ_branch_612, cc20Eq115CoefficientQ_branch_613, cc20Eq115CoefficientQ_branch_614, cc20Eq115CoefficientQ_branch_615, cc20Eq115CoefficientQ_branch_616, cc20Eq115CoefficientQ_branch_617, cc20Eq115CoefficientQ_branch_618, cc20Eq115CoefficientQ_branch_619, cc20Eq115CoefficientQ_branch_620, cc20Eq115CoefficientQ_branch_621, cc20Eq115CoefficientQ_branch_622, cc20Eq115CoefficientQ_branch_623, cc20Eq115CoefficientQ_branch_624, cc20Eq115CoefficientQ_branch_625, cc20Eq115CoefficientQ_branch_626, cc20Eq115CoefficientQ_branch_627, cc20Eq115CoefficientQ_branch_628, cc20Eq115CoefficientQ_branch_629, cc20Eq115CoefficientQ_branch_630, cc20Eq115CoefficientQ_branch_631, cc20Eq115CoefficientQ_branch_632, cc20Eq115CoefficientQ_branch_633, cc20Eq115CoefficientQ_branch_634, cc20Eq115CoefficientQ_branch_635, cc20Eq115CoefficientQ_branch_636, cc20Eq115CoefficientQ_branch_637, cc20Eq115CoefficientQ_branch_638, cc20Eq115CoefficientQ_branch_639, cc20Eq115CoefficientQ_branch_640, cc20Eq115CoefficientQ_branch_641, cc20Eq115CoefficientQ_branch_642, cc20Eq115CoefficientQ_branch_643, cc20Eq115CoefficientQ_branch_644, cc20Eq115CoefficientQ_branch_645, cc20Eq115CoefficientQ_branch_646, cc20Eq115CoefficientQ_branch_647, cc20Eq115CoefficientQ_branch_648, cc20Eq115CoefficientQ_branch_649, cc20Eq115CoefficientQ_branch_650, cc20Eq115CoefficientQ_branch_651, cc20Eq115CoefficientQ_branch_652, cc20Eq115CoefficientQ_branch_653, cc20Eq115CoefficientQ_branch_654, cc20Eq115CoefficientQ_branch_655, cc20Eq115CoefficientQ_branch_656, cc20Eq115CoefficientQ_branch_657, cc20Eq115CoefficientQ_branch_658, cc20Eq115CoefficientQ_branch_659, cc20Eq115CoefficientQ_branch_660, cc20Eq115CoefficientQ_branch_661, cc20Eq115CoefficientQ_branch_662, cc20Eq115CoefficientQ_branch_663, cc20Eq115CoefficientQ_branch_664, cc20Eq115CoefficientQ_branch_665, cc20Eq115CoefficientQ_branch_666, cc20Eq115CoefficientQ_branch_667, cc20Eq115CoefficientQ_branch_668, cc20Eq115CoefficientQ_branch_669, cc20Eq115CoefficientQ_branch_670, cc20Eq115CoefficientQ_branch_671, cc20Eq115CoefficientQ_branch_672, cc20Eq115CoefficientQ_branch_673, cc20Eq115CoefficientQ_branch_674, cc20Eq115CoefficientQ_branch_675, cc20Eq115CoefficientQ_branch_676, cc20Eq115CoefficientQ_branch_677, cc20Eq115CoefficientQ_branch_678, cc20Eq115CoefficientQ_branch_679, cc20Eq115CoefficientQ_branch_680, cc20Eq115CoefficientQ_branch_681, cc20Eq115CoefficientQ_branch_682, cc20Eq115CoefficientQ_branch_683, cc20Eq115CoefficientQ_branch_684, cc20Eq115CoefficientQ_branch_685, cc20Eq115CoefficientQ_branch_686, cc20Eq115CoefficientQ_branch_687, cc20Eq115CoefficientQ_branch_688, cc20Eq115CoefficientQ_branch_689, cc20Eq115CoefficientQ_branch_690, cc20Eq115CoefficientQ_branch_691, cc20Eq115CoefficientQ_branch_692, cc20Eq115CoefficientQ_branch_693, cc20Eq115CoefficientQ_branch_694, cc20Eq115CoefficientQ_branch_695, cc20Eq115CoefficientQ_branch_696, cc20Eq115CoefficientQ_branch_697, cc20Eq115CoefficientQ_branch_698, cc20Eq115CoefficientQ_branch_699, cc20Eq115CoefficientQ_branch_700, cc20Eq115CoefficientQ_branch_701, cc20Eq115CoefficientQ_branch_702, cc20Eq115CoefficientQ_branch_703, cc20Eq115CoefficientQ_branch_704, cc20Eq115CoefficientQ_branch_705, cc20Eq115CoefficientQ_branch_706, cc20Eq115CoefficientQ_branch_707, cc20Eq115CoefficientQ_branch_708, cc20Eq115CoefficientQ_branch_709, cc20Eq115CoefficientQ_branch_710, cc20Eq115CoefficientQ_branch_711, cc20Eq115CoefficientQ_branch_712, cc20Eq115CoefficientQ_branch_713, cc20Eq115CoefficientQ_branch_714, cc20Eq115CoefficientQ_branch_715, cc20Eq115CoefficientQ_branch_716, cc20Eq115CoefficientQ_branch_717, cc20Eq115CoefficientQ_branch_718, cc20Eq115CoefficientQ_branch_719, cc20Eq115CoefficientQ_branch_720, cc20Eq115CoefficientQ_branch_721, cc20Eq115CoefficientQ_branch_722, cc20Eq115CoefficientQ_branch_723, cc20Eq115CoefficientQ_branch_724, cc20Eq115CoefficientQ_branch_725, cc20Eq115CoefficientQ_branch_726, cc20Eq115CoefficientQ_branch_727, cc20Eq115CoefficientQ_branch_728, cc20Eq115CoefficientQ_branch_729, cc20Eq115CoefficientQ_branch_730, cc20Eq115CoefficientQ_branch_731, cc20Eq115CoefficientQ_branch_732, cc20Eq115CoefficientQ_branch_733, cc20Eq115CoefficientQ_branch_734, cc20Eq115CoefficientQ_branch_735, cc20Eq115CoefficientQ_branch_736, cc20Eq115CoefficientQ_branch_737, cc20Eq115CoefficientQ_branch_738, cc20Eq115CoefficientQ_branch_739, cc20Eq115CoefficientQ_branch_740, cc20Eq115CoefficientQ_branch_741, cc20Eq115CoefficientQ_branch_742, cc20Eq115CoefficientQ_branch_743, cc20Eq115CoefficientQ_branch_744, cc20Eq115CoefficientQ_branch_745, cc20Eq115CoefficientQ_branch_746, cc20Eq115CoefficientQ_branch_747, cc20Eq115CoefficientQ_branch_748, cc20Eq115CoefficientQ_branch_749, cc20Eq115CoefficientQ_branch_750, cc20Eq115CoefficientQ_branch_751, cc20Eq115CoefficientQ_branch_752, cc20Eq115CoefficientQ_branch_753, cc20Eq115CoefficientQ_branch_754, cc20Eq115CoefficientQ_branch_755, cc20Eq115CoefficientQ_branch_756, cc20Eq115CoefficientQ_branch_757, cc20Eq115CoefficientQ_branch_758, cc20Eq115CoefficientQ_branch_759, cc20Eq115CoefficientQ_branch_760, cc20Eq115CoefficientQ_branch_761, cc20Eq115CoefficientQ_branch_762, cc20Eq115CoefficientQ_branch_763, cc20Eq115CoefficientQ_branch_764, cc20Eq115CoefficientQ_branch_765, cc20Eq115CoefficientQ_branch_766, cc20Eq115CoefficientQ_branch_767, cc20Eq115CoefficientQ_branch_768, cc20Eq115CoefficientQ_branch_769, cc20Eq115CoefficientQ_branch_770, cc20Eq115CoefficientQ_branch_771, cc20Eq115CoefficientQ_branch_772, cc20Eq115CoefficientQ_branch_773, cc20Eq115CoefficientQ_branch_774, cc20Eq115CoefficientQ_branch_775, cc20Eq115CoefficientQ_branch_776, cc20Eq115CoefficientQ_branch_777, cc20Eq115CoefficientQ_branch_778, cc20Eq115CoefficientQ_branch_779, cc20Eq115CoefficientQ_branch_780, cc20Eq115CoefficientQ_branch_781, cc20Eq115CoefficientQ_branch_782, cc20Eq115CoefficientQ_branch_783, cc20Eq115CoefficientQ_branch_784, cc20Eq115CoefficientQ_branch_785, cc20Eq115CoefficientQ_branch_786, cc20Eq115CoefficientQ_branch_787, cc20Eq115CoefficientQ_branch_788, cc20Eq115CoefficientQ_branch_789, cc20Eq115CoefficientQ_branch_790, cc20Eq115CoefficientQ_branch_791, cc20Eq115CoefficientQ_branch_792, cc20Eq115CoefficientQ_branch_793, cc20Eq115CoefficientQ_branch_794, cc20Eq115CoefficientQ_branch_795, cc20Eq115CoefficientQ_branch_796, cc20Eq115CoefficientQ_branch_797, cc20Eq115CoefficientQ_branch_798, cc20Eq115CoefficientQ_branch_799, cc20Eq115CoefficientQ_branch_800, cc20Eq115CoefficientQ_branch_801, cc20Eq115CoefficientQ_branch_802, cc20Eq115CoefficientQ_branch_803, cc20Eq115CoefficientQ_branch_804, cc20Eq115CoefficientQ_branch_805, cc20Eq115CoefficientQ_branch_806, cc20Eq115CoefficientQ_branch_807, cc20Eq115CoefficientQ_branch_808, cc20Eq115CoefficientQ_branch_809, cc20Eq115CoefficientQ_branch_810, cc20Eq115CoefficientQ_branch_811, cc20Eq115CoefficientQ_branch_812, cc20Eq115CoefficientQ_branch_813, cc20Eq115CoefficientQ_branch_814, cc20Eq115CoefficientQ_branch_815, cc20Eq115CoefficientQ_branch_816, cc20Eq115CoefficientQ_branch_817, cc20Eq115CoefficientQ_branch_818, cc20Eq115CoefficientQ_branch_819, cc20Eq115CoefficientQ_branch_820, cc20Eq115CoefficientQ_branch_821, cc20Eq115CoefficientQ_branch_822, cc20Eq115CoefficientQ_branch_823, cc20Eq115CoefficientQ_branch_824, cc20Eq115CoefficientQ_branch_825, cc20Eq115CoefficientQ_branch_826, cc20Eq115CoefficientQ_branch_827, cc20Eq115CoefficientQ_branch_828, cc20Eq115CoefficientQ_branch_829, cc20Eq115CoefficientQ_branch_830, cc20Eq115CoefficientQ_branch_831, cc20Eq115CoefficientQ_branch_832, cc20Eq115CoefficientQ_branch_833, cc20Eq115CoefficientQ_branch_834, cc20Eq115CoefficientQ_branch_835, cc20Eq115CoefficientQ_branch_836, cc20Eq115CoefficientQ_branch_837, cc20Eq115CoefficientQ_branch_838, cc20Eq115CoefficientQ_branch_839, cc20Eq115CoefficientQ_branch_840, cc20Eq115CoefficientQ_branch_841, cc20Eq115CoefficientQ_branch_842, cc20Eq115CoefficientQ_branch_843, cc20Eq115CoefficientQ_branch_844, cc20Eq115CoefficientQ_branch_845, cc20Eq115CoefficientQ_branch_846, cc20Eq115CoefficientQ_branch_847, cc20Eq115CoefficientQ_branch_848, cc20Eq115CoefficientQ_branch_849, cc20Eq115CoefficientQ_branch_850, cc20Eq115CoefficientQ_branch_851, cc20Eq115CoefficientQ_branch_852, cc20Eq115CoefficientQ_branch_853, cc20Eq115CoefficientQ_branch_854, cc20Eq115CoefficientQ_branch_855, cc20Eq115CoefficientQ_branch_856, cc20Eq115CoefficientQ_branch_857, cc20Eq115CoefficientQ_branch_858, cc20Eq115CoefficientQ_branch_859, cc20Eq115CoefficientQ_branch_860, cc20Eq115CoefficientQ_branch_861, cc20Eq115CoefficientQ_branch_862, cc20Eq115CoefficientQ_branch_863, cc20Eq115CoefficientQ_branch_864, cc20Eq115CoefficientQ_branch_865, cc20Eq115CoefficientQ_branch_866, cc20Eq115CoefficientQ_branch_867, cc20Eq115CoefficientQ_branch_868, cc20Eq115CoefficientQ_branch_869, cc20Eq115CoefficientQ_branch_870, cc20Eq115CoefficientQ_branch_871, cc20Eq115CoefficientQ_branch_872, cc20Eq115CoefficientQ_branch_873, cc20Eq115CoefficientQ_branch_874, cc20Eq115CoefficientQ_branch_875, cc20Eq115CoefficientQ_branch_876, cc20Eq115CoefficientQ_branch_877, cc20Eq115CoefficientQ_branch_878, cc20Eq115CoefficientQ_branch_879, cc20Eq115CoefficientQ_branch_880, cc20Eq115CoefficientQ_branch_881, cc20Eq115CoefficientQ_branch_882, cc20Eq115CoefficientQ_branch_883, cc20Eq115CoefficientQ_branch_884, cc20Eq115CoefficientQ_branch_885, cc20Eq115CoefficientQ_branch_886, cc20Eq115CoefficientQ_branch_887, cc20Eq115CoefficientQ_branch_888, cc20Eq115CoefficientQ_branch_889, cc20Eq115CoefficientQ_branch_890, cc20Eq115CoefficientQ_branch_891, cc20Eq115CoefficientQ_branch_892, cc20Eq115CoefficientQ_branch_893, cc20Eq115CoefficientQ_branch_894, cc20Eq115CoefficientQ_branch_895, cc20Eq115CoefficientQ_branch_896, cc20Eq115CoefficientQ_branch_897, cc20Eq115CoefficientQ_branch_898, cc20Eq115CoefficientQ_branch_899, cc20Eq115CoefficientQ_branch_900, cc20Eq115CoefficientQ_branch_901, cc20Eq115CoefficientQ_branch_902, cc20Eq115CoefficientQ_branch_903, cc20Eq115CoefficientQ_branch_904, cc20Eq115CoefficientQ_branch_905, cc20Eq115CoefficientQ_branch_906, cc20Eq115CoefficientQ_branch_907, cc20Eq115CoefficientQ_branch_908, cc20Eq115CoefficientQ_branch_909, cc20Eq115CoefficientQ_branch_910, cc20Eq115CoefficientQ_branch_911, cc20Eq115CoefficientQ_branch_912, cc20Eq115CoefficientQ_branch_913, cc20Eq115CoefficientQ_branch_914, cc20Eq115CoefficientQ_branch_915, cc20Eq115CoefficientQ_branch_916, cc20Eq115CoefficientQ_branch_917, cc20Eq115CoefficientQ_branch_918, cc20Eq115CoefficientQ_branch_919, cc20Eq115CoefficientQ_branch_920, cc20Eq115CoefficientQ_branch_921, cc20Eq115CoefficientQ_branch_922, cc20Eq115CoefficientQ_branch_923, cc20Eq115CoefficientQ_branch_924, cc20Eq115CoefficientQ_branch_925, cc20Eq115CoefficientQ_branch_926, cc20Eq115CoefficientQ_branch_927, cc20Eq115CoefficientQ_branch_928, cc20Eq115CoefficientQ_branch_929, cc20Eq115CoefficientQ_branch_930, cc20Eq115CoefficientQ_branch_931, cc20Eq115CoefficientQ_branch_932, cc20Eq115CoefficientQ_branch_933, cc20Eq115CoefficientQ_branch_934, cc20Eq115CoefficientQ_branch_935, cc20Eq115CoefficientQ_branch_936, cc20Eq115CoefficientQ_branch_937, cc20Eq115CoefficientQ_branch_938, cc20Eq115CoefficientQ_branch_939, cc20Eq115CoefficientQ_branch_940, cc20Eq115CoefficientQ_branch_941, cc20Eq115CoefficientQ_branch_942, cc20Eq115CoefficientQ_branch_943, cc20Eq115CoefficientQ_branch_944, cc20Eq115CoefficientQ_branch_945, cc20Eq115CoefficientQ_branch_946, cc20Eq115CoefficientQ_branch_947, cc20Eq115CoefficientQ_branch_948, cc20Eq115CoefficientQ_branch_949, cc20Eq115CoefficientQ_branch_950, cc20Eq115CoefficientQ_branch_951, cc20Eq115CoefficientQ_branch_952, cc20Eq115CoefficientQ_branch_953, cc20Eq115CoefficientQ_branch_954, cc20Eq115CoefficientQ_branch_955, cc20Eq115CoefficientQ_branch_956, cc20Eq115CoefficientQ_branch_957, cc20Eq115CoefficientQ_branch_958, cc20Eq115CoefficientQ_branch_959, cc20Eq115CoefficientQ_branch_960, cc20Eq115CoefficientQ_branch_961, cc20Eq115CoefficientQ_branch_962, cc20Eq115CoefficientQ_branch_963, cc20Eq115CoefficientQ_branch_964, cc20Eq115CoefficientQ_branch_965, cc20Eq115CoefficientQ_branch_966, cc20Eq115CoefficientQ_branch_967, cc20Eq115CoefficientQ_branch_968, cc20Eq115CoefficientQ_branch_969, cc20Eq115CoefficientQ_branch_970, cc20Eq115CoefficientQ_branch_971, cc20Eq115CoefficientQ_branch_972, cc20Eq115CoefficientQ_branch_973, cc20Eq115CoefficientQ_branch_974, cc20Eq115CoefficientQ_branch_975, cc20Eq115CoefficientQ_branch_976, cc20Eq115CoefficientQ_branch_977, cc20Eq115CoefficientQ_branch_978, cc20Eq115CoefficientQ_branch_979, cc20Eq115CoefficientQ_branch_980, cc20Eq115CoefficientQ_branch_981, cc20Eq115CoefficientQ_branch_982, cc20Eq115CoefficientQ_branch_983, cc20Eq115CoefficientQ_branch_984, cc20Eq115CoefficientQ_branch_985, cc20Eq115CoefficientQ_branch_986, cc20Eq115CoefficientQ_branch_987, cc20Eq115CoefficientQ_branch_988, cc20Eq115CoefficientQ_branch_989, cc20Eq115CoefficientQ_branch_990, cc20Eq115CoefficientQ_branch_991, cc20Eq115CoefficientQ_branch_992, cc20Eq115CoefficientQ_branch_993, cc20Eq115CoefficientQ_branch_994, cc20Eq115CoefficientQ_branch_995, cc20Eq115CoefficientQ_branch_996, cc20Eq115CoefficientQ_branch_997, cc20Eq115CoefficientQ_branch_998, cc20Eq115CoefficientQ_branch_999, cc20Eq115CoefficientQ_branch_1000, cc20Eq115CoefficientQ_branch_1001, cc20Eq115CoefficientQ_branch_1002, cc20Eq115CoefficientQ_branch_1003, cc20Eq115CoefficientQ_branch_1004, cc20Eq115CoefficientQ_branch_1005, cc20Eq115CoefficientQ_branch_1006, cc20Eq115CoefficientQ_branch_1007, cc20Eq115CoefficientQ_branch_1008, cc20Eq115CoefficientQ_branch_1009, cc20Eq115CoefficientQ_branch_1010, cc20Eq115CoefficientQ_branch_1011, cc20Eq115CoefficientQ_branch_1012, cc20Eq115CoefficientQ_branch_1013, cc20Eq115CoefficientQ_branch_1014, cc20Eq115CoefficientQ_branch_1015, cc20Eq115CoefficientQ_branch_1016, cc20Eq115CoefficientQ_branch_1017, cc20Eq115CoefficientQ_branch_1018, cc20Eq115CoefficientQ_branch_1019, cc20Eq115CoefficientQ_branch_1020, cc20Eq115CoefficientQ_branch_1021, cc20Eq115CoefficientQ_branch_1022, cc20Eq115CoefficientQ_branch_1023, cc20Eq115CoefficientQ_branch_1024, cc20Eq115CoefficientQ_branch_1025, cc20Eq115CoefficientQ_branch_1026, cc20Eq115CoefficientQ_branch_1027, cc20Eq115CoefficientQ_branch_1028, cc20Eq115CoefficientQ_branch_1029, cc20Eq115CoefficientQ_branch_1030, cc20Eq115CoefficientQ_branch_1031, cc20Eq115CoefficientQ_branch_1032, cc20Eq115CoefficientQ_branch_1033, cc20Eq115CoefficientQ_branch_1034, cc20Eq115CoefficientQ_branch_1035, cc20Eq115CoefficientQ_branch_1036, cc20Eq115CoefficientQ_branch_1037, cc20Eq115CoefficientQ_branch_1038, cc20Eq115CoefficientQ_branch_1039, cc20Eq115CoefficientQ_branch_1040, cc20Eq115CoefficientQ_branch_1041, cc20Eq115CoefficientQ_branch_1042, cc20Eq115CoefficientQ_branch_1043, cc20Eq115CoefficientQ_branch_1044, cc20Eq115CoefficientQ_branch_1045, cc20Eq115CoefficientQ_branch_1046, cc20Eq115CoefficientQ_branch_1047, cc20Eq115CoefficientQ_branch_1048, cc20Eq115CoefficientQ_branch_1049, cc20Eq115CoefficientQ_branch_1050, cc20Eq115CoefficientQ_branch_1051, cc20Eq115CoefficientQ_branch_1052, cc20Eq115CoefficientQ_branch_1053, cc20Eq115CoefficientQ_branch_1054, cc20Eq115CoefficientQ_branch_1055, cc20Eq115CoefficientQ_branch_1056, cc20Eq115CoefficientQ_branch_1057, cc20Eq115CoefficientQ_branch_1058, cc20Eq115CoefficientQ_branch_1059, cc20Eq115CoefficientQ_branch_1060, cc20Eq115CoefficientQ_branch_1061, cc20Eq115CoefficientQ_branch_1062, cc20Eq115CoefficientQ_branch_1063, cc20Eq115CoefficientQ_branch_1064, cc20Eq115CoefficientQ_branch_1065, cc20Eq115CoefficientQ_branch_1066, cc20Eq115CoefficientQ_branch_1067, cc20Eq115CoefficientQ_branch_1068, cc20Eq115CoefficientQ_branch_1069, cc20Eq115CoefficientQ_branch_1070, cc20Eq115CoefficientQ_branch_1071, cc20Eq115CoefficientQ_branch_1072, cc20Eq115CoefficientQ_branch_1073, cc20Eq115CoefficientQ_branch_1074, cc20Eq115CoefficientQ_branch_1075, cc20Eq115CoefficientQ_branch_1076, cc20Eq115CoefficientQ_branch_1077, cc20Eq115CoefficientQ_branch_1078, cc20Eq115CoefficientQ_branch_1079, cc20Eq115CoefficientQ_branch_1080, cc20Eq115CoefficientQ_branch_1081, cc20Eq115CoefficientQ_branch_1082, cc20Eq115CoefficientQ_branch_1083, cc20Eq115CoefficientQ_branch_1084, cc20Eq115CoefficientQ_branch_1085, cc20Eq115CoefficientQ_branch_1086, cc20Eq115CoefficientQ_branch_1087, cc20Eq115CoefficientQ_branch_1088, cc20Eq115CoefficientQ_branch_1089, cc20Eq115CoefficientQ_branch_1090, cc20Eq115CoefficientQ_branch_1091, cc20Eq115CoefficientQ_branch_1092, cc20Eq115CoefficientQ_branch_1093, cc20Eq115CoefficientQ_branch_1094, cc20Eq115CoefficientQ_branch_1095, cc20Eq115CoefficientQ_branch_1096, cc20Eq115CoefficientQ_branch_1097, cc20Eq115CoefficientQ_branch_1098, cc20Eq115CoefficientQ_branch_1099, cc20Eq115CoefficientQ_branch_1100, cc20Eq115CoefficientQ_branch_1101, cc20Eq115CoefficientQ_branch_1102, cc20Eq115CoefficientQ_branch_1103, cc20Eq115CoefficientQ_branch_1104, cc20Eq115CoefficientQ_branch_1105, cc20Eq115CoefficientQ_branch_1106, cc20Eq115CoefficientQ_branch_1107, cc20Eq115CoefficientQ_branch_1108, cc20Eq115CoefficientQ_branch_1109, cc20Eq115CoefficientQ_branch_1110, cc20Eq115CoefficientQ_branch_1111, cc20Eq115CoefficientQ_branch_1112, cc20Eq115CoefficientQ_branch_1113, cc20Eq115CoefficientQ_branch_1114, cc20Eq115CoefficientQ_branch_1115, cc20Eq115CoefficientQ_branch_1116, cc20Eq115CoefficientQ_branch_1117, cc20Eq115CoefficientQ_branch_1118, cc20Eq115CoefficientQ_branch_1119, cc20Eq115CoefficientQ_branch_1120, cc20Eq115CoefficientQ_branch_1121, cc20Eq115CoefficientQ_branch_1122, cc20Eq115CoefficientQ_branch_1123, cc20Eq115CoefficientQ_branch_1124, cc20Eq115CoefficientQ_branch_1125, cc20Eq115CoefficientQ_branch_1126, cc20Eq115CoefficientQ_branch_1127, cc20Eq115CoefficientQ_branch_1128, cc20Eq115CoefficientQ_branch_1129, cc20Eq115CoefficientQ_branch_1130, cc20Eq115CoefficientQ_branch_1131, cc20Eq115CoefficientQ_branch_1132, cc20Eq115CoefficientQ_branch_1133, cc20Eq115CoefficientQ_branch_1134, cc20Eq115CoefficientQ_branch_1135, cc20Eq115CoefficientQ_branch_1136, cc20Eq115CoefficientQ_branch_1137, cc20Eq115CoefficientQ_branch_1138, cc20Eq115CoefficientQ_branch_1139, cc20Eq115CoefficientQ_branch_1140, cc20Eq115CoefficientQ_branch_1141, cc20Eq115CoefficientQ_branch_1142, cc20Eq115CoefficientQ_branch_1143, cc20Eq115CoefficientQ_branch_1144, cc20Eq115CoefficientQ_branch_1145, cc20Eq115CoefficientQ_branch_1146, cc20Eq115CoefficientQ_branch_1147, cc20Eq115CoefficientQ_branch_1148, cc20Eq115CoefficientQ_branch_1149, cc20Eq115CoefficientQ_branch_1150, cc20Eq115CoefficientQ_branch_1151, cc20Eq115CoefficientQ_branch_1152, cc20Eq115CoefficientQ_branch_1153, cc20Eq115CoefficientQ_branch_1154, cc20Eq115CoefficientQ_branch_1155, cc20Eq115CoefficientQ_branch_1156, cc20Eq115CoefficientQ_branch_1157, cc20Eq115CoefficientQ_branch_1158, cc20Eq115CoefficientQ_branch_1159, cc20Eq115CoefficientQ_branch_1160, cc20Eq115CoefficientQ_branch_1161, cc20Eq115CoefficientQ_branch_1162, cc20Eq115CoefficientQ_branch_1163, cc20Eq115CoefficientQ_branch_1164, cc20Eq115CoefficientQ_branch_1165, cc20Eq115CoefficientQ_branch_1166, cc20Eq115CoefficientQ_branch_1167, cc20Eq115CoefficientQ_branch_1168, cc20Eq115CoefficientQ_branch_1169, cc20Eq115CoefficientQ_branch_1170, cc20Eq115CoefficientQ_branch_1171, cc20Eq115CoefficientQ_branch_1172, cc20Eq115CoefficientQ_branch_1173, cc20Eq115CoefficientQ_branch_1174, cc20Eq115CoefficientQ_branch_1175, cc20Eq115CoefficientQ_branch_1176, cc20Eq115CoefficientQ_branch_1177, cc20Eq115CoefficientQ_branch_1178, cc20Eq115CoefficientQ_branch_1179, cc20Eq115CoefficientQ_branch_1180, cc20Eq115CoefficientQ_branch_1181, cc20Eq115CoefficientQ_branch_1182, cc20Eq115CoefficientQ_branch_1183, cc20Eq115CoefficientQ_branch_1184, cc20Eq115CoefficientQ_branch_1185, cc20Eq115CoefficientQ_branch_1186, cc20Eq115CoefficientQ_branch_1187, cc20Eq115CoefficientQ_branch_1188, cc20Eq115CoefficientQ_branch_1189, cc20Eq115CoefficientQ_branch_1190, cc20Eq115CoefficientQ_branch_1191, cc20Eq115CoefficientQ_branch_1192, cc20Eq115CoefficientQ_branch_1193, cc20Eq115CoefficientQ_branch_1194, cc20Eq115CoefficientQ_branch_1195, cc20Eq115CoefficientQ_branch_1196, cc20Eq115CoefficientQ_branch_1197, cc20Eq115CoefficientQ_branch_1198, cc20Eq115CoefficientQ_branch_1199, cc20Eq115CoefficientQ_branch_1200, cc20Eq115CoefficientQ_branch_1201, cc20Eq115CoefficientQ_branch_1202, cc20Eq115CoefficientQ_branch_1203, cc20Eq115CoefficientQ_branch_1204, cc20Eq115CoefficientQ_branch_1205, cc20Eq115CoefficientQ_branch_1206, cc20Eq115CoefficientQ_branch_1207, cc20Eq115CoefficientQ_branch_1208, cc20Eq115CoefficientQ_branch_1209, cc20Eq115CoefficientQ_branch_1210, cc20Eq115CoefficientQ_branch_1211, cc20Eq115CoefficientQ_branch_1212, cc20Eq115CoefficientQ_branch_1213, cc20Eq115CoefficientQ_branch_1214, cc20Eq115CoefficientQ_branch_1215, cc20Eq115CoefficientQ_branch_1216, cc20Eq115CoefficientQ_branch_1217, cc20Eq115CoefficientQ_branch_1218, cc20Eq115CoefficientQ_branch_1219, cc20Eq115CoefficientQ_branch_1220, cc20Eq115CoefficientQ_branch_1221, cc20Eq115CoefficientQ_branch_1222, cc20Eq115CoefficientQ_branch_1223, cc20Eq115CoefficientQ_branch_1224, cc20Eq115CoefficientQ_branch_1225, cc20Eq115CoefficientQ_branch_1226, cc20Eq115CoefficientQ_branch_1227, cc20Eq115CoefficientQ_branch_1228, cc20Eq115CoefficientQ_branch_1229, cc20Eq115CoefficientQ_branch_1230, cc20Eq115CoefficientQ_branch_1231, cc20Eq115CoefficientQ_branch_1232, cc20Eq115CoefficientQ_branch_1233, cc20Eq115CoefficientQ_branch_1234, cc20Eq115CoefficientQ_branch_1235, cc20Eq115CoefficientQ_branch_1236, cc20Eq115CoefficientQ_branch_1237, cc20Eq115CoefficientQ_branch_1238, cc20Eq115CoefficientQ_branch_1239, cc20Eq115CoefficientQ_branch_1240, cc20Eq115CoefficientQ_branch_1241, cc20Eq115CoefficientQ_branch_1242, cc20Eq115CoefficientQ_branch_1243, cc20Eq115CoefficientQ_branch_1244, cc20Eq115CoefficientQ_branch_1245, cc20Eq115CoefficientQ_branch_1246, cc20Eq115CoefficientQ_branch_1247, cc20Eq115CoefficientQ_branch_1248, cc20Eq115CoefficientQ_branch_1249, cc20Eq115CoefficientQ_branch_1250, cc20Eq115CoefficientQ_branch_1251, cc20Eq115CoefficientQ_branch_1252, cc20Eq115CoefficientQ_branch_1253, cc20Eq115CoefficientQ_branch_1254, cc20Eq115CoefficientQ_branch_1255, cc20Eq115CoefficientQ_branch_1256, cc20Eq115CoefficientQ_branch_1257, cc20Eq115CoefficientQ_branch_1258, cc20Eq115CoefficientQ_branch_1259, cc20Eq115CoefficientQ_branch_1260, cc20Eq115CoefficientQ_branch_1261, cc20Eq115CoefficientQ_branch_1262, cc20Eq115CoefficientQ_branch_1263, cc20Eq115CoefficientQ_branch_1264, cc20Eq115CoefficientQ_branch_1265, cc20Eq115CoefficientQ_branch_1266, cc20Eq115CoefficientQ_branch_1267, cc20Eq115CoefficientQ_branch_1268, cc20Eq115CoefficientQ_branch_1269, cc20Eq115CoefficientQ_branch_1270, cc20Eq115CoefficientQ_branch_1271, cc20Eq115CoefficientQ_branch_1272, cc20Eq115CoefficientQ_branch_1273, cc20Eq115CoefficientQ_branch_1274, cc20Eq115CoefficientQ_branch_1275, cc20Eq115CoefficientQ_branch_1276, cc20Eq115CoefficientQ_branch_1277, cc20Eq115CoefficientQ_branch_1278, cc20Eq115CoefficientQ_branch_1279, cc20Eq115CoefficientQ_branch_1280, cc20Eq115CoefficientQ_branch_1281, cc20Eq115CoefficientQ_branch_1282, cc20Eq115CoefficientQ_branch_1283, cc20Eq115CoefficientQ_branch_1284, cc20Eq115CoefficientQ_branch_1285, cc20Eq115CoefficientQ_branch_1286, cc20Eq115CoefficientQ_branch_1287, cc20Eq115CoefficientQ_branch_1288, cc20Eq115CoefficientQ_branch_1289, cc20Eq115CoefficientQ_branch_1290, cc20Eq115CoefficientQ_branch_1291, cc20Eq115CoefficientQ_branch_1292, cc20Eq115CoefficientQ_branch_1293, cc20Eq115CoefficientQ_branch_1294, cc20Eq115CoefficientQ_branch_1295, cc20Eq115CoefficientQ_branch_1296, cc20Eq115CoefficientQ_branch_1297, cc20Eq115CoefficientQ_branch_1298, cc20Eq115CoefficientQ_branch_1299, cc20Eq115CoefficientQ_branch_1300, cc20Eq115CoefficientQ_branch_1301, cc20Eq115CoefficientQ_branch_1302, cc20Eq115CoefficientQ_branch_1303, cc20Eq115CoefficientQ_branch_1304, cc20Eq115CoefficientQ_branch_1305, cc20Eq115CoefficientQ_branch_1306, cc20Eq115CoefficientQ_branch_1307, cc20Eq115CoefficientQ_branch_1308, cc20Eq115CoefficientQ_branch_1309, cc20Eq115CoefficientQ_branch_1310, cc20Eq115CoefficientQ_branch_1311, cc20Eq115CoefficientQ_branch_1312, cc20Eq115CoefficientQ_branch_1313, cc20Eq115CoefficientQ_branch_1314, cc20Eq115CoefficientQ_branch_1315, cc20Eq115CoefficientQ_branch_1316, cc20Eq115CoefficientQ_branch_1317, cc20Eq115CoefficientQ_branch_1318, cc20Eq115CoefficientQ_branch_1319, cc20Eq115CoefficientQ_branch_1320, cc20Eq115CoefficientQ_branch_1321, cc20Eq115CoefficientQ_branch_1322, cc20Eq115CoefficientQ_branch_1323, cc20Eq115CoefficientQ_branch_1324, cc20Eq115CoefficientQ_branch_1325, cc20Eq115CoefficientQ_branch_1326, cc20Eq115CoefficientQ_branch_1327, cc20Eq115CoefficientQ_branch_1328, cc20Eq115CoefficientQ_branch_1329, cc20Eq115CoefficientQ_branch_1330, cc20Eq115CoefficientQ_branch_1331, cc20Eq115CoefficientQ_branch_1332, cc20Eq115CoefficientQ_branch_1333, cc20Eq115CoefficientQ_branch_1334, cc20Eq115CoefficientQ_branch_1335, cc20Eq115CoefficientQ_branch_1336, cc20Eq115CoefficientQ_branch_1337, cc20Eq115CoefficientQ_branch_1338, cc20Eq115CoefficientQ_branch_1339, cc20Eq115CoefficientQ_branch_1340, cc20Eq115CoefficientQ_branch_1341, cc20Eq115CoefficientQ_branch_1342, cc20Eq115CoefficientQ_branch_1343, cc20Eq115CoefficientQ_branch_1344, cc20Eq115CoefficientQ_branch_1345, cc20Eq115CoefficientQ_branch_1346, cc20Eq115CoefficientQ_branch_1347, cc20Eq115CoefficientQ_branch_1348, cc20Eq115CoefficientQ_branch_1349, cc20Eq115CoefficientQ_branch_1350, cc20Eq115CoefficientQ_branch_1351, cc20Eq115CoefficientQ_branch_1352, cc20Eq115CoefficientQ_branch_1353, cc20Eq115CoefficientQ_branch_1354, cc20Eq115CoefficientQ_branch_1355, cc20Eq115CoefficientQ_branch_1356, cc20Eq115CoefficientQ_branch_1357, cc20Eq115CoefficientQ_branch_1358, cc20Eq115CoefficientQ_branch_1359, cc20Eq115CoefficientQ_branch_1360, cc20Eq115CoefficientQ_branch_1361, cc20Eq115CoefficientQ_branch_1362, cc20Eq115CoefficientQ_branch_1363, cc20Eq115CoefficientQ_branch_1364, cc20Eq115CoefficientQ_branch_1365, cc20Eq115CoefficientQ_branch_1366, cc20Eq115CoefficientQ_branch_1367, cc20Eq115CoefficientQ_branch_1368, cc20Eq115CoefficientQ_branch_1369, cc20Eq115CoefficientQ_branch_1370, cc20Eq115CoefficientQ_branch_1371, cc20Eq115CoefficientQ_branch_1372, cc20Eq115CoefficientQ_branch_1373, cc20Eq115CoefficientQ_branch_1374, cc20Eq115CoefficientQ_branch_1375, cc20Eq115CoefficientQ_branch_1376, cc20Eq115CoefficientQ_branch_1377, cc20Eq115CoefficientQ_branch_1378, cc20Eq115CoefficientQ_branch_1379, cc20Eq115CoefficientQ_branch_1380, cc20Eq115CoefficientQ_branch_1381, cc20Eq115CoefficientQ_branch_1382, cc20Eq115CoefficientQ_branch_1383, cc20Eq115CoefficientQ_branch_1384, cc20Eq115CoefficientQ_branch_1385, cc20Eq115CoefficientQ_branch_1386, cc20Eq115CoefficientQ_branch_1387, cc20Eq115CoefficientQ_branch_1388, cc20Eq115CoefficientQ_branch_1389, cc20Eq115CoefficientQ_branch_1390, cc20Eq115CoefficientQ_branch_1391, cc20Eq115CoefficientQ_branch_1392, cc20Eq115CoefficientQ_branch_1393, cc20Eq115CoefficientQ_branch_1394, cc20Eq115CoefficientQ_branch_1395, cc20Eq115CoefficientQ_branch_1396, cc20Eq115CoefficientQ_branch_1397, cc20Eq115CoefficientQ_branch_1398, cc20Eq115CoefficientQ_branch_1399, cc20Eq115CoefficientQ_branch_1400, cc20Eq115CoefficientQ_branch_1401, cc20Eq115CoefficientQ_branch_1402, cc20Eq115CoefficientQ_branch_1403, cc20Eq115CoefficientQ_branch_1404, cc20Eq115CoefficientQ_branch_1405, cc20Eq115CoefficientQ_branch_1406, cc20Eq115CoefficientQ_branch_1407, cc20Eq115CoefficientQ_branch_1408, cc20Eq115CoefficientQ_branch_1409, cc20Eq115CoefficientQ_branch_1410, cc20Eq115CoefficientQ_branch_1411, cc20Eq115CoefficientQ_branch_1412, cc20Eq115CoefficientQ_branch_1413, cc20Eq115CoefficientQ_branch_1414, cc20Eq115CoefficientQ_branch_1415, cc20Eq115CoefficientQ_branch_1416, cc20Eq115CoefficientQ_branch_1417, cc20Eq115CoefficientQ_branch_1418, cc20Eq115CoefficientQ_branch_1419, cc20Eq115CoefficientQ_branch_1420, cc20Eq115CoefficientQ_branch_1421, cc20Eq115CoefficientQ_branch_1422, cc20Eq115CoefficientQ_branch_1423, cc20Eq115CoefficientQ_branch_1424, cc20Eq115CoefficientQ_branch_1425, cc20Eq115CoefficientQ_branch_1426, cc20Eq115CoefficientQ_branch_1427, cc20Eq115CoefficientQ_branch_1428, cc20Eq115CoefficientQ_branch_1429, cc20Eq115CoefficientQ_branch_1430, cc20Eq115CoefficientQ_branch_1431, cc20Eq115CoefficientQ_branch_1432, cc20Eq115CoefficientQ_branch_1433, cc20Eq115CoefficientQ_branch_1434, cc20Eq115CoefficientQ_branch_1435, cc20Eq115CoefficientQ_branch_1436, cc20Eq115CoefficientQ_branch_1437, cc20Eq115CoefficientQ_branch_1438, cc20Eq115CoefficientQ_branch_1439, cc20Eq115CoefficientQ_branch_1440, cc20Eq115CoefficientQ_branch_1441, cc20Eq115CoefficientQ_branch_1442, cc20Eq115CoefficientQ_branch_1443, cc20Eq115CoefficientQ_branch_1444, cc20Eq115CoefficientQ_branch_1445, cc20Eq115CoefficientQ_branch_1446, cc20Eq115CoefficientQ_branch_1447, cc20Eq115CoefficientQ_branch_1448, cc20Eq115CoefficientQ_branch_1449, cc20Eq115CoefficientQ_branch_1450, cc20Eq115CoefficientQ_branch_1451, cc20Eq115CoefficientQ_branch_1452, cc20Eq115CoefficientQ_branch_1453, cc20Eq115CoefficientQ_branch_1454, cc20Eq115CoefficientQ_branch_1455, cc20Eq115CoefficientQ_branch_1456, cc20Eq115CoefficientQ_branch_1457, cc20Eq115CoefficientQ_branch_1458, cc20Eq115CoefficientQ_branch_1459, cc20Eq115CoefficientQ_branch_1460, cc20Eq115CoefficientQ_branch_1461, cc20Eq115CoefficientQ_branch_1462, cc20Eq115CoefficientQ_branch_1463, cc20Eq115CoefficientQ_branch_1464, cc20Eq115CoefficientQ_branch_1465, cc20Eq115CoefficientQ_branch_1466, cc20Eq115CoefficientQ_branch_1467, cc20Eq115CoefficientQ_branch_1468, cc20Eq115CoefficientQ_branch_1469, cc20Eq115CoefficientQ_branch_1470, cc20Eq115CoefficientQ_branch_1471, cc20Eq115CoefficientQ_branch_1472, cc20Eq115CoefficientQ_branch_1473, cc20Eq115CoefficientQ_branch_1474, cc20Eq115CoefficientQ_branch_1475, cc20Eq115CoefficientQ_branch_1476, cc20Eq115CoefficientQ_branch_1477, cc20Eq115CoefficientQ_branch_1478, cc20Eq115CoefficientQ_branch_1479, cc20Eq115CoefficientQ_branch_1480, cc20Eq115CoefficientQ_branch_1481, cc20Eq115CoefficientQ_branch_1482, cc20Eq115CoefficientQ_branch_1483, cc20Eq115CoefficientQ_branch_1484, cc20Eq115CoefficientQ_branch_1485, cc20Eq115CoefficientQ_branch_1486, cc20Eq115CoefficientQ_branch_1487, cc20Eq115CoefficientQ_branch_1488, cc20Eq115CoefficientQ_branch_1489, cc20Eq115CoefficientQ_branch_1490, cc20Eq115CoefficientQ_branch_1491, cc20Eq115CoefficientQ_branch_1492, cc20Eq115CoefficientQ_branch_1493, cc20Eq115CoefficientQ_branch_1494, cc20Eq115CoefficientQ_branch_1495, cc20Eq115CoefficientQ_branch_1496, cc20Eq115CoefficientQ_branch_1497, cc20Eq115CoefficientQ_branch_1498, cc20Eq115CoefficientQ_branch_1499, cc20Eq115CoefficientQ_branch_1500, cc20Eq115CoefficientQ_branch_1501, cc20Eq115CoefficientQ_branch_1502, cc20Eq115CoefficientQ_branch_1503, cc20Eq115CoefficientQ_branch_1504, cc20Eq115CoefficientQ_branch_1505, cc20Eq115CoefficientQ_branch_1506, cc20Eq115CoefficientQ_branch_1507, cc20Eq115CoefficientQ_branch_1508, cc20Eq115CoefficientQ_branch_1509, cc20Eq115CoefficientQ_branch_1510, cc20Eq115CoefficientQ_branch_1511, cc20Eq115CoefficientQ_branch_1512, cc20Eq115CoefficientQ_branch_1513, cc20Eq115CoefficientQ_branch_1514, cc20Eq115CoefficientQ_branch_1515, cc20Eq115CoefficientQ_branch_1516, cc20Eq115CoefficientQ_branch_1517, cc20Eq115CoefficientQ_branch_1518, cc20Eq115CoefficientQ_branch_1519, cc20Eq115CoefficientQ_branch_1520, cc20Eq115CoefficientQ_branch_1521, cc20Eq115CoefficientQ_branch_1522, cc20Eq115CoefficientQ_branch_1523, cc20Eq115CoefficientQ_branch_1524, cc20Eq115CoefficientQ_branch_1525, cc20Eq115CoefficientQ_branch_1526, cc20Eq115CoefficientQ_branch_1527, cc20Eq115CoefficientQ_branch_1528, cc20Eq115CoefficientQ_branch_1529, cc20Eq115CoefficientQ_branch_1530, cc20Eq115CoefficientQ_branch_1531, cc20Eq115CoefficientQ_branch_1532, cc20Eq115CoefficientQ_branch_1533, cc20Eq115CoefficientQ_branch_1534, cc20Eq115CoefficientQ_branch_1535, cc20Eq115CoefficientQ_branch_1536, cc20Eq115CoefficientQ_branch_1537, cc20Eq115CoefficientQ_branch_1538, cc20Eq115CoefficientQ_branch_1539, cc20Eq115CoefficientQ_branch_1540, cc20Eq115CoefficientQ_branch_1541, cc20Eq115CoefficientQ_branch_1542, cc20Eq115CoefficientQ_branch_1543, cc20Eq115CoefficientQ_branch_1544, cc20Eq115CoefficientQ_branch_1545, cc20Eq115CoefficientQ_branch_1546, cc20Eq115CoefficientQ_branch_1547, cc20Eq115CoefficientQ_branch_1548, cc20Eq115CoefficientQ_branch_1549, cc20Eq115CoefficientQ_branch_1550, cc20Eq115CoefficientQ_branch_1551, cc20Eq115CoefficientQ_branch_1552, cc20Eq115CoefficientQ_branch_1553, cc20Eq115CoefficientQ_branch_1554, cc20Eq115CoefficientQ_branch_1555, cc20Eq115CoefficientQ_branch_1556, cc20Eq115CoefficientQ_branch_1557, cc20Eq115CoefficientQ_branch_1558, cc20Eq115CoefficientQ_branch_1559, cc20Eq115CoefficientQ_branch_1560, cc20Eq115CoefficientQ_branch_1561, cc20Eq115CoefficientQ_branch_1562, cc20Eq115CoefficientQ_branch_1563, cc20Eq115CoefficientQ_branch_1564, cc20Eq115CoefficientQ_branch_1565, cc20Eq115CoefficientQ_branch_1566, cc20Eq115CoefficientQ_branch_1567, cc20Eq115CoefficientQ_branch_1568, cc20Eq115CoefficientQ_branch_1569, cc20Eq115CoefficientQ_branch_1570, cc20Eq115CoefficientQ_branch_1571, cc20Eq115CoefficientQ_branch_1572, cc20Eq115CoefficientQ_branch_1573, cc20Eq115CoefficientQ_branch_1574, cc20Eq115CoefficientQ_branch_1575, cc20Eq115CoefficientQ_branch_1576, cc20Eq115CoefficientQ_branch_1577, cc20Eq115CoefficientQ_branch_1578, cc20Eq115CoefficientQ_branch_1579, cc20Eq115CoefficientQ_branch_1580, cc20Eq115CoefficientQ_branch_1581, cc20Eq115CoefficientQ_branch_1582, cc20Eq115CoefficientQ_branch_1583, cc20Eq115CoefficientQ_branch_1584, cc20Eq115CoefficientQ_branch_1585, cc20Eq115CoefficientQ_branch_1586, cc20Eq115CoefficientQ_branch_1587, cc20Eq115CoefficientQ_branch_1588, cc20Eq115CoefficientQ_branch_1589, cc20Eq115CoefficientQ_branch_1590, cc20Eq115CoefficientQ_branch_1591, cc20Eq115CoefficientQ_branch_1592, cc20Eq115CoefficientQ_branch_1593, cc20Eq115CoefficientQ_branch_1594, cc20Eq115CoefficientQ_branch_1595, cc20Eq115CoefficientQ_branch_1596, cc20Eq115CoefficientQ_branch_1597, cc20Eq115CoefficientQ_branch_1598, cc20Eq115CoefficientQ_branch_1599, cc20Eq115CoefficientQ_branch_1600, cc20Eq115CoefficientQ_branch_1601, cc20Eq115CoefficientQ_branch_1602, cc20Eq115CoefficientQ_branch_1603, cc20Eq115CoefficientQ_branch_1604, cc20Eq115CoefficientQ_branch_1605, cc20Eq115CoefficientQ_branch_1606, cc20Eq115CoefficientQ_branch_1607, cc20Eq115CoefficientQ_branch_1608, cc20Eq115CoefficientQ_branch_1609, cc20Eq115CoefficientQ_branch_1610, cc20Eq115CoefficientQ_branch_1611, cc20Eq115CoefficientQ_branch_1612, cc20Eq115CoefficientQ_branch_1613, cc20Eq115CoefficientQ_branch_1614, cc20Eq115CoefficientQ_branch_1615, cc20Eq115CoefficientQ_branch_1616, cc20Eq115CoefficientQ_branch_1617, cc20Eq115CoefficientQ_branch_1618, cc20Eq115CoefficientQ_branch_1619, cc20Eq115CoefficientQ_branch_1620, cc20Eq115CoefficientQ_branch_1621, cc20Eq115CoefficientQ_branch_1622, cc20Eq115CoefficientQ_branch_1623, cc20Eq115CoefficientQ_branch_1624, cc20Eq115CoefficientQ_branch_1625, cc20Eq115CoefficientQ_branch_1626, cc20Eq115CoefficientQ_branch_1627, cc20Eq115CoefficientQ_branch_1628, cc20Eq115CoefficientQ_branch_1629, cc20Eq115CoefficientQ_branch_1630, cc20Eq115CoefficientQ_branch_1631, cc20Eq115CoefficientQ_branch_1632, cc20Eq115CoefficientQ_branch_1633, cc20Eq115CoefficientQ_branch_1634, cc20Eq115CoefficientQ_branch_1635, cc20Eq115CoefficientQ_branch_1636, cc20Eq115CoefficientQ_branch_1637, cc20Eq115CoefficientQ_branch_1638, cc20Eq115CoefficientQ_branch_1639, cc20Eq115CoefficientQ_branch_1640, cc20Eq115CoefficientQ_branch_1641, cc20Eq115CoefficientQ_branch_1642, cc20Eq115CoefficientQ_branch_1643, cc20Eq115CoefficientQ_branch_1644, cc20Eq115CoefficientQ_branch_1645, cc20Eq115CoefficientQ_branch_1646, cc20Eq115CoefficientQ_branch_1647, cc20Eq115CoefficientQ_branch_1648, cc20Eq115CoefficientQ_branch_1649, cc20Eq115CoefficientQ_branch_1650, cc20Eq115CoefficientQ_branch_1651, cc20Eq115CoefficientQ_branch_1652, cc20Eq115CoefficientQ_branch_1653, cc20Eq115CoefficientQ_branch_1654, cc20Eq115CoefficientQ_branch_1655, cc20Eq115CoefficientQ_branch_1656, cc20Eq115CoefficientQ_branch_1657, cc20Eq115CoefficientQ_branch_1658, cc20Eq115CoefficientQ_branch_1659, cc20Eq115CoefficientQ_branch_1660, cc20Eq115CoefficientQ_branch_1661, cc20Eq115CoefficientQ_branch_1662, cc20Eq115CoefficientQ_branch_1663, cc20Eq115CoefficientQ_branch_1664, cc20Eq115CoefficientQ_branch_1665, cc20Eq115CoefficientQ_branch_1666, cc20Eq115CoefficientQ_branch_1667, cc20Eq115CoefficientQ_branch_1668, cc20Eq115CoefficientQ_branch_1669, cc20Eq115CoefficientQ_branch_1670, cc20Eq115CoefficientQ_branch_1671, cc20Eq115CoefficientQ_branch_1672, cc20Eq115CoefficientQ_branch_1673, cc20Eq115CoefficientQ_branch_1674, cc20Eq115CoefficientQ_branch_1675, cc20Eq115CoefficientQ_branch_1676, cc20Eq115CoefficientQ_branch_1677, cc20Eq115CoefficientQ_branch_1678, cc20Eq115CoefficientQ_branch_1679, cc20Eq115CoefficientQ_branch_1680, cc20Eq115CoefficientQ_branch_1681, cc20Eq115CoefficientQ_branch_1682, cc20Eq115CoefficientQ_branch_1683, cc20Eq115CoefficientQ_branch_1684, cc20Eq115CoefficientQ_branch_1685, cc20Eq115CoefficientQ_branch_1686, cc20Eq115CoefficientQ_branch_1687, cc20Eq115CoefficientQ_branch_1688, cc20Eq115CoefficientQ_branch_1689, cc20Eq115CoefficientQ_branch_1690, cc20Eq115CoefficientQ_branch_1691, cc20Eq115CoefficientQ_branch_1692, cc20Eq115CoefficientQ_branch_1693, cc20Eq115CoefficientQ_branch_1694, cc20Eq115CoefficientQ_branch_1695, cc20Eq115CoefficientQ_branch_1696, cc20Eq115CoefficientQ_branch_1697, cc20Eq115CoefficientQ_branch_1698, cc20Eq115CoefficientQ_branch_1699, cc20Eq115CoefficientQ_branch_1700, cc20Eq115CoefficientQ_branch_1701, cc20Eq115CoefficientQ_branch_1702, cc20Eq115CoefficientQ_branch_1703, cc20Eq115CoefficientQ_branch_1704, cc20Eq115CoefficientQ_branch_1705, cc20Eq115CoefficientQ_branch_1706, cc20Eq115CoefficientQ_branch_1707, cc20Eq115CoefficientQ_branch_1708, cc20Eq115CoefficientQ_branch_1709, cc20Eq115CoefficientQ_branch_1710, cc20Eq115CoefficientQ_branch_1711, cc20Eq115CoefficientQ_branch_1712, cc20Eq115CoefficientQ_branch_1713, cc20Eq115CoefficientQ_branch_1714, cc20Eq115CoefficientQ_branch_1715, cc20Eq115CoefficientQ_branch_1716, cc20Eq115CoefficientQ_branch_1717, cc20Eq115CoefficientQ_branch_1718, cc20Eq115CoefficientQ_branch_1719, cc20Eq115CoefficientQ_branch_1720, cc20Eq115CoefficientQ_branch_1721, cc20Eq115CoefficientQ_branch_1722, cc20Eq115CoefficientQ_branch_1723, cc20Eq115CoefficientQ_branch_1724, cc20Eq115CoefficientQ_branch_1725, cc20Eq115CoefficientQ_branch_1726, cc20Eq115CoefficientQ_branch_1727, cc20Eq115CoefficientQ_branch_1728, cc20Eq115CoefficientQ_branch_1729, cc20Eq115CoefficientQ_branch_1730, cc20Eq115CoefficientQ_branch_1731]; norm_num)

/-- The real form of every published equation-(115) coefficient is
nonnegative. -/
theorem cc20Eq115Coefficient_nonneg :
    ∀ n : Fin 1732, 0 ≤ cc20Eq115Coefficient n := by
  intro n
  rw [cc20Eq115Coefficient]
-- Term-level mod_cast lifts the source relation as-is and needs a
-- known strict target: weaken the goal to < first via le_of_lt.
  apply le_of_lt
  exact mod_cast (cc20Eq115CoefficientQ_pos n)

end C1CC20Eq115CoefficientPositivity
end Source
end ConnesWeilRH
