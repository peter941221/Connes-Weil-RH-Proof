import ConnesWeilRH.Dev.C1RouteAExpNode2541P000
import ConnesWeilRH.Dev.C1RouteAExpNode2541P001
import ConnesWeilRH.Dev.C1RouteAExpNode2541P002
import ConnesWeilRH.Dev.C1RouteAExpNode2541P003
import ConnesWeilRH.Dev.C1RouteAExpNode2541P004
import ConnesWeilRH.Dev.C1RouteAExpNode2541P005
import ConnesWeilRH.Dev.C1RouteAExpNode2541P006
import ConnesWeilRH.Dev.C1RouteAExpNode2541P007
import ConnesWeilRH.Dev.C1RouteAExpNode2541P008
import ConnesWeilRH.Dev.C1RouteAExpNode2541P009
import ConnesWeilRH.Dev.C1RouteAExpNode2541P010
import ConnesWeilRH.Dev.C1RouteAExpNode2541P011
import ConnesWeilRH.Dev.C1RouteAExpNode2541P012
import ConnesWeilRH.Dev.C1RouteAExpNode2541P013
import ConnesWeilRH.Dev.C1RouteAExpNode2541P014
import ConnesWeilRH.Dev.C1RouteAExpNode2541P015
import ConnesWeilRH.Dev.C1RouteAExpNode2541P016
import ConnesWeilRH.Dev.C1RouteAExpNode2541P017
import ConnesWeilRH.Dev.C1RouteAExpNode2541P018
import ConnesWeilRH.Dev.C1RouteAExpNode2541P019
import ConnesWeilRH.Dev.C1RouteAExpNode2541P020
import ConnesWeilRH.Dev.C1RouteAExpNode2541P021
import ConnesWeilRH.Dev.C1RouteAExpNode2541P022
import ConnesWeilRH.Dev.C1RouteAExpNode2541P023
import ConnesWeilRH.Dev.C1RouteAExpNode2541P024
import ConnesWeilRH.Dev.C1RouteAExpNode2541P025
import ConnesWeilRH.Dev.C1RouteAExpNode2541P026
import ConnesWeilRH.Dev.C1RouteAExpNode2541P027
import ConnesWeilRH.Dev.C1RouteAExpNode2541P028
import ConnesWeilRH.Dev.C1RouteAExpNode2541P029
import ConnesWeilRH.Dev.C1RouteACenterNode2540

/-! Signed nonzero node certificate; exact interpolation membership remains open. -/

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit
open ConnesWeilRH.Source.C1RouteAItem5Arithmetic

noncomputable def nodePosition2541 : ℝ := ((65536001 : ℝ) /
        51200000000)

noncomputable def nodeSumValue2541 : ℂ := ⟨(((((596802159 * 10^40
        + 8319281225752123073601382599309360727545) * 10^40
        + 2491621662830202853029527916828330246086) * 10^40
        + 2046757066676402726364838561642536697059) : ℝ) /
        (((43322963 * 10^40
        + 9706377321809127216272356828661943293027) * 10^40
        + 4713398703874344710345793446290035999960) * 10^40
        + 95377180907771737671271930809827721216)),
    (((-(((851414 * 10^40
        + 3391680379622465534274944331217079624584) * 10^40
        + 8606551726907517379116810387780167549213) * 10^40
        + 3879784579552301049292004098524677110035)) : ℝ) /
        (((1353842 * 10^40
        + 6240824291306535225508511150895685727907) * 10^40
        + 1084793709496073272198306045196563624998) * 10^40
        + 7502980536903367866802227247837807116288))⟩

noncomputable def nodeUpper2541 : ℝ := ((137900014901 : ℝ) /
        10000000000)

noncomputable def nodeZ2541 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => nodeZP0002541
  | 1 => nodeZP0012541
  | 2 => nodeZP0022541
  | 3 => nodeZP0032541
  | 4 => nodeZP0042541
  | 5 => nodeZP0052541
  | 6 => nodeZP0062541
  | 7 => nodeZP0072541
  | 8 => nodeZP0082541
  | 9 => nodeZP0092541
  | 10 => nodeZP0102541
  | 11 => nodeZP0112541
  | 12 => nodeZP0122541
  | 13 => nodeZP0132541
  | 14 => nodeZP0142541
  | 15 => nodeZP0152541
  | 16 => nodeZP0162541
  | 17 => nodeZP0172541
  | 18 => nodeZP0182541
  | 19 => nodeZP0192541
  | 20 => nodeZP0202541
  | 21 => nodeZP0212541
  | 22 => nodeZP0222541
  | 23 => nodeZP0232541
  | 24 => nodeZP0242541
  | 25 => nodeZP0252541
  | 26 => nodeZP0262541
  | 27 => nodeZP0272541
  | 28 => nodeZP0282541
  | 29 => nodeZP0292541
  | _ => 0

noncomputable def nodeValue2541 (i : Fin 30) : ℂ :=
  match i.val with
  | 0 => nodeSP0002541 6
  | 1 => nodeSP0012541 6
  | 2 => nodeSP0022541 6
  | 3 => nodeSP0032541 6
  | 4 => nodeSP0042541 6
  | 5 => nodeSP0052541 6
  | 6 => nodeSP0062541 6
  | 7 => nodeSP0072541 6
  | 8 => nodeSP0082541 6
  | 9 => nodeSP0092541 6
  | 10 => nodeSP0102541 6
  | 11 => nodeSP0112541 6
  | 12 => nodeSP0122541 6
  | 13 => nodeSP0132541 6
  | 14 => nodeSP0142541 6
  | 15 => nodeSP0152541 6
  | 16 => nodeSP0162541 6
  | 17 => nodeSP0172541 6
  | 18 => nodeSP0182541 6
  | 19 => nodeSP0192541 6
  | 20 => nodeSP0202541 6
  | 21 => nodeSP0212541 6
  | 22 => nodeSP0222541 6
  | 23 => nodeSP0232541 6
  | 24 => nodeSP0242541 6
  | 25 => nodeSP0252541 6
  | 26 => nodeSP0262541 6
  | 27 => nodeSP0272541 6
  | 28 => nodeSP0282541 6
  | 29 => nodeSP0292541 6
  | _ => 0

noncomputable def nodeError2541 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => nodeEP0002541 6
  | 1 => nodeEP0012541 6
  | 2 => nodeEP0022541 6
  | 3 => nodeEP0032541 6
  | 4 => nodeEP0042541 6
  | 5 => nodeEP0052541 6
  | 6 => nodeEP0062541 6
  | 7 => nodeEP0072541 6
  | 8 => nodeEP0082541 6
  | 9 => nodeEP0092541 6
  | 10 => nodeEP0102541 6
  | 11 => nodeEP0112541 6
  | 12 => nodeEP0122541 6
  | 13 => nodeEP0132541 6
  | 14 => nodeEP0142541 6
  | 15 => nodeEP0152541 6
  | 16 => nodeEP0162541 6
  | 17 => nodeEP0172541 6
  | 18 => nodeEP0182541 6
  | 19 => nodeEP0192541 6
  | 20 => nodeEP0202541 6
  | 21 => nodeEP0212541 6
  | 22 => nodeEP0222541 6
  | 23 => nodeEP0232541 6
  | 24 => nodeEP0242541 6
  | 25 => nodeEP0252541 6
  | 26 => nodeEP0262541 6
  | 27 => nodeEP0272541 6
  | 28 => nodeEP0282541 6
  | 29 => nodeEP0292541 6
  | _ => 0

noncomputable def nodeModulation2541 (i : Fin 30) : ℝ :=
  match i.val with
  | 0 => (((-5524291025718029) : ℝ) /
        140737488355328)
  | 1 => (((-5524291025718029) : ℝ) /
        140737488355328)
  | 2 => ((5524291025718029 : ℝ) /
        140737488355328)
  | 3 => ((5524291025718029 : ℝ) /
        140737488355328)
  | 4 => (((-5524291025718029) : ℝ) /
        140737488355328)
  | 5 => (0 : ℝ)
  | 6 => (0 : ℝ)
  | 7 => (0 : ℝ)
  | 8 => (((-3978571430081297) : ℝ) /
        281474976710656)
  | 9 => (((-5917178117733711) : ℝ) /
        281474976710656)
  | 10 => (((-3519965277442521) : ℝ) /
        140737488355328)
  | 11 => (((-3894251610461801) : ℝ) /
        140737488355328)
  | 12 => (((-2140960324737725) : ℝ) /
        70368744177664)
  | 13 => (((-4635197846686455) : ℝ) /
        140737488355328)
  | 14 => (((-5289784310949011) : ℝ) /
        140737488355328)
  | 15 => (((-5758797740487047) : ℝ) /
        140737488355328)
  | 16 => (((-3048871735671609) : ℝ) /
        70368744177664)
  | 17 => (((-6756124363134027) : ℝ) /
        140737488355328)
  | 18 => (((-1751261042181613) : ℝ) /
        35184372088832)
  | 19 => (((-1863727500536955) : ℝ) /
        35184372088832)
  | 20 => (((-7944103127967419) : ℝ) /
        140737488355328)
  | 21 => (((-8352353914239387) : ℝ) /
        140737488355328)
  | 22 => (((-8561311721741165) : ℝ) /
        140737488355328)
  | 23 => (((-4581887954876333) : ℝ) /
        70368744177664)
  | 24 => (((-4720322026636147) : ℝ) /
        70368744177664)
  | 25 => (((-152934154702833) : ℝ) /
        2199023255552)
  | 26 => (((-316954711375437) : ℝ) /
        4398046511104)
  | 27 => (((-665905501606627) : ℝ) /
        8796093022208)
  | 28 => (((-2714292757716727) : ℝ) /
        35184372088832)
  | 29 => (((-2791435723263659) : ℝ) /
        35184372088832)
  | _ => 0

theorem nodeUnit_eq2541 (i : Fin 30) :
    weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541 =
      Complex.exp ((2 : ℂ)^6 * nodeZ2541 i) := by
  have hx : |nodePosition2541| < storedWidth i ^ 2 := by
    fin_cases i <;> norm_num [nodePosition2541, storedWidth]
  simp only [weightedUnitJet2539, iteratedDeriv_zero]
  rw [weighted_unit_inside_exp2541 _ _ _ _ hx]
  congr 1
  fin_cases i <;> apply Complex.ext <;>
    norm_num [nodePosition2541, nodeModulation2541, storedWidth, nodeZ2541,
      nodeZP0002541,
      nodeZP0012541,
      nodeZP0022541,
      nodeZP0032541,
      nodeZP0042541,
      nodeZP0052541,
      nodeZP0062541,
      nodeZP0072541,
      nodeZP0082541,
      nodeZP0092541,
      nodeZP0102541,
      nodeZP0112541,
      nodeZP0122541,
      nodeZP0132541,
      nodeZP0142541,
      nodeZP0152541,
      nodeZP0162541,
      nodeZP0172541,
      nodeZP0182541,
      nodeZP0192541,
      nodeZP0202541,
      nodeZP0212541,
      nodeZP0222541,
      nodeZP0232541,
      nodeZP0242541,
      nodeZP0252541,
      nodeZP0262541,
      nodeZP0272541,
      nodeZP0282541,
      nodeZP0292541, Complex.mul_re, Complex.mul_im]

theorem nodeExp_error2541 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541 -
      nodeValue2541 i‖ ≤ nodeError2541 i := by
  rw [nodeUnit_eq2541]
  fin_cases i
  · exact nodeExpP000_error2541
  · exact nodeExpP001_error2541
  · exact nodeExpP002_error2541
  · exact nodeExpP003_error2541
  · exact nodeExpP004_error2541
  · exact nodeExpP005_error2541
  · exact nodeExpP006_error2541
  · exact nodeExpP007_error2541
  · exact nodeExpP008_error2541
  · exact nodeExpP009_error2541
  · exact nodeExpP010_error2541
  · exact nodeExpP011_error2541
  · exact nodeExpP012_error2541
  · exact nodeExpP013_error2541
  · exact nodeExpP014_error2541
  · exact nodeExpP015_error2541
  · exact nodeExpP016_error2541
  · exact nodeExpP017_error2541
  · exact nodeExpP018_error2541
  · exact nodeExpP019_error2541
  · exact nodeExpP020_error2541
  · exact nodeExpP021_error2541
  · exact nodeExpP022_error2541
  · exact nodeExpP023_error2541
  · exact nodeExpP024_error2541
  · exact nodeExpP025_error2541
  · exact nodeExpP026_error2541
  · exact nodeExpP027_error2541
  · exact nodeExpP028_error2541
  · exact nodeExpP029_error2541

theorem nodeUnit_norm2541 (i : Fin 30) :
    ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖ ≤ 1 := by
  rw [nodeUnit_eq2541, Complex.norm_exp, Real.exp_le_one_iff]
  fin_cases i <;> norm_num [nodeZ2541,
    nodeZP0002541,
    nodeZP0012541,
    nodeZP0022541,
    nodeZP0032541,
    nodeZP0042541,
    nodeZP0052541,
    nodeZP0062541,
    nodeZP0072541,
    nodeZP0082541,
    nodeZP0092541,
    nodeZP0102541,
    nodeZP0112541,
    nodeZP0122541,
    nodeZP0132541,
    nodeZP0142541,
    nodeZP0152541,
    nodeZP0162541,
    nodeZP0172541,
    nodeZP0182541,
    nodeZP0192541,
    nodeZP0202541,
    nodeZP0212541,
    nodeZP0222541,
    nodeZP0232541,
    nodeZP0242541,
    nodeZP0252541,
    nodeZP0262541,
    nodeZP0272541,
    nodeZP0282541,
    nodeZP0292541, Complex.mul_re, Complex.mul_im]

theorem nodeSum_eq2541 :
    (∑ i : Fin 30, baseCoefficientCenter2540 i * nodeValue2541 i) =
      nodeSumValue2541 := by
  rw [sum30_chain2541]
  apply Complex.ext <;>
    norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, nodeValue2541,
      nodeSumValue2541, nodeSP0002541,
      nodeSP0012541,
      nodeSP0022541,
      nodeSP0032541,
      nodeSP0042541,
      nodeSP0052541,
      nodeSP0062541,
      nodeSP0072541,
      nodeSP0082541,
      nodeSP0092541,
      nodeSP0102541,
      nodeSP0112541,
      nodeSP0122541,
      nodeSP0132541,
      nodeSP0142541,
      nodeSP0152541,
      nodeSP0162541,
      nodeSP0172541,
      nodeSP0182541,
      nodeSP0192541,
      nodeSP0202541,
      nodeSP0212541,
      nodeSP0222541,
      nodeSP0232541,
      nodeSP0242541,
      nodeSP0252541,
      nodeSP0262541,
      nodeSP0272541,
      nodeSP0282541,
      nodeSP0292541, Complex.mul_re, Complex.mul_im]

theorem nodeSum_norm2541 :
    ‖∑ i : Fin 30, baseCoefficientCenter2540 i * nodeValue2541 i‖ ≤
      ((1379000149 : ℝ) /
        100000000) := by
  rw [nodeSum_eq2541]
  apply complex_norm_le_of_sq2541 _ _ (by norm_num)
  norm_num [nodeSumValue2541]

theorem nodeEvaluation_charge2541 :
    (∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
      |(baseCoefficientCenter2540 i).im|) * nodeError2541 i) ≤ (1 : ℝ)/10^12 := by
  rw [sum30_chain2541]
  norm_num [baseCoefficientCenter2540, baseCoefficientBox2540, nodeError2541,
    nodeEP0002541,
    nodeEP0012541,
    nodeEP0022541,
    nodeEP0032541,
    nodeEP0042541,
    nodeEP0052541,
    nodeEP0062541,
    nodeEP0072541,
    nodeEP0082541,
    nodeEP0092541,
    nodeEP0102541,
    nodeEP0112541,
    nodeEP0122541,
    nodeEP0132541,
    nodeEP0142541,
    nodeEP0152541,
    nodeEP0162541,
    nodeEP0172541,
    nodeEP0182541,
    nodeEP0192541,
    nodeEP0202541,
    nodeEP0212541,
    nodeEP0222541,
    nodeEP0232541,
    nodeEP0242541,
    nodeEP0252541,
    nodeEP0262541,
    nodeEP0272541,
    nodeEP0282541,
    nodeEP0292541]

theorem signedJet_nonzero_le2541 :
    signedJetUpper2539 0 (1/2) baseCoefficientCenter2540 baseCoefficientError2540
      nodeModulation2541 nodePosition2541 ≤ nodeUpper2541 := by
  have hsum :
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i *
        weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖ ≤
      ‖∑ i : Fin 30, baseCoefficientCenter2540 i * nodeValue2541 i‖ +
        ∑ i : Fin 30, (|(baseCoefficientCenter2540 i).re| +
          |(baseCoefficientCenter2540 i).im|) * nodeError2541 i := by
    apply norm_sum_le_center_sum_add_error2531
    intro i _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) (nodeExp_error2541 i)
      (norm_nonneg _) (by positivity)
  have heach : ∀ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖ ≤
        (1 : ℝ)/10^30 := by
    intro i
    have h := mul_le_mul_of_nonneg_left (nodeUnit_norm2541 i)
      (by norm_num [baseCoefficientError2540] : 0 ≤ baseCoefficientError2540 i)
    simpa [baseCoefficientError2540] using h
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  have he' : (∑ i : Fin 30, baseCoefficientError2540 i *
      ‖weightedUnitJet2539 0 (1/2) nodeModulation2541 i nodePosition2541‖) ≤
        (30 : ℝ)/10^30 := by simpa using he
  unfold signedJetUpper2539 nodeUpper2541
  linarith [nodeSum_norm2541, nodeEvaluation_charge2541]

theorem weightedPhysical_nonzero_le2541 (coefficients : Fin 30 → ℂ)
    (hbox : ∀ i, (baseCoefficientBox2540 i).Mem (coefficients i)) :
    ‖weightedPhysical2539 (1/2) coefficients nodeModulation2541 nodePosition2541‖ ≤
      nodeUpper2541 := by
  have h := weightedPhysical2539_jet_le_center_error 0 (1/2) coefficients
    baseCoefficientCenter2540 baseCoefficientError2540 nodeModulation2541
    (fun i => baseCoefficient_error_of_box2540 i (coefficients i) (hbox i)) nodePosition2541
  simpa only [iteratedDeriv_zero] using h.trans signedJet_nonzero_le2541

theorem production_grid_nonzero2541 :
    -stripRadius2303 + (5121 : ℝ)*(2*stripRadius2303/10240) = nodePosition2541 := by
  norm_num [stripRadius2303, nodePosition2541]

end ConnesWeilRH.Dev
