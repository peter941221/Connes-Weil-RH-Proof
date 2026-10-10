#!/usr/bin/env python3
"""Write _probe/probe_2663_names.lean v4: clean timing pilots for the
partition brick (dispatcher decide sum + one-panel bar norm_num + tiling).

v4 fixes vs v3 (all from the v3 log):
  - `∑ k in ...` -> `∑ k ∈ ...` (house spelling; 180 committed modules use
    `∈`, zero use `in` -- the v3 line-208 parse error);
  - probeArg2663/probeG2663 body copied TOKEN-EXACT from
    normalizedMomentIntegrand2618 (left-assoc `* (radius : ℂ) * (u : ℂ)`);
  - continuity built with an explicit `Complex.ofReal (realDiv)` (the v3
    ascription `((...) : ℂ)` split the division into a COMPLEX division --
    the 2ch/2cq cast-split law);
  - the tiling hint constructed via ContinuousOn.intervalIntegrable_of_Icc
    + IntervalIntegrable.congr on `Ι a b` (uIoc), no junk `▸`.
"""
import math, sys
from fractions import Fraction as F
sys.path.insert(0, "scripts")
import gen_2663_slots as S

def qlit(x):
    return f"(({x.numerator} : ℚ) / {x.denominator})"

# ---- 190-arm dispatcher of medium rationals (kernel-replay cost pilot) ----
arms, tot = [], F(0)
for k in range(190):
    v = F(math.isqrt(10**120 + 7*k + 1), 10**90)   # ~1e-30, 61/90 digits
    arms.append(qlit(v)); tot += v
disp = "noncomputable def probeDisp2663 : ℕ → ℚ :=\n  fun k => match k with\n" + "\n".join(
    f"  | {k} => {a}" for k, a in enumerate(arms)) + "\n  | _ => 1\n"

# ---- one-panel bar (60 significant digits) on the P094 assembly center ----
s = S.slots(94)
ph = S.pair(S.read(s["phase_module"] + ".lean"), "phaseValue2658P094")
tb = S.read(s["table_module"] if s["table_module"].endswith(".lean") else s["table_module"] + ".lean")
integral = S.pair(tb, "complexPanelIntegral2648P094")
c_re = s["amp_val"] * (ph[0]*integral[0] - ph[1]*integral[1])
c_im = s["amp_val"] * (ph[0]*integral[1] + ph[1]*integral[0])

def bars60(x):
    if x == 0:
        return F(0), F(0)
    e = math.floor(math.log10(abs(float(x))))
    step = F(10) ** (e - 60)
    return (x // step) * step, -((-x) // step) * step

re_lo, re_hi = bars60(c_re)
im_lo, im_hi = bars60(c_im)

body = f'''
-- kernel replay of a 190-arm dispatcher sum (decide +kernel timing pilot)
set_option maxHeartbeats 4000000 in
-- heartbeat budget for the kernel replay pilot
example : (∑ k ∈ Finset.range 190, probeDisp2663 k) = {qlit(tot)} := by decide +kernel

-- one-panel bar theorem (norm_num cost probe, 60 significant digits)
set_option maxHeartbeats 4000000 in
-- heartbeat budget for the bar norm_num pilot
theorem probeBarP094_2663 :
    ({qlit(re_lo)} : ℚ) ≤ panelAssemblyCenter2662P094.1
      ∧ panelAssemblyCenter2662P094.1 ≤ ({qlit(re_hi)} : ℚ)
      ∧ ({qlit(im_lo)} : ℚ) ≤ panelAssemblyCenter2662P094.2
      ∧ panelAssemblyCenter2662P094.2 ≤ ({qlit(im_hi)} : ℚ) := by
  constructor
  · norm_num [panelAssemblyCenter2662P094, pairScale2542, pairMul2542,
      ampValue2657P094, phaseValue2658P094, complexPanelIntegral2648P094]
  constructor
  · norm_num [panelAssemblyCenter2662P094, pairScale2542, pairMul2542,
      ampValue2657P094, phaseValue2658P094, complexPanelIntegral2648P094]
  constructor
  · norm_num [panelAssemblyCenter2662P094, pairScale2542, pairMul2542,
      ampValue2657P094, phaseValue2658P094, complexPanelIntegral2648P094]
  · norm_num [panelAssemblyCenter2662P094, pairScale2542, pairMul2542,
      ampValue2657P094, phaseValue2658P094, complexPanelIntegral2648P094]

-- tiling application probe on the actual entry integrand
noncomputable def probeF2663 (u : ℝ) : ℂ :=
  normalizedMomentIntegrand2618 (capturedModulations2584 3) (storedWidth 3 ^ 2) (capturedNodes2584 0) u

-- body token-exact modulo the 2618 parameter substitution
noncomputable def probeArg2663 (u : ℝ) : ℂ :=
  (-30 / (1 - u ^ 2) : ℝ) +
    (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I) *
      (storedWidth 3 ^ 2 : ℂ) * (u : ℂ)

noncomputable def probeG2663 (u : ℝ) : ℂ := Complex.exp (probeArg2663 u)

noncomputable def probeA2663 (k : ℕ) : ℝ := -(19/20) + (k : ℝ) * (1/100)

set_option maxHeartbeats 4000000 in
-- heartbeat budget for the tiling pilot
theorem probeTiling2663 :
    (∑ k ∈ Finset.Ico 0 190, ∫ x in probeA2663 k..probeA2663 (k + 1), probeF2663 x)
      = ∫ x in probeA2663 0..probeA2663 190, probeF2663 x := by
  have hden : ContinuousOn (fun u : ℝ => 1 - u ^ 2) (Set.Icc (-(19/20)) (19/20)) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have h0 : ∀ u ∈ Set.Icc (-(19/20) : ℝ) (19/20), 1 - u ^ 2 ≠ 0 := by
    intro u hu
    have h1 : |u| ≤ (19/20 : ℝ) := abs_le.mpr hu
    have h2 : u ^ 2 ≤ (19/20 : ℝ) ^ 2 := by
      rw [← sq_abs u]
      exact pow_le_pow_left₀ (abs_nonneg u) h1 2
    have : (0 : ℝ) < 1 - u ^ 2 := by nlinarith
    exact ne_of_gt this
  have hdiv : ContinuousOn (fun u : ℝ => (-30 : ℝ) / (1 - u ^ 2))
      (Set.Icc (-(19/20)) (19/20)) := by
    show ContinuousOn ((fun _ : ℝ => (-30 : ℝ)) / fun u : ℝ => 1 - u ^ 2) _
    exact ContinuousOn.div continuousOn_const hden h0
  have hdivC : ContinuousOn (fun u : ℝ => Complex.ofReal ((-30 : ℝ) / (1 - u ^ 2)))
      (Set.Icc (-(19/20)) (19/20)) :=
    Complex.continuous_ofReal.comp_continuousOn hdiv
  have hlin : ContinuousOn (fun u : ℝ =>
      (capturedNodes2584 0 + (capturedModulations2584 3 : ℂ) * Complex.I) *
        (storedWidth 3 ^ 2 : ℂ) * (u : ℂ)) (Set.Icc (-(19/20)) (19/20)) :=
    (continuousOn_const.mul continuousOn_const).mul
      (Complex.continuous_ofReal.comp_continuousOn continuousOn_id)
  have hArg : ContinuousOn probeArg2663 (Set.Icc (-(19/20)) (19/20)) :=
    hdivC.add hlin
  have hG : ContinuousOn probeG2663 (Set.Icc (-(19/20)) (19/20)) :=
    Complex.continuous_exp.comp_continuousOn hArg
  have hfg : Set.EqOn probeF2663 probeG2663 (Set.Icc (-(19/20)) (19/20)) := by
    intro u hu
    have h1 : |u| ≤ (19/20 : ℝ) := abs_le.mpr hu
    have hlt : |u| < 1 := by linarith
    simp only [probeF2663, probeG2663, probeArg2663,
      normalizedMomentIntegrand2618, if_pos hlt]
  refine intervalIntegral.sum_integral_adjacent_intervals_Ico (f := probeF2663)
    (μ := volume) (a := probeA2663) (m := 0) (n := 190) (by norm_num) ?_
  intro k hk
  have hk_le : k ≤ 189 := by have := hk.2; omega
  have hkR : (k : ℝ) ≤ 189 := by exact_mod_cast hk_le
  have hmono : probeA2663 k ≤ probeA2663 (k + 1) := by
    unfold probeA2663
    push_cast
    linarith
  have hsubIcc : Set.Icc (probeA2663 k) (probeA2663 (k + 1)) ⊆
      Set.Icc (-(19/20)) (19/20) := by
    intro u hu
    constructor
    · have h := hu.1
      unfold probeA2663 at h
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have : (0 : ℝ) ≤ (k : ℝ) * (1/100) := mul_nonneg hk0 (by norm_num)
      linarith
    · have h := hu.2
      unfold probeA2663 at h
      have : (k : ℝ) * (1/100) ≤ 189 * (1/100) :=
        mul_le_mul_of_nonneg_right hkR (by norm_num)
      linarith
  have hsubU : Set.uIcc (probeA2663 k) (probeA2663 (k + 1)) ⊆
      Set.Icc (-(19/20)) (19/20) := by
    rw [Set.uIcc_of_le hmono]
    exact hsubIcc
  have hGsub : ContinuousOn probeG2663 (Set.Icc (probeA2663 k) (probeA2663 (k + 1))) :=
    hG.mono hsubIcc
  have hIntG : IntervalIntegrable probeG2663 volume (probeA2663 k) (probeA2663 (k + 1)) :=
    ContinuousOn.intervalIntegrable_of_Icc hmono hGsub
  have heqIoc : Set.EqOn probeG2663 probeF2663
      (Set.uIoc (probeA2663 k) (probeA2663 (k + 1))) :=
    fun u hu => (hfg u (Set.uIoc_subset_uIcc.trans hsubU hu)).symm
  exact IntervalIntegrable.congr heqIoc hIntG

end ConnesWeilRH.Dev
'''

with open("_probe/probe_2663_names.lean", "w", encoding="utf-8", newline="\n") as fh:
    fh.write("import ConnesWeilRH.Dev.C1RouteAPanelTrueBall2662P094\n\n"
             "open MeasureTheory\nopen scoped BigOperators\n"
             "open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit\n\n"
             "namespace ConnesWeilRH.Dev\n\n"
             "set_option trace.profiler true\n\n")
    fh.write(disp)
    fh.write(body)
print("probe v4 written")