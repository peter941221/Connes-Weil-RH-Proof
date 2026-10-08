import json, re, sys
from fractions import Fraction as F

sys.set_int_max_str_digits(0)

centers = {}
for path, scope in [
    ('results/2622_moment_panel_batch_payload.json', range(90, 100)),
    ('results/2625_moment_panel_remaining_payload.json',
     [i for i in range(180) if not 90 <= i <= 99]),
]:
    d = json.load(open(path, encoding='utf-8'))
    for k in scope:
        centers[k] = F(d['panels_data'][str(k)]['integral_center'])
assert len(centers) == 180

dec = {}
for p in range(180):
    s = open(r'ConnesWeilRH/Dev/C1RouteAMomentActualPanel2622Panel%03d.lean' % p,
             encoding='utf-8').read()
    m = re.search(r'theorem actualMomentPanel%03d_integral_error_le2622[\s\S]*?≤ \(1 : [^)]*\) / 10 \^ (\d+)' % p, s)
    assert m, p
    dec[p] = int(m.group(1))

mu = sum(centers[p] for p in range(180))
eps = F(2, 10**68) + sum(F(1, 10**dec[p]) for p in range(180))
chunks = [sum(centers[p] for p in range(30*j, 30*j+30)) for j in range(6)]

reLoN = '743385289111314700018066124496515390696115316514754031412488212787202855100552797508478504614343'
reLoD = '9394170331095332911557922387157348109502730195633279482829163886128836100458433773854795993539074812127739904'
reHiN = '743385289111314700018066124496515390696115316514755152681889425131760968462627791947481122683335'
reHiD = reLoD

muN, muD = str(mu.numerator), str(mu.denominator)
epsN, epsD = str(eps.numerator), str(eps.denominator)

L = []
L.append('import ConnesWeilRH.Dev.ZProbe2628Integrability')
L.append('import ConnesWeilRH.Dev.C1RouteACorrectionAnalyticIntervals2597')
for p in range(180):
    L.append('import ConnesWeilRH.Dev.C1RouteAMomentActualPanel2622Panel%03d' % p)
L.append('')
L.append('set_option maxHeartbeats 4000000')
L.append('set_option maxRecDepth 100000')
L.append('namespace ConnesWeilRH.Dev')
L.append('')
L.append('open MeasureTheory')
L.append('open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit')
L.append('')
L.append('def partitionCenter2628 : ℕ → ℚ')
for p in range(180):
    L.append('  | %d => momentPanelIntegralCenter2622P%03d' % (p, p))
L.append('  | _ => 0')
L.append('')
L.append('def dec2628 : ℕ → ℕ')
for p in range(180):
    L.append('  | %d => %d' % (p, dec[p]))
L.append('  | _ => 0')
L.append('')
L.append('noncomputable def panelIntegral2628 : ℕ → ℝ')
for p in range(180):
    panel_left = F(-9, 10) + F(p, 100)
    panel_right = panel_left + F(1, 100)
    left_text = ('-(%d / %d)' % (-panel_left.numerator, panel_left.denominator)) if panel_left < 0 else ('%d / %d' % (panel_left.numerator, panel_left.denominator))
    right_text = ('-(%d / %d)' % (-panel_right.numerator, panel_right.denominator)) if panel_right < 0 else ('%d / %d' % (panel_right.numerator, panel_right.denominator))
    L.append('  | %d => (storedWidth 0 ^ 2) * (∫ position in (%s : ℝ)..(%s : ℝ),' % (p, left_text, right_text))
    L.append('      realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)')
    L.append('        (capturedNodes2584 0).re position)')
L.append('  | _ => 0')
L.append('')
L.append('theorem panelIntegral2628_eq_global (p : ℕ) (hp : p < 180) :')
L.append('    panelIntegral2628 p =')
L.append('      (storedWidth 0 ^ 2) * (∫ x in ((-9 / 10 : ℝ) + p / 100)..((-9 / 10 : ℝ) + (p + 1) / 100),')
L.append('        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)')
L.append('          (capturedNodes2584 0).re x) := by')
L.append('  interval_cases p <;> norm_num [panelIntegral2628]')
L.append('')
for p in range(180):
    L.append('theorem panelError2628_%03d :' % p)
    L.append('    |panelIntegral2628 %d - (partitionCenter2628 %d : ℝ)| ≤' % (p, p))
    L.append('      (1 : ℝ) / 10 ^ dec2628 %d := by' % p)
    L.append('  simpa [panelIntegral2628, partitionCenter2628, dec2628] using')
    L.append('    actualMomentPanel%03d_integral_error_le2622' % p)
    L.append('')
L.append('theorem panelIntegrals2628_sum_eq_global :')
L.append('    ∑ p ∈ Finset.range 180, panelIntegral2628 p =')
L.append('      (storedWidth 0 ^ 2) * (∫ x in (-9 / 10 : ℝ)..(9 / 10 : ℝ),')
L.append('        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)')
L.append('          (capturedNodes2584 0).re x) := by')
L.append('  have hint : ∀ k : ℕ, k < 180 → IntervalIntegrable')
L.append('      (realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)')
L.append('        (capturedNodes2584 0).re) volume')
L.append('      ((-9 / 10 : ℝ) + (k : ℝ) / 100)')
L.append('      ((-9 / 10 : ℝ) + (((k + 1 : ℕ) : ℝ) / 100)) := by')
L.append('    intro k hk')
L.append('    exact probeIntervalIntegrable2628 (storedWidth 0 ^ 2)')
L.append('      (capturedNodes2584 0).re _ _')
L.append('  have hsum := intervalIntegral.sum_integral_adjacent_intervals')
L.append('    (f := realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2)')
L.append('      (capturedNodes2584 0).re) (μ := volume)')
L.append('    (a := fun k : ℕ => (-9 / 10 : ℝ) + (k : ℝ) / 100)')
L.append('    (n := 180) hint')
L.append('  norm_num at hsum')
L.append('  calc')
L.append('    ∑ p ∈ Finset.range 180, panelIntegral2628 p =')
L.append('        ∑ p ∈ Finset.range 180, (storedWidth 0 ^ 2) * (∫ x in')
L.append('          ((-9 / 10 : ℝ) + (p : ℝ) / 100)..((-9 / 10 : ℝ) + (((p + 1 : ℕ) : ℝ) / 100)),')
L.append('          realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re x) := by')
L.append('      apply Finset.sum_congr rfl')
L.append('      intro p hp')
L.append('      rw [panelIntegral2628_eq_global p (Finset.mem_range.mp hp)]')
L.append('      congr 1')
L.append('      norm_num')
L.append('    _ = (storedWidth 0 ^ 2) * (∑ p ∈ Finset.range 180, ∫ x in')
L.append('          ((-9 / 10 : ℝ) + (p : ℝ) / 100)..((-9 / 10 : ℝ) + (((p + 1 : ℕ) : ℝ) / 100)),')
L.append('          realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re x) := by')
L.append('      rw [Finset.mul_sum]')
L.append('    _ = (storedWidth 0 ^ 2) * (∫ x in (-9 / 10 : ℝ)..(9 / 10 : ℝ),')
L.append('        realNormalizedMomentIntegrand2618 (storedWidth 0 ^ 2) (capturedNodes2584 0).re x) := by')
L.append('      convert congrArg (fun z : ℝ => (storedWidth 0 ^ 2) * z) hsum using 1 <;> norm_num')
L.append('')
L.append('theorem panelError2628 (p : ℕ) (hp : p < 180) :')
L.append('    |panelIntegral2628 p - (partitionCenter2628 p : ℝ)| ≤')
L.append('      (1 : ℝ) / 10 ^ dec2628 p := by')
L.append('  interval_cases p')
for p in range(180):
    L.append('  · exact panelError2628_%03d' % p)
L.append('')
L.append('theorem panelErrorSum2628 :')
L.append('    |∑ p ∈ Finset.range 180,')
L.append('        (panelIntegral2628 p - (partitionCenter2628 p : ℝ))| ≤')
L.append('      ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628 p := by')
L.append('  calc')
L.append('    |∑ p ∈ Finset.range 180,')
L.append('        (panelIntegral2628 p - (partitionCenter2628 p : ℝ))| ≤')
L.append('      ∑ p ∈ Finset.range 180,')
L.append('        |panelIntegral2628 p - (partitionCenter2628 p : ℝ)| := by')
L.append('      exact Finset.abs_sum_le_sum_abs (s := Finset.range 180)')
L.append('        (f := fun p => panelIntegral2628 p - (partitionCenter2628 p : ℝ))')
L.append('    _ ≤ ∑ p ∈ Finset.range 180, (1 : ℝ) / 10 ^ dec2628 p := by')
L.append('      apply Finset.sum_le_sum')
L.append('      intro p hp')
L.append('      exact panelError2628 p (Finset.mem_range.mp hp)')
L.append('')


def nested(terms):
    # right-nested sum: a + (b + (c + ... + z))
    if len(terms) == 1:
        return terms[0]
    return terms[0] + ' + (' + nested(terms[1:]) + ')'


for j in range(6):
    terms = ['partitionCenter2628 %d' % (30*j + k) for k in range(30)]
    L.append('def chunkCenters2628_%d : ℚ := %s' % (j, nested(terms)))
L.append('')
for j in range(6):
    L.append('theorem chunkCenters_replay2628_%d : chunkCenters2628_%d =' % (j, j))
    names = ', '.join('momentPanelIntegralCenter2622P%03d' % (30*j + k) for k in range(30))
    L.append('  ((%s : ℚ) / %s) := by norm_num [chunkCenters2628_%d, partitionCenter2628, %s]' %
             (chunks[j].numerator, chunks[j].denominator, j, names))
L.append('')
L.append('def totalCenters2628 : ℚ := %s' % nested(
    ['chunkCenters2628_%d' % j for j in range(6)]))
L.append('')
rw_list = ', '.join('chunkCenters_replay2628_%d' % j for j in range(6))
L.append('theorem totalCenters_replay2628 : totalCenters2628 = ((%s : ℚ) / %s) := by' % (muN, muD))
L.append('  rw [totalCenters2628, %s]' % rw_list)
L.append('  norm_num')
L.append('')
L.append('theorem probeEpsReplay2628 :')
L.append('    ((2 : ℚ) / 10 ^ 68 + %s) = ((%s : ℚ) / %s) := by'
         % (nested(['(1 : ℚ) / 10 ^ %d' % dec[p] for p in range(180)]), epsN, epsD))
L.append('  norm_num')
L.append('')
L.append('theorem probeFinalLo2628 :')
L.append('    ((%s : ℚ) / %s) ≤ (%s : ℚ) / %s - (%s : ℚ) / %s := by'
         % (reLoN, reLoD, muN, muD, epsN, epsD))
L.append('  norm_num')
L.append('')
L.append('theorem probeFinalHi2628 :')
L.append('    (%s : ℚ) / %s + (%s : ℚ) / %s ≤ (%s : ℚ) / %s := by'
         % (muN, muD, epsN, epsD, reHiN, reHiD))
L.append('  norm_num')
L.append('')
L.append('theorem probeCloseLo2628 :')
L.append('    (analyticMomentInterval2597 0 0).reLo ≤ (((%s : ℚ) / %s : ℚ) : ℝ) := by' % (muN, muD))
L.append('  have hreLoEq : (analyticMomentInterval2597 0 0).reLo =')
L.append('      (((%s : ℚ) / %s : ℚ) : ℝ) := by' % (reLoN, reLoD))
L.append('    norm_num [analyticMomentInterval2597, analyticMomentInterval2597_row_00]')
L.append('  have hlo2 : (%s : ℚ) / %s ≤ (%s : ℚ) / %s := by norm_num' % (reLoN, reLoD, muN, muD))
L.append('  rw [hreLoEq]')
L.append('  exact Rat.cast_le.mpr hlo2')
L.append('')
L.append('theorem probeCloseHi2628 :')
L.append('    (((%s : ℚ) / %s : ℚ) : ℝ) ≤ (analyticMomentInterval2597 0 0).reHi := by' % (muN, muD))
L.append('  have hreHiEq : (analyticMomentInterval2597 0 0).reHi =')
L.append('      (((%s : ℚ) / %s : ℚ) : ℝ) := by' % (reHiN, reHiD))
L.append('    norm_num [analyticMomentInterval2597, analyticMomentInterval2597_row_00]')
L.append('  have hhi2 : (%s : ℚ) / %s ≤ (%s : ℚ) / %s := by norm_num' % (muN, muD, reHiN, reHiD))
L.append('  rw [hreHiEq]')
L.append('  exact Rat.cast_le.mpr hhi2')
L.append('')
L.append('end ConnesWeilRH.Dev')
L.append('')

with open('ConnesWeilRH/Dev/ZProbe2628Sum.lean', 'w', encoding='utf-8', newline='\n') as f:
    f.write('\n'.join(L))
print('emitted ConnesWeilRH/Dev/ZProbe2628Sum.lean')
print('mu digits:', len(muN), '/', len(muD), ' eps digits:', len(epsN), '/', len(epsD))
