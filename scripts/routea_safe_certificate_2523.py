"""Exact witnesses for all safe cells on the actual Lean production grid.

Python selects rational witnesses; every inequality is rechecked by Lean.
124 right-half cells cover 248 cells through the proved reflection identity.
--smoke emits the centre and edge modules; --full emits the complete family.
No float is used to choose a certified upper. The 415 budget is an exact gate.
"""
import argparse
import hashlib
import json
import math
import re
from fractions import Fraction as F
from pathlib import Path

import routea_owner_family_binding_2493 as binding

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT/"ConnesWeilRH/Dev"
GRID_SOURCE = DEV/"C1RouteAItem5Arithmetic.lean"
OUT = ROOT/"results/2523_safe_certificate.json"
EXP_ONE = F(3678794411714424, 10**16)
ERR = F(21, math.factorial(20)*20)


def ceil_grid(value, denominator):
    return F(-((-value.numerator*denominator)//value.denominator), denominator)


def lit(value):
    return f"(({value.numerator} : ℝ) / {value.denominator})"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def header(imports):
    return [*(f"import {name}" for name in imports), "",
        "/-! Generated exact witnesses for record 2523. No external bound is assumed. -/",
        "namespace ConnesWeilRH.Dev",
        "open ConnesWeilRH.Source.C1RouteAItem5Arithmetic",
        "open ConnesWeilRH.Source.C1ScaledExpRationalEnvelope",
        "set_option linter.style.longLine false", "set_option maxRecDepth 100000", ""]


def write(name, lines):
    path = DEV/(name+".lean")
    path.write_text("\n".join(lines+["", "end ConnesWeilRH.Dev", ""]),
                    encoding="utf-8", newline="\n")
    return path


def chain30():
    result = "f 29"
    for i in reversed(range(29)):
        result = f"f {i} + ({result})"
    return result


def inputs():
    grid_text = GRID_SOURCE.read_text(encoding="utf-8")
    match = re.search(r"^def stripRadius2303 : Real := ([0-9.]+)$", grid_text, re.M)
    assert match, "actual grid literal is not recognized"
    radius = F(match[1])
    scalar, coefficients = binding.parse_lean_defs()
    families = []
    for i in range(30):
        r, m = scalar[f"rad{i}_2460"], scalar[f"mod{i}_2460"]
        c = sum(map(abs, coefficients[f"coef{i}_2460"]))
        x = r/10
        assert 0 <= x <= 1
        exp_upper = (sum((x**k/math.factorial(k) for k in range(20)), F(0)) + x**20*ERR)**5
        W = ceil_grid(exp_upper, 10**20)
        families.append((r, m, c, W))
    return radius, families


def data_for(radius, families):
    cells = []
    for j in range(320, 444):
        left, right = -radius+j*radius/320, -radius+(j+1)*radius/320
        rows = []
        for i, (r, m, c, W) in enumerate(families):
            t = max(abs(left), abs(right))/r
            a = F(0) if left <= 0 <= right else min(abs(left), abs(right))/r
            assert 0 <= a <= t < 1
            z = 30/(1-a*a)
            n = z.numerator//z.denominator
            rem = z-n
            P = ceil_grid(EXP_ONE**min(n, 200), 10**80)
            poly = sum(((-rem)**k/math.factorial(k) for k in range(20)), F(0))+ERR
            assert 0 <= rem < 1 and poly > 0
            U = ceil_grid(P*poly, 10**50)
            d = 1-t*t
            slope = 60*t/(d*d*r)
            factor = c*(60*(1/d**2+4*t*t/d**3)/r**2 + slope**2 + m*m +
                        2*abs(m)*slope + slope + abs(m) + F(1,4))
            B = ceil_grid(W*U*factor, 1024)
            assert W*U*factor <= B and EXP_ONE**n*poly <= U
            rows.append(dict(i=i, n=n, z=z, P=P, U=U, B=B))
        cells.append(dict(index=j, rows=rows, upper=sum((x['B'] for x in rows), F(0))))
    return cells


def constants(families, cells):
    lines = header(["ConnesWeilRH.Dev.C1RouteASafeScalar2523", "Mathlib.Algebra.BigOperators.Fin"])
    for i, (_, _, _, W) in enumerate(families):
        lines += [f"theorem safeWeight{i}_2523 : Real.exp (ownerRad_2463 {i} / 2) ≤ {lit(W)} := by",
                  "  apply exp_weight_rational2523",
                  f"  · norm_num [ownerRad_2463, rad{i}_2460]",
                  f"  · norm_num [ownerRad_2463, rad{i}_2460]",
                  f"  · norm_num [ownerRad_2463, rad{i}_2460, Finset.sum_range_succ]", ""]
    powers = {row['n']: row['P'] for cell in cells for row in cell['rows']}
    powers[200] = ceil_grid(EXP_ONE**200, 10**80)
    for n, P in sorted(powers.items()):
        lines += [f"theorem safePower{n}_2523 : expNegOneUpper2498 ^ {n} ≤ {lit(P)} := by"]
        if n <= 200:
            lines += ["  norm_num [expNegOneUpper2498]", ""]
        else:
            lines += ["  exact (pow_le_pow_of_le_one (a := expNegOneUpper2498) (by norm_num [expNegOneUpper2498])",
                      "    (by norm_num [expNegOneUpper2498])",
                      f"    (by norm_num : 200 ≤ {n})).trans safePower200_2523", ""]
    lines += ["theorem safe_sum30_chain2523 (f : Fin 30 → ℝ) :",
              f"    (∑ i : Fin 30, f i) = {chain30()} := by",
              "  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]", "  rfl", ""]
    return write("C1RouteASafeConstants2523", lines)


def cell_proofs(cell, families):
    j, rows, total = cell['index'], cell['rows'], cell['upper']
    lines = []
    for row, (_, _, _, W) in zip(rows, families):
        i, n, z, P, U, B = (row[k] for k in ('i','n','z','P','U','B'))
        defs = (f"ownerRad_2463, ownerMod_2463, ownerCoef_2463, "
                f"rad{i}_2460, mod{i}_2460, coef{i}_2460")
        lines += [f"theorem safeCell{j}Family{i}_2523 : safeFamily2523 {j} {i} ≤ {lit(B)} := by",
                  f"  have hz : 30 / (1 - (ownerCellLowerRatio2501 stripRadius2303",
                  f"      (stripRadius2303 / 320) {j} {i}) ^ 2) = {lit(z)} := by",
                  f"    norm_num [ownerCellLowerRatio2501, stripRadius2303, {defs}]",
                  f"  have hu : ownerProductionExpUpper2514 {j} {i} ≤ {lit(U)} := by",
                  "    unfold ownerProductionExpUpper2514", "    rw [hz]",
                  f"    apply split_upper_rational2523 {lit(z)} {lit(P)} {lit(U)} {n}",
                  "    · apply (Nat.floor_eq_iff' (by norm_num)).mpr",
                  "      constructor <;> norm_num",
                  f"    · exact safePower{n}_2523", "    · norm_num", "    · norm_num",
                  "    · norm_num [expTaylor20, expTaylor20Error, Finset.sum_range_succ]",
                  f"  apply safeFamily_le_rational2523 {j} {i} {lit(W)} {lit(U)} {lit(B)}",
                  f"    safeWeight{i}_2523 hu (by norm_num)",
                  f"    (safeFactor_owner_nonneg2523 {j} {i} (by omega) (by omega))",
                  f"  norm_num [safeFactor2523, ownerProductionT2516, ownerCellEndpointRatio2488,",
                  f"    stripRadius2303, {defs}]", ""]
    lines += [f"theorem safeCell{j}_2523 : (∑ i : Fin 30, safeFamily2523 {j} i) ≤ {lit(total)} := by",
              "  rw [safe_sum30_chain2523]"]
    # Build the sum inequality without placing large terms in elaborator metavariables.
    proof = f"safeCell{j}Family29_2523"
    for i in reversed(range(29)):
        proof = f"add_le_add safeCell{j}Family{i}_2523 ({proof})"
    lines += [f"  have h := {proof}", "  norm_num at h ⊢", "  exact h", ""]
    return lines


def summary_module(cells, modules, radius):
    lines = header([f"ConnesWeilRH.Dev.{name}" for name in modules])
    lines += ["noncomputable def safeCellTable2523 (index : ℕ) : ℝ :=", "  match index with"]
    lines += [f"  | {cell['index']} => {lit(cell['upper'])}" for cell in cells]
    lines += ["  | _ => 0", "",
        "theorem safeRight_hcell2523 (index : ℕ) (hlo : 320 ≤ index) (hhi : index ≤ 443) :",
        "    (∑ i : Fin 30, safeFamily2523 index i) ≤ safeCellTable2523 index := by",
        "  interval_cases index"]
    lines += [f"  · exact safeCell{cell['index']}_2523" for cell in cells]
    lines += ["", "def safeCanonical2523 (index : ℕ) : ℕ := if index < 320 then 639 - index else index", "",
        "noncomputable def productionTable2523 (index : ℕ) : ℝ :=",
        "  if ownerProductionSafe2516 index = true then safeCellTable2523 (safeCanonical2523 index)",
        "  else 1387328", "",
        "theorem safe_hcell2523 (sigma : ℝ) (index : ℕ)",
        "    (hsigma : sigma = -(1 / 2 : ℝ) ∨ sigma = (1 / 2 : ℝ))",
        "    (hlo : 196 ≤ index) (hhi : index ≤ 443) :",
        "    ownerProductionRemainderTerm2521 sigma index ≤ productionTable2523 index := by",
        "  rw [production_safe_scalar2523 sigma index hsigma hlo hhi]",
        "  simp only [productionTable2523, ownerProductionSafe2516,",
        "    if_pos (And.intro hlo hhi), ↓reduceIte]",
        "  by_cases hleft : index < 320",
        "  · simp only [safeCanonical2523, if_pos hleft]",
        "    rw [← safeSum_reflect2523 index (by omega)]",
        "    exact safeRight_hcell2523 (639 - index) (by omega) (by omega)",
        "  · simp only [safeCanonical2523, if_neg hleft]",
        "    exact safeRight_hcell2523 index (by omega) hhi", "",
        "theorem production_hcell2523 (sigma : ℝ) (index : ℕ)",
        "    (hsigma : sigma = -(1 / 2 : ℝ) ∨ sigma = (1 / 2 : ℝ)) :",
        "    ownerProductionRemainderTerm2521 sigma index ≤ productionTable2523 index := by",
        "  by_cases hs : 196 ≤ index ∧ index ≤ 443",
        "  · exact safe_hcell2523 sigma index hsigma hs.1 hs.2",
        "  · simpa [ownerProductionRemainderTerm2521, productionTable2523,",
        "      ownerProductionSafe2516, hs] using familyFallback_bound2522 sigma hsigma", "",
        ""]
    # The 640-entry table is never evaluated in a single norm_num: one call
    # unfolding all entries times out at whnf (record 2523 build log), and a
    # single explicit 640-leaf chain also times out.  Nine peel lemmas split
    # the range by Finset.sum_range_add; ten segment lemmas each evaluate 64
    # entries; the final gate sums ten exact rationals.
    scale = (radius / 320) ** 3 / 12
    cellmap = {cell["index"]: cell["upper"] for cell in cells}

    def table_value(j):
        if 196 <= j <= 443:
            return cellmap[j if j >= 320 else 639 - j]
        return F(1387328)

    def off(k):
        s = "i"
        for _ in range(k):
            s = f"64 + ({s})"
        return s

    def body(e):
        return f"productionTable2523 ({e}) * (stripRadius2303 / 320) ^ 3 / 12"
    for k in range(10):
        block = sum((table_value(64*k+t)*scale for t in range(64)), F(0))
        lines += ["set_option maxHeartbeats 4000000 in",
                  "-- each segment unfolds exactly 64 table entries inside one bounded norm_num call",
                  f"theorem remainder_segment{k:02d}_2523 :",
                  f"    ∑ i ∈ Finset.range 64, {body(off(k))}",
                  f"      = {lit(block)} := by",
                  "  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]",
                  "  norm_num [productionTable2523, safeCellTable2523, safeCanonical2523,",
                  "    ownerProductionSafe2516, stripRadius2303]", ""]
    for k in range(9):
        left_range, right_range = 64*(10-k), 64*(9-k)
        lines += [f"theorem remainder_peel{k:02d}_2523 :",
                  f"    ∑ i ∈ Finset.range {left_range}, {body(off(k))}",
                  f"      = {lit(sum(table_value(64*k+t)*scale for t in range(64)))}",
                  f"        + ∑ i ∈ Finset.range {right_range}, {body(off(k+1))} := by",
                  f"  have h : {left_range} = 64 + {right_range} := by norm_num",
                  f"  rw [h, Finset.sum_range_add, remainder_segment{k:02d}_2523]", ""]
    lines += ["theorem productionTable_remainder_le_415_2523 :",
              "    localCurvatureRemainder2474 productionTable2523 (stripRadius2303 / 320) 640 ≤ 415 := by",
              "  simp only [localCurvatureRemainder2474]",
              "  rw [" + ", ".join([f"remainder_peel{k:02d}_2523" for k in range(9)] +
                  ["remainder_segment09_2523"]) + "]",
              "  norm_num", "",
              "theorem ownerPanelStripNorm_le_nodes_add_415_2523 (sigma : ℝ)",
              "    (hsigma : sigma = -(1 / 2 : ℝ) ∨ sigma = (1 / 2 : ℝ)) :",
              "    stripNorm sigma ownerPanelSumValue_2467 ≤",
              "      compositeNodeUpper2347",
              "        (ownerPanelNodeUpper2471 sigma stripRadius2303 (stripRadius2303 / 320))",
              "        (stripRadius2303 / 320) 640 + 415 := by",
              "  have h := ownerPanelStripNorm_le_productionTable2521 sigma productionTable2523",
              "    (fun index _ => production_hcell2523 sigma index hsigma)",
              "  exact h.trans (add_le_add (le_refl _) productionTable_remainder_le_415_2523)"]
    return write("C1RouteASafeCertificate2523", lines)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--smoke', action='store_true')
    parser.add_argument('--full', action='store_true')
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    radius, families = inputs()
    cells = data_for(radius, families)
    total = (392*F(1387328)+2*sum((x['upper'] for x in cells),F(0)))*(radius/320)**3/12
    assert total < 415, 'the explicit remainder target fails'
    old = json.loads((ROOT/'results/2517_owner_production_exp_remainder.json').read_text(encoding='utf-8'))
    old_radius = F(2076918743413931858457251756481,316912650057057350374175801344)
    old_table = [F.from_float(float.fromhex(x)) if 196 <= i <= 443 else F(1387328)
                 for i,x in enumerate(old['rows'][0]['cell_upper_nextup_hex'])]
    old_total = sum(old_table)*(old_radius/320)**3/12
    result = {'record':2523, 'status':'EXACT_WITNESSES_BUILD_REQUIRED',
              'grid_radius_exact':str(radius), 'old_price_radius_exact':str(old_radius),
              'radius_equal':radius==old_radius, 'right_cells':124, 'safe_cells':248,
              'fallback_cells':392, 'total_upper_exact':str(total),
              'total_upper_display':float(total), 'target':415,
              'old_2522_table_total_reassembled':float(old_total),
              'safe_cells_bounds':[{'index':x['index'],'upper':str(x['upper'])} for x in cells],
              'scope':'fixed 2463 midpoint function, sigma +/-1/2; node sum remains',
              'sources':{str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in
                  [Path(__file__).resolve(),binding.LEAN,GRID_SOURCE,DEV/'C1RouteASafeScalar2523.lean']}}
    if args.check:
        stored = json.loads(OUT.read_text(encoding='utf-8'))
        for key, value in result.items():
            assert stored[key] == value, f'artifact drift: {key}'
        for name, digest in stored.get('generated', {}).items():
            assert sha(ROOT/name) == digest, f'generated source drift: {name}'
        print('PASS: exact grid, all rational witnesses, source hashes, generated module hashes')
        return
    if args.smoke or args.full:
        paths=[constants(families,cells)]
        if args.full:
            modules=[]
            for offset in range(0,124,8):
                name=f'C1RouteASafeCells2523Part{offset//8:02}'
                modules.append(name)
                lines=header(['ConnesWeilRH.Dev.C1RouteASafeConstants2523'])
                for cell in cells[offset:offset+8]:
                    lines+=cell_proofs(cell,families)
                paths.append(write(name,lines))
            paths.append(summary_module(cells,modules,radius))
        else:
            lines=header(['ConnesWeilRH.Dev.C1RouteASafeConstants2523'])
            for cell in (cells[0],cells[-1]):
                lines+=cell_proofs(cell,families)
            paths.append(write('C1RouteASafeSmoke2523',lines))
        result['generated']={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in paths}
    OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(f'Exact radius {radius}; total {float(total):.12f} < 415; {len(cells)} right cells')


if __name__=='__main__':
    main()
