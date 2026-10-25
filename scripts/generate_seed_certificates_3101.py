#!/usr/bin/env python3
"""Generate exact rational witnesses for the actual D4/D7 seed integrals.

Python is only a witness generator. Every interval widening, exponential
scaling step, derivative recurrence and price is checked again by Lean.
Default: four difficult/boundary cells. --all: the complete 8192-cell owner.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEN = 1 << 256
COUNT = 8192
CHUNK = 64
WIDTH = Q(2047, 33554432)
ZERO = (Q(0), Q(0))
ONE = (Q(1), Q(1))


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def mul(a, b):
    products = [x*y for x in a for y in b]
    return min(products), max(products)


def inv(a):
    assert a[0] > 0
    return 1/a[1], 1/a[0]


def power(a, n):
    result = ONE
    for _ in range(n):
        result = mul(result, a)
    return result


def scale(n, a):
    return mul((Q(n), Q(n)), a)


def total(values):
    result = ZERO
    for value in values:
        result = add(result, value)
    return result


def rounded(a):
    return Q(math.floor(a[0]*DEN), DEN), Q(math.ceil(a[1]*DEN), DEN)


def contains(outer, inner):
    return outer[0] <= inner[0] <= inner[1] <= outer[1]


def phase(cell, n):
    return scale(math.factorial(n), sub(power(inv(sub(ONE, cell)), n+1),
                                      scale((-1)**n, power(inv(cell), n+1))))


def taylor(x):
    return sum((x**j / math.factorial(j) for j in range(20)), Q(0))


def tail(x):
    return x**20 * 21 / (math.factorial(20)*20)


def initial_exp(p, k):
    low, high = -p[0]/(1 << k), -p[1]/(1 << k)
    assert 0 <= high <= low <= 1
    return 1/(taylor(low)+tail(low)), 1/(taylor(high)-tail(high))


def exp_step(phases, exps, n):
    return total(scale(math.comb(n, j), mul(phases[j+1], exps[n-j]))
                 for j in range(n+1))


def recip_step(exps, recips, n):
    return mul(sub(ZERO, total(scale(math.comb(n+1, j+1),
                                    mul(exps[j+1], recips[n-j]))
                               for j in range(n+1))), inv(add(ONE, exps[0])))


def product_slot(exps, recips, n):
    return total(scale(math.comb(n, j), mul(exps[j], recips[n-j]))
                 for j in range(n+1))


def certificate(index):
    cell = Q(8192+2047*index, 33554432), Q(8192+2047*(index+1), 33554432)
    phases = [phase(cell, n) for n in range(8)]
    k = 0
    while (1 << k) < -phases[0][0]:
        k += 1
    powers = [rounded(initial_exp(phases[0], k))]
    for _ in range(k):
        powers.append(rounded(mul(powers[-1], powers[-1])))
    exps = [powers[-1]]
    for n in range(7):
        exps.append(rounded(exp_step(phases, exps, n)))
    recips = [rounded(inv(add(ONE, exps[0])))]
    for n in range(7):
        recips.append(rounded(recip_step(exps, recips, n)))
    prices = {}
    for n in (4, 7):
        output = product_slot(exps, recips, n)
        prices[n] = math.ceil(4*WIDTH*max(abs(output[0]), abs(output[1]))*4096)
    cert = {"index": index, "k": k, "powers": powers, "exps": exps,
            "recips": recips, "prices": prices}
    assert contains(powers[0], initial_exp(phases[0], k))
    assert all(contains(powers[j+1], mul(powers[j], powers[j])) for j in range(k))
    assert all(contains(exps[n+1], exp_step(phases, exps, n)) for n in range(7))
    assert contains(recips[0], inv(add(ONE, exps[0])))
    assert all(contains(recips[n+1], recip_step(exps, recips, n)) for n in range(7))
    return cert


def signed_literal(value):
    return f"({value})" if value < 0 else str(value)


def box_literal(value):
    lo, hi = value[0]*DEN, value[1]*DEN
    assert lo.denominator == hi.denominator == 1
    return f"dyadic {signed_literal(lo.numerator)} {signed_literal(hi.numerator)}"


def cert_literal(c):
    lists = []
    for key in ("powers", "exps", "recips"):
        lists.append(f"{key} := [\n    " + ",\n    ".join(map(box_literal, c[key])) + "]")
    return "{ k := " + str(c["k"]) + ",\n  " + ",\n  ".join(lists) + \
           f",\n  price4 := {c['prices'][4]}, price7 := {c['prices'][7]} }}"


HEADER = """import ConnesWeilRH.Dev.C1SeedIntegralCertificate3100

namespace ConnesWeilRH.Dev.C1SeedCertificate3101
open C1SeedCertificate3098
set_option maxRecDepth 100000
set_option linter.style.longLine false
section
set_option maxHeartbeats 8000000
set_option Elab.async false

"""


def write_pilot():
    indices = (0, 1249, 2010, 8191)
    lines = [HEADER]
    readings = []
    for index in indices:
        c = certificate(index)
        name = f"cell{index:04d}"
        lines += [f"def {name} : Certificate :=\n" + cert_literal(c) + "\n",
                  f"theorem {name}_checked : checkCell {index} {name} = true := by decide +kernel\n",
                  f"theorem {name}_integral4 :\n"
                  f"    4 * (∫ x in (endpoint {index})..(endpoint {index+1}),\n"
                  f"      ‖iteratedDeriv 4 Real.smoothTransition x‖) ≤ ({c['prices'][4]} : Real) / 4096 :=\n"
                  f"  by simpa [price, {name}] using\n"
                  f"    cell_integral_le_price {index} {name} (of_decide_eq_true {name}_checked) 4 (Or.inl rfl)\n",
                  f"theorem {name}_integral7 :\n"
                  f"    4 * (∫ x in (endpoint {index})..(endpoint {index+1}),\n"
                  f"      ‖iteratedDeriv 7 Real.smoothTransition x‖) ≤ ({c['prices'][7]} : Real) / 4096 :=\n"
                  f"  by simpa [price, {name}] using\n"
                  f"    cell_integral_le_price {index} {name} (of_decide_eq_true {name}_checked) 7 (Or.inr rfl)\n"]
        readings.append({"index": index, "scaling_squares": c["k"], "price_units": c["prices"]})
    lines.append("end\nend ConnesWeilRH.Dev.C1SeedCertificate3101\n")
    output = ROOT / "ConnesWeilRH/Dev/C1SeedCertificatePilot3101.lean"
    output.write_text("\n".join(lines), encoding="utf-8")
    print(json.dumps({"pilot": readings, "source_bytes": output.stat().st_size}, indent=2))


def write_all():
    folder = ROOT / "ConnesWeilRH/Dev/SeedCertificates3101"
    folder.mkdir(exist_ok=True)
    sums = {4: 0, 7: 0}
    chunks = []
    for start in range(0, COUNT, CHUNK):
        index = start // CHUNK
        cs = [certificate(i) for i in range(start, start+CHUNK)]
        name = f"chunk{index:03d}"
        lines = [HEADER]
        cell_names = []
        for c in cs:
            cname = f"cert{c['index']:04d}"
            cell_names.append(cname)
            lines += [f"def {cname} : Certificate :=\n" + cert_literal(c) + "\n",
                      f"theorem {cname}_checked : checkCell {c['index']} {cname} = true := by decide +kernel\n"]
        lines += [f"def {name} : List Certificate := [\n  " +
                  ",\n  ".join(cell_names) + "]\n",
                  f"theorem {name}_checked : checkCells {start} {name} = true := by\n"
                  "  simp only [" + ", ".join([name, "checkCells", "Nat.reduceAdd"] +
                    [cname + "_checked" for cname in cell_names] + ["Bool.true_and"]) + "]\n",
                  f"theorem {name}_length : {name}.length = {CHUNK} := by decide\n"]
        subtotals = {}
        for n in (4, 7):
            subtotal = sum(c["prices"][n] for c in cs)
            sums[n] += subtotal
            subtotals[n] = subtotal
            lines.append(f"theorem {name}_price{n} : totalPrice {name} {n} = {subtotal} := by decide\n")
        lines.append("end\nend ConnesWeilRH.Dev.C1SeedCertificate3101\n")
        output = folder / f"Chunk{index:03d}.lean"
        output.write_text("\n".join(lines), encoding="utf-8")
        chunks.append({"chunk": index, "start": start, "count": CHUNK,
                       "units": subtotals, "source_sha256": hashlib.sha256(
                           output.read_bytes().replace(b"\r\n", b"\n")).hexdigest()})
        if index % 8 == 0:
            print(f"generated {start+CHUNK}/{COUNT}", flush=True)
    assert sums[4]+4096 < 1500*4096 and sums[7]+4096 < 2000000000*4096
    report = {"record": 3101, "status": "EXACT_RATIONAL_WITNESSES_GENERATED",
              "cells": COUNT, "chunk_size": CHUNK, "dyadic_bits": 256,
              "units_denominator": 4096, "price_units": sums, "chunks": chunks,
              "generator_sha256": hashlib.sha256(
                  Path(__file__).read_bytes().replace(b"\r\n", b"\n")).hexdigest(),
              "scope": "Candidate data only; Lean kernel checks are required."}
    (ROOT / "results/3101_seed_certificate_generation.json").write_text(
        json.dumps(report, indent=2)+"\n", encoding="utf-8")
    write_aggregate(sums)
    print(json.dumps({"cells": COUNT, "exact_prices": {n: str(Q(s,4096)) for n,s in sums.items()}}))


def write_aggregate(sums):
    names = [f"chunk{i:03d}" for i in range(COUNT // CHUNK)]
    lines = [f"import ConnesWeilRH.Dev.SeedCertificates3101.Chunk{i:03d}"
             for i in range(COUNT // CHUNK)]
    lines += ["import ConnesWeilRH.Dev.C1SeedDerivativeReflection3102", "",
              "namespace ConnesWeilRH.Dev.C1SeedCertificate3101",
              "open C1SeedCertificate3098",
              "open ConnesWeilRH.Source.C1ExplicitSmoothSeed",
              "open ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection",
              "set_option maxRecDepth 100000",
              "set_option linter.style.longLine false", "",
              "def allCells : List Certificate :=\n  " + " ++\n  ".join(names), "",
              "theorem allCells_length : allCells.length = 8192 := by",
              "  norm_num only [allCells, List.length_append, " +
              ", ".join(n + "_length" for n in names) + "]",
              "",
              "set_option maxHeartbeats 8000000 in",
              "theorem allCells_checked : checkCells 0 allCells = true := by",
              "  simp only [allCells, checkCells_append, List.length_append, Nat.reduceAdd, " +
              ", ".join(n + "_length" for n in names) + ", " +
              ", ".join(n + "_checked" for n in names) + ", Bool.true_and]", ""]
    for order in (4, 7):
        lines += [f"theorem allCells_price{order} : totalPrice allCells {order} = {sums[order]} := by",
                  "  norm_num only [allCells, totalPrice_append, " +
                  ", ".join(n + f"_price{order}" for n in names) + "]",
                  ""]
    for order, target, word in ((4, 1500, "four"), (7, 2000000000, "seven")):
        lines += [f"theorem transition_integral_{word}_lt3103 :",
                  "    4 * (∫ x in (0 : Real)..(1 / 2),",
                  f"      ‖iteratedDeriv {order} Real.smoothTransition x‖) < ({target} : Real) := by",
                  "  apply checked_full_integral_lt allCells allCells_length allCells_checked",
                  f"    {order} (by omega) {target}",
                  f"  rw [allCells_price{order}]", "  norm_num", "",
                  f"theorem smoothSeed_derivOrderL1_{word}_lt3103 :",
                  f"    derivOrderL1 {order} smoothSeed < ({target} : Real) := by",
                  f"  rw [derivOrderL1_smoothSeed_eq_half_integral3102 {order} (by norm_num)]",
                  f"  exact transition_integral_{word}_lt3103", ""]
    lines += ["theorem smoothSeed_d4_d7_bounds3103 :",
              "    derivOrderL1 4 smoothSeed < (1500 : Real) ∧",
              "      derivOrderL1 7 smoothSeed < (2000000000 : Real) :=",
              "  ⟨smoothSeed_derivOrderL1_four_lt3103, smoothSeed_derivOrderL1_seven_lt3103⟩",
              "", "end ConnesWeilRH.Dev.C1SeedCertificate3101", ""]
    (ROOT / "ConnesWeilRH/Dev/C1SeedD4D7Certified3103.lean").write_text(
        "\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true")
    options = parser.parse_args()
    write_all() if options.all else write_pilot()
