#!/usr/bin/env python3
"""Record 2722F generator: exact capture of the stored row-B witness data.

This lane (reopen-motion audit under the map-103 freeze) turns the three
finite-data hypotheses of
`ConnesWeilRH.Source.C1RowBCardinalCarrier2722D.fourPointContradictionRowBCarrier2722D`
(`hsub`, `htri`, `hy`) into proved theorems about CONCRETE captured data:
the record-1980 stored row-B configuration at candidate `CANDIDATES[1]`
(`gamma_2 = 21.022039638771556`, `re = 0.55`, `N = 5`): the 8 healthy
targets, the 56-node owner, the stored correction values and the formal
radius.  All binary64 values are exact dyadic rationals, so the capture
carries zero error radius.

Modes:
  --selftest   re-derive the row-B data, assert the structural facts, print
               the payload and exit (no files written)
  (default)    emit C1RowBStoredCapture2722F.lean, its paired Audit module,
               and the data payload results/2722f_rowB_capture_data.json

Shapes:
  --neg-shape=absurd (default) negation lemmas closed by
                     `intro h; exact absurd (congrArg Complex.im h)
                      (by norm_num)` -- probe-verified for all nine
                     instances and the `if_neg` chain (2026-10-17)
  --neg-shape=norm   bare `norm_num` (FALSIFIED by the probe: leaves the
                     nine negation goals unsolved; kept for replay only)

Run with the WSL python (3.12.3 / numpy 2.5.3 / mpmath 1.4.1), the same
engine as the committed 2720 / 2722C / 2722E runs, so the float decode is
bitwise the one those artifacts certified.
"""

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import fourpoint_actual_owner_1980 as op  # noqa: E402

GAMMA = 21.022039638771556
RE = 0.55
NCUT = 5
MAXLINE = 100

TRIPLE_SPELL = {Fraction(1, 2): "(1 / 2 : ℂ)", Fraction(1): "(1 : ℂ)",
                 Fraction(3, 2): "(3 / 2 : ℂ)"}
TRIPLE_ORDER = ["(1 / 2 : ℂ)", "(1 : ℂ)", "(3 / 2 : ℂ)"]
TRIPLE_SHORT = ["Half", "One", "ThreeHalf"]
NODE_SHORT = ["Rho", "Omc", "Rph"]


def fr_of(v: float) -> str:
    n, d = float(v).as_integer_ratio()
    return str(Fraction(n, d))


def rat(v: float) -> str:
    """Exact dyadic literal of a binary64 value, house capture spelling."""
    n, d = float(v).as_integer_ratio()
    if d == 1:
        return f"({n} : ℝ)"
    return f"(({n} : ℝ) / {d})"


def cplx(z) -> str:
    """Complex literal; shifted-CC20 triple points keep the parent spelling."""
    re, im = float(z.real), float(z.imag)
    f = Fraction(*float(re).as_integer_ratio())
    if im == 0.0 and f in TRIPLE_SPELL:
        return TRIPLE_SPELL[f]
    return f"⟨{rat(re)}, {rat(im)}⟩"


class RowData:
    """The stored row-B configuration (record-1980 builders)."""

    def __init__(self):
        rho = complex(RE, GAMMA)
        owner, targets, radius, known = op.build_owner(rho, NCUT)
        owner = [complex(z) for z in owner]
        targets = [complex(z) for z in targets]
        values = [complex(op.target_value(rho, z)) for z in owner]
        self.rho, self.owner, self.targets = rho, owner, targets
        self.values, self.radius, self.known = values, radius, known
        self.specials = [rho, 1.0 - rho.conjugate(), rho + 0.5]
        assert len(targets) == 8 and len(owner) == 56 and len(known) == 48
        self.spec_idx = [owner.index(z) for z in self.specials]
        assert self.spec_idx == [48, 49, 52], self.spec_idx
        assert [values[i] for i in self.spec_idx] == \
               [complex(1), complex(-1), complex(-1)]
        self.tri_idx = [owner.index(complex(x)) for x in (0.5, 1.0, 1.5)]
        assert self.tri_idx == [53, 54, 55], self.tri_idx
        self.tgt_idx = [owner.index(t) for t in targets]
        assert self.tgt_idx == [48, 49, 50, 51, 52, 53, 54, 55], self.tgt_idx
        # the ite specials are the only nonzero values, matched exactly
        nonzero = [i for i, v in enumerate(values) if v != 0j]
        assert nonzero == self.spec_idx, nonzero
        for z, v in zip(owner, values):
            dmin = min(abs(z - s) for s in self.specials)
            if dmin > 1e-10:
                assert v == 0j
            else:
                assert dmin == 0.0, (z, dmin)

    def payload(self):
        return {
            "schema": "2722F_ROWB_CAPTURE_DATA_V1",
            "source_scripts": ["fourpoint_actual_owner_1980.py",
                               "p3_certified_strip_constants_2720.py"],
            "candidate": {"gamma": repr(GAMMA), "re": repr(RE), "N": NCUT},
            "rho": [fr_of(self.rho.real), fr_of(self.rho.imag)],
            "radius": fr_of(self.radius),
            "targets": [[fr_of(z.real), fr_of(z.imag)] for z in self.targets],
            "owner": [[fr_of(z.real), fr_of(z.imag)] for z in self.owner],
            "values": [[fr_of(v.real), fr_of(v.imag)]
                       for v in self.values],
            "spec_idx": self.spec_idx,
            "tri_idx": self.tri_idx,
            "target_owner_index": self.tgt_idx,
            "known_count": len(self.known),
        }


def pair_block(entry: str, ind: str) -> list[str]:
    """One Finset entry as line(s); pairs break after the real part."""
    if entry.startswith("⟨"):
        re_p, im_p = entry[1:-1].split(", ", 1)
        return [f"{ind}⟨{re_p},", f"{ind}    {im_p}⟩"]
    return [f"{ind}{entry}"]


def emit_finset(name: str, entries: list[str]) -> list[str]:
    lines = [f"def {name} : Finset ℂ :=", "  {"]
    for k, e in enumerate(entries):
        if k > 0:
            lines[-1] = lines[-1] + ","
        lines.extend(pair_block(e, "  "))
    lines[-1] = lines[-1] + "}"
    return lines


def subset_theorem(name: str, sub: str, sup: str, idxs: list[int],
                   sup_len: int) -> list[str]:
    """`sub ⊆ sup` by simp-unfold, rcases over sub, apply-chain over sup.

    The sup literal unfolds to nested `Finset.insert` ending in the
    singleton `{last}`, so the LAST disjunct is a bare equality and no
    `Or.inl` applies there; every other position is a left disjunct of an
    `Or`.
    """
    simp = f"  simp only [{sub}, {sup}, Finset.mem_insert,"
    lines = [f"theorem {name} :", f"    {sub} ⊆ {sup} := by",
             "  intro x hx", simp, "    Finset.mem_singleton] at hx ⊢",
             "  rcases hx with (" + "|".join(["rfl"] * len(idxs)) + ")"]
    for j in idxs:
        first = True

        def emit(s: str, _f=[0]) -> None:
            nonlocal first
            lines.append(("  · " if first else "    ") + s)
            first = False

        for _ in range(j):
            emit("apply Or.inr")
        if j < sup_len - 1:
            emit("apply Or.inl")
        emit("exact rfl")
    return lines


def split_pair(n: str) -> list[str]:
    """`⟨re, im⟩` -> [re_part, im_part]."""
    return n[1:-1].split(", ", 1)


def emit_ydef(triples: list[tuple[str, str]]) -> list[str]:
    """The `storedY2722F` ite-chain def, node literals split across lines.

    Each condition is `z = (⟨re, im⟩ : ℂ)`; the continuation lines sit
    deeper than the opening bracket (record-2634 structure-indent law).
    """
    lines = ["def storedY2722F : ℂ → ℂ :=", "  fun z =>"]
    for k, (n, v) in enumerate(triples):
        re_p, im_p = split_pair(n)
        kw = "if" if k == 0 else "else if"
        lines.append(f"    {kw} z =")
        lines.append(f"      (⟨{re_p},")
        lines.append(f"        {im_p}⟩ : ℂ) then")
        lines.append(f"      {v}")
    lines.append("    else 0")
    return lines


def neg_theorems(tri: list[str], nodes: list[str], shape: str) -> list[str]:
    """The nine `triple ≠ node` refutations (imaginary part separates).

    The node literal is emitted across lines so every line respects the
    100-column style linter; the `¬(...)` body elaborates to the same
    condition as the unfolded `storedY2722F` ite.
    """
    lines = []
    for a, z in enumerate(tri):
        for b, n in enumerate(nodes):
            nm = f"storedNe{TRIPLE_SHORT[a]}{NODE_SHORT[b]}2722F"
            re_p, im_p = split_pair(n)
            lines.append(f"theorem {nm} :")
            lines.append(f"    ¬(({z} : ℂ) =")
            lines.append(f"      (⟨{re_p},")
            lines.append(f"        {im_p}⟩ : ℂ))")
            if shape == "norm":
                lines[-1] = lines[-1] + " := by norm_num"
            else:
                lines[-1] = lines[-1] + " := by"
                lines.append("    intro h")
                # `norm_num at him` would close the goal itself, so the
                # trailing `exact him` is dead code; the absurd form keeps
                # the norm_num as a term and is probe-verified.
                lines.append("    exact absurd (congrArg Complex.im h)"
                             " (by norm_num)")
            lines.append("")
    return lines


def hy_theorem() -> list[str]:
    lines = ["theorem storedYVanishes2722F :",
             "    ∀ s ∈ shiftedCC20Triple2722D, storedY2722F s = 0 := by",
             "  intro s hs",
             "  simp only [shiftedCC20Triple2722D, Finset.mem_insert,",
             "    Finset.mem_singleton] at hs",
             "  rcases hs with (rfl|rfl|rfl)"]
    for a in range(3):
        nms = [f"storedNe{TRIPLE_SHORT[a]}{NODE_SHORT[b]}2722F"
               for b in range(3)]
        lines.append("  · simp only [storedY2722F]")
        # one `if_neg` per rw entry; split lines to respect the 100-col
        # style linter for the longest (ThreeHalf) name triple
        lines.append(f"    rw [if_neg {nms[0]},")
        lines.append(f"      if_neg {nms[1]},")
        lines.append(f"      if_neg {nms[2]}]")
    return lines


HEADER = """\
/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1RowBCardinalCarrier2722D
"""

DOCBLOCK = """\
/-
# Record 2722F: exact capture of the stored row-B witness data

The 2722E screen decided the finite-data legs of the reopen motion on the
stored row-B configuration at model grade; this record makes them Lean
theorems.  The stored binary64 lists (8 healthy targets, the 56-node owner,
the correction values and the formal radius at `gamma_2 = 21.022039638771556`,
`re = 0.55`, `N = 5`) are exact dyadic rationals, so the capture carries no
error radius: every literal below is the exact value of the stored float.

Proved here with zero premises: `storedTripleSubset2722F`
(`{1/2, 1, 3/2} ⊆ storedTargets2722F`), `storedTargetsSubset2722F`
(`storedTargets2722F ⊆ storedNodes2722F`), and `storedYVanishes2722F`
(`storedY2722F = 0` on the shifted triple).  The stored correction function
`storedY2722F` is `1` at the node `rho`, `-1` at `1 - conj rho` and at
`rho + 1/2`, and `0` elsewhere (the record-1980 `target_value` table, tied
by the generator payload `results/2722f_rowB_capture_data.json`).

`fourPointContradictionRowBStored2722F` is the 2722D contradiction
instantiated at this data: the three finite-data hypotheses are discharged,
and the concrete lists, radius and value function are definitions instead
of quantified arguments.  What remains named (seven hypotheses): the rho
caps, the three cardinal-sum pins (artifact-grade support: the 2722E
screen; Lean certification is the next brick), and `hgate24` / `hprefix`
(the RH core under the map-103 freeze).  `rho` stays a named carrier point.

Honesty line: this record does not discharge any pin, the gate or the
prefix; `wired_hypotheses_removed = 3` counts only the finite data legs.
No producer GO, no RH claim; the `DEAD_ON_CURRENT_FAMILY` freeze is
unchanged.
-/
"""

OPENS = """
namespace ConnesWeilRH
namespace Source
namespace C1RowBStoredCapture2722F

open Matrix
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open ConnesWeilRH.Dev.C1C3CarrierTransport
open C1ArchimedeanIntegrabilityGeneric
open C1CenterTwoCriterionBridge
open C1GateMatrixRepresentation
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1LocalConfigurationDomination
open C1OrbitWindowSemiLocalGate
open C1SpectralWeil
open C1SpectralTailBound
open C1SpectralSummability
open C1SameOwnerWeil
open C1TwoPointSpectralDecomposition
open C1FourPointSpectralPrefixTransport
open C1FourPointHighShellTail
open C1FourPointSpanGateCertificate
open C1SignedVarianceIdentity
open C1BipartiteMeanGapCertificate
open C1FourPointContradictionAssembly
open C1FourPointRowBWired2721
open C1ExplicitFiniteNodeCorrection
open C1StripTransport2722C
open C1RowBCardinalCarrier2722D
open scoped BigOperators

noncomputable section
"""

ENDS = """
end
"""


def pin_binders() -> list[str]:
    """The three pin binders at the captured data (verbatim shapes)."""
    return [
        "    (hcontractPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,",
        "        64 ≤ |t| →",
        "          ‖cardinalSum storedTargets2722F (explicitSeed",
        "            storedRadius2722F storedHRadius2722F) (fun _ => 1)",
        "            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤",
        "            wiredQRowB2721)",
        "    (hquarticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,",
        "        ‖t / (2 * Real.pi)‖ ^ 4 * ‖cardinalSum storedTargets2722F",
        "          (explicitSeed storedRadius2722F storedHRadius2722F)",
        "          (fun _ => 1) ((sigma : Complex) + (t : Complex) *",
        "            Complex.I)‖ ≤ wiredC4RowB2721)",
        "    (hquadraticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,",
        "        ‖t / (2 * Real.pi)‖ ^ 2 * ‖cardinalSum storedNodes2722F",
        "          (explicitSeed storedRadius2722F storedHRadius2722F)",
        "          storedY2722F ((sigma : Complex) + (t : Complex) *",
        "            Complex.I)‖ ≤ wiredC2RowB2721)",
    ]


def gate_prefix_binders() -> list[str]:
    """Verbatim parent gate/prefix token structure, stored names substituted.

    The application `(carrierSourceTest2722D targets nodes r hr y)` becomes
    `(storedCarrierSourceTest2722F)` (parentheses mirrored; a dot accessor
    NEVER sits at end of line - record-2722D layout law).
    """
    C = "(storedCarrierSourceTest2722F)"
    return [
        "    (hgate24 : ICgate",
        "        ((fullFunctionalEquationOrbitAnnihilator",
        f"          {C} rho.1).convolutionSquare) -",
        "      24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator",
        f"          {C} rho.1).involution.convolution",
        f"            {C}) +",
        f"        ICgate ({C}.involution.convolution",
        "          (fullFunctionalEquationOrbitAnnihilator",
        f"            {C} rho.1))) +",
        "      24 ^ 2 * ICgate",
        f"        ({C}.convolutionSquare) ≤ 0)",
        "    (hprefix : (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,",
        "        spectralTerm",
        "          (annihilatorDetectorSpanVector",
        "            (fullFunctionalEquationOrbitAnnihilator",
        f"              {C} rho.1)",
        f"            {C} 24).convolutionSquare",
        "          z.1).re ≤",
        "      -((xiMultiplicity rho : Real) * 24 ^ 2)) :",
    ]


def main_theorem() -> list[str]:
    lines = ["/-- The 2722D row-B contradiction at the captured stored data.",
             "The finite-data legs `hsub` / `htri` / `hy` are the proved",
             "theorems above; `rho`, the caps, the three pins, the gate and",
             "the prefix stay named hypotheses. -/",
             "theorem fourPointContradictionRowBStored2722F",
             "    (rho : sourceNontrivialZeroSet)",
             "    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)",
             "    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)",
             ]
    lines.extend(pin_binders())
    lines.extend(gate_prefix_binders())
    lines.append("    False :=")
    lines.append("  fourPointContradictionRowBCarrier2722D storedTargets2722F")
    lines.append("    storedNodes2722F storedTargetsSubset2722F")
    lines.append("    storedTripleSubset2722F storedRadius2722F")
    lines.append("    storedHRadius2722F storedY2722F storedYVanishes2722F")
    lines.append("    rho hNorm hIm hcontractPin hquarticPin hquadraticPin")
    lines.append("    hgate24 hprefix")
    return lines


def build_module(rd: RowData, neg_shape: str) -> str:
    t_lit = [cplx(z) for z in rd.targets]
    n_lit = [cplx(z) for z in rd.owner]
    rho_lit, omc_lit, rph_lit = (n_lit[i] for i in rd.spec_idx)
    rad_lit = rat(rd.radius)

    lines: list[str] = []
    lines.append(HEADER.rstrip("\n"))
    lines.append("")
    lines.append(DOCBLOCK.rstrip("\n"))
    lines.append(OPENS.rstrip("\n"))
    lines.append("")
    lines.append(f"/-- Exact dyadic literal of the stored formal radius "
                 f"{rd.radius!r}. -/")
    lines.append("def storedRadius2722F : ℝ :=")
    lines.append(f"  {rad_lit}")
    lines.append("")
    lines.append("theorem storedHRadius2722F : 0 < storedRadius2722F := by")
    lines.append("  norm_num [storedRadius2722F]")
    lines.append("")
    lines.append("/-- The stored row-B healthy targets (record-1980")
    lines.append("`healthy_targets`). -/")
    lines.extend(emit_finset("storedTargets2722F", t_lit))
    lines.append("")
    lines.append("/-- The stored row-B owner (record-1980 `build_owner`: 48")
    lines.append("known ball zeros, the orbit, and the targets). -/")
    lines.extend(emit_finset("storedNodes2722F", n_lit))
    lines.append("")
    lines.append("/-- The stored correction value function (record-1980")
    lines.append("`target_value`): `1` at `rho`, `-1` at `1 - conj rho` and")
    lines.append("`rho + 1/2`, zero elsewhere. -/")
    lines.extend(emit_ydef([(rho_lit, "(1 : ℂ)"), (omc_lit, "(-1 : ℂ)"),
                            (rph_lit, "(-1 : ℂ)")]))
    lines.append("")
    lines.append("/-! ## The captured finite-data legs -/")
    lines.append("")
    lines.extend(neg_theorems(TRIPLE_ORDER, [rho_lit, omc_lit, rph_lit],
                              neg_shape))
    lines.extend(subset_theorem("storedTripleSubset2722F",
                                "shiftedCC20Triple2722D",
                                "storedTargets2722F",
                                [rd.targets.index(complex(x))
                                 for x in (0.5, 1.0, 1.5)], len(t_lit)))
    lines.append("")
    lines.extend(subset_theorem("storedTargetsSubset2722F",
                                "storedTargets2722F", "storedNodes2722F",
                                rd.tgt_idx, len(n_lit)))
    lines.append("")
    lines.extend(hy_theorem())
    lines.append("")
    lines.append("/-! ## The carrier instance and the captured contradiction -/")
    lines.append("")
    lines.append("def storedCarrierSourceTest2722F : CompactLogTest :=")
    lines.append("  carrierSourceTest2722D storedTargets2722F storedNodes2722F")
    lines.append("    storedRadius2722F storedHRadius2722F storedY2722F")
    lines.append("")
    lines.extend(main_theorem())
    lines.append("")
    lines.append(ENDS.rstrip("\n"))
    lines.append("end C1RowBStoredCapture2722F")
    lines.append("end Source")
    lines.append("end ConnesWeilRH")
    text = "\n".join(lines) + "\n"
    for i, ln in enumerate(text.split("\n")):
        assert len(ln) <= MAXLINE, (i + 1, len(ln), ln[:60])
    assert "sorry" not in text and "admit" not in text
    return text


AUDIT = """\
/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1RowBStoredCapture2722F

/-! Paired axiom audit for record 2722F (see the Dev module docstring). -/

#print axioms ConnesWeilRH.Source.C1RowBStoredCapture2722F.storedHRadius2722F
#print axioms ConnesWeilRH.Source.C1RowBStoredCapture2722F.storedTargetsSubset2722F
#print axioms ConnesWeilRH.Source.C1RowBStoredCapture2722F.storedTripleSubset2722F
#print axioms ConnesWeilRH.Source.C1RowBStoredCapture2722F.storedYVanishes2722F
#print axioms ConnesWeilRH.Source.C1RowBStoredCapture2722F.fourPointContradictionRowBStored2722F
"""


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    args = sys.argv[1:]
    neg_shape = "absurd"
    for a in args:
        if a.startswith("--neg-shape="):
            neg_shape = a.split("=", 1)[1]
        elif a not in ("--selftest",):
            print(f"unknown argument {a}")
            return 2
    rd = RowData()
    payload = rd.payload()
    if "--selftest" in args:
        print(json.dumps(payload, indent=1, sort_keys=True))
        print("SELFTEST OK")
        return 0
    dev = ROOT / "ConnesWeilRH" / "Dev"
    mod = dev / "C1RowBStoredCapture2722F.lean"
    audit = dev / "C1RowBStoredCapture2722FAudit.lean"
    text = build_module(rd, neg_shape)
    with open(mod, "w", newline="\n", encoding="utf-8") as fh:
        fh.write(text)
    with open(audit, "w", newline="\n", encoding="utf-8") as fh:
        fh.write(AUDIT)
    payload["modules"] = {
        "C1RowBStoredCapture2722F.lean": sha256(mod),
        "C1RowBStoredCapture2722FAudit.lean": sha256(audit),
    }
    payload["provenance"] = {
        "generator": "scripts/generate_rowB_capture_2722f.py",
        "generator_sha256": sha256(Path(__file__).resolve()),
        "neg_shape": neg_shape,
        "engine": "fourpoint_actual_owner_1980.build_owner/target_value",
    }
    res = ROOT / "results"
    res.mkdir(exist_ok=True)
    out = res / "2722f_rowB_capture_data.json"
    with open(out, "w", newline="\n", encoding="utf-8") as fh:
        json.dump(payload, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("wrote:", mod.name, audit.name, out.name)
    print("module sha256:", payload["modules"]["C1RowBStoredCapture2722F.lean"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
