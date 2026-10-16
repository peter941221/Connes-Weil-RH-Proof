# 2722F — Stored row-B witness data captured as exact Lean data; hsub/htri/hy PROVED at the capture (2722F-ROWB-CAPTURE-CHECK-GREEN; three finite-data premises removed; zero RH-core premises touched)

Verdict: the record-2722E screen's finite-data legs are now theorems.
The stored row-B configuration (`gamma_2 = 21.022039638771556`,
`re = 0.55`, `N = 5`: the 8 healthy targets, the 56-node owner, the
correction value table, and the formal radius) is imported into
`ConnesWeilRH.Source.C1RowBStoredCapture2722F` as exact dyadic
literals — binary64 values are dyadic rationals, so the capture
carries NO error radius. Three theorems are proved there with zero
premises:

```
storedTripleSubset2722F :  shiftedCC20Triple2722D ⊆ storedTargets2722F
storedTargetsSubset2722F : storedTargets2722F ⊆ storedNodes2722F
storedYVanishes2722F    :  ∀ s ∈ shiftedCC20Triple2722D,
                              storedY2722F s = 0
```

`fourPointContradictionRowBStored2722F` is the 2722D contradiction
instantiated at this data: the carrier arguments (targets, nodes,
radius, `y`) become definitions, and the three finite-data
hypotheses `hsub` / `htri` / `hy` are discharged by the theorems
above — the first premise removals since 2721C on this lane
(`wired_hypotheses_removed = 3`). What remains named is exactly the
seven-hypothesis core declared by 2722D: the `rho` caps (`hNorm`,
`hIm`), the three cardinal-sum pins (`hcontractPin`, `hquarticPin`,
`hquadraticPin`), and `hgate24` / `hprefix` (the RH core under the
map-103 freeze). `rho` itself stays a named carrier point; no pin,
the gate, or the prefix is discharged. No producer GO, no RH claim,
`DEAD_ON_CURRENT_FAMILY` unchanged.

Lean build green (footer 3867 jobs; 0 lines starting `error:`, 0
sorry, 0 warnings on the two entry files; five-declaration axiom
census exactly `[propext, Classical.choice, Quot.sound]` — all
values carried in the check artifact's B-lane, not in a run log).
Checker `scripts/check_rowB_capture_2722f.py`, 22/22 GREEN
(`results/2722f_rowB_capture_check.json`), tying every emitted
literal to the payload in exact rational arithmetic, verifying the
main-theorem binder set and application sequence, and firing four
feasibility-checked mutation controls.

## 0. Binding-route audit (start-of-round declaration)

- Consumer: `fourPointContradictionRowBCarrier2722D` (record 2722D),
  reached from `fourPointContradictionRowBWired2722C` (2722C) and the
  untouched 2721C parent. Downstream chain: selected detector
  `qw < 0` -> same-owner `qw >= 0` -> `SourceRH` -> Mathlib RH. This
  record acts only on the reopen-motion premise list of the wired
  row-B contradiction, exactly as authorized by the 2722E routing
  decision ("witness node-list enumeration CLOSED on the finite-data
  legs; reopen obstruction is {hgate24, hprefix} + Lean-side pin
  certification/capture/seed-transfer bricks").
- Owner: the stored row-B configuration — the record-1980
  `build_owner` / `healthy_targets` / `target_value` lists for
  `CANDIDATES[1]`, the same data the 2722E screen machine-checked.
- Premises removed: `hsub`, `htri`, `hy` (logical count 10 -> 7).
- Failure criterion / stop: two modules, at most three record
  builds, one generator plus one checker; no pin certification, no
  gate/prefix motion; stop at verdict. Used: 2 builds (build 1
  failed on three tactic-shape defects, build 2 green).

## 1. What the capture is

- `storedRadius2722F` = the exact rational of the stored formal
  radius float (87.07226052...), with `storedHRadius2722F : 0 <
  storedRadius2722F` closed by `norm_num [storedRadius2722F]`.
- `storedTargets2722F` (8 entries) and `storedNodes2722F` (56
  entries) are `Finset ℂ` literals of the stored binary64 values
  decoded exactly (`as_integer_ratio`); the shifted CC20 triple
  keeps the parent's spelling `(1 / 2 : ℂ)`, `(1 : ℂ)`,
  `(3 / 2 : ℂ)` at target positions 5/6/7.
- `storedY2722F : ℂ → ℂ` is the classical `if`-chain equal to the
  record-1980 `target_value` table: `1` at `rho`, `-1` at
  `1 - conj rho`, `-1` at `rho + 1/2`, `0` elsewhere. Its guards are
  the three node literals themselves, so the table identity is
  definitional, not asserted.
- `storedCarrierSourceTest2722F` instantiates the 2722D
  `carrierSourceTest2722D` at the captured lists — the gate/prefix
  binder text mirrors the parent's parentheses token-for-token
  (record-2722D layout law).

The three proved legs:

```
targets (8)      == owner[48:56]           -> storedTargetsSubset2722F
triple {1/2,1,3/2} ⊆ targets (at 5,6,7)    -> storedTripleSubset2722F
y = 0 on the triple                        -> storedYVanishes2722F
```

`storedYVanishes2722F` is decided by nine `storedNe*2722F`
negation theorems (`triple point != node` — the imaginary parts
separate: the triple sits on the real axis, every special node has
imaginary part exactly `5917178117733711 / 281474976710656`), each
closed by `intro h; exact absurd (congrArg Complex.im h)
(by norm_num)`, then a `rcases`-on-disjunction elimination against
the `Finset.mem_insert`/`mem_singleton` unfolding.

## 2. Instrument findings (this round's tactic-shape probes)

- Bare `norm_num` does NOT refute `¬((1 / 2 : ℂ) =
  ⟨re, im⟩ record)` — it leaves all nine goals (build 1). The
  working shape routes through the imaginary-part projection
  (`congrArg Complex.im`), because the discriminating coordinate is
  `im`.
- `norm_num at h` on a false numeric equality CLOSES THE GOAL
  itself: a trailing `exact h` is dead code and fails with
  "No goals to be solved". A `norm_num`-in-term-position
  (`absurd ... (by norm_num)`) is the stable spelling.
- `x ∈ {e1, ..., en}` unfolds under simp to the right-nested
  disjunction `x = e1 ∨ (x = e2 ∨ ... ∨ x = en)` with NO trailing
  `x ∈ ∅` disjunct (mem_singleton + or_false collapse). Membership
  proofs must therefore use `(pos)` `Or.inr` + `Or.inl` + `rfl` for
  non-last positions but `(n-1)` `Or.inr` + BARE `exact rfl` for the
  last element — `apply Or.inl` there fails (the goal is no longer
  a disjunction). All shapes were machine-verified in a throwaway
  direct-`lean` probe before the second build.
- Build 1 also died on a transcribed-parentheses defect: the
  parent's `(carrierSourceTest2722D targets nodes r hr y) rho.1`
  parenthesization must be mirrored exactly, and no dot accessor
  may wrap across a line end (record-2722D law, third instance).

## 3. Evidence and honesty line

- Data payload: `results/2722f_rowB_capture_data.json` (schema
  `2722F_ROWB_CAPTURE_DATA_V1`; re-derives from
  `scripts/fourpoint_actual_owner_1980.py` under the same WSL
  python engine as the 2720/2722C/2722E runs).
- Check artifact: `results/2722f_rowB_capture_check.json` (schema
  `2722F_ROWB_CAPTURE_CHECK_V1`; P-lane payload ties, S-lane
  module-vs-payload transcription ties, K-lane mutation controls,
  B-lane build census with the log's sha256 bound for provenance).
- Generator: `scripts/generate_rowB_capture_2722f.py`
  (`--selftest` reproduces the data; module sha256
  `2244175cc4b92d483f07d8b9b746aae3dc8220a27c6035400e1a554bc1d6f2e7`).
- Checker: `scripts/check_rowB_capture_2722f.py`; its own sha256 is
  bound in the artifact — any later edit invalidates the binding and
  mandates a re-run.
- Lean: `ConnesWeilRH/Dev/C1RowBStoredCapture2722F.lean` and the
  paired `ConnesWeilRH/Dev/C1RowBStoredCapture2722FAudit.lean`
  (five `#print axioms` records).
- This record proves the finite-data legs ONLY. The three cardinal
  pins remain named hypotheses: their numeric support is the 2722E
  screen (artifact-grade), and their Lean certification is the next
  named brick. `xiMultiplicity`, `hgate24`, `hprefix` untouched.
  The capture is the STORED row-B configuration, not the actual
  selected detector; reopening map 103 still requires the full
  obstruction list of 2722E minus what this record discharged.
