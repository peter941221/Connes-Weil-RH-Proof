# 1391 — R1 route-alpha owner leaf FORMAL DONE (009 §5 item 2/4 discharge)

Date: 2026-09-13. Lane: FORMAL (Lean/Mathlib, lake build acceptance via log
readback). RH is NOT claimed anywhere in this record.

Predecessors: 1387 (margin consumer shape layer), 1389 (route-alpha recon —
the register this leaf instantiates), 1390 (discharge prereg v2, zero digits —
governs the `hfit`/`hJ1` confirmation that this leaf intentionally leaves as
hypotheses). 1388 is superseded by 1390 and must not be executed.

## 0. Verdict up front

GOOD: the R1 leaf compiles. `C1RouteAlphaOwner` delivers ONE owner carrying
the minimal healthy data, the normalization, the ROOT pinning support, and the
closed-form factorized L2 budget; the margin consumer chains on the same
owner; the gate-conditional promotion to `HealthyYoshidaDetectorData` is one
application of the record-1375 template. Acceptance:
`009_routealpha_try5.log` — `Build completed successfully (3686 jobs)`,
`^error` count 0, `sorryAx` count 0, `Quot.sound` prints 7/7, zero warnings
attributable to `C1RouteAlphaOwner` (the 178 log warnings are all upstream
replay noise). All seven `#print axioms` lines report exactly
`[propext, Classical.choice, Quot.sound]`.

What is NOT done here (by design, law 42 discipline): the archimedean gate
`harch` (inherited open science, records 1080/1081), the numeric confirmation
of `hfit`/`hJ1` (belongs to the 1390 rig, whose run precondition — this leaf —
is now satisfied), and any `C_min`/`δ`/rate digits.

## 1. What the leaf is (files and deliverables)

```text
ConnesWeilRH/Dev/C1RouteAlphaOwner.lean        (4 theorems + register defs)
ConnesWeilRH/Dev/C1RouteAlphaOwnerAudit.lean   (7 #print axioms)
```

+-------------------------------+-------------------------------------------+
| deliverable                   | content                                   |
+-------------------------------+-------------------------------------------+
| routeAlphaIndex / Nodes /     | the 4-node register `healthyDetectorNode- |
| BaseValue / _nonempty         | Set rho = {0, 1/2, 1, rho}` as `Finite-   |
|                               | MellinNode`, node map = `Subtype.val`     |
|                               | (injectivity free), base pattern = ones,  |
|                               | Nonempty via `0 ∈ set` by `simp`          |
+-------------------------------+-------------------------------------------+
| windowGramInverse_cost_re_    | `0 ≤ (star (G⁻¹.mulVec y) ⬝ᵥ y).re` —     |
| nonneg                        | solved-vector cost is a window integral   |
|                               | of a squared modulus (1383 identity +     |
|                               | 1384 pinned solve, then `integral_nonneg`)|
+-------------------------------+-------------------------------------------+
| exists_routeAlphaOwner        | THE R1 owner: `HealthyMinimalLaplaceRe-   |
|                               | alizes rho g` + `laplaceAt g rho = -1` +  |
|                               | `support g.test ⊆ Icc (-(log2/2)) (log2/  |
|                               | 2)` + `compactLogL2sq g ≤ (2*Ru) · ((1+   |
|                               | ε')·K_u) · ((1+ε)·K_f)`; single numeric   |
|                               | side condition `Ru + Rf ≤ log 2 / 2`      |
+-------------------------------+-------------------------------------------+
| exists_routeAlphaOwner_       | same owner through `margin_pos_of_owner_- |
| margin_pos                    | cost_fits` (1387): FIT + (J1) ⇒ `0 < δ/2  |
|                               | - Cmin · compactLogL2sq g` on the healthy |
|                               | owner — the component-5 endpoint          |
+-------------------------------+-------------------------------------------+
| healthyDetectorData_of_       | 009 §5 item 4 wiring: 1375 promotion tem- |
| routeAlphaOwner               | plate consumed through the ROOT pinning   |
|                               | lemma; gated on `harch` (the inherited    |
|                               | open sign — not claimed, never claimed)   |
+-------------------------------+-------------------------------------------+

## 2. The three design decisions that made it work

A. Value split (1389 §7 recipe, item (a)). The xi-side owner `u` takes the
all-ones pattern `routeAlphaBaseValue`; the taper owner takes the
concentrated pattern `healthyDetectorNodeTarget rho = (0, 0, 0, -1)`. Record
1386's multiplicative value law `laplaceAt g z = laplaceAt u z * y z` then
reproduces the register target exactly (`rw [h2, one_mul]` closes it — see
trap T3). Both owners come from the record-1385 wrapper with
`nodes = Subtype.val` — injectivity is FREE for the subtype enumeration, which
retires 1385's anticipated Injective obligation entirely.

B. Pinning via one numeric side condition (item (c)). The assembly window is
`Ioo (-Ru-Rf) (Ru+Rf)` after the `ring` rewrite `(-Ru)+(-Rf) = -(Ru+Rf)`;
`Ioo ⊆ Icc(-(log2/2)) (log2/2)` is exactly `Ru + Rf ≤ log 2 / 2` — the hard
constraint of 1389 §4, now encoded as a theorem hypothesis (law F8's
corollary: constraint as gate, not hope).

C. Budget chain needs the nonneg lemma (item (d)). 1386 exports
`‖g‖² ≤ (d-c) · ‖u‖² · E_f`; multiplying `‖u‖² ≤ (1+ε')·K_u` through requires
`0 ≤ E_f = (1+ε)·K_f`, and `K_f ≥ 0` is NOT automatic from the Gram API — it
is a per-value-pattern fact, supplied by `windowGramInverse_cost_re_nonneg`.
This is the only genuinely new analytic line in the leaf, and it is 1383/1384
machinery re-pointed at the solved vector.

## 3. Build evidence trail (try1 → try5)

```text
try1  15 error lines: missing [DecidableEq ι] (matrix inversion); nine sites
      where the value function was applied INSIDE the isUnit paren group
      ("Function expected ... this term has type IsUnit (...)"); hvalues left
      `laplaceAt u z` unconsumed.
try2  paren-count class: named function arg `(X rho)` carries its OWN closing
      paren, the template's bare `y` does not — every site needed arg1 with
      THREE `)` (self + mulVec + star) and `.re` with exactly TWO closes;
      the statement also had `.re))` over-closing by one before `:= by`.
      (Found by dumping ALL `^error` lines with literal paths, not the first.)
try3  single error: `rw [← hre]` — wrong direction plus congrArg does NOT
      reduce `.re` under the integral; replaced with 1385's compiled idiom
      `rw [← hqz, integral_norm_sq_re]` (orient the quadratic as
      integral = dot; `ofReal_pow` defeq absorbs the cast placement).
try4  died mid-file: the foreground `wsl.exe` session was cut (localhost-
      proxy flake) and the lake child took SIGHUP — log truncated with no
      completion marker (SILENT FAKE-EMPTY reconfirmed: absence of evidence
      is worse than fake zeros).
try5  detached via `setsid nohup bash run_try5.sh &` — GREEN (see §0).
```

## 4. Traps hardened (written to AGENTS.md §7b/§7l)

T1  Nested-quote variable death: `\$L` inside `wsl.exe -- bash -c "..."`
    silently expanded to EMPTY twice today (readback commands printed bare
    `0`s / empty output that LOOKED like a healthy grep). Law re-confirmed:
    literal paths in EVERY nested command, no exceptions for "trivial" vars.
T2  `cmd1 && cmd2 && setsid prog & echo LAUNCHED` backgrounds the WHOLE &&
    chain — if the launcher bash exits, setup dies before the script exists.
    Two-call pattern: (i) foreground write+verify script, (ii) separate
    `setsid nohup bash script > /dev/null 2>&1 < /dev/null &` + sentinel file.
T3  `simp only [...] at h1 h2 ⊢` does NOT always finish multiplicative
    normalizations: `one_mul` had to be fired explicitly with `rw [h2, one_mul]
    at h1` after the substitution hypothesis `h2 : laplaceAt u z = 1` was
    produced.
T4  isUnit-inversion spelling (1387 byte-identical-mirroring law, refined):
    the paren shape of `↑(windowExpGramMatrix_isUnit_of_injective hab nodes
    hne).unit⁻¹` must be copied at TERM level, not "same idea" — one
    misplaced `)` turns `dotProduct` into a partial application and the error
    surfaces far away as `HMul ℝ ((? → ?) → ?)`.

## 5. What this unlocks

009 §5 item status after this leaf:

```text
item 1  prereg 1390 (zero digits)                  COMMITTED (1390)
item 2  R1 leaf, hfit-shaped budget on one owner   FORMAL DONE (this record)
item 3  1390 rig digits: confirm hfit + (J1)       OPEN — precondition MET
item 4  healthy-data wiring via the IFF            FORMAL DONE (gate-conditional)
item 5  archimedean gate sign                      OPEN, inherited science (NOT N2β)
```

The rig (item 3) is now runnable exactly as prereg'd: compute on the
1390 §1 closed forms (split value patterns, `G_00 = 2R` branch, `C_C`, `C_D`),
grid of §2 (25 cells, admissible by construction), gates G0–G6, DONE sentinel
`DONE gates=G0:PASS,...`. No grid or gate may be edited to reach a PASS
(law 42).
