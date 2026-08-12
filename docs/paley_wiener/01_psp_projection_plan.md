# 01 - PSP / Paley-Wiener Project: a nonzero element of the archimedean Sonin carrier

Status: OPEN, live target (docs/1000 steps 1/2/3). This is the gate for the
infinite-carrier Gate-3U `{2}` readout. RH NOT claimed. No new axiom / sorry.

**Milestone A DONE (2026-08-12).** `Dev/PaleyWindowProbe.lean` builds a concrete
nonzero radial window element `soninWindowIndicator` (constant `1` on
`(log lambda, log lambda + log 2)`, typed in `cc20GlobalLogCrossingL2`) and
proves `soninWindowIndicator_mem_radial` + `soninWindowIndicator_ne_zero`
(WSL `lake build ConnesWeilRH.Dev.PaleyWindowProbe` green, `#print
axioms=[propext, Classical.choice, Quot.sound]`, 0 sorry). Closes sub-target A.
Next: sub-target B (HT isometry assembly). sub-target C (band-limit /
Paley-Wiener-Titchmarsh element in `V_arch`) stays the honest new-analysis leaf.

## 0. Why this project exists

The whole route 1/2/3 (docs/1000) reduces to one analytic existence:

```text
archimedeanSoninCarrier_nontrivial lambda  :=  exists u, u : sourceSoninCarrier lambda
                                                with u != 0
V_arch(lambda)  =  Radial(lambda)  INTER  HT^-1( Radial(lambda) )
Radial(lambda)  =  { u : L2(R), u = 0 a.e. on (-inf, log lambda) }
```

Here `HT = ccm24ArchimedeanHardyTitchmarsh` (conveniently involutive isometry,
already in the repo). A nonzero element of `V_arch` reaching the window
`(log lambda, log lambda + log 2)` closes step 2/3, i.e. makes
`twoOuterNonzeroObligation` a real theorem.

Survey in docs/1000 found: no library witness, the exact `+-1`-eigenroute is
`L2`-void (scattering multiplier level-set thin), and the CompactLog "healthy"
world has no bridge to `sourceSoninCarrier`. So the only real construction is a
**continuous-spectrum band limit / Hardy ("PSP / prolate-spheroidal wave")**
element: a function that vanishes on the lower half-log-line and whose
Hardy-Titchmarsh image does too.

## 1. Decomposition into closeable sub-targets

We cut the load-bearing claim into pieces, each independently build/audit-able,
in dependency order. AN evidence gate is recorded per piece.

| # | Sub-target | Math | Depends on | Gate |
|---|-----------|------|-----------|------|
| A | `nonzeroRadialExists` : a concrete `L2` function `R` radial at `lambda` (vanishing below `log lambda`) with nonzero mass on `(log lambda, log+log2)` | explicit test function + Lp | setup | **DONE** (Dev/PaleyWindowProbe, 3317 jobs, axiom-clean) |
| B | `Hardy0norm` : the radial image `HT(R)` is a well-defined L2 element and cont. (handed to us) | HT isometry (in repo) | A | assembly |
| C | `Sonin_nonzero_cone` : some continuous band / projected element lies in `V_arch` and `!= 0` | Paley-Wiener / Titchmarsh / band-limit projection theorem (NEW to mathlib v4.30.0) | A,B - C is the honest new analysis | must be built with new math |
| D | "-bar coatoma" : that element has nonzero mass on the window | Consequence of the explicit construction | C | assemble |
| E | Lift `twoOuterNonzeroObligation` and flip AGENTS 998/999 to closed | coframe bridge (typed gate exists) | D | theorem |

Negative sub-targets (to be killed with a named guard if they fail): the exact
+-1 eigenspace construction (void); a "CompactLog-only" shortcut (no bridge).

## 3. Execution cadence

- Work top-down from the route consumer (the typed gate
  `twoOuterNonzero_gate_on_archwitness` in `Dev/SoninWindowWitness.lean`).
- Each sub-target: WSL isolate mirror `flock lake build <mod>` + `#print axioms`
  = `[propext, Classical.choice, Quot.sound]`, 0 sorry.
- Sub-target A is the first attackable item (next commit). Sub-target B is pure
  assembly. Sub-target C is where new math enters and may take many sessions;
  its exact, typed declaration already exists in the SoninWindowWitness kernel.

## 4. This repo vs mathlib

The pieces that are genuinely NEW (to be authored, then upstreamed):
- Paley - Hardy/Radial one-sided Fourier support detection (the Titchmarsh
  theorem): not in mathlib v4.30.0.
- The band-limit projection "PSP" fixed-point/embedded construction.

Everything else (Hardy-Titchmarsh isometry, radial subspace kernel, inner
products) is already repo/mathlib and only needs assembly.

## 5. First execution phase (step A): explicit nonzero radial window element

Construct and prove in Lean (`ConnesWeilRH/Dev/PaleyWindowProbe.lean`):

```text
def hRayWindow f (f on interval) ...
lemma radialMem_nonzero : exists _, _ = 0 on <log-> AND nonzero on window is,
corollary build the L2 vector.
```

Next sub-goal in the code (A opens now, B after, C after B).
