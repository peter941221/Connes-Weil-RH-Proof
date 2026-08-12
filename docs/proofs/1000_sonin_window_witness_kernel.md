# 1000 - Sonin-window witness kernel (typed contract, build-verified)

Date: 2026-08-12. Status: typed-verified, axiom-clean **module kernel**; the
analytic leaf `archimedeanSoninCarrier_nontrivial` remains OPEN (docs/999).
This module documents seam, not a closure of the leaf. RH NOT claimed.
No new axiom / sorry.

## 1. What was delivered

New module `ConnesWeilRH/Dev/SoninWindowWitness.lean`, isolated-mirror built
(`cwr-998outer`, `flock`-guarded `lake build ConnesWeilRH.Dev.SoninWindowWitness`,
3316 jobs, exit 0). `#print axioms` on all four declarations =
`[propext, Classical.choice, Quot.sound]`; zero `sorryAx`; no project axiom.

The module pins, by exact typed `Prop`s, the irreducible leaf from docs/999;
these statements are build-verified and axiom-clean because a `noncomputable
def ... : Prop` carries no proof obligation. The factual closures in the module
(the window is a nonempty open interval of length `log 2`) are proved.

## 2. The verified typed contract (exact)

For `lambda : CCM24SoninScale`, with
`V_arch = sourceSoninCarrier lambda = (ccm24ArchimedeanSoninClosedSubspace
lambda).toSubmodule = Radial lambda ⊓ Fourier lambda`:

```text
archimedeanSoninCarrier_nontrivial lambda : Prop
  = ∃ u : sourceSoninCarrier lambda, u ≠ 0

archimedeanSonin_membership_pred lambda u : Prop
  = u ∈ ccm24LogRadialSupportClosedSubspace lambda ∧
    u ∈ ccm24ArchimedeanFourierSupportClosedSubspace lambda

windowT lambda : Set ℝ = Ioo (log lambda) (log lambda + log 2)
windowT_nonempty lambda : (windowT lambda).Nonempty     -- PROVED, axiom-clean

archimedeanSonin_window_mass lambda : Prop
  = ∃ u : sourceSoninCarrier lambda,
      u ≠ 0 ∧ ∃ x, x ∈ windowT lambda ∧ ((u : carrier) x) ≠ 0
```

The last step to the family-`{2}` outer-zero readout (docs/998 §3, docs/999) is
consuming `archimedeanSonin_window_mass` through the biorthogonal coframe
`D = Ambient o GInv` into `sourceOuterCoframeLeakage lambda twoFamily ≠ 0`;
that full bridge is not yet in Lean (see next).

## 3. What remains OPEN (honest)

- Closing `archimedeanSoninCarrier_nontrivial` (equivalently
  `archimedeanSonin_window_mass`) requires exhibiting a concrete nonzero
  element of the archimedean Sonin carrier and proving its window mass: exactly
  the Paley-Wiener / Titchmarsh / Hardy-space determining-set construction
  enumerated in docs/999 §3. mathlib v4.30.0 ships none of it; the repo ships
  no witness (grep-audit empty).
- Therefore `twoOuterNonzeroObligation` is NOT lifted to a theorem yet; it
  stays an axiom-clean build itself, and AGENTS §2 998/999 notes stay
  "OPEN-boot block / live target", not "已闭合".

## 4. Next session entry point

Build on this exact typed kernel: turn `archimedeanSonin_window_mass` into the
analytic closure by constructing the band-limit / PSP element. Then lift the
obligation through the coframe bridge. RH not claimed.

## 5. Execution-Progression 2026-08-12 (second session)

Added and WSL-verified (cwr-998outer, `lake build ...`, 3316 jobs, axiom-clean)
one more proved artifact in `Dev/SoninWindowWitness.lean`:

```text
archimedeanSonin_membership_pred_of_radial_and_involutive lambda u
  (huRadial : u in Radial(lambda))
  (hinv : HT u = u  OR  HT u = -u) :
  archimedeanSonin_membership_pred lambda u
```

i.e. a radial eigenvector (eigenvalue +-1) of the involutive Hardy-Titchmarsh
isometry already satisfies the full `V_arch` membership predicate; the
Fourier-support half is automatic. `#print axioms` = `[propext,
Classical.choice, Quot.sound]`, 0 sorry.

Structural remark recorded for the next session: this reduction routes the
construction toward the *exact* `+-1` eigenspace of `HT`. Because the
scattering multiplier is a unit-modulus complex phase `m(xi)` (not identically
`+-1`), an `L2` eigenvector `phi` must vanish a.e. off the thin level set
`{xi : m(xi) = +-1}`, which carries no nonzero `L2` vector in general. Hence the
viable route is the **continuous-spectrum / band-limit projection** construction
(the Paley-Wiener / Titchmarsh content of docs/998 §6 and docs/999), not an
exact finite-eigenfunction. The kernel + reduction lemma now pin where that
construction must land. The closed leaf `archimedeanSoninCarrier_nontrivial`
remains OPEN new analysis; `twoOuter...Obligation` is NOT yet lifted. RH not
claimed.

## 6. Steps 1/2/3 collapse to ONE gate (2026-08-12, third pass)

Tracing the exact operator chain for the {2} family (all repo defs,
`CCM24FiniteGramResponse.lean`):

```text
w : sourceSoninCarrier lambda
w = finiteEulerGram lambda family u0   (u0 : sourceSoninCarrier lambda)
x := sourceInclusion lambda (finiteEulerGramInv lambda family w)
   = sourceInclusion lambda u0            [since GramInv (Gram u0) = u0]
   (= u0 as a vector of the ambient carrier, J is the inclusion isometry)
D w = finiteEulerAmbientGram family x
sourceOuterFeasage lambda family w := (id - radialSupportProjector)(D w)
```

Step 2/3 (bridge + lift) are therefore fully deterministic once one supplies

```text
u0 : sourceSoninCarrier lambda,   u0 != 0,
   nonzero L2 mass on (log lambda, log lambda + log 2)
```

i.e. exactly `archimedeanSoninCarrier_nontrivial` + `archimedeanSonin_window_mass`
from this kernel. Every subsequent stage (the `(1-R)(Ambient x) =
-2^-1/2 shift` band depletion, the operator-nonzero `ne maps.ne_zero_iff`, and
`not_ext` for `ContinuousLinearMap`) is mechanical library assembly. So the
entire 1/2/3 request is closed-form GATED on the single genuinely-open analytic
step: **a concrete nonzero element of `V_arch`**. No such element exists in the
repo; the exact `+-1`-eigenvector reduction (above) degenerates in `L2`; only a
continuous-spectrum / band-limit (PSP / Hardy) generator can supply it; that is
the multi-session new-analysis bottom of docs/999. RH not claimed.

No new proof was added in this pass beyond keeping the obligation honest; the
module remains axiom-clean, `[propext, Classical.choice, Quot.sound]`, 0 sorry.

## 7. Step-1 survey verdict (2026-08-12, pursued directly)

I inventoried every reachable carrier/equivalence for a nonzero `V_arch`
element this pass:

- Archimedean Sonin carrier `sourceSoninCarrier lambda`: hard-coded intersection
  `Radial ∩ HT^-1(Radial)`. Repo contains NO element of it (all CCM24*Sonin/,
  *HardyTitchmarsh, *SemilocalFourier, *LogRadialSupport theorems compute
  transports, never exhibit a member; grep for `Nonempty`/`ne_zero` over those
  spaces is empty).
- `+-1` eigens of involutive `HT` reduce (proved) membership, but the 
  multiplier `m(xi)=Gamma_R(1/2-2pi i xi)/conj(...)` has |m|=1 and is non-constant,
  so a nonzero `L2` eigenvector must vanish a.e. off `{xi:m(xi)=+-1}` (measure-zero
  levels) -> only the trivial vector. So exact finite-eigenconstruction is void.
- Healthy/`CompactLog` carriers (`A3NonzeroCompactLogGateProbe` etc.) DO carry
  explicit nonzero windows, but live on a re-typed hand-rolled carrier with NO
  bridge to `sourceSoninCarrier` (route 914/914b explicitly states the absence).
- Restricted/semilocal Sonin equivalences rotate the operator, do not supply
  a nonzero input.

Conclusion (honest): the only viable construction is a continuous-spectrum
band-limit / Hardy (Paley-Wiener / Titchmarsh "PSP") element of V_arch reaching
(log, lambda+log2). This is exactly the multi-session-new-analysis bottom of
docs/999; it is not closable here without it. The module therefore keeps the
gate typed (non-fake) and the obligation a build Prop. RH not claimed.
