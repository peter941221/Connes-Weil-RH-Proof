# 1081 - consumer #3 structural exit: the root-supported gate named, the RH exit composed, the tail made damper-free

Date: 2026-09-01. Follows 1080 (consumer #2 exit).  This record lands the
LEAN skeleton of consumer 3 of `RH_MAINLINE_FREEZE.md`: *detector-specific
semi-local positivity on the same healthy owner*.

## 1. What consumer #3 actually is (recon result)

The unconditional spectral-negativity construction
(`C1HealthyYoshidaSpectralNegativity.exists_healthyDetectorData_of_
sourceNontrivialZero_right`) ALREADY produces `HealthyYoshidaDetectorData`
for every off-line source zero oriented to the right of the critical line -
but on an n-fold convolution orbit whose support leaves the ROOT window.
The capstone
`sourceRH_of_rootSupportedHealthyDetectorData_and_endpointCertificates`
consumes the data only together with
`support g.test ⊆ Icc(−log 2 / 2, log 2 / 2)`.  Consumer 3 is therefore
PRECISELY the root-support transport of the strict spectral sign:

    rootSupportedHealthyDetectorGate rho :=
      exists g, HealthyYoshidaDetectorData rho g /\
                support g.test ⊆ [-log 2 / 2, log 2 / 2]

## 2. What landed (`ConnesWeilRH/Dev/C1HealthyDetectorRootSupportExit.lean`)

1. `rootSupportedHealthyDetectorGate` - the gate as a named proposition, in
   the exact shape the capstone consumes.
2. `rootSupportedGate_of_selectedDetectorArchimedeanGate` - the C2 -> C3
   glue: on a PINNED detector (record 1080), the scalar archimedean gate
   plus the explicit root-support radius implies the root-supported gate.
   This is the honest reduction of consumer 3 to one scalar inequality:
   `0 < archimedeanTerm g.convolutionSquare`.
3. `sourceRH_of_rootSupportedGate_rightRep_and_endpointCertificates` - the
   RH exit composition.  For an off-line zero take its functional-equation
   representative strictly right of the line, its root-supported detector,
   and the CC20 endpoint certificate for that same test: the certificate
   forces `0 <= qw g`, the detector data forces
   `qw g = spectralWeilValue g.convolutionSquare < 0`.  Contradiction.
   Only `vanishesOnF` + `weilSquareSumPositive` are consumed; the detection
   field is not needed.
4. `exists_fourthOrderTail_halfDensityShift_convolutionSquare` - the
   DAMPER-FREE TAIL.  For EVERY compact-log test `h` and every strip anchor
   `rho` there are an explicit threshold `T = max 1 (|Im rho| + 1)` and size
   `epsilon = 1 + 81 * C * (2 pi)^2` (with `C` the proved uniform quadratic
   vertical-decay constant of `h`) such that the half-density square
   satisfies `FourthOrderSpectralTail`.  Mechanism: the Hermitian product
   `laplaceAt h rho * conj(laplaceAt h (1 - conj rho))` squares the
   quadratic vertical decay into FOURTH order, so no n-fold base damping is
   needed on the tail side.

## 3. The wall, now isolated to one side

The library's unconditional sign construction runs through
`CC20YoshidaConvolution.exists_nearbyZero_unscaled_targetValues_assembly_
of_fixedThreshold`, whose support is
`Ioo((n+1)*baseLower + lower, (n+1)*baseUpper + upper)`: the n-fold base
iterate exists ONLY as a geometric decay damper (|base-tilde| <= 1/2 at
|Im z| >= T, so |base-tilde|^n kills the quadratic decay constant `C`) to
meet a caller-fixed `epsilon` - and the damper is exactly what destroys
root support.  The epsilon-vs-radius circle
(`epsilon = f(C(corr(R(n0(epsilon)))))`, tail size vs ball-radius
interpolation constants) is broken in-library only by that n-damping;
escaping it needs uniform-in-radius interpolation-constant control, which
is real open mathematics.

What this record changes: the TAIL side is now damper-free closable (item 4
above, proved, for every test - not just the orbit).  The remaining
root-support obstruction sits ENTIRELY on the prefix side: the
ball-radius interpolation constants versus the geometric shell budget
`(3/4)^n0`.  That is the named open kernel of consumer 3, alongside the
scalar archimedean inequality on a pinned detector (1079 measures it at
`fl2 = -1.294`, sink 33.78% of lever, for zero #2).

## 4. Build evidence

WSL ext4 mirror build through the resource runner
(`build-logs/c3_root_support5.log`):

    Build completed successfully (3633 jobs).
    zero `^error:` lines; zero `sorryAx` in the log.

Focused axiom audit (`C1HealthyDetectorRootSupportExitAudit.lean`) - all
three theorems depend on exactly the three standard axioms
`[propext, Classical.choice, Quot.sound]`:

    rootSupportedGate_of_selectedDetectorArchimedeanGate            OK
    sourceRH_of_rootSupportedGate_rightRep_and_endpointCertificates OK
    exists_fourthOrderTail_halfDensityShift_convolutionSquare       OK

Five build iterations (error cascade 20 -> 6 -> 1 -> 1 -> 0).  Authoring
defects caught by the kernel, all semantic: bare `ext` does not fire on
`Complex` (needs `apply Complex.ext` + two `simp` goals); the two Icc
constructor goals of `(1 - star z).re` come out swapped against intuition;
`abs_sub_le a b c` is `|a - c| <= |a - b| + |b - c|`; `mul_le_mul_of_
nonneg_left` cannot see through left-association (`81 * A * B` vs
`81 * (A * B)` - state the goal pre-grouped and let `ring` re-associate).

## 5. What is NOT here

`archimedeanTerm > 0` is NOT proven for any specific test; the
prefix-side interpolation constant is NOT controlled uniformly in the
radius; RH is NOT claimed; no frozen namespace was touched; the capstone
premises are unchanged.  Consumer 3 is structurally reduced - to the named
scalar gate (1080) plus the named prefix-side wall (this record) - but the
two kernels themselves remain open.  The coverage root remains
RH-equivalent, not a density lemma.
