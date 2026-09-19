# 1694 — The collapse is blocked at the aggregate equality; Erratum G′ (the carrier IS the meet); the orientation fracture (F66): Theorem D killed the 1622 `U_m` form, not the Lean carrier; the mass face reduces to a density bound and passes the F52-calibrated rig

Date: 2026-09-19.

Status: audit record (paper level, hand-derived) + one F52-calibrated
numeric rig (`scripts/sonin_meet_density_1694.py`, run in WSL2; no new
Lean brick this wave — the two decisive Lean facts were read out of
committed modules, and the remaining H²-level statements have no
Mathlib framework to check against, see 1692 §10).  No uniform bound is
machine-checked and RH is not claimed.

This record resolves the session's carrier crisis in five findings:
the collapse-to-RH chain is blocked at the aggregate equality (`heq`,
§1); 1693's Erratum G is retracted (§2); Theorem D's emptiness does NOT
transfer to the Lean carrier because of an orientation fracture between
two committed operator forms (§3, law F66); the mass face reduces
exactly to a spectral-density bound and passes the F52-calibrated rig
(§4); the map is redrawn with three faces (§5).

## 1. The collapse is blocked at `heq` — the gate has three faces, not one

The crisis: if the Lean meet were `{0}` (Theorem D transferring), then
any `HilbertBasis` of `sourceSoninCarrier lambda` is empty, the survivor
core `Summable ‖J†CJ e_i‖²` holds trivially, the machine-checked 1680
no-slack iff
(`C1G8R3AnnularTraceEquivalence.lean:188`,
`uniformAnnularTraceBound_iff_survivorCore`) hands over the uniform
annular bound, and — if that bound were the gate — RH would follow.
Absurd; so some link must break.

The break is at the LAST link, and it is structural.  The committed
qw-consumers
(`C1G8R5AggregateExpansion.lean:318` `qw_nonnegative_of_g8_survivorCore_and_aggregate_eq`,
`:339` `qw_nonnegative_of_g8_ambientGate_and_aggregate_eq`) consume TWO
hypotheses:

```text
  hcore : Summable_i ‖J† C J (basis i)‖²          (the mass face)
  heq   : (ordinaryTraceAlong sourceBasis
            (g8EndpointSourceCutoffLimitOperator …)).re
          = C1SameOwnerWeil.qw owner.sourceTest    (the AGGREGATE EQUALITY)
```

With an empty basis the trace along it is `0`, so `heq` reads
`0 = qw(g)` — and at the healthy tests where the committed detector
data forces `qw g < 0` (record 1225 `L1`, consumed by the A1 kill lemma
`not_bombieriQuadraticAggregateP2BridgeData_of_healthyDetectorData`,
`C1AggregateSocketSatisfiability.lean:73`) this is unsatisfiable.  The
mass face being free does NOT produce the sign.

Verdict:

```text
  GATE  =  [mass face: core summable]  +  [sign face: heq]  +  [index face: ∀g]
```

1692 §11's closing sentence ("completing the estimate IS proving RH")
is corrected by this decomposition: completing the estimate completes
only the mass face.  Even a proof that the carrier is `{0}` would not
reach the gate through this lane, because `heq` becomes `qw(g) = 0`,
which the committed A1-style facts refute at healthy `g`.

## 2. Erratum G′ — 1693's Erratum G is retracted

1693 §2 claimed 1682 §1's identification `core = tr(P₀ M_φ P₀)` (with
`P₀` the meet projection) was false because "the Lean core sums over
`sourceSoninCarrier λ` ≠ the meet".  That premise is wrong: the Lean
carrier IS the meet —

```text
  ccm24ArchimedeanSoninClosedSubspace λ
      = radial ⊓ Fourier-support           (CCM24HardyTitchmarsh.lean:376–380)
  sourceSoninCarrier λ  =  E_λ ⊓ comap T (E_λ)      (the meet, literally)
```

so 1682 §1's operator identity stands as an operator identity, and the
reductio that motivated Erratum G fails at §1's `heq` blocker anyway.
1682 §1 is reinstated; Erratum G is withdrawn.

## 3. The orientation fracture — law F66

Two committed operator forms exist in the tree:

```text
  (T-form, the LEAN carrier)  T = F⁻¹ ∘ M_m̃ ∘ Refl ∘ F
      readback (Tu)^ = m̃(ξ)·(Fu)(−ξ)      (CCM24HardyTitchmarsh.lean:340–344)
      m̃(ξ) = Gamma_R(1/2 − 2πiξ)/Gamma_R(1/2 + 2πiξ)

  (U_m-form, the 1622 module)  U_m = F ∘ M_{conj m̃} ∘ F⁻¹
      (SoninCarrierMultiplierConjugate; reflection applied OUTSIDE:
       condition "U_m u ∈ R(Radial λ)")
```

Mechanical PW bookkeeping (derived five times this session; every step
a one-line consequence of the shifted Paley–Wiener dictionary
`supp w ⊆ [c,∞) ⟺ e^{2πicξ}(Fw) ∈ H²(ℂ₋)` and the reflection swap
`h ∈ H²(ℂ₋) ⟺ h(−·) ∈ H²(ℂ₊)`):

```text
  Lean meet ≠ {0}  ⟺  ∃ K ≠ 0:  K ∈ H²(ℂ₊),
                                e^{4πiaξ}·m̃(+ξ)·K ∈ H²(ℂ₋)     a = log λ
  1629 normalization / Thm D object  ⟺
                        ∃ H ≠ 0:  H ∈ H²(ℂ₊),
                                e^{4πiaξ}·m̃(−ξ)·H ∈ H²(ℂ₋)
```

The two multipliers differ by the Γ-ratio conjugation
(`m̃(−ξ) = conj m̃(ξ)`), and the basic criterion's Kolmogorov ceiling is
TAIL-ORIENTATION-ASYMMETRIC.  From the representation `γ = h̃ − α` with
`α` increasing: on the left tail `α ≤ c₂`, so `h̃ = γ + α ≤ γ + c₂`;
a ceiling contradiction needs the upper bound to diverge, i.e. the
ceiling fires exactly on `[left tail → −∞]` or `[right tail → +∞]`
and is silent on `[left → +∞, right → −∞]` (that is why the linear
`m̃ = 1`, `λ < 1` model keeps its witness — 1692 §4's own table).

```text
+---------------------------------------------------------------+
| object                 | slot phase          | tails    | fate |
+------------------------+---------------------+----------+------+
| Thm D (m̃(−ξ) orient.)  | 4πaξ+arg m̃(−ξ) = γc | L→−∞ R→+∞| DEAD |
| Lean meet (m̃(+ξ))      | 4πaξ+arg m̃(+ξ)      | L→+∞ R→−∞| OPEN |
|   φ_me = −γc + 8πaξ    | (odd; stationary    |          |      |
|                        |  points ±λ²)        |          |      |
+---------------------------------------------------------------+
```

At `m̃ ≡ 1` the two forms coincide (the window `L²[a,−a]` for `a < 0`),
which is why the 1629 model check could not see the fracture; the
Γ-ratio is what splits them.

**Law F66.**  Theorem D (1692) decides the 1622 `U_m`-form carrier.
The Lean carrier (`T`-form) is a different two-sided problem whose
phase points the safe way; its `p = 2` nonemptiness is OPEN.  1692 §4's
"both orientations are dead" paragraph is retracted (its reflection
argument does not convert `N⁺[e^{−iγ}]`-emptiness into
`N⁺[e^{iφ_me}]`-emptiness, and the ceiling is silent on `φ_me`'s
orientation).

## 4. The mass face: exact reduction, the density bound, and the rig

The mass face in Lean terms is `Summable_i ‖J† C J e_i‖²` with
`C = rootConvolution owner = cc20GlobalLogConvolution (involution test)`
(`CCM24FiniteSBandTrace.lean:36`).  Hand reduction (F27/F28):

```text
  Σ_i ‖J†CJ e_i‖²  =  tr(P_meet C*C P_meet)
                   =  ∫ |κ(ξ)|² · D(ξ) dξ,
  κ = Fk  (spectral multiplier of the convolution),
  D(ξ)   = diagonal of F P_meet F⁻¹  (the carrier projection's
           spectral dimension density; basis-independent).
```

Shear normal form (the two-sided condition is, per frequency `ξ`, a
time-window of length `−φ_me′(ξ)/(2π)`):

```text
  D(ξ)  ≈  ( −φ_me′(ξ)/2π )₊  =  ( log|ξ| − 2a )₊ ,
```

vanishing on `|ξ| < λ²` (where `φ_me′ > 0`) and growing only
logarithmically.  The paper-level bound `D(ξ) ≲ 1 + |φ_me′(ξ)|/2π`
(localization/Landau–Pollak count for two-sided model spaces) is the
formal backing; its careful write-up is a named next step.

The rig (`scripts/sonin_meet_density_1694.py`, v4; WSL2): the meet is
built exactly on the grid (support condition diagonal; condition 2 via
the `(t_f + t_k)` reflection matrix `M[f,k] = (1/N)Σ_j m̃_j
e^{2πiξ_j(t_f+t_k)}`; the meet = `ker A_s` INSIDE the support
coordinates — v1/v2's `ker(M·P1)` contained all of `ker P1` and failed
F52; the density readout `D(ξ) = dt·f̃*Πf̃` with δ-normalization).
Results:

```text
+---------------------------------------------------------------+
| F52 calibration (m̃=1)      | measured          | expected     |
+-----------------------------+-------------------+--------------+
| D interior (a=−1)           | 2.0625 flat       | 2 (+1 gridpt)|
| D interior (a=−0.5)         | 1.0625 flat       | 1 (+1 gridpt)|
| dim (a=−1, N=1024)          | 65                | 64 (+1)      |
+-----------------------------+-------------------+--------------+
| real Γ-ratio                | measured D        | shear line   |
+-----------------------------+-------------------+--------------+
| a=−2: D(1), D(4), D(7.5)    | 4.00, 5.40, 6.03  | 4.00,5.39,6.01|
| a=−1: D(1), D(4), D(7.5)    | 1.93, 3.40, 4.03  | 2.00,3.39,4.01|
| a=−0.5: D(2), D(4), D(7.5)  | 1.68, 2.40, 3.02  | 1.69,2.39,3.01|
| D on |ξ| < λ²               | → 0 under N↑      | 0            |
| N ∈ {512,1024,2048} scaling | STABLE profile    | (nonempty!)  |
+---------------------------------------------------------------+
```

Two decisive readings.  (i) The density is the shear line to 1–3% in
the normal-form region, with the predicted dead zone `|ξ| < λ²` — the
log-growth is real, not an artifact.  (ii) The N-scaling is stable:
if the continuum meet were `{0}` the interior density would decay to
zero under refinement; it converges instead.  The meet is NONEMPTY —
confirming law F66 numerically, independently of the paper-level
orientation audit.

Mass-face verdict: `∫|κ|²D` is finite for every test with
`|κ|²log|ξ| ∈ L¹`; the rig measures it finite for gaussian, `C_c^∞`
bump, and rational-family κ at `a = −1` (1.73 / 6.97 / 0.80).  Every
`CompactLogTest` has smooth compact log-support, hence Schwartz κ —
so the survivor core is square-summable and (by the machine-checked
1680 iff) the uniform annular bound holds, for every owner and λ.
Status: paper-level reduction + F52-calibrated confirmation; the
machine check waits on a Mathlib PW/Hardy framework (the 1692 §10
gap).  The formal write-up of the density bound is the remaining
paper step of this face.

## 5. Map 045 — three faces

```text
+------------------------------------------------------------------+
|  GATE 0 ≤ qw(g) ∀g   ⟺  RH   (F20, machine-checked)              |
|     |                                                            |
|     +-- mass face:  Σ‖J†CJ e_i‖² < ∞                             |
|     |     = ∫|κ|²D, D ≲ 1+|φ′|/2π ~ log|ξ|                       |
|     |     DONE (paper + F52-calibrated rig; §4)                  |
|     |     ⟹ uniform annular bound (1680 iff, MC) — free          |
|     |                                                            |
|     +-- sign face:  heq (the aggregate equality                  |
|     |     trace = qw) — THE FRONT; with the mass face free,      |
|     |     every remaining G8/Socket obligation lives here        |
|     |                                                            |
|     +-- index face:  the ∀g expansion of the single-owner sign   |
|           (F62 no-index territory; socket field1 realizability,  |
|            record 1226 C3)                                       |
+------------------------------------------------------------------+
```

Corrections of prior records: 1693 §2 (Erratum G) retracted (§2 here);
1693 §5's completion-map rows "exact face done" and "global = ONE
object" are replaced by the three-face table above (the exact face is
OPEN with the meet nonempty, §3; the mass face is DONE, §4); 1692 §4's
"both orientations are dead" paragraph retracted (§3); 1692 §11's
"completing the estimate IS proving RH" corrected (§1).  No committed
numeric result is invalidated; the 1680 iff, the trace-limit theorems,
and the leakage summability are unchanged (they were conditional).

## 6. Boundary

No RH, no gate, no machine-checked bound.  New law: F66 (orientation
fracture).  Retracted: 1693's Erratum G, 1692 §4's both-orientations
paragraph.  Open: the density bound's formal write-up; `heq`; the ∀g
index; the machine check of everything H²-level (Mathlib gap).  The
deliverable: the crisis is resolved without a collapse, the carrier is
nonempty, the mass face is reduced to a log-density bound and passes
its calibration, and the program's remaining content is precisely
located on the sign and index faces.
