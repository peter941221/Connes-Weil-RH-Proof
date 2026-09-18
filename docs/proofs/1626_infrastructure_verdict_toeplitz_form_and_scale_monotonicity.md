# 1626 — Infrastructure verdict, the exact Toeplitz form of the carrier base, and scale monotonicity

Date: 2026-09-18.

Status: one accepted Lean brick (scale monotonicity, section 5) + route recon
(sections 1–4). No existence statement, no estimate. The carrier base, T4, B4,
S3 and RH stay OPEN. RH is not claimed.

Consumer (named, unchanged): the healthy-`CompactLog` B5 statement
`0 <= C1SameOwnerWeil.qw g` through `G8SameOwnerReadbackData`
([012](../map/012_g8_same_owner_readback_rh_reachability.md)); the carrier base
is the base of both WO legs of map
[042](../map/042_g8_diagonal_leg_operator_bridge_audit.md).

## 1. What is committed, and what is actually missing

Exact committed statements (this is the whole critical path; nothing here needs
an H² layer to be *stated*):

```text
+-------------------------------------------+------------------------------------------+
| object                                    | committed form                           |
+-------------------------------------------+------------------------------------------+
| scale                                     | `CCM24SoninScale := {l : R // 0 < l}`    |
|                                           | (CCM24LogRadialSupport.lean:27)          |
| Radial(l)                                 | `ker` of the restriction to `Iio (log l)`|
|                                           | (:48); membership `a.e. t < log l ->     |
|                                           | u t = 0` (:67)                           |
| FourierSupport(l)                         | `comap H (Radial l)`                     |
|                                           | (CCM24HardyTitchmarsh.lean:361);         |
|                                           | membership is `Iff.rfl` (:371)           |
| carrier                                   | `Sonin(l) = Radial(l) inf Fourier(l)`    |
|                                           | (:376)                                   |
| carrier as a space                        | `sourceSoninCarrier l = (Sonin l).toSub` |
|                                           | (CCM24FiniteSGramResponse.lean:33)       |
| the open Prop                             | `archimedeanSoninCarrier_nontrivial l := |
|                                           | EXISTS u : sourceSoninCarrier l, u != 0` |
|                                           | (Dev/SoninWindowWitness.lean:44)         |
| frequency halves                          | `HardyPositive = ker P-`,                |
|                                           | `HardyNegative = ker P+`                 |
|                                           | (CCM24PaleyWienerSpectral.lean:251/256)  |
+-------------------------------------------+------------------------------------------+
```

Verdict on the infrastructure question of [1623](1623_t4_prolate_attack_four_obligations_and_two_mismatches.md)
section 5 / [1624](1624_b4_certificate_and_carrier_are_one_toeplitz_condition.md)
section 4: **a new H²/Paley–Wiener layer is NOT needed to state anything on
this path.** Every object above is a support or frequency-half condition on
`L2(R)`, and the Toeplitz condition can be written with `HardyPositive` /
`HardyNegative` directly. The missing layer is needed only to *prove*
existence/uniqueness statements of de Branges/Toeplitz type, and Mathlib has
none (1623 section 5). This lowers the formalization bill for any future brick
relative to what 1623/1624 assumed.

## 2. The exact Toeplitz form, re-derived from the committed factor

Committed (`CCM24HardyTitchmarsh.lean:104`):

```text
ccm24ArchimedeanScatteringPhase xi = ccm24ArchimedeanFactor xi / conj (ccm24ArchimedeanFactor xi)
ccm24ArchimedeanFactor xi = Gamma_R(1/2 - 2*pi*I*xi)
```

For real `xi`, Schwarz reflection for `Gamma_R` gives
`conj (Gamma_R(s)) = Gamma_R(conj s)`, so the symbol has the *explicit* ratio
form

```text
m(xi) = A(xi) / B(xi),   A(xi) := Gamma_R(1/2 - 2*pi*I*xi),   B(xi) = A(-xi).
```

Ledger (Stirling; hand-derived here, matching 1624's list):

```text
+------------------+-------------------------------------------------------------+
| A                | analytic and zero-free on C_+; simple poles at              |
|                  | -I*(4n+1)/(4*pi) in C_-                                     |
| B = A(-.)        | analytic and zero-free on C_-; simple poles at              |
|                  | +I*(4n+1)/(4*pi) in C_+                                     |
| m                | analytic on C_+ with zeros at +I*(4n+1)/(4*pi) (the poles   |
|                  | of B, removable points of the quotient); poles in C_-;      |
|                  | |m| = 1 on R; |m(x+I*y)| ~ (pi*x)^(2*pi*y) for pi*x large  |
+------------------+-------------------------------------------------------------+
```

`m` is analytic in the strip `|Im xi| < 1/(4*pi)`, so it is **unimodular and
real-analytic on R**. The Paley–Wiener dictionary used in 1624 (conventions
re-verified on `f(t) = e^{-t}1_{t>0}`, `Ff = 1/(1+2*pi*I*xi)`):

```text
supp w subset [c, inf)   <=>   xi |-> e^(2*pi*I*c*xi) (F w)(xi) is in H^2(C_-)
F(H^2(C_+)) = {FT supported on xi >= 0},  F(H^2(C_-)) = {FT supported on xi <= 0},
H^2(C_+) INTER H^2(C_-) = {0}.
```

gives the carrier base in Toeplitz form:

```text
EXISTS phi != 0,  phi in H^2(C_+),  m*phi in H^2(C_-).            (T)
```

## 3. The de Branges shape of (T), and the one obstruction

Setting `psi := m*phi` and `W := A*phi = B*psi`: `W` is analytic on each open
half-plane and continuous across `R`, hence **entire**, and

```text
phi = W/A in H^2(C_+),   psi = W/B in H^2(C_-).                   (DB)
```

This is the de Branges-space pattern (cf. the standard definition: `H(E)`
consists of the entire `F` with `F/E` and `F^#/E` in `H^2`; quote from the
literature sweep: "The de Branges space H(E) associated with E is defined to be
the space of entire functions F satisfying F/E in H^2(C_+), F^#/E in H^2",
Baranov–Poltoratski-type survey, <https://people.math.wisc.edu/~poltoratski/SchroedingerDB-9.pdf>).

Obstruction, checked by hand: **`A` is not Hermite–Biehler.** At `z = I/(4*pi)`
one has `m(z) = 0` while `A` is finite and nonzero there (`A(I/(4 pi)) =
Gamma_R(1 + 1/2)`), so `|A| < |A^#|` near `z`, violating `|E| > |E^#|` on `C_+`.
Consequently the classical `H(E)` theory (which needs `E` HB) does **not**
literally apply; (DB) is used here only as the shape of the obligation. Note
also that the poles of `A` are too dense to be cleared by an entire factor with
the same ratio (`SUM 1/|z_n| = SUM 4*pi/(4n+1) = infinity`), so `m` is not a
quotient `E/E^#` with `E` entire — a second failure of the textbook hypothesis.

## 4. No cheap scalar test decides (T): the classical regime analysis

What [1624](1624_b4_certificate_and_carrier_are_one_toeplitz_condition.md)
section 5 promised as "the decisive cheap test" is, after this recon, a
*negative* result for cheapness:

- **Continuous-symbol index theory is unavailable.** For unimodular symbols
  continuous on the compactified line, the kernel dimension is governed by the
  winding number (model case: `ker T_{theta-bar} = K_theta`, the model space,
  of dimension `deg theta`). Our `m` has argument `gamma(xi) ~ -2*pi*xi*log|xi|
  -> minus/plus infinity` (Stirling), i.e. **no limit at `+-infinity`**: `m` is
  not in that class, and its winding number is not defined.
- **Model test (affine phase).** For `m(xi) = e^(I*a*xi)` the kernel is `{0}`:
  `m*phi in H^2(C_-)` says the transform of `phi` shifted by `a` lies on the
  other side of `F(H^2(C_+))`, which a translate cannot do. So a phase that
  *grows* but stays bounded below in oscillation also gives nothing.
- **Model test (`m = 1`).** `H^2(C_+) INTER H^2(C_-) = {0}` forces `phi = 0`
  (1624 section 3).
- **The applicable classical tool** is the Makarov–Poltoratski criterion for
  unimodular real-analytic symbols `U = e^(I*gamma)`, which — quote from the
  literature sweep — "gave a necessary and sufficient condition for the
  injectivity of a Toeplitz operator with the symbol `U = e^(I*gamma)` where
  `gamma` is a real-analytic real function", formulated via **uniqueness sets
  for model spaces** (Blaschke sets): M. C. Câmara, J. R. Partington,
  "Toeplitz kernels and model spaces", arXiv:1711.04511, section 2.3; survey
  A. Hartmann, M. Mitkovski, "Kernels of Toeplitz operators",
  arXiv:1511.08326. The structural half is Dyakonov's theorem (same source,
  Theorem 2.4): every kernel is `g b^{-1}(K_B INTER b H^2)` — a model-space
  intersection in disguise.

**Verdict.** (T) is decidable only by model-space/de Branges machinery, i.e. by
exactly the prolate-type world of T4
([1003](1003_psp_inner_outer_attack_plan.md), [1590](1590_carrier_base_obligation_is_a_de_branges_existence_and_1331_erratum.md)).
The 1624 section 5 promise of a cheap scalar test is hereby withdrawn; the
substitute is (DB), a two-sided growth condition on one entire function.

Growth-only character of (DB), for the record: from the ledger, `A` is
pole-free and zero-free on `C_+` and `B` is pole-free and zero-free on `C_-`,
so `W/A in H^2(C_+)` and `W/B in H^2(C_-)` impose **no pointwise cancellation
conditions** at all — the entire content of the carrier base is the pair of
line-norm bounds

```text
sup_{y>0} || W(./A)(x + I*y) ||_{L2(dx)} < infinity,
sup_{y<0} || W(./B)(x + I*y) ||_{L2(dx)} < infinity,   W entire, W != 0.
```

## 5. Scale monotonicity (the brick)

`ConnesWeilRH/Dev/SoninScaleMonotonicity.lean` + audit, five declarations, no
`sorry`, standard axioms only:

```text
+-------------------------------------------------+----------------------------------+
| declaration                                     | content                          |
+-------------------------------------------------+----------------------------------+
| ccm24LogRadialSupportClosedSubspace_mono        | Radial(l') <= Radial(l) for      |
|                                                 | l <= l'                          |
| ccm24ArchimedeanFourierSupportClosedSubspace_mono| same for FourierSupport         |
| ccm24ArchimedeanSoninClosedSubspace_mono        | same for the carrier             |
| archimedeanSoninCarrier_nontrivial_of_le        | a witness at l' witnesses l      |
| archimedeanSoninCarrier_nontrivial_of_not_of_le | triviality at l forces triviality|
|                                                 | at every larger scale            |
+-------------------------------------------------+----------------------------------+
```

Reason: the vanishing region `Iio (log l)` grows with `l`. Consequences:

- the admissible scales of the carrier base form a **downward-closed interval**:
  the obligation is a sharp-threshold statement, not an isolated existence;
- the `m = 1` sanity check of 1624 becomes structural: in the model the carrier
  is `{0}` at `l = 1` (`log 1 = 0`, the two half-lines meet), hence `{0}` for
  all `l >= 1`;
- a single refuted scale refutes every larger scale, so any future witness
  search should run from below.

## 6. Self-check recorded as a caution

While deriving (DB) the claim "no nonzero entire function lies in `H^2(C_+)`"
was drafted and then **refuted by an explicit example**:

```text
W(z) = INT_0^a e^(2*pi*I*xi*z) dxi = (e^(2*pi*I*a*z) - 1)/(2*pi*I*z),   a > 0,
```

entire of exponential type `a`; line norms in `C_+` are `INT_0^a
e^(-4*pi*xi*y) dxi <= a`, while in `C_-` they grow like `e^(4*pi*a*|y|)`. Hence
`W in H^2(C_+)` and `W not in H^2(C_-)`: the entire-and-`H^2(C_+)` class is
nonempty, and the correct witness is an exponential-type function whose
transform is supported on a half-line. Record 1590's *claim* on this point is
right; its example (`((sin z)/z)^2 e^(2Iz)`) is not (its `C_+` line norms blow
up as `y -> 0+`). The lesson is law F27/F28 in action: compute the simplest
example before asserting a rigidity theorem.

## 7. Boundaries

The carrier base (now in form (T)/(DB)), T4, B4, S3, WO-S, WO-B,
`EndpointMass(eps)`, T1, (star), `rho5`, R4/(OB)/W1 and RH are unchanged and
open. No gap premise, `SourceRH`, or universal gate is introduced.

## 8. Acceptance

Build log: `build-logs/sonin_scale_monotonicity2.log`.
`Build completed successfully (3319 jobs)`, zero `error:` lines, zero
`sorryAx`, five axiom prints all resolving to
`[propext, Classical.choice, Quot.sound]`, no warning in the two new modules.