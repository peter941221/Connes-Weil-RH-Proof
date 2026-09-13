# 1389 — Component 5 discharge recon: route alpha collapses the healthy-data package to one scalar sign

Date: 2026-09-13. Lane: **FORMAL source readback** (no Lean was written, no
build was run, no digit was produced). Authority: this record corrects two
locks in [1388](1388_component5_route_A_prereg.md) and supersedes it; the
corrected prereg is [1390](1390_component5_route_A_prereg_v2.md).

Verdict up front, because it is mixed:

```text
GOOD   Recon A: the healthy-space membership condition is UNCONDITIONAL.
GOOD   Recon C: route alpha has an IFF that collapses the entire
       HealthyYoshidaDetectorData package to ONE scalar sign, and it needs
       no iterate, no decay constant, no height tail, and no n.
BAD    Recon B: 1388 section 1 locked the WRONG node family.  The register's
       minimal route uses 4 nodes {0, 1/2, 1, rho}, not the 7-node orbit.
BAD    1388 section 2's radius grid is inadmissible: route alpha forces
       Rf + Ru <= log(2)/2, which 19 of the 25 locked cells violate.
BAD    1388 section 0's claim that R1 "closes with ZERO new analysis" was an
       OVER-CLAIM.  It is true for the budget side and false for the
       healthy-data side, which lands on a pre-existing open sign.
```

## 1. Recon A — membership in the healthy test space is free

The worry recorded in 1388 section 0 was that a record-1385 taper owner might
fail to land in `C1.healthyCC20TestSpace`. It cannot fail.

`ConnesWeilRH/Dev/C1HealthyTestSpace.lean:44-56`:

```lean
noncomputable def healthyCC20TestSpace : ConnesWeilRH.Source.CC20TestSpace where
  Test := CompactLogTest
  ...
  compactSupportSmooth := fun g =>
    HasCompactSupport (C1LogPositiveBridge.toPositiveRouteTest g)

theorem healthyCC20CompactSupportSmooth (g : CompactLogTest) :
    healthyCC20TestSpace.compactSupportSmooth g :=
  C1LogPositiveBridge.toPositiveRouteTest_compactSupport g
```

The membership predicate is a function of `g` with **no hypothesis on `g`**, and
the proof is a one-line application. Any `CompactLogTest` is a member, so a
taper owner qualifies by typing alone. Recon A: **CLOSED, obstacle does not
exist.**

## 2. Recon B — the node family is 4 nodes, not the orbit

1388 section 1 locked

```text
nodes(rho) = sourceFunctionalEquationOrbit rho = {rho, 1 - conj rho, conj rho, 1 - rho}
y(rho)     = negativeSourceOrbitValue rho
```

That is the family used by the **orbit package** (route beta). The route-alpha
register uses a different, much smaller family.
`ConnesWeilRH/Dev/C1HealthyYoshidaMinimalInterpolation.lean:27-43`:

```lean
noncomputable def healthyDetectorNodeSet (rho : Complex) : Finset Complex :=
  {0, 1 / 2, 1, rho}

noncomputable def healthyDetectorNodeTarget
    (rho : Complex)
    (z : FiniteMellinNode (healthyDetectorNodeSet rho)) : Complex :=
  if z.1 = rho then -1 else 0

def HealthyMinimalLaplaceRealizes (rho : Complex) (g : CompactLogTest) : Prop :=
  CompactLogTest.laplaceAt g 0 = 0 /\
    CompactLogTest.laplaceAt g (1 / 2) = 0 /\
      CompactLogTest.laplaceAt g 1 = 0 /\
        CompactLogTest.laplaceAt g rho ≠ 0
```

Two consequences.

**(a) The vanishings sit on `g` itself, not on its square.** The earlier
half-density-shift reading — source vanishing at `{1/2, 1, 3/2}` producing
square vanishing at `{0, 1/2, 1}` — belongs to route beta
(`C1SelectedSquareHeightTail.lean:575-615`, whose hypothesis is
`laplaceAt (selectedOwner base correction n).convolutionSquare (w.1 - 1/2) = 0`).
Route alpha has no shift and no square in its vanishing condition. The larger
7-node family is therefore **not** mandatory; it was mandatory only for the
route I had wrongly assumed.

**(b) Node distinctness is already funded.** The record-1385 taper wrapper needs
`Function.Injective nodes`, i.e. `rho` distinct from `0`, `1/2`, `1`. The same
file proves all three as private lemmas from `sourceNontrivialZero rho` and
`hoff : rho.re ≠ 1/2`:

```lean
private theorem source_nontrivial_zero_ne_zero   ... : rho ≠ 0
private theorem source_nontrivial_zero_ne_half   ... : rho ≠ (1 / 2 : Complex)
private theorem source_nontrivial_zero_ne_one    ... : rho ≠ 1
```

No new distinctness work is required.

## 3. Recon C — route alpha has an IFF, and it is the cheap route

`ConnesWeilRH/Dev/C1HealthyDetectorPinning.lean:113-137`:

```lean
def selectedDetectorArchimedeanGate (_rho : Complex) (g : CompactLogTest) :
    Prop :=
  0 < C1SameOwnerWeil.archimedeanTerm g.convolutionSquare

theorem healthyDetectorData_iff_selectedDetectorArchimedeanGate
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyMinimalLaplaceRealizes rho g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) :
    HealthyYoshidaDetectorData rho g ↔
      selectedDetectorArchimedeanGate rho g
```

This is the decisive structural fact. On a ROOT-pinned minimal-realizing test,
the **whole** healthy-data package — `compactSupportSmooth`, `vanishesOnF`,
`detectsRho`, `weilSquareSumPositive` — is equivalent to one scalar sign.

Comparing the two routes now available:

```text
+-------------------+----------------------------------+----------------------------------+
|                   | ROUTE ALPHA (minimal interp.)    | ROUTE BETA (orbit package)       |
+-------------------+----------------------------------+----------------------------------+
| node family       | {0, 1/2, 1, rho}       (4 nodes) | orbit U {rho+1/2,1/2,1,3/2} (7)  |
| vanishings on     | g itself                         | g.convolutionSquare, shifted -1/2  |
| support           | Icc(-log2/2, log2/2)   FIXED     | Ioo((n+1)*bl+l, (n+1)*bu+u) GROWS|
| owner shape       | single convolution u * f         | (n+1)-fold iterate, rescaled     |
| decay constants   | NOT NEEDED                       | C_b, C_c required                |
| height tail / N   | NOT NEEDED                       | required, with hnb inequality    |
| iterate exponent n| ABSENT                           | present; positivity wants n LARGE  |
| positivity reduces| ONE sign: archimedeanTerm > 0    | height-budget inequality hnb     |
+-------------------+----------------------------------+----------------------------------+
```

Route alpha is strictly cheaper. Two of its cells deserve comment.

**Decay constants are free even on route beta.** Had beta been needed, the
constant would not have been new analysis either —
`ConnesWeilRH/Dev/C1XiContourDecay.lean:30-36` takes a *plain* `CompactLogTest`
with **no support hypothesis at all**:

```lean
theorem exists_uniform_laplaceAt_vertical_quadratic_decay_on_unit_strip
    (F : CompactLogTest) (a : Real) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc a (a + 1), ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖CompactLogTest.laplaceAt F
              ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C
```

and line 57 extends it to `Icc (-3/2) (3/2)`. The constant is **existential**,
which is exactly what makes the F3 producer unconditional (choose `N` large
against the given `C`). So the "explicit vertical decay constant" I had feared
as a new brick does not exist as an obligation.

**The iterate is L1-normalized, so the n-squeeze is milder than it looks.**
`CC20YoshidaConvolution.lean:226-228`:

```lean
noncomputable def rescale (f : CompactLogTest) (r : ℝ) (hr : 0 < r) :
    CompactLogTest := by
  let raw : ℝ → ℂ := fun x => ((r : ℂ)⁻¹) * f.test (x / r)
```

The `r⁻¹` Jacobian factor makes `rescale` **L1-isometric**, so
`‖(iterate)‖₁ = ‖base‖₁` and the L2 bound of an `(n+1)`-fold iterate grows like
`‖base‖₁^(2(n+1))` with no extra polynomial-in-`n` factor. Combined with
`laplaceAt_convolutionIterate : laplaceAt (convolutionIterate f n) s =
laplaceAt f s ^ (n + 1)` (`CC20YoshidaConvolution.lean:465-467`), route beta
would have been a two-sided squeeze on `n` — positivity pushes `n` up, the (J1)
budget pushes it down — but only through the single scalar `‖base‖₁`. Route
alpha has **no `n` at all**, so the squeeze never arises. This is the main
reason to prefer alpha beyond node count.

## 4. The exact radius constraint, and why 1388's grid fails it

`C1HealthyDetectorPinning.lean:42-47`:

```lean
theorem convolutionSquare_support_logTwo_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)) :
    Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2)
```

Component 4 places the assembled owner `g = u.convolution f` in the **summed**
window `Ioo (c + a) (d + b)`. With symmetric factor windows `(-Ru, Ru)` and
`(-Rf, Rf)` that is `Ioo (-(Ru+Rf)) (Ru+Rf)`, and route alpha's pinning
hypothesis is a closed window of half-width `log(2)/2`. So:

```text
HARD CONSTRAINT (route alpha):    Rg = Ru + Rf  <=  log(2)/2  ~=  0.34657
```

Audit of the grid 1388 section 2 locked (`Rf, Ru ∈ {0.05, 0.1, 0.25, 0.5, 1.0}`,
25 cells):

```text
admissible (Rf + Ru <= 0.34657):
  (0.05, 0.05) = 0.10     (0.05, 0.10) = 0.15     (0.10, 0.05) = 0.15
  (0.10, 0.10) = 0.20     (0.05, 0.25) = 0.30     (0.25, 0.05) = 0.30
                                                     ->  6 of 25 cells

inadmissible:  19 of 25 cells, including every cell with a radius >= 0.5.
Borderline:    (0.10, 0.25) and (0.25, 0.10) both give 0.35 > 0.34657.
```

So **76% of the locked grid was inadmissible** under the route the prereg itself
committed to. This is a law-42 defect found before any digit, which is the only
acceptable time to find it: per the record-1373 protocol a model revision
requires a NEW record and a NEW prereg, not an edit. Hence 1390.

## 5. The constraint is not a handicap — the asymptotics run the other way

A narrow window sounds restrictive, but it is the favourable direction for (J1).
Both couplings of record 1378 shrink with `Rg` on `(-Rg, Rg)`:

```text
C_C = 8*pi*sinh(d*Rg)^2 + 2*delta^3*Rg^3*exp(2*d*Rg)   ->  0  like Rg^2
C_D = 2*Rg*delta*(exp(d*Rg) - 1)^2 + (4/3)*delta^3*Rg^3 ->  0  like Rg^3
```

so `C_min -> 0` and the allowed budget `delta / (2*C_min) -> +infinity`. The
cost side grows, but only like the inverse width: for a window of half-width `R`
the Gram entries tend to `2R` as `R -> 0` at fixed *low* frequency, giving
`K_loc ~ ‖pattern‖^2 / (2R)`, hence

```text
ceiling  =  2*Ru * K_loc_u * (1 + eps') * (1 + eps) * K_loc_f
         ~  2*Ru * (‖v‖^2 / 2Ru) * (‖y‖^2 / 2Rf)  =  ‖v‖^2 ‖y‖^2 / (2 Rf)
2 * C_min * ceiling / delta  ~  Rg^2 / Rf  ->  0   as the windows shrink
```

The controlling small parameter is therefore `Rg^2 / Rf`, and route alpha's
`Rg <= 0.34657` pushes toward PASS rather than away from it. This is an
asymptotic **structure** statement (algebra in the locked formulas), not a rig
digit; whether the actual cells pass is exactly what 1390 gates.

Two honest caveats on that scaling. First, node `rho` carries
`|Im rho| ~ 14.13`, so `|s_i + conj s_j| * R` is **not** small at `R ~ 0.1`; the
Gram is genuinely oscillatory and `K_loc` can be much larger than the
low-frequency heuristic. Second, the heuristic ignores which of `C_C`, `C_D`
attains the minimum. Both are what the rig measures.

## 6. Correction of the 1388 section 0 over-claim

1388 section 0 stated that R1 makes `(FIT)` close "with ZERO new analysis". The
recon splits that claim:

```text
BUDGET SIDE (hfit)        TRUE and now stronger.  Route alpha needs no
                          iterate, no decay constant, no height tail.  The
                          record-1385 wrapper funds ||u||_2^2 and the
                          record-1386 assembly funds the ceiling directly.

HEALTHY-DATA SIDE         FALSE.  The wiring does not close for free; it
                          terminates at
                              0 < archimedeanTerm g.convolutionSquare
                          which is a PRE-EXISTING open sign, not a new one.
```

`C1HealthyDetectorArchRescue.lean:7-11` records its provenance:

```text
Records 1080/1081 introduced a conditional ROOT-supported branch whose open
sign is `0 < archimedeanTerm g.convolutionSquare` on a pinned
triple-vanishing test. This sign promotes the test to strict-negative detector
data. It is distinct from the active C3/P2 premise `qw >= 0` ...
```

N2beta does not create this gate and does not claim to close it. What N2beta
does add is that the gate's owner can now be chosen to carry a funded L2 bound
at the same time — the same-owner discipline of 009 section 2.

One structural observation that makes the gate less coupled to the budget than
it looks: `archimedeanTerm` is **linear** in its argument
(`C1SameOwnerWeil.lean:61-64`, a linear combination of `F.test 0` and an
integral of `archimedeanIntegrand F`), and `convolutionSquare` is quadratic in
`g`, so `g |-> archimedeanTerm g.convolutionSquare` is homogeneous of degree 2.
Its **sign is therefore scale-invariant**:

```text
archimedeanTerm (c*g).convolutionSquare = c^2 * archimedeanTerm g.convolutionSquare
                                          ==>  shrinking g cannot flip the gate
```

The gate constrains the *shape* of `g` (hence the window and the node pattern);
(J1) constrains its *magnitude*. They interact only through the shared window
choice, not through amplitude. That decoupling is what makes it legitimate to
run the (J1) rig of 1390 while the gate stays open.

## 7. What R1 now is, exactly

```text
+-----------------------------------------------------------------------------+
| R1  Build ONE owner g = u.convolution f (component 4's owner) such that     |
+-----------------------------------------------------------------------------+
| (a) u realizes v = (1, 1, 1, 1) on {0, 1/2, 1, rho}, window (-Ru, Ru)       |
|     f realizes y = (0, 0, 0, -1) on the same nodes, window (-Rf, Rf)        |
|     -> record-1385 taper wrapper, twice.            FUNDED, mechanical      |
|                                                                             |
| (b) laplaceAt g = v_i * y_i = (0, 0, 0, -1)                                 |
|     -> record-1387's two value hooks (mul_zero / mul_ne_zero).  FUNDED      |
|     -> gives HealthyMinimalLaplaceRealizes rho g                            |
|                                                                             |
| (c) support g.test subset Icc (-(Ru+Rf)) (Ru+Rf) subset Icc(-log2/2,log2/2) |
|     -> component 4's summed window + ONE numeric inequality Ru+Rf<=log2/2   |
|                                                                             |
| (d) compactLogL2sq g <= 2Ru*(1+eps')K_loc_u*(1+eps)K_loc_f =: ceiling       |
|     -> component 4's exists_assembledOwner_cost_le.  FUNDED                 |
|                                                                             |
| (e) ceiling < delta/(2*C_min)                        -> (J1), rig-gated     |
|                                                                             |
| (f) 0 < archimedeanTerm g.convolutionSquare          -> OPEN, pre-existing  |
+-----------------------------------------------------------------------------+
```

Items (a), (b), (d) are wiring over green components. Item (c) is one numeric
side condition. Item (e) is what 1390 measures. Item (f) is the register's
long-standing open sign and is **the** remaining science on this branch.

R1 is therefore "half a day of wiring" for (a)-(d) — the original estimate
holds — but the honest total for *closing 009* is (e) plus (f), and (f) is not
an N2beta obligation.

## 8. Boundary

No Lean was written. No build was run. No digit was computed; the only numbers
above are definitional constants read out of source (`log(2)/2`, the grid
radii already committed in 1388) and algebraic asymptotics of formulas already
committed in 1378 and 1386. The sign `log(4*pi) + gamma > 0` used implicitly in
section 6 is proved, not measured: `4*pi > 1` gives `log(4*pi) > 0`, and the
Euler--Mascheroni constant is positive.

No claim about actual zeta zeros is made: every `rho` in this record is a
hypothetical off-line zero. No RH inference in either direction.
