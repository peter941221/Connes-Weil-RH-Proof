# 1578 — W0 lands: the archimedean symbol is pinned in closed form, C' = log(pi); and 1417 §3b's operator box is missing a committed hypothesis, so (OB) is a CONSTRAINED supremum, not a Paley-Wiener extremum

Date: 2026-09-17.

Status: PAPER + SYMBOLIC. Zero Lean, zero digits presented as evidence, zero
rig. This is the first spend of [map 011](../map/011_arakelov_bridge_program.md)
track W, executed owner-selected after
[1577](1577_b3_composite_phantom_verdict_and_card_repricing.md). It satisfies
milestone A1 as the same computation. RH not claimed.

```text
+====================================================================+
| VERDICT                                                            |
+====================================================================+
| 1. C' IS PINNED, in closed form, from committed definitions only:  |
|                                                                    |
|      Psi(xi) = log(pi) - Re psi(1/4 + i pi xi)                     |
|      Phi(r)  = log(pi) - Re psi(1/4 + i r/2),   r = 2 pi xi        |
|                                                                    |
|    i.e.  C' = log(pi) = 1.1447298858494001741...  (proof in s1)    |
|    The head coefficient log(4pi)+gamma = 3.108239911870824         |
|    CANCELLS against the -gamma inside psi(1/2) = -gamma - 2 log 2, |
|    which is why it never appears in the final symbol.              |
|                                                                    |
| 2. THE BOX WAS WRONG IN A THIRD WAY. 1417 s3b's `(OB) ?== sup over |
|    PW_R` drops a committed hypothesis: the window class also       |
|    carries `laplaceAt g (1/2) = 0`. So (OB) is a supremum over a   |
|    codimension-one complex subspace of PW_R, and an extremum found |
|    on all of PW_R is NOT a counterexample to it (s2).              |
|                                                                    |
| 3. FORM DOMAIN named (s3); the corrected obligation is stated (s4);|
|    what W1 must now actually use is identified (s5).               |
+====================================================================+
```

## 1. The pinned symbol, derived from committed source

The two committed readouts, verbatim:

```lean
-- ConnesWeilRH/Source/CCM25Concrete/SelectedWeilFormula.lean:96-109
noncomputable def archimedeanNumerator (owner : ...) (y : ℝ) : ℂ :=
  (Complex.ofRealCLM (Real.exp (y / 2)) *
      (owner.convolutionSquare.test y + owner.convolutionSquare.test (-y)) -
        2 * owner.convolutionSquare.test 0)
/-- The denominator `2 sinh y` of the archimedean density. -/
noncomputable def archimedeanDenominator (y : ℝ) : ℝ :=
  Real.exp y - Real.exp (-y)
noncomputable def archimedeanIntegrand (owner : ...) (y : ℝ) : ℂ :=
  owner.archimedeanNumerator y / (archimedeanDenominator y : ℂ)

-- ConnesWeilRH/Dev/C1SameOwnerWeil.lean:61-64
noncomputable def archimedeanTerm (F : CompactLogTest) : Real :=
  ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
        F.test 0) +
      ∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y).re
```

and the half-density square, verbatim:

```lean
-- ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean:114-124
noncomputable def convolutionSquare (g : CompactLogTest) : CompactLogTest :=
  g.involution.convolution g
theorem convolutionSquare_neg (g : CompactLogTest) (x : ℝ) :
    g.convolutionSquare.test (-x) = star (g.convolutionSquare.test x)
```

`F = g * g~` is Hermitian, so `F y + F (-y) = 2 Re F y`, `F 0` is real, the
outer `.re` is a no-op, and with `e^y - e^{-y} = 2 sinh y` the functional is

```text
  (D1)  A(g) = (log 4pi + gamma) F(0)
               + int_0^inf [ e^{y/2} Re F(y) - F(0) ] / sinh y dy
```

Under the repository's Fourier convention `g-hat(xi) = int g(x) e^{-2 pi i x xi} dx`
(Mathlib's, record 1331 s1), `F-hat = |g-hat|^2`, `F(0) = int |g-hat|^2`, and
`Re F(y) = int |g-hat(xi)|^2 cos(2 pi y xi) dxi`. Substituting into (D1),

```text
  A(g) = int |g-hat(xi)|^2 Psi(xi) dxi,
  Psi(xi) = (log 4pi + gamma) + J(2 pi xi),
  J(s) := int_0^inf [ e^{y/2} cos(s y) - 1 ] / sinh y dy
```

**J converges without regularisation** - which is the first correction to 1417
s2, where the same integral was called renormalised and the counter-term was
left implicit. Near `y = 0` the numerator is `y/2 + O(y^2)` against
`sinh y = y + O(y^3)`, so the integrand tends to `1/2`; at infinity
`e^{y/2}/sinh y = O(e^{-y/2})`. The subtraction is inside one integrand, so no
separately divergent piece is ever formed.

Derivation, five steps, each justified:

```text
 (a) 1/sinh y = 2 sum_{k>=0} e^{-(2k+1)y} on (0,inf), uniform on [d,inf); the
     k-th combined integral is O(k^-2), uniformly for d in [0,1], which
     dominates the exchange of sum and integral.

 (b) J(s) = 2 sum_k [ int_0^inf e^{-(2k+1/2)y} cos(sy) dy
                      - int_0^inf e^{-(2k+1)y} dy ]
          both converge separately, so no regularisation is used;
          int_0^inf e^{-a y} cos(sy) dy = a/(a^2+s^2), int_0^inf e^{-b y} dy = 1/b.

 (c) with a_k = k + 1/4  (so 2k+1/2 = 2 a_k):
     J(s) = sum_k [ (k+1/4)/((k+1/4)^2 + (s/2)^2) - 1/(k+1/2) ].

 (d) Re 1/(k+a-ib) = (k+a)/((k+a)^2+b^2), and
     sum_k [ 1/(k+z) - 1/(k+w) ] = psi(w) - psi(z)   (from
     psi(w) = -gamma + sum_k [1/(k+1) - 1/(k+w)]), so adding and subtracting
     1/(k+1/4):
     J(s) = Re[psi(1/4) - psi(1/4 - i s/2)] + [psi(1/2) - psi(1/4)]
          = psi(1/2) - Re psi(1/4 + i s/2).

 (e) psi(1/2) = -gamma - 2 log 2  (Gauss). Therefore
     Psi(xi) = log 4pi + gamma - gamma - 2 log 2 - Re psi(1/4 + i pi xi)
             = log(4pi/4) - Re psi(1/4 + i pi xi)
             = log(pi) - Re psi(1/4 + i pi xi).            QED
```

```text
  +----------------+----------------------------------+------------------+
  | quantity       | closed form                      | value            |
  +----------------+----------------------------------+------------------+
  | C'             | log pi                           | 1.14472988584940 |
  | head H         | log(4pi) + gamma                 | 3.10823991187082 |
  | Phi(0) = max   | log pi + gamma + pi/2 + 3 log 2  | 5.37218341922567 |
  | tail           | Phi(r) = log(2pi) - log|r| + o(1)| -> -infinity   |
  | r_0 (first 0)  | Re psi(1/4+ir/2) = log pi        | 6.28983598883690 |
  | xi_0 = r_0/2pi |                                  | 1.00105848886069 |
  +----------------+----------------------------------+------------------+
```

`Phi(0)` uses Gauss's `psi(1/4) = -gamma - pi/2 - 3 log 2`, so the maximum of
the symbol is itself a closed form. `r_0` is the constant 1417 §2 deferred
naming "until pinning C' ... would violate law F18"; it is named now, and `r_0`
is within 0.1% of `2 pi`. The `r_0` digit is an evaluation of the pinned closed
form (residual `2.9e-42` at 50 digits), not a measurement; law 65 still applies
until Lean reads the same expression.

This settles A1 as a by-product and, contra map 011 §W0's expectation that the
head term "does not yet have a numeric rival", the head is *absorbed*: what
survives is `log pi`, not `3.1083 + C'`.

## 2. The correction: the window class has a second committed hypothesis

1417 §3b's box reads `sup { <g0, T_K_eff g0> : g0 in PW_R, ||g0||_2 = 1 }`. The
committed theorems that the box is supposed to reinterpret carry TWO
hypotheses:

```lean
-- ConnesWeilRH/Dev/C1MinimalWeilCriterion.lean:263-271
theorem qw_nonneg_of_archimedeanTerm_nonpos_of_vanishesOn_halfOnly_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
      {CriticalVanishingPoint.half} g)
    (hsupport : Function.support g.test ⊆
      Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (harch : C1SameOwnerWeil.archimedeanTerm g.convolutionSquare ≤ 0) :
    0 ≤ C1SameOwnerWeil.qw g
```

Unwinding `hvanishes` through the committed realizations, verbatim:

```lean
-- ConnesWeilRH/Source/CC20TestSpace.lean:28-34
def CC20VanishesOn (C : CC20TestSpace) (F : Finset CriticalVanishingPoint)
    (g : C.Test) : Prop :=
  ∀ p : CriticalVanishingPoint, p ∈ F → C.mellinAt g (criticalVanishingPointValue p) = 0

-- ConnesWeilRH/Source/CC20RHExit.lean:26-29
noncomputable def criticalVanishingPointValue : CriticalVanishingPoint → ℂ
  | zero => 0  | half => (1 / 2 : ℂ)  | one => 1

-- ConnesWeilRH/Dev/C1HealthyTestSpace.lean:44-47  (the mellinAt slot)
  mellinAt := CompactLogTest.laplaceAt

-- ConnesWeilRH/Source/CC20YoshidaConvolution.lean:35-37, 55-56
noncomputable def exponentialWeight (f : CompactLogTest) (s : ℂ) : CompactLogTest := ...
  let raw : ℝ → ℂ := fun x => Complex.exp (s * (x : ℂ)) * f.test x
noncomputable def laplaceAt (f : CompactLogTest) (s : ℂ) : ℂ :=
  ∫ x : ℝ, (exponentialWeight f s).test x
```

so the omitted hypothesis is exactly

```text
  hvanishes   <=>   laplaceAt g (1/2) = 0   <=>   int_R g(x) e^{x/2} dx = 0
```

and in the Fourier coordinate, since `g` is compactly supported and hence
`g-hat` is entire of exponential type `2 pi R = pi log 2`,

```text
  int g(x) e^{x/2} dx = g-hat(i / (4 pi))        because  -2 pi i xi = 1/2
  ==>  the window class is   { h entire, type <= pi log 2, in L2(R),
                               h(i/4pi) = 0, h = g-hat with supp g in [-R,R] }.
```

That is a codimension-one COMPLEX linear condition, and it is not decorative:
`Phi` attains its maximum `+5.372` at `xi = 0`, and the condition removes the
freedom to place `|g-hat|^2` there at will. `e^{x/2}` on `[-R,R] =
[-0.3466, 0.3466]` ranges only over `[2^{-1/4}, 2^{1/4}] = [0.841, 1.189]`, so
the condition is "weighted mean zero with a mild tilt", which forces `g` to
change sign, which is what pushes `|g-hat|^2` out of the positive core. This is
the concrete mechanism behind 1417 §3b's assertion that the uncertainty
principle is the positivity source on this class - previously that claim rested
only on the support-width argument, which is much weaker than a linear
constraint landing on the peak.

**The diagnostic that caught it.** An unconstrained Galerkin pass on all of
`PW_R` returns a positive maximum (increasing with the trial subspace). Taken at
face value that is a counterexample to `(OB)`, hence `qw g < 0` for an
admissible `g` (the prime sum vanishes on the class), hence failure of the
machine-checked gate `(∀ g, 0 ≤ qw g) ⟺ SourceRH`, hence **not-RH, produced by
one hour of linear algebra**. That conclusion is far more probably a defect in
the computation than a disproof of RH, and the defect was then located in the
committed source: the trial class was a strict superset of the obligation's
class. Two independent problems compound in the discarded number - wrong class,
and a trial basis whose orthonormality sentinel (`Psi ≡ 1` must give the
identity matrix) had not been run. See s6.

Recorded as law F28: **before extremizing an obligation, read
its full membership hypothesis set from source; a violation found on a
superset is not a counterexample, and a result whose consequence is absurd is
evidence against the computation, not against the theorem.**

## 3. The form domain, named

`Phi` is bounded above (`max Phi = Phi(0)`) and unbounded below (`-log|r|`), so
`T` is an unbounded-below self-adjoint multiplier: 1418 §5's objection that
`lambda_max` is not a quantity stands, and it is fixed by taking a form, not an
operator. The maximal natural domain of the form on the window is

```text
  D = { g in L2(R) : supp g ⊆ [-R,R],  int |g-hat(xi)|^2 log(1+|xi|) dxi < ∞ }
```

(the log-moment condition is exactly `A(g) > -infinity`, since
`Phi(2pi xi) = log(2pi) - log|xi| + o(1)`; the upper bound needs no condition
because `Phi <= Phi(0)`). The committed class is
`D ∩ { laplaceAt g (1/2) = 0 } ∩ { g smooth }`, and `CompactLogTest` -
`C^∞` with compact support - sits inside it, so `(OB)` is stated over a class
where every quantity is finite without further convention. Attainment of the
supremum remains open and is not needed: 1417's `-log` tail means the form is
not compact, so W1 must be an inequality, not an eigenvalue computation.

## 4. The corrected (OB)

```text
  R = log 2 / 2,   Phi(r) = log pi - Re psi(1/4 + i r/2)

  (OB)   for all g with  supp g ⊆ [-R, R]  and  g-hat(i/4pi) = 0,
                   A(g) := int_R |g-hat(xi)|^2 Phi(2 pi xi) dxi  <=  0

  equivalently, normalising ||g||_2 = 1,
         sup { A(g) : g in C_c^∞(-R,R),  int g e^{x/2} = 0 }  <=  0
```

`A` is scale-invariant in `g`, so the normalisation is harmless. Everything in
the box is now determined: the symbol, the class, the domain, and the single
number `Phi(0) = 5.37218341922567` that bounds the positive part. map 011 §W0's
exit condition - "C' pinned, form domain named and sup decided, or a mismatch
named" - is met on the first two clauses, and on the third by naming the
mismatch between the preregistered box and the committed class.

## 5. What W1 must now use, and what it must not

```text
  +--------------------------------------------------------------+
  | the WRONG problem : max over PW_R (unconstrained)            |
  |   -> the maximiser is a prolate/Slepian function concentrating|
  |      |g-hat|^2 at xi = 0, where Phi = +5.372; the answer is   |
  |      positive and says nothing about (OB)                     |
  +--------------------------------------------------------------+
                              |
                              v  impose the committed constraint
  +--------------------------------------------------------------+
  | the RIGHT problem : max over PW_R ∩ { h(i/4pi) = 0 }         |
  |   one complex linear constraint placed exactly on the peak of |
  |   the symbol. The extremal object is therefore a CONSTRAINTED |
  |   Slepian problem: the reproducing kernel at i/4pi of the     |
  |   Paley-Wiener space must be quotiented out, i.e. the class   |
  |   is the range of (I - P_k) where k(·, i/4pi) is the kernel   |
  |   vector, and A restricted to it is the object to bound.      |
  +--------------------------------------------------------------+
```

Consequences for pricing, stated without inflation:

* The literature handle changes. Unconstrained truncated-convolution extrema are
  Slepian/Benedicks-Czaja territory; a codimension-one constraint at a complex
  point is a reproducing-kernel quotient problem. W1's technique note must be
  re-pointed accordingly.
* The constraint's strength is not obvious in either direction. One complex
  linear condition is small, but it lands on the unique maximum of `Phi`, and
  the class also has `g` sign-changing. W0 deliberately does not guess the sign
  of the constrained supremum: that is W1's content.
* Consistency check worth naming: `(OB)` on the correct class is a consequence
  of RH (via the machine-checked gate), so a positive constrained extremum would
  be a disproof of RH, and any such finding must be treated first as a defect in
  the computation until it survives a class audit.

## 6. Numerics: demoted to self-check, and what it earned

Owner instruction on this wave: attack directly where committed source can
decide, and do not open a numerical surface for a question the definitions
already answer. Applied here, the script is retained as an appendix
(`scripts/w0_window_symbol/`) with `TEST C` marked invalid for `(OB)`, and its
role is reduced to checking algebra. That role was not trivial - it caught two
real errors of mine, both of which would otherwise have entered a record:

```text
  1. Truncating (D1) at y = 2R.  Even when Re F(y) = 0 for y > 2R, the
     counter-term -F(0)/sinh y persists, and its tail is the explicit
     constant  int_Y^inf dy/sinh y = log coth(Y/2),  so truncation is wrong by
     F(0) log coth(R).  Caught because the residual matched that closed form
     to all printed digits (0.610649 vs R log coth(R/2) = 0.610649).
     This is what makes 1417 s2's "renormalised integral" remark precise:
     the renormalisation is NON-LOCAL.
  2. The integration-by-parts moment recursion for int x^k e^{-i theta x} dx
     divides by theta k times and loses catastrophic precision near theta = 0;
     it produced |g-hat|^2 of order 1e217. Replaced by the exact Taylor series
     for |theta| < 30.
  3. (still open in the script) the Legendre basis normalisation was wrong in
     the first draft; the `Psi = 1 => M = I` sentinel that would have caught it
     was never run, which is exactly why the +3.43 number must not be quoted.
```

For `C'` none of this is load-bearing: the derivation in s1 is a five-step proof
from committed definitions and needs no quadrature. Recorded as law F27:
**committed source is the first instrument; a rig is admissible
only where the answer is not decidable by reading, and never as the authority
for a claim that a hand proof already fixes.**

## 7. Boundary: what moved and what did not

```text
  MOVED
    C' pinned:            log pi            (A1 satisfied as a by-product)
    symbol:               Phi(r) = log pi - Re psi(1/4 + i r/2)
    r_0 named:            6.28983598883690278   (1417 s2's deferred constant)
    form domain:          named, s3
    (OB):               restated correctly as a CONSTRAINED supremum, s4
    1417 s3b:           third defect found and named (dropped hvanishes)
    map 011 W0:         exit condition met; W1 re-pointed at the constrained
                        Slepian/reproducing-kernel problem
    laws F26-F28:       born

  NOT MOVED
    (OB) itself is NOT proved and NOT refuted. W1 is open.
    The 1418 s5 objections to `lambda_max` are unchanged and were not
      re-litigated; this record builds on them.
    (star), S3, B4, rho4, rho5, source/ambient transport, R4: all OPEN.
    O2's radius gap: untouched, exactly as 1417 s3b warned. Even W1, if proved,
      settles the gate on the window subclass only.
    No Lean was built; nothing here is machine-checked; no number above is
      certified by Lean (law 65).
    RH is not claimed, in either direction.
```
