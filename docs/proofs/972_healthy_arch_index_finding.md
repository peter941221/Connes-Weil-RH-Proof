# 972 — Healthy-carrier arch bridge: 2-fold vs 4-fold index finding

Date: 2026-08-11. Status: route finding (definitions read + docs cross-check; not a new proof).
RH NOT claimed. See also docs/958 (probe), 964/965 (dead verdict), 950/957.

## What the bridge needs

To "kill" the healthy Wall-A 1.4 refutation we need the single scalar
`arch(f*f) != 0` on the healthy carrier (`Wall14ArchReduction` / `Wall14SelfTestWitness`
hinge `healthy_target_refuted_of_arch_ne_zero`). The healthy algebra pins this value to

    healthySymbols.archimedeanTerm (healthySymbols.convolutionStar f f)
      = totalArchimedean (healthyConvolutionStar f f)             (HealthyArchData.healthyArchData_readOff)

`totalArchimedean F` (CompactArchTotal) = `compactLogArchimedeanTerm (rep F)` where `rep.test = F`,
and `compactLogArchimedeanTerm g = Re (owner(g).archimedeanTerm)` (CompactLogArchimedeanLift), where
`owner(g).archimedeanTerm` reads `owner.convolutionSquare.test = (g*g).test`
(CompactLogConvolution.convolutionSquare = involution . convolution).

## The mismatch (double square)

Feeding `F = convolution f f` (the healthy convolution square) into `totalArchimedean`:

    totalArchimedean (f * (f)) = compactArchimedean(rep with rep.test = f*f) = arch term at (f*f)*(f*f)

i.e. the **4-fold**. But the mathematically intended value (docs/958, /965, CCM25 Eq.3.7) is the
**2-fold**:

    arch(f) = (log(4π)+γ) * Re((f*f)(0)) + Integral_0^∞ ...
    leading Re((f*f)(0)) = ||f||^2 , probe arch = +0.294 (docs/958, mpmath 80-dps)

So the code double-squares relative to the stated Eq.3.7 scalar. The natural (2-fold) object is
`totalArchimedean f` (= `Re(owner(f).archimedeanTerm)`), which is EXACTLY what the new
`bumpArchimedeanTerm_re_pos : 0 < Re(bumpPlateauOwner.archimedeanTerm)` proves
(axiom-clean) for `f = bump.tests`.

## Implication + required decision

- If the healthy SCAL arch slot should read the **2-fold** (matches Eq.3.7 / docs/958),
  the wiring must feed `f` (not `f*f`) to the single-test arch / total, then the bump gives
  `arch != 0` and the healthy-wall hinge closes directly.
- If the 4-fold is what the algebra truly wants, a NEW nonnegative `Re((f*f)*(f*f))(0) > 0` + integral
  bound on the 4-fold owner is needed — NOT implied by the 2-fold closure.
This is a semantic decision on an API the route and many closed proofs depend on; record before claiming
a clean close. RH NOT claimed.

## Numeric tie-break (2026-08-11) — BOTH folds are non-zero

Quick numpy probe on the explicit plateau bump (`bumpEx`, plateau 1 on [-9/10,9/10], support [-1,1]):
- 2-fold: `arch2 = +4.76` (leading `C*g2(0)=5.83`, `g2(0)=1.876=||bumpEx||^2`); consistent with docs/958 sign (their test differs).
- 4-fold: `arch4 = +14.64` (leading `C*g4(0)=14.25`, `g4(0)=4.58=||bumpEx*bumpEx||^2`).
Both strongly positive => `arch != 0` holds under EITHER the 2-fold (docs/numeric) or the 4-fold (current Lean `totalArchimedean(convolution f f)`) reading. Numeric, not a proof. Implications:
- Direction B (prove the 4-fold owner nonzero via the generic sufficiency: lead `Re((g*g)(0))=||g||^2>0` for `g=conv bump` + a new 4-fold hI bound) is viable WITHOUT any depended-API change.
- Direction A (rewire to 2-fold) remains viable but touches depended-on algebra; B is lower-blast-radius.
Closed-suggestion: prefer B to keep the healthy algebra's reading intact and match `docs/065`'s verdict quantity.


## 4-fold hI constants + huge slack (2026-08-11, numpy probe)
4-fold owner `convBump = bumpEx * bumpEx`, lead `g4(0) = ||convBump||_2^2 = 4.584`:
- `C*g4(0) = 14.249` (C = log(4pi)+gamma),
- integral `I4 = Int_{y>0} [e^{y/2}(g4+g4(-))-2g4(0)]/(e^y-e^-y) dy = +0.391`,
- `arch4 = 14.640`, slack ratio `C*g4(0)/|I4| = 36.4 >= 1`.
So the 4-fold hI (`|I4| < C*||convBump||^2`) needs only a CRUDE upper bound;
`g4` has support in [-1,1]^(fold) so the tail `y>4` is ~ -2*g4(0)*e^-y (tiny), and
`||convBump||^2` is large (4.58). Very attackable in Lean (no tight constants needed).
Numeric, not proof. RH not claimed.


## 4-fold hI closure blueprint (2026-08-11, numeric near/tail/mid)
For owner(convBump), integrand g4=convBump.convolutionSquare.test (support in [-4,4], g4(0)=4.5842):
- max |integand|/g4(0) on (0,4] = 0.4997 (near-0 cancellation keeps it O(g4(0)), not 1/y).
- int_(0,4) integ = 0.559 ; int_(4,inf) integ = -0.168 (= -2 g4(0)/(e^y-e^-y) since g4=0).
- |int_0^inf| <= 0.727 while C*g4(0)=14.249 (C=log4pi+gamma=3.1086): margin ~19x.
Lean closure needs (mechanically): (a) near band |integ|<=g4(0) (i.e. congr to e:0 cancellation),
(b) mid bound on support width, (c) tail = -2 g4(0) small. ALL easy constants, no tight analysis.
Numeric only. RH not claimed.
