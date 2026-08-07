# Proof-717 / Gate-3U: 841 — Route-C DOES avoid the 3U lambda-wall; its open point is the Yoshida pole-pairing detector EXISTS axiom (a different, lambda-free floor), not the generic-lambda prolate HS

Date: 2026-08-07 · Status: audit verdict (build-informed). This answers the
"escape via Route-C" option: Route-C is a **separate tree** that never consumes
the generic-lambda prolate HS, but it still bottoms at RH in an axiom (the
Yoshida detector existence), so it does not lower the analytic floor to zero --
it relocates it.

SOURCE: `Route/CC20RouteRealization.lean`, `Source/CC20PropositionC1.lean`,
`Source/CC20YoshidaCriterion.lean`, `Dev/UnconditionalSkeleton.lean`.

## 0. Result (先讲结论)

**Route-C completely avoids the generic-lambda prolate HS --- yes, it really
skips the 3U lambda-wall.** But it does not push the floor to zero: it moves
the gate/floor to the **Yoshida detector existence (pole-pairing nonnegative
realizer)** as a single axiom.

```
Route        Core object                    generic-lambda prolate HS?   open root
--------     ----------------------------   ---------------------------  ------------
Route 3U     Metric endpoint-norm           REQUIRED (blocked 839/840)   generic-lambda HS
             canonicalRealGate3UAt
Route C      CC20 trace / carrier            NO (fully avoided)           Yoshida detector
             CC20YoshidaCriterion            (CC20RouteRealization        pole-pairing
                 contains no prolate)        has no Prolate reference)      axiom
```

The lambda-free nature is not free: the input `CC20YoshidaDetectorExists` is
hung on `RiemannHypothesis` (`UnconditionalSkeleton:5890-5894` proves
`PolePairingNonnegativeCore <-> RH`), so it is another RH-scale existence face,
not a reduction of an HS-scale fact to zero.

## 1. Evidence A: Route-C is prolate- and lambda-free(by source grep)

- `Route/CC20RouteRealization.lean`: full grep for `prolate|Prolate|Sonin|
  sourceSonin|FourierSupport|Summable ‖` -> **0 hits**. Route-C never reaches
  `sourceProlateHilbertSchmidtFactor`.
- `Source/CC20YoshidaCriterion.lean` defines `CC20YoshidaDetectorExists`
  (L35-41) as: for every nontrivial zero rho, a compact-support smooth test D
  with non-diagonal Mellin value at rho and positive Weil local sum off line.
  All `Weil-sum / Mellin`, no prolate.
- `Source/CC20PropositionC1.lean` theorem `cc20_proposition_c1_from_yoshida_
  detector` (L213) closes to `SourceRH` from detector exists + finite-vanishing
  criterion only.

Conclusion: Route-C's lambda-scale is lifted out of the trace chain at the
implementation layer (per-common fixed carrier `FixedLambdaCommon` /
`common.sourceTest`, the S2 refactor), so the prolate factor is simply never
instantiated.

## 2. But the open item is the same RH floor

`Dev/UnconditionalSkeleton.lean`:

```
5894  theorem ...PolePairingNonnegativeCore_iff_mathlibRH :
5895    Normalized..PolePairingNonnegativeRealizer <-> _root_.RiemannHypothesis
5896  axiom  normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot :
5897    Normalized..PolePairingNonnegativeRealizer
```

So: the pole-pairing detector existence is an **axiom** (`...CoreRoot`) and it
is iff Mathlib RH. Together with the 41 total axioms (this included) and 1
`sorryAx`, the "Route-C avoids lambda" claim does not mean "Route-C avoids all
RH-floor"; it swaps the analytic load-bearer from generic-lambda prolate HS
(blocked) to "exists a pole-pairing probe with the Weil local-sum sign" -- still
a guess-level premise near the critical law.

## 3. The two-route comparison (final)

| dimension        | Route 3U (prolate tree)            | Route-C (Yoshida tree)        |
|------------------|------------------------------------|-------------------------------|
| load factor      | generic-lambda HS `Summable ‖F‖`   | pole-pairing detector exists |
| lambda scale     | INSIDE factor (blocked 840)        | per-common fixed carrier      |
| proved (clean)   | unit-lambda HS axiom-clean (839)    | Yoshida criterion fully      |
| open axiom       | needs generic-lambda HS (blocked)  | `PolePairingNonnegCoreRoot`  |
| distance to RH   | via `hfactor` premise              | axiom IFF RH (UncondSkel)     |

Therefore "escape via Route-C" technically **does** skip the 3U lambda wall -- a
real analytic advantage (prolate-free). But it keeps/adds the **same RH-level
existence axiom** (`PolePairingNonnegativeCore`); it does not replace that axiom
by something provable or simpler.

## 4. Verdict / honest ceiling

1. **Avoids**: Route-C does not consume generic-lambda prolate HS -- the 840
   blocking point does not bind Route-C.
2. **Not free**: Route-C's evidence bottoms at `axiom PolePairingNonnegative
   CoreRoot` (5904), and that axiom IFF Mathlib RH (5894); i.e. it is itself a
   dual to "all non-trivial zeros lie on the line" -- it moves the "generic-lambda
   HS" wall to a "pole-pairing detector exists" wall.
3. **Choice**: if the goal is "do not have the 3U operator/HS wall blocking the
   numeric route", Route-C is the right choice (relocation). If the goal is "a
   carrier not needing to assume RH", Route-C and 3U are the same floor -- both
   need some existence face at zero-detection. The former sidesteps an operator
   corner; the latter is that aspect's API-dual.
4. **Next step honest**: Route-C is not "a place to fill a different hole", it
   is "the same gap, differently stated". A real move on RH is still either
   (1) push pole-pairing detector existence (a real harmonic/probe estimate), or
   (2) close the line-energy cancellation (the cross-branch cancellation of the
   837 line). Merely re-selecting the axiom does not get you closer.

## Repro

```
# no new probe; conclusions from source grep + ledger read. Baseline:
WSL  lake build ConnesWeilRH.Source.CC20YoshidaCriterion
     lake build ConnesWeilRH.Source.CC20PropositionC1
```