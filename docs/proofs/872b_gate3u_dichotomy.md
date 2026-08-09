# 872b — Gate-3U `D_S == J`: nil-side closed, nonempty side is the whole route

Date: 2026-08-09. Continuation of `docs/proofs/872`. Type: decision-confluence record
(repo-verified). No code change. RH NOT claimed. No new axiom, no sorry.

## 0. The question

User asked directly whether the Proof-717 analytic front `F + D == J` (docs/872) can be
"hit" (打 b). This records the exact truth of that front today.

## 1. Reduction (872 original, repo-verified)

`D_S == J` reduces to ONE off-Sonin component on `(range P)^perp`:

    (*)   (I − P) F  =  −(I − P) D

The P-directed envelope is already proven in Lean (all of `J^dag (F+D)=I`,
`P (F+D)=J`, `P F=0`, `P D=J`, `P J=J`). Nothing above the `(range P)^perp` component
is missing in algebra.

## 2. The only family Lean closes is the nil family (repo theorem)

`CCM24FiniteSCausalMarkovRawBase.lean:92`
`sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil`:

    family.visiblePrimes = [] -> sourcePhysicalCoframeLeakage lambda family = 0

promoting (lines 102-162) to `rawCompletePhysicalHermitianTrace = 0` on nil.

## 3. The nonempty side is NOT closed; no algebraic theorem covers it

- 872 §8 family-search: `(*)` holds iff leakage zero; the only provable family is nil.
  Any nonempty finite prime family is a genuine off-P operator that no route theorem
  annihilates.
- Numeric 824/884: `(I − P) D ≈ 0.61` flat across the whole physical scale line
  logla ∈ [-2,+2] (884 reproduces 824 exactly). The outer metric channel never decays.

Conclusion: for nonempty carriers the outer endpoint channel diverges from 0. `(*)`
is a real boundary (route-refutation risk), not a missing lemma. Not a formal Lean
counterexample (finite-grid numerics only).

## 4. Decision carry

- 打 b (prove `F == −D + J` by Lean algebra on a nonempty carrier) is only sound if we
  are willing to formally refute the route otherwise. Do not advertise a Lean refutation
  until a genuine proof lands.
- Either an exact analytic identity on `(range P)^perp` for the concrete carrier exists
  (needs the projected inner spectral family beyond a finite grid), or the route is
  refuted at its analytic bottom for nonempty families.

## 5. Recommended next (not done)

A `Dev` leaf restating `(*)` as a first-class `Prop` obligation and deriving its only
known handle from `visiblePrimes_nil` + the dichotomy
`[∀ family, leakage=0] -> ∀ family, visiblePrimes=[]`. That turns the question into an
unambiguous formal basis instead of a numeric guess.

Status: OPEN (analytic). RH unclaimed. No new axiom/sorry.
