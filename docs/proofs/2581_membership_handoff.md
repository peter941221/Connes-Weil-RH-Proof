# Record 2581: external coefficient-membership handoff

Date: 2026-10-05

Status: EXTERNAL-MEMBERSHIP-HANDOFF-PASS. This record binds the exact
analytic repair artifact to the correction coefficient boxes consumed by the
2570/2574 chain. It is not a Lean membership theorem and does not claim
producer GO or RH.

## Verified chain

The validator checks all of the following in one run:

- record 2338 is the 30 by 30 exact analytic moment-matrix repair;
- the certified Neumann defect is below 1/2;
- the interval solve residual contains zero;
- all 30 correction coefficient rows are present;
- the 2564 correction margin artifact is derived from the same 2338 hash;
- all 30 representative truncations are inside the correction boxes;
- the correction box L1 half-diagonal has slack 1.5580206698597658x;
- the generated 2570 box source carries the same 2338 source hash;
- the generated center source still states membership as a consumer premise.

The resulting handoff fields are:

matrix dimension                         30
Neumann defect < 1/2                     true
solution interval residual contains 0    true
correction rows checked                  30
representatives inside boxes              30/30
correction box slack                      1.5580206698597658x
smallest truncation exponent              95
Lean membership theorem                   false
owner transfer to live consumer           false
producer_go                               false
rh_claim                                  false

## Boundary

The external Arb certificate establishes an enclosure for the unique finite
analytic interpolation solution. The Lean source currently imports the exact
box endpoints and proves the distance estimate conditional on box membership;
it does not yet prove that the live analytic owner inhabits those boxes.

The next formal obligation is therefore the matrix/operator transfer, not more
local second-chord cells.

## Evidence

- scripts/validate_membership_handoff_2581.py
- results/2581_membership_handoff.json
- results/2338_exact_interpolation_repair.json
- results/2564_membership_margin_probe.json
- ConnesWeilRH/Dev/C1RouteACorrectionCoefficientBoxes2570.lean
- ConnesWeilRH/Dev/C1RouteACorrectionCenterNode2570.lean
