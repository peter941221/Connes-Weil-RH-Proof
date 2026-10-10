Record 2653: live-tuple transfer seam — the stability composition over cell2700 GREEN
Date: 2026-10-10

Result

Positive: `ConnesWeilRH/Dev/C1RouteALiveTransfer2653.lean` built green
(`ℹ [3929/3929] Built ConnesWeilRH.Dev.C1RouteALiveTransfer2653 (51s)`
+ `Build completed successfully (3929 jobs)`; 0 error, 0 `uses sorry`,
0 module warning; all three theorems depend only on
`[propext, Classical.choice, Quot.sound]`).

Three theorems landed:

    capBase_gap_2653                 live 2275-capture tuple is OUTSIDE
                                     the 1/10^30 certificate ball, with
                                     the EXACT max gap 4.6186100724e3
                                     (attained at family 0)
    cell2700_live_transfer_2653      conditional seam: bounded change
                                     integral extends the cell2700
                                     certificate to ANY tuple
    cell2700_capBase_transfer_2653   the seam instantiated at the live
                                     tuple

The exact constant (87-digit numerator over the record-2338
denominator) is the true maximum over the 30 families of
|dre| + |dim| between `capBaseCoef2452` and the record-2338 box
centers.

Audit correction inside the record

The float-derived gap estimate carried since the 2649-era analysis,
`147795/32 = 4618.59375`, is BELOW the true maximum
`4618.61007243...` — Lean itself falsified it: with that constant the
case-0 `norm_num` goal reduced to `False`, which is how the first
build failed.  The replacement is the exact rational computed from
the 2338 payload and the 2452 literals.  Law: display-text numbers
are not certificates; every constant that enters a Lean case-bash
must be re-derived exactly from payloads/literals (AGENTS 2cn).

What the seam proves — and what it does not

The transfer is a STABILITY composition, not a membership check:
membership of the live tuple in the record-2338 boxes is false by
4.6e3 orders over the 1/10^30 ball.  Instead,

    ∫ ‖P(c)‖ ≤ ∫ ‖P(c) − P(center)‖ + ∫ ‖P(center)‖  (triangle)
    ∫ ‖P(c) − P(center)‖ ≤ baseTransformChangeUpper2653  (PREMISE)
    ∫ ‖P(center)‖ ≤ 57/5·10^11  (cell2700_center_discharge2650)

so the cell2700 certificate reaches any tuple — in particular the
live one — as soon as its change integral is bounded.

The premise is NOT discharged here.  The 2338 record itself declares
`owner_transfer_to_live_consumer = false`: its strip constant covers
the 2338-internal repair delta, not the live-tuple delta (gap scale
4.6e3 at family 0).  Certifying
`∫ ‖P(capBaseCoef2452) − P(center)‖` over the edge span is the
residual content of audit unknown #1; the seam theorem is its waiting
consumer.  Proof mechanics that worked (positional
`integral_mono_on hab hfint hgint hpt` with ascribed
`IntervalIntegrable ... volume a b` haves; `rw` of a `funext fun x =>
rfl` pointwise-to-Pi bridge before `integral_add`; linarith on the
shared atoms) are recorded as AGENTS 2cn.

Scope

cell2700 edge span only; conditional transfer; no full-grid claim;
no Weil-positivity conclusion (the bounds are integrals of norms);
Producer GO, SourceRH, RH remain open.

Next obligations

1. Live change-integral enclosure (unknown #1 residue): bound
   ∫ ‖P(capBase) − P(center)‖ on the cell2700 span by its own
   certified computation; the seam then fires unconditionally.
2. Grid scale-out deliverables for record 2654 (cells 2703/2704 both
   signs built GREEN in the same session): discharge brick, payload,
   docs record.
3. Parallel 2649 lane: 190-panel partition over column 3, then the
   (0,3) entry containment against the committed 2597 rectangle.
