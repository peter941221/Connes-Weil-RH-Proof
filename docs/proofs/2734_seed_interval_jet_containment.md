# Record 2734: source derivative interval-jet containment

Task card: actual Real.smoothTransition and same stored seed calculus.
Premise to remove: interval derivative-jet containment, using existing
RealInterval2429 operations rather than a new interval type/provider.
Consumer: finite-region derivative bounds for the2730 D4/D7 integration.
Completion: kernel-checked reciprocal/product/exp jet propagation and
actual transition cell containment; standard-trio audit; one bounded
representative-cell convention control. Budget one module+audit,
<=40minutes, <=4GiB storage, single-threaded. No8192-cell replay.
Stop on failed containment/control or an unavailable analytic premise;
record the scoped gap rather than extend. Previous turn was PROGRESS:
2733 actual endpoint integral certificate was proved and pushed.

The existing real interval algebra supplies addition, subtraction,
multiplication, positive reciprocal and exponential membership laws.
The canonical enclosure uses exact real exponential endpoints; turning
these into rational bounds remains a separate certificate obligation.


## What is enclosed

A derivative jet is the sequence of actual derivatives at one point;
slot n is the n-th derivative, not a Taylor coefficient divided by n!.
The interval jet replaces each real slot by lower and upper endpoints.
Membership means the actual derivative lies between those endpoints.

The construction reuses RealInterval2429's proved arithmetic. Its route
from a cell B is:

```text
B=[lo,hi], 0<lo<=x<=hi<1
       |
       +--> jets of x and 1-x
                    |
              positive reciprocals
                    |
              F=1/(1-x)-1/x
                    |
                 E=exp(F)
                    |
              R=1/(1+E)
                    |
                 T=E*R
                    |
       interval contains actual T^(n)(x)
```

The reciprocal interval recurrence is proved from differentiating
f*(1/f)=1 in a neighborhood where f is nonzero, then isolating the
highest derivative. The exponential recurrence uses the actual source
phase theorem from2731. Interval sums and products preserve membership;
strong induction carries this through the recursively defined jets.
The initial affine jets are proved from derivatives of x and 1-x.

The final `seedTransitionJetInterval_mem2734` theorem assumes only
geometric cell conditions and x membership. It has no supplied derivative
upper bounds, floating data or target conclusions. It holds for every
natural order n; the intended finite certificate only uses orders<=7.
`norm_iteratedDeriv_le_seedCellJet2734` reads the interval's endpoint
absolute maximum as an upper bound on the actual derivative norm.

## Exact-real scope versus numerical replay

The canonical base exponential interval is [exp(F_lo),exp(F_hi)] with
exact real endpoints. This establishes the mathematical enclosure
algorithm, not a certificate for mpmath's rounded endpoints. The generic
exponential helper can also accept a separately certified starting box,
but those rational exponential bounds still need proof before replay.
No claim is made that arbitrary machine intervals contain these exact
canonical endpoints merely because sample tests pass.

Next obligations are rational exponential endpoint certification,
outward rational operation replay and the finite partition integral.
Then combine with the already proved2733 endpoint charge and the
seed-to-transition integration identity. D4/D7 integral hypotheses,
cardinal pins, carrier re-seed and genuine-rho gate remain open.

## One-cell convention control

Only the original8192-grid cell with index4096 is evaluated. The control
independently implements the displayed interval recurrence at40-digit
interval precision, compares all eight slots with the unchanged2720
engine, and checks direct80-digit numerical differentiation at its left,
midpoint and right points. All34 checks pass; the worst normalized
endpoint difference is2.09416452359504e-39 (the implementations use
inverse multiplication versus division in the reciprocal step).

The1e-25 comparison gate is a convention/implementation diagnostic,
not a certified rounding allowance. The three points per slot are not
a whole-cell proof: whole-cell containment comes from the Lean theorem
for exact real arithmetic. No grid sweep or large rollout was performed.
Evidence: `scripts/seed_interval_jet_control_2734.py` and
`results/2734_seed_interval_jet_control.json`.


## Verification

Focused Linux-native build, LEAN_NUM_THREADS=1 under the resource runner:

    lake build ConnesWeilRH.Dev.C1SeedIntervalJet2734Audit

Build completed successfully (3654 jobs). All13 theorem leaves have
exactly [propext, Classical.choice, Quot.sound]. No new-entry warnings
or errors. Source copies and compiled objects are current, and the reused
interval algebra and2731 source definitions match the reviewed copies.
The source readback passes27/27 gates, including exact cell-domain binder
pins at each declaration plus a global count, and the current control hash.

    python3 scripts/check_seed_interval_jet_2734.py --workspace WORKSPACE
    python3 scripts/seed_interval_jet_control_2734.py

WORKSPACE denotes the Linux-native verification checkout. The portable
proof artifact is `results/2734_seed_interval_jet.json`; the separate
one-cell diagnostic artifact is named above. Neither artifact contains
local verification paths. Shared Dev objects are retained; no disposable
entry assembly was generated. Target disk remains289GiB free.

This completes the bounded mathematical containment target. It licenses
no automatic cell rollout: rational exponential bounds, exact outward
arithmetic replay and finite integration still need their own proof and
cost gates. The binding route and the row-B reopen scope are unchanged.
