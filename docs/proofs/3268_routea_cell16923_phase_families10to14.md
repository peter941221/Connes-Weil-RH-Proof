# 3268: Route A cell-16923 phase families 10..14

Status
------

Lean-verified phase infrastructure. This record does not prove the complete
finite-window aggregate, the full-line tail, B5 readback, `producer_go`,
`SourceRH`, or RH.

Method
------

The formal weighted-original negative witness is cell 16923. For families
10 through 14, the generator propagates rational complex rectangles through
the nine repeated-squaring stages needed to represent the 512-fold phase.
The base rectangle is checked against `phaseRect3218`; every later rectangle
is checked against the exact four-corner product of the previous rectangle.

The focused build runs in WSL2 ext4 with `leanprover/lean4:v4.30.0` and Lean
4.30.0. The independent audit reports exactly:

    [propext, Classical.choice, Quot.sound]

Reproduction
------------

    python scripts/generate_routea_phase_boxes_16923_3268.py
    lake build ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseFamilies10to14TightStaged3268
    lean ConnesWeilRH/Dev/C1RouteAConcreteOwnerPhaseFamilies10to14TightStaged3268Audit.lean

Source and audit
----------------

    ConnesWeilRH/Dev/C1RouteAConcreteOwnerPhaseFamilies10to14TightStaged3268.lean
    ConnesWeilRH/Dev/C1RouteAConcreteOwnerPhaseFamilies10to14TightStaged3268Audit.lean
