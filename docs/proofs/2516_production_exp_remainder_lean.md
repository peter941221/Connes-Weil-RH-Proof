# Record 2516 — production remainder instantiation

The 2516 theorem instantiates the exponential-upper remainder interface on
the certified production safe range `196..443`.  It uses the 2508 envelope in
those cells and explicitly keeps the existing L1 curvature fallback elsewhere
in the 640-cell strip.  This is a Lean remainder bound, not a completed
numerical margin audit.

Evidence: `ConnesWeilRH/Dev/C1RouteAExpProductionRemainder2516.lean` and its
audit.
