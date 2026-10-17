# Record 2746: historical jet fault controls

Three independently injected faults reproduce the 2743 errors. Collapsed
coordinate cells fail 24 sampled containments; wrong exponential coefficients
fail 18. Reversing phase endpoints initially escaped final sampled tests:
subsequent arithmetic can mask an invalid intermediate interval. Interval
construction now rejects lower > upper immediately, detecting that fault.

The baseline remains valid under diagnostic sampled checks. Fault injection
runs isolated copies of the function and never changes the checked source.
Normal 2743 and refinement 2745 runs are repeated after the new invariant.
These controls guard the numerical instrument; no continuum/Lean replay or
D4/D7 claim follows.
