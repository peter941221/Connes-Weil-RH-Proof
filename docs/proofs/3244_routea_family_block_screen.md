# 3244: Route A family block screen

Status
------

Diagnostic only. No Lean certificate, full-line tail, producer_go, SourceRH,
or RH claim follows from this record.

Method
------

scripts/routea_cell16923_family_screen_3244.py reuses the concrete owner
loader and the 192-bit Arb evaluator from record 3204. It evaluates midpoint
family terms at the known strongest diagnostic cell 17168, then reports
exact-rational upper and lower endpoints and contiguous five-family block
sums.

The output is screening evidence only. It is not imported into Lean and does
not replace the 3243 rectangle membership proofs.

Result
------

At cell 17168, with midpoint

    -434044934623 / 409600000000

the contiguous five-family screen is:

    block 0..4       upper ~=   149622.08035817172
    block 5..9       upper ~=        10.20881324534450
    block 10..14     upper ~=  -779289.26577863990
    block 15..19     upper ~=   516789.78056440240
    block 20..24     upper ~=    -5868.87257843345
    block 25..29     upper ~=      -65.2595974100080
    total            upper ~= -118801.32821866391

This confirms that 17168, not 16923, is the correct first sign target for
the 3204 Taylor-6 owner diagnostic. The earlier 16923 screen had total upper
approximately +117075.51, so it must not be used as the initial negative-cell
proof target.

Interpretation
--------------

The result supports a signed block proof, but contiguous blocks alone do not
close the Lean sign theorem: three blocks are positive and three are negative.
The next formal unit should be a family-level rectangle endpoint lemma at
17168, followed by a deliberately chosen sign-aware grouping. The grouping
must preserve the same owner and phase coordinates and must be checked against
the rectangle over-approximation, not only midpoint values.

Reproduction
------------

    python scripts/routea_cell16923_family_screen_3244.py

Output
------

    results/3244_routea_family_screen.json

Verification boundary
---------------------

The script passed git diff --check. The attempted direct Lean expansion of
all six five-family rectangle blocks was abandoned because Lean 4.30.0 hit
the simplifier step limit after 10,000,000 heartbeats; the failed files were
removed rather than retained as an unverified interface.
