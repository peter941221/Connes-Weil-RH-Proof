3190 Route-A Correction Owner Tail Match
=========================================

Status
------

NUMERIC_CORRECTION_OWNER_TAIL_MATCHED_LEAN_OPEN

Record 3190 uses the correction contour row from 2353, rather than the base
row used by the conservative 3189 comparison. It checks that the 2353 input
hashes match the current 2338 repair and 2275 capture, and that the correction
row has the same 30-family geometry.

Reproduction
------------

    python scripts/routea_correction_owner_tail_match_3190.py

Output:

    results/3190_correction_owner_tail_match.json

This closes only a numerical data-identity audit. It does not create the Lean
full-line signed-kernel theorem or claim SourceRH/RH.

Observed result
---------------

The repair and capture hashes match the 2353 inputs, the coefficient and family
counts are both 30, and the correction contour row has an upper bound of about
1.1725259700e-16. Adding it to the 3187 finite-window upper gives about
-3.5110507150e-9. The data-level correction-owner identity therefore passes;
the Lean signed full-line theorem and producer import remain open.