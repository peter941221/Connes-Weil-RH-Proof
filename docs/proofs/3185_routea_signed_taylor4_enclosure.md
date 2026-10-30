3185 Route-A Signed Taylor-4 Enclosure
======================================

Status
------

SIGNED_TAYLOR4_INTERVAL_STYLE_ENCLOSURE

Record 3185 replaces the composite-trapezoid remainder with the symmetric
midpoint Taylor formula:

    integral <= h*f(mid) + h^3*f_second(mid)/24
                  + h^5*sup_abs_fourth/1920

Odd Taylor terms cancel over the symmetric cell. The coefficient and fourth
derivative terms remain conservatively enclosed. This is an external numerical
artifact, not a Lean certificate.

Reproduction
------------

    python scripts/routea_signed_taylor4_enclosure_3185.py

Output:

    results/3185_signed_taylor4_enclosure.json

Observed result
---------------

At 2560 cells and 192-bit precision, the fourth-order remainder upper is about
214.7617448969 and the total upper is about 214.7617448934. The bound is
therefore still positive, although it is substantially smaller than the 3184
second-order remainder. The remaining loss comes from the familywise absolute
fourth-derivative envelope.