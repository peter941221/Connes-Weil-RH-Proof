# 2478 - project-MPFR local curvature smoke

Date: 2026-10-03.

The 2477 edge-split/subcell algorithm was ported to the repository's existing
256-bit `libmpfr.so.6` RNDD/RNDU wrapper used by records 2286 and 2445.  It
keeps the actual 2460 owner family data, the 2475 order-0/1/2 ladder, and
subcell `h³` accumulation.

The coefficient binding has now been promoted to an exact rational
`abs(Re(mid))+abs(Im(mid))` upper bound, converted through a 220-decimal
outward MPFR interval.  An independent self-test checks containment for all 30
rows.  This is slightly looser than the Euclidean norm but safe and exact at
the rational-input level.

The result is still not a Lean numeric import: the cell enclosure and its
source/mutation pin remain to be formalized before feeding the array to 2475.
