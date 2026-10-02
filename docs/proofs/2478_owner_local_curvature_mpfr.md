# 2478 - project-MPFR local curvature smoke

Date: 2026-10-03.

The 2477 edge-split/subcell algorithm was ported to the repository's existing
256-bit `libmpfr.so.6` RNDD/RNDU wrapper used by records 2286 and 2445.  It
keeps the actual 2460 owner family data, the 2475 order-0/1/2 ladder, and
subcell `h³` accumulation.

This is a backend smoke rather than a Lean certificate: coefficient norms are
temporarily outward-rounded from binary floating conversion, and no exact
rational binding/pin has been emitted.  The next promotion step is to replace
that one binding with exact owner-rational operands and add an independent
containment/mutation pin before feeding the array to 2475.
