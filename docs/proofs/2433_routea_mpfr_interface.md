# 2433 — Route A directed endpoint interface

Date: 2026-10-02.

The new Lean interface packages an exact real or complex value together with
an axis-aligned directed enclosure.  Product, sum, and difference constructors
are proved sound using the interval algebra from records 2430–2431.

This intentionally does not model MPFR, binary64, or unsafe machine
operations.  The remaining numerical obligation is explicit: a future MPFR
certificate must prove the two endpoint inequalities for each primitive
operand and directed operation.  Once supplied, the interface transports
those facts through `iprod`/`ciprod` without another floating-point argument.
