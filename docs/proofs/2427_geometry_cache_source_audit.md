# 2427 — geometry-cache source regression audit

Date: 2026-10-02.

The evaluator source audit confirms that the public hull margin and the
geometry-cache margin are separately named, that both outward binary64
directions are present, and that all five cached lower/upper geometry pairs
use the directional helpers.  This guards the 2421 repair against accidental
removal or conflation of the cache margin.

It is source regression evidence only; it does not prove the mathematical
pointwise enclosure or Lean numeric import.
