# 2866 Route B D4 hotspot diagnostic

The sharp-e0 replay-owned charge was decomposed by cell using the same
endpoint absolute-max pricing as record 2865. The largest D4 contributions are
at the high-xi edge (cells 8192, 8191, ...), but the concentration is weak:
the ten largest cells contribute only about 1.144% of the D4 total. The first
cell is therefore not the source of the 2.81x excess; a local exception or
discarding a small tail cannot close the gap.

This points to a structural tightening of the D4 enclosure or charge formula:
the current `max(abs(lo), abs(hi))` endpoint norm is being paid across the
whole interval. The next useful proof target is a D4-specific derivative
enclosure that preserves cancellation or uses a certified interior maximum.
No global Lean closure is claimed by this diagnostic.
