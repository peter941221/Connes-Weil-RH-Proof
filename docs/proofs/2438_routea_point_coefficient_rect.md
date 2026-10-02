# 2438 — Route A exact coefficient rectangle

Date: 2026-10-02.

The interval algebra now provides an exact point rectangle for every Lean
complex coefficient.  Its containment is proved by reflexive order, so the
coefficient factor introduces no interval uncertainty once the stored value
identity is established.

This does not yet import the stored binary64 coefficient table.  It separates
that provenance/readback obligation from the bump/amplitude and phase endpoint
certificates.
