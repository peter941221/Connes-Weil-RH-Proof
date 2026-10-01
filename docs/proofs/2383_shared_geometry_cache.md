# 2383 — shared directed geometry cache

Date: 2026-10-02.

The four channel evaluators now share the per-family outward binary64
geometry bounds produced by the first channel.  The cache stores only RNDD /
RNDU-converted enclosure endpoints; channel-specific MPFR arithmetic remains
unchanged.  On the 1001-node exact-audit control, all dominance controls pass.

At 5001 nodes and 16 workers, runtime falls from the 2382 baseline of 38.24 s
to 32.74 s (about 14.4% faster).  The directed values widen slightly, as
expected from reusing outward binary64 endpoints, and are not treated as a
tighter numerical claim.  The 776611-node certificate remains open.
