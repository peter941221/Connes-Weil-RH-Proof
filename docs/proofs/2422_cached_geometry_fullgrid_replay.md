# 2422 — full-grid replay after cached-geometry repair

Date: 2026-10-02.

The 776611-node, 16-worker replay was regenerated after the geometry-cache
outward repair.  Current source hashes match, and the 39-span readback passes
with lengths `38×20001+16573`.  The directed span-sum readings are retained
as the current evaluator output; the old 2414 artifact is not reused.

The replay remains numerical interface data.  It does not establish the
mathematical pointwise enclosure theorem or Lean numeric import.
