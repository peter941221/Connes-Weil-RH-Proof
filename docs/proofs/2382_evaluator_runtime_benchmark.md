# 2382 — evaluator runtime benchmark

Date: 2026-10-02.

The same-expression directed path was measured at 5001 nodes with 16 worker
processes and 20001-node span size.  The run completed in 38.24 seconds and
preserved the directed controls.  The machine exposes 16 WSL CPUs with ample
free memory, so the current obstacle is per-node evaluator work rather than
memory pressure or the removed `Fraction` audit.

This is a performance benchmark only; it does not alter the producer status
or establish the 776611-node numerical certificate.
