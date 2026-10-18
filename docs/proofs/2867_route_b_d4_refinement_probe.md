# 2867 Route B D4 refinement probe

The same sharp replay-owned D4 charge was recomputed with finer cell meshes:

```text
cells | D4 charge
------+----------
8192  | 4211.4134
16384 | 4131.2360
32768 | 4091.1975
```

Mesh refinement reduces interval dependency, but the sequence is still far
above the 1500 target and appears to converge near 4,000. Therefore simply
increasing the number of cells is not a viable closure mechanism. The next
step must change the D4 bound itself, such as a cancellation-preserving
derivative enclosure or a mathematically justified decomposition.

This is a model pricing probe, not a Lean certificate.
