# 2473 - refinement scan for the actual-owner panel attachment

Date: 2026-10-02.

The 2472 diagnostic was repeated at 10, 20, 40, 80, and 160 equal cells.
The node composite decreases from about `8.28e3` to `2.75e2`, so the local
panel construction is responsive to refinement.  With the current global
owner derivative package (`B0 ≈ 69.19`, `B1 ≈ 4.115e3`, `B2 ≈ 2.620e5`),
the curvature contribution decreases from about `1.323e7` at 10 cells to
`5.168e4` at 160 cells.

Decision: the next bottleneck is the global second-derivative envelope, not
the node rectangle.  Do not spend the next round on a 10-cell directed node
literal; either price a finer grid or replace the global curvature budget by
a panel/local derivative enclosure.  All readings are diagnostic
high-precision evaluations, not directed bounds or Lean certificates.
