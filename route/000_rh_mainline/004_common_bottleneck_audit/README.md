# 004 - A/B common bottleneck audit

Purpose: compare Routes A and B before spending more Lean or numerical effort.
This record is a decision aid, not a new producer theorem.

```text
B5 CompactLog same-owner semi-local positivity
                         |
             +-----------+-----------+
             |                       |
       Route A                  Route B
   signed residual          determinant + tail
             |                       |
             +-----------+-----------+
                         |
             v
              qw(g) >= 0 for same owner
```

+----------------------------+----------------------------+----------------------------+
| Layer                      | Route A                    | Route B                    |
+----------------------------+----------------------------+----------------------------+
| Same owner                 | Formal readback; final     | Formal owner wiring;       |
|                            | signed margin OPEN         | actual determinant OPEN   |
+----------------------------+----------------------------+----------------------------+
| Main analytic sign        | aggregate residual <= -e   | det_n < 0                  |
+----------------------------+----------------------------+----------------------------+
| Tail / decay               | derivative-cost margin    | same-index tail ratio     |
|                            | and parameter closure OPEN | OPEN                      |
+----------------------------+----------------------------+----------------------------+
| Quantifiers                | rho and selector class    | rho, n, lambda, owner     |
|                            | closure OPEN              | closure OPEN              |
+----------------------------+----------------------------+----------------------------+
| Known scoped obstruction   | current selector final-   | under-approximation and   |
|                            | sign no-go                | unproved q / full owner   |
+----------------------------+----------------------------+----------------------------+

The fastest shared decision variables are:

```text
owner cardinality and separation
correction condition and mass
signed determinant or residual margin
same-index tail ratio
margin degradation as Im(rho) grows
```

Decision rule:

- Do not promote A or B from a candidate based on interfaces alone.
- Prefer the route with a certified margin on the actual owner, not the route
  with more completed Lean wrappers.
- If both margins collapse on the same owner family, audit Route C's full
  positivity bridge before inventing another finite selector.

Current recommendation:

```text
1. Run Route B survival screen through actual-owner determinant and tail.
2. Run Route A's final-sign selector audit on the same owner class.
3. In parallel, line-audit Route C's claimed full positivity bridge.
4. Promote Route C only if it removes the same-owner sign obligation directly.
```

Authoritative route records remain `docs/map/104_*.md`, `docs/map/106_*.md`,
and `docs/map/README.md`.