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
C > 0 health screen (PREREQUISITE; 1931 forces ICgate(g^2) > 0 for
  every healthy detector, so a C < 0 reading certifies the owner
  unhealthy and kills the 1902 opposite-gates certificate before D
  is read — no extension experiment may proceed past a failed screen)
owner cardinality and separation
correction condition and mass
signed determinant or residual margin
same-index tail ratio
margin degradation as Im(rho) grows
instrument certification (n_primes <= 4000 for three live routes;
  above that route Ap is dropped and spread 0.0 means "one route",
  not agreement — 1994 instrument law)
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

Execution status:

```text
2. EXECUTED (records 1994 + 1996): opposite-gates height audit on the
   committed owner class, then the full scale sweep. gamma_5 hole
   rescued (6/15 cells); gamma_7/gamma_8 both HOST_CONFIRMED with
   ordinate-dependent single-scale health windows (0.92 / 0.88) at
   every delta, D < 0 on 33/33 cells certified. The 1994 "collapse"
   was a 2-cell sampling artifact; hosts now certified at every
   measured ordinate gamma_1..gamma_8. The C > 0 health screen and
   the sweep-don't-sample rule are binding for any future extension.
3. EXECUTED (record 1995): Route C / Velez stabilization claim FAILS
   the five-question promotion audit. Route C remains audit-only.
1, 4. OPEN. (F2 remains gated by the owner-transport bridge — desk
   record 1997 prices the un-gating path: resolution certificate ->
   owner-window ladder + domination measurement -> F2.)

COVER. MEASURED for the width track (record 2016, KNOT_COMPLEX): over the
   eight registered heights the health predicate C > 0 is a comb of 4-7
   disjoint scale bands, not a window; D >= 0 on 43 of 190 cells, all at
   gamma_1..gamma_5; the gamma_5 layer control fires, so no cross-height
   width law is licensed. Consequence for this audit: the C > 0 health
   screen stays binding pointwise, but it cannot be spent as the COVER
   currency, and direction A of record 1998 is excluded by measurement.
   Floor half (record 2017, FLOOR_UNIFORM): floor = 0.02, the smallest
   registered delta, at all eight heights; the host scale window is
   delta-stable while the C-comb is not, and n_primes does not move with
   delta. Direction D stays down-graded; the verdict covers delta >= 0.02
   only. One-resolution caveat and the dxi = 0.002 re-read are registered
   in record 2016 section 5; the COVER currency question is mapped in
   docs/map/107_cover_layer_measured_state.md.
```

Authoritative route records remain `docs/map/104_*.md`, `docs/map/106_*.md`,
and `docs/map/README.md`. Executed-audit records:
`docs/proofs/1994_opposite_gates_height_audit.md`,
`docs/proofs/1995_route_c_velez_stabilization_audit.md`,
`docs/proofs/2016_cover_window_law_outcome.md`,
`docs/proofs/2017_cover_delta_floor_outcome.md`.