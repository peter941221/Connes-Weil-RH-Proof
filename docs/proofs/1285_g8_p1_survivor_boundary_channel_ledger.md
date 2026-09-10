# G8 P1 survivor--boundary channel ledger (2026-09-10)

The import-facing leaf `ConnesWeilRH.Dev.C1G8P1BoundaryChannelLedger`
proves an exact same-owner operator identity for the linear survivor/boundary
metric channel at every literal cutoff. Writing `B_S` for the ordered
`visiblePrimes` boundary-map list and `u_S` for the real upper Euler factor,

```text
channel(Survivor, u_S • B_S.sum)
  = u_S • (B_S.map (fun B => channel(Survivor, B))).sum.
```

The proof is finite operator algebra (`comp_sum_eq_sum_comp` and scalar
homogeneity). The detector, finite family, source basis, and cutoff are all
unchanged. This supplies the aggregate visible-boundary interface required by
the next finite visible-prime/prime-power comparison; it does not identify an
individual boundary map with a radial prime-power crossing, prove a sign, a
cutoff limit, or any `qw` statement.

Acceptance: `/home/peter/rh/build-logs/1307_g8_p1_boundary_channel_final.log`,
3926 jobs, zero `error:`/`sorryAx`, and the paired audit prints only
`[propext, Classical.choice, Quot.sound]`.
