# Route A records 3304 and 3305: derivative-row no-go and signed consumer

Record 3304 tests whether the directed 3302 block manifest can be consumed
through the existing formal derivative rows from record 3224.

The 3224 object is an absolute-value majorant (a bound formed by summing the
norm of every family contribution).  The 3302 block values are signed
upper bounds produced from the tight real endpoint replay and therefore retain
family cancellation.  These are different mathematical objects.

The diagnostic re-evaluates the 3224 definitions with Arb interval arithmetic,
using the same owner coefficients, stored squared widths, grid, and Taylor-6
cell formula.  It compares each 256-cell block with the directed 3302 block
constant.  All 160 blocks fail the required direction:

```text
formal 3224 block upper  >  directed 3302 manifest block upper
```

The smallest positive gap is approximately `6.385559487775981e-12`; the
largest is approximately `6.1361560960921005e-2`.  Representative values are:

```text
block   manifest upper       formal 3224 upper      formal - manifest
000     2.2251e-27            6.3856e-12            6.3856e-12
046    -3.1676072210e-3     -3.1675317253e-3       7.5496e-8
067     3.1975547439         3.1998543171          2.2996e-3
105    -1.1044237080e-2     -1.1044170502e-2       6.6578e-8
```

The complete diagnostic is stored in
`results/3304_formal_derivative_block_no_go.json`.  It is external evidence
only and is not imported into Lean.

Record 3305 adds a parameterized Lean consumer:
`intervalIntegral_record2680_40960_strict_upper_of_tight_signed_block_manifest3305`.
It keeps the 3298 tight endpoint and 3302 block-sum shape, while taking the
second-, fourth-, and sixth-derivative upper rows as explicit premises.  This
separates the signed block consumer from the 3224 absolute-value derivative
provider.  A future signed derivative-row proof can therefore be connected
without changing the owner identity, grid, endpoint, or block indexing.

The focused WSL2 ext4 Lean 4.30.0 build completed at 3975 jobs.  The
independent audit completed at 3976 jobs and reports exactly
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The finite-window strict-negative theorem is still not instantiated: the
missing premises are now specifically a signed derivative-row provider and the
160 block inequalities for that provider.

Nonclaims:

- no imported Arb or JSON endpoint;
- no finite-window strict negativity theorem;
- no full-line tail, B5 readback, `producer_go`, `SourceRH`, or RH claim.
