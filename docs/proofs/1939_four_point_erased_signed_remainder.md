# Record 1939: exact erased signed physical remainder

## Result

For every actual `OrbitG8Geometry`, the finite prime sum is formally split as

```text
finitePrimeSum
  = finitePrimeTerm 2
    + sum over (actual owner range).erase 2 of
        vonMangoldt(k) / sqrt(k) *
          2 * (positivePhysicalIntegral(k) - negativePhysicalIntegral(k)).
```

The theorem is
`finitePrimeSum_eq_two_term_add_erased_signed_physical_remainder` in
`C1FourPointPrimePrefixReduction.lean`. The range is the actual owner range;
no ambient visible-prime set or replacement detector is introduced.

## Why this is a real reduction

Record 1938 supplied an absolute support-overlap majorant for the erased
remainder and then subtracted the majorant's own n=2 contribution. That bound
is useful as a guard, but map 093 already gives a scoped no-go for closing the
current route by scalar absolute majorants. The new theorem preserves the
exact positive-minus-negative cancellation of every erased physical node.

Thus the live obligation is now a signed owner-specific budget: prove that
the negative physical mass of the erased range, together with the n=2 sample,
beats the Archimedean term and the erased positive mass. No claim of a gate
sign is made here.

## Verification

Focused WSL build `20260924_signed_remainder4.log` completed successfully
with 3801 jobs and zero errors. The paired audit prints only
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` occurs.

Evidence level: FORMAL exact decomposition; the strict signed inequality
remains OPEN.
