# 1084 - consumer #3 kernel (a): the anchor collapses to one test

Date: 2026-09-01.  Follows 1083 (explicit even/odd pair).  Advances
consumer 3 kernel (a): the scalar gate on the constructed pair.

## 1. What landed (`ConnesWeilRH/Dev/C1HealthyDetectorAnchorReduction.lean`)

1. SCALING (`archimedeanTerm_convolutionSquare_eq_four_mul`): if
   `F.test = 2 * h.test` pointwise then
   `arch F.convSq = 4 * arch h.convSq`.  The convolution square scales by
   four (`star 2 * 2 = 4`, integral congruence + `integral_const_mul`), the
   numerator/integrand scale by four (the archimedean term is a
   constant-times-`F 0` plus an integral, so the whole reduction is pure
   congruence with NO integrability input).
2. `anchor_eq_four_mul_of_even_odd_sum` - THE ANCHOR COLLAPSE: for an even
   `f`, an odd `g`, and `f + g = 2h` pointwise,
   `arch f.convSq + arch g.convSq = 4 * arch h.convSq` EXACTLY.  Proof: the
   1082 headline kills the cross term on the even/odd class, and scaling
   handles the sum.
3. `arch_pair_eq_four_mul (h)` - specialization to the record-1083 pair
   `(evenPart h, oddPart h)`: the pair's certificate obligation
   `0 < arch f.convSq + arch g.convSq` is EQUIVALENT to
   `0 < arch h.convSq`.
4. `rootGate_of_tripleVanishing_detecting_rootWindow` - KERNEL (a) FINAL
   FORM: ONE root-window test `h` with the triple vanishings
   `{0, 1/2, 1}`, detection at `rho`, and `0 < arch h.convSq` satisfies the
   FULL root-supported healthy detector gate.  The even/odd pair is a
   decomposition device - all its bookkeeping (nodal sums, detection,
   support, anchor) is derived from `h` alone.
5. `exists_kernelA_final` - for every off-line source zero there EXISTS
   such a test (the 7-node symmetric interpolant of record 1083, whose
   values at the criterion nodes follow from the now-public target-value
   lemmas of `C1HealthyDetectorEvenOddPair`).

Also landed: seven previously-private lemmas of
`C1HealthyDetectorEvenOddPair` made public (the `Ne` facts and the target
values at the five criterion nodes) - statements unchanged, additive API.

## 2. Structural verdict (honest)

Consumer 3 kernel (a) is now in its SHARPEST possible shape:

    find ONE compact-log test h with
      support h in the root window, lap h = 0 on {0, 1/2, 1},
      lap h rho != 0,  and  0 < arch h.convSq;

then `rootSupportedHealthyDetectorGate rho` follows.  This is exactly the
pinned-detector scalar gate of record 1080 - the architecture has come
full circle: 1080 named the scalar gate, 1082 gave it an exact algebra,
1083 discharged the gate's hypothesis debts on a constructed pair, and 1084
collapses the pair back onto the single detector itself.  The open
inequality is unchanged in content (`arch h.convSq > 0` is the
1077-1079-measured object, fl2 = -1.294, sink 33.78%); what changed is that
no bookkeeping surrounds it.  Kernel (b), the prefix-side wall, is
untouched.  RH is NOT claimed.

## 3. Build evidence

WSL ext4 mirror through the resource runner
(`build-logs/anchor_reduction1.log`):

    Build completed successfully (3652 jobs).
    zero `^error:` lines; zero `sorryAx`.

Focused axiom audit (`C1HealthyDetectorAnchorReductionAudit.lean`, same
log) - all six pinned statements depend on exactly the three standard
axioms `[propext, Classical.choice, Quot.sound]`:

    archimedeanTerm_convolutionSquare_eq_four_mul   OK
    anchor_eq_four_mul_of_even_odd_sum              OK
    arch_pair_eq_four_mul                           OK
    laplaceAt_sumTest_evenOdd                       OK
    rootGate_of_tripleVanishing_detecting_rootWindow OK
    exists_kernelA_final                            OK

## 4. What is NOT here

No proof of `0 < arch h.convSq` for any specific test; no explicit
Gaussian-family object (the 1077-1079 program remains the numeric
blueprint); the prefix-side interpolation wall (kernel (b)) is untouched;
capstone premises unchanged.
