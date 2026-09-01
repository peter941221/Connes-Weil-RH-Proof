# 1082 - consumer #3 archimedean-rescue algebra: the odd kill, the exact quadratic decomposition, the rescue gate

Date: 2026-09-01. Follows 1081 (consumer #3 structural exit).  Advances
consumer 3 kernel (a): the scalar gate `0 < archimedeanTerm g.convolutionSquare`
on a pinned root-supported triple-vanishing detector.

## 1. What landed (`ConnesWeilRH/Dev/C1HealthyDetectorArchRescue.lean`)

1. `sumTest` / `laplaceAt_sumTest` - pointwise sums of compact-log tests with
   the Laplace additivity readback.
2. `archimedeanTerm_convolutionSquare_sumTest` - THE EXACT QUADRATIC
   DECOMPOSITION: for all tests `f g`,
   `arch (sumTest f g).convSq = arch f.convSq + arch g.convSq + arch (cross f g)`,
   where `crossTest f g = f^.conv g + g^.conv f` is the polarized cross.
   Every archimedean integrand involved is integrable
   (`integrableOn_archimedeanIntegrand_convolutionSquare` /
   `integrableOn_archimedeanIntegrand_crossTest`): the integrand is linear in
   the test, so the cross integrand is transported from the three squares by
   `IntegrableOn.sub`/`.add` through the existing selected-owner bridge.
3. `archimedeanTerm_eq_zero_of_test_odd` - THE ODD KILL: the archimedean term
   of ANY odd test vanishes identically (oddness forces `F 0 = 0`, which
   zeroes the constant term, and zeroes the numerator `e^{y/2}(F y + F(-y))`
   pointwise - no integrability input needed).
4. `test_neg_crossTest_of_even_odd` + `laplaceAt_eq_zero_of_test_odd` - the
   cross of an even test and an odd test is odd, and an odd test is Mellin-
   blind at the origin (`laplaceAt h 0 = 0`, via `lap h(s) = -lap h(-s)`).
5. `archimedeanTerm_convolutionSquare_sumTest_of_even_odd` - HEADLINE: on the
   even/odd class `arch (f+h)^*(f+h) = arch f^*f + arch h^*h` EXACTLY; the
   cross terms are dead by symmetry.
6. `rootSupportedGate_of_evenBase_oddCorrection` - THE RESCUE GATE: an even
   base, an odd correction, the three nodal SUMS vanishing, detection,
   root support, and strict positivity of the two-term anchor imply the FULL
   root-supported healthy detector gate of record 1081.  A future certificate
   owes exactly two terms: `0 < arch f.convSq + arch g.convSq`.

## 2. Structural verdict (honest)

The symmetry route RELOCATES the open kernel; it does not close it:

- the cross terms are dead (exact theorem, zero analysis);
- but the mass-zero node `{0}` of the triple vanishing set CANNOT be served
  by the odd correction (odd Mellin blindness is proved), so the even base
  must be sign-changing - and for a sign-changing base the positivity of
  `arch f^*f` is uncontrolled.

Consumer 3 kernel (a) therefore remains exactly as open as before, now in the
cleaner form: *positivity of the two-term anchor `arch f^*f + arch h^*h` on
the even/odd class with three nodal-sum constraints*.  What 1082 adds is the
certificate STRUCTURE (which terms a future explicit-family certificate must
supply) and the exact algebra it plugs into.  Discharging it still needs the
explicit-family formalization (the 1077-1079 program, measured
`fl2 = -1.294`, sink 33.78%).  The prefix-side wall (kernel (b)) is
untouched.  RH is NOT claimed.

## 3. Build evidence

WSL ext4 mirror through the resource runner
(`build-logs/arch_rescue6.log`):

    Build completed successfully (3649 jobs).
    zero `^error:` lines; zero `sorryAx`.

Focused axiom audit (`C1HealthyDetectorArchRescueAudit.lean`,
`build-logs/arch_rescue_audit.log`, 3650 jobs) - all five headline statements
depend on exactly the three standard axioms
`[propext, Classical.choice, Quot.sound]`:

    archimedeanTerm_convolutionSquare_sumTest             OK
    archimedeanTerm_eq_zero_of_test_odd                   OK
    archimedeanTerm_convolutionSquare_sumTest_of_even_odd OK
    laplaceAt_eq_zero_of_test_odd                         OK
    rootSupportedGate_of_evenBase_oddCorrection           OK

## 4. What is NOT here

No explicit even/odd detector pair is constructed; `arch > 0` is not proven
for any specific test; the prefix-side interpolation wall is untouched; the
capstone premises are unchanged.  The kernel list of consumer 3 is unchanged
in count - (a) the scalar gate, now with a named certificate shape, and (b)
the prefix wall.
