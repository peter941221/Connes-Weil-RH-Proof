# 1083 - consumer #3 kernel (a): the explicit even/odd pair exists

Date: 2026-09-01.  Follows 1082 (arch-rescue algebra).  Advances consumer 3
kernel (a): the scalar gate `0 < archimedeanTerm g.convolutionSquare`.

## 1. What landed (`ConnesWeilRH/Dev/C1HealthyDetectorEvenOddPair.lean`)

1. `negTest` / `laplaceAt_negTest` - pointwise negation of a compact-log
   test with the Laplace readback `lap (negTest f) s = -lap f s`.
2. `laplaceAt_reflection` - KEY IDENTITY: reflection in the log coordinate
   WITHOUT conjugation trades the Laplace parameter for its negative,
   `lap f.reflection s = lap f (-s)`, by pure substitution
   (`w_{-s}(-x) = e^{sx} f(-x) = w_s` composed with the reflection) - no
   symmetry hypothesis on the test is needed.
3. `evenPart h = h + h.reflection`, `oddPart h = h - h.reflection` - EVEN
   and ODD unconditionally, with Laplace values `y(s) + y(-s)` and
   `y(s) - y(-s)` for `y = lap h`.
4. The 7-node symmetric interpolation: on
   `{rho, -rho, 0, +-1/2, +-1}` the residual-window correction tool
   (`exists_residualWindow_correction`, window taken DIRECTLY at
   `(-log 2 / 2, log 2 / 2)` - the tool only requires `lower < 0 < upper`)
   realizes `1` at `rho`, `-1` at `-rho`, `0` on the five criterion nodes.
   All distinctness facts come from the off-line hypothesis: `0 < rho.re`,
   `rho.re < 1` (so `rho` misses `0, 1/2, 1, -1/2, -1`) and `rho != 0`
   (so `-rho` misses every node and `rho` itself).
5. `exists_evenOddPair_of_offLineZero` - HEADLINE: for every off-line source
   zero there is a CONSTRUCTED pair `(f, g) = (evenPart h, oddPart h)` with
   - `f` even, `g` odd (unconditional);
   - `lap f 0 = 0` (each y-value pairs with its mirrored y-value);
   - the half and one nodal SUMS vanish exactly (`0 + 0`);
   - detection value `2 = (1 + (-1)) + (1 - (-1)) != 0` at `rho`;
   - combined support in the CLOSED root window
     `[-log 2 / 2, log 2 / 2]` (symmetric window + reflection support
     transport);
   - the FULL record-1082 rescue gate
     `rootSupportedHealthyDetectorGate rho` follows from the two-term anchor
     positivity `0 < arch f.convSq + arch g.convSq` ALONE.

## 2. Structural verdict (honest)

Record 1082 left the rescue gate's hypothesis debts OPEN: the three nodal
sums, the detection, and the root support were HYPOTHESES.  They are now
THEOREMS on an explicit pair - the certificate a future proof owes for
kernel (a) is EXACTLY ONE INEQUALITY on a named object:

    0 < archimedeanTerm (evenPart h).convolutionSquare
                      + archimedeanTerm (oddPart h).convolutionSquare

with `h` the 7-node interpolant.  This is precisely the object the
1077-1079 numeric program measures (`fl2 = -1.294`, sink 33.78% of lever at
the fired config).  The anchor positivity itself is NOT proven here - it
stays the single open inequality of kernel (a), now with zero bookkeeping
around it.  Kernel (b), the prefix-side wall (uniform-in-radius
interpolation constants vs the `(3/4)^n0` shell budget), is untouched.
RH is NOT claimed.

## 3. Build evidence

WSL ext4 mirror through the resource runner
(`build-logs/even_odd_pair1.log`):

    Build completed successfully (3651 jobs).
    zero `^error:` lines; zero `sorryAx`.

Focused axiom audit (`C1HealthyDetectorEvenOddPairAudit.lean`, same log) -
all six pinned statements depend on exactly the three standard axioms
`[propext, Classical.choice, Quot.sound]`:

    laplaceAt_reflection                 OK
    laplaceAt_negTest                    OK
    test_even_evenPart                   OK
    test_neg_oddPart                     OK
    support_oddPart_subset_Icc           OK
    exists_evenOddPair_of_offLineZero    OK

## 4. What is NOT here

No proof of `0 < arch f.convSq + arch g.convSq` for any test; no explicit
Gaussian-family formalization (the 1077-1079 `g_3` object is not landed);
the prefix-side interpolation wall (kernel (b)) is untouched; capstone
premises are unchanged.  Consumer 3's kernel list is unchanged in count -
(a) the scalar gate, now carried by a CONSTRUCTED pair, and (b) the prefix
wall.
