# Proof 550: actual Julia range-sine Douglas owner

## Result

Proof 550 lowers the remaining weighted range-sine field to an exact
functional-analytic owner. It does not prove the source estimate, Gate 3U,
the finite-S sign, Burnol's identity, or RH.

The source module is:

~~~
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualJuliaRangeSineDouglas.lean
~~~

The focused audit is:

~~~
ConnesWeilRH/Dev/
  CCM24FiniteSActualJuliaRangeSineDouglasAudit.lean
~~~

## Exact reduction

For one visible prime p and suffix S, define the actual canonical defect of
the normalized Schur frame:

~~~
D_(p,S) =
  canonicalJuliaDefect(normalizedSchurFrame_(p,S),
                       normalizedSchurFrame_contract_(p,S)).
~~~

The weighted range-sine estimate is:

~~~
(p - 1) ||rangeSine x||^2 <= ||D_(p,S) x||^2.
~~~

Because p > 1, primeJuliaWeight p = p - 1 is strictly positive. Proof 550
proves the exact equivalence:

~~~
weighted range-sine estimate
  <=>
exists factor F with ||F|| <= 1 and
  F D_(p,S) = sqrt(p - 1) rangeSine.
~~~

The factor is a genuine Douglas factor through the actual canonical defect;
it is not a basis estimate and it is not inferred from graph contractivity.

## Kernel guard

The same estimate necessarily implies:

~~~
D_(p,S) x = 0 -> rangeSine x = 0.
~~~

Therefore a source-specific vector satisfying

~~~
D_(p,S) x = 0
and
rangeSine x != 0
~~~

rules out the weighted estimate for that row. The literal Proof 546 readback
specialization applies this directly to
readout * graphSine(graphCosine).

This is the next concrete test: either construct the physical Douglas factor,
or construct an actual canonical-defect zero mode that the physical readout
does not annihilate. Proof 550 constructs neither witness.

## Verification

Commands were run in the Ubuntu-24.04 WSL2 ext4 mirror:

~~~
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualJuliaRangeSineDouglas
lake env lean ConnesWeilRH/Dev/CCM24FiniteSActualJuliaRangeSineDouglasAudit.lean
lake build ConnesWeilRH.Source.CCM25Concrete
lake build
~~~

+------------------------------------------+--------+--------+
| target                                   | jobs   | result |
+------------------------------------------+--------+--------+
| focused source module                    |        | PASS   |
| focused axiom audit                      |        | PASS   |
| CCM25Concrete aggregate                  | 3820   | PASS   |
| full repository                          | 3901   | PASS   |
+------------------------------------------+--------+--------+

The focused audit reports exactly:

~~~
[propext, Classical.choice, Quot.sound]
~~~

The new source and audit contain no sorry, admit, or user axiom declaration.
Existing repository linter warnings are unchanged. Gate 3U, the finite-S
sign, Burnol's identity, and _root_.RiemannHypothesis remain open.
