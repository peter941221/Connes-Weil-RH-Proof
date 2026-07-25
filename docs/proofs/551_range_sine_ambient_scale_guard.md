# Proof 551: range-sine / ambient-loss scale guard

## Result

Proof 551 rejects a tempting but invalid shortcut after Proof 550. The
ambient-loss scalar from Proof 506 is not the scalar normalizer required by
the Proof 550 weighted range-sine Douglas row.

The source module is:

~~~
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard.lean
~~~

The focused audit is:

~~~
ConnesWeilRH/Dev/
  CCM24FiniteSActualJuliaRangeSineAmbientScaleGuardAudit.lean
~~~

## What It Rules Out

Proof 550 uses the range-sine weight:

~~~
primeJuliaWeight p = p - 1
weighted row = sqrt(p - 1) * rangeSine
~~~

Proof 506's ambient antiresonant loss column uses:

~~~
a = p^(-1/2)
ambient scale = sqrt(a) / (1 + a)
~~~

Lean proves:

~~~
ambient scale^2 < primeJuliaWeight p
ambient scale^2 != primeJuliaWeight p
ambient scale != sqrt(primeJuliaWeight p)
~~~

So the ambient-loss factor cannot be silently reused as the missing
range-sine producer. Any future producer must still construct a genuine
factor through the actual canonical Schur defect, or produce the zero-mode
obstruction from Proof 550.

## Verification

Commands were run in the Ubuntu-24.04 WSL2 ext4 mirror:

~~~
lake build ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
lake env lean ConnesWeilRH/Dev/CCM24FiniteSActualJuliaRangeSineAmbientScaleGuardAudit.lean
~~~

+------------------------------------------+--------+--------+
| target                                   | jobs   | result |
+------------------------------------------+--------+--------+
| focused source module                    | 3326   | PASS   |
| focused axiom audit                      |        | PASS   |
+------------------------------------------+--------+--------+

The focused audit reports exactly:

~~~
[propext, Classical.choice, Quot.sound]
~~~

This is a route guard only. It does not prove the weighted range-sine
estimate, construct component rows, close Gate 3U, prove the finite-S sign,
prove Burnol's identity, or prove _root_.RiemannHypothesis.
