# 1138 - rational-power interval integral engine

Date: 2026-09-05.

Status: PRE-REGISTRATION, committed before implementation.
Consumer: the true central `classMoment 0`/`classMoment 2` producer, hence the
healthy `CompactLog`, B5-shaped Hbox chain. RH is not claimed.

## 1. Purpose

Record 1137 turns the central class weight into a pointwise-controlled power
of a finite Taylor polynomial in `(1 - x^2)⁻¹`. This record supplies the
calculus needed to integrate that rational function exactly on
`[-97/100, 97/100]`.

The primitive family is defined by

```text
J₀(x) = x
J₁(x) = (log(1+x) - log(1-x))/2
Jₖ(x) = x / (2(k-1)(1-x²)^(k-1))
       + (2k-3)/(2(k-1)) Jₖ₋₁(x),   k >= 2.
```

On the open unit interval this has derivative `(1-x²)⁻ᵏ`. Its symmetric
endpoint difference therefore satisfies the exact recurrence

```text
V₀ = 2r
V₁ = log((1+r)/(1-r))
Vₖ = r / ((k-1)(1-r²)^(k-1))
     + (2k-3)/(2(k-1)) Vₖ₋₁,
```

with `r = 97/100`. The order-2 moment uses
`x²(1-x²)⁻ᵏ = (1-x²)⁻ᵏ - (1-x²)⁻(k-1)` for `k >= 1`, and the elementary
`2r³/3` value at `k = 0`.

## 2. Registered declarations

1. A denominator-power integrand and its recursive primitive are defined.
2. The primitive derivative is proved on `|x| < 1`, including the logarithmic
   base case and the recurrence case.
3. The interval integral of every denominator power on the fixed central
   interval is proved equal to its recursive endpoint value.
4. A finite sum of denominator powers receives an exact interval-integral
   formula by finite linearity.
5. The corresponding order-2 moment sum receives the exact difference formula
   above.

## 3. Integrity gates

- No target moment, decimal oracle, stored conclusion, `sorry`, `admit`, or RH
  conclusion is introduced.
- The only non-algebraic symbol in the endpoint value is the explicit
  `Real.log (197/3)`; its rational enclosure is a later record.
- The fixed-radius formulas are used only by the healthy class-moment
  certificate and do not alter the ROOT route or the normalized audit socket.

## 4. Acceptance gates

- G1: owning and paired audit modules build through the canonical WSL runner
  with the success footer and zero `^error:` lines.
- G2: every audited declaration has exactly
  `[propext, Classical.choice, Quot.sound]`, with zero `sorryAx`.
- G3: the derivative and interval formulas are proved from Mathlib calculus,
  finite sums, and explicit nonvanishing of `1-x²` on the interval.
- G4: staged-diff hygiene is clean and the route remains unclaimed.

The post-run addendum will state whether this calculus engine landed. It will
not state that the target moments, true-data Hbox, semi-local positivity, or RH
are complete.

## 5. Post-run addendum (2026-09-05, after builds 1-7)

VERDICT: LANDED.

The preregistration commit `3a322dd` preceded the implementation.  The final
canonical ext4 build completed successfully with 3663 jobs, zero `^error:`
lines, and zero `sorryAx` occurrences.  The paired audit printed five
declarations, each with exactly `[propext, Classical.choice, Quot.sound]`.
The final new-module warning count was zero.

The landed API proves the recursive primitive derivative, the exact fixed-
radius interval value for every denominator power, finite-sum linearity, and
the order-2 identity reducing `x²(1-x²)⁻ᵏ` to adjacent denominator powers.
The high-precision logarithm enclosure, concrete Taylor-power coefficient
certificate, target moment boxes, true-data Hbox, defect contraction,
same-detector semi-local positivity, and RH remain open.
