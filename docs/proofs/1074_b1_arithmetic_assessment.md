# 1074 - ASSESSMENT: GATE 1 alpha B1, the (983)-bound arithmetic brick

Date: 2026-08-31. Assessment item from the 1070/1071 session plan (GATE 1
alpha: attempt only if budget remains).  This is a FEASIBILITY record, not
a run record: no probe, no fork.  RH is not claimed anywhere.

## 0. The target and the brick

Target contract (committed, axiom-clean):
`CC20EndpointSpectralData.eigenvalue_sq_lt_one : forall n, eigenvalue n ^ 2 < 1`
(ConnesWeilRH/Source/CC20Concrete/EndpointKernelFormula.lean:43, a field of
the input structure).  Any concrete instantiation of the structure must
prove it.

B1 = the pure-arithmetic spine of that proof for n >= 2, from the paper's
own rapid-decay inequality (tex:983, citing Rokhlin Thm 14 + appendix-cv):

```text
  |lambda(n)| <= b(n) := 2^(2n) pi^(2n+1/2) ((2n)!)^2
                         / ((4n)! Gamma(2n + 3/2))
```

## 1. The arithmetic facts (hand-verified this session)

```text
  Gamma(11/2) = (945/32) sqrt(pi)            (half-integer chain)
  b(2) = 2^4 pi^(9/2) (4!)^2 / (8! Gamma(11/2)) = 768 pi^4 / 99225
       = 0.7546... < 1.
  Rational certificate: pi < 22/7  =>  b(2) < 768 (22/7)^4 / 99225
       = 179908608 / 238247225 < 1.          (exact rationals)
  b(0) = 2, b(1) = 3.509...  => (983) is VACUOUS for n = 0, 1.
  b(n+1)/b(n) = 4 pi^2 (2n+2)^2 (2n+1)^2 /
       [(4n+1)(4n+2)(4n+3)(4n+4)(2n+3/2)(2n+5/2)],
       measured: 0.0836 at n = 2, decreasing in n;
       pi^2 < 10 (from 22/7: 484/49 < 10) gives ratio < 1 with margin
       for all n >= 2, hence b(n) <= b(2) * (ratio)^... -> 1 is never
       reached again; lambda(n)^2 < 1 for all n >= 2.
```

## 2. Feasibility verdict

```text
  Verdict: WORTH ONE ATTEMPT (medium-high confidence), scope n >= 2 ONLY.
  Shape: a standalone Dev leaf
    - def bound983 (n : Nat) : Real   (the closed form, pi^2 factored)
    - theorem bound982_two_lt_one : bound983 2 < 1
        (pi_lt_twenty_two_sevenths + ring/linarith over rationals;
         the 768 pi^4 / 99225 factorization needs the Gamma(11/2) chain)
    - theorem bound983_ratio_lt_one : forall n, 2 <= n ->
        bound983 (n+1) < bound983 n * 4 * 10 * ...   (or simply < bound983 n)
        (Nat.factorial telescoping + pi^2 < 10 + linarith)
  Mathlib deps: Real.pi_lt_twenty_two_sevenths (exists), Gamma shift
  (Real.Gamma/Gamma_succ form - exact name to verify at attempt time),
  Nat.factorial casts.  Risk: Gamma half-integer API naming; factorial
  cast friction; 1 sitting, ~100-150 lines.
```

## 3. What B1 does NOT give (honesty ledger)

- The transfer hypothesis |lambda(n)| <= b(n) is ANALYTIC (Rokhlin Thm 14
  + the paper's appendix); producing it in Lean is a separate, much larger
  obligation.  B1 is the reusable brick behind that contract line.
- n = 0 and n = 1 are NOT covered by (983) (b(0) = 2 > 1, b(1) > 1).
  Their strict inequality needs the analytic strict-contraction argument
  (mu = 1 would force a compactly supported Fourier eigenfunction on
  [-1, 1], impossible unless 0).  Also out of B1's scope.
- Hence B1 alone does NOT instantiate CC20EndpointSpectralData; it
  discharges the n >= 2 arithmetic core once the transfer contract is
  stated as a hypothesis.
