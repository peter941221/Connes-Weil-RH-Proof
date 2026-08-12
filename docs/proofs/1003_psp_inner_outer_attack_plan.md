# 1003 - Inner/outer factorization of the Gamma-R scattering phase: attack plan

Status: PLAN (not a closure). It splits sub-target C's core into independent,
separately Lean-buildable sub-propositions. RH not claimed. No sorry / axiom.

## Goal recap (docs/1002)

Find a nonzero psi (upper-Hardy, H+) with m * psi (lower-Hardy, H-), where

    m(x) = Gamma_R(1/2 - i 2 pi x) / conj(Gamma_R(1/2 + i 2 pi x)),   |m| = 1.

Then the corresponding u lies in V_arch (radial AND HT-radial) and carries
nonzero window mass.  The typed gate is `vArch_mem_iff_support_ae`.

## Decomposition (each sub-prop is an independent, buildable step when the
previous one holds)

A1  The scattering phase is already a programme def in the repo
    (`ccm24ArchimedeanScatteringPhase`), meromorphic via the Gamma factors.
    Gate: give its meromorphic extension data on the real line.

A2  Inner/outer (Beurling) split: for any |m|=1 analytic-in-a-strip symbol
    that is the boundary value of a Nevanlinna (inner/outer class) function,
    there exist P in H+ and Q in H- with m = Q / P and |P| = |Q| = 1 a.e.

A3  Explicit outer representation:  P = exp( Pi_- (log m) ) and
    Q = exp( Pi_+ (log m) ), where Pi_- / Pi_+ are the lower / upper real
    Wiener spectral projections of the analytic log m; then m = Q/P and
    log|m|=0 forces it to an inner-outer boundary.

A4  L2-placement: the resulting psi = P lies in L2, and m * psi = Q lies in
    L2 (so both are genuine Lp elements on the carrier).

A5  Sufficiency lift: use `vArch_mem_iff_support_ae` to turn the analytic
    pair into a Lean theorem; then prove window mass D; then lift
    `twoOuterNonzeroObligation` to a theorem (E).

## Mathlib / repo gaps (evidence of size)

- Formalization wedge: mathlib v4.30.0 has no H+/H- Hardy subspaces of
  L2(R) and no inner/outer (Paley-Wiener) filter for our scattering phase;
  those have to be built (new math) before the analytic pair can be closed.

## Acceptance criteria per A_k

A_k closes iff:
 1. a typed def and normal theorem (no sorry / axiom), and
 2. a focused WSL `flock lake build <dev target>` green + `#print axioms`
    `[propext, Classical.choice, Quot.sound]`, and
 3. it advances toward A5 gate.