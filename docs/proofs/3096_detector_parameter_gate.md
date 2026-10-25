# 3096 - Actual detector costs and the row-B extension gate

Status: FORMAL necessary height and inverse-gap costs. The fixed row-B
instance is not a universal producer. D4/D7 actual integral bounds remain open.

1. The same raw factor in both bounds

Fix `geometry : OrbitG8Geometry rho g`. Let `phi` be
`orbitRawFactor geometry`, the unshifted convolution factor of the selected
test, and let `L = geometry.orbitIndex + 2`. This is the construction's actual
factor, not the fixed repaired coefficient owner. Its support is in `(-L,L)`.
Let `delta = |Re(rho)-1/2|` and assume `delta > 0`.

The new module proves both of the following on this same `phi`:

```text
|Im(rho)| <= exp(L) * derivOrderL1(1,phi)

1 / (L * exp(L) * delta) <= l1Mass(phi)
```

Here `l1Mass(phi)` is the integral of `|phi|`; it measures total magnitude.
The first derivative's L1 mass measures total variation. Neither is a signed
Weil functional. These lower requirements cannot establish the desired sign.

2. Inverse-gap proof

The geometry's actual interpolation pins are `laplaceAt(phi,rho)=1` and
`laplaceAt(phi,1-conj(rho))=-1`. The nodes are separated by `2*delta`.
Differentiation under the compact-support integral, already proved in
`C1XiResidue`, gives the uniform derivative estimate:

```text
support(f) in [-B,B], |Re(s)| <= A
    |
    v
|deriv(laplaceAt f)(s)| <= B * exp(A*B) * l1Mass(f)
    |
    v
|laplaceAt(f,s1) - laplaceAt(f,s2)|
    <= B * exp(A*B) * l1Mass(f) * |s1-s2|
```

The second line uses the mean value inequality on a convex complex strip.
Substituting the opposite target values and `A=1` proves the displayed
inverse-gap bound. This closes the L1 portion of the paper-level claim in
record 3063. It does not formalize that record's separate L1-to-quadratic-strip
comparison.

The theorem `no_raw_factor_mass_cap_below_inverse_gap` rejects any claimed
mass ceiling below the actual required cost. The boundary theorem
`opposite_targets_nodes_ne` prevents assigning 1 and -1 at a single node;
the inverse-gap theorem explicitly retains the off-line hypothesis.

3. Row-B decision

The actual `fourPointContradictionRowBStored2723` still uses norm cap 22,
height cap `421/20`, orbit index 3 and span coefficient 24. Its three strip
bounds refer to the stored `explicitSeed` carrier. The authorized re-seeding
to `poweredSeed`, target and prefix-zero duties, and the selected gate
inequality remain separate obligations.

```text
fixed stored row B
    |
    +--> bounded height and fixed coefficients
    +--> remaining target / zero / gate hypotheses
    |
    v
no deduction covering every hypothetical off-line zero

rho-dependent construction
    |
    +--> must pay its actual height cost
    +--> must pay its inverse-gap cost
    +--> must close gate and spectral tail at the same index
    |
    v
still a candidate; no universal sign theorem is supplied here
```

The two necessary cost bounds do not rule out this candidate. They identify
parameters that cannot be silently kept fixed during a universal extension.
No actual small-gap or high off-line zero is asserted to exist.

4. D4/D7 boundary

`C1RouteBSeedLedgerAllowance3071` and its existing paired audit are now
verified in this round's Linux integration build.
Its full-target arithmetic adds the separately proved endpoint integral and
the finite charge sum under explicit per-cell and ledger hypotheses. It does
not prove those hypotheses.

In particular, record 3070's mpmath observation that 8192 cell comparisons fit
an allowance is not used as a Lean fact. A coarse-grid exploratory interval
evaluation (record 3097) failed its D4 target; this is a failure of that coarse
enclosure,
not a lower bound on the true integral. No D4/D7 numerical integral theorem,
cardinal pin, carrier transfer, positive Weil value, or RH proof is claimed.

5. Verification

Run `python3 scripts/detector_parameter_audit_3096.py` in a Linux checkout
with the pinned Lean toolchain. It builds the new audits, all record-3094
local-screen controls, the existing 3071 arithmetic audit, and the stored row-B
consumer.
It rejects missing declarations, nonzero build exits, error lines, missing
success footers, `sorryAx`, and any reported axiom set other than
`[propext, Classical.choice, Quot.sound]`.

`--self-test` exercises these failure controls. The portable evidence is
`results/3096_detector_parameter_audit.json`; source hashes establish artifact
provenance, while Lean checks the stated mathematics. Text-source hashes
normalize CRLF line endings to LF, so they match the committed source bytes.
