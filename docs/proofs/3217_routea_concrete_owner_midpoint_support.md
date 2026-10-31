3217 Route-A Concrete-Owner Midpoint Support Isolation
======================================================

Status
------

PASS_LEAN_SUPPORT_ISOLATION_FAMILY4_SIGNED_OBLIGATION_OPEN

Purpose
-------

The external 3216 rectangle has one nonzero family after outward rounding.
This record turns that observation into a Lean theorem about the actual
diagnostic midpoint, without importing the external rectangle as a theorem.

The theorem proves that every family index other than 4 is outside its
support at `record2680Center3212 0`. Therefore the full physical sum equals
the family-4 term at that coordinate.

Remaining obligation
--------------------

The theorem does not prove the sign of family 4. The next local target is the
single inequality

    Re (externalFamilyValue2344 ... 4 ... (record2680Center3212 0)) <= 0

with a Lean interval or Taylor certificate for the bump and phase at this
exact coordinate. This is narrower than the former 30-family rectangle
obligation and preserves the owner and coordinate identities.

The file also proves the exact real-part expansion

    Re(c * bump * exp(i * theta * x))
      = c.re * bump * cos(theta * x)
        - c.im * bump * sin(theta * x)

so the next certificate can use ordinary real interval arithmetic rather than
reasoning through an opaque complex rectangle.

Phase boundary
--------------

The first direct attempt to apply the existing 26th-order small-angle pins
`cosPin2676` and `sinPin2676` was rejected by Lean: the exact family-4 phase
at this midpoint has absolute value about `257`, so it does not satisfy the
required `|angle| <= 1` premise. The next valid route must split or scale the
complex exponential before applying the small-angle pin, then compose the
resulting interval through the required number of powers.

Verification
------------

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- Lean: `4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerMidpointSupport3217`
- axiom audit: `[propext, Classical.choice, Quot.sound]`
- build log: `build-logs/3217_build.log`
- audit log: `build-logs/3217_audit.log`

Source
------

- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerMidpointSupport3217.lean`
- `ConnesWeilRH/Dev/C1RouteAConcreteOwnerMidpointSupport3217Audit.lean`
