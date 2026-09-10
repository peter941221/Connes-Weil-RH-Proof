# G8 physical cutoff trace-product is self-adjoint

Date: 2026-09-10

The finite-cutoff trace-product carrier from record 1261 is itself
self-adjoint.  The proof rewrites it as `C† K_phys C`, uses positivity of the
physical endpoint Gram to obtain its self-adjointness, and closes the same
owner without any trace cyclicity assumption.

Formal declaration: `g8PhysicalEndpointSourceCutoffPairData_traceProduct_isSelfAdjoint`
in `ConnesWeilRH.Dev.C1G8AdjointShearGram`.

Evidence: `1262_physical_cutoff_selfadjoint_main.log` and
`1262_physical_cutoff_selfadjoint_audit.log`; both builds completed
successfully, with zero `error:` and zero `sorryAx` lines.  The focused audit
reports exactly `[propext, Classical.choice, Quot.sound]`.

This makes the finite-cutoff trace a real scalar after the standard adjoint
trace argument.  It does not provide the cutoff limit, finite-visible-prime
identity, `qw` sign, or RH conclusion.
