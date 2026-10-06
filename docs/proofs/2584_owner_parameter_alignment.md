# Record 2584: 2338-to-Lean owner parameter alignment

Date: 2026-10-05

Status: OWNER-WIDTH-ALIGNMENT-PASS.

This validator checks the exact binary64 family widths captured by record 2338
against the 30 rational entries in Lean's `storedWidth`. Every width matches
at the exact binary64 rational value. Both sides use the squared width as the
analytic bump radius.

This removes one possible owner mismatch before importing the analytic
residual. It does not instantiate the Lean `modulations`, `nodes`, or
`target` arguments, and therefore does not prove coefficient membership.

## Boundary

The next certificate must still bind those three parameter vectors to the same
2338 capture and provide the directed componentwise residual required by the
2583 bridge.

## Evidence

- `scripts/validate_owner_parameter_alignment_2584.py`
- `results/2584_owner_parameter_alignment.json`
- `results/2275_gap_owner_audit.json`
- `ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean`
