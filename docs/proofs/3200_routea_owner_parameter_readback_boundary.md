# Record 3200: Route A owner parameter readback boundary

This record checks whether the numerical Taylor-6 family evaluator and the
Lean Route A owner describe the same object. It is a boundary audit, not a
producer certificate.

The analytic family formula matches:

```text
Python: exp(-30/q + sigma*x + i*theta*x), q = 1 - (x/r)^2
Lean:   externalFamilyValue2344 and externalFamilyValue2344_eq_familyTerm
```

The captured family radii match the Lean support radii after squaring the
captured width values. The remaining window difference is:

```text
Python diagnostic window: 65536001 / 10000000 = 6.5536001
Lean owner support:       storedWidth 4 ^ 2 ~= 6.553600000000003
```

The JSONL cells therefore cannot be treated as a direct Lean owner-window
certificate. A future bridge must prove the extra outer interval is zero by
support, or regenerate the grid over the exact owner window.

Concrete owner data does exist in later Lean records, but the 2338 ideal coefficient boxes do not contain the binary64 owner values. Record 3203 audits this distinction; the binding gap is coefficient-box compatibility, not absence of all owner definitions.

Evidence: `scripts/audit_routea_owner_parameter_readback_3200.py`,
`results/3200_routea_owner_parameter_readback_audit.json`,
`ConnesWeilRH/Dev/C1RouteAExternalOwnerIdentity.lean`,
`ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean`, and
`scripts/routea_owner_whole_cell_2535.py`.

The audit intentionally reports no producer certificate, no `SourceRH`, and no
Riemann Hypothesis result.
