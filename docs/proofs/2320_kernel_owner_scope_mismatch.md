# 2320 — Kernel-owner scope mismatch

Scope clarification (2336): the 2308 radius 2*max(width^2) is not the
composed selected-source square support-cover radius. For the captured base
and correction at n=0, support composition gives 4*max(width^2). This record
compares kernel conventions only; neither book is established as the actual
detector complete nonzero prime set.

Record 2320 compares the executable owner inputs of records 2249 and 2308.
The 30 owner families are bitwise equal, with the same family digest
`2c64f0e863e5ec483350667e7f86e4d554f02c2a1349bc0656e26b44f5afcce3`.
However, the support-derived prime books are not equal.

```text
+----------------------+----------------------+----------------------+
| field                | record 2249          | record 2308          |
+----------------------+----------------------+----------------------+
| support formula      | 2 * max(width)       | 2 * max(width^2)     |
| support              | 5.120000000000001    | 13.107200000000006   |
| cutoff               | 167                  | 492475               |
| prime-power count    | 52                   | 41136                |
| last prime power     | 167                  | 492467               |
+----------------------+----------------------+----------------------+
```

The 2249 prime book is therefore a strict prefix of the 2308 book only at the
integer-list level; its weights and the resulting kernel are not the same
functional. The coefficient/family identity does not transfer the 2249 L1
margin to the actual selected-square physical kernel.

The next mathematical obligation is the explicit omitted-book contribution:

```text
K_2308 - K_2249 = 2 * sum over 167 < n <= 492475 of
                  Lambda(n) / sqrt(n) * cos(2*pi*log(n)*xi)
```

This difference must be evaluated on the actual selected owner and enclosed
with the same signed convention as the producer margin. Until that is done,
records 2249 and 2308 retain separate scopes. No producer GO and no RH claim.

Evidence:

- script: `scripts/routea_kernel_owner_scope_audit_2320.py`
- artifact: `results/2320_kernel_owner_scope_audit.json`
- source formulas: `scripts/routea_weighted_zero_l1_enclosure_2249.py` and
  `scripts/routea_hgap_window_cert_2308.py`
- selected-owner support interface:
  `ConnesWeilRH/Dev/C1SameOwnerWeil.lean` and
  `ConnesWeilRH/Dev/C1G8R0OrbitGeometry.lean`
