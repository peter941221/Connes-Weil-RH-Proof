# Record 3308: corrected signed real upper block probe

Result: the corrected row semantics produce a negative total, but the old 3302
per-block manifest is too tight and must be regenerated.

The 3306 theorem gives the upper shape

```text
real(actual derivative)
    <= real(center aggregate jet)
       + sum(error_i * norm(unit jet_i))
```

For the exact record-2680 owner, the coefficient errors are zero. Record 3308
therefore evaluates the signed real center jet directly, while keeping the
3220 uniform sixth-order norm row and the directed 3300 endpoint rows.

```text
corrected block upper sum: approximately -1.312998292365491e-8
positive gaps vs 3302:     110 / 160
minimum gap:               approximately -1.9848053883271953e-2
maximum gap:               approximately 1.8123023029099215e-2
```

The negative total is the key result. The 110 positive per-block gaps do not
prove failure of the signed route; they show that the 3302 constants were
generated for a different derivative-row object. The next artifact should be a
new outward-rounded 160-block manifest generated from the corrected 3306 row
semantics, followed by its Lean arithmetic mirror and a new block consumer.

The diagnostic script is
`scripts/routea_signed_real_upper_block_probe_3308.py`; the result is
`results/3308_signed_real_upper_block_probe.json`. This is external Arb
evidence only and is not imported into Lean.
