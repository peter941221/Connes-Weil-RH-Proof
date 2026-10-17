# 2759 - D4/D7 partition budget consumer

Status: Lean-verified partition-level budget.

`representativeD4D7Partition_budget2759` combines the exact left/right integral assembly with the representative-cell interval envelope. It bounds the sum of the two child-cell D4 integrals by the representative D4 box budget, and likewise for D7.

Verification: Linux-native audit build 3669/3669, zero errors; standard axiom trio only.

This is a partition budget consumer, not child-cell outward replay or a numerical D4/D7 pin. Producer GO, SourceRH and RH remain open.
