# 2838 Route B cell-4096/order-4 Lean bridge

Record 2838 specializes the existing exact Lean interval-jet enclosure to the
first non-underflowing comparison target used by the Python artifact 2837:
Route B cell index 4096 and derivative order 4.

The Lean theorem proves, for every x in that cell, that
`seedTransitionJetInterval2734 (routeBSeedCell2809 4096) 4` contains
`iteratedDeriv 4 Real.smoothTransition x`, and therefore bounds its norm by the
interval endpoint maximum. It also pins the cell endpoints to
`8392704 / 33554432` and `8394751 / 33554432`.

This is a concrete Lean-side enclosure, not a semantic equality with Python
`p3.seed_jet`. The Python artifact still lacks a proof that its reciprocal,
exponential, product, and interval endpoint conventions coincide with the Lean
definitions. No ledger domination, D4/D7 aggregate, SourceRH, or RH claim
follows from this record.

Source: `ConnesWeilRH/Dev/C1RouteBCell4096Order4Bridge2838.lean`.

Linux-native ext4 build: `lake build ConnesWeilRH.Dev.C1RouteBCell4096Order4Bridge2838`,
3657 jobs, completed successfully. The paired audit prints only
`propext`, `Classical.choice`, and `Quot.sound` for all three theorems.
