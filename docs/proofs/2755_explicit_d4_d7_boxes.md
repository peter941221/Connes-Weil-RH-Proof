# 2755 - Explicit representative D4/D7 boxes

Status: Lean-verified owner-level box interface.

`representativeD4Box2755` and `representativeD7Box2755` name the order-4 and order-7 `RealInterval2429` outputs of the rational transition jet on `representativeCell2736`. The three theorems prove each membership and their conjunction for every point in the cell.

The boxes are aliases of the already verified exact-real jet enclosure; this record adds no numerical rounding claim. It is the direct input shape for a later D4/D7 integral or tail consumer.

Verification: Linux-native audit build 3666/3666, zero errors; all three declarations use only `[propext, Classical.choice, Quot.sound]`.

Remaining: outward replay, integral bounds, numerical pins, carrier transfer, universal-rho duties, Producer GO, SourceRH, and RH.
