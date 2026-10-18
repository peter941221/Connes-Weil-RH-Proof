# 2892 Route B D4 gate

`scripts/route_b_d4_gate2892.py` is the single entrypoint for the committed
D4 artifact gate. It runs the 2891 checker and verifies the resulting JSON
status. A passing gate means the numerical artifacts, generator hashes, and
Cauchy arithmetic are mutually consistent; it does not claim the missing
formal Cauchy theorem or RH.
