# 2913 Route B trigonometric Taylor order sizing

For the two endpoints of the first refined subcell, direct high-precision
replay gives the following scale:

```text
order 16:  sin error about 1.6e-15, cos error about 1.0e-14
order 18:  sin error about 6.1e-19, cos error about 4.5e-18
order 20:  sin error about 1.6e-22, cos error about 1.3e-21
```

The next formal target is therefore an order-20 alternating Taylor enclosure
with a proved remainder, plus rational pi and endpoint-angle brackets.  This
record sizes the proof; it is not itself a formal Taylor certificate.

