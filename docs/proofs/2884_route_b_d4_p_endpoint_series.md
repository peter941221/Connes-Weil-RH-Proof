# 2884 Route B D4 endpoint series

The first nonzero owner-path terms of the derivative polynomial are:

```text
right endpoint t -> 0-:   P(t,z(t)) = (210735/5670) t^2 + O(t^4)
left endpoint t -> -1+:   P(t,z(t)) = -384 (t+1)^2 + O((t+1)^3)
```

The right coefficient is positive and the left coefficient is negative. This
explains the zero endpoint values in record 2883 and gives the correct local
sign target for a centered Taylor enclosure. The series are formal local
evidence, not yet a global endpoint certificate.
