import ConnesWeilRH.Dev.C1RouteAIntervalAlgebra

namespace ConnesWeilRH.Dev

/-- An exact-value interface for a directed real endpoint certificate.

The `lo_le` and `value_le` fields are the only obligations a future MPFR or
IEEE proof must supply.  No machine arithmetic is modeled here. -/
structure DirectedRealValue2433 where
  value : ℝ
  interval : RealInterval2429
  lo_le : interval.lo ≤ value
  value_le : value ≤ interval.hi

def DirectedRealValue2433.product (a b : DirectedRealValue2433) :
    DirectedRealValue2433 :=
  let interval := a.interval.mul b.interval
  { value := a.value * b.value
    interval := interval
    lo_le := (RealInterval2429.mem_mul
      ⟨a.lo_le, a.value_le⟩ ⟨b.lo_le, b.value_le⟩).1
    value_le := (RealInterval2429.mem_mul
      ⟨a.lo_le, a.value_le⟩ ⟨b.lo_le, b.value_le⟩).2 }

def DirectedRealValue2433.sum (a b : DirectedRealValue2433) :
    DirectedRealValue2433 :=
  let interval := a.interval.add b.interval
  { value := a.value + b.value
    interval := interval
    lo_le := (RealInterval2429.mem_add
      ⟨a.lo_le, a.value_le⟩ ⟨b.lo_le, b.value_le⟩).1
    value_le := (RealInterval2429.mem_add
      ⟨a.lo_le, a.value_le⟩ ⟨b.lo_le, b.value_le⟩).2 }

def DirectedRealValue2433.difference (a b : DirectedRealValue2433) :
    DirectedRealValue2433 :=
  let interval := a.interval.sub b.interval
  { value := a.value - b.value
    interval := interval
    lo_le := (RealInterval2429.mem_sub
      ⟨a.lo_le, a.value_le⟩ ⟨b.lo_le, b.value_le⟩).1
    value_le := (RealInterval2429.mem_sub
      ⟨a.lo_le, a.value_le⟩ ⟨b.lo_le, b.value_le⟩).2 }

/-- A directed complex value whose real and imaginary endpoints are certified. -/
structure DirectedComplexValue2433 where
  value : ℂ
  rectangle : ComplexRect2427
  contains : rectangle.Mem value

def DirectedComplexValue2433.product (a b : DirectedComplexValue2433) :
    DirectedComplexValue2433 :=
  { value := a.value * b.value
    rectangle := a.rectangle.mul b.rectangle
    contains := ComplexRect2427.mem_mul a.contains b.contains }

def DirectedComplexValue2433.sum (a b : DirectedComplexValue2433) :
    DirectedComplexValue2433 :=
  { value := a.value + b.value
    rectangle := a.rectangle.add b.rectangle
    contains := ComplexRect2427.mem_add a.contains b.contains }

def DirectedComplexValue2433.difference (a b : DirectedComplexValue2433) :
    DirectedComplexValue2433 :=
  { value := a.value - b.value
    rectangle := a.rectangle.sub b.rectangle
    contains := ComplexRect2427.mem_sub a.contains b.contains }

end ConnesWeilRH.Dev
