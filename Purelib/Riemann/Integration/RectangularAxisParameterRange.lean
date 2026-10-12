module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Tactic.Ring

@[expose] public section

/-! Normalize a whole physical interval in a nondegenerate parent axis.
The two divisions are retained as the executable parameter interval. -/
namespace Purelib.Riemann.Integration.RectangularAxisParameterRange
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Data.Rat.Fraction.Compatibility

set_option genInjectivity false in
/-- A retained parameter interval mapping exactly onto a physical subinterval.

Its endpoints lie between zero and one, and both affine endpoint equations use the same parent axis. -/
structure AxisParameterRange (lower upper : Coordinate) (physical : Interval) where
  /-- The retained strictly ordered rational parameter interval. -/ range : Interval
  /-- Both parameter endpoints lie inside the unit interval. -/ within : 0 ≤ range.lower ∧ range.upper ≤ 1
  /-- The lower parameter endpoint maps to the physical lower endpoint. -/ first_eq : lower + range.lower * (upper -
    lower) = physical.lower
  /-- The upper parameter endpoint maps to the physical upper endpoint. -/ last_eq : lower + range.upper * (upper -
    lower) = physical.upper

constructive_injectivity AxisParameterRange

open Purelib.Data in
open Purelib.Geometry in
/-- Normalize a contained physical interval in a strictly increasing parent axis.

Compute both endpoint divisions once and retain their strict order, unit-interval bounds and exact affine readbacks. -/
def AxisParameterRange.build (lower upper : Coordinate) (physical : Interval) (ordered : lower < upper)
    (contains : lower ≤ physical.lower ∧ physical.upper ≤ upper) : AxisParameterRange lower upper physical :=
  let first := Rectangle.Partition.RectangularOverlapGeometry.SegmentParameter.build lower upper physical.lower ordered
    ⟨contains.1, physical.ordered.le.trans contains.2⟩
  let last := Rectangle.Partition.RectangularOverlapGeometry.SegmentParameter.build lower upper physical.upper ordered
    ⟨contains.1.trans physical.ordered.le, contains.2⟩
  have increasing : first.value < last.value := by
    apply Rat.Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := upper - lower) _
      (Rat.Fraction.Order.Arithmetic.sub_pos_direct ordered)
    have translated := Rat.Fraction.Order.Arithmetic.sub_lt_sub_right_direct physical.ordered lower
    rw [← first.equation, ← last.equation] at translated
    dsimp only [id_eq] at translated
    exact (show first.value * (upper - lower) = (lower + first.value * (upper - lower)) - lower by ring1).trans_lt
      (translated.trans_eq (by ring1))
  ⟨⟨first.value, last.value, increasing⟩, ⟨first.inside.1, last.inside.2⟩, first.equation, last.equation⟩

end Purelib.Riemann.Integration.RectangularAxisParameterRange
