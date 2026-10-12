module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace Purelib.Geometry.Space.Metric.DirectionSpread.Residual

section

variable {K : Type*} [ExplicitField K]

/-- The spread of two non-null vectors is their Gram residual divided by the product of quadrances.

Both quadrances must be nonzero, so the denominator can be cancelled in the explicit field. -/
public theorem directionSpread_residual_formula
    (first second : Coordinates3.Vector K)
    (firstNonzero : Coordinates3.Vector.quadrance first ≠ 0)
    (secondNonzero : Coordinates3.Vector.quadrance second ≠ 0) :
    Coordinates3.Vector.spread first second firstNonzero secondNonzero =
      (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second -
          Coordinates3.Vector.dot first second ^ 2) /
        (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second) := by
  have denominatorNonzero :
      Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second ≠ 0 :=
    ExplicitField.mul_ne_zero firstNonzero secondNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  unfold Coordinates3.Vector.spread
  have leftCancel := ExplicitField.div_mul_cancel
    (Coordinates3.Vector.dot first second ^ 2) denominatorNonzero
  have rightCancel := ExplicitField.div_mul_cancel
    (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second - Coordinates3.Vector.dot first second ^
      2)
      denominatorNonzero
  calc
    (1 - Coordinates3.Vector.dot first second ^ 2 /
          (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second)) *
        (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second) =
      Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second -
        (Coordinates3.Vector.dot first second ^ 2 /
          (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second)) *
          (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second) := by ring1
    _ = Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second -
        Coordinates3.Vector.dot first second ^ 2 := by
      rw [leftCancel]
    _ = ((Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second -
          Coordinates3.Vector.dot first second ^ 2) /
          (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second)) *
        (Coordinates3.Vector.quadrance first * Coordinates3.Vector.quadrance second) :=
      rightCancel.symm

end
end Purelib.Geometry.Space.Metric.DirectionSpread.Residual

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 22: three-dimensional problems

The source explicitly describes its three-dimensional treatment as informal.
Here every assertion is split into finite Cartesian dot-product algebra and
the scalar identities used in the printed solutions.  Algebraic roots and
distances are supplied as witnesses; no completed real-number construction is
introduced.
-/

namespace Purelib.Geometry.Space.Metric.DirectionSpread.Residual

section

variable {K : Type*} [ExplicitField K]

/-- Equal nonzero vector quadrances express spread as `(metric² - dotValue²) / metric²`.

The supplied equalities identify both quadrances and their dot product with the retained scalar data. -/
public theorem directionSpread_metric_formula
    (first second : Coordinates3.Vector K) (metric dotValue : K)
    (metricNonzero : metric ≠ 0)
    (firstMetric : Coordinates3.Vector.quadrance first = metric)
    (secondMetric : Coordinates3.Vector.quadrance second = metric)
    (dotMetric : Coordinates3.Vector.dot first second = dotValue) :
    Coordinates3.Vector.spread first second
        (by rw [firstMetric]; exact metricNonzero)
        (by rw [secondMetric]; exact metricNonzero) =
      (metric ^ 2 - dotValue ^ 2) / metric ^ 2 := by
  have denominatorNonzero : metric * metric ≠ 0 :=
    ExplicitField.mul_ne_zero metricNonzero metricNonzero
  apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
  unfold Coordinates3.Vector.spread
  rw [firstMetric, secondMetric, dotMetric]
  have leftCancel :=
    ExplicitField.div_mul_cancel (dotValue ^ 2) denominatorNonzero
  have rightCancel :=
    ExplicitField.div_mul_cancel
      (metric ^ 2 - dotValue ^ 2) denominatorNonzero
  calc
    (1 - dotValue ^ 2 / (metric * metric)) * (metric * metric) =
        metric ^ 2 -
          (dotValue ^ 2 / (metric * metric)) * (metric * metric) := by
            ring1
    _ = metric ^ 2 - dotValue ^ 2 := by rw [leftCancel]
    _ = ((metric ^ 2 - dotValue ^ 2) / metric ^ 2) *
          (metric * metric) := by
            simpa only [pow_two] using rightCancel.symm

end
end Purelib.Geometry.Space.Metric.DirectionSpread.Residual

end
