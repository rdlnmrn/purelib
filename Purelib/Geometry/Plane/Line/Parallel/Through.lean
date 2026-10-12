module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

section
@[expose] public section

/-!
# Divine Proportions, Chapter 21: two-dimensional problems

The applications are separated into their finite metric identities and the
geometric incidence arguments that supply those identities.  Denominators are
always accompanied by explicit nonzero certificates.
-/

namespace Purelib.Geometry.Plane.Line.Parallel.Through

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Two lines through a common point and two other points of one displayed line are parallel. -/
public theorem parallel_pair_through_common_line [DecidableEq K]
    (first second third : Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (common : Line K)
    (containsFirst : common.Contains first)
    (containsSecond : common.Contains second)
    (containsThird : common.Contains third) :
    (Incidence.lineThrough first second firstSecondDistinct).Parallel
      (Incidence.lineThrough first third firstThirdDistinct) := by
  have firstEquivalent := Incidence.lineThrough_unique first second
    firstSecondDistinct common containsFirst containsSecond
  have secondEquivalent := Incidence.lineThrough_unique first third
    firstThirdDistinct common containsFirst containsThird
  exact Relations.line_parallel_trans
    (Relations.line_parallel_of_equivalent firstEquivalent)
    (Line.parallel_symm (Relations.line_parallel_of_equivalent secondEquivalent))

end
end Purelib.Geometry.Plane.Line.Parallel.Through

end
