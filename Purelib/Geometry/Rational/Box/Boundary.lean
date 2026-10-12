module
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction

open Purelib

open Purelib.Geometry

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

section

namespace Purelib.Geometry.Rational.Box.Boundary

/-- Exact coordinate predicate for the boundary of a constructive box. -/
def OnBoxBoundary (box : Rational.Box) (z :
  Data.Gaussian.Basic.Canonical) : Prop :=
  box.Contains z ∧
    (z.re = box.xLower ∨ z.re = box.xUpper ∨
      z.im = box.yLower ∨ z.im = box.yUpper)

/-- Decide whether a Gaussian point lies in the box and on at least one of its four sides. -/
instance onBoxBoundaryDecidable (box : Rational.Box) (z :
  Data.Gaussian.Basic.Canonical) :
    Decidable (OnBoxBoundary box z) := by
  unfold OnBoxBoundary
  infer_instance

end Purelib.Geometry.Rational.Box.Boundary

end

end
