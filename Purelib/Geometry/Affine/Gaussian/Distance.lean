module
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction

open Purelib

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Finite measure observations of boxed CCL names

This module turns each boxed CCL certificate into a generic finite
observation and supplies arbitrarily small rational-area observations of a
progressive site.  The possible predicate is deliberately allowed to refine:
no intersection of all cylinders and no completed point is asserted.
-/

namespace Purelib.Geometry.Affine.Gaussian
section

/-- Squared Euclidean distance between two canonical rational Gaussian points.

This is the Gaussian norm of their difference, retained as an exact rational value. -/
def affineDistance (left right : Data.Gaussian.Basic.Canonical) :
  Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (left - right)
end

end Purelib.Geometry.Affine.Gaussian

end
