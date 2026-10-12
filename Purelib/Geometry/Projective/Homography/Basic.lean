module
import Purelib.Data.Gaussian.Basic
public import Purelib.LinearAlgebra.Coordinates2.Matrix

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Gaussian.Field

open Purelib

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace Purelib.Geometry.Projective.Homography.Basic

/-- The affine numerator `a*z+b` of a homography. -/
def numerator (matrix : GaussianMatrix) (tail :
  Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  matrix.a * tail + matrix.b

/-- The affine denominator `c*z+d` of a homography. -/
def denominator (matrix : GaussianMatrix) (tail
  : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  matrix.c * tail + matrix.d

/-- Affine value of one finite projective decoder matrix. -/
def homographic (matrix : GaussianMatrix) (tail
  : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  numerator matrix tail * (denominator matrix
    tail)⁻¹
end Purelib.Geometry.Projective.Homography.Basic

end
