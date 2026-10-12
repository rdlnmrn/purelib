module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Curves.Plane

section
@[expose] public section

/-!
# Divine Proportions, §15.1: conics and their centers

A conic is kept as its six displayed coefficients.  Its quadratic part is
required to be nonzero, exactly as in the source.  Center calculations use only
the two finite linear equations obtained by expanding rotation invariance.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The determinant, with the sign convention printed in Theorem 99. -/
def centerDiscriminant (conic : Conic K) : K :=
  conic.e ^ 2 - 4 * conic.d * conic.f

end Purelib.Curves.Plane.Conic

end

section
@[expose] public section

/-!
# Divine Proportions, Exercise 15.14

The quadratic coefficients of a grammola determine a binary quadratic whose
two factors are its diagonal directions.  This avoids diagonalizing a matrix
or selecting square roots.  The unique center then restores the affine line
offsets, and evaluation at that center restores the associated quadrance.
-/

namespace Purelib.Curves.Plane.Conic.QuadraticPart.Grammola

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The homogeneous quadratic part of a displayed conic. -/
def quadraticValue (conic : Conic K) (x y : K) : K
  :=
  conic.d * x ^ 2 + conic.e * x * y + conic.f * y ^ 2

/-- Four times the determinant of the symmetric quadratic coefficient matrix, written without dividing the mixed
coefficient by two. -/
def fourQuadraticDeterminant (conic : Conic K) : K
  :=
  4 * conic.d * conic.f - conic.e ^ 2

end Purelib.Curves.Plane.Conic.QuadraticPart.Grammola

end
