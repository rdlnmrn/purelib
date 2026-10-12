module
public import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Rational rotations, section 7: recovering the anchor

The paper's boxed antisymmetric formula is the executable definition of a
rotation's anchor.  An explicit adjugate inverse for `I + ρ` ties that cached
value to the big Cayley transform; downstream proofs use the cached formula
rather than recomputing the inverse.
-/

namespace Purelib.LinearAlgebra.Coordinates3.Cayley

variable {K : Type*} [ExplicitField K]

/-- Definition 34: the big Cayley transform, with its inverse supplied by the
displayed adjugate certificate. -/
def bigCayley (matrix : Coordinates3.Matrix3 K)
    (defined : Coordinates3.Matrix3.determinant
      (Coordinates3.Matrix3.add Coordinates3.Matrix3.identity matrix) ≠ 0) : Coordinates3.Matrix3 K :=
  Coordinates3.Matrix3.mul (Coordinates3.Matrix3.sub Coordinates3.Matrix3.identity matrix)
    (Coordinates3.Matrix3.inverse (Coordinates3.Matrix3.add Coordinates3.Matrix3.identity matrix) defined)
end Purelib.LinearAlgebra.Coordinates3.Cayley

end
