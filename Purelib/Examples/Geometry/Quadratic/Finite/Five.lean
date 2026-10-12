module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Five
public import Purelib.Algebra.Field.Finite.Five.Presentation
public import Purelib.Geometry.Quadratic.Space3.NullVectors
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

open Purelib

open Purelib.Geometry

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Rational rotations, Theorem 2: null vectors

The paper treats ordered fields and finite fields separately.  The ordered
rational case below is proved from the stored finite numerator order on the
repository's canonical rational carrier.  The finite-field construction is
implemented by a recursive intersection search over explicit carrier and
square tables, so the resulting null vector is executable data rather than a
bare existence claim.
-/

namespace Purelib.Examples.Geometry.Quadratic.Finite.Five

open Purelib.Examples

open Purelib.Algebra.Field.Finite.Five renaming Element -> F5

variable {K : Type*} [ExplicitField K]

namespace FieldFive

/-- Example 3's displayed vector `(1,2,0)` over the executable field `F₅`. -/
def nullVector : Vector3
  F5 := ⟨1, 2, 0⟩

/-- The collision `(0,2)` gives the alternate nonzero null vector `(0,2,1)`
used by the proof of Theorem 2. -/
def squareCollision :
  Quadratic.Space3.NullVectors.SquareCollision F5 where
  first := 0
  second := 2
  collision := by decide

/-- Fully checked finite odd-field input for the executable `F₅` model,
computed by the generic finite square-table intersection. -/
def finiteOddFieldNullCertificate :
  Quadratic.Space3.NullVectors.FiniteOddFieldNullCertificate F5 :=
  Algebra.Field.Finite.Five.Presentation.FieldFive.finiteOddFieldPresentation.nullCertificate

/-- The vector selected by the executable F₅ square-table certificate is null. -/
theorem certificateWitness_isNull :
    finiteOddFieldNullCertificate.witness.vector.IsNull :=
  finiteOddFieldNullCertificate.witness.null

/-- The retained F₅ null-certificate vector is nonzero. -/
theorem certificateWitness_ne_zero :
    finiteOddFieldNullCertificate.witness.vector ≠ Vector3.zero :=
  finiteOddFieldNullCertificate.witness.nonzero

/-- Example 3: `(1,2,0)` has quadrance `1+4=0` in `F₅`. -/
theorem nullVector_isNull :
  nullVector.IsNull := by
  change (1 : F5) * 1 + 2 * 2 + 0 * 0 = 0
  decide

/-- Example 3's null vector is nevertheless nonzero. -/
theorem nullVector_ne_zero :
  nullVector ≠ Vector3.zero := by decide

/-- Example 3 also observes that the nonzero null vector is perpendicular to
itself. -/
theorem nullVector_perpendicular_self :
    nullVector.Perpendicular
      nullVector := by
  change (1 : F5) * 1 + 2 * 2 + 0 * 0 = 0
  decide

end FieldFive

end Purelib.Examples.Geometry.Quadratic.Finite.Five

end
