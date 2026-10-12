module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Data.Rat

open Purelib.LinearAlgebra

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

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Quadratic.Space3.NullVectors

/-- An explicit certificate that three squares can sum to zero only trivially. Ordered computational fields can provide
this finite interface without importing a general infinite ordered-field hierarchy. -/
structure SumSquaresSeparate (K : Type*)
  [Algebra.Field.ExplicitField K] where
  /-- A vanishing sum of three coordinate squares forces all three coordinates to vanish. -/ separate : ∀ first second
    third : K,
    first ^ 2 + second ^ 2 + third ^ 2 = 0 →
      first = 0 ∧ second = 0 ∧ third = 0

/-- The ordered-field half of Theorem 2, factored through its exact algebraic content: a field whose sums of three
squares separate coordinates has only the zero null vector. -/
theorem only_zero_null_vector (certificate :
  SumSquaresSeparate K)
    (vector : Coordinates3.Vector K) (null : vector.IsNull) : vector = Coordinates3.Vector.zero := by
  have coordinates := certificate.separate vector.t vector.r vector.s (by
    unfold Coordinates3.Vector.IsNull Coordinates3.Vector.quadrance Coordinates3.Vector.dot at null
    simpa only [pow_two] using null)
  exact Coordinates3.Vector.ext coordinates.1 coordinates.2.1 coordinates.2.2

/-- The quotient-free canonical rationals carry an explicit proof that a sum of three squares vanishes only
coordinatewise. -/
theorem rationalSumSquaresSeparate :
    SumSquaresSeparate Fraction.Rational where
  separate := by
    intro first second third sumZero
    have firstNonnegative :=
      Fraction.Order.Arithmetic.sq_nonneg_direct first
    have secondNonnegative :=
      Fraction.Order.Arithmetic.sq_nonneg_direct second
    have thirdNonnegative :=
      Fraction.Order.Arithmetic.sq_nonneg_direct third
    have secondThirdNonnegative : 0 ≤ second ^ 2 + third ^ 2 :=
      add_nonneg secondNonnegative thirdNonnegative
    have firstUpper : first ^ 2 ≤ 0 := by
      have bounded : first ^ 2 ≤ first ^ 2 + (second ^ 2 + third ^ 2) :=
        le_add_of_nonneg_right secondThirdNonnegative
      rwa [← add_assoc, sumZero] at bounded
    have firstSquareZero : first ^ 2 = 0 :=
      le_antisymm firstUpper firstNonnegative
    have secondUpper : second ^ 2 ≤ 0 := by
      have bounded : second ^ 2 ≤
          first ^ 2 + second ^ 2 + third ^ 2 := by
        calc
          second ^ 2 ≤ first ^ 2 + second ^ 2 :=
            le_add_of_nonneg_left firstNonnegative
          _ ≤ first ^ 2 + second ^ 2 + third ^ 2 :=
            le_add_of_nonneg_right thirdNonnegative
      rwa [sumZero] at bounded
    have secondSquareZero : second ^ 2 = 0 :=
      le_antisymm secondUpper secondNonnegative
    have thirdUpper : third ^ 2 ≤ 0 := by
      have firstSecondNonnegative : 0 ≤ first ^ 2 + second ^ 2 :=
        add_nonneg firstNonnegative secondNonnegative
      have bounded : third ^ 2 ≤
          first ^ 2 + second ^ 2 + third ^ 2 :=
        le_add_of_nonneg_left firstSecondNonnegative
      rwa [sumZero] at bounded
    have thirdSquareZero : third ^ 2 = 0 :=
      le_antisymm thirdUpper thirdNonnegative
    exact
      ⟨(Fraction.Order.Arithmetic.sq_eq_zero_direct first).mp
          firstSquareZero,
        (Fraction.Order.Arithmetic.sq_eq_zero_direct second).mp
          secondSquareZero,
        (Fraction.Order.Arithmetic.sq_eq_zero_direct third).mp
          thirdSquareZero⟩

/-- In particular, the only null vector over the repository's executable rational field is zero. -/
theorem rational_only_zero_null_vector
    (vector : Coordinates3.Vector Fraction.Rational)
    (null : vector.IsNull) : vector = Coordinates3.Vector.zero :=
  only_zero_null_vector
    rationalSumSquaresSeparate vector null

set_option genInjectivity false in
/-- The explicit collision between the two square tables used by the finite field proof of Theorem 2. -/
structure SquareCollision (K : Type*) [Algebra.Field.ExplicitField
  K] where
  /-- The retained first square root in the collision. -/ first : K
  /-- The retained second square root in the collision. -/ second : K
  /-- The first square equals the negative of one plus the second square. -/ collision : first ^ 2 = -(1 + second ^ 2)

constructive_injectivity SquareCollision

end Purelib.Geometry.Quadratic.Space3.NullVectors

namespace Purelib.Geometry.Quadratic.Space3.NullVectors.SquareCollision

/-- The paper's finite-field construction turns a square collision into the displayed nonzero null vector `(t,r,1)`. -/
def nullVector (collision :
  SquareCollision K) : Coordinates3.Vector K :=
  ⟨collision.first, collision.second, 1⟩

/-- The vector computed from a square collision is null. -/
theorem nullVector_isNull (collision :
  SquareCollision K) :
    collision.nullVector.IsNull := by
  unfold nullVector Coordinates3.Vector.IsNull
    Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  change collision.first * collision.first +
      collision.second * collision.second + 1 * 1 = 0
  calc
    collision.first * collision.first +
          collision.second * collision.second + 1 * 1 =
        collision.first ^ 2 + collision.second ^ 2 + 1 := by ring1
    _ = 0 := by rw [collision.collision]; ring1

/-- When one is nonzero, the vector computed from a square collision is nonzero because its last coordinate is one. -/
theorem nullVector_ne_zero (collision :
  SquareCollision K)
    (oneNonzero : (1 : K) ≠ 0) :
    collision.nullVector ≠ Coordinates3.Vector.zero := by
  intro equal
  have lastCoordinate := congrArg Coordinates3.Vector.s equal
  exact oneNonzero lastCoordinate

end Purelib.Geometry.Quadratic.Space3.NullVectors.SquareCollision

namespace Purelib.Geometry.Quadratic.Space3.NullVectors

set_option genInjectivity false in
/-- A nonzero null vector stored together with the two finite certificates needed by every downstream use. -/
structure NonzeroNullVector (K : Type*)
  [Algebra.Field.ExplicitField K] where
  /-- The displayed null vector. -/ vector : Coordinates3.Vector K
  /-- The displayed vector has zero quadrance. -/ null : vector.IsNull
  /-- The displayed vector differs from the zero vector. -/ nonzero : vector ≠ Coordinates3.Vector.zero

constructive_injectivity NonzeroNullVector

end Purelib.Geometry.Quadratic.Space3.NullVectors

namespace Purelib.Geometry.Quadratic.Space3.NullVectors.SquareCollision

/-- Package the paper's collision construction as executable output. -/
def nonzeroNullVector (collision :
  SquareCollision K)
    (oneNonzero : (1 : K) ≠ 0) : NonzeroNullVector K where
  vector := collision.nullVector
  null := collision.nullVector_isNull
  nonzero := collision.nullVector_ne_zero oneNonzero

end Purelib.Geometry.Quadratic.Space3.NullVectors.SquareCollision

section

variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

/-- The paper's Theorem 2 collision is the target `-1` specialization of the stronger two-square computation. -/
def squareCollision :
  Purelib.Geometry.Quadratic.Space3.NullVectors.SquareCollision K := by
  let representation := presentation.twoSquareRepresentation (-1)
  refine
    { first := representation.first
      second := representation.second
      collision := ?_ }
  have equation := representation.equation
  calc
    representation.first ^ 2 =
        (representation.first ^ 2 + representation.second ^ 2) -
          representation.second ^ 2 := by ring1
    _ = -1 - representation.second ^ 2 :=
      congrArg (fun value => value - representation.second ^ 2) equation
    _ = -(1 + representation.second ^ 2) := by ring1

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

namespace Purelib.Geometry.Quadratic.Space3.NullVectors

set_option genInjectivity false in
/-- Exact constructive input replacing the paper's cardinality argument for a displayed finite field of odd
characteristic. A presentation supplies the collision calculated for that field rather than globally enumerating all its
elements. -/
structure FiniteOddFieldNullCertificate
    (K : Type*) [Algebra.Field.ExplicitField K] where
  /-- Two is nonzero in the coefficient field. -/ twoNonzero : (2 : K) ≠ 0
  /-- The retained square collision used to construct a nonzero null vector. -/ collision :
    SquareCollision K

constructive_injectivity FiniteOddFieldNullCertificate

end Purelib.Geometry.Quadratic.Space3.NullVectors

section

namespace Purelib.Geometry.Quadratic.Space3.NullVectors.FiniteOddFieldNullCertificate

/-- The retained nonvanishing of two implies that one is nonzero. -/
theorem oneNonzero (certificate :
  FiniteOddFieldNullCertificate K) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply certificate.twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

/-- A checked collision certificate computes the nonzero null vector asserted by the finite-field half of Theorem 2. -/
def witness (certificate :
  FiniteOddFieldNullCertificate K) :
    NonzeroNullVector K :=
  certificate.collision.nonzeroNullVector certificate.oneNonzero

end Purelib.Geometry.Quadratic.Space3.NullVectors.FiniteOddFieldNullCertificate

end

section

variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

/-- The complete finite square-table presentation computes the nonzero null vector asserted by Theorem 2. -/
def nullCertificate :
  Purelib.Geometry.Quadratic.Space3.NullVectors.FiniteOddFieldNullCertificate K where
  twoNonzero := presentation.twoNonzero
  collision := presentation.squareCollision

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

end

end
