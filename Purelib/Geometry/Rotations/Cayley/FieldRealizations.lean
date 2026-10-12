module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.ExplicitOrder.Basic
import Purelib.Algebra.Field.ExplicitOrder.Sign
public import Purelib.Algebra.Field.ExplicitOrder.Differences
import Purelib.Algebra.Field.Finite.Odd.Presentation
public import Purelib.Algebra.Field.Finite.Odd.ThreeSquares
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Geometry.Quadratic.Space3.NullVectors
import Purelib.Geometry.Quadratic.Space3.Ordered
public import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Ring.Nat
import Purelib.Data.Rat.Fraction.Order.Arithmetic

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Algebra.Field.ExplicitOrder.Basic

open Purelib.Algebra.Field.Finite.Odd

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Data.Rat

open Purelib.Geometry.Quadratic.Space3

open Purelib.Geometry.Quadratic.Space3.Ordered

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Cayley

open Purelib.Geometry.Rotations.Projective.Action

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Field-specific claims between the numbered results

The paper makes several mathematical assertions in the prose surrounding
Theorems 24 and 29.  This module records them explicitly.  Ordered and
rational claims are proved directly from finite coordinates.  The assertion
that every half-spread value occurs over a finite field is computed from an
explicit finite carrier and cached square table, with no choice-derived
enumeration or witness.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Geometry.Rotations.Cayley.FieldRealizations

/-- A null anchor has the unipotent quadratic cap formula stated before Example 27. -/
theorem cap_of_null (vector : Coordinates3.Vector K)
    (defined : Cap.capDenominator vector ≠ 0)
    (null : vector.quadrance = 0) :
    Cap.cap vector defined =
      Matrix3.add Matrix3.identity
        (Matrix3.scale 2
          (Matrix3.add (Antisymmetric.anchor vector)
            (Matrix3.mul (Antisymmetric.anchor vector) (Antisymmetric.anchor vector)))) := by
  have denominatorOne : Cap.capDenominator vector = 1 := by
    unfold Cap.capDenominator
    rw [null]
    ring1
  have oneNonzero : (1 : K) ≠ 0 := by
    rw [← denominatorOne]
    exact defined
  have inverseOne : (1 : K)⁻¹ = 1 := by
    have cancel := ExplicitField.mul_inv_cancel (1 : K) oneNonzero
    simpa only [one_mul] using cancel
  rw [Cap.cap_quadratic vector defined, denominatorOne,
    ExplicitField.div_eq_mul_inv, inverseOne, mul_one]

/-- The characteristic polynomial of every null cap is `(X-1)³`, not only for the displayed `F₅` example. -/
theorem characteristicValue_cap_of_null (vector :
  Coordinates3.Vector K)
    (defined : Cap.capDenominator vector ≠ 0)
    (null : vector.quadrance = 0) (X : K) :
    Matrix3.characteristicValue (Cap.cap vector defined) X = (X - 1) ^ 3 := by
  have denominatorOne : Cap.capDenominator vector = 1 := by
    unfold Cap.capDenominator
    rw [null]
    ring1
  have oneNonzero : (1 : K) ≠ 0 := by
    rw [← denominatorOne]
    exact defined
  have inverseOne : (1 : K)⁻¹ = 1 := by
    have cancel := ExplicitField.mul_inv_cancel (1 : K) oneNonzero
    simpa only [one_mul] using cancel
  rw [Cap.characteristicValue_cap vector defined X, null, denominatorOne,
    ExplicitField.div_eq_mul_inv, inverseOne]
  ring1

/-- The cap at the zero anchor is the identity matrix. -/
theorem cap_zero_eq_identity
    (defined : Cap.capDenominator (Coordinates3.Vector.zero : Coordinates3.Vector K) ≠ 0) :
    Cap.cap Coordinates3.Vector.zero defined = Matrix3.identity := by
  rw [cap_of_null Coordinates3.Vector.zero defined
    Coordinates3.Vector.quadrance_zero]
  ext <;>
    unfold Matrix3.add Matrix3.scale Matrix3.mul Matrix3.identity Antisymmetric.anchor
      Coordinates3.Vector.zero <;>
    ring1

/-! ## Rational cap claims -/

end Purelib.Geometry.Rotations.Cayley.FieldRealizations

section

namespace Purelib.Geometry.Rotations.Cayley.FieldRealizations.RationalFieldClaims

/-- The unnumbered assertion after Lemma 22: every rational anchor lies in the domain of the cap. -/
theorem capDenominator_positive (vector :
  Coordinates3.Vector Fraction.Rational) :
    0 < Cap.capDenominator vector := by
  have onePositive : (0 : Fraction.Rational) < 1 :=
    Fraction.Cast.Order.natCast_pos_direct
      (n := 1) (by decide)
  have oneAtMost : (1 : Fraction.Rational) ≤ 1 + vector.quadrance :=
    le_add_of_nonneg_right (RationalFieldClaims.vector_quadrance_nonnegative vector)
  unfold Cap.capDenominator
  exact lt_of_lt_of_le onePositive oneAtMost

/-- Every rational anchor has nonzero cap denominator. -/
theorem capDenominator_ne_zero (vector :
  Coordinates3.Vector Fraction.Rational) :
    Cap.capDenominator vector ≠ 0 :=
  (capDenominator_positive vector).ne'

/-- Over the rationals a null anchor is zero, so the corresponding cap is the identity; the nonidentity parabolic
phenomenon of Example 27 cannot occur. -/
theorem null_cap_eq_identity (vector :
  Coordinates3.Vector Fraction.Rational)
    (null : vector.quadrance = 0) :
    Cap.cap vector (capDenominator_ne_zero vector) =
      Matrix3.identity := by
  have vectorZero : vector = Coordinates3.Vector.zero :=
    NullVectors.rational_only_zero_null_vector vector null
  rw [vectorZero]
  exact cap_zero_eq_identity _

end Purelib.Geometry.Rotations.Cayley.FieldRealizations.RationalFieldClaims

end

/-! ## Ordered half-spread interval -/

section

variable {F : Type*} [Purelib.Algebra.Field.ExplicitOrder.Basic.OrderedExplicitField F]

-- Keep this instance's original owner and activation throughout the ordered-field section.
with_weak_namespace _root_.Purelib.Rotations.OrderedFieldClaims
  /-- Use the ordered field's explicit equality decision. -/
  local instance : DecidableEq F := OrderedExplicitField.eq_decidable

namespace Purelib.Geometry.Rotations.Cayley.FieldRealizations.OrderedFieldClaims

/-- Every anchor over the supplied ordered field has positive cap denominator. -/
theorem capDenominatorPositive (vector :
  Coordinates3.Vector F) :
    0 < Cap.capDenominator vector := by
  by_cases vectorZero : vector = Coordinates3.Vector.zero
  · rw [vectorZero]
    unfold Cap.capDenominator
    rw [Coordinates3.Vector.quadrance_zero, add_zero]
    exact OrderedExplicitField.zero_lt_one_direct
  · unfold Cap.capDenominator
    exact OrderedExplicitField.add_pos_direct
      OrderedExplicitField.zero_lt_one_direct
      (Purelib.Geometry.Quadratic.Space3.Ordered.OrderedFieldClaims.vectorQuadrancePositive vector vectorZero)

/-- The lower half of the source's interval assertion: an ordered-field cap has zero or strictly positive half spread.
-/
theorem halfSpread_cap_eq_zero_or_positive
  (vector : Coordinates3.Vector F)
    (defined : Cap.capDenominator vector ≠ 0)
    (twoNonzero : (2 : F) ≠ 0) :
    Spread.halfSpread (Cap.capRotation vector defined) = 0 ∨
      0 < Spread.halfSpread (Cap.capRotation vector defined) := by
  by_cases vectorZero : vector = Coordinates3.Vector.zero
  · left
    rw [Spread.halfSpread_cap vector defined twoNonzero, vectorZero,
      Coordinates3.Vector.quadrance_zero, ExplicitField.zero_div]
  · right
    rw [Spread.halfSpread_cap vector defined twoNonzero,
      ExplicitField.div_eq_mul_inv]
    exact OrderedExplicitField.mul_pos_direct
      (Purelib.Geometry.Quadratic.Space3.Ordered.OrderedFieldClaims.vectorQuadrancePositive vector vectorZero)
      (OrderedExplicitField.inv_pos_direct
        (capDenominatorPositive vector))

/-- The upper half of the interval assertion, expressed without adding a second generic order hierarchy: the complement
`1-p` is strictly positive. -/
theorem one_sub_halfSpread_cap_positive
  (vector : Coordinates3.Vector F)
    (defined : Cap.capDenominator vector ≠ 0)
    (twoNonzero : (2 : F) ≠ 0) :
    0 < 1 - Spread.halfSpread (Cap.capRotation vector defined) := by
  rw [Spread.one_sub_halfSpread_cap vector defined twoNonzero,
    ExplicitField.div_eq_mul_inv]
  exact OrderedExplicitField.mul_pos_direct
    OrderedExplicitField.zero_lt_one_direct
    (OrderedExplicitField.inv_pos_direct
      (capDenominatorPositive vector))

end Purelib.Geometry.Rotations.Cayley.FieldRealizations.OrderedFieldClaims

end

namespace Purelib.Geometry.Rotations.Cayley.FieldRealizations

/-- For `p ≠ 1`, three squares representing `p(1-p)` give the proportion `(1-p:t:r:s)`, whose norm is exactly `1-p`. -/
def affineHalfSpreadPreimage (algorithm :
  ThreeSquares.ThreeSquareAlgorithm K)
    (value : K) (notOne : value ≠ 1) : Projective.Basic.NonNullProportion K := by
  let output := algorithm.represent (value * (1 - value))
  refine
    { scalar := 1 - value
      vector := output.vector
      normNonzero := ?_ }
  have quadrance := output.vector_quadrance
  change (1 - value) ^ 2 + output.vector.quadrance ≠ 0
  rw [quadrance]
  have normValue :
      (1 - value) ^ 2 + value * (1 - value) = 1 - value := by ring1
  rw [normValue]
  intro differenceZero
  apply notOne
  calc
    value = 1 - (1 - value) := by ring1
    _ = 1 := by rw [differenceZero]; ring1

/-- The three-square preimage for a value other than one has norm `1 - value`. -/
theorem affineHalfSpreadPreimage_norm (algorithm :
  ThreeSquares.ThreeSquareAlgorithm K)
    (value : K) (notOne : value ≠ 1) :
    (affineHalfSpreadPreimage algorithm value notOne).toProportion.norm =
      1 - value := by
  let output := algorithm.represent (value * (1 - value))
  change (1 - value) ^ 2 + output.vector.quadrance = 1 - value
  rw [output.vector_quadrance]
  ring1

/-- The constructed affine preimage has the requested half spread.

The value differs from one, and two is nonzero in the coefficient field. -/
theorem affineHalfSpreadPreimage_value (algorithm :
  ThreeSquares.ThreeSquareAlgorithm K)
    (value : K) (notOne : value ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (NonNullProportion.rotation (affineHalfSpreadPreimage
      algorithm value notOne)) =
      value := by
  rw [NonNullProportion.halfSpread_rotation _ twoNonzero]
  let output := algorithm.represent (value * (1 - value))
  change output.vector.quadrance /
      (affineHalfSpreadPreimage algorithm value notOne).toProportion.norm =
    value
  rw [output.vector_quadrance,
    affineHalfSpreadPreimage_norm algorithm value notOne]
  rw [ExplicitField.div_eq_mul_inv]
  calc
    value * (1 - value) * (1 - value)⁻¹ =
        value * ((1 - value) * (1 - value)⁻¹) := by ring1
    _ = value := by
      rw [ExplicitField.mul_inv_cancel
        (1 - value) ((fun {K : Type _} [ExplicitField K] {value : K} (notOne : value ≠ 1) =>
          (ExplicitField.one_sub_ne_zero_of_ne_one (K := K) (value := value) notOne : 1 - value ≠
          0)) notOne),
          mul_one]

/-- A fixed proportion at infinity supplies half spread one. -/
def halfTurnHalfSpreadPreimage (twoNonzero : (2 : K) ≠ 0) :
    Projective.Basic.NonNullProportion K where
  scalar := 0
  vector := ⟨1, 0, 0⟩
  normNonzero := by
    intro normZero
    apply (fun {K : Type _} [ExplicitField K] (twoNonzero : (2 : K) ≠ 0) =>
      (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero (K := K) twoNonzero : (1 : K) ≠ 0))
      twoNonzero
    calc
      (1 : K) = Proportion.norm
          (⟨0, (⟨1, 0, 0⟩ : Coordinates3.Vector K)⟩ : Proportion K) := by
        unfold Proportion.norm
          Purelib.LinearAlgebra.Coordinates3.Vector.quadrance Purelib.LinearAlgebra.Coordinates3.Vector.dot
        ring1
      _ = 0 := normZero

/-- The fixed coordinate half-turn preimage has half spread one. -/
theorem halfTurnHalfSpreadPreimage_value [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.halfSpread (NonNullProportion.rotation
      (halfTurnHalfSpreadPreimage twoNonzero)) = 1 :=
  (NonNullProportion.halfSpread_rotation_eq_one_iff
    (halfTurnHalfSpreadPreimage twoNonzero) twoNonzero).2 rfl

/-- A three-square algorithm computes a rotation for every requested half-spread value. -/
theorem halfSpread_surjective_of_threeSquareAlgorithm
  [DecidableEq K]
    (algorithm : ThreeSquares.ThreeSquareAlgorithm K) (twoNonzero : (2 : K) ≠ 0)
    (value : K) :
    ∃ proportion : Projective.Basic.NonNullProportion K,
      Spread.halfSpread (NonNullProportion.rotation proportion) = value := by
  by_cases valueOne : value = 1
  · subst value
    exact ⟨halfTurnHalfSpreadPreimage twoNonzero,
      halfTurnHalfSpreadPreimage_value twoNonzero⟩
  · exact ⟨affineHalfSpreadPreimage algorithm value valueOne,
      affineHalfSpreadPreimage_value algorithm value valueOne twoNonzero⟩

end Purelib.Geometry.Rotations.Cayley.FieldRealizations

namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

/-- The unnumbered finite-field assertion after Theorem 29: an explicit finite odd-field square presentation computes a
rotation with every requested half-spread value. -/
theorem halfSpread_surjective
    (presentation : Presentation.FiniteOddFieldPresentation K) (value : K) :
    ∃ proportion : Projective.Basic.NonNullProportion K,
      Spread.halfSpread (NonNullProportion.rotation proportion) = value := by
  letI : DecidableEq K := presentation.eqDecidable
  exact Purelib.Geometry.Rotations.Cayley.FieldRealizations.halfSpread_surjective_of_threeSquareAlgorithm
    presentation.threeSquareAlgorithm presentation.twoNonzero value

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

end

public section

section

open Purelib.Algebra.Field.ExplicitOrder.Sign

variable {F : Type*} [RayOrderedExplicitField F]

namespace Purelib.Geometry.Rotations.Cayley.FieldRealizations.OrderedFieldClaims

/-- Every Euclidean anchor in a ray-ordered field has a nonzero cap denominator.

The original sum-of-squares denominator is positive. The retained positive
cone excludes zero, providing the domain certificate for the original cap.
-/
theorem capDenominatorNonzero (vector : Vector3 F) : Cap.capDenominator vector ≠ 0 :=
  RayOrderedExplicitField.positive_ne_zero_direct (capDenominatorPositive vector)

/-- An ordered Euclidean cap has nonnegative half spread strictly below one.

The lower endpoint uses equality or strict positivity. The upper comparison
uses the supplied difference law for the same original field and order,
together with the retained positive complement of the cap's half spread.
-/
theorem halfSpread_cap_unit_interval (law : OrderDifferenceLaw F) (vector : Vector3 F)
    (defined : Cap.capDenominator vector ≠ 0) (twoNonzero : (2 : F) ≠ 0) :
    (Spread.halfSpread (Cap.capRotation vector defined) = 0 ∨
      0 < Spread.halfSpread (Cap.capRotation vector defined)) ∧
    Spread.halfSpread (Cap.capRotation vector defined) < 1 :=
  ⟨halfSpread_cap_eq_zero_or_positive vector defined twoNonzero,
    (law.lt_one_iff _).mpr (one_sub_halfSpread_cap_positive vector defined twoNonzero)⟩

end Purelib.Geometry.Rotations.Cayley.FieldRealizations.OrderedFieldClaims

end
