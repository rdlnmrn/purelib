module

import Purelib.Algebra.Field.Characteristic.Nonzero

import Purelib.Data.Rat.Fraction.Order.Cast
public import Purelib.Examples.Geometry.Rotations.Reflections
public import Purelib.Examples.Geometry.Rotations.Caps
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Five
import Purelib.Algebra.Field.Inverse
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Examples.Geometry.Rotations.HalfSpreads
public import Purelib.Geometry.Rotations.Axis.Recovery
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rotations.Basic
import Purelib.Geometry.Rotations.Reflection
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Rational rotations, section 7: recovering the anchor

The paper's boxed antisymmetric formula is the executable definition of a
rotation's anchor.  An explicit adjugate inverse for `I + ρ` ties that cached
value to the big Cayley transform; downstream proofs use the cached formula
rather than recomputing the inverse.
-/

namespace Purelib.Examples.Geometry.Rotations.RotationAnchors

open Purelib.Examples

open Purelib.Geometry.Rotations.Cayley
open Purelib.Examples.Geometry.Rotations
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rotations.Axis

open Purelib.Rotations

variable {K : Type*} [ExplicitField K]
namespace ExampleThirtySix

/-- The rational cap rotation of the displayed anchor vector (4, 1, 7). -/
def rotation : Rotations.Basic.Rotation
  Fraction.Rational :=
  Cap.capRotation Caps.ExampleTwentyFive.vector
    Caps.ExampleTwentyFive.defined

/-- Two is nonzero in the displayed rational field. -/
theorem displayedTwoNonzero : (2 :
  Fraction.Rational) ≠ 0 := by
  intro castZero
  exact (by decide : (2 : Nat) ≠ 0)
    (Fraction.Cast.Compatibility.natCast_injective_direct castZero)

/-- The displayed rational rotation has trace −63/67. -/
theorem trace_value :
  Coordinates3.Matrix3.trace rotation.matrix = (-63 :
  Fraction.Rational) / 67 := by
  unfold rotation
  change Coordinates3.Matrix3.trace
      (Cap.cap Caps.ExampleTwentyFive.vector
        Caps.ExampleTwentyFive.defined) =
    (-63 : Fraction.Rational) / 67
  rw [Cap.trace_cap]
  unfold Cap.capDenominator
  rw [Caps.ExampleTwentyFive.quadrance]
  have numerator : (3 - 66 : Fraction.Rational) = -63 := by ring1
  have denominator : (1 + 66 : Fraction.Rational) = 67 := by ring1
  rw [numerator, denominator]

/-- One plus the displayed rotation trace equals 4/67. -/
theorem trace_denominator :
    1 + Coordinates3.Matrix3.trace rotation.matrix = (4 :
      Fraction.Rational) / 67 := by
  rw [trace_value]
  exact Purelib.Algebra.Field.Inverse.one_add_neg_sixtyThree_div_sixtySeven
    (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 67) (by decide) : (67 :
      Rational) ≠ 0)

/-- The explicit antisymmetric matrix scaled by 1/67. -/
def displayedAntisymmetricPart :
  Coordinates3.Matrix3 Fraction.Rational :=
  Coordinates3.Matrix3.scale (1 / 67) ⟨0, 14, -2, -14, 0, 8, 2, -8, 0⟩

/-- The antisymmetric matrix of the displayed anchor has the stated scaled coordinates when two is nonzero. -/
private theorem
  antisymmetricPart_numeric
    {F : Type*} [ExplicitField F] (twoNonzero : (2 : F) ≠ 0) :
    Coordinates3.Matrix3.scale ((1 / 2 : F) * (4 / 67))
        (Coordinates3.Antisymmetric.anchor (⟨4, 1, 7⟩ : Vector3 F)) =
      Coordinates3.Matrix3.scale (1 / 67)
        ⟨0, 14, -2, -14, 0, 8, 2, -8, 0⟩ := by
  have twoCancel := ExplicitField.mul_inv_cancel (2 : F) twoNonzero
  have coefficient :
      (1 / 2 : F) * (4 / 67) = 2 / 67 := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      1 * (2 : F)⁻¹ * (4 * (67 : F)⁻¹) =
          (2 * (67 : F)⁻¹) * (2 * (2 : F)⁻¹) := by ring1
      _ = 2 * (67 : F)⁻¹ := by rw [twoCancel]; ring1
  rw [coefficient]
  ext <;> unfold Coordinates3.Matrix3.scale Coordinates3.Antisymmetric.anchor <;>
    simp only [ExplicitField.div_eq_mul_inv] <;> ring1

/-- The rotation's antisymmetric part equals the displayed matrix. -/
theorem antisymmetricPart_displayed :
    Coordinates3.Antisymmetric.antisymmetricPart rotation.matrix =
      displayedAntisymmetricPart := by
  have denominator :
      Cap.capDenominator Caps.ExampleTwentyFive.vector = (67 : Fraction.Rational) :=
        by
    unfold Cap.capDenominator
    rw [Caps.ExampleTwentyFive.quadrance]
    ring1
  unfold rotation Cap.capRotation
    Coordinates3.Antisymmetric.antisymmetricPart
    displayedAntisymmetricPart
  rw [Cap.cap_antisymmetric_part, denominator, Coordinates3.Matrix3.scale_scale]
  exact antisymmetricPart_numeric
    (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 2) (by decide) : (2 :
      Rational) ≠ 0)

/-- Recovery from the rotation returns the antisymmetric anchor of its original cap vector. -/
theorem recovered_anchor :
    Recovery.rotationAnchor rotation
        (Rotations.Spread.halfSpread_cap_ne_one Caps.ExampleTwentyFive.vector
          Caps.ExampleTwentyFive.defined
            displayedTwoNonzero) =
      Coordinates3.Antisymmetric.anchor Caps.ExampleTwentyFive.vector := by
  exact Recovery.rotationAnchor_cap Caps.ExampleTwentyFive.vector
    Caps.ExampleTwentyFive.defined
    displayedTwoNonzero

/-- Recovery from the rotation returns its original vector (4, 1, 7). -/
theorem recovered_vector :
    Recovery.rotationAnchorVector rotation
        (Rotations.Spread.halfSpread_cap_ne_one Caps.ExampleTwentyFive.vector
          Caps.ExampleTwentyFive.defined
            displayedTwoNonzero) =
      Caps.ExampleTwentyFive.vector := by
  apply Coordinates3.Antisymmetric.anchor_injective
  rw [Recovery.anchor_rotationAnchorVector rotation _
    displayedTwoNonzero,
    recovered_anchor]

end ExampleThirtySix
namespace ExampleThirtyNine

/-- The two displayed reflection normals have dot product one. -/
theorem dot_value :
    Vector3.dot Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second =
      (1 : Fraction.Rational) :=
  HalfSpreads.ExampleThirtyThree.dot_value

/-- The two displayed reflection normals have nonzero dot product. -/
theorem dot_nonzero :
    Vector3.dot Reflections.ExampleTwenty.first Reflections.ExampleTwenty.second ≠
      (0 : Fraction.Rational) := by
  rw [dot_value]
  intro oneZero
  exact (by decide : (1 : Nat) ≠ 0)
    (Fraction.Cast.Compatibility.natCast_injective_direct oneZero)

/-- The reflection-product anchor recovery returns the original displayed axis. -/
theorem recovered_vector :
    Recovery.reflectionProductAnchorVector Reflections.ExampleTwenty.first
      Reflections.ExampleTwenty.second
        dot_nonzero =
          Reflections.ExampleTwenty.axis := by
  unfold Recovery.reflectionProductAnchorVector
  rw [dot_value,
    Reflections.ExampleTwenty.cross_displayed]
  have oneNonzero : (1 : Fraction.Rational) ≠ 0 := by
    intro oneZero
    exact (by decide : (1 : Nat) ≠ 0)
      (Fraction.Cast.Compatibility.natCast_injective_direct oneZero)
  have oneCancel := ExplicitField.mul_inv_cancel (1 : Fraction.Rational) oneNonzero
  have oneDivOne : (1 : Fraction.Rational) / 1 = 1 := by
    rw [ExplicitField.div_eq_mul_inv, oneCancel]
  rw [oneDivOne, Vector3.one_scale]

/-- The recovered reflection-product anchor has quadrance 83. -/
theorem recovered_quadrance :
    (Recovery.reflectionProductAnchorVector Reflections.ExampleTwenty.first
      Reflections.ExampleTwenty.second
      dot_nonzero).quadrance = (83 : Fraction.Rational) := by
  rw [recovered_vector]
  unfold Reflections.ExampleTwenty.axis Vector3.quadrance Vector3.dot
  ring1

/-- The ratio of the reflection spread to its complement equals 83. -/
theorem half_twist :
    Vector3.spread Reflections.ExampleTwenty.first
      Reflections.ExampleTwenty.second
        Reflections.ExampleTwenty.first_nonNull
          Reflections.ExampleTwenty.second_nonNull /
      (1 - Vector3.spread Reflections.ExampleTwenty.first
        Reflections.ExampleTwenty.second
        Reflections.ExampleTwenty.first_nonNull
          Reflections.ExampleTwenty.second_nonNull) =
      (83 : Fraction.Rational) := by
  rw [← Recovery.quadrance_reflectionProductAnchorVector
    Reflections.ExampleTwenty.first
      Reflections.ExampleTwenty.second Reflections.ExampleTwenty.first_nonNull
      Reflections.ExampleTwenty.second_nonNull
        dot_nonzero
        (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 2) (by decide) : (2 :
          Rational) ≠ 0),
    recovered_quadrance]

end ExampleThirtyNine
namespace CanonicalAxisSpreadExamples

/-- Two is nonzero in the rational canonical-axis examples. -/
theorem rationalTwoNonzero : (2 :
  Fraction.Rational) ≠ 0 := by
  intro castZero
  exact (by decide : (2 : Nat) ≠ 0)
    (Fraction.Cast.Compatibility.natCast_injective_direct castZero)

/-- One is nonzero in the rational canonical-axis examples. -/
theorem rationalOneNonzero : (1 :
  Fraction.Rational) ≠ 0 :=
  Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_two_ne_zero
    rationalTwoNonzero

/-- Two is nonzero in the explicit five-element field. -/
theorem fieldFiveTwoNonzero : (2
  : Algebra.Field.Finite.Five.Element) ≠ 0 := by decide

/-- The zero-vector cap denominator is nonzero over the rationals. -/
theorem identityDefined :
    Cap.capDenominator (Vector3.zero : Vector3 Fraction.Rational) ≠ 0 := by
  unfold Cap.capDenominator
  rw [Vector3.quadrance_zero, add_zero]
  exact rationalOneNonzero

/-- The rational identity rotation constructed from the zero-vector cap. -/
def identity :
  Rotations.Basic.Rotation Fraction.Rational :=
  Cap.capRotation Vector3.zero
    identityDefined

/-- The nonidentity null-axis cap over the explicit five-element field. -/
def nullCap :
  Rotations.Basic.Rotation Algebra.Field.Finite.Five.Element :=
  Cap.capRotation Caps.ExampleTwentySeven.vector
    Caps.ExampleTwentySeven.defined

/-- The rational unit coordinate axis (1, 0, 0) for the half-turn example. -/
def halfTurnAxisExample : Vector3
  Fraction.Rational := ⟨1, 0, 0⟩

/-- The displayed half-turn axis has nonzero quadrance. -/
theorem
  halfTurnAxisExample_nonNull :
  Vector3.quadrance halfTurnAxisExample ≠ 0 := by
  intro quadranceZero
  apply rationalOneNonzero
  calc
    (1 : Fraction.Rational) = Vector3.quadrance
      Geometry.Rotations.RotationAnchors.CanonicalAxisSpreadExamples.halfTurnAxisExample := by
      unfold halfTurnAxisExample Vector3.quadrance
        Vector3.dot
      ring1
    _ = 0 := quadranceZero

/-- The rational half turn about the displayed unit coordinate axis. -/
def halfTurnExample :
  Rotations.Basic.Rotation Fraction.Rational :=
  Rotations.Reflection.halfTurnRotation
    halfTurnAxisExample
    halfTurnAxisExample_nonNull

/-- The rational identity rotation has half spread zero. -/
theorem identity_halfSpread :
  Rotations.Spread.halfSpread identity = 0 := by
  unfold identity
  rw [Rotations.Spread.halfSpread_cap Vector3.zero
    identityDefined
    rationalTwoNonzero,
    Vector3.quadrance_zero]
  unfold Cap.capDenominator
  exact ExplicitField.zero_div _

/-- The nonidentity null cap over the five-element field has half spread zero. -/
theorem nullCap_halfSpread :
  Rotations.Spread.halfSpread nullCap = 0 := by
  unfold nullCap
  rw [Rotations.Spread.halfSpread_cap Caps.ExampleTwentySeven.vector
    Caps.ExampleTwentySeven.defined
      fieldFiveTwoNonzero,
    Caps.ExampleTwentySeven.null]
  unfold Cap.capDenominator
  exact ExplicitField.zero_div _

/-- The displayed rational half turn has half spread one. -/
theorem
  halfTurnExample_halfSpread :
  Rotations.Spread.halfSpread halfTurnExample = 1 := by
  unfold halfTurnExample
  exact Rotations.Spread.halfSpread_halfTurn
    halfTurnAxisExample
    halfTurnAxisExample_nonNull
    rationalTwoNonzero

/-- The identity rotation has spread zero along its canonically recovered direction. -/
theorem identity_canonical_spread
  :
    Rotations.Spread.rotationSpreadAt identity
        (Recovery.canonicalRotationSpreadDirection
          identity
          rationalTwoNonzero)
        (Recovery.canonicalRotationSpreadDirection_nonNull
          identity
          rationalTwoNonzero) = 0 := by
  rw [Recovery.rotationSpreadAt_canonical
    identity
    rationalTwoNonzero]
  unfold Rotations.Spread.rotationSpread
  rw [identity_halfSpread, mul_zero, zero_mul]

/-- The null cap over the five-element field has spread zero along its canonically recovered direction. -/
theorem nullCap_canonical_spread
  :
    Rotations.Spread.rotationSpreadAt nullCap
        (Recovery.canonicalRotationSpreadDirection
          nullCap
          fieldFiveTwoNonzero)
        (Recovery.canonicalRotationSpreadDirection_nonNull
          nullCap
          fieldFiveTwoNonzero) = 0 := by
  rw [Recovery.rotationSpreadAt_canonical
    nullCap
    fieldFiveTwoNonzero]
  unfold Rotations.Spread.rotationSpread
  rw [nullCap_halfSpread]
  decide

/-- The rational half turn has spread zero along its canonically recovered direction. -/
theorem
  halfTurnExample_canonical_spread
  :
    Rotations.Spread.rotationSpreadAt halfTurnExample
        (Recovery.canonicalRotationSpreadDirection
          halfTurnExample
          rationalTwoNonzero)
        (Recovery.canonicalRotationSpreadDirection_nonNull
          halfTurnExample
          rationalTwoNonzero) = 0 := by
  rw [Recovery.rotationSpreadAt_canonical
    halfTurnExample
    rationalTwoNonzero]
  unfold Rotations.Spread.rotationSpread
  rw [halfTurnExample_halfSpread, sub_self, mul_zero]

end CanonicalAxisSpreadExamples
end Purelib.Examples.Geometry.Rotations.RotationAnchors

end
