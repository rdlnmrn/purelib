module

public import Purelib.Geometry.Rotations.Ternary.Lorentz.Orientation
public import Purelib.Algebra.Field.ExplicitOrder.Differences
import Purelib.Geometry.Rotations.Ternary.Lorentz.Cayley
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Causal half-spread ranges of Lorentz rotations

The original recovered vector supplies the axis quadrance. Time direction
is determined by the same cap denominator; its positive and negative
signs give the exact half-spread ranges through explicit differences.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField OrderDifferenceLaw)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {F : Type*} [RayOrderedExplicitField F] (oneNonzero : (1 : F) ≠ 0)

/-- A source cap preserves time direction exactly when its original denominator is positive. -/
theorem cap_time_pos_iff (vector : Vector3 F) (defined : capDenominator oneNonzero vector ≠ 0) :
    0 < (capRotation oneNonzero vector defined).matrix.tt ↔ 0 < capDenominator oneNonzero vector := by
  have normDefined : 1 ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0 := by
    simpa only [one_pow, capDenominator] using defined
  have equivalent := proportionRotation_time_pos_iff oneNonzero 1 vector normDefined
  rw [proportionRotation_one oneNonzero vector defined] at equivalent
  simpa only [one_pow, capDenominator] using equivalent

/-- Every time-preserving source cap has half spread strictly below one. -/
theorem cap_halfSpread_lt_one (law : OrderDifferenceLaw F) (vector : Vector3 F)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : F) ≠ 0)
    (timePositive : 0 < (capRotation oneNonzero vector defined).matrix.tt) :
    rotationHalfSpread (Form.lorentz oneNonzero) (capRotation oneNonzero vector defined) < 1 := by
  apply (law.lt_one_iff _).mpr
  rw [one_sub_halfSpread_cap oneNonzero vector defined twoNonzero, ExplicitField.div_eq_mul_inv, one_mul]
  exact OrderedExplicitField.inv_pos_direct ((cap_time_pos_iff oneNonzero vector defined).mp timePositive)

/-- A time-preserving source cap with timelike vector has half spread strictly between zero and one. -/
theorem cap_halfSpread_timelike (law : OrderDifferenceLaw F) (vector : Vector3 F)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : F) ≠ 0)
    (timePositive : 0 < (capRotation oneNonzero vector defined).matrix.tt)
    (timelike : 0 < (Form.lorentz oneNonzero).quadrance vector) :
    0 < rotationHalfSpread (Form.lorentz oneNonzero) (capRotation oneNonzero vector defined) ∧
      rotationHalfSpread (Form.lorentz oneNonzero) (capRotation oneNonzero vector defined) < 1 := by
  constructor
  · rw [halfSpread_cap oneNonzero vector defined twoNonzero, ExplicitField.div_eq_mul_inv]
    exact OrderedExplicitField.mul_pos_direct timelike
      (OrderedExplicitField.inv_pos_direct ((cap_time_pos_iff oneNonzero vector defined).mp timePositive))
  · exact cap_halfSpread_lt_one oneNonzero law vector defined twoNonzero timePositive

/-- A time-preserving source cap with spacelike vector has negative half spread. -/
theorem cap_halfSpread_spacelike (law : OrderDifferenceLaw F) (vector : Vector3 F)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : F) ≠ 0)
    (timePositive : 0 < (capRotation oneNonzero vector defined).matrix.tt)
    (spacelike : (Form.lorentz oneNonzero).quadrance vector < 0) :
    rotationHalfSpread (Form.lorentz oneNonzero) (capRotation oneNonzero vector defined) < 0 := by
  apply (law.lt_zero_iff _).mpr
  rw [halfSpread_cap oneNonzero vector defined twoNonzero, ExplicitField.div_eq_mul_inv]
  have positive := OrderedExplicitField.mul_pos_direct ((law.lt_zero_iff _).mp spacelike)
    (OrderedExplicitField.inv_pos_direct ((cap_time_pos_iff oneNonzero vector defined).mp timePositive))
  rw [show -((Form.lorentz oneNonzero).quadrance vector * (capDenominator oneNonzero vector)⁻¹) =
    -(Form.lorentz oneNonzero).quadrance vector * (capDenominator oneNonzero vector)⁻¹ by ring1]
  exact positive

/-- A source cap with null vector has half spread zero. -/
theorem cap_halfSpread_null (vector : Vector3 F) (defined : capDenominator oneNonzero vector ≠ 0)
    (twoNonzero : (2 : F) ≠ 0) (null : (Form.lorentz oneNonzero).quadrance vector = 0) :
    rotationHalfSpread (Form.lorentz oneNonzero) (capRotation oneNonzero vector defined) = 0 := by
  rw [halfSpread_cap oneNonzero vector defined twoNonzero, null, ExplicitField.div_eq_mul_inv, zero_mul]

/-- A source cap which fails positive time orientation has half spread above one and spacelike vector.

The finite sign split selects the negative denominator. Its reciprocal
determines the negative unit complement of the half spread, while its
original equation `D=1+Q` determines the negative axis quadrance.
-/
theorem cap_halfSpread_not_timePositive (law : OrderDifferenceLaw F) (vector : Vector3 F)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : F) ≠ 0)
    (notTimePositive : ¬ 0 < (capRotation oneNonzero vector defined).matrix.tt) :
    1 < rotationHalfSpread (Form.lorentz oneNonzero) (capRotation oneNonzero vector defined) ∧
      (Form.lorentz oneNonzero).quadrance vector < 0 := by
  have negativeDenominator : 0 < -(capDenominator oneNonzero vector) := by
    rcases RayOrderedExplicitField.sign_split_direct _ defined with positive | negative
    · exact False.elim (notTimePositive ((cap_time_pos_iff oneNonzero vector defined).mpr positive))
    · exact negative
  constructor
  · apply (law.one_lt_iff _).mpr
    have positiveInverse := OrderedExplicitField.inv_pos_direct negativeDenominator
    rw [ExplicitField.inv_neg] at positiveInverse
    have complement := one_sub_halfSpread_cap oneNonzero vector defined twoNonzero
    rw [ExplicitField.div_eq_mul_inv, one_mul] at complement
    have excess : rotationHalfSpread (Form.lorentz oneNonzero) (capRotation oneNonzero vector defined) - 1 =
        -(capDenominator oneNonzero vector)⁻¹ := by
      calc
        _ = -(1 - rotationHalfSpread (Form.lorentz oneNonzero) (capRotation oneNonzero vector defined)) := by ring1
        _ = _ := congrArg (fun value : F => -value) complement
    rw [excess]
    exact positiveInverse
  · apply (law.lt_zero_iff _).mpr
    have positive := OrderedExplicitField.add_pos_direct OrderedExplicitField.zero_lt_one_direct negativeDenominator
    have equal : 1 + -(capDenominator oneNonzero vector) = -(Form.lorentz oneNonzero).quadrance vector := by
      unfold capDenominator
      ring1
    rw [equal] at positive
    exact positive

/-- A time-preserving original non-half-turn rotation has the causal ranges of its exact recovered axis.

The same retained readback and cap recovery supply all three cases.
Timelike axes give the open unit interval, spacelike axes give negative
half spread, and null axes give zero. The null case includes identity;
the parabolic interpretation additionally requires a nonidentity rotation.
-/
theorem rotation_halfSpread_timePositive_ranges [DecidableEq F] (law : OrderDifferenceLaw F)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : F) ≠ 0)
    (notHalfTurn : rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1)
    (timePositive : 0 < rotation.matrix.tt) :
    let vector := rotationAnchorVector oneNonzero rotation
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
    (0 < (Form.lorentz oneNonzero).quadrance vector →
      0 < rotationHalfSpread (Form.lorentz oneNonzero) rotation ∧
        rotationHalfSpread (Form.lorentz oneNonzero) rotation < 1) ∧
    ((Form.lorentz oneNonzero).quadrance vector < 0 →
      rotationHalfSpread (Form.lorentz oneNonzero) rotation < 0) ∧
    ((Form.lorentz oneNonzero).quadrance vector = 0 →
      rotationHalfSpread (Form.lorentz oneNonzero) rotation = 0) ∧
    rotationHalfSpread (Form.lorentz oneNonzero) rotation < 1 := by
  let vector := rotationAnchorVector oneNonzero rotation
    ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
  let defined := rotationAnchorVector_defined oneNonzero rotation twoNonzero notHalfTurn
  have represents : capRotation oneNonzero vector defined = rotation :=
    cap_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn
  have capTimePositive : 0 < (capRotation oneNonzero vector defined).matrix.tt := by
    rw [represents]
    exact timePositive
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro timelike
    have ranges := cap_halfSpread_timelike oneNonzero law vector defined twoNonzero capTimePositive timelike
    rw [represents] at ranges
    exact ranges
  · intro spacelike
    have negative := cap_halfSpread_spacelike oneNonzero law vector defined twoNonzero capTimePositive spacelike
    rw [represents] at negative
    exact negative
  · intro null
    have zero := cap_halfSpread_null oneNonzero vector defined twoNonzero null
    rw [represents] at zero
    exact zero
  · have below := cap_halfSpread_lt_one oneNonzero law vector defined twoNonzero capTimePositive
    rw [represents] at below
    exact below

/-- An original non-half-turn rotation failing positive time orientation has half spread above one and spacelike axis.

The axis is the original computed vector readback, with its retained
denominator certificate. Its exact cap recovers the same original
rotation, so both inequalities concern that rotation and that axis.
-/
theorem rotation_halfSpread_not_timePositive [DecidableEq F] (law : OrderDifferenceLaw F)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : F) ≠ 0)
    (notHalfTurn : rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1)
    (notTimePositive : ¬ 0 < rotation.matrix.tt) :
    1 < rotationHalfSpread (Form.lorentz oneNonzero) rotation ∧
      (Form.lorentz oneNonzero).quadrance (rotationAnchorVector oneNonzero rotation
        ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)) < 0 := by
  let vector := rotationAnchorVector oneNonzero rotation
    ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
  let defined := rotationAnchorVector_defined oneNonzero rotation twoNonzero notHalfTurn
  have represents : capRotation oneNonzero vector defined = rotation :=
    cap_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn
  have capNotTimePositive : ¬ 0 < (capRotation oneNonzero vector defined).matrix.tt := by
    rw [represents]
    exact notTimePositive
  have ranges := cap_halfSpread_not_timePositive oneNonzero law vector defined twoNonzero capNotTimePositive
  rw [represents] at ranges
  exact ranges

end Purelib.Geometry.Rotations.Ternary.Lorentz
