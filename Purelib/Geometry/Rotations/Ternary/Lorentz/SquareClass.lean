module

public import Purelib.Geometry.Rotations.Ternary.Lorentz.Projective
public import Purelib.Geometry.Rotations.Ternary.Clifford.SquareClass
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Lorentz
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Quadrance classes of source Lorentz rotations

The original projective Clifford correspondence supplies the invariant.
Source dihedron norms and their explicit witnesses connect that invariant
to the paper's coordinates without selecting quotient representatives.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.SquareClass.Basic (SquareClassRepresentative)
open Purelib.Algebra.Clifford.Lorentz
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- The source proportion norm represents the original rotation's quadrance class.

The actual non-null Clifford representative retains scalar `x` and vector
`-v`. Its exact norm is `x² + Q(v)`, and the projective correspondence
supplies the nonzero square factor comparing it to the cached preimage.
-/
theorem quadranceClass_proportionRotation [DecidableEq K] (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    ((proportionRotation oneNonzero scalar vector defined).quadranceClass twoNonzero).Equivalent
      ⟨scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector, defined⟩ := by
  have classes := Form.SpecialOrthogonal.quadranceClass_action
    (Matrix.nonNullCoordinates oneNonzero scalar vector defined) twoNonzero
  rcases classes with ⟨factor, factorNonzero, equal⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector =
    factor ^ 2 * ((proportionRotation oneNonzero scalar vector defined).quadranceClass twoNonzero).value
  rw [← Matrix.norm_coordinates_quadrance oneNonzero scalar vector]
  exact equal

/-- A source cap's original denominator represents its quadrance class. -/
theorem quadranceClass_cap [DecidableEq K] (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    ((capRotation oneNonzero vector defined).quadranceClass twoNonzero).Equivalent
      ⟨capDenominator oneNonzero vector, defined⟩ := by
  have normDefined : 1 ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0 := by
    simpa only [one_pow, capDenominator] using defined
  have classes := quadranceClass_proportionRotation oneNonzero 1 vector normDefined twoNonzero
  rw [proportionRotation_one oneNonzero vector defined] at classes
  rcases classes with ⟨factor, factorNonzero, equal⟩
  refine ⟨factor, factorNonzero, ?_⟩
  exact (show capDenominator oneNonzero vector = 1 ^ 2 +
    (Form.lorentz oneNonzero).quadrance vector by unfold capDenominator; ring1).trans equal

/-- A source half turn's original axis quadrance represents its quadrance class. -/
theorem quadranceClass_halfTurn [DecidableEq K] (axis : Vector3 K)
    (nonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (((Form.lorentz oneNonzero).halfTurnRotation axis nonNull).quadranceClass twoNonzero).Equivalent
      ⟨(Form.lorentz oneNonzero).quadrance axis, nonNull⟩ := by
  have normDefined : 0 ^ 2 + (Form.lorentz oneNonzero).quadrance axis ≠ 0 := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_add] using nonNull
  have classes := quadranceClass_proportionRotation oneNonzero 0 axis normDefined twoNonzero
  rw [proportionRotation_zero oneNonzero axis nonNull] at classes
  rcases classes with ⟨factor, factorNonzero, equal⟩
  refine ⟨factor, factorNonzero, ?_⟩
  exact (show (Form.lorentz oneNonzero).quadrance axis =
    0 ^ 2 + (Form.lorentz oneNonzero).quadrance axis by ring1).trans equal

/-- One minus the half spread represents every non-half-turn source rotation's quadrance class.

The retained computed cap supplies its exact denominator. Its inverse
differs from that denominator by the square of the same nonzero inverse,
giving the requested square-class witness in the original rotation owner.
-/
theorem quadranceClass_one_sub_halfSpread [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (nonzero : 1 - Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (Form.lorentz oneNonzero) rotation ≠ 0) :
    (rotation.quadranceClass twoNonzero).Equivalent
      ⟨1 - Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation, nonzero⟩ := by
  have notHalfTurn : Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (Form.lorentz oneNonzero) rotation ≠ 1 := by
    intro halfSpreadOne
    apply nonzero
    rw [halfSpreadOne]
    ring1
  let vector := rotationAnchorVector oneNonzero rotation
    ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
  have recovery := rotationAnchorVector_cap_recovery oneNonzero rotation twoNonzero notHalfTurn
  let defined : capDenominator oneNonzero vector ≠ 0 := recovery.1
  have represents : capRotation oneNonzero vector defined = rotation := recovery.2 defined
  have classes := quadranceClass_cap oneNonzero vector defined twoNonzero
  rw [represents] at classes
  apply SquareClassRepresentative.equivalent_trans classes
  refine ⟨(capDenominator oneNonzero vector)⁻¹, ExplicitField.inv_ne_zero defined, ?_⟩
  change 1 - Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation =
    (capDenominator oneNonzero vector)⁻¹ ^ 2 * capDenominator oneNonzero vector
  rw [← represents, one_sub_halfSpread_cap oneNonzero vector defined twoNonzero,
    ExplicitField.div_eq_mul_inv, one_mul]
  have cancellation := ExplicitField.mul_inv_cancel (capDenominator oneNonzero vector) defined
  calc
    _ = (capDenominator oneNonzero vector)⁻¹ *
        (capDenominator oneNonzero vector * (capDenominator oneNonzero vector)⁻¹) := by
      rw [cancellation, mul_one]
    _ = _ := by ring1

/-- An explicit source dihedron with the prescribed reduced norm.

Its time and second spatial coordinates vanish. The scalar and first
spatial coordinate are the half-sum and half-difference of the requested
norm and the unit, respectively.
-/
@[expose] def normWitness (value : K) : (Form.lorentz oneNonzero).EvenClifford :=
  Matrix.coordinates oneNonzero ((value + 1) / 2) ⟨0, (value - 1) / 2, 0⟩

/-- The retained source half-sum and half-difference dihedron has exactly the requested norm. -/
theorem norm_normWitness (value : K) (twoNonzero : (2 : K) ≠ 0) :
    EvenClifford.norm (normWitness oneNonzero value) = value := by
  unfold normWitness
  rw [Matrix.norm_coordinates_quadrance, Form.quadrance_lorentz]
  dsimp only
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    _ = (2 * (2 : K)⁻¹) ^ 2 * value := by ring1
    _ = value := by rw [ExplicitField.mul_inv_cancel _ twoNonzero, one_pow, one_mul]

/-- Retain the prescribed nonzero source norm in the original non-null Clifford owner. -/
@[expose] def nonNullNormWitness (value : K) (nonzero : value ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (Form.lorentz oneNonzero).NonNullEvenClifford where
  toEvenClifford := normWitness oneNonzero value
  normNonzero := by rw [norm_normWitness oneNonzero value twoNonzero]; exact nonzero

/-- Every nonzero scalar square class is represented by an executable source Lorentz rotation.

The preimage is the original Clifford action of the retained norm witness.
Its exact norm equals the requested representative, so the final class
comparison keeps that request and an explicit nonzero square factor.
-/
theorem quadranceClass_surjective [DecidableEq K] (target : SquareClassRepresentative K)
    (twoNonzero : (2 : K) ≠ 0) :
    ∃ rotation : (Form.lorentz oneNonzero).SpecialOrthogonal,
      (rotation.quadranceClass twoNonzero).Equivalent target := by
  let value := nonNullNormWitness oneNonzero target.value target.nonzero twoNonzero
  refine ⟨NonNullEvenClifford.actionRotation value, ?_⟩
  have classes := Form.SpecialOrthogonal.quadranceClass_action value twoNonzero
  rcases classes with ⟨factor, factorNonzero, equal⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change EvenClifford.norm (normWitness oneNonzero target.value) = _ at equal
  rw [norm_normWitness oneNonzero target.value twoNonzero] at equal
  exact equal

end Purelib.Geometry.Rotations.Ternary.Lorentz
