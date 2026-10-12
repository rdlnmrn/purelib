module

import formalisations.MinkowskiRotations.MinkowskiRotations
import Purelib.Tactic.Ring

/-!
# Source-coordinate consumer checks for the Minkowski publication

Only the promised publication facade supplies the mathematical API. The
introductory boost checks the paper's signs in both matrix dimensions.
-/

namespace Test.Geometry.Rotations.MinkowskiPublication

open Purelib.Algebra
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Clifford.Lorentz
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Quadratic.Ternary
open Purelib.Geometry
open Purelib.Geometry.Projective.Line (Proj)
open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm
open Purelib.Examples.Geometry.Quadratic
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3
open Purelib.Polynomial.RecursiveDense.Rational
open Purelib.Polynomial.Quadratic

/-- The rational field has nonzero unit. -/
private theorem oneNonzero : (1 : Rational) ≠ 0 := by decide

/-- The displayed introductory dihedron has norm eight. -/
private theorem introductory_norm :
    EvenClifford.norm (Matrix.coordinates oneNonzero 3 ⟨0, 0, 1⟩) = 8 := by decide

/-- The introductory dihedron gives the displayed two-by-two boost matrix. -/
private theorem introductory_matrix :
    Matrix.toMatrix oneNonzero (Matrix.coordinates oneNonzero 3 ⟨0, 0, 1⟩) =
      (⟨4, 0, 0, 2⟩ : Matrix2 Rational) := by decide

/-- The retained norm certificate makes the introductory dihedron non-null. -/
private def introductoryValue : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford where
  toEvenClifford := Matrix.coordinates oneNonzero 3 ⟨0, 0, 1⟩
  normNonzero := by
    rewrite [introductory_norm]
    decide

/-- The original Clifford action gives the paper's three-by-three introductory boost. -/
private theorem introductory_action :
    NonNullEvenClifford.actionMatrix introductoryValue =
      (⟨5 / 4, 3 / 4, 0, 3 / 4, 5 / 4, 0, 0, 0, 1⟩ : Matrix3 Rational) := by decide

/-- A facade consumer can recover an arbitrary Lorentz anchor and its original vector. -/
private theorem anchor_bijection {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (vector : Vector3 K) (matrix : Matrix3 K) (skew : Lorentz.IsAnchor oneNonzero matrix) :
    Lorentz.anchorVector (Lorentz.anchor oneNonzero vector) = vector ∧
      Lorentz.anchor oneNonzero (Lorentz.anchorVector matrix) = matrix :=
  ⟨Lorentz.anchorVector_anchor oneNonzero vector,
    Lorentz.anchor_anchorVector oneNonzero matrix twoNonzero skew⟩

/-- The facade supplies the signed triple product in the paper's literal convention. -/
private theorem signed_triple_product {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (first second third : Vector3 K) :
    (TernaryForm.lorentz oneNonzero).bilinear (Lorentz.cross oneNonzero first second) third =
      -Vector3.determinant first second third :=
  Lorentz.scalar_triple_product oneNonzero first second third

/-- The facade supplies spread rescaling using the original quadratic-form owner. -/
private theorem spread_rescaling {K : Type*} [ExplicitField K]
    (form : TernaryForm K) (scalar : K) (left right : Vector3 K)
    (scalarNonzero : scalar ≠ 0) (leftNonNull : form.quadrance left ≠ 0)
    (rightNonNull : form.quadrance right ≠ 0) :
    form.spread left (Vector3.scale scalar right) leftNonNull
        (form.quadrance_scale_ne_zero scalar right scalarNonzero rightNonNull) =
      form.spread left right leftNonNull rightNonNull :=
  form.spread_scale_right scalar left right scalarNonzero leftNonNull rightNonNull

/-- The exact rational spread outside the unit interval is public through the facade. -/
private theorem rational_spread_example :
    1 < Ternary.Lorentz.form.spread Ternary.Lorentz.first Ternary.Lorentz.second
      Ternary.Lorentz.firstNonNull Ternary.Lorentz.secondNonNull :=
  Ternary.Lorentz.spread_first_second_gt_one

/-- The public zero-spread example retains genuinely distinct rational directions. -/
private theorem rational_zero_spread_directions (scalar : Rational) :
    Vector3.scale scalar Ternary.Lorentz.zeroSpreadFirst ≠ Ternary.Lorentz.zeroSpreadSecond :=
  Ternary.Lorentz.zero_spread_directions_distinct scalar

/-- The rational anchor's entire characteristic polynomial is public through the facade. -/
private theorem rational_anchor_characteristic (X : Rational) :
    Matrix3.characteristicValue (Lorentz.anchor Ternary.Lorentz.oneNonzero Ternary.Lorentz.first) X =
      X ^ 3 - 12 * X :=
  Ternary.Lorentz.anchor_characteristic X

/-- Rational polynomial vanishing is reachable with finite polynomial and point owners. -/
private theorem polynomial_vanishing {arity : Nat} (left right : Basic.Expression arity)
    (rightNonzero : right.isZero = false)
    (vanishes : ∀ point : Basic.Point arity, right.eval point ≠ 0 → left.eval point = 0) :
    left.isZero = true :=
  Avoidance.isZero_of_vanishes_where_second_nonzero left right rightNonzero vanishes

/-- The original integral polynomial identity transfers from its rational generic locus to every supplied field. -/
private theorem integral_identity_transfer {arity : Nat} (polynomial locus : Basic.Expression arity)
    (integral : polynomial.Integral) (locusNonzero : locus.isZero = false)
    (vanishes : ∀ point : Basic.Point arity, locus.eval point ≠ 0 → polynomial.eval point = 0)
    {K : Type*} [ExplicitField K] (point : Basic.PointOver K arity) :
    polynomial.evalIntegral integral point = 0 :=
  polynomial.transfer_integral_identity locus integral locusNonzero vanishes point

/-- The certified integer evaluator preserves the original rational polynomial and its exact coordinate tuple. -/
private theorem integral_rational_agreement {arity : Nat} (polynomial : Basic.Expression arity)
    (integral : polynomial.Integral) (point : Basic.PointOver Rational arity) :
    polynomial.evalIntegral integral point = polynomial.eval point.toRationalPoint :=
  polynomial.evalIntegral_rational integral point

/-- Lorentz reflection fixed vectors are characterized through the facade in both directions. -/
private theorem reflection_fixed_vectors {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (normal vector : Vector3 K)
    (nonNull : (TernaryForm.lorentz oneNonzero).quadrance normal ≠ 0) :
    Matrix3.rowMul vector ((TernaryForm.lorentz oneNonzero).reflection normal nonNull) = vector ↔
      (TernaryForm.lorentz oneNonzero).Perpendicular vector normal :=
  (TernaryForm.lorentz oneNonzero).rowMul_reflection_eq_self_iff_perpendicular normal nonNull twoNonzero vector

/-- The Lorentz adjoint of a reflection is publicly its original reflection. -/
private theorem reflection_adjoint {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (normal : Vector3 K)
    (nonNull : (TernaryForm.lorentz oneNonzero).quadrance normal ≠ 0) :
    Lorentz.adjoint oneNonzero ((TernaryForm.lorentz oneNonzero).reflection normal nonNull) =
      (TernaryForm.lorentz oneNonzero).reflection normal nonNull :=
  Lorentz.adjoint_reflection oneNonzero normal nonNull

/-- A facade consumer can use the full half-turn uniqueness theorem on Lorentz matrices. -/
private theorem halfTurn_uniqueness {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (axis : Vector3 K)
    (nonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0) (matrix : Matrix3 K)
    (fixesAxis : Matrix3.rowMul axis matrix = axis)
    (negatesPerpendicular : ∀ vector : Vector3 K,
      (TernaryForm.lorentz oneNonzero).Perpendicular vector axis →
        Matrix3.rowMul vector matrix = Vector3.neg vector) :
    matrix = (TernaryForm.lorentz oneNonzero).halfTurn axis nonNull :=
  (TernaryForm.lorentz oneNonzero).halfTurn_unique axis nonNull matrix fixesAxis negatesPerpendicular

/-- The displayed rational reflection product is available through the promised facade. -/
private theorem rational_reflection_product :
    Matrix3.mul
        (Ternary.Lorentz.form.reflection Ternary.Lorentz.first Ternary.Lorentz.firstNonNull)
        (Ternary.Lorentz.form.reflection Ternary.Lorentz.second Ternary.Lorentz.secondNonNull) =
      Matrix3.scale (1 / 6) ⟨-19, 15, -10, -10, 6, -10, 15, -15, 6⟩ :=
  Ternary.Lorentz.reflection_product_matrix

/-- An independent pair of Lorentz normals supplies a nonzero fixed cross direction. -/
private theorem reflection_product_axis_nonzero {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (first second : Vector3 K)
    (independent : Vector3.Independent first second) :
    Lorentz.cross oneNonzero first second ≠ Vector3.zero :=
  Lorentz.cross_ne_zero_of_independent oneNonzero first second independent

/-- The scalar Clifford branch retains the supplied nonzero fallback direction. -/
private theorem fixed_vector_identity_readback :
    (NonNullEvenClifford.fixedVector (NonNullEvenClifford.identity (TernaryForm.lorentz oneNonzero))
      (⟨1, 0, 0⟩ : Vector3 Rational) (by decide)).1 = ⟨1, 0, 0⟩ := by decide

/-- The introductory boost retains its nonzero Clifford vector as the fixed direction. -/
private theorem fixed_vector_introductory_readback :
    (NonNullEvenClifford.fixedVector introductoryValue
      (⟨1, 0, 0⟩ : Vector3 Rational) (by decide)).1 = ⟨0, 0, -1⟩ := by decide

/-- A facade consumer can construct a nonzero fixed direction for every Lorentz rotation. -/
private def fixed_direction {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) :
    Σ' vector : Vector3 K, vector ≠ Vector3.zero ∧ Matrix3.rowMul vector rotation.matrix = vector :=
  (TernaryForm.lorentz oneNonzero).fixedDirection rotation twoNonzero

/-- The total fixed-direction builder retains the time axis for the identity Lorentz rotation. -/
private theorem fixed_direction_identity_readback :
    ((TernaryForm.lorentz oneNonzero).fixedDirection
      (SpecialOrthogonal.identity (TernaryForm.lorentz oneNonzero)) (by decide)).1 =
      (⟨1, 0, 0⟩ : Vector3 Rational) := by decide

/-- The revised facade supplies the cap's actual resolvent inverse and quadratic reduction. -/
private theorem cap_formulas {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (vector : Vector3 K)
    (defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero vector ≠ 0) :
    Rotations.Ternary.Lorentz.cap oneNonzero vector defined =
      Matrix3.mul (Matrix3.add Matrix3.identity (Lorentz.anchor oneNonzero vector))
        (Rotations.Ternary.Lorentz.anchorResolventInverse oneNonzero vector defined) :=
  Rotations.Ternary.Lorentz.cap_eq_cayley oneNonzero vector defined

/-- The revised facade excludes every nonzero minus-one cap eigenvector. -/
private theorem cap_negative_eigenvector {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (axis vector : Vector3 K)
    (defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero axis ≠ 0)
    (negativeEigen : Matrix3.rowMul vector (Rotations.Ternary.Lorentz.cap oneNonzero axis defined) =
      Vector3.neg vector) : vector = Vector3.zero :=
  Rotations.Ternary.Lorentz.rowMul_cap_eq_neg_implies_zero oneNonzero axis defined twoNonzero vector negativeEigen

/-- Every original null-anchor cap has cube-zero difference from identity through the facade. -/
private theorem null_cap_cube {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (axis : Vector3 K)
    (defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero axis ≠ 0)
    (null : (TernaryForm.lorentz oneNonzero).quadrance axis = 0) :
    let difference := Matrix3.sub (Rotations.Ternary.Lorentz.cap oneNonzero axis defined) Matrix3.identity
    Matrix3.mul (Matrix3.mul difference difference) difference = Matrix3.zero :=
  Rotations.Ternary.Lorentz.cap_sub_identity_cube_of_null oneNonzero axis defined null

/-- The boost example retains its exact half spread and time-axis velocity ratio through the facade. -/
private theorem boost_readback :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread Ternary.Lorentz.form
      (Rotations.Ternary.Lorentz.capRotation Ternary.Lorentz.oneNonzero
        Ternary.Lorentz.boostAxis Ternary.Lorentz.boostAxisDefined) = -1 / 8 :=
  Ternary.Lorentz.boost_halfSpread_velocity.1

/-- The shared half-turn converse returns a non-null axis of the original Lorentz rotation. -/
private def half_turn_converse {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (halfSpreadOne : Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (TernaryForm.lorentz oneNonzero) rotation = 1) :
    Σ' axis : Vector3 K, Σ' nonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0,
      (TernaryForm.lorentz oneNonzero).halfTurnRotation axis nonNull = rotation :=
  Rotations.Ternary.Cayley.TernaryForm.halfTurnWitness
    (TernaryForm.lorentz oneNonzero) rotation twoNonzero halfSpreadOne

/-- Every nonzero null vector has executable homogeneous parameters through the publication facade. -/
private def null_parameters {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K)
    (null : (TernaryForm.lorentz oneNonzero).IsNull vector) (nonzero : vector ≠ Vector3.zero) :
    SplitNullConic.MinkowskiClifford.NullParameterWitness (Lorentz.toSplit vector) :=
  Lorentz.nullParameterWitness oneNonzero twoNonzero vector null nonzero

/-- The original witness scale represents the time-first input vector. -/
private theorem null_parameters_spec {K : Type*} [ExplicitField K] (vector : Vector3 K)
    (witness : SplitNullConic.MinkowskiClifford.NullParameterWitness (Lorentz.toSplit vector)) :
    Lorentz.nullParameter witness.first witness.second = Vector3.scale witness.factor vector :=
  Lorentz.nullParameterWitness_spec vector witness

/-- Equivalent homogeneous parameters describe exactly the same null line. -/
private theorem null_parameters_unique {K : Type*} [ExplicitField K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) (left right : Proj K)
    (leftNonzero : left.Nonzero) (rightNonzero : right.Nonzero) :
    left.Equivalent right ↔ ∃ factor : K, factor ≠ 0 ∧
      Lorentz.nullParameter left.p left.q = Vector3.scale factor (Lorentz.nullParameter right.p right.q) :=
  Lorentz.nullParameter_sameLine_iff twoNonzero left right leftNonzero rightNonzero

/-- Both projective parameter charts give the displayed time-first null directions. -/
private theorem null_parameter_charts :
    Lorentz.nullParameter (1 : Rational) 0 = ⟨1, 1, 0⟩ ∧
      Lorentz.nullParameter (0 : Rational) 1 = ⟨1, -1, 0⟩ := by
  constructor <;> decide

/-- The executable builder retains the expected parameters and scales in both coordinate charts. -/
private theorem null_parameter_builder_charts :
    let first := Lorentz.nullParameterWitness oneNonzero (by decide : (2 : Rational) ≠ 0)
      (⟨1, 1, 0⟩ : Vector3 Rational) (TernaryForm.lorentz_null_direction oneNonzero) (by decide)
    let second := Lorentz.nullParameterWitness oneNonzero (by decide : (2 : Rational) ≠ 0)
      (⟨1, -1, 0⟩ : Vector3 Rational)
      (by change (TernaryForm.lorentz oneNonzero).quadrance _ = 0; rw [TernaryForm.quadrance_lorentz]; decide)
      (by decide)
    first.first = 2 ∧ first.second = 0 ∧ first.factor = 4 ∧
      second.first = 0 ∧ second.second = -1 ∧ second.factor = 1 := by
  decide

/-- A rational nonzero null vector has a nonzero time coordinate through the facade. -/
private theorem null_time_nonzero (vector : Vector3 Rational)
    (null : (TernaryForm.lorentz oneNonzero).IsNull vector) (nonzero : vector ≠ Vector3.zero) :
    vector.t ≠ 0 := Lorentz.rational_null_time_nonzero oneNonzero vector null nonzero

/-- Every scalar quadrance has an executable Lorentz vector through the facade. -/
private def quadrance_witness {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (value : K) :
    Σ' vector : Vector3 K, (TernaryForm.lorentz oneNonzero).quadrance vector = value :=
  Lorentz.quadranceWitness oneNonzero twoNonzero value

/-- Every non-unit half spread has an executable cap and retained denominator certificate. -/
private def cap_half_spread_witness {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (value : K) (notOne : value ≠ 1) :
    Σ' vector : Vector3 K, Σ' defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero vector ≠ 0,
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero)
        (Rotations.Ternary.Lorentz.capRotation oneNonzero vector defined) = value :=
  Rotations.Ternary.Lorentz.capHalfSpreadWitness oneNonzero twoNonzero value notOne

/-- Every half spread has an executable rotation of the original Lorentz form. -/
private def half_spread_witness {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (value : K) :
    Σ' rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal,
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation = value :=
  Rotations.Ternary.Lorentz.halfSpreadWitness oneNonzero twoNonzero value

/-- The executable cap and half-turn branches retain their expected rational vector, denominator and matrix. -/
private theorem half_spread_builder_branches :
    let cap := Rotations.Ternary.Lorentz.capHalfSpreadWitness oneNonzero
      (by decide : (2 : Rational) ≠ 0) 2 (by decide)
    let half := Rotations.Ternary.Lorentz.halfSpreadWitness oneNonzero
      (by decide : (2 : Rational) ≠ 0) 1
    cap.1 = ⟨-1 / 2, -3 / 2, 0⟩ ∧
      Rotations.Ternary.Lorentz.capDenominator oneNonzero cap.1 = -1 ∧
      half.1.matrix = ⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩ := by
  decide

/-- A non-null Lorentz cap axis has a retained non-null measurement with the prescribed geometric spread. -/
private def cap_spread_witness {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (axis : Vector3 K)
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0)
    (defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero axis ≠ 0) :
    Σ' witness : (TernaryForm.lorentz oneNonzero).PerpendicularNonNullVectorWitness axis,
      (TernaryForm.lorentz oneNonzero).spread witness.value
        (TernaryForm.Isometry.act (Rotations.Ternary.Lorentz.capRotation oneNonzero axis defined).toIsometry
          witness.value)
        witness.nonNull
        ((Rotations.Ternary.Lorentz.capRotation oneNonzero axis defined).toIsometry.quadrance_act_ne_zero
          witness.value witness.nonNull) =
          Rotations.Ternary.Cayley.TernaryForm.rotationSpread (TernaryForm.lorentz oneNonzero)
            (Rotations.Ternary.Lorentz.capRotation oneNonzero axis defined) :=
  Rotations.Ternary.Lorentz.capSpreadWitness oneNonzero axis axisNonNull defined twoNonzero

/-- A Lorentz half turn has a retained non-null perpendicular geometric measurement. -/
private def half_turn_spread_witness {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (axis : Vector3 K)
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0) :
    Σ' witness : (TernaryForm.lorentz oneNonzero).PerpendicularNonNullVectorWitness axis,
      (TernaryForm.lorentz oneNonzero).spread witness.value
        (TernaryForm.Isometry.act
          ((TernaryForm.lorentz oneNonzero).halfTurnRotation axis axisNonNull).toIsometry witness.value) witness.nonNull
        (((TernaryForm.lorentz oneNonzero).halfTurnRotation axis axisNonNull).toIsometry.quadrance_act_ne_zero
          witness.value witness.nonNull) =
          Rotations.Ternary.Cayley.TernaryForm.rotationSpread (TernaryForm.lorentz oneNonzero)
            ((TernaryForm.lorentz oneNonzero).halfTurnRotation axis axisNonNull) :=
  Rotations.Ternary.Cayley.TernaryForm.halfTurnSpreadWitness
    (TernaryForm.lorentz oneNonzero) axis axisNonNull twoNonzero

/-- The displayed spacelike cap's geometric and trace spread measurements are both minus eight. -/
private theorem cap_geometric_spread :
    let rotation := Rotations.Ternary.Lorentz.capRotation Ternary.Lorentz.oneNonzero
      Ternary.Lorentz.capAxis Ternary.Lorentz.capAxisDefined
    let vector := Ternary.Lorentz.capPerpendicular
    Ternary.Lorentz.form.spread vector (TernaryForm.Isometry.act rotation.toIsometry vector)
        Ternary.Lorentz.capPerpendicularNonNull
        (rotation.toIsometry.quadrance_act_ne_zero vector Ternary.Lorentz.capPerpendicularNonNull) = -8 ∧
      Rotations.Ternary.Cayley.TernaryForm.rotationSpread Ternary.Lorentz.form rotation = -8 :=
  Ternary.Lorentz.cap_geometric_spread

/-- The Lorentz spread-of-normals law uses the original form-indexed reflection product. -/
private theorem normals_half_spread {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (first second : Vector3 K)
    (firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (TernaryForm.lorentz oneNonzero).quadrance second ≠ 0) :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero)
        ((TernaryForm.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull) =
      (TernaryForm.lorentz oneNonzero).spread first second firstNonNull secondNonNull :=
  Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread_reflectionProduct
    (TernaryForm.lorentz oneNonzero) first second firstNonNull secondNonNull twoNonzero

/-- The revised Lorentz normals example retains the exact trace and both spread values. -/
private theorem normals_example :
    Ternary.Lorentz.form.spread Ternary.Lorentz.first Ternary.Lorentz.second
        Ternary.Lorentz.firstNonNull Ternary.Lorentz.secondNonNull = 25 / 24 ∧
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread Ternary.Lorentz.form
        (Ternary.Lorentz.form.reflectionProductRotation Ternary.Lorentz.first Ternary.Lorentz.second
          Ternary.Lorentz.firstNonNull Ternary.Lorentz.secondNonNull) = 25 / 24 ∧
      Matrix3.trace (Matrix3.mul (Ternary.Lorentz.form.reflection Ternary.Lorentz.first Ternary.Lorentz.firstNonNull)
        (Ternary.Lorentz.form.reflection Ternary.Lorentz.second Ternary.Lorentz.secondNonNull)) = -7 / 6 :=
  ⟨Ternary.Lorentz.spread_first_second, Ternary.Lorentz.reflection_product_halfSpread,
    Ternary.Lorentz.reflection_product_trace⟩

/-- The literal Lorentz anchor domain is exactly the complement of half spread one. -/
private theorem anchor_domain {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) :
    Matrix3.determinant (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0 ↔
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation ≠ 1 :=
  rotation.determinant_identity_add_ne_zero_iff twoNonzero

/-- The Lorentz anchor is recovered from the original retained matrix and inverse with the literal Cayley formula. -/
private theorem anchor_inverse_formula {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (notHalfTurn : Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (TernaryForm.lorentz oneNonzero) rotation ≠ 1) :
    let defined := (rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn
    let determinantNonzero := (rotation.determinant_identity_add_ne_zero_iff twoNonzero).mpr notHalfTurn
    rotation.anchor defined = Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
      (Matrix3.inverse (Matrix3.add Matrix3.identity rotation.matrix) determinantNonzero) :=
  rotation.anchor_eq_inverseFormula _ _

/-- The cap anchor recovers the paper's original positive Lorentz vector convention. -/
private theorem anchor_cap {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (axis : Vector3 K)
    (defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero axis ≠ 0) :
    let rotation := Rotations.Ternary.Lorentz.capRotation oneNonzero axis defined
    rotation.anchor ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr
      (Rotations.Ternary.Lorentz.halfSpread_cap_ne_one oneNonzero axis defined twoNonzero)) =
        Lorentz.anchor oneNonzero axis :=
  TernaryForm.SpecialOrthogonal.anchor_capRotation (Vector3.neg axis)
    (by rw [Rotations.Ternary.Lorentz.cayleyDenominator_neg]; exact defined) twoNonzero

/-- The original Lorentz vector readback reconstructs its matrix, cap, fixed vector and half twist. -/
private theorem anchor_vector_contract {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (notHalfTurn : Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (TernaryForm.lorentz oneNonzero) rotation ≠ 1) :
    let defined := (rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn
    let vector := Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation defined
    Lorentz.anchor oneNonzero vector = rotation.anchor defined ∧
      Rotations.Ternary.Lorentz.capRotation oneNonzero vector
          (Rotations.Ternary.Lorentz.rotationAnchorVector_defined oneNonzero rotation twoNonzero notHalfTurn) =
        rotation ∧
      Matrix3.rowMul vector rotation.matrix = vector ∧
      (TernaryForm.lorentz oneNonzero).quadrance vector =
        Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation /
          (1 - Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation) :=
  ⟨Rotations.Ternary.Lorentz.anchor_rotationAnchorVector oneNonzero rotation _ twoNonzero,
    Rotations.Ternary.Lorentz.cap_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn,
    Rotations.Ternary.Lorentz.rowMul_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn,
    Rotations.Ternary.Lorentz.quadrance_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn⟩

/-- The matrix anchor determines a unique original Lorentz vector. -/
private theorem anchor_vector_unique {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) (defined : rotation.anchorDenominator ≠ 0)
    (vector : Vector3 K) (represents : Lorentz.anchor oneNonzero vector = rotation.anchor defined) :
    vector = Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation defined :=
  Rotations.Ternary.Lorentz.rotationAnchorVector_unique oneNonzero rotation defined vector represents

/-- The Lorentz anchor is two over one plus trace times the literal adjoint-antisymmetric part. -/
private theorem anchor_adjoint_formula {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) (defined : rotation.anchorDenominator ≠ 0) :
    rotation.anchor defined = Matrix3.scale (2 / (1 + Matrix3.trace rotation.matrix))
      (Matrix3.scale (1 / 2) (Matrix3.sub rotation.matrix (Lorentz.adjoint oneNonzero rotation.matrix))) :=
  Rotations.Ternary.Lorentz.rotationAnchor_eq_adjointFormula oneNonzero rotation defined twoNonzero

/-- The spacelike worked example retains both displayed matrices, its read-back vector and half twist. -/
private theorem anchor_example :
    let rotation := Rotations.Ternary.Lorentz.capRotation Ternary.Lorentz.oneNonzero
      Ternary.Lorentz.capAxis Ternary.Lorentz.capAxisDefined
    let defined := Ternary.Lorentz.capRotationAnchorDefined
    let vector := Rotations.Ternary.Lorentz.rotationAnchorVector Ternary.Lorentz.oneNonzero rotation defined
    rotation.anchorDenominator = -4 ∧ 2 / rotation.anchorDenominator = -1 / 2 ∧
      rotation.antisymmetricPart Ternary.Lorentz.twoNonzero = ⟨0, -2, 2, -2, 0, 0, 2, 0, 0⟩ ∧
      rotation.anchor defined = Lorentz.anchor Ternary.Lorentz.oneNonzero Ternary.Lorentz.capAxis ∧
      rotation.anchor defined = ⟨0, 1, -1, 1, 0, 0, -1, 0, 0⟩ ∧
      vector = Ternary.Lorentz.capAxis ∧ Ternary.Lorentz.form.quadrance vector = -2 :=
  ⟨Ternary.Lorentz.cap_rotation_anchor_denominator.1, Ternary.Lorentz.cap_rotation_anchor_denominator.2,
    Ternary.Lorentz.cap_adjoint_antisymmetric, Ternary.Lorentz.cap_rotation_anchor_matrix.1,
    Ternary.Lorentz.cap_rotation_anchor_matrix.2, Ternary.Lorentz.cap_rotation_anchor_vector,
    Ternary.Lorentz.cap_rotation_anchor_values.1⟩

/-- The original Lorentz reflection-product anchor satisfies both literal matrix formulas and its vector readback. -/
private theorem reflection_product_anchor {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (first second : Vector3 K)
    (firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (TernaryForm.lorentz oneNonzero).quadrance second ≠ 0)
    (pairingNonzero : (TernaryForm.lorentz oneNonzero).bilinear first second ≠ 0) :
    let form := TernaryForm.lorentz oneNonzero
    let rotation := form.reflectionProductRotation first second firstNonNull secondNonNull
    let defined := form.reflectionProduct_anchorDefined
      first second firstNonNull secondNonNull pairingNonzero twoNonzero
    let vector := Vector3.scale (form.bilinear first second)⁻¹ (Lorentz.cross oneNonzero first second)
    rotation.anchor defined = Lorentz.anchor oneNonzero vector ∧
      rotation.anchor defined = Matrix3.scale (form.bilinear first second)⁻¹
        (Matrix3.sub (Matrix3.outer (form.dual first) second) (Matrix3.outer (form.dual second) first)) ∧
      Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation defined = vector ∧
      form.quadrance vector = form.spread first second firstNonNull secondNonNull /
        (1 - form.spread first second firstNonNull secondNonNull) :=
  ⟨Rotations.Ternary.Lorentz.rotationAnchor_reflectionProduct
      oneNonzero first second firstNonNull secondNonNull pairingNonzero twoNonzero,
    Rotations.Ternary.Lorentz.rotationAnchor_reflectionProduct_outerFormula
      oneNonzero first second firstNonNull secondNonNull pairingNonzero twoNonzero,
    Rotations.Ternary.Lorentz.rotationAnchorVector_reflectionProduct
      oneNonzero first second firstNonNull secondNonNull pairingNonzero twoNonzero,
    Rotations.Ternary.Lorentz.quadrance_reflectionProductAnchor
      oneNonzero first second firstNonNull secondNonNull pairingNonzero⟩

/-- Independent nonzero rescaling of Lorentz mirror normals preserves the original product rotation. -/
private theorem reflection_product_lines {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (leftScale rightScale : K) (first second : Vector3 K)
    (leftNonzero : leftScale ≠ 0) (rightNonzero : rightScale ≠ 0)
    (firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (TernaryForm.lorentz oneNonzero).quadrance second ≠ 0) :
    let form := TernaryForm.lorentz oneNonzero
    form.reflectionProductRotation (Vector3.scale leftScale first) (Vector3.scale rightScale second)
        (form.quadrance_scale_ne_zero leftScale first leftNonzero firstNonNull)
        (form.quadrance_scale_ne_zero rightScale second rightNonzero secondNonNull) =
      form.reflectionProductRotation first second firstNonNull secondNonNull :=
  (TernaryForm.lorentz oneNonzero).reflectionProductRotation_scale
    leftScale rightScale first second leftNonzero rightNonzero firstNonNull secondNonNull

/-- The retained Lorentz normals recover the exact anchor vector, quadrance and half twist. -/
private theorem reflection_anchor_example :
    let rotation := Ternary.Lorentz.form.reflectionProductRotation Ternary.Lorentz.first Ternary.Lorentz.second
      Ternary.Lorentz.firstNonNull Ternary.Lorentz.secondNonNull
    let vector := Rotations.Ternary.Lorentz.rotationAnchorVector Ternary.Lorentz.oneNonzero rotation
      Ternary.Lorentz.reflectionProductAnchorDefined
    rotation.anchor Ternary.Lorentz.reflectionProductAnchorDefined =
        Lorentz.anchor Ternary.Lorentz.oneNonzero (⟨-5, 5, -5⟩ : Vector3 Rational) ∧
      vector = ⟨-5, 5, -5⟩ ∧ Ternary.Lorentz.form.quadrance vector = -25 ∧
      Ternary.Lorentz.form.quadrance vector =
        Ternary.Lorentz.form.spread Ternary.Lorentz.first Ternary.Lorentz.second
          Ternary.Lorentz.firstNonNull Ternary.Lorentz.secondNonNull /
          (1 - Ternary.Lorentz.form.spread Ternary.Lorentz.first Ternary.Lorentz.second
            Ternary.Lorentz.firstNonNull Ternary.Lorentz.secondNonNull) :=
  ⟨Ternary.Lorentz.reflection_product_anchor_matrix, Ternary.Lorentz.reflection_product_anchor_vector,
    Ternary.Lorentz.reflection_product_anchor_values⟩

/-- The spacelike example retains the computed second normal and equality with the original cap rotation. -/
private theorem cap_factorization_example :
    Ternary.Lorentz.capSecondNormal = (⟨3, 2, -2⟩ : Vector3 Rational) ∧
      Ternary.Lorentz.form.reflectionProductRotation Ternary.Lorentz.capPerpendicular
          Ternary.Lorentz.capSecondNormal Ternary.Lorentz.capPerpendicularNonNull
          Ternary.Lorentz.capSecondNormalNonNull =
        Rotations.Ternary.Lorentz.capRotation Ternary.Lorentz.oneNonzero
          Ternary.Lorentz.capAxis Ternary.Lorentz.capAxisDefined :=
  ⟨Ternary.Lorentz.cap_second_normal_values.2.1, Ternary.Lorentz.cap_reflection_product⟩

/-- Every original Lorentz rotation has two retained non-null reflection normals through the facade. -/
private def reflection_factorization {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) :
    Σ' first : Vector3 K, Σ' firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0,
      Σ' second : Vector3 K, Σ' secondNonNull : (TernaryForm.lorentz oneNonzero).quadrance second ≠ 0,
        (TernaryForm.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull =
          rotation := by
  let factors := (TernaryForm.lorentz oneNonzero).twoHalfTurnFactorization rotation twoNonzero
  refine ⟨factors.firstAxis, factors.firstNonNull, factors.secondAxis, factors.secondNonNull, ?_⟩
  apply SpecialOrthogonal.eq_of_matrix_eq
  exact Rotations.Ternary.Cayley.TernaryForm.TwoHalfTurnFactorization.reflectionProductMatrix factors

/-- An arbitrary non-null perpendicular first normal constructs the paper's exact second normal and cap product. -/
private def free_first_cap_mirror {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (axis first : Vector3 K)
    (defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero axis ≠ 0)
    (firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0)
    (perpendicular : (TernaryForm.lorentz oneNonzero).Perpendicular first axis) :
    Σ' second : Vector3 K, Σ' secondNonNull : (TernaryForm.lorentz oneNonzero).quadrance second ≠ 0,
      second = Vector3.add first (Lorentz.cross oneNonzero axis first) ∧
        (TernaryForm.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull =
          Rotations.Ternary.Lorentz.capRotation oneNonzero axis defined := by
  let form := TernaryForm.lorentz oneNonzero
  have genericDefined : Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator form (Vector3.neg axis) ≠ 0 := by
    rw [Rotations.Ternary.Lorentz.cayleyDenominator_neg]
    exact defined
  have genericPerpendicular : form.Perpendicular first (Vector3.neg axis) := by
    change form.bilinear first (Vector3.neg axis) = 0
    rw [form.bilinear_neg_right, perpendicular]
    ring1
  refine ⟨form.capSecondMirror (Vector3.neg axis) first,
    form.capSecondMirror_nonNull (Vector3.neg axis) first genericDefined firstNonNull genericPerpendicular, ?_, ?_⟩
  · unfold TernaryForm.capSecondMirror Lorentz.cross
    rw [form.cliffordCross_neg_left]
  · exact form.reflectionProduct_capSecondMirror
      (Vector3.neg axis) first genericDefined firstNonNull genericPerpendicular

/-- An arbitrary non-null perpendicular first normal constructs a half-turn second normal with its actual scale. -/
private def free_first_half_turn_mirror {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (axis first : Vector3 K)
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0)
    (firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0)
    (perpendicular : (TernaryForm.lorentz oneNonzero).Perpendicular first axis) :
    Σ' second : Vector3 K, Σ' secondNonNull : (TernaryForm.lorentz oneNonzero).quadrance second ≠ 0,
      second = Vector3.neg (Lorentz.cross oneNonzero axis first) ∧
        (TernaryForm.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull =
          (TernaryForm.lorentz oneNonzero).halfTurnRotation axis axisNonNull := by
  let form := TernaryForm.lorentz oneNonzero
  refine ⟨form.halfTurnSecondMirror axis first,
    form.halfTurnSecondMirror_nonNull axis first axisNonNull firstNonNull perpendicular, ?_, ?_⟩
  · exact (Vector3.neg_neg (form.cliffordCross axis first)).symm
  · exact form.reflectionProduct_halfTurnSecondMirror axis first axisNonNull firstNonNull perpendicular

/-- A fixed original Lorentz first mirror determines the second normal line with a retained nonzero scale. -/
private theorem second_mirror_line_unique {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (first left right : Vector3 K)
    (firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0)
    (leftNonNull : (TernaryForm.lorentz oneNonzero).quadrance left ≠ 0)
    (rightNonNull : (TernaryForm.lorentz oneNonzero).quadrance right ≠ 0)
    (sameProduct : (TernaryForm.lorentz oneNonzero).reflectionProductRotation first left firstNonNull leftNonNull =
      (TernaryForm.lorentz oneNonzero).reflectionProductRotation first right firstNonNull rightNonNull) :
    ∃ scalar : K, scalar ≠ 0 ∧ right = Vector3.scale scalar left :=
  (TernaryForm.lorentz oneNonzero).reflectionProduct_secondLine_unique
    first left right firstNonNull leftNonNull rightNonNull twoNonzero sameProduct

/-- The free-first-mirror construction reconstructs an arbitrary original non-half-turn Lorentz rotation. -/
private def free_first_rotation_mirror {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (notHalfTurn : Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (TernaryForm.lorentz oneNonzero) rotation ≠ 1)
    (first : Vector3 K) (firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0)
    (perpendicular : (TernaryForm.lorentz oneNonzero).Perpendicular first
      (Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation
        ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn))) :
    let axis := Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
    Σ' second : Vector3 K, Σ' secondNonNull : (TernaryForm.lorentz oneNonzero).quadrance second ≠ 0,
      second = Vector3.add first (Lorentz.cross oneNonzero axis first) ∧
        (TernaryForm.lorentz oneNonzero).reflectionProductRotation first second firstNonNull secondNonNull =
          rotation :=
  Rotations.Ternary.Lorentz.reflectionFactorizationFromFirst
    oneNonzero rotation twoNonzero notHalfTurn first firstNonNull perpendicular

/-- The public arbitrary-first constructor computes the spacelike example's original second normal. -/
private theorem cap_first_mirror_readback :
    let rotation := Rotations.Ternary.Lorentz.capRotation Ternary.Lorentz.oneNonzero
      Ternary.Lorentz.capAxis Ternary.Lorentz.capAxisDefined
    let notHalfTurn := Rotations.Ternary.Lorentz.halfSpread_cap_ne_one Ternary.Lorentz.oneNonzero
      Ternary.Lorentz.capAxis Ternary.Lorentz.capAxisDefined Ternary.Lorentz.twoNonzero
    let perpendicular : Ternary.Lorentz.form.Perpendicular Ternary.Lorentz.capPerpendicular
        (Rotations.Ternary.Lorentz.rotationAnchorVector Ternary.Lorentz.oneNonzero rotation
          ((rotation.anchorDenominator_ne_zero_iff Ternary.Lorentz.twoNonzero).mpr notHalfTurn)) := by
      rw [Rotations.Ternary.Lorentz.rotationAnchorVector_cap Ternary.Lorentz.oneNonzero
        Ternary.Lorentz.capAxis Ternary.Lorentz.capAxisDefined Ternary.Lorentz.twoNonzero]
      exact Ternary.Lorentz.cap_perpendicular_values.1
    (Rotations.Ternary.Lorentz.reflectionFactorizationFromFirst Ternary.Lorentz.oneNonzero rotation
      Ternary.Lorentz.twoNonzero notHalfTurn Ternary.Lorentz.capPerpendicular
      Ternary.Lorentz.capPerpendicularNonNull perpendicular).1 = Ternary.Lorentz.capSecondNormal := by decide

/-- Inversion negates the original Lorentz anchor vector through the publication API. -/
private theorem inverse_anchor {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) :
    Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero
        (Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.inverse rotation)
        (by rw [rotation.anchorDenominator_inverse]; exact defined) =
      Vector3.neg (Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation defined) :=
  Rotations.Ternary.Lorentz.rotationAnchorVector_inverse oneNonzero rotation defined

/-- Inversion preserves the original Lorentz half spread. -/
private theorem inverse_half_spread {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero)
        (Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.inverse rotation) =
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation :=
  Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread_inverse _ rotation

/-- The exact orientation determinant uses the paper's signed cross and original cap. -/
private theorem orientation_determinant {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (axis vector : Vector3 K)
    (defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero axis ≠ 0)
    (perpendicular : (TernaryForm.lorentz oneNonzero).Perpendicular vector axis) :
    Vector3.determinant axis vector
        (Matrix3.rowMul vector (Rotations.Ternary.Lorentz.cap oneNonzero axis defined)) =
      (-2 * (TernaryForm.lorentz oneNonzero).quadrance axis /
        Rotations.Ternary.Lorentz.capDenominator oneNonzero axis) *
        (TernaryForm.lorentz oneNonzero).quadrance vector :=
  Rotations.Ternary.Lorentz.determinant_cap_frame oneNonzero axis vector defined perpendicular

/-- A timelike axis gives positive orientation for every nonzero perpendicular test vector. -/
private theorem timelike_orientation {K : Type*} [RayOrderedExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (axis vector : Vector3 K)
    (defined : Rotations.Ternary.Lorentz.capDenominator oneNonzero axis ≠ 0)
    (positive : 0 < (TernaryForm.lorentz oneNonzero).quadrance axis)
    (perpendicular : (TernaryForm.lorentz oneNonzero).Perpendicular vector axis)
    (nonzero : vector ≠ Vector3.zero) :
    0 < Vector3.determinant axis vector
      (Matrix3.rowMul vector (Rotations.Ternary.Lorentz.cap oneNonzero axis defined)) :=
  Rotations.Ternary.Lorentz.determinant_cap_frame_pos_of_timelike
    oneNonzero axis vector defined positive perpendicular nonzero

/-- The boost's two displayed perpendicular frames have opposite determinant signs. -/
private theorem boost_frame_values :
    Vector3.determinant Ternary.Lorentz.boostAxis Ternary.Lorentz.time
      (Matrix3.rowMul Ternary.Lorentz.time (Rotations.Ternary.Lorentz.cap Ternary.Lorentz.oneNonzero
        Ternary.Lorentz.boostAxis Ternary.Lorentz.boostAxisDefined)) = 1 / 4 ∧
    Vector3.determinant Ternary.Lorentz.boostAxis (⟨0, 1, 0⟩ : Vector3 Rational)
      (Matrix3.rowMul ⟨0, 1, 0⟩ (Rotations.Ternary.Lorentz.cap Ternary.Lorentz.oneNonzero
        Ternary.Lorentz.boostAxis Ternary.Lorentz.boostAxisDefined)) = -1 / 4 :=
  ⟨Ternary.Lorentz.boost_time_frame_determinant, Ternary.Lorentz.boost_space_frame_determinant⟩

/-- The source composition law preserves the original Lorentz rotation owners and output domain certificate. -/
private theorem anchor_composition {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (left right : Vector3 K)
    (leftDefined : Rotations.Ternary.Lorentz.capDenominator oneNonzero left ≠ 0)
    (rightDefined : Rotations.Ternary.Lorentz.capDenominator oneNonzero right ≠ 0)
    (productDefined : Rotations.Ternary.Lorentz.anchorProductDenominator oneNonzero left right ≠ 0) :
    Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.mul
        (Rotations.Ternary.Lorentz.capRotation oneNonzero left leftDefined)
        (Rotations.Ternary.Lorentz.capRotation oneNonzero right rightDefined) =
      Rotations.Ternary.Lorentz.capRotation oneNonzero
        (Rotations.Ternary.Lorentz.anchorProduct oneNonzero left right productDefined)
        (Rotations.Ternary.Lorentz.capDenominator_anchorProduct_ne_zero
          oneNonzero left right leftDefined rightDefined productDefined) :=
  Rotations.Ternary.Lorentz.capRotation_mul oneNonzero left right leftDefined rightDefined productDefined

/-- The pairing-one half-turn criterion is available with the source Lorentz owner through the facade. -/
private theorem half_turn_product_criterion {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) (left right : Vector3 K)
    (leftDefined : Rotations.Ternary.Lorentz.capDenominator oneNonzero left ≠ 0)
    (rightDefined : Rotations.Ternary.Lorentz.capDenominator oneNonzero right ≠ 0) :
    (∃ axis : Vector3 K, ∃ nonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0,
      Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.mul
          (Rotations.Ternary.Lorentz.capRotation oneNonzero left leftDefined)
          (Rotations.Ternary.Lorentz.capRotation oneNonzero right rightDefined) =
        (TernaryForm.lorentz oneNonzero).halfTurnRotation axis nonNull) ↔
      (TernaryForm.lorentz oneNonzero).bilinear left right = 1 :=
  Rotations.Ternary.Lorentz.capRotation_mul_isHalfTurn_iff oneNonzero left right leftDefined rightDefined twoNonzero

/-- The two non-collinear boost products have opposite source time components. -/
private theorem boost_product_signs :
    Rotations.Ternary.Lorentz.anchorProduct Ternary.Lorentz.oneNonzero Ternary.Lorentz.boostAxis
      (⟨0, 1 / 3, 0⟩ : Vector3 Rational) (by decide) = ⟨-1 / 9, 1 / 3, 1 / 3⟩ ∧
    Rotations.Ternary.Lorentz.anchorProduct Ternary.Lorentz.oneNonzero
      (⟨0, 1 / 3, 0⟩ : Vector3 Rational) Ternary.Lorentz.boostAxis (by decide) = ⟨1 / 9, 1 / 3, 1 / 3⟩ :=
  Ternary.Lorentz.perpendicular_boost_products.2.2

/-- The literal product pair gives the computed source anchor through the exported operation. -/
private theorem composition_anchor_readback :
    Rotations.Ternary.Lorentz.anchorProduct Ternary.Lorentz.oneNonzero
        Ternary.Lorentz.compositionLeft Ternary.Lorentz.compositionRight Ternary.Lorentz.composition_domains.2.2 =
      ⟨-5, -5, -3⟩ := Ternary.Lorentz.composition_anchor_values.1

/-- The forbidden affine product retains the source half-turn matrix and its original surviving numerator. -/
private theorem forbidden_product_readback :
    Rotations.Ternary.Lorentz.anchorProductNumerator Ternary.Lorentz.oneNonzero
      Ternary.Lorentz.first Ternary.Lorentz.second = ⟨8, -4, 9⟩ ∧
    Matrix3.mul
        (Rotations.Ternary.Lorentz.cap Ternary.Lorentz.oneNonzero Ternary.Lorentz.first
          Ternary.Lorentz.firstSecondCapsDefined.1)
        (Rotations.Ternary.Lorentz.cap Ternary.Lorentz.oneNonzero Ternary.Lorentz.second
          Ternary.Lorentz.firstSecondCapsDefined.2) =
      Matrix3.scale (1 / 33) (⟨-161, 64, -144, -64, -1, -72, 144, -72, 129⟩ : Matrix3 Rational) :=
  ⟨Ternary.Lorentz.forbidden_product_values.1, Ternary.Lorentz.forbidden_product_matrix.1⟩

/-- The rational Einstein identity retains the four actual nonzero scalar denominators. -/
private theorem velocity_addition {K : Type*} [ExplicitField K] (left right : K)
    (leftDefined : 1 + left ^ 2 ≠ 0) (rightDefined : 1 + right ^ 2 ≠ 0)
    (anchorDefined : 1 + left * right ≠ 0)
    (velocityDefined : 1 + Rotations.Ternary.Lorentz.boostVelocity left *
      Rotations.Ternary.Lorentz.boostVelocity right ≠ 0) :
    Rotations.Ternary.Lorentz.boostVelocity ((left + right) / (1 + left * right)) =
      (Rotations.Ternary.Lorentz.boostVelocity left + Rotations.Ternary.Lorentz.boostVelocity right) /
        (1 + Rotations.Ternary.Lorentz.boostVelocity left * Rotations.Ternary.Lorentz.boostVelocity right) :=
  Rotations.Ternary.Lorentz.boostVelocity_add left right leftDefined rightDefined anchorDefined velocityDefined

/-- The owned ordered field proves the Einstein denominator positive for every defined collinear anchor sum. -/
private theorem velocity_denominator_positive {K : Type*} [RayOrderedExplicitField K] (left right : K)
    (anchorDefined : 1 + left * right ≠ 0) :
    0 < 1 + Rotations.Ternary.Lorentz.boostVelocity left * Rotations.Ternary.Lorentz.boostVelocity right :=
  Rotations.Ternary.Lorentz.boostVelocity_add_denominator_pos left right anchorDefined

/-- The original rational pair has the source spacelike and timelike causal types. -/
private theorem causal_types : Lorentz.IsSpacelike Ternary.Lorentz.oneNonzero Ternary.Lorentz.first ∧
    Lorentz.IsTimelike Ternary.Lorentz.oneNonzero Ternary.Lorentz.second := by
  unfold Lorentz.IsSpacelike Lorentz.IsTimelike
  decide

/-- The literal source dihedron product is available in the same retained Lorentz Clifford owner. -/
private theorem dihedron_product {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (leftScalar rightScalar : K) (leftVector rightVector : Vector3 K) :
    EvenClifford.mul (Matrix.coordinates oneNonzero leftScalar leftVector)
        (Matrix.coordinates oneNonzero rightScalar rightVector) =
      Matrix.coordinates oneNonzero
        (leftScalar * rightScalar - (TernaryForm.lorentz oneNonzero).bilinear leftVector rightVector)
        (Vector3.sub (Vector3.add (Vector3.scale leftScalar rightVector) (Vector3.scale rightScalar leftVector))
          (Lorentz.cross oneNonzero leftVector rightVector)) :=
  Matrix.coordinates_mul oneNonzero leftScalar rightScalar leftVector rightVector

/-- The source matrix map preserves addition of the original Clifford values. -/
private theorem dihedron_matrix_add {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (left right : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    Matrix.toMatrix oneNonzero (EvenClifford.add left right) =
      Matrix2.add (Matrix.toMatrix oneNonzero left) (Matrix.toMatrix oneNonzero right) :=
  Matrix.toMatrix_add oneNonzero left right

/-- The source matrix map preserves the retained homogeneous scalar factor. -/
private theorem dihedron_matrix_scale {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (factor : K) (value : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    Matrix.toMatrix oneNonzero (EvenClifford.scale factor value) =
      Matrix2.scalarScale factor (Matrix.toMatrix oneNonzero value) := Matrix.toMatrix_scale oneNonzero factor value

/-- The source matrix trace is twice the scalar coordinate under the owned matrix trace operation. -/
private theorem dihedron_matrix_trace {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K) :
    Matrix2.trace (Matrix.toMatrix oneNonzero (Matrix.coordinates oneNonzero scalar vector)) = 2 * scalar :=
  Matrix.trace_coordinates oneNonzero scalar vector

/-- The original dihedron algebra has a two-sided inverse precisely at nonzero reduced norm. -/
private theorem dihedron_invertible {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (value : (TernaryForm.lorentz oneNonzero).EvenClifford) :
    (∃ inverse : (TernaryForm.lorentz oneNonzero).EvenClifford,
      EvenClifford.mul value inverse = EvenClifford.identity (TernaryForm.lorentz oneNonzero) ∧
      EvenClifford.mul inverse value = EvenClifford.identity (TernaryForm.lorentz oneNonzero)) ↔
      EvenClifford.norm value ≠ 0 := EvenClifford.invertible_iff_norm_ne_zero value

/-- The source basis squares retain the negative time and positive space products. -/
private theorem dihedron_basis_squares {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0) :
    EvenClifford.mul (Matrix.i oneNonzero) (Matrix.i oneNonzero) =
      EvenClifford.scale (-1) (EvenClifford.identity (TernaryForm.lorentz oneNonzero)) ∧
    EvenClifford.mul (Matrix.j oneNonzero) (Matrix.j oneNonzero) =
      EvenClifford.identity (TernaryForm.lorentz oneNonzero) ∧
    EvenClifford.mul (Matrix.k oneNonzero) (Matrix.k oneNonzero) =
      EvenClifford.identity (TernaryForm.lorentz oneNonzero) :=
  ⟨(Matrix.basis_table oneNonzero).1, (Matrix.basis_table oneNonzero).2.1,
    (Matrix.basis_table oneNonzero).2.2.1⟩

/-- The source basis cross products retain the original row-action order. -/
private theorem dihedron_basis_forward {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0) :
    EvenClifford.mul (Matrix.j oneNonzero) (Matrix.i oneNonzero) = Matrix.k oneNonzero ∧
    EvenClifford.mul (Matrix.j oneNonzero) (Matrix.k oneNonzero) = Matrix.i oneNonzero ∧
    EvenClifford.mul (Matrix.i oneNonzero) (Matrix.k oneNonzero) = Matrix.j oneNonzero :=
  ⟨(Matrix.basis_table oneNonzero).2.2.2.1, (Matrix.basis_table oneNonzero).2.2.2.2.1,
    (Matrix.basis_table oneNonzero).2.2.2.2.2.1⟩

/-- The public source-coordinate constructor computes the original introductory Clifford representative. -/
private theorem dihedron_constructor_readback :
    (Matrix.nonNullCoordinates oneNonzero 3 (⟨0, 0, 1⟩ : Vector3 Rational) (by decide)).toEvenClifford =
      introductoryValue.toEvenClifford := rfl

/-- The facade exposes the proportion half spread in the literal source coordinates. -/
private theorem proportion_halfSpread {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero)
        (Rotations.Ternary.Lorentz.proportionRotation oneNonzero scalar vector defined) =
      (TernaryForm.lorentz oneNonzero).quadrance vector /
        (scalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance vector) :=
  Rotations.Ternary.Lorentz.halfSpread_proportionRotation oneNonzero scalar vector defined twoNonzero

/-- Equal rotations have one explicit homogeneous factor for both original source coordinates. -/
private theorem proportion_fibers {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (leftScalar rightScalar : K) (leftVector rightVector : Vector3 K)
    (leftDefined : leftScalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance leftVector ≠ 0)
    (rightDefined : rightScalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance rightVector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : Rotations.Ternary.Lorentz.proportionRotation oneNonzero leftScalar leftVector leftDefined =
      Rotations.Ternary.Lorentz.proportionRotation oneNonzero rightScalar rightVector rightDefined) :
    ∃ factor : K, factor ≠ 0 ∧ rightScalar = factor * leftScalar ∧
      rightVector = Vector3.scale factor leftVector :=
  (Rotations.Ternary.Lorentz.proportionRotation_eq_iff oneNonzero leftScalar rightScalar leftVector rightVector
    leftDefined rightDefined twoNonzero).mp equal

/-- The executable preimage returns to the same original rotation through the source-coordinate chart. -/
private theorem proportion_preimage {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) :
    Rotations.Ternary.Lorentz.proportionRotation oneNonzero
        (Rotations.Ternary.Lorentz.rotationProportion oneNonzero twoNonzero rotation).scalar
        (Vector3.neg (Rotations.Ternary.Lorentz.rotationProportion oneNonzero twoNonzero rotation).vector)
        (Rotations.Ternary.Lorentz.rotationProportion_nonzero oneNonzero twoNonzero rotation) = rotation :=
  Rotations.Ternary.Lorentz.proportionRotation_rotationProportion oneNonzero twoNonzero rotation

/-- Pure source dihedrons give the displayed row action under the retained normalized sandwich. -/
private theorem proportion_sandwich {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (scalar : K) (vector input : Vector3 K)
    (defined : scalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance vector ≠ 0) :
    Matrix.coordinates oneNonzero 0 (Matrix3.rowMul input
        (Rotations.Ternary.Lorentz.proportionRotation oneNonzero scalar vector defined).matrix) =
      EvenClifford.scale (scalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance vector)⁻¹
        (EvenClifford.mul
          (EvenClifford.mul (EvenClifford.conjugate (Matrix.coordinates oneNonzero scalar vector))
            (Matrix.coordinates oneNonzero 0 input)) (Matrix.coordinates oneNonzero scalar vector)) :=
  Rotations.Ternary.Lorentz.proportionRotation_sandwich oneNonzero scalar vector input defined

/-- Both source time-orientation examples retain their literal rational time entries. -/
private theorem proportion_time_examples :
    (Rotations.Ternary.Lorentz.proportionRotation oneNonzero 3 (⟨0, 0, 1⟩ : Vector3 Rational)
      (by decide)).matrix.tt = 5 / 4 ∧
    (Rotations.Ternary.Lorentz.proportionRotation oneNonzero 2 (⟨1, 2, 3⟩ : Vector3 Rational)
      (by decide)).matrix.tt = -(9 / 4) := by
  constructor <;> rw [Rotations.Ternary.Lorentz.proportionRotation_timeEntry] <;> decide

/-- Positive time entry is closed under the product of the original certified Lorentz rotations. -/
private theorem time_direction_product {K : Type*} [RayOrderedExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (left right : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (leftPositive : 0 < left.matrix.tt) (rightPositive : 0 < right.matrix.tt) :
    0 < (SpecialOrthogonal.mul left right).matrix.tt :=
  Rotations.Ternary.Lorentz.rotation_mul_time_pos oneNonzero left right leftPositive rightPositive

/-- Positive time entry is closed under the retained inverse of an original Lorentz rotation. -/
private theorem time_direction_inverse {K : Type*} [RayOrderedExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (positive : 0 < rotation.matrix.tt) :
    0 < (SpecialOrthogonal.inverse rotation).matrix.tt :=
  Rotations.Ternary.Lorentz.rotation_inverse_time_pos oneNonzero rotation positive

/-- The source norm witness realizes the requested nontrivial rational norm exactly. -/
private theorem prescribed_dihedron_norm :
    EvenClifford.norm (Rotations.Ternary.Lorentz.normWitness oneNonzero (2 : Rational)) = 2 :=
  Rotations.Ternary.Lorentz.norm_normWitness oneNonzero 2 (by decide)

/-- Every retained rational square class has a certified original Lorentz rotation preimage. -/
private theorem quadrance_class_onto
    (target : Purelib.Algebra.Field.SquareClass.Basic.SquareClassRepresentative Rational) :
    ∃ rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal,
      (rotation.quadranceClass (by decide : (2 : Rational) ≠ 0)).Equivalent target :=
  Rotations.Ternary.Lorentz.quadranceClass_surjective oneNonzero target (by decide)

/-- The original reflection normals determine the square class of their quadrance product. -/
private theorem reflection_quadrance_class {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (first second : Vector3 K)
    (firstNonNull : (TernaryForm.lorentz oneNonzero).quadrance first ≠ 0)
    (secondNonNull : (TernaryForm.lorentz oneNonzero).quadrance second ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (((TernaryForm.lorentz oneNonzero).reflectionProductRotation first second firstNonNull
      secondNonNull).quadranceClass twoNonzero).Equivalent
      ⟨(TernaryForm.lorentz oneNonzero).quadrance first * (TernaryForm.lorentz oneNonzero).quadrance second,
        ExplicitField.mul_ne_zero firstNonNull secondNonNull⟩ :=
  TernaryForm.SpecialOrthogonal.quadranceClass_reflectionProduct first second firstNonNull secondNonNull twoNonzero

/-- Unit-norm representatives exist precisely for the original rotation's trivial quadrance class. -/
private theorem unit_norm_obstruction {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    (∃ value : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford,
      NonNullEvenClifford.actionRotation value = rotation ∧ EvenClifford.norm value.toEvenClifford = 1) ↔
      (rotation.quadranceClass twoNonzero).Equivalent ⟨1, oneNonzero⟩ :=
  rotation.unitNormPreimage_iff twoNonzero

/-- The source trace and antisymmetric-part recipe reconstructs the original non-half-turn rotation. -/
private theorem projective_cap_recipe {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (TernaryForm.lorentz oneNonzero) rotation ≠ 1) :
    Rotations.Ternary.Lorentz.proportionRotation oneNonzero rotation.anchorDenominator
        (Rotations.Ternary.Lorentz.projectiveInverseVector oneNonzero rotation twoNonzero)
        (Rotations.Ternary.Lorentz.projectiveInverse_nonzero oneNonzero rotation twoNonzero notHalfTurn) = rotation :=
  Rotations.Ternary.Lorentz.proportionRotation_projectiveInverse oneNonzero rotation twoNonzero notHalfTurn

/-- The projective inverse vector has the literal source anchor required by the trace recipe. -/
private theorem projective_cap_recipe_anchor {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Lorentz.anchor oneNonzero (Rotations.Ternary.Lorentz.projectiveInverseVector oneNonzero rotation twoNonzero) =
      Matrix3.scale 2 (rotation.antisymmetricPart twoNonzero) :=
  Rotations.Ternary.Lorentz.anchor_projectiveInverseVector oneNonzero rotation defined twoNonzero

/-- Every nonzero supplied row-space vector of identity plus a half turn gives its source proportion. -/
private def projective_half_turn_row_recipe {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0)
    (halfSpreadOne : Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (TernaryForm.lorentz oneNonzero) rotation = 1)
    (input : Vector3 K)
    (nonzero : Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix) ≠ Vector3.zero) :
    Σ' defined : 0 ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance
      (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix)) ≠ 0,
      Rotations.Ternary.Lorentz.proportionRotation oneNonzero 0
        (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix)) defined = rotation :=
  Rotations.Ternary.Lorentz.halfTurnRowProportion oneNonzero rotation twoNonzero halfSpreadOne input nonzero

/-- The spacelike axis retains a non-null perpendicular first mirror normal. -/
private def nonNullAxisMirror :
    (TernaryForm.lorentz oneNonzero).PerpendicularNonNullVectorWitness (⟨0, 1, 1⟩ : Vector3 Rational) where
  value := ⟨1, 1, -1⟩
  perpendicular := by
    unfold TernaryForm.Perpendicular
    decide
  nonNull := by decide

/-- The null axis retains a non-null perpendicular first mirror normal. -/
private def nullAxisMirror :
    (TernaryForm.lorentz oneNonzero).PerpendicularNonNullVectorWitness (⟨1, 1, 0⟩ : Vector3 Rational) where
  value := ⟨0, 0, 1⟩
  perpendicular := by
    unfold TernaryForm.Perpendicular
    decide
  nonNull := by decide

/-- The zero axis retains the original time direction as a first mirror normal. -/
private def zeroAxisMirror :
    (TernaryForm.lorentz oneNonzero).PerpendicularNonNullVectorWitness (Vector3.zero : Vector3 Rational) where
  value := ⟨1, 0, 0⟩
  perpendicular := by
    unfold TernaryForm.Perpendicular
    decide
  nonNull := by decide

/-- All three axis branches retain the expected executable alternate first mirror direction. -/
private theorem alternate_first_line_readbacks :
    (nonNullAxisMirror.alternateDirection (by decide)).1.value = (⟨-2, -1, 1⟩ : Vector3 Rational) ∧
    (nullAxisMirror.alternateDirection (by decide)).1.value = (⟨1, 1, 1⟩ : Vector3 Rational) ∧
    (zeroAxisMirror.alternateDirection (by decide)).1.value = (⟨0, 1, 0⟩ : Vector3 Rational) := by decide

/-- Every retained perpendicular non-null first mirror has an explicitly different admissible line. -/
private def alternate_first_line {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (axis : Vector3 K)
    (first : (TernaryForm.lorentz oneNonzero).PerpendicularNonNullVectorWitness axis)
    (twoNonzero : (2 : K) ≠ 0) :
    Σ' second : (TernaryForm.lorentz oneNonzero).PerpendicularNonNullVectorWitness axis,
      ¬ ∃ factor : K, factor ≠ 0 ∧ second.value = Vector3.scale factor first.value :=
  first.alternateDirection twoNonzero

/-- Every original Lorentz rotation has two certified reflection factorizations with different first lines. -/
private def distinct_mirror_factorizations {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) :
    Σ' first : (TernaryForm.lorentz oneNonzero).TwoHalfTurnFactorization rotation,
      Σ' second : (TernaryForm.lorentz oneNonzero).TwoHalfTurnFactorization rotation,
        ¬ ∃ factor : K, factor ≠ 0 ∧ second.firstAxis = Vector3.scale factor first.firstAxis :=
  (TernaryForm.lorentz oneNonzero).distinctFirstMirrorFactorizations rotation twoNonzero

/-- Every finite Lorentz kernel-coset request returns the exact requested length. -/
private theorem finite_kernel_pack_length (count : Nat) :
    (Rotations.Ternary.Lorentz.separatedKernelCosetPack oneNonzero (by decide) count).entries.length = count :=
  (Rotations.Ternary.Lorentz.separatedKernelCosetPack oneNonzero (by decide) count).length_eq

/-- The retained kernel-coset pack excludes unit-norm preimages of the actual relative rotations. -/
private theorem finite_kernel_pack_separation (count : Nat) :
    (Rotations.Ternary.Lorentz.separatedKernelCosetPack oneNonzero (by decide) count).entries.Pairwise
      fun left right => ¬ ∃ value : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford,
        NonNullEvenClifford.actionRotation value =
          SpecialOrthogonal.mul (SpecialOrthogonal.inverse left.rotation) right.rotation ∧
        EvenClifford.norm value.toEvenClifford = 1 :=
  (Rotations.Ternary.Lorentz.separatedKernelCosetPack oneNonzero (by decide) count).pairwiseSeparated

/-- The Lorentz facade supplies the finite quaternion split model in literal source coordinates. -/
private theorem finite_quaternion_dictionary {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0)
    (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (value : Purelib.Algebra.Quaternion.Projective.Basic.Proportion K) :
    let split := Purelib.Algebra.Quaternion.SplitMatrix.finiteSplit presentation
    Purelib.Algebra.Quaternion.SplitMatrix.toMatrix split value = Matrix.toMatrix oneNonzero
      (Matrix.coordinates oneNonzero value.scalar
        ⟨value.vector.t, split.second * value.vector.r - split.first * value.vector.s,
          split.first * value.vector.r + split.second * value.vector.s⟩) :=
  Purelib.Algebra.Quaternion.SplitMatrix.toMatrix_eq_lorentz_coordinates oneNonzero _ value

/-- The introductory boost's exact norm class and rational unit-preimage obstruction are public. -/
private theorem introductory_unit_obstruction :
    ((NonNullEvenClifford.actionRotation Ternary.Lorentz.introductoryValue).quadranceClass
      Ternary.Lorentz.twoNonzero).Equivalent ⟨2, by decide⟩ ∧
      ¬ ∃ value : Ternary.Lorentz.form.NonNullEvenClifford,
        NonNullEvenClifford.actionRotation value =
          NonNullEvenClifford.actionRotation Ternary.Lorentz.introductoryValue ∧
        EvenClifford.norm value.toEvenClifford = 1 :=
  ⟨Ternary.Lorentz.introductory_quadranceClass_two, Ternary.Lorentz.introductory_no_unit_preimage⟩

/-- The original non-half-turn Lorentz rotation has all three causal half-spread ranges through the facade. -/
private theorem causal_ranges {F : Type*} [RayOrderedExplicitField F] [DecidableEq F]
    (oneNonzero : (1 : F) ≠ 0)
    (law : Purelib.Algebra.Field.ExplicitOrder.Sign.OrderDifferenceLaw F)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : F) ≠ 0)
    (notHalfTurn : Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread
      (TernaryForm.lorentz oneNonzero) rotation ≠ 1) (timePositive : 0 < rotation.matrix.tt) :
    let vector := Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation
      ((rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn)
    (0 < (TernaryForm.lorentz oneNonzero).quadrance vector →
      0 < Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation ∧
        Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation < 1) ∧
    ((TernaryForm.lorentz oneNonzero).quadrance vector < 0 →
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation < 0) ∧
    ((TernaryForm.lorentz oneNonzero).quadrance vector = 0 →
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation = 0) ∧
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation < 1 :=
  Rotations.Ternary.Lorentz.rotation_halfSpread_timePositive_ranges
    oneNonzero law rotation twoNonzero notHalfTurn timePositive

/-- The rational strict comparison supplies the same explicit difference law required by causal classification. -/
private theorem rational_order_differences :
    Purelib.Algebra.Field.ExplicitOrder.Sign.OrderDifferenceLaw Rational :=
  Purelib.Data.Rat.Fraction.Order.Basic.lt_iff_zero_lt_sub

/-- The rational ray-order model retains the complete original field and strict-comparison dictionaries. -/
private theorem rational_ray_dictionaries :
    (inferInstance : RayOrderedExplicitField Rational).toOrderedExplicitField.toExplicitField =
      (inferInstance : ExplicitField Rational) ∧
    (inferInstance : RayOrderedExplicitField Rational).toOrderedExplicitField.toLT =
      (inferInstance : LT Rational) := by
  constructor <;> rfl

/-- The negative-time source proportion has exact half spread three halves. -/
private theorem negative_time_half_spread :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero)
      (Rotations.Ternary.Lorentz.proportionRotation oneNonzero 2 ⟨1, 2, 3⟩ (by decide)) = 3 / 2 := by
  rw [Rotations.Ternary.Lorentz.halfSpread_proportionRotation oneNonzero 2 ⟨1, 2, 3⟩ (by decide) (by decide)]
  decide

/-- The source negative-time rotation retains its original spacelike axis and exact time entry. -/
private theorem negative_time_example_values :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread Ternary.Lorentz.form
        Ternary.Lorentz.negativeTimeRotation = 3 / 2 ∧
      Ternary.Lorentz.negativeTimeRotation.matrix.tt = -9 / 4 ∧
      Matrix3.rowMul Ternary.Lorentz.first Ternary.Lorentz.negativeTimeRotation.matrix = Ternary.Lorentz.first :=
  ⟨Ternary.Lorentz.negativeTimeRotation_values.1, Ternary.Lorentz.negativeTimeRotation_values.2,
    Ternary.Lorentz.negativeTimeRotation_fixed_first⟩

/-- The negative-time source matrix has the centered factor with roots negative two plus or minus root three. -/
private theorem negative_time_characteristic (point : Rational) :
    Matrix3.characteristicValue Ternary.Lorentz.negativeTimeRotation.matrix point =
      (point - 1) * ((point + 2) ^ 2 - 3) :=
  Ternary.Lorentz.negativeTimeRotation_characteristic_centered point

/-- The original negative-time matrix has no rational nontrivial eigenvalue. -/
private theorem negative_time_nonsplit (point : Rational) (notOne : point ≠ 1) :
    ¬ Nonempty (Matrix3.RowEigenvector Ternary.Lorentz.negativeTimeRotation.matrix point) :=
  Ternary.Lorentz.negativeTimeRotation_no_nontrivial_eigenvalue point notOne

/-- A supplied square root of three gives exactly the two source roots of the negative-time reciprocal factor. -/
private theorem negative_time_root_formula {F : Type*} [ExplicitField F]
    (radius point : F) (square : radius ^ 2 = 3) :
    Reciprocal.eval (-2) point =
      (point - (-2 + radius)) * (point - (-2 - radius)) := by
  apply Reciprocal.eval_factor
  calc
    radius ^ 2 = 3 := square
    _ = (-2 : F) ^ 2 - 1 := by ring1

/-- An arbitrary certified spatial plane rotation retains its Euclidean row arithmetic in the Lorentz owner. -/
private theorem spatial_embedding {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)
    (cosine sine : K) (unit : cosine ^ 2 + sine ^ 2 = 1) (vector : Vector3 K) :
    Matrix3.rowMul vector (Rotations.Ternary.Lorentz.spatialRotation oneNonzero cosine sine unit).matrix =
      ⟨vector.t, cosine * vector.r - sine * vector.s, sine * vector.r + cosine * vector.s⟩ :=
  Rotations.Ternary.Lorentz.spatialRotation_apply oneNonzero cosine sine unit vector

/-- The actual product of spatially embedded Lorentz rotations has the original plane coefficient product. -/
private theorem spatial_product {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)
    (leftCosine leftSine rightCosine rightSine : K)
    (leftUnit : leftCosine ^ 2 + leftSine ^ 2 = 1) (rightUnit : rightCosine ^ 2 + rightSine ^ 2 = 1) :
    (SpecialOrthogonal.mul
      (Rotations.Ternary.Lorentz.spatialRotation oneNonzero leftCosine leftSine leftUnit)
      (Rotations.Ternary.Lorentz.spatialRotation oneNonzero rightCosine rightSine rightUnit)).matrix =
      Rotations.Ternary.Lorentz.spatialRotationMatrix (leftCosine * rightCosine - leftSine * rightSine)
        (leftCosine * rightSine + leftSine * rightCosine) :=
  Rotations.Ternary.Lorentz.spatialRotation_mul_matrix
    oneNonzero leftCosine leftSine rightCosine rightSine leftUnit rightUnit

/-- The general spatial embedding agrees with the original source quarter-turn cap matrix. -/
private theorem spatial_quarter_turn_agrees :
    (Rotations.Ternary.Lorentz.spatialRotation oneNonzero 0 1 (by decide)).matrix =
      (Rotations.Ternary.Lorentz.capRotation oneNonzero ⟨1, 0, 0⟩ (by decide)).matrix := by decide

/-- The imaginary-unit coordinate dictionary uses the original Lorentz dihedron owner in the target field. -/
private theorem imaginary_quaternion_dictionary {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (i : K) (value : Quaternion.Projective.Basic.Proportion K) :
    Quaternion.Matrix.toMatrix i value = Matrix.toMatrix oneNonzero
      (Matrix.coordinates oneNonzero value.scalar
        ⟨value.vector.t, i * value.vector.r, i * value.vector.s⟩) :=
  Quaternion.Matrix.toMatrix_eq_lorentz_coordinates oneNonzero i value

/-- The imaginary spatial-coordinate change identifies Lorentz and Euclidean quadrance. -/
private theorem imaginary_quadrance_dictionary {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (i : K) (iSquare : i ^ 2 = -1) (vector : Vector3 K) :
    (TernaryForm.lorentz oneNonzero).quadrance ⟨vector.t, i * vector.r, i * vector.s⟩ = vector.quadrance :=
  Lorentz.quadrance_spatial_imaginary oneNonzero i iSquare vector

/-- The original algebras are the twisted and ordinary conjugation fixed forms in the quadratic field. -/
private theorem quaternion_dihedron_forms {K : Type*} [ExplicitField K] [DecidableEq K]
    (noRoot : Field.Squares.NoSquareRootOfNegativeOne (K := K)) (twoNonzero : (2 : K) ≠ 0)
    (matrix : Matrix2 (Quadratic.Pair K (1 : K))) :
    letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
    ((∃ value : Quaternion.Projective.Basic.Proportion K,
      Quaternion.Matrix.toEmbeddedMatrix (Quadratic.Pair.ImaginaryField.scalarEmbedding noRoot twoNonzero)
        Quadratic.Pair.generator value = matrix) ↔
      Matrix2.mul (Matrix2.mul ⟨0, -1, 1, 0⟩ matrix) ⟨0, 1, -1, 0⟩ =
        Matrix2.map Quadratic.Pair.conjugate matrix) ∧
      (Matrix2.map Quadratic.Pair.conjugate matrix = matrix ↔
        ∃ base : Matrix2 K, Matrix2.map Quadratic.Pair.scalar base = matrix) := by
  letI := Quadratic.Pair.ImaginaryField.explicitField noRoot twoNonzero
  exact ⟨Quaternion.Matrix.imaginary_image_iff_fixed noRoot twoNonzero matrix,
    Quaternion.Matrix.conjugation_fixed_iff_base_matrix twoNonzero matrix⟩

/-- A nonzero null dihedron returns its exact matrix's original nonzero column and row spinors. -/
private def null_dihedron_spinors {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) (nonzero : value ≠ ⟨0, Vector3.zero⟩)
    (null : EvenClifford.norm value = 0) : Matrix2.RankOneFactorization (Matrix.toMatrix oneNonzero value) :=
  Matrix.nullFactorization oneNonzero twoNonzero value nonzero null

/-- The retained spinors reconstruct the original dihedron matrix and give a point on both labelled rulings. -/
private theorem null_dihedron_rulings {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) (nonzero : value ≠ ⟨0, Vector3.zero⟩)
    (null : EvenClifford.norm value = 0) :
    let witness := Matrix.nullFactorization oneNonzero twoNonzero value nonzero null
    Matrix2.outer witness.column witness.row = Matrix.toMatrix oneNonzero value ∧
      Matrix2.ColumnRuling witness.column (Matrix.toMatrix oneNonzero value) ∧
      Matrix2.RowRuling witness.row (Matrix.toMatrix oneNonzero value) := by
  let witness := Matrix.nullFactorization oneNonzero twoNonzero value nonzero null
  exact ⟨witness.reconstruction, ⟨witness.columnNonzero, witness.row, witness.rowNonzero, witness.reconstruction⟩,
    ⟨witness.rowNonzero, witness.column, witness.columnNonzero, witness.reconstruction⟩⟩

/-- Spinor factorization ambiguity is exactly a common nonzero column scale with the reciprocal row scale. -/
private def spinor_scale_witness {K : Type*} [ExplicitField K] [DecidableEq K]
    (leftColumn leftRow rightColumn rightRow : Proj K)
    (leftColumnNonzero : leftColumn.Nonzero) (leftRowNonzero : leftRow.Nonzero)
    (rightColumnNonzero : rightColumn.Nonzero) (rightRowNonzero : rightRow.Nonzero)
    (equal : Matrix2.outer leftColumn leftRow = Matrix2.outer rightColumn rightRow) :
    Σ' factor : K, factor ≠ 0 ∧ rightColumn = leftColumn.scale factor ∧ rightRow = leftRow.scale factor⁻¹ :=
  Matrix2.outer_scaleWitness leftColumn leftRow rightColumn rightRow
    leftColumnNonzero leftRowNonzero rightColumnNonzero rightRowNonzero equal

/-- Same-family null-quadric rulings are disjoint for distinct original projective spinor labels. -/
private theorem ruling_disjointness {K : Type*} [ExplicitField K] (left right : Proj K)
    (distinct : ¬ left.Equivalent right) :
    (¬ ∃ matrix : Matrix2 K, Matrix2.ColumnRuling left matrix ∧ Matrix2.ColumnRuling right matrix) ∧
      (¬ ∃ matrix : Matrix2 K, Matrix2.RowRuling left matrix ∧ Matrix2.RowRuling right matrix) :=
  ⟨Matrix2.column_rulings_disjoint distinct, Matrix2.row_rulings_disjoint distinct⟩

/-- Opposite rulings meet in precisely the projective point of the outer matrix of their original labels. -/
private theorem ruling_intersection {K : Type*} [ExplicitField K] [DecidableEq K]
    (column row : Proj K) (columnNonzero : column.Nonzero) (rowNonzero : row.Nonzero)
    (matrix : Matrix2 K) (columnMember : Matrix2.ColumnRuling column matrix)
    (rowMember : Matrix2.RowRuling row matrix) :
    Matrix2.ColumnRuling column (Matrix2.outer column row) ∧
      Matrix2.RowRuling row (Matrix2.outer column row) ∧
      ∃ factor : K, factor ≠ 0 ∧ matrix = Matrix2.scalarScale factor (Matrix2.outer column row) := by
  have meets := Matrix2.opposite_rulings_meet columnNonzero rowNonzero
  exact ⟨meets.1, meets.2, Matrix2.opposite_rulings_intersection columnMember rowMember⟩

/-- Each ruling is parametrized by the other original projective line with exact projective fibers. -/
private theorem ruling_parametrizations {K : Type*} [ExplicitField K] [DecidableEq K]
    (fixed left right : Proj K) (fixedNonzero : fixed.Nonzero)
    (leftNonzero : left.Nonzero) (rightNonzero : right.Nonzero) :
    ((∃ factor : K, factor ≠ 0 ∧
      Matrix2.outer fixed right = Matrix2.scalarScale factor (Matrix2.outer fixed left)) ↔ left.Equivalent right) ∧
      ((∃ factor : K, factor ≠ 0 ∧
        Matrix2.outer right fixed = Matrix2.scalarScale factor (Matrix2.outer left fixed)) ↔ left.Equivalent right) :=
  ⟨Matrix2.column_ruling_parametrization fixed left right fixedNonzero leftNonzero rightNonzero,
    Matrix2.row_ruling_parametrization fixed left right fixedNonzero leftNonzero rightNonzero⟩

/-- Changing a spinor label to an equivalent original valid pair preserves its ruling. -/
private theorem ruling_label_transport {K : Type*} [ExplicitField K] [DecidableEq K]
    (left right : Proj K) (rightNonzero : right.Nonzero) (equivalent : left.Equivalent right) (matrix : Matrix2 K) :
    (Matrix2.ColumnRuling left matrix → Matrix2.ColumnRuling right matrix) ∧
      (Matrix2.RowRuling left matrix → Matrix2.RowRuling right matrix) :=
  ⟨Matrix2.column_ruling_transport rightNonzero equivalent, Matrix2.row_ruling_transport rightNonzero equivalent⟩

/-- Each fixed spinor gives a linear span with two original coordinates and injective coordinate readback. -/
private theorem ruling_linear_coordinates {K : Type*} [ExplicitField K]
    (column row left right : Proj K) (columnNonzero : column.Nonzero) (rowNonzero : row.Nonzero) :
    Matrix2.outer column row = Matrix2.add (Matrix2.scalarScale row.p (Matrix2.outer column ⟨1, 0⟩))
        (Matrix2.scalarScale row.q (Matrix2.outer column ⟨0, 1⟩)) ∧
      Matrix2.outer column row = Matrix2.add (Matrix2.scalarScale column.p (Matrix2.outer ⟨1, 0⟩ row))
        (Matrix2.scalarScale column.q (Matrix2.outer ⟨0, 1⟩ row)) ∧
      Matrix2.outer column ⟨left.p + right.p, left.q + right.q⟩ =
        Matrix2.add (Matrix2.outer column left) (Matrix2.outer column right) ∧
      Matrix2.outer ⟨left.p + right.p, left.q + right.q⟩ row =
        Matrix2.add (Matrix2.outer left row) (Matrix2.outer right row) ∧
      (Matrix2.outer column left = Matrix2.outer column right → left = right) ∧
      (Matrix2.outer left row = Matrix2.outer right row → left = right) :=
  ⟨Matrix2.outer_row_coordinates column row, Matrix2.outer_column_coordinates column row,
    Matrix2.outer_row_add column left right, Matrix2.outer_column_add row left right,
    Matrix2.outer_row_injective columnNonzero, Matrix2.outer_column_injective rowNonzero⟩

/-- Both ruling families contain only original nonzero singular matrices. -/
private theorem ruling_points_singular {K : Type*} [ExplicitField K] (label : Proj K) (matrix : Matrix2 K) :
    (Matrix2.ColumnRuling label matrix → matrix.IsNonzero ∧ matrix.determinant = 0) ∧
      (Matrix2.RowRuling label matrix → matrix.IsNonzero ∧ matrix.determinant = 0) :=
  ⟨Matrix2.ColumnRuling.nonzero_singular, Matrix2.RowRuling.nonzero_singular⟩

/-- The four nonzero-column charts retain exact computed rational spinor coordinates. -/
private theorem rank_one_computed_charts :
    let first := Matrix2.rankOneFactorization (⟨2, 6, 3, 9⟩ : Matrix2 Rational) oneNonzero
      (Or.inl (by decide)) (by decide)
    let third := Matrix2.rankOneFactorization (⟨0, 0, 2, 6⟩ : Matrix2 Rational) oneNonzero
      (Or.inr (Or.inr (Or.inl (by decide)))) (by decide)
    let second := Matrix2.rankOneFactorization (⟨0, 2, 0, 6⟩ : Matrix2 Rational) oneNonzero
      (Or.inr (Or.inl (by decide))) (by decide)
    let fourth := Matrix2.rankOneFactorization (⟨0, 0, 0, 6⟩ : Matrix2 Rational) oneNonzero
      (Or.inr (Or.inr (Or.inr (by decide)))) (by decide)
    first.column = ⟨2, 3⟩ ∧ first.row = ⟨1, 3⟩ ∧
      third.column = ⟨0, 2⟩ ∧ third.row = ⟨1, 3⟩ ∧
      second.column = ⟨2, 6⟩ ∧ second.row = ⟨0, 1⟩ ∧
      fourth.column = ⟨0, 6⟩ ∧ fourth.row = ⟨0, 1⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The invertible-matrix bridge retains exact original dihedron and matrix round trips. -/
private theorem invertible_dihedron_round_trips {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (value : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford) (matrix : Matrix2.Invertible K) :
    Matrix.fromInvertible oneNonzero twoNonzero (Matrix.toInvertible oneNonzero value) = value ∧
      Matrix.toInvertible oneNonzero (Matrix.fromInvertible oneNonzero twoNonzero matrix) = matrix :=
  ⟨Matrix.fromInvertible_toInvertible oneNonzero twoNonzero value,
    Matrix.toInvertible_fromInvertible oneNonzero twoNonzero matrix⟩

/-- The facade supplies complete group operations on the original invertible matrices. -/
private theorem invertible_matrix_group {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (first second third : Matrix2.Invertible K) :
    Matrix2.Invertible.mul (Matrix2.Invertible.mul first second) third =
        Matrix2.Invertible.mul first (Matrix2.Invertible.mul second third) ∧
      Matrix2.Invertible.mul (Matrix2.Invertible.identity oneNonzero) first = first ∧
      Matrix2.Invertible.mul first (Matrix2.Invertible.identity oneNonzero) = first ∧
      Matrix2.Invertible.mul first (Matrix2.Invertible.inverse first) = Matrix2.Invertible.identity oneNonzero ∧
      Matrix2.Invertible.mul (Matrix2.Invertible.inverse first) first = Matrix2.Invertible.identity oneNonzero :=
  ⟨Matrix2.Invertible.mul_assoc first second third, Matrix2.Invertible.identity_mul oneNonzero first,
    Matrix2.Invertible.mul_identity oneNonzero first, Matrix2.Invertible.mul_inverse oneNonzero first,
    Matrix2.Invertible.inverse_mul oneNonzero first⟩

/-- The source Lorentz action is the onto projective invertible-matrix homomorphism with exact scalar fibers. -/
private theorem projective_matrix_correspondence {K : Type*} [ExplicitField K] [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) (left right : Matrix2.Invertible K) :
    Rotations.Ternary.Lorentz.matrixRotation oneNonzero twoNonzero
        (Rotations.Ternary.Lorentz.rotationMatrixRepresentative oneNonzero twoNonzero rotation) = rotation ∧
      Rotations.Ternary.Lorentz.matrixRotation oneNonzero twoNonzero (Matrix2.Invertible.mul left right) =
        SpecialOrthogonal.mul (Rotations.Ternary.Lorentz.matrixRotation oneNonzero twoNonzero left)
          (Rotations.Ternary.Lorentz.matrixRotation oneNonzero twoNonzero right) ∧
      (Rotations.Ternary.Lorentz.matrixRotation oneNonzero twoNonzero left =
        Rotations.Ternary.Lorentz.matrixRotation oneNonzero twoNonzero right ↔ left.Equivalent right) :=
  ⟨Rotations.Ternary.Lorentz.matrixRotation_rotationMatrixRepresentative oneNonzero twoNonzero rotation,
    Rotations.Ternary.Lorentz.matrixRotation_mul oneNonzero twoNonzero left right,
    Rotations.Ternary.Lorentz.matrixRotation_eq_iff_equivalent oneNonzero twoNonzero left right⟩

/-- A retained finite splitting certificate enumerates and counts every original Lorentz rotation. -/
private theorem finite_lorentz_rotation_count {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) :
    let split := Quaternion.SplitMatrix.finiteSplit presentation
    (Rotations.Ternary.Lorentz.finiteRotations oneNonzero presentation split).Nodup ∧
      rotation ∈ Rotations.Ternary.Lorentz.finiteRotations oneNonzero presentation split ∧
      (Rotations.Ternary.Lorentz.finiteRotations oneNonzero presentation split).length =
        presentation.carrier.length * (presentation.carrier.length * presentation.carrier.length - 1) :=
  ⟨Rotations.Ternary.Lorentz.finiteRotations_nodup oneNonzero presentation _,
    Rotations.Ternary.Lorentz.finiteRotations_complete oneNonzero presentation _ rotation,
    Rotations.Ternary.Lorentz.finiteRotations_length oneNonzero presentation _⟩

/-- The shared anchor form and quadrance have the paper's literal trace definitions. -/
private theorem anchor_trace_definitions {K : Type*} [ExplicitField K] (left right : Matrix3 K) :
    Antisymmetric.anchorForm left right = -Matrix3.trace (Matrix3.mul left right) / 2 ∧
      Antisymmetric.anchorQuadrance left = Antisymmetric.anchorForm left left := ⟨rfl, rfl⟩

/-- The original Lorentz rotation half spread has the paper's literal trace definition. -/
private theorem half_spread_trace_definition {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation =
      (3 - Matrix3.trace rotation.matrix) / 4 := rfl

/-- The original null Lorentz proportion list has the claimed count and no repeated representatives. -/
private theorem finite_null_lorentz_count {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) :
    (Rotations.Ternary.Lorentz.finiteNullProportions oneNonzero presentation).Nodup ∧
      (Rotations.Ternary.Lorentz.finiteNullProportions oneNonzero presentation).length =
        (presentation.carrier.length + 1) * (presentation.carrier.length + 1) :=
  ⟨Rotations.Ternary.Lorentz.finiteNullProportions_nodup oneNonzero presentation,
    Rotations.Ternary.Lorentz.finiteNullProportions_length oneNonzero presentation⟩

/-- Every listed null proportion has its original nonzero and zero-norm certificates. -/
private theorem finite_null_lorentz_points {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford)
    (member : value ∈ Rotations.Ternary.Lorentz.finiteNullProportions oneNonzero presentation) :
    value ≠ ⟨0, Vector3.zero⟩ ∧ EvenClifford.norm value = 0 :=
  Rotations.Ternary.Lorentz.finiteNullProportions_nonzero_null oneNonzero presentation member

/-- A facade client computes the original nonzero null dihedron's unique finite projective representative. -/
private def finite_null_lorentz_representative {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (value : (TernaryForm.lorentz oneNonzero).EvenClifford) (nonzero : value ≠ ⟨0, Vector3.zero⟩)
    (null : EvenClifford.norm value = 0) :
    Σ' factor : K, Σ' representative : (TernaryForm.lorentz oneNonzero).EvenClifford, factor ≠ 0 ∧
      representative ∈ Rotations.Ternary.Lorentz.finiteNullProportions oneNonzero presentation ∧
      representative = EvenClifford.scale factor value :=
  Rotations.Ternary.Lorentz.finiteNullNormalize oneNonzero presentation value nonzero null

/-- A nonzero scale cannot identify distinct listed original Lorentz null proportions. -/
private theorem finite_null_lorentz_uniqueness {K : Type*} [ExplicitField K]
    (oneNonzero : (1 : K) ≠ 0) (presentation : Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)
    (left right : (TernaryForm.lorentz oneNonzero).EvenClifford)
    (leftMember : left ∈ Rotations.Ternary.Lorentz.finiteNullProportions oneNonzero presentation)
    (rightMember : right ∈ Rotations.Ternary.Lorentz.finiteNullProportions oneNonzero presentation)
    (factor : K) (nonzero : factor ≠ 0) (represents : right = EvenClifford.scale factor left) : left = right :=
  Rotations.Ternary.Lorentz.finiteNullProportions_eq_of_scale oneNonzero presentation leftMember rightMember
    factor nonzero represents

/-- The rational Lorentz group has the exact four-coordinate projective fibers outside its original null quadric. -/
private theorem rational_projective_space_fibers (leftScalar rightScalar : Rational)
    (leftVector rightVector : Vector3 Rational)
    (leftDefined : leftScalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance leftVector ≠ 0)
    (rightDefined : rightScalar ^ 2 + (TernaryForm.lorentz oneNonzero).quadrance rightVector ≠ 0) :
    Rotations.Ternary.Lorentz.proportionRotation oneNonzero leftScalar leftVector leftDefined =
        Rotations.Ternary.Lorentz.proportionRotation oneNonzero rightScalar rightVector rightDefined ↔
      ∃ factor : Rational, factor ≠ 0 ∧ rightScalar = factor * leftScalar ∧
        rightVector = Vector3.scale factor leftVector :=
  Rotations.Ternary.Lorentz.proportionRotation_eq_iff oneNonzero leftScalar rightScalar leftVector rightVector
    leftDefined rightDefined (by decide)

section PrescribedAxes

open Purelib.Geometry.Rotations.Ternary
open Field.Squares
open Field.SquareClass.Basic (SquareClassRepresentative)

variable {K : Type*} [ExplicitField K]

/-- The Lorentz square condition refers to the complete fixed line of the original matrix. -/
private theorem prescribed_axis_geometric_existence [DecidableEq K] (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector3 K) (amount : K) (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0)
    (amountNonzero : amount ≠ 0) (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    (∃ rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal,
      Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation = amount ∧
      ∀ vector : Vector3 K, Matrix3.rowMul vector rotation.matrix = vector ↔
        ∃ factor : K, vector = Vector3.scale factor axis) ↔
      Nonempty (Witness.NonzeroSquare (Lorentz.prescribedAxisSquareValue oneNonzero axis amount)) :=
  Lorentz.prescribedAxis_fixedLine_exists_iff oneNonzero axis amount
    axisNonNull amountNonzero amountNotOne twoNonzero

/-- The Lorentz full-spread condition uses the same retained axis quadrance. -/
private theorem prescribed_axis_spread_condition (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector3 K) (amount : K) (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (Witness.NonzeroSquare (Lorentz.prescribedAxisSquareValue oneNonzero axis amount)) ↔
      Nonempty (Witness.NonzeroSquare ((TernaryForm.lorentz oneNonzero).quadrance axis *
        (4 * amount * (1 - amount)))) :=
  Lorentz.prescribedAxis_square_iff_spreadSquare oneNonzero axis amount twoNonzero

/-- Every retained Lorentz candidate has one of the two distinct inverse matrices computed from the original root. -/
private theorem prescribed_axis_exact_pair [DecidableEq K] (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (Lorentz.prescribedAxisSquareValue oneNonzero axis amount))
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) (candidate : Lorentz.PrescribedAxisRotation oneNonzero axis amount) :
    let positive := Lorentz.prescribedAxisRotationOfSquare oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero
    let negative := Lorentz.prescribedAxisRotationOfSquare oneNonzero axis amount certificate.neg
      axisNonNull amountNotOne twoNonzero
    positive.rotation.matrix ≠ negative.rotation.matrix ∧
      SpecialOrthogonal.inverse positive.rotation = negative.rotation ∧
      (candidate.rotation.matrix = positive.rotation.matrix ∨
        candidate.rotation.matrix = negative.rotation.matrix) :=
  ⟨Lorentz.prescribedAxisRotation_pair_distinct oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero,
    Lorentz.prescribedAxisRotation_pair_inverse oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero,
    candidate.matrix_eq_pair oneNonzero certificate axisNonNull amountNotOne twoNonzero⟩

/-- The constructor retains the original root-derived scale, requested amount and exact computed anchor. -/
private theorem prescribed_axis_constructor (oneNonzero : (1 : K) ≠ 0) (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (Lorentz.prescribedAxisSquareValue oneNonzero axis amount))
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    let candidate := Lorentz.prescribedAxisRotationOfSquare oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero
    candidate.anchorScale = certificate.root / ((TernaryForm.lorentz oneNonzero).quadrance axis * (1 - amount)) ∧
      Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) candidate.rotation = amount ∧
      Lorentz.rotationAnchorVector oneNonzero candidate.rotation candidate.anchorDefined =
        Vector3.scale candidate.anchorScale axis :=
  ⟨rfl, (Lorentz.prescribedAxisRotationOfSquare oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero).halfSpread_eq,
    (Lorentz.prescribedAxisRotationOfSquare oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero).anchor_eq⟩

/-- The half-spread-one endpoint is the original unique half turn about the supplied non-null fixed axis. -/
private theorem prescribed_axis_half_turn [DecidableEq K] (oneNonzero : (1 : K) ≠ 0) (axis : Vector3 K)
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (halfSpreadOne : Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation = 1)
    (axisFixed : Matrix3.rowMul axis rotation.matrix = axis) :
    Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero)
        ((TernaryForm.lorentz oneNonzero).halfTurnRotation axis axisNonNull) = 1 ∧
      rotation = (TernaryForm.lorentz oneNonzero).halfTurnRotation axis axisNonNull :=
  ⟨Lorentz.prescribedAxis_halfTurn_halfSpread oneNonzero axis axisNonNull twoNonzero,
    Lorentz.prescribedAxis_halfTurn_unique oneNonzero axis axisNonNull rotation twoNonzero halfSpreadOne axisFixed⟩

/-- The rational spacelike axis and half spread minus one eighth have the retained root three eighths. -/
private def rational_boost_axis_square :
    Witness.NonzeroSquare (Lorentz.prescribedAxisSquareValue oneNonzero
      (⟨0, 0, 1⟩ : Vector3 Rational) (-(1 : Rational) / 8)) where
  root := 3 / 8
  rootNonzero := by decide
  square := by decide

/-- The negative of the retained root constructs the original introductory boost with its axis and half spread. -/
private def rational_prescribed_boost : Lorentz.PrescribedAxisRotation oneNonzero
    (⟨0, 0, 1⟩ : Vector3 Rational) (-(1 : Rational) / 8) :=
  Lorentz.prescribedAxisRotationOfSquare oneNonzero ⟨0, 0, 1⟩ (-(1 : Rational) / 8)
    rational_boost_axis_square.neg (by decide) (by decide) (by decide)

/-- The negative-root scale is one third and its matrix is exactly the original introductory boost action. -/
private theorem rational_prescribed_boost_agreement :
    rational_prescribed_boost.anchorScale = ((1 : Rational) / 3) ∧
      rational_prescribed_boost.rotation.matrix = NonNullEvenClifford.actionMatrix introductoryValue := by
  constructor
  · decide
  · calc
      rational_prescribed_boost.rotation.matrix =
          (⟨5 / 4, 3 / 4, 0, 3 / 4, 5 / 4, 0, 0, 0, 1⟩ : Matrix3 Rational) := by decide
      _ = NonNullEvenClifford.actionMatrix introductoryValue := introductory_action.symm

/-- The facade supplies arithmetic splitting for the original rotation and its complete non-null fixed axis. -/
private theorem arithmetic_splitting [DecidableEq K] (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector3 K) (amount : K) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0)
    (halfSpread : Cayley.TernaryForm.rotationHalfSpread (TernaryForm.lorentz oneNonzero) rotation = amount)
    (fixedLine : ∀ vector : Vector3 K, Matrix3.rowMul vector rotation.matrix = vector ↔
      ∃ factor : K, vector = Vector3.scale factor axis) :
    (∃ point : K, point ≠ 1 ∧ Nonempty (Matrix3.RowEigenvector rotation.matrix point)) ↔
      ∃ root : K, root ^ 2 = -(TernaryForm.lorentz oneNonzero).quadrance axis :=
  Lorentz.arithmetic_splitting oneNonzero axis amount rotation
    axisNonNull amountNonzero amountNotOne twoNonzero halfSpread fixedLine

/-- The facade supplies the literal discriminant and its negative-axis square class. -/
private theorem arithmetic_discriminant [DecidableEq K] (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector3 K) (amount : K) (candidate : Lorentz.PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Reciprocal.discriminant (1 - 2 * amount) = -16 * amount * (1 - amount) ∧
      SquareClassRepresentative.Equivalent
        (⟨-(TernaryForm.lorentz oneNonzero).quadrance axis, ExplicitField.neg_ne_zero_of_ne_zero axisNonNull⟩ :
          SquareClassRepresentative K)
        ⟨Reciprocal.discriminant (1 - 2 * amount),
          Lorentz.discriminant_halfSpread_nonzero amount amountNonzero amountNotOne twoNonzero⟩ :=
  ⟨Lorentz.discriminant_halfSpread amount,
    candidate.discriminant_squareClass oneNonzero axisNonNull amountNonzero amountNotOne twoNonzero⟩

/-- The computed split pair has two distinct nontrivial eigenvalues and actual eigenvectors of the original matrix. -/
private theorem split_eigenvectors [DecidableEq K] (oneNonzero : (1 : K) ≠ 0)
    (axis : Vector3 K) (amount : K) (candidate : Lorentz.PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (TernaryForm.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0)
    (axisSquare : Witness.NonzeroSquare (-(TernaryForm.lorentz oneNonzero).quadrance axis)) :
    let pair := candidate.splitEigenvectors oneNonzero axisNonNull amountNonzero amountNotOne twoNonzero axisSquare
    let positive := Reciprocal.positiveRoot (1 - 2 * amount) pair.1
    let negative := Reciprocal.negativeRoot (1 - 2 * amount) pair.1
    positive ≠ negative ∧ positive ≠ 1 ∧ negative ≠ 1 ∧
      Matrix3.rowMul pair.2.1.value candidate.rotation.matrix = Vector3.scale positive pair.2.1.value ∧
      Matrix3.rowMul pair.2.2.value candidate.rotation.matrix = Vector3.scale negative pair.2.2.value := by
  let pair := candidate.splitEigenvectors oneNonzero axisNonNull amountNonzero amountNotOne twoNonzero axisSquare
  have positiveRoot : Reciprocal.eval (1 - 2 * amount) (Reciprocal.positiveRoot (1 - 2 * amount) pair.1) = 0 :=
    (Reciprocal.root_iff_eq_roots _ pair.1 twoNonzero _).mpr (Or.inl rfl)
  have negativeRoot : Reciprocal.eval (1 - 2 * amount) (Reciprocal.negativeRoot (1 - 2 * amount) pair.1) = 0 :=
    (Reciprocal.root_iff_eq_roots _ pair.1 twoNonzero _).mpr (Or.inr rfl)
  exact ⟨Reciprocal.roots_distinct _ pair.1 twoNonzero,
    Lorentz.reciprocal_root_ne_one amount _ amountNonzero twoNonzero positiveRoot,
    Lorentz.reciprocal_root_ne_one amount _ amountNonzero twoNonzero negativeRoot,
    pair.2.1.equation, pair.2.2.equation⟩

/-- The facade factors the actual characteristic polynomial using the same retained discriminant certificate. -/
private theorem split_characteristic (oneNonzero : (1 : K) ≠ 0) (axis : Vector3 K) (amount : K)
    (candidate : Lorentz.PrescribedAxisRotation oneNonzero axis amount)
    (certificate : Witness.NonzeroSquare (Reciprocal.discriminant (1 - 2 * amount)))
    (twoNonzero : (2 : K) ≠ 0) (point : K) :
    Matrix3.characteristicValue candidate.rotation.matrix point =
      (point - 1) * (point - Reciprocal.positiveRoot (1 - 2 * amount) certificate) *
        (point - Reciprocal.negativeRoot (1 - 2 * amount) certificate) :=
  candidate.characteristicValue_split oneNonzero certificate twoNonzero point

/-- The introductory rational boost's retained split certificate computes roots two and one half. -/
private theorem rational_boost_split_roots :
    let pair := rational_prescribed_boost.splitEigenvectors oneNonzero (by decide) (by decide) (by decide) (by decide)
      (⟨1, by decide, by decide⟩ : Witness.NonzeroSquare
        (-(TernaryForm.lorentz oneNonzero).quadrance (⟨0, 0, 1⟩ : Vector3 Rational)))
    pair.1.root = (3 : Rational) / 2 ∧
      Reciprocal.positiveRoot (1 - 2 * (-(1 : Rational) / 8)) pair.1 = 2 ∧
      Reciprocal.negativeRoot (1 - 2 * (-(1 : Rational) / 8)) pair.1 = 1 / 2 := by decide

/-- The spacelike rational example preserves time orientation and has no nontrivial rational eigenvalues. -/
private theorem rational_spacelike_nonsplit :
    Ternary.Lorentz.firstAxisRotation.anchorScale = (1 : Rational) / 4 ∧
      0 < Ternary.Lorentz.firstAxisRotation.rotation.matrix.tt ∧
      ¬ ∃ point : Rational, point ≠ 1 ∧
        Nonempty (Matrix3.RowEigenvector Ternary.Lorentz.firstAxisRotation.rotation.matrix point) :=
  ⟨Ternary.Lorentz.firstAxisRotation_coordinates.1,
    Ternary.Lorentz.firstAxisRotation_timePositive, Ternary.Lorentz.firstAxisRotation_no_nontrivial_eigenvalue⟩

end PrescribedAxes

/-- The original Lorentz ray representatives retain associative multiplication and exact two-sided inverse laws. -/
private theorem lorentz_ray_group {F : Type*} [RayOrderedExplicitField F] (oneNonzero : (1 : F) ≠ 0)
    (first second third : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford) :
    NonNullEvenClifford.mul (NonNullEvenClifford.mul first second) third =
        NonNullEvenClifford.mul first (NonNullEvenClifford.mul second third) ∧
      NonNullEvenClifford.mul first (NonNullEvenClifford.inverse first) =
        NonNullEvenClifford.identity (TernaryForm.lorentz oneNonzero) ∧
      NonNullEvenClifford.mul (NonNullEvenClifford.inverse first) first =
        NonNullEvenClifford.identity (TernaryForm.lorentz oneNonzero) :=
  ⟨NonNullEvenClifford.mul_assoc first second third,
    NonNullEvenClifford.mul_inverse first, NonNullEvenClifford.inverse_mul first⟩

/-- Multiplication and the computed original inverse preserve positive Lorentz ray equivalence. -/
private theorem lorentz_ray_operations {F : Type*} [RayOrderedExplicitField F] (oneNonzero : (1 : F) ≠ 0)
    (left left' right right' : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford)
    (leftEq : NonNullEvenClifford.RayEquivalent left left')
    (rightEq : NonNullEvenClifford.RayEquivalent right right') :
    NonNullEvenClifford.RayEquivalent (NonNullEvenClifford.mul left right)
        (NonNullEvenClifford.mul left' right') ∧
      NonNullEvenClifford.RayEquivalent (NonNullEvenClifford.inverse left) (NonNullEvenClifford.inverse left') ∧
      NonNullEvenClifford.actionRotation (NonNullEvenClifford.inverse left) =
        SpecialOrthogonal.inverse (NonNullEvenClifford.actionRotation left) :=
  ⟨NonNullEvenClifford.mul_respects_rayEquivalent leftEq rightEq,
    NonNullEvenClifford.inverse_respects_rayEquivalent leftEq, NonNullEvenClifford.actionRotation_inverse left⟩

/-- The original Lorentz action covers every rotation with exactly two opposite rays and the two scalar kernel rays. -/
private theorem lorentz_ray_cover {F : Type*} [RayOrderedExplicitField F] (oneNonzero : (1 : F) ≠ 0)
    (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (left right : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford) :
    (∃ value : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford,
      NonNullEvenClifford.actionRotation value = rotation) ∧
      (NonNullEvenClifford.actionRotation left = NonNullEvenClifford.actionRotation right ↔
        NonNullEvenClifford.RayEquivalent left right ∨
          NonNullEvenClifford.RayEquivalent (NonNullEvenClifford.neg left) right) ∧
      ¬ NonNullEvenClifford.RayEquivalent left (NonNullEvenClifford.neg left) ∧
      (NonNullEvenClifford.actionRotation left = SpecialOrthogonal.identity (TernaryForm.lorentz oneNonzero) ↔
        NonNullEvenClifford.RayEquivalent (NonNullEvenClifford.identity (TernaryForm.lorentz oneNonzero)) left ∨
          NonNullEvenClifford.RayEquivalent
            (NonNullEvenClifford.neg (NonNullEvenClifford.identity (TernaryForm.lorentz oneNonzero))) left) :=
  ⟨NonNullEvenClifford.actionRotation_ray_surjective rotation,
    NonNullEvenClifford.actionRotation_eq_iff_rayEquivalent_or_neg left right,
    NonNullEvenClifford.not_rayEquivalent_neg left,
    NonNullEvenClifford.actionRotation_eq_identity_iff_scalar_rays left⟩

/-- Lorentz ray normalization uses the original norm class and has a unique unit representative when one exists. -/
private theorem lorentz_ray_normalization {F : Type*} [RayOrderedExplicitField F] (oneNonzero : (1 : F) ≠ 0)
    (left right : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford)
    (leftNorm : EvenClifford.norm left.toEvenClifford = 1)
    (rightNorm : EvenClifford.norm right.toEvenClifford = 1)
    (sameRay : NonNullEvenClifford.RayEquivalent left right) :
    ((∃ factor : F, 0 < factor ∧ EvenClifford.norm (EvenClifford.scale factor left.toEvenClifford) = 1) ↔
      (NonNullEvenClifford.normClass left).Equivalent ⟨1, oneNonzero⟩) ∧ left = right :=
  ⟨NonNullEvenClifford.ray_unitNormScale_iff left,
    NonNullEvenClifford.eq_of_rayEquivalent_norm_one leftNorm rightNorm sameRay⟩

/-- The original Lorentz inverse has a distinct opposite anchor ray for every nonzero anchor, including null anchors. -/
private theorem inverse_anchor_distinct_ray {F : Type*} [RayOrderedExplicitField F]
    (oneNonzero : (1 : F) ≠ 0) (rotation : (TernaryForm.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0)
    (anchorNonzero : Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation defined ≠ Vector3.zero) :
    ¬ Vector3.RayEquivalent (Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero rotation defined)
      (Rotations.Ternary.Lorentz.rotationAnchorVector oneNonzero (SpecialOrthogonal.inverse rotation)
        (by rw [rotation.anchorDenominator_inverse]; exact defined)) :=
  Rotations.Ternary.Lorentz.rotationAnchorVector_inverse_distinct_ray oneNonzero rotation defined anchorNonzero

/-- The source negative-norm proportion retains its original scalar, axis and non-null certificate. -/
private def negativeNormValue : (TernaryForm.lorentz oneNonzero).NonNullEvenClifford :=
  Matrix.nonNullCoordinates oneNonzero 2 Ternary.Lorentz.first (by decide)

/-- A negative-norm rational ray has a computed two-sided inverse with the same original owner. -/
private theorem negative_norm_ray_inverse :
    EvenClifford.norm negativeNormValue.toEvenClifford = (-8 : Rational) ∧
      (NonNullEvenClifford.inverse negativeNormValue).scalar = -(1 : Rational) / 4 ∧
      (NonNullEvenClifford.inverse negativeNormValue).vector.t = -(1 : Rational) / 8 ∧
      (NonNullEvenClifford.inverse negativeNormValue).vector.r = -(1 : Rational) / 4 ∧
      (NonNullEvenClifford.inverse negativeNormValue).vector.s = -(3 : Rational) / 8 ∧
      EvenClifford.norm (NonNullEvenClifford.inverse negativeNormValue).toEvenClifford = -(1 : Rational) / 8 ∧
      Matrix.toMatrix oneNonzero (NonNullEvenClifford.inverse negativeNormValue).toEvenClifford =
        (⟨1 / 8, 1 / 8, 3 / 8, -5 / 8⟩ : Matrix2 Rational) := by
  decide

end Test.Geometry.Rotations.MinkowskiPublication
