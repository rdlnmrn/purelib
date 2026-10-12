module

import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Geometry.Quadratic.Space3.Ordered
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.Monoid.Int
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Group.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Divisibility
import Purelib.Algebra.Quaternion.Projective.UnitObstruction
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Geometry.Rotations.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Quadratic.Space3.NullVectors
import Purelib.Geometry.Rotations.Axis.Prescribed
import Purelib.Geometry.Rotations.Axis.Recovery
import Purelib.Geometry.Rotations.Cayley.Product
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Geometry.Rotations.Projective.Correspondence
public import Purelib.Geometry.Rotations.Projective.SquareClass
import Purelib.Geometry.Rotations.Spread
public import Purelib.LinearAlgebra.Coordinates3.Rational.Powers
import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.NumberTheory.Recurrence.RationalLucas
public import Purelib.NumberTheory.SquareClass.Rational.Signature
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quaternion.Projective.SquareClass
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat.Fraction (Rational)

open Purelib

open Purelib.Algebra

open Purelib.Algebra.Field

open Purelib.Algebra.Field.SquareClass.Basic

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity

open Purelib.Algebra.Quaternion.Projective.SquareClass

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Quadratic.Space3

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Axis

open Purelib.Geometry.Rotations.Projective.Action

open Purelib.Geometry.Rotations.Projective.Correspondence

open Purelib.Geometry.Rotations.Projective.SquareClass

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

open Purelib.LinearAlgebra.Coordinates3.Rational.Powers

open Purelib.NumberTheory.Recurrence.RationalLucas

open Purelib.NumberTheory.SquareClass.Rational.Signature

section
@[expose] public section

/-!
# Finite-order rational rotations

Finite order is supplied by an explicit positive exponent and a checked
finite matrix-power equation.  The trace calculation below is a direct
three-coordinate Cayley--Hamilton recurrence.  It forms no collection of all
torsion rotations and uses neither complex roots nor cyclotomic polynomials.
-/

namespace Purelib.Geometry.Rotations.Rational.Order.RotationOrder

open Purelib.Data.Int

section

/-- The identity in the stored rotation structure. -/
def identityRotation : Rotations.Basic.Rotation
  Fraction.Rational where
  matrix := Matrix3.identity
  orthogonal := by
    unfold Purelib.LinearAlgebra.Coordinates3.Matrix3.IsOrthogonal
    rw [Matrix3.transpose_identity, Matrix3.identity_mul]
  determinantOne := Matrix3.determinant_identity

/-- Finite recursive powers of one displayed rational rotation. -/
def rotationPow (rotation : Rotations.Basic.Rotation
  Fraction.Rational) : Nat → Rotations.Basic.Rotation Fraction.Rational
  | 0 => identityRotation
  | exponent + 1 => Purelib.Geometry.Rotations.Cayley.Product.rotationProduct
    (rotationPow rotation exponent) rotation

/-- The zeroth retained rotation power has the identity matrix. -/
@[simp] theorem rotationPow_zero (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    (rotationPow rotation 0).matrix = Matrix3.identity := rfl

/-- The successor rotation power has the previous power matrix multiplied by the original rotation. -/
@[simp] theorem rotationPow_succ (rotation :
  Rotations.Basic.Rotation Fraction.Rational)
    (exponent : Nat) :
    (rotationPow rotation (exponent + 1)).matrix =
      Matrix3.mul (rotationPow rotation exponent).matrix rotation.matrix
        :=
  rfl

/-- Adding finite exponents multiplies the retained rotation-power matrices. -/
theorem rotationPow_add_matrix (rotation :
  Rotations.Basic.Rotation Fraction.Rational) (left : Nat) :
    ∀ right : Nat,
      (rotationPow rotation (left + right)).matrix =
        Matrix3.mul (rotationPow rotation left).matrix
          (rotationPow rotation right).matrix
  | 0 => by
      simp only [Nat.add_zero, rotationPow_zero, Matrix3.mul_identity,
        -eq_self, -iff_self] ; rfl
  | right + 1 => by
      rw [Nat.add_succ, rotationPow_succ,
        rotationPow_succ,
        rotationPow_add_matrix rotation left right,
          Matrix3.mul_assoc]

/-- The retained rotation power reads back as the direct finite matrix power. -/
theorem rotationPow_matrix (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    ∀ exponent : Nat,
      (rotationPow rotation exponent).matrix =
        RotationOrder.matrixPow rotation.matrix exponent
  | 0 => rfl
  | exponent + 1 => by
      rw [rotationPow_succ, RotationOrder.matrixPow_succ,
        rotationPow_matrix]

/-- The rational trace parameter of the nontrivial quadratic factor of the rotation characteristic polynomial. -/
def traceParameter (rotation : Rotations.Basic.Rotation
  Fraction.Rational) : Fraction.Rational :=
  Matrix3.trace rotation.matrix - 1

/-- Cayley--Hamilton for a rotation, written as a displayed cubic matrix identity and derived from the stored transpose
inverse. -/
theorem rotation_cube (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    RotationOrder.matrixPow rotation.matrix 3 =
      Matrix3.add
        (Matrix3.sub
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (RotationOrder.matrixPow rotation.matrix 2))
          (Matrix3.scale (Matrix3.trace rotation.matrix) rotation.matrix))
        Matrix3.identity := by
  have multiplied := congrArg
    (fun matrix => Matrix3.mul matrix rotation.matrix)
    (Recovery.rotation_square_sub_transpose rotation)
  have differenceIdentity :
      Matrix3.sub (RotationOrder.matrixPow rotation.matrix 3) Matrix3.identity =
        Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub (RotationOrder.matrixPow rotation.matrix 2) rotation.matrix) := by
    calc
      Matrix3.sub (RotationOrder.matrixPow rotation.matrix 3) Matrix3.identity =
          Matrix3.mul
            (Matrix3.sub
              (Matrix3.mul rotation.matrix rotation.matrix)
              (Matrix3.transpose rotation.matrix)) rotation.matrix := by
        rw [Matrix3.mul_sub_left, Recovery.transpose_mul_rotation]
        rw [RotationOrder.matrixPow_three]
      _ = Matrix3.mul
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (Matrix3.sub rotation.matrix Matrix3.identity))
          rotation.matrix := multiplied
      _ = Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub (RotationOrder.matrixPow rotation.matrix 2) rotation.matrix) := by
        rw [Matrix3.mul_scale_left, Matrix3.mul_sub_left,
          Matrix3.identity_mul]
        rw [RotationOrder.matrixPow_two]
  calc
    RotationOrder.matrixPow rotation.matrix 3 =
        Matrix3.add
          (Matrix3.sub (RotationOrder.matrixPow rotation.matrix 3) Matrix3.identity)
          Matrix3.identity := by
      apply Matrix3.ext <;>
        unfold Matrix3.add Matrix3.sub Matrix3.identity <;> ring1
    _ = Matrix3.add
        (Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub (RotationOrder.matrixPow rotation.matrix 2) rotation.matrix))
        Matrix3.identity := by rw [differenceIdentity]
    _ = Matrix3.add
        (Matrix3.sub
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (RotationOrder.matrixPow rotation.matrix 2))
          (Matrix3.scale (Matrix3.trace rotation.matrix) rotation.matrix))
        Matrix3.identity := by
      apply Matrix3.ext <;>
        unfold Matrix3.add Matrix3.sub Matrix3.scale <;> ring1

/-- Rotation matrix powers satisfy the cubic Cayley–Hamilton recurrence with the original trace. -/
theorem rotationPow_third_recurrence (rotation :
  Rotations.Basic.Rotation Fraction.Rational)
    (index : Nat) :
    RotationOrder.matrixPow rotation.matrix (index + 3) =
      Matrix3.add
        (Matrix3.sub
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (RotationOrder.matrixPow rotation.matrix (index + 2)))
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (RotationOrder.matrixPow rotation.matrix (index + 1))))
        (RotationOrder.matrixPow rotation.matrix index) := by
  calc
    RotationOrder.matrixPow rotation.matrix (index + 3) =
        Matrix3.mul (RotationOrder.matrixPow rotation.matrix index)
          (RotationOrder.matrixPow rotation.matrix 3) := by
      exact RotationOrder.matrixPow_add rotation.matrix index 3
    _ = Matrix3.mul (RotationOrder.matrixPow rotation.matrix index)
        (Matrix3.add
          (Matrix3.sub
            (Matrix3.scale (Matrix3.trace rotation.matrix)
              (RotationOrder.matrixPow rotation.matrix 2))
            (Matrix3.scale (Matrix3.trace rotation.matrix) rotation.matrix))
          Matrix3.identity) := by rw [rotation_cube]
    _ = Matrix3.add
        (Matrix3.sub
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (RotationOrder.matrixPow rotation.matrix (index + 2)))
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (RotationOrder.matrixPow rotation.matrix (index + 1))))
        (RotationOrder.matrixPow rotation.matrix index) := by
      rw [Matrix3.mul_add_right, Matrix3.mul_sub_right,
        Matrix3.mul_scale_right, Matrix3.mul_scale_right,
        Matrix3.mul_identity,
        ← RotationOrder.matrixPow_add rotation.matrix index 2,
        ← RotationOrder.matrixPow_succ rotation.matrix index]

/-- Traces of rotation matrix powers satisfy the induced third-order scalar recurrence. -/
theorem trace_rotationPow_recurrence (rotation :
  Rotations.Basic.Rotation Fraction.Rational)
    (index : Nat) :
    Matrix3.trace (RotationOrder.matrixPow rotation.matrix (index + 3)) =
      Matrix3.trace rotation.matrix *
          Matrix3.trace (RotationOrder.matrixPow rotation.matrix (index + 2)) -
        Matrix3.trace rotation.matrix *
          Matrix3.trace (RotationOrder.matrixPow rotation.matrix (index + 1)) +
        Matrix3.trace (RotationOrder.matrixPow rotation.matrix index) := by
  rw [rotationPow_third_recurrence, Matrix3.trace_add,
    Purelib.LinearAlgebra.Coordinates3.Matrix3.trace_sub_rational,
    Matrix3.trace_scale, Matrix3.trace_scale]

/-- The trace of every supplied finite power is `1` plus the finite Lucas recurrence of the quadratic trace parameter.
-/
theorem trace_rotationPow (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    ∀ exponent : Nat,
      Matrix3.trace (RotationOrder.matrixPow rotation.matrix exponent) =
        1 + RotationOrder.traceLucas exponent (traceParameter rotation) := by
  intro exponent
  induction exponent using Nat.strong_induction_on with
  | h exponent inductionHypothesis =>
      rcases exponent with _ | _ | index
      · simp only [RotationOrder.matrixPow_zero, Matrix3.trace_identity,
          RotationOrder.traceLucas_zero]
        ring1
      · simp only [RotationOrder.matrixPow_succ, RotationOrder.matrixPow_zero,
          Matrix3.identity_mul, traceParameter]
        change Matrix3.trace rotation.matrix =
          1 + (Matrix3.trace rotation.matrix - 1)
        ring1
      · rcases index with _ | index
        · rw [RotationOrder.matrixPow_succ, RotationOrder.matrixPow_succ, RotationOrder.matrixPow_zero,
            Matrix3.identity_mul, Matrix3.trace_square,
            Spread.principalTrace_rotation]
          change Matrix3.trace rotation.matrix ^ 2 -
              2 * Matrix3.trace rotation.matrix =
            1 + RotationOrder.traceLucas 2 (traceParameter rotation)
          rw [RotationOrder.traceLucas_two]
          unfold traceParameter
          ring1
        · have atIndex := inductionHypothesis index (by omega)
          have atFirst := inductionHypothesis (index + 1) (by omega)
          have atSecond := inductionHypothesis (index + 2) (by omega)
          rw [trace_rotationPow_recurrence rotation index,
            atIndex, atFirst, atSecond,
            RotationOrder.traceLucas_third index (traceParameter rotation)]
          unfold traceParameter
          ring1

set_option genInjectivity false in
/-- A supplied exact-order certificate retains the finite power table below the positive exponent as executable data. -/
structure ExactOrderCertificate (rotation :
  Rotations.Basic.Rotation Fraction.Rational)
    (order : Nat) where
  /-- The retained exact order is a positive natural number. -/ orderPositive : 0 < order
  /-- The cached rotation at the retained order. -/ power : Rotations.Basic.Rotation Fraction.Rational
  /-- The cached rotation is exactly the original rotation raised to the retained order. -/ power_eq : power =
    rotationPow rotation order
  /-- The cached order-th rotation has the identity matrix. -/ power_identity : power.matrix = Matrix3.identity
  /-- The cached finite table of powers below the retained order. -/ smallerPowers : List (Rotations.Basic.Rotation
    Fraction.Rational)
  /-- The retained table is exactly the original rotation evaluated on the range below the order. -/ smallerPowers_eq :
    smallerPowers = (List.range order).map (rotationPow rotation)
  /-- Every positive exponent below the retained order has a nonidentity matrix. -/ smaller_nonidentity : ∀ exponent, 0
    < exponent → exponent < order →
    (rotationPow rotation exponent).matrix ≠ Matrix3.identity

constructive_injectivity ExactOrderCertificate

/-- The matrix of the original rotation at the certified exact order is the identity. -/
theorem ExactOrderCertificate.power_matrix_identity
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order) :
    (rotationPow rotation order).matrix = Matrix3.identity := by
  rw [← certificate.power_eq]
  exact certificate.power_identity

/-- A supplied identity power forces the finite quadratic trace recurrence to return the trace `2` of the two non-axis
coordinates. -/
theorem ExactOrderCertificate.traceLucas_eq_two
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order) :
    RotationOrder.traceLucas order (traceParameter rotation) = 2 := by
  have traced := congrArg Matrix3.trace certificate.power_matrix_identity
  rw [rotationPow_matrix,
    trace_rotationPow,
    Matrix3.trace_identity] at traced
  exact (Group.add_left_cancel (common := (1 : Fraction.Rational))) (by
    calc
      1 + RotationOrder.traceLucas order (traceParameter rotation) = 3
        := traced
      _ = 1 + 2 := by ring1)

/-- The rational trace parameter of a supplied finite-order rotation is an integer.

The supplied exponent and finite recurrence retain the original rational
trace parameter. Its stored Bézout certificate forces its denominator to be one. -/
theorem ExactOrderCertificate.traceParameter_isInteger
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order) :
    ∃ numerator : Int, traceParameter rotation = (numerator :
      Fraction.Rational) := by
  let trace := traceParameter rotation
  let numerator := (Fraction.Basic.representative trace).num
  let denominator := (Fraction.Basic.representative trace).den
  have cleared := Fraction.Cast.representative_mul_den trace
  change trace * (denominator : Fraction.Rational) = (numerator : Fraction.Rational) at cleared
  have homogeneousCast := RotationOrder.homogeneousTraceLucas_cast trace numerator
    denominator cleared order
  have recurrenceRoot : RotationOrder.traceLucas order trace = 2 :=
    certificate.traceLucas_eq_two
  rw [recurrenceRoot] at homogeneousCast
  have homogeneousEquation :
      RotationOrder.homogeneousTraceLucas numerator denominator order =
        2 * (denominator : Int) ^ order := by
    apply Fraction.Cast.Compatibility.intCast_injective_direct
    rw [Ring.IntCast.intCast_mul, Ring.IntCast.intCast_pow,
      Int.cast_natCast]
    calc
      (RotationOrder.homogeneousTraceLucas numerator denominator order : Fraction.Rational) =
          (denominator : Fraction.Rational) ^ order * 2 := homogeneousCast
      _ = 2 * (denominator : Fraction.Rational) ^ order := by ring1
  have denominatorDividesHomogeneous :
      (denominator : Int) ∣
        RotationOrder.homogeneousTraceLucas numerator denominator order := by
    rcases order with _ | previous
    · exact (Nat.not_lt_zero 0 certificate.orderPositive).elim
    · refine ⟨2 * (denominator : Int) ^ previous, ?_⟩
      rw [homogeneousEquation, pow_succ]
      ring1
  have congruence := RotationOrder.denominator_dvd_homogeneousTraceLucas_sub_pow
    numerator denominator order certificate.orderPositive
  have denominatorDividesNumeratorPowerInteger :
      (denominator : Int) ∣ numerator ^ order := by
    have difference : (denominator : Int) ∣
        RotationOrder.homogeneousTraceLucas numerator denominator order -
          (RotationOrder.homogeneousTraceLucas numerator denominator order - numerator ^ order) := by
      obtain ⟨firstFactor, firstEquation⟩ := denominatorDividesHomogeneous
      obtain ⟨secondFactor, secondEquation⟩ := congruence
      refine ⟨firstFactor - secondFactor, ?_⟩
      rw [secondEquation, firstEquation]
      ring1
    have differenceValue :
        RotationOrder.homogeneousTraceLucas numerator denominator order -
            (RotationOrder.homogeneousTraceLucas numerator denominator order -
              numerator ^ order) = numerator ^ order := by ring1
    rw [differenceValue] at difference
    exact difference
  have denominatorDividesNumeratorPower :
      denominator ∣ numerator.natAbs ^ order := by
    have absolute := Divisibility.natAbs_dvd_natAbs_of_dvd
      denominatorDividesNumeratorPowerInteger
    simpa only [Int.natAbs_natCast, Int.Arithmetic.natAbs_pow] using absolute
  have denominatorDividesOne : denominator ∣ 1 := by
    rcases (Fraction.Basic.representative trace).reduced with
      ⟨coprime⟩
    apply coprime.symm.dvd_of_dvd_mul_right_pow order
    simpa only [Nat.one_mul] using denominatorDividesNumeratorPower
  have denominatorOne : denominator = 1 :=
    Nat.Divisibility.eq_one_of_dvd_one denominatorDividesOne
  refine ⟨numerator, ?_⟩
  simpa only [denominatorOne, Nat.cast_one, mul_one] using cleared

/-! ## Exact rational trace bounds -/

section
variable {K : Type*} [ExplicitField K]

/-- The canonical quaternion representative has the original rotation's half spread. -/
private theorem ofRotation_halfSpread
  (rotation : Rotations.Basic.Rotation Fraction.Rational) :
    Spread.halfSpread
        (NonNullProportion.rotation (RotationProportion.ofRotation rotation (by decide))) =
      Spread.halfSpread rotation := by
  let twoNonzero : (2 : Fraction.Rational) ≠ 0 := by decide
  have matrixEqual :=
    RotationProportion.ofRotation_rotationMatrix rotation twoNonzero
  change
    (NonNullProportion.rotation (RotationProportion.ofRotation rotation twoNonzero)).matrix =
      rotation.matrix at matrixEqual
  unfold Spread.halfSpread
  rw [matrixEqual]

end

/-- The half spread of a rational rotation is nonnegative, proved directly from the three displayed rational squares in
its canonical projective representative. -/
theorem halfSpread_nonnegative (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    0 ≤ Spread.halfSpread rotation := by
  let proportion := RotationProportion.ofRotation rotation (by decide)
  have quotientNonnegative :
      0 ≤ proportion.vector.quadrance /
        proportion.toProportion.norm :=
    Fraction.Order.Field.div_nonneg_direct
      ((fun (vector : Purelib.LinearAlgebra.Coordinates3.Vector Rational) =>
        (Purelib.Geometry.Quadratic.Space3.Ordered.RationalFieldClaims.vector_quadrance_nonnegative vector : 0 ≤
        vector.quadrance)) proportion.vector)
      (TheoremSixtyTwo.nonNullProportion_norm_positive proportion).le
  calc
    0 ≤ Spread.halfSpread (NonNullProportion.rotation proportion) := by
      rw [NonNullProportion.halfSpread_rotation proportion (by decide)]
      exact quotientNonnegative
    _ = Spread.halfSpread rotation :=
      ofRotation_halfSpread rotation

/-- The complementary half spread is nonnegative, again from one displayed rational square and the positive cached norm.
-/
theorem one_sub_halfSpread_nonnegative (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    0 ≤ 1 - Spread.halfSpread rotation := by
  let proportion := RotationProportion.ofRotation rotation (by decide)
  have quotientNonnegative :
      0 ≤ proportion.scalar ^ 2 /
        proportion.toProportion.norm :=
    Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct proportion.scalar)
      (TheoremSixtyTwo.nonNullProportion_norm_positive proportion).le
  calc
    0 ≤ 1 - Spread.halfSpread (NonNullProportion.rotation proportion) := by
      rw [NonNullProportion.one_sub_halfSpread_rotation proportion
        (by decide)]
      exact quotientNonnegative
    _ = 1 - Spread.halfSpread rotation := by
      rw [ofRotation_halfSpread rotation]

/-- The quadratic trace parameter is the affine half-spread coordinate `2(1-2h)`. -/
theorem traceParameter_eq_halfSpread (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    traceParameter rotation = 2 * (1 - 2 * Spread.halfSpread rotation) := by
  have relation := Recovery.one_add_trace_eq_four_mul_one_sub_halfSpread rotation
    (by decide)
  unfold traceParameter
  calc
    Matrix3.trace rotation.matrix - 1 =
        (1 + Matrix3.trace rotation.matrix) - 2 := by ring1
    _ = 4 * (1 - Spread.halfSpread rotation) - 2 := by rw [relation]
    _ = 2 * (1 - 2 * Spread.halfSpread rotation) := by ring1

/-- Exact rational bounds for the trace parameter, with no transfer through the reals. -/
theorem traceParameter_bounds (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    (-2 : Fraction.Rational) ≤ traceParameter rotation ∧
      traceParameter rotation ≤ 2 := by
  have spreadNonnegative := halfSpread_nonnegative rotation
  have complementNonnegative := one_sub_halfSpread_nonnegative rotation
  constructor
  · apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    rw [traceParameter_eq_halfSpread]
    have scaled :
        0 ≤ (4 : Fraction.Rational) * (1 - Spread.halfSpread rotation) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        complementNonnegative
    convert scaled using 1
    all_goals ring1
  · apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    rw [traceParameter_eq_halfSpread]
    have scaled : 0 ≤ (4 : Fraction.Rational) * Spread.halfSpread rotation :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        spreadNonnegative
    convert scaled using 1
    all_goals ring1

/-- A finite-order certificate reduces the integral trace parameter to five explicit values. -/
theorem ExactOrderCertificate.traceParameter_five_cases
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order) :
    ∃ numerator : Int,
      traceParameter rotation = (numerator : Fraction.Rational) ∧
        (numerator = -2 ∨ numerator = -1 ∨ numerator = 0 ∨
          numerator = 1 ∨ numerator = 2) := by
  rcases certificate.traceParameter_isInteger with ⟨numerator, traceEq⟩
  have bounds := traceParameter_bounds rotation
  have lowerCast : ((-2 : Int) : Fraction.Rational) ≤ (numerator : Fraction.Rational) := by
    calc
      ((-2 : Int) : Fraction.Rational) = (-2 : Fraction.Rational) := by ring1
      _ ≤ traceParameter rotation := bounds.1
      _ = (numerator : Fraction.Rational) := traceEq
  have upperCast : (numerator : Fraction.Rational) ≤ ((2 : Int) : Fraction.Rational) := by
    calc
      (numerator : Fraction.Rational) = traceParameter rotation :=
        traceEq.symm
      _ ≤ (2 : Fraction.Rational) := bounds.2
      _ = ((2 : Int) : Fraction.Rational) := by ring1
  have lower : (-2 : Int) ≤ numerator :=
    (Fraction.Cast.Order.intCast_le_intCast_iff_direct (-2) numerator).mp
      lowerCast
  have upper : numerator ≤ (2 : Int) :=
    (Fraction.Cast.Order.intCast_le_intCast_iff_direct numerator 2).mp
      upperCast
  refine ⟨numerator, traceEq, ?_⟩
  omega

/-! ## Five exact finite orders -/

/-- If the finite Lucas recurrence returns `2`, the corresponding displayed matrix power is the identity. The final
separation step is the rational three-square theorem, not a complex eigenvalue argument. -/
theorem matrixPow_eq_identity_of_traceLucas_eq_two
    (rotation : Rotations.Basic.Rotation Fraction.Rational) (exponent : Nat)
    (root : RotationOrder.traceLucas exponent (traceParameter rotation)
      = 2) :
    RotationOrder.matrixPow rotation.matrix exponent = Matrix3.identity := by
  have spreadZero : Spread.halfSpread (rotationPow rotation exponent) =
    0 := by
    unfold Spread.halfSpread
    rw [rotationPow_matrix,
      trace_rotationPow, root]
    decide
  have identity := Prescribed.rotation_eq_identity_of_halfSpread_zero
    NullVectors.rationalSumSquaresSeparate (rotationPow rotation
      exponent) spreadZero
      (by decide)
  rwa [rotationPow_matrix] at identity

/-- Exact minimality bounds the stored order by every other positive identity exponent. -/
theorem ExactOrderCertificate.order_le_of_power_identity
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order candidate : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (candidatePositive : 0 < candidate)
    (candidateIdentity :
      RotationOrder.matrixPow rotation.matrix candidate = Matrix3.identity) :
    order ≤ candidate := by
  by_cases candidateSmaller : candidate < order
  · have nonidentity := certificate.smaller_nonidentity candidate
      candidatePositive candidateSmaller
    rw [rotationPow_matrix] at nonidentity
    exact (nonidentity candidateIdentity).elim
  · omega

section
variable {K : Type*} [ExplicitField K]

/-- A certified exact finite order is one when the trace parameter is two. -/
private theorem
  exactOrder_eq_one_of_traceParameter_eq_two
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (2 : Fraction.Rational)) :
      order = 1 := by
  have candidateRoot : RotationOrder.traceLucas 1 (traceParameter
    rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 1 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 1
      candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  omega

/-- A certified exact finite order is two when the trace parameter is minus two. -/
private theorem
  exactOrder_eq_two_of_traceParameter_eq_neg_two
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (-2 : Fraction.Rational)) :
      order = 2 := by
  have candidateRoot : RotationOrder.traceLucas 2 (traceParameter
    rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 2 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 2
      candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  have actualRoot := certificate.traceLucas_eq_two
  have orderCases : order = 1 ∨ order = 2 := by omega
  rcases orderCases with orderOne | orderTwo
  · subst order
    rw [RotationOrder.traceLucas_one, traceEq] at actualRoot
    exact ((by decide : (-2 : Fraction.Rational) ≠ 2) actualRoot).elim
  · exact orderTwo

/-- A certified exact finite order is three when the trace parameter is minus one. -/
private theorem
  exactOrder_eq_three_of_traceParameter_eq_neg_one
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (-1 : Fraction.Rational)) :
      order = 3 := by
  have candidateRoot : RotationOrder.traceLucas 3 (traceParameter
    rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 3 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 3
      candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  have actualRoot := certificate.traceLucas_eq_two
  have orderCases : order = 1 ∨ order = 2 ∨ order = 3 := by omega
  rcases orderCases with orderOne | orderTwo | orderThree
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 1 (-1 : Fraction.Rational) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 2 (-1 : Fraction.Rational) ≠ 2) actualRoot).elim
  · exact orderThree

/-- A certified exact finite order is four when the trace parameter is zero. -/
private theorem
  exactOrder_eq_four_of_traceParameter_eq_zero
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (0 : Fraction.Rational)) :
      order = 4 := by
  have candidateRoot : RotationOrder.traceLucas 4 (traceParameter
    rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 4 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 4
      candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  have actualRoot := certificate.traceLucas_eq_two
  have orderCases : order = 1 ∨ order = 2 ∨ order = 3 ∨ order = 4 := by
    omega
  rcases orderCases with orderOne | orderTwo | orderThree | orderFour
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 1 (0 : Fraction.Rational) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 2 (0 : Fraction.Rational) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 3 (0 : Fraction.Rational) ≠ 2) actualRoot).elim
  · exact orderFour

/-- A certified exact finite order is six when the trace parameter is one. -/
private theorem
  exactOrder_eq_six_of_traceParameter_eq_one
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (1 : Fraction.Rational)) :
      order = 6 := by
  have candidateRoot : RotationOrder.traceLucas 6 (traceParameter
    rotation) = 2 := by
    rw [traceEq]
    decide
  have orderUpper : order ≤ 6 :=
    certificate.order_le_of_power_identity (by decide)
    (matrixPow_eq_identity_of_traceLucas_eq_two rotation 6
      candidateRoot)
  have orderPositive : 0 < order := certificate.orderPositive
  have actualRoot := certificate.traceLucas_eq_two
  have orderCases : order = 1 ∨ order = 2 ∨ order = 3 ∨ order = 4 ∨
      order = 5 ∨ order = 6 := by omega
  rcases orderCases with orderOne | orderTwo | orderThree | orderFour |
      orderFive | orderSix
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 1 (1 : Fraction.Rational) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 2 (1 : Fraction.Rational) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 3 (1 : Fraction.Rational) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 4 (1 : Fraction.Rational) ≠ 2) actualRoot).elim
  · subst order
    rw [traceEq] at actualRoot
    exact ((by decide : RotationOrder.traceLucas 5 (1 : Fraction.Rational) ≠ 2) actualRoot).elim
  · exact orderSix

/- Proof certificates used by the executable classifier.  The original
exact-order proof helpers remain private. -/

end

/-- A certified exact finite order is one when the trace parameter is two. -/
theorem exactOrder_eq_one_cert {rotation :
  Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (2 : Fraction.Rational)) :
      order = 1 :=
  exactOrder_eq_one_of_traceParameter_eq_two certificate
    traceEq

/-- A certified exact finite order is two when the trace parameter is minus two. -/
theorem exactOrder_eq_two_cert {rotation :
  Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (-2 : Fraction.Rational)) :
      order = 2 :=
  exactOrder_eq_two_of_traceParameter_eq_neg_two
    certificate traceEq

/-- A certified exact finite order is three when the trace parameter is minus one. -/
theorem exactOrder_eq_three_cert {rotation :
  Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (-1 : Fraction.Rational)) :
      order = 3 :=
  exactOrder_eq_three_of_traceParameter_eq_neg_one
    certificate traceEq

/-- A certified exact finite order is four when the trace parameter is zero. -/
theorem exactOrder_eq_four_cert {rotation :
  Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (0 : Fraction.Rational)) :
      order = 4 :=
  exactOrder_eq_four_of_traceParameter_eq_zero
    certificate traceEq

/-- A certified exact finite order is six when the trace parameter is one. -/
theorem exactOrder_eq_six_cert {rotation :
  Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order)
    (traceEq : traceParameter rotation = (1 : Fraction.Rational)) :
      order = 6 :=
  exactOrder_eq_six_of_traceParameter_eq_one certificate
    traceEq

/-- No completed torsion carrier is needed: every supplied exact finite-order certificate has one of the five possible
positive exponents. -/
theorem ExactOrderCertificate.order_five_cases
    {rotation : Rotations.Basic.Rotation Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order) :
    order = 1 ∨ order = 2 ∨ order = 3 ∨ order = 4 ∨ order = 6 := by
  rcases certificate.traceParameter_five_cases with
    ⟨numerator, traceEq, numeratorCases⟩
  rcases numeratorCases with negativeTwo | negativeOne | zero | one | two
  · subst numerator
    have literalTrace : traceParameter rotation = (-2 :
      Fraction.Rational) := by
      calc
        traceParameter rotation = ((-2 : Int) : Fraction.Rational) :=
          traceEq
        _ = (-2 : Fraction.Rational) := by ring1
    exact Or.inr (Or.inl
      (exactOrder_eq_two_of_traceParameter_eq_neg_two
        certificate literalTrace))
  · subst numerator
    have literalTrace : traceParameter rotation = (-1 :
      Fraction.Rational) := by
      calc
        traceParameter rotation = ((-1 : Int) : Fraction.Rational) :=
          traceEq
        _ = (-1 : Fraction.Rational) := by ring1
    exact Or.inr (Or.inr (Or.inl
      (exactOrder_eq_three_of_traceParameter_eq_neg_one
        certificate literalTrace)))
  · subst numerator
    have literalTrace : traceParameter rotation = (0 :
      Fraction.Rational) := by
      calc
        traceParameter rotation = ((0 : Int) : Fraction.Rational) :=
          traceEq
        _ = (0 : Fraction.Rational) := by ring1
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (exactOrder_eq_four_of_traceParameter_eq_zero
        certificate literalTrace))))
  · subst numerator
    have literalTrace : traceParameter rotation = (1 :
      Fraction.Rational) := by
      calc
        traceParameter rotation = ((1 : Int) : Fraction.Rational) :=
          traceEq
        _ = (1 : Fraction.Rational) := by ring1
    exact Or.inr (Or.inr (Or.inr (Or.inr
      (exactOrder_eq_six_of_traceParameter_eq_one
        certificate literalTrace))))
  · subst numerator
    have literalTrace : traceParameter rotation = (2 :
      Fraction.Rational) := by
      calc
        traceParameter rotation = ((2 : Int) : Fraction.Rational) :=
          traceEq
        _ = (2 : Fraction.Rational) := by ring1
    exact Or.inl
      (exactOrder_eq_one_of_traceParameter_eq_two
        certificate literalTrace)

/-! ## Executable value classifier -/

/-- The one canonical projective representative consumed by the value table. -/
def canonicalProportion (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    Projective.Basic.NonNullProportion Fraction.Rational :=
  RotationProportion.ofRotation rotation (by decide)

/-- The canonical quaternion proportion represents the original rotation matrix. -/
theorem canonicalProportion_rotationMatrix (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    (NonNullProportion.rotation (canonicalProportion rotation)).matrix =
      rotation.matrix := by
  exact RotationProportion.ofRotation_rotationMatrix rotation
    (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 2) (by decide) : (2 :
      Rational) ≠ 0)

/-- The canonical proportion has the original rotation's half spread. -/
theorem canonicalProportion_halfSpread (rotation :
  Rotations.Basic.Rotation Fraction.Rational) :
    Spread.halfSpread (NonNullProportion.rotation (canonicalProportion
      rotation)) =
      Spread.halfSpread rotation := by
  unfold Spread.halfSpread
  rw [canonicalProportion_rotationMatrix]

/-- Solving the defining trace equation for one displayed trace parameter. -/
theorem halfSpread_eq_of_traceParameter_eq (rotation :
  Rotations.Basic.Rotation Fraction.Rational)
    (value : Fraction.Rational) (traceEq : traceParameter rotation =
      value) :
    Spread.halfSpread rotation = (2 - value) / 4 := by
  have matrixTrace : Matrix3.trace rotation.matrix = value + 1 := by
    calc
      Matrix3.trace rotation.matrix =
          (Matrix3.trace rotation.matrix - 1) + 1 := by ring1
      _ = value + 1 := by rw [← traceEq]; rfl
  unfold Spread.halfSpread
  rw [matrixTrace]
  apply congrArg (fun numerator : Fraction.Rational => numerator / 4)
  ring1

section
variable {K : Type*} [ExplicitField K]

/-- A non-half-turn spread and an explicit nonzero square factor certify the canonical quadrance class.

The supplied target value is that factor squared times the complementary half spread. -/
private theorem
  canonicalQuadranceClass_equivalent_of_halfSpread
    (rotation : Rotations.Basic.Rotation Fraction.Rational) (spread factor : Fraction.Rational)
    (target : SquareClass.Basic.SquareClassRepresentative Fraction.Rational)
    (spreadEq : Spread.halfSpread rotation = spread)
    (spreadNotOne : spread ≠ 1) (factorNonzero : factor ≠ 0)
    (targetValue : target.value = factor ^ 2 * (1 - spread)) :
    (NonNullProportion.quadranceClass (canonicalProportion
      rotation)).Equivalent target := by
  let proportion := canonicalProportion rotation
  have proportionSpread : Spread.halfSpread (NonNullProportion.rotation proportion) = spread :=
    (canonicalProportion_halfSpread rotation).trans spreadEq
  have scalarNonzero : proportion.scalar ≠ 0 := by
    intro scalarZero
    have spreadOne :=
      (NonNullProportion.halfSpread_rotation_eq_one_iff proportion
        (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 2) (by decide) : (2 :
          Rational) ≠ 0)).2 scalarZero
    apply spreadNotOne
    exact proportionSpread.symm.trans spreadOne
  have affine :=
    NonNullProportion.quadranceClass_equivalent_one_sub_halfSpread
      proportion scalarNonzero (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 2) (by decide) :
        (2 : Rational) ≠ 0)
  apply SquareClassRepresentative.equivalent_trans affine
  refine ⟨factor, factorNonzero, ?_⟩
  change target.value = factor ^ 2 * (1 - Spread.halfSpread (NonNullProportion.rotation proportion))
  rw [proportionSpread]
  exact targetValue

end

/-- Certify the canonical quadrance class from the supplied half spread and nonzero square factor. -/
theorem canonicalQuadranceClass_equivalent_cert
    (rotation : Rotations.Basic.Rotation Fraction.Rational) (spread factor : Fraction.Rational)
    (target : SquareClass.Basic.SquareClassRepresentative Fraction.Rational)
    (spreadEq : Spread.halfSpread rotation = spread)
    (spreadNotOne : spread ≠ 1) (factorNonzero : factor ≠ 0)
    (targetValue : target.value = factor ^ 2 * (1 - spread)) :
    (NonNullProportion.quadranceClass (canonicalProportion
      rotation)).Equivalent target :=
  canonicalQuadranceClass_equivalent_of_halfSpread
    rotation spread factor target
    spreadEq spreadNotOne factorNonzero targetValue

/-- The five branches cache the exact order, trace parameter, half spread, and quotient-free quadrance-class value. The
half-turn branch retains the displayed canonical axis quadrance rather than claiming an unsupported three-square image
classification. -/
inductive Classification (rotation :
  Rotations.Basic.Rotation Fraction.Rational) (order : Nat) : Type
  /-- Order one retains trace parameter two, half spread zero, and the unit square class. -/ | orderOne
      (order_eq : order = 1)
      (traceParameter_eq : traceParameter rotation = 2)
      (halfSpread_eq : Spread.halfSpread rotation = 0)
      (quadranceClass_equivalent :
        (NonNullProportion.quadranceClass (canonicalProportion
          rotation)).Equivalent
          (PositiveSquareClassSignatures.positiveNaturalClass 1 (by decide)))
  /-- Order two retains trace parameter minus two, half spread one, and the canonical null-scalar axis quadrance. -/ |
    orderTwo
      (order_eq : order = 2)
      (traceParameter_eq : traceParameter rotation = -2)
      (halfSpread_eq : Spread.halfSpread rotation = 1)
      (canonicalScalar_eq_zero :
        (canonicalProportion rotation).scalar = 0)
      (quadranceClass_value_eq_axisQuadrance :
        (NonNullProportion.quadranceClass (canonicalProportion
          rotation)).value =
          (canonicalProportion rotation).vector.quadrance)
  /-- Order three retains trace parameter minus one, half spread three quarters, and the unit square class. -/ |
    orderThree
      (order_eq : order = 3)
      (traceParameter_eq : traceParameter rotation = -1)
      (halfSpread_eq : Spread.halfSpread rotation = 3 / 4)
      (quadranceClass_equivalent :
        (NonNullProportion.quadranceClass (canonicalProportion
          rotation)).Equivalent
          (PositiveSquareClassSignatures.positiveNaturalClass 1 (by decide)))
  /-- Order four retains trace parameter zero, half spread one half, and square class two. -/ | orderFour
      (order_eq : order = 4)
      (traceParameter_eq : traceParameter rotation = 0)
      (halfSpread_eq : Spread.halfSpread rotation = 1 / 2)
      (quadranceClass_equivalent :
        (NonNullProportion.quadranceClass (canonicalProportion
          rotation)).Equivalent
          (PositiveSquareClassSignatures.positiveNaturalClass 2 (by decide)))
  /-- Order six retains trace parameter one, half spread one quarter, and square class three. -/ | orderSix
      (order_eq : order = 6)
      (traceParameter_eq : traceParameter rotation = 1)
      (halfSpread_eq : Spread.halfSpread rotation = 1 / 4)
      (quadranceClass_equivalent :
        (NonNullProportion.quadranceClass (canonicalProportion
          rotation)).Equivalent
          (PositiveSquareClassSignatures.positiveNaturalClass 3 (by decide)))

/-- Total finite-order value classification from one supplied exact finite power/minimality certificate. -/
def classify {rotation : Rotations.Basic.Rotation
  Fraction.Rational} {order : Nat}
    (certificate : ExactOrderCertificate rotation order) :
    Classification rotation order := by
  by_cases negativeTwo : traceParameter rotation = (-2 :
    Fraction.Rational)
  · have literalTrace := negativeTwo
    have orderEq :=
      exactOrder_eq_two_cert certificate literalTrace
    have spreadFormula :=
      halfSpread_eq_of_traceParameter_eq rotation (-2) literalTrace
    have spreadEq : Spread.halfSpread rotation = (1 : Fraction.Rational) := by
      calc
        Spread.halfSpread rotation = (2 - (-2 : Fraction.Rational)) / 4 := spreadFormula
        _ = 1 := by decide
    have proportionSpread :
        Spread.halfSpread (NonNullProportion.rotation
          (canonicalProportion rotation)) = 1 :=
      (canonicalProportion_halfSpread rotation).trans spreadEq
    have scalarZero :=
      (NonNullProportion.halfSpread_rotation_eq_one_iff
        (canonicalProportion rotation) (by decide)).1 proportionSpread
    have axisClass := NonNullProportion.quadranceClass_at_infinity
      (canonicalProportion rotation) scalarZero
    exact Geometry.Rotations.Rational.Order.RotationOrder.Classification.orderTwo orderEq literalTrace spreadEq
      scalarZero
      axisClass
  · by_cases negativeOne : traceParameter rotation = (-1 :
      Fraction.Rational)
    · have literalTrace := negativeOne
      have orderEq :=
        exactOrder_eq_three_cert certificate literalTrace
      have spreadFormula :=
        halfSpread_eq_of_traceParameter_eq rotation (-1) literalTrace
      have spreadEq : Spread.halfSpread rotation = (3 / 4 : Fraction.Rational) := by
        calc
          Spread.halfSpread rotation = (2 - (-1 : Fraction.Rational)) / 4 := spreadFormula
          _ = 3 / 4 := by decide
      have classEq := canonicalQuadranceClass_equivalent_cert rotation
        (3 / 4) 2
        (PositiveSquareClassSignatures.positiveNaturalClass 1 (by decide))
        spreadEq (by decide) (by decide) (by decide)
      exact Geometry.Rotations.Rational.Order.RotationOrder.Classification.orderThree orderEq literalTrace spreadEq
        classEq
    · by_cases zero : traceParameter rotation = (0 : Fraction.Rational)
      · have literalTrace := zero
        have orderEq :=
          exactOrder_eq_four_cert certificate literalTrace
        have spreadFormula :=
          halfSpread_eq_of_traceParameter_eq rotation 0 literalTrace
        have spreadEq : Spread.halfSpread rotation = (1 / 2 : Fraction.Rational) := by
          calc
            Spread.halfSpread rotation = (2 - (0 : Fraction.Rational)) / 4 := spreadFormula
            _ = 1 / 2 := by decide
        have classEq := canonicalQuadranceClass_equivalent_cert rotation
          (1 / 2) 2
          (PositiveSquareClassSignatures.positiveNaturalClass 2 (by decide))
          spreadEq (by decide) (by decide) (by decide)
        exact Geometry.Rotations.Rational.Order.RotationOrder.Classification.orderFour orderEq literalTrace spreadEq
          classEq
      · by_cases one : traceParameter rotation = (1 : Fraction.Rational)
        · have literalTrace := one
          have orderEq :=
            exactOrder_eq_six_cert certificate literalTrace
          have spreadFormula :=
            halfSpread_eq_of_traceParameter_eq rotation 1 literalTrace
          have spreadEq : Spread.halfSpread rotation = (1 / 4 : Fraction.Rational) := by
            calc
              Spread.halfSpread rotation = (2 - (1 : Fraction.Rational)) / 4 := spreadFormula
              _ = 1 / 4 := by decide
          have classEq :=
            canonicalQuadranceClass_equivalent_cert rotation
              (1 / 4) 2
              (PositiveSquareClassSignatures.positiveNaturalClass 3 (by decide))
              spreadEq (by decide) (by decide) (by decide)
          exact Geometry.Rotations.Rational.Order.RotationOrder.Classification.orderSix orderEq literalTrace spreadEq
            classEq
        · by_cases two : traceParameter rotation = (2 :
            Fraction.Rational)
          · have literalTrace := two
            have orderEq :=
              exactOrder_eq_one_cert certificate literalTrace
            have spreadFormula :=
              halfSpread_eq_of_traceParameter_eq rotation 2 literalTrace
            have spreadEq : Spread.halfSpread rotation = (0 : Fraction.Rational) := by
              calc
                Spread.halfSpread rotation = (2 - (2 : Fraction.Rational)) / 4 := spreadFormula
                _ = 0 := by decide
            have classEq :=
              canonicalQuadranceClass_equivalent_cert rotation 0 1
                (PositiveSquareClassSignatures.positiveNaturalClass 1
                  (by decide))
                spreadEq (by decide) (by decide) (by decide)
            exact Geometry.Rotations.Rational.Order.RotationOrder.Classification.orderOne orderEq literalTrace spreadEq
              classEq
          · have impossible : False := by
              rcases certificate.traceParameter_five_cases with
                ⟨numerator, traceEq, numeratorCases⟩
              rcases numeratorCases with negTwo | negOne | numeratorZero |
                  numeratorOne | numeratorTwo
              · subst numerator
                apply negativeTwo
                calc
                  traceParameter rotation = ((-2 : Int) :
                    Fraction.Rational) := traceEq
                  _ = (-2 : Fraction.Rational) := by ring1
              · subst numerator
                apply negativeOne
                calc
                  traceParameter rotation = ((-1 : Int) :
                    Fraction.Rational) := traceEq
                  _ = (-1 : Fraction.Rational) := by ring1
              · subst numerator
                apply zero
                calc
                  traceParameter rotation = ((0 : Int) :
                    Fraction.Rational) := traceEq
                  _ = (0 : Fraction.Rational) := by ring1
              · subst numerator
                apply one
                calc
                  traceParameter rotation = ((1 : Int) :
                    Fraction.Rational) := traceEq
                  _ = (1 : Fraction.Rational) := by ring1
              · subst numerator
                apply two
                calc
                  traceParameter rotation = ((2 : Int) :
                    Fraction.Rational) := traceEq
                  _ = (2 : Fraction.Rational) := by ring1
            exact impossible.elim

end

end Purelib.Geometry.Rotations.Rational.Order.RotationOrder

end
