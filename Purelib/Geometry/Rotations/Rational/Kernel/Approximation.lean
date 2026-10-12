module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Order.Bounds
public import Purelib.Algebra.Quaternion.Projective.UnitObstruction
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Geometry.Rotations.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity
public import Purelib.Approximation.Rational.SquareRootBracket
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Geometry.Rotations.Projective.Correspondence
import Purelib.Geometry.Rotations.Spread
public import Purelib.LinearAlgebra.Coordinates3.Rational.Distance
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.NumberTheory.SquareClass.Rational.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Algebra.Quaternion.Projective.SquareClass
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Algebra.Quaternion.Projective.Rational.Surjectivity

open Purelib.Algebra.Quaternion.Projective.SquareClass

open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion

open Purelib.Approximation.Rational.SquareRootBracket

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Projective

open Purelib.Geometry.Rotations.Projective.Action

open Purelib.Geometry.Rotations.Projective.Correspondence

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

open Purelib.LinearAlgebra.Coordinates3.Rational

open Purelib.NumberTheory.SquareClass.Rational.Basic

public section

/-!
# Finite rational approximation by unit-quaternion rotations

This module proves the finite-precision form of the density clause in Problem
70.  It uses squared error on the nine displayed matrix entries, a finite
integer-square-root bracket, and a rational stereographic candidate whose norm
is exactly one.  Every positive rational radius request terminates with a
strict error certificate.  No real square root, topology, sequence, or limit
is formed.
-/

namespace Purelib.Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation

/-- For displayed rotations, squared entrywise error is determined by the trace of their relative rotation. -/
theorem matrixDistanceSq_eq_six_sub_two_trace_mul_transpose
    (left right : Rotations.Basic.Rotation Fraction.Rational) :
    Distance.KernelApproximation.matrixDistanceSq left.matrix right.matrix =
      6 - 2 * Matrix3.trace
        (Matrix3.mul left.matrix (Matrix3.transpose right.matrix)) := by
  have leftFirst := congrArg (fun matrix : Coordinates3.Matrix3 Fraction.Rational => matrix.tt)
    left.orthogonal
  have leftSecond := congrArg (fun matrix : Coordinates3.Matrix3 Fraction.Rational => matrix.rr)
    left.orthogonal
  have leftThird := congrArg (fun matrix : Coordinates3.Matrix3 Fraction.Rational => matrix.ss)
    left.orthogonal
  have rightFirst := congrArg (fun matrix : Coordinates3.Matrix3 Fraction.Rational => matrix.tt)
    right.orthogonal
  have rightSecond := congrArg (fun matrix : Coordinates3.Matrix3 Fraction.Rational => matrix.rr)
    right.orthogonal
  have rightThird := congrArg (fun matrix : Coordinates3.Matrix3 Fraction.Rational => matrix.ss)
    right.orthogonal
  change left.matrix.tt * left.matrix.tt +
      left.matrix.tr * left.matrix.tr +
      left.matrix.ts * left.matrix.ts = 1 at leftFirst
  change left.matrix.rt * left.matrix.rt +
      left.matrix.rr * left.matrix.rr +
      left.matrix.rs * left.matrix.rs = 1 at leftSecond
  change left.matrix.st * left.matrix.st +
      left.matrix.sr * left.matrix.sr +
      left.matrix.ss * left.matrix.ss = 1 at leftThird
  change right.matrix.tt * right.matrix.tt +
      right.matrix.tr * right.matrix.tr +
      right.matrix.ts * right.matrix.ts = 1 at rightFirst
  change right.matrix.rt * right.matrix.rt +
      right.matrix.rr * right.matrix.rr +
      right.matrix.rs * right.matrix.rs = 1 at rightSecond
  change right.matrix.st * right.matrix.st +
      right.matrix.sr * right.matrix.sr +
      right.matrix.ss * right.matrix.ss = 1 at rightThird
  calc
    Distance.KernelApproximation.matrixDistanceSq left.matrix right.matrix =
        (left.matrix.tt * left.matrix.tt +
          left.matrix.tr * left.matrix.tr +
          left.matrix.ts * left.matrix.ts) +
        (left.matrix.rt * left.matrix.rt +
          left.matrix.rr * left.matrix.rr +
          left.matrix.rs * left.matrix.rs) +
        (left.matrix.st * left.matrix.st +
          left.matrix.sr * left.matrix.sr +
          left.matrix.ss * left.matrix.ss) +
        (right.matrix.tt * right.matrix.tt +
          right.matrix.tr * right.matrix.tr +
          right.matrix.ts * right.matrix.ts) +
        (right.matrix.rt * right.matrix.rt +
          right.matrix.rr * right.matrix.rr +
          right.matrix.rs * right.matrix.rs) +
        (right.matrix.st * right.matrix.st +
          right.matrix.sr * right.matrix.sr +
          right.matrix.ss * right.matrix.ss) -
        2 * Matrix3.trace
          (Matrix3.mul left.matrix (Matrix3.transpose right.matrix)) := by
      unfold Distance.KernelApproximation.matrixDistanceSq Matrix3.trace Matrix3.mul Matrix3.transpose
      ring1
    _ = 6 - 2 * Matrix3.trace
        (Matrix3.mul left.matrix (Matrix3.transpose right.matrix)) := by
      rw [leftFirst, leftSecond, leftThird, rightFirst, rightSecond,
        rightThird]
      ring1

/-- Quaternion conjugation displays the transpose inverse rotation. -/
theorem conjugate_rotationMatrix (proportion : Projective.Basic.NonNullProportion Fraction.Rational) :
    (NonNullProportion.rotationMatrix (NonNullProportion.conjugate proportion)) =
      Matrix3.transpose (NonNullProportion.rotationMatrix proportion) := by
  rw [NonNullProportion.rotationMatrix_eq_scaled_numerator,
    NonNullProportion.rotationMatrix_eq_scaled_numerator]
  change Matrix3.scale
      (Proportion.norm (Proportion.conjugate proportion.toProportion))⁻¹
      (Action.proportionRotationNumerator
        (Proportion.conjugate proportion.toProportion)) =
    Matrix3.transpose
      (Matrix3.scale proportion.toProportion.norm⁻¹
        (Action.proportionRotationNumerator proportion.toProportion))
  rw [Proportion.norm_conjugate, Matrix3.transpose_scale]
  apply Matrix3.ext <;>
    unfold Action.proportionRotationNumerator Proportion.conjugate Matrix3.scale
      Matrix3.transpose Coordinates3.Vector.neg <;> ring1

/-- Squared matrix error is eight times the half spread of the relative quaternion rotation. -/
theorem matrixDistanceSq_eq_eight_mul_halfSpread_relative
    (left right : Projective.Basic.NonNullProportion Fraction.Rational) :
    Distance.KernelApproximation.matrixDistanceSq (NonNullProportion.rotationMatrix left)
      (NonNullProportion.rotationMatrix right) =
      8 * Spread.halfSpread
        (NonNullProportion.rotation (NonNullProportion.mul left
          (NonNullProportion.conjugate right))) := by
  change Distance.KernelApproximation.matrixDistanceSq (NonNullProportion.rotation left).matrix
    (NonNullProportion.rotation right).matrix = _
  rw [matrixDistanceSq_eq_six_sub_two_trace_mul_transpose]
  change 6 - 2 * Matrix3.trace
      (Matrix3.mul (NonNullProportion.rotationMatrix left)
        (Matrix3.transpose (NonNullProportion.rotationMatrix right))) = _
  rw [← conjugate_rotationMatrix right,
    ← NonNullProportion.rotationMatrix_mul]
  have fourCancel : (4 : Fraction.Rational) * (4 : Fraction.Rational)⁻¹ = 1 :=
    Algebra.Field.ExplicitField.mul_inv_cancel 4 (by decide)
  unfold Spread.halfSpread NonNullProportion.rotation
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    6 - 2 * Matrix3.trace
        (NonNullProportion.rotationMatrix (NonNullProportion.mul left
          (NonNullProportion.conjugate right))) =
      2 * (3 - Matrix3.trace
        (NonNullProportion.rotationMatrix (NonNullProportion.mul left
          (NonNullProportion.conjugate right)))) := by ring1
    _ = 8 * ((3 - Matrix3.trace
        (NonNullProportion.rotationMatrix (NonNullProportion.mul left
          (NonNullProportion.conjugate right)))) *
          (4 : Fraction.Rational)⁻¹) := by
      calc
        2 * (3 - Matrix3.trace
            (NonNullProportion.rotationMatrix (NonNullProportion.mul left
              (NonNullProportion.conjugate right)))) =
          2 * (3 - Matrix3.trace
            (NonNullProportion.rotationMatrix (NonNullProportion.mul left
              (NonNullProportion.conjugate right)))) *
            (4 * (4 : Fraction.Rational)⁻¹) := by rw [fourCancel]; ring1
        _ = 8 * ((3 - Matrix3.trace
            (NonNullProportion.rotationMatrix (NonNullProportion.mul left
              (NonNullProportion.conjugate right)))) *
              (4 : Fraction.Rational)⁻¹) := by ring1

/-! ## A rational norm-one stereographic candidate -/

/-- Select the projectively equal sign whose scalar coordinate is nonnegative. -/
@[expose] def orientNonnegative (proportion : Projective.Basic.NonNullProportion Fraction.Rational) :
    Projective.Basic.NonNullProportion Fraction.Rational :=
  if nonnegative : 0 ≤ proportion.scalar then proportion
  else NonNullProportion.scale (-1) (by
    intro negativeOneZero
    have oneZero : (1 : Fraction.Rational) = 0 := by
      calc
        1 = -(-1 : Fraction.Rational) := by ring1
        _ = -0 := by rw [negativeOneZero]
        _ = 0 := by ring1
    exact proportion.one_ne_zero oneZero) proportion

/-- Choosing the nonnegative scalar orientation preserves explicit projective equivalence. -/
theorem orientNonnegative_equivalent (proportion : Projective.Basic.NonNullProportion Fraction.Rational) :
    proportion.Equivalent (orientNonnegative proportion) := by
  unfold orientNonnegative
  split
  · exact NonNullProportion.equivalent_refl proportion
  · rename_i negative
    refine ⟨-1, ?_, rfl⟩
    intro negativeOneZero
    have oneZero : (1 : Fraction.Rational) = 0 := by
      calc
        1 = -(-1 : Fraction.Rational) := by ring1
        _ = -0 := by rw [negativeOneZero]
        _ = 0 := by ring1
    exact proportion.one_ne_zero oneZero

/-- The oriented representative has nonnegative scalar coordinate. -/
theorem orientNonnegative_scalar_nonnegative
    (proportion : Projective.Basic.NonNullProportion Fraction.Rational) :
    0 ≤ (orientNonnegative proportion).scalar := by
  unfold orientNonnegative
  split
  · assumption
  · rename_i negative
    have scaledScalar :
        (Proportion.scale (-1) proportion.toProportion).scalar =
          -proportion.scalar := by
      change (-1 : Fraction.Rational) * proportion.scalar = -proportion.scalar
      ring1
    change 0 ≤ (Proportion.scale (-1) proportion.toProportion).scalar
    rw [scaledScalar]
    have less := Fraction.Order.Arithmetic.lt_of_not_ge_direct negative
    have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct less.le
    change 0 ≤ -proportion.scalar at reversed
    exact reversed

/-- Choosing the scalar orientation preserves the quaternion norm. -/
theorem orientNonnegative_norm
    (proportion : Projective.Basic.NonNullProportion Fraction.Rational) :
    (orientNonnegative proportion).toProportion.norm =
      proportion.toProportion.norm := by
  unfold orientNonnegative
  split
  · rfl
  · change (Proportion.scale (-1) proportion.toProportion).norm =
      proportion.toProportion.norm
    rw [Proportion.norm_scale]
    ring1

/-- Positive norm packaged for the finite square-root bracket. -/
@[expose] def positiveNormTarget (proportion : Projective.Basic.NonNullProportion Fraction.Rational) :
    TheoremSixtyTwo.PositiveSquareClassRepresentative where
  representative := (NonNullProportion.quadranceClass proportion)
  positive := TheoremSixtyTwo.nonNullProportion_norm_positive proportion

/-- Unnormalized rational stereographic point. -/
@[expose] def stereographicRaw (proportion : Projective.Basic.NonNullProportion Fraction.Rational)
    (root : Fraction.Rational) : Projective.Basic.Proportion Fraction.Rational :=
  let chart := root + proportion.scalar
  { scalar := chart ^ 2 - proportion.vector.quadrance
    vector := Coordinates3.Vector.scale (2 * chart) proportion.vector }

/-- Common stereographic denominator. -/
@[expose] def stereographicDenominator (proportion : Projective.Basic.NonNullProportion Fraction.Rational)
    (root : Fraction.Rational) : Fraction.Rational :=
  let chart := root + proportion.scalar
  chart ^ 2 + proportion.vector.quadrance

/-- The raw stereographic quaternion norm is the square of its common denominator. -/
theorem stereographicRaw_norm
    (proportion : Projective.Basic.NonNullProportion Fraction.Rational) (root : Fraction.Rational) :
    (stereographicRaw proportion root).norm =
      stereographicDenominator proportion root ^ 2 := by
  unfold stereographicRaw stereographicDenominator Proportion.norm
  rw [Coordinates3.Vector.quadrance_scale]
  ring1

/-- Every rational three-vector has nonnegative quadrance. -/
theorem vector_quadrance_nonnegative (vector : Coordinates3.Vector Fraction.Rational) :
    0 ≤ vector.quadrance := by
  unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
  exact add_nonneg
    (add_nonneg
      (by
          simpa only [pow_two]
            using Fraction.Order.Arithmetic.sq_nonneg_direct vector.t)
      (by
          simpa only [pow_two]
            using Fraction.Order.Arithmetic.sq_nonneg_direct vector.r))
    (by
        simpa only [pow_two]
          using Fraction.Order.Arithmetic.sq_nonneg_direct vector.s)

/-- A positive root and nonnegative scalar coordinate give a positive stereographic denominator. -/
theorem stereographicDenominator_positive
    (proportion : Projective.Basic.NonNullProportion Fraction.Rational) (root : Fraction.Rational)
    (rootPositive : 0 < root) (scalarNonnegative : 0 ≤ proportion.scalar) :
    0 < stereographicDenominator proportion root := by
  have chartPositive : 0 < root + proportion.scalar :=
    add_pos_of_pos_of_nonneg rootPositive scalarNonnegative
  have chartSquarePositive :=
    Fraction.Order.Arithmetic.pow_pos_direct chartPositive 2
  unfold stereographicDenominator
  exact add_pos_of_pos_of_nonneg chartSquarePositive
    (vector_quadrance_nonnegative proportion.vector)

set_option genInjectivity false in
/-- Cached finite data for one exact unit-quaternion candidate. -/
structure UnitCandidate (source : Projective.Basic.NonNullProportion Fraction.Rational) (scale : Nat) where
  /-- The cached representative with nonnegative scalar orientation. -/ oriented : Projective.Basic.NonNullProportion
    Fraction.Rational
  /-- The retained orientation is exactly the computed sign adjustment of the source. -/ oriented_eq : oriented =
    orientNonnegative source
  /-- The retained oriented representative is projectively equivalent to the original source. -/ oriented_equivalent :
    source.Equivalent oriented
  /-- The retained finite square-root bracket for the source norm at the requested scale. -/ bracket :
    KernelApproximation.SqrtBracket (positiveNormTarget source) scale
  /-- The cached rational upper endpoint of the root bracket. -/ root : Fraction.Rational
  /-- The cached root is exactly the retained bracket's upper endpoint. -/ root_eq : root = bracket.upper
  /-- The retained root is strictly positive. -/ root_positive : 0 < root
  /-- The cached non-null raw stereographic representative. -/ raw : Projective.Basic.NonNullProportion
    Fraction.Rational
  /-- The raw representative is exactly the stereographic expression in the retained orientation and root. -/ raw_value
    : raw.toProportion = stereographicRaw oriented root
  /-- The cached stereographic normalization denominator. -/ denominator : Fraction.Rational
  /-- The cached denominator is exactly the stereographic denominator in the retained orientation and root. -/
    denominator_eq : denominator = stereographicDenominator oriented root
  /-- The cached normalization denominator is positive. -/ denominator_positive : 0 < denominator
  /-- The cached normalized quaternion representative. -/ unit : Projective.Basic.NonNullProportion Fraction.Rational
  /-- The normalized representative is exactly the raw representative scaled by the retained denominator inverse. -/
    unit_eq : unit = NonNullProportion.scale denominator⁻¹
    (Algebra.Field.ExplicitField.inv_ne_zero denominator_positive.ne') raw
  /-- The retained normalized representative has norm one. -/ unit_norm : unit.toProportion.norm = 1
  /-- The raw and normalized representatives are projectively equivalent. -/ unit_equivalent_raw : raw.Equivalent unit
  /-- The retained normalized representative belongs to the unit-quaternion kernel. -/ unit_hasUnitRepresentative :
    (QuaternionObstruction.HasUnitRepresentative unit)

constructive_injectivity UnitCandidate

/-- Compute one rational norm-one candidate at the supplied finite square-root refinement. -/
@[expose] def unitCandidate (source : Projective.Basic.NonNullProportion Fraction.Rational) (scale : Nat) :
    UnitCandidate source scale := by
  let oriented := orientNonnegative source
  let bracket := KernelApproximation.sqrtBracket (positiveNormTarget source) scale
  let root := bracket.upper
  have rootPositive : 0 < root := bracket.upper_positive
  have scalarNonnegative : 0 ≤ oriented.scalar :=
    orientNonnegative_scalar_nonnegative source
  let denominator := stereographicDenominator oriented root
  have denominatorPositive : 0 < denominator :=
    stereographicDenominator_positive oriented root rootPositive
      scalarNonnegative
  let raw : Projective.Basic.NonNullProportion Fraction.Rational :=
    { toProportion := stereographicRaw oriented root
      normNonzero := by
        rw [stereographicRaw_norm]
        simpa only [pow_two] using Algebra.Field.ExplicitField.mul_ne_zero
          denominatorPositive.ne' denominatorPositive.ne' }
  let unit := NonNullProportion.scale denominator⁻¹
    (Algebra.Field.ExplicitField.inv_ne_zero denominatorPositive.ne') raw
  have denominatorCancel := Algebra.Field.ExplicitField.mul_inv_cancel
    denominator denominatorPositive.ne'
  have unitNorm : unit.toProportion.norm = 1 := by
    unfold unit
    change (Proportion.scale denominator⁻¹ raw.toProportion).norm = 1
    rw [Proportion.norm_scale]
    change denominator⁻¹ ^ 2 *
      (stereographicRaw oriented root).norm = 1
    rw [stereographicRaw_norm]
    change denominator⁻¹ ^ 2 * denominator ^ 2 = 1
    calc
      denominator⁻¹ ^ 2 * denominator ^ 2 =
          (denominator * denominator⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [denominatorCancel]; ring1
  refine
    { oriented := oriented
      oriented_eq := rfl
      oriented_equivalent := orientNonnegative_equivalent source
      bracket := bracket
      root := root
      root_eq := rfl
      root_positive := rootPositive
      raw := raw
      raw_value := rfl
      denominator := denominator
      denominator_eq := rfl
      denominator_positive := denominatorPositive
      unit := unit
      unit_eq := rfl
      unit_norm := unitNorm
      unit_equivalent_raw := ?_
      unit_hasUnitRepresentative := ?_ }
  · refine ⟨denominator⁻¹,
      Algebra.Field.ExplicitField.inv_ne_zero denominatorPositive.ne', rfl⟩
  · refine ⟨1, unit.one_ne_zero, ?_⟩
    rw [Proportion.one_scale]
    exact unitNorm

/-- The raw candidate is a scalar multiple of the oriented source plus one explicit scalar-coordinate error `root^2 -
norm`. -/
theorem stereographicRaw_decomposition
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (root : Fraction.Rational) :
    stereographicRaw source root =
      { scalar :=
          (2 * (root + source.scalar)) * source.scalar +
            (root ^ 2 - source.toProportion.norm)
        vector := Coordinates3.Vector.scale (2 * (root + source.scalar)) source.vector } := by
  apply Proportion.ext
  · unfold stereographicRaw Proportion.norm
    ring1
  · rfl

/-- Multiplying the raw candidate by the conjugate target cancels its scalar multiple exactly; only the square-root
error remains in the vector part. -/
theorem stereographicRaw_mul_conjugate_vector_quadrance
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (root : Fraction.Rational) :
    (Proportion.mul (stereographicRaw source root)
        (Proportion.conjugate source.toProportion)).vector.quadrance =
      (root ^ 2 - source.toProportion.norm) ^ 2 *
        source.vector.quadrance := by
  unfold stereographicRaw Proportion.mul Proportion.conjugate Proportion.norm
    Coordinates3.Vector.quadrance Coordinates3.Vector.dot Coordinates3.Vector.neg Coordinates3.Vector.scale
      Coordinates3.Vector.sub Coordinates3.Vector.add
    Coordinates3.Vector.cross
  ring1

/-- Exact rational error of the cached norm-one candidate. The only approximation term is the square-root bracket error
`root² - norm`; all remaining factors are cached source and chart data. -/
theorem unitCandidate_matrixDistanceSq
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (scale : Nat) :
    Distance.KernelApproximation.matrixDistanceSq (NonNullProportion.rotationMatrix (unitCandidate source scale).unit)
        (NonNullProportion.rotationMatrix source) =
      8 * (((unitCandidate source scale).root ^ 2 -
          source.toProportion.norm) ^ 2 *
        (unitCandidate source scale).oriented.vector.quadrance /
        ((unitCandidate source scale).denominator ^ 2 *
          source.toProportion.norm)) := by
  let candidate := unitCandidate source scale
  have rawUnit : (NonNullProportion.rotationMatrix candidate.raw) =
      (NonNullProportion.rotationMatrix candidate.unit) :=
    NonNullProportion.rotationMatrix_respects_equivalent
      candidate.unit_equivalent_raw
  have sourceOriented : (NonNullProportion.rotationMatrix source) =
      (NonNullProportion.rotationMatrix candidate.oriented) :=
    NonNullProportion.rotationMatrix_respects_equivalent
      candidate.oriented_equivalent
  change Distance.KernelApproximation.matrixDistanceSq (NonNullProportion.rotationMatrix candidate.unit)
      (NonNullProportion.rotationMatrix source) =
    8 * ((candidate.root ^ 2 - source.toProportion.norm) ^ 2 *
      candidate.oriented.vector.quadrance /
      (candidate.denominator ^ 2 * source.toProportion.norm))
  rw [← rawUnit, sourceOriented,
    matrixDistanceSq_eq_eight_mul_halfSpread_relative]
  rw [NonNullProportion.halfSpread_rotation _ (by decide)]
  have vectorQuadrance :
      (NonNullProportion.mul candidate.raw
        (NonNullProportion.conjugate candidate.oriented)).vector.quadrance =
        (candidate.root ^ 2 - candidate.oriented.toProportion.norm) ^ 2 *
          candidate.oriented.vector.quadrance := by
    change (Proportion.mul candidate.raw.toProportion
      (Proportion.conjugate candidate.oriented.toProportion)).vector.quadrance =
        _
    rw [candidate.raw_value]
    exact stereographicRaw_mul_conjugate_vector_quadrance
      candidate.oriented candidate.root
  have conjugateNorm :
      (NonNullProportion.conjugate candidate.oriented).toProportion.norm =
        candidate.oriented.toProportion.norm := by
    change (Proportion.conjugate candidate.oriented.toProportion).norm = _
    exact Proportion.norm_conjugate candidate.oriented.toProportion
  have rawNorm : candidate.raw.toProportion.norm =
      candidate.denominator ^ 2 := by
    rw [candidate.raw_value, stereographicRaw_norm,
      ← candidate.denominator_eq]
  have orientedNorm : candidate.oriented.toProportion.norm =
      source.toProportion.norm := by
    rw [candidate.oriented_eq]
    exact orientNonnegative_norm source
  rw [vectorQuadrance, NonNullProportion.mul_norm, conjugateNorm, rawNorm,
    orientedNorm]

/-- The bracket error of a cached candidate is strictly positive. -/
theorem unitCandidate_square_error_positive
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (scale : Nat) :
    0 < (unitCandidate source scale).root ^ 2 -
      source.toProportion.norm := by
  let candidate := unitCandidate source scale
  have upperBound := candidate.bracket.value_lt_upper_square
  change source.toProportion.norm < candidate.bracket.upper ^ 2 at upperBound
  rw [← candidate.root_eq] at upperBound
  exact Fraction.Order.Arithmetic.sub_pos_direct upperBound

/-- The candidate's square-root error obeys the reciprocal finite-refinement bound supplied by its cached bracket. -/
theorem unitCandidate_square_error_le
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (scale : Nat) :
    (unitCandidate source scale).root ^ 2 -
        source.toProportion.norm ≤
      (2 * source.toProportion.norm + 3) / (scale + 1 : Nat) := by
  let candidate := unitCandidate source scale
  have bounded := KernelApproximation.sqrtBracket_square_error_le
    (positiveNormTarget source) scale candidate.bracket
  change candidate.bracket.upper ^ 2 - source.toProportion.norm ≤ _ at bounded
  rw [← candidate.root_eq] at bounded
  exact bounded

/-- The oriented vector quadrance is bounded by the positive source norm. -/
theorem unitCandidate_oriented_vector_quadrance_le_norm
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (scale : Nat) :
    (unitCandidate source scale).oriented.vector.quadrance ≤
      source.toProportion.norm := by
  let candidate := unitCandidate source scale
  have scalarSquareNonnegative :=
    Fraction.Order.Arithmetic.sq_nonneg_direct candidate.oriented.scalar
  have bounded : candidate.oriented.vector.quadrance ≤
      candidate.oriented.toProportion.norm := by
    unfold Proportion.norm
    exact le_add_of_nonneg_left scalarSquareNonnegative
  rw [candidate.oriented_eq, orientNonnegative_norm source] at bounded
  exact bounded

/-- The positive stereographic denominator strictly exceeds the source norm, providing the denominator separation used
by the error estimate. -/
theorem unitCandidate_norm_lt_denominator
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (scale : Nat) :
    source.toProportion.norm < (unitCandidate source scale).denominator := by
  let candidate := unitCandidate source scale
  have rootSquareAbove := candidate.bracket.value_lt_upper_square
  change source.toProportion.norm < candidate.bracket.upper ^ 2 at rootSquareAbove
  rw [← candidate.root_eq] at rootSquareAbove
  have scalarNonnegative : 0 ≤ candidate.oriented.scalar := by
    rw [candidate.oriented_eq]
    exact orientNonnegative_scalar_nonnegative source
  have rootLeChart : candidate.root ≤
      candidate.root + candidate.oriented.scalar :=
    le_add_of_nonneg_right scalarNonnegative
  have chartSquareAbove : candidate.root ^ 2 ≤
      (candidate.root + candidate.oriented.scalar) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      candidate.root_positive.le rootLeChart 2
  have vectorNonnegative :=
    vector_quadrance_nonnegative candidate.oriented.vector
  calc
    source.toProportion.norm < candidate.root ^ 2 := rootSquareAbove
    _ ≤ (candidate.root + candidate.oriented.scalar) ^ 2 :=
      chartSquareAbove
    _ ≤ (candidate.root + candidate.oriented.scalar) ^ 2 +
        candidate.oriented.vector.quadrance :=
      le_add_of_nonneg_right vectorNonnegative
    _ = candidate.denominator := by
      rw [candidate.denominator_eq]
      rfl

/-- Conservative rational refinement demand for one positive squared-radius request. Its natural numerator is already a
terminating sufficient scale. -/
@[expose] def precisionDemand (source : Projective.Basic.NonNullProportion Fraction.Rational)
    (radiusSq : Fraction.Rational) : Fraction.Rational :=
  8 * (2 * source.toProportion.norm + 3) ^ 2 /
    (radiusSq * source.toProportion.norm ^ 2)

/-- A positive requested squared radius gives a positive conservative refinement demand. -/
theorem precisionDemand_positive (source : Projective.Basic.NonNullProportion Fraction.Rational)
    (radiusSq : Fraction.Rational) (radiusPositive : 0 < radiusSq) :
    0 < precisionDemand source radiusSq := by
  have normPositive :=
    TheoremSixtyTwo.nonNullProportion_norm_positive source
  have factorPositive : 0 < 2 * source.toProportion.norm + 3 := by
    exact Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide) normPositive)
      (by decide)
  unfold precisionDemand
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Fraction.Order.Arithmetic.pow_pos_direct factorPositive 2))
    (Fraction.Order.Arithmetic.mul_pos_direct radiusPositive
      (Fraction.Order.Arithmetic.pow_pos_direct normPositive 2))

/-- A finite refinement selected directly from the canonical numerator of the conservative rational demand. -/
@[expose] def precisionScale (source : Projective.Basic.NonNullProportion Fraction.Rational)
    (radiusSq : Fraction.Rational) : Nat :=
  (precisionDemand source radiusSq).num.toNat

/-- The canonical numerator-based scale plus one strictly exceeds the positive refinement demand. -/
theorem precisionDemand_lt_precisionScale_succ
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (radiusSq : Fraction.Rational)
    (radiusPositive : 0 < radiusSq) :
    precisionDemand source radiusSq <
      (precisionScale source radiusSq + 1 : Nat) := by
  exact Fraction.Order.Bounds.positiveRational_lt_numerator_succ
    (precisionDemand source radiusSq)
    (precisionDemand_positive source radiusSq radiusPositive)

/-- Any refinement strictly above the conservative demand meets the requested squared matrix radius. The proof clears
only positive rational factors and uses the cached bracket, chart, and norm data. -/
theorem unitCandidate_matrixDistanceSq_lt_of_demand_lt
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (radiusSq : Fraction.Rational)
    (radiusPositive : 0 < radiusSq) (scale : Nat)
    (demandBelow : precisionDemand source radiusSq <
      (scale + 1 : Nat)) :
    Distance.KernelApproximation.matrixDistanceSq (NonNullProportion.rotationMatrix (unitCandidate source scale).unit)
        (NonNullProportion.rotationMatrix source) < radiusSq := by
  let candidate := unitCandidate source scale
  let norm := source.toProportion.norm
  let error := candidate.root ^ 2 - norm
  let factor := 2 * norm + 3
  let refinement : Fraction.Rational := (scale + 1 : Nat)
  have normPositive : 0 < norm := by
    unfold norm
    exact TheoremSixtyTwo.nonNullProportion_norm_positive source
  have radiusNormSquarePositive : 0 < radiusSq * norm ^ 2 :=
    Fraction.Order.Arithmetic.mul_pos_direct radiusPositive
      (Fraction.Order.Arithmetic.pow_pos_direct normPositive 2)
  have factorPositive : 0 < factor := by
    unfold factor
    exact Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide) normPositive)
      (by decide)
  have refinementPositive : 0 < refinement := by
    unfold refinement
    exact Fraction.Cast.Order.natCast_pos_direct (by omega0)
  have refinementAtLeastOne : (1 : Fraction.Rational) ≤ refinement := by
    unfold refinement
    simpa only [Nat.cast_one] using
      Fraction.Cast.Order.natCast_le_direct (by omega0 : 1 ≤ scale + 1)
  have refinementLeSquare : refinement ≤ refinement ^ 2 := by
    calc
      refinement = 1 * refinement := by ring1
      _ ≤ refinement * refinement :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          refinementAtLeastOne refinementPositive.le
      _ = refinement ^ 2 := by ring1
  have errorPositive : 0 < error := by
    unfold error norm candidate
    exact unitCandidate_square_error_positive source scale
  have errorLe : error ≤ factor / refinement := by
    unfold error factor norm refinement candidate
    exact unitCandidate_square_error_le source scale
  have errorTimesRefinementLe : error * refinement ≤ factor :=
    (Fraction.Order.Field.le_div_iff_pos refinementPositive).mp errorLe
  have errorTimesRefinementNonnegative :
      0 ≤ error * refinement :=
    Fraction.Order.Arithmetic.mul_nonneg_direct errorPositive.le
      refinementPositive.le
  have errorSquareCleared :
      error ^ 2 * refinement ^ 2 ≤ factor ^ 2 := by
    have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
      errorTimesRefinementNonnegative errorTimesRefinementLe 2
    calc
      error ^ 2 * refinement ^ 2 =
          (error * refinement) ^ 2 := by ring1
      _ ≤ factor ^ 2 := squares
  have demandBelowSquare : precisionDemand source radiusSq <
      refinement ^ 2 := by
    exact demandBelow.trans_le refinementLeSquare
  have demandCleared : 8 * factor ^ 2 <
      refinement ^ 2 * (radiusSq * norm ^ 2) := by
    apply (Fraction.Order.Field.div_lt_iff_pos
      radiusNormSquarePositive).mp
    change precisionDemand source radiusSq < refinement ^ 2
    exact demandBelowSquare
  have errorCoefficientNonnegative : 0 ≤ 8 * norm :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) normPositive.le
  have scaledErrorLe :
      (8 * error ^ 2 * norm) * refinement ^ 2 ≤
        8 * factor ^ 2 * norm := by
    calc
      (8 * error ^ 2 * norm) * refinement ^ 2 =
          (8 * norm) * (error ^ 2 * refinement ^ 2) := by ring1
      _ ≤ (8 * norm) * factor ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          errorSquareCleared errorCoefficientNonnegative
      _ = 8 * factor ^ 2 * norm := by ring1
  have demandTimesNorm :
      8 * factor ^ 2 * norm <
        (radiusSq * norm ^ 2 * norm) * refinement ^ 2 := by
    have scaled :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        demandCleared normPositive
    calc
      8 * factor ^ 2 * norm <
          (refinement ^ 2 * (radiusSq * norm ^ 2)) * norm := scaled
      _ = (radiusSq * norm ^ 2 * norm) * refinement ^ 2 := by ring1
  have coreScaled :
      (8 * error ^ 2 * norm) * refinement ^ 2 <
        (radiusSq * norm ^ 2 * norm) * refinement ^ 2 :=
    scaledErrorLe.trans_lt demandTimesNorm
  have core : 8 * error ^ 2 * norm <
      radiusSq * norm ^ 2 * norm :=
    Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct coreScaled
      (Fraction.Order.Arithmetic.pow_pos_direct refinementPositive 2)
  have vectorNonnegative :
      0 ≤ candidate.oriented.vector.quadrance :=
    vector_quadrance_nonnegative candidate.oriented.vector
  have vectorLeNorm : candidate.oriented.vector.quadrance ≤ norm := by
    unfold candidate norm
    exact unitCandidate_oriented_vector_quadrance_le_norm source scale
  have numeratorLe :
      8 * error ^ 2 * candidate.oriented.vector.quadrance ≤
        8 * error ^ 2 * norm := by
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      vectorLeNorm
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct error))
  have normBelowDenominator : norm < candidate.denominator := by
    unfold norm candidate
    exact unitCandidate_norm_lt_denominator source scale
  have normSquareLeDenominatorSquare :
      norm ^ 2 ≤ candidate.denominator ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct normPositive.le
      normBelowDenominator.le 2
  have radiusNormNonnegative : 0 ≤ radiusSq * norm :=
    Fraction.Order.Arithmetic.mul_nonneg_direct radiusPositive.le
      normPositive.le
  have requestedDenominatorLe : radiusSq * norm ^ 2 * norm ≤
      radiusSq * candidate.denominator ^ 2 * norm := by
    calc
      radiusSq * norm ^ 2 * norm =
          (radiusSq * norm) * norm ^ 2 := by ring1
      _ ≤ (radiusSq * norm) * candidate.denominator ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          normSquareLeDenominatorSquare radiusNormNonnegative
      _ = radiusSq * candidate.denominator ^ 2 * norm := by ring1
  have numeratorStrict :
      8 * error ^ 2 * candidate.oriented.vector.quadrance <
        radiusSq * (candidate.denominator ^ 2 * norm) := by
    calc
      8 * error ^ 2 * candidate.oriented.vector.quadrance ≤
          8 * error ^ 2 * norm := numeratorLe
      _ < radiusSq * norm ^ 2 * norm := core
      _ ≤ radiusSq * candidate.denominator ^ 2 * norm :=
        requestedDenominatorLe
      _ = radiusSq * (candidate.denominator ^ 2 * norm) := by ring1
  have denominatorPositive : 0 < candidate.denominator ^ 2 * norm :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Order.Arithmetic.pow_pos_direct
        candidate.denominator_positive 2)
      normPositive
  change Distance.KernelApproximation.matrixDistanceSq (NonNullProportion.rotationMatrix candidate.unit)
      (NonNullProportion.rotationMatrix source) < radiusSq
  rw [unitCandidate_matrixDistanceSq]
  change 8 * (error ^ 2 * candidate.oriented.vector.quadrance /
      (candidate.denominator ^ 2 * norm)) < radiusSq
  rw [show 8 * (error ^ 2 * candidate.oriented.vector.quadrance /
      (candidate.denominator ^ 2 * norm)) =
      (8 * error ^ 2 * candidate.oriented.vector.quadrance) /
        (candidate.denominator ^ 2 * norm) by
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    ring1]
  exact (Fraction.Order.Field.div_lt_iff_pos denominatorPositive).2
    numeratorStrict

/-! ## One finite certificate for one rational precision request -/

set_option genInjectivity false in
/-- The complete finite output for one target rotation and one positive rational squared radius. The canonical source
representative, selected refinement, bracketed candidate, exact unit representative, associated rotation, and final
error comparison are all retained as executable data. -/
structure KernelApproximationCertificate (target : Rotations.Basic.Rotation Fraction.Rational)
    (radiusSq : Fraction.Rational) where
  /-- The original requested squared radius is positive. -/ radius_positive : 0 < radiusSq
  /-- The cached canonical quaternion representative of the target rotation. -/ source :
    Projective.Basic.NonNullProportion Fraction.Rational
  /-- The source is exactly the canonical inverse representative of the original target. -/ source_eq : source =
    RotationProportion.ofRotation target (by decide)
  /-- The cached source represents the original target rotation matrix. -/ source_represents :
    (NonNullProportion.rotationMatrix source) = target.matrix
  /-- The retained natural refinement scale. -/ scale : Nat
  /-- The retained scale is exactly the numerator-based demand computed for the cached source and requested radius. -/
    scale_eq : scale = precisionScale source radiusSq
  /-- The retained certified stereographic candidate for the original source and scale. -/ candidate : UnitCandidate
    source scale
  /-- The candidate is exactly the finite construction at the retained source and scale. -/ candidate_eq : candidate =
    unitCandidate source scale
  /-- The cached norm-one approximating quaternion. -/ approximant : Projective.Basic.NonNullProportion
    Fraction.Rational
  /-- The approximant is exactly the retained candidate's normalized quaternion. -/ approximant_eq : approximant =
    candidate.unit
  /-- The cached approximant has norm one. -/ approximant_norm : approximant.toProportion.norm = 1
  /-- The approximant belongs to the unit-quaternion kernel. -/ approximant_hasUnitRepresentative :
    (QuaternionObstruction.HasUnitRepresentative approximant)
  /-- The cached certified rotation of the approximant. -/ rotation : Rotations.Basic.Rotation Fraction.Rational
  /-- The retained rotation is exactly the action of the cached approximant. -/ rotation_eq : rotation =
    (NonNullProportion.rotation approximant)
  /-- The squared entrywise matrix error from the original target is strictly below the requested radius. -/ error_lt :
    Distance.KernelApproximation.matrixDistanceSq rotation.matrix target.matrix < radiusSq

constructive_injectivity KernelApproximationCertificate

/-- Compute an exact rational unit-kernel approximation for one displayed rational rotation and one positive rational
squared-radius request. The constructor performs only the canonical finite inverse, base-four integer square-root
refinement, and fixed-coordinate rational arithmetic. -/
@[expose] def kernelApproximation (target : Rotations.Basic.Rotation Fraction.Rational) (radiusSq : Fraction.Rational)
    (radiusPositive : 0 < radiusSq) :
    KernelApproximationCertificate target radiusSq := by
  let source := RotationProportion.ofRotation target (by decide)
  have sourceRepresents : (NonNullProportion.rotationMatrix source) = target.matrix :=
    RotationProportion.ofRotation_rotationMatrix target (by decide)
  let scale := precisionScale source radiusSq
  let candidate := unitCandidate source scale
  have demandBelow : precisionDemand source radiusSq <
      (scale + 1 : Nat) := by
    unfold scale
    exact precisionDemand_lt_precisionScale_succ source radiusSq
      radiusPositive
  have sourceError :
      Distance.KernelApproximation.matrixDistanceSq (NonNullProportion.rotationMatrix candidate.unit)
        (NonNullProportion.rotationMatrix source) <
        radiusSq := by
    unfold candidate
    exact unitCandidate_matrixDistanceSq_lt_of_demand_lt source radiusSq
      radiusPositive scale demandBelow
  have targetError :
      Distance.KernelApproximation.matrixDistanceSq (NonNullProportion.rotationMatrix candidate.unit) target.matrix <
        radiusSq := by
    rw [← sourceRepresents]
    exact sourceError
  exact
    { radius_positive := radiusPositive
      source := source
      source_eq := rfl
      source_represents := sourceRepresents
      scale := scale
      scale_eq := rfl
      candidate := candidate
      candidate_eq := rfl
      approximant := candidate.unit
      approximant_eq := rfl
      approximant_norm := candidate.unit_norm
      approximant_hasUnitRepresentative :=
        candidate.unit_hasUnitRepresentative
      rotation := (NonNullProportion.rotation candidate.unit)
      rotation_eq := rfl
      error_lt := targetError }

/-- The candidate's stored rotation is in the unit-quaternion kernel. -/
theorem unitCandidate_rotation_hasUnitQuaternion
    (source : Projective.Basic.NonNullProportion Fraction.Rational) (scale : Nat) :
    (QuaternionObstruction.HasUnitRepresentative (unitCandidate source scale).unit) :=
  (unitCandidate source scale).unit_hasUnitRepresentative

end Purelib.Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation

end
