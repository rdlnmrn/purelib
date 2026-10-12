module

public import Purelib.Algebra.Quadratic.Ternary.Lorentz
public import Purelib.Geometry.Quadratic.Ternary.SplitNullConic
import Purelib.Geometry.Quadratic.Space3.NullVectors
import Purelib.Data.Rat.Fraction.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Homogeneous parametrization of the time-first Lorentz null cone

The coordinate cycle identifies the Lorentz null cone with the existing
split null conic, reversing quadrance. Its executable two-chart builder
retains the original homogeneous parameters and nonzero comparison scale.
Projective equivalence of parameter pairs exactly characterizes equality
of the resulting null lines.
-/

public section

namespace Purelib.Geometry.Quadratic.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry.Quadratic.Ternary.SplitNullConic
open Purelib.Geometry.Quadratic.Space3
open Purelib.Geometry.Projective.Line (Proj)
open Purelib.Data.Rat
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*}

/-- Move the time-first coordinates to the split form's last-time-coordinate convention. -/
@[expose] def toSplit (vector : Vector3 K) : Vector3 K := ⟨vector.r, vector.s, vector.t⟩

/-- Restore the time-first coordinates from the split form's last-time-coordinate convention. -/
@[expose] def fromSplit (vector : Vector3 K) : Vector3 K := ⟨vector.s, vector.t, vector.r⟩

/-- Restoring split coordinates recovers the original time-first vector. -/
theorem fromSplit_toSplit (vector : Vector3 K) : fromSplit (toSplit vector) = vector := rfl

/-- Moving restored time-first coordinates recovers the original split vector. -/
theorem toSplit_fromSplit (vector : Vector3 K) : toSplit (fromSplit vector) = vector := rfl

variable [ExplicitField K]

/-- The coordinate cycle commutes with vector scaling. -/
theorem toSplit_scale (factor : K) (vector : Vector3 K) :
    toSplit (Vector3.scale factor vector) = Vector3.scale factor (toSplit vector) := rfl

/-- The inverse coordinate cycle commutes with vector scaling. -/
theorem fromSplit_scale (factor : K) (vector : Vector3 K) :
    fromSplit (Vector3.scale factor vector) = Vector3.scale factor (fromSplit vector) := rfl

/-- Split quadrance of the cycled vector is the negative of its Lorentz quadrance. -/
theorem quadrance_toSplit (oneNonzero : (1 : K) ≠ 0) (vector : Vector3 K) :
    (Form.minkowski oneNonzero).quadrance (toSplit vector) =
      -(Form.lorentz oneNonzero).quadrance vector := by
  rw [Form.quadrance_minkowski, Form.quadrance_lorentz]
  unfold toSplit
  ring1

/-- Lorentz quadrance of the restored vector is the negative of its split quadrance. -/
theorem quadrance_fromSplit (oneNonzero : (1 : K) ≠ 0) (vector : Vector3 K) :
    (Form.lorentz oneNonzero).quadrance (fromSplit vector) =
      -(Form.minkowski oneNonzero).quadrance vector := by
  rw [Form.quadrance_minkowski, Form.quadrance_lorentz]
  unfold fromSplit
  ring1

/-- The homogeneous null vector with time coordinate equal to the sum of parameter squares. -/
@[expose] def nullParameter (first second : K) : Vector3 K :=
  fromSplit (MinkowskiClifford.nullParameter first second)

/-- The time-first null parametrization has the Pythagorean coordinate formula. -/
theorem nullParameter_coordinates (first second : K) :
    nullParameter first second = ⟨first ^ 2 + second ^ 2, first ^ 2 - second ^ 2, 2 * first * second⟩ := rfl

/-- Every homogeneous parameter vector is Lorentz-null. -/
theorem nullParameter_isNull (oneNonzero : (1 : K) ≠ 0) (first second : K) :
    (Form.lorentz oneNonzero).IsNull (nullParameter first second) := by
  change (Form.lorentz oneNonzero).quadrance (fromSplit (MinkowskiClifford.nullParameter first second)) = 0
  rw [quadrance_fromSplit]
  have null := MinkowskiClifford.nullParameter_isNull oneNonzero first second
  change (Form.minkowski oneNonzero).quadrance (MinkowskiClifford.nullParameter first second) = 0 at null
  rw [null, neg_zero]

/-- Nonzero homogeneous parameters give a nonzero Lorentz-null vector. -/
theorem nullParameter_nonzero [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (first second : K) (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    nullParameter first second ≠ Vector3.zero := by
  intro parameterZero
  have splitZero := congrArg toSplit parameterZero
  change MinkowskiClifford.nullParameter first second = Vector3.zero at splitZero
  exact MinkowskiClifford.nullParameter_nonzero twoNonzero first second parametersNonzero splitZero

/-- Construct retained homogeneous parameters for a nonzero Lorentz-null vector.

The result is the original split-conic witness on the cycled input, retaining
its exact parameters, nonzero scale and two-chart construction. The companion
transport law states its parameter equation in time-first coordinates.
-/
@[expose] def nullParameterWitness [DecidableEq K] (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K)
    (null : (Form.lorentz oneNonzero).IsNull vector) (nonzero : vector ≠ Vector3.zero) :
    MinkowskiClifford.NullParameterWitness (toSplit vector) := by
  have splitNull : (Form.minkowski oneNonzero).IsNull (toSplit vector) := by
    change (Form.minkowski oneNonzero).quadrance (toSplit vector) = 0
    rw [quadrance_toSplit]
    change (Form.lorentz oneNonzero).quadrance vector = 0 at null
    rw [null, neg_zero]
  have splitNonzero : toSplit vector ≠ Vector3.zero := by
    intro splitZero
    exact nonzero (congrArg fromSplit splitZero)
  exact MinkowskiClifford.nullParameterWitness oneNonzero twoNonzero (toSplit vector) splitNull splitNonzero

/-- The retained split-conic witness represents the original Lorentz vector with its original scale. -/
theorem nullParameterWitness_spec (vector : Vector3 K)
    (witness : MinkowskiClifford.NullParameterWitness (toSplit vector)) :
    nullParameter witness.first witness.second = Vector3.scale witness.factor vector := by
  have represents := congrArg fromSplit witness.parameter_spec
  rw [fromSplit_scale, fromSplit_toSplit] at represents
  exact represents

/-- Projective parameter equivalence is exactly equality of the corresponding Lorentz-null lines. -/
theorem nullParameter_sameLine_iff [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (left right : Proj K) (leftNonzero : left.Nonzero) (rightNonzero : right.Nonzero) :
    left.Equivalent right ↔ ∃ factor : K, factor ≠ 0 ∧
      nullParameter left.p left.q = Vector3.scale factor (nullParameter right.p right.q) := by
  constructor
  · intro equivalent
    rcases (MinkowskiClifford.nullParameter_sameLine_iff twoNonzero left right leftNonzero rightNonzero).mp
      equivalent with ⟨factor, factorNonzero, represents⟩
    refine ⟨factor, factorNonzero, ?_⟩
    have cycled := congrArg fromSplit represents
    rw [fromSplit_scale] at cycled
    exact cycled
  · rintro ⟨factor, factorNonzero, represents⟩
    apply (MinkowskiClifford.nullParameter_sameLine_iff twoNonzero left right leftNonzero rightNonzero).mpr
    refine ⟨factor, factorNonzero, ?_⟩
    have cycled := congrArg toSplit represents
    rw [toSplit_scale] at cycled
    exact cycled

/-- Any two retained parameter witnesses for the same nonzero null vector give the same projective point. -/
theorem nullParameterWitness_unique [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (vector : Vector3 K) (left right : MinkowskiClifford.NullParameterWitness (toSplit vector)) :
    (⟨left.first, left.second⟩ : Proj K).Equivalent ⟨right.first, right.second⟩ := by
  apply (nullParameter_sameLine_iff twoNonzero
    ⟨left.first, left.second⟩ ⟨right.first, right.second⟩ left.parametersNonzero right.parametersNonzero).mpr
  refine ⟨left.factor / right.factor, ExplicitField.div_ne_zero left.factorNonzero right.factorNonzero, ?_⟩
  rw [nullParameterWitness_spec vector left, nullParameterWitness_spec vector right, Vector3.scale_scale,
    ExplicitField.div_mul_cancel left.factor right.factorNonzero]

/-- A nonzero rational Lorentz-null vector has nonzero time coordinate.

If time vanished, the spatial squares would sum to zero. The original
rational sum-of-squares separation certificate then forces the whole vector
to vanish.
-/
theorem rational_null_time_nonzero (oneNonzero : (1 : Fraction.Rational) ≠ 0)
    (vector : Vector3 Fraction.Rational) (null : (Form.lorentz oneNonzero).IsNull vector)
    (nonzero : vector ≠ Vector3.zero) : vector.t ≠ 0 := by
  intro timeZero
  have nullEquation : vector.t ^ 2 - vector.r ^ 2 - vector.s ^ 2 = 0 := by
    change (Form.lorentz oneNonzero).quadrance vector = 0 at null
    rw [Form.quadrance_lorentz] at null
    exact null
  have euclideanNull : vector.IsNull := by
    change vector.t * vector.t + vector.r * vector.r + vector.s * vector.s = 0
    calc
      _ = -(vector.t ^ 2 - vector.r ^ 2 - vector.s ^ 2) := by rw [timeZero]; ring1
      _ = 0 := by rw [nullEquation, neg_zero]
  exact nonzero (NullVectors.rational_only_zero_null_vector vector euclideanNull)

end Purelib.Geometry.Quadratic.Ternary.Lorentz

end
