module

import Purelib.Algebra.Field.Squares

import Purelib.Algebra.Quadratic.Ternary.Basic
public import Purelib.Algebra.Quadratic.Ternary.Minkowski
public import Purelib.Geometry.Projective.Line.Scale
import Purelib.Geometry.Projective.Line.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.LinearAlgebra

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Homogeneous parametrization of the split null conic. -/
def nullParameter (first second : K) :
  Coordinates3.Vector K :=
  ⟨first ^ 2 - second ^ 2,
    2 * first * second,
    first ^ 2 + second ^ 2⟩
end
end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

set_option genInjectivity false in
/-- Explicit projective coordinates for a nonzero null direction. The parameter vector is tied to the input by a
displayed nonzero scale. -/
structure NullParameterWitness (vector :
  Coordinates3.Vector K) where
  /-- The first retained homogeneous parameter. -/ first : K
  /-- The second retained homogeneous parameter. -/ second : K
  /-- The retained scale relating the parameter vector to the input vector. -/ factor : K
  /-- At least one homogeneous parameter is nonzero. -/ parametersNonzero : first ≠ 0 ∨ second ≠ 0
  /-- The retained comparison scale is nonzero. -/ factorNonzero : factor ≠ 0
  /-- The homogeneous parameter vector is the retained nonzero multiple of the input. -/ parameter_spec :
    Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter first second = Coordinates3.Vector.scale
      factor vector

constructive_injectivity NullParameterWitness

end
end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

set_option genInjectivity false in
/-- Both directions of the constructive projective parametrization of the Minkowski null conic, packaged for direct
downstream use. -/
structure NullConicParametrization
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) where
  /-- Every homogeneous parameter vector is null for the Minkowski form. -/ parameterNull : ∀ first second : K,
    (TernaryForm.minkowski oneNonzero).IsNull
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter first second)
  /-- Nonzero homogeneous parameters produce a nonzero vector. -/ parameterNonzero : ∀ first second : K,
    first ≠ 0 ∨ second ≠ 0 →
      Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter first second ≠ Coordinates3.Vector.zero
  /-- Construct parameters and a nonzero comparison scale for each nonzero null vector. -/ covers : ∀ vector :
    Coordinates3.Vector K,
    (TernaryForm.minkowski oneNonzero).IsNull vector →
      vector ≠ Coordinates3.Vector.zero →
        NullParameterWitness vector

constructive_injectivity NullConicParametrization

end
end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- The homogeneous formula `(u²-v², 2uv, u²+v²)` has zero Minkowski quadrance. -/
theorem nullParameter_isNull (oneNonzero : (1
  : K) ≠ 0)
    (first second : K) :
    (TernaryForm.minkowski oneNonzero).IsNull
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter first second) := by
  unfold TernaryForm.IsNull
  rw [TernaryForm.quadrance_minkowski]
  unfold Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter
  ring1
end
end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end

section
@[expose] public section
section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace MinkowskiClifford

end MinkowskiClifford
end

end

section
@[expose] public section
section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace MinkowskiClifford

end MinkowskiClifford
end

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- The homogeneous null parametrization is nonzero on nonzero parameters.

The proof requires two to be nonzero and retains the supplied nonzero parameter alternative. -/
theorem nullParameter_nonzero [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) (first second : K)
    (parametersNonzero : first ≠ 0 ∨ second ≠ 0) :
    Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter first second ≠ Coordinates3.Vector.zero :=
      by
  intro parameterZero
  have firstCoordinate := congrArg Coordinates3.Vector.t parameterZero
  have thirdCoordinate := congrArg Coordinates3.Vector.s parameterZero
  change first ^ 2 - second ^ 2 = 0 at firstCoordinate
  change first ^ 2 + second ^ 2 = 0 at thirdCoordinate
  have twiceFirstSquare : 2 * first ^ 2 = 0 := by
    calc
      2 * first ^ 2 =
          (first ^ 2 - second ^ 2) +
            (first ^ 2 + second ^ 2) := by ring1
      _ = 0 := by rw [firstCoordinate, thirdCoordinate, add_zero]
  have twiceSecondSquare : 2 * second ^ 2 = 0 := by
    calc
      2 * second ^ 2 =
          (first ^ 2 + second ^ 2) -
            (first ^ 2 - second ^ 2) := by ring1
      _ = 0 := by rw [firstCoordinate, thirdCoordinate]; ring1
  have firstSquareZero :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
    twoNonzero twiceFirstSquare
  have secondSquareZero :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] {factor value : K} (factorNonzero : factor ≠ 0)
      (productZero : factor * value = 0) => (Purelib.Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left (R := K)
      (factor := factor) (value := value) factorNonzero productZero : value = 0))
    twoNonzero twiceSecondSquare
  have firstZero :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] (value : K) (squareZero : value ^ 2 = 0)
      => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0)) first
    firstSquareZero
  have secondZero :=
    (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] (value : K) (squareZero : value ^ 2 = 0)
      => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0)) second
    secondSquareZero
  rcases parametersNonzero with firstNonzero | secondNonzero
  · exact firstNonzero firstZero
  · exact secondNonzero secondZero
end
end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Read back scalar vanishing from its zero-square certificate. -/
theorem square_eq_zero_readback [DecidableEq
  K] (value : K)
    (squareZero : value ^ 2 = 0) : value = 0 :=
  (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K] (value : K) (squareZero : value ^ 2 = 0) =>
    (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value = 0)) value
    squareZero
end
end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Every nonzero null vector lies on the homogeneous parametrization, by one decidable two-chart split and without
choosing roots. -/
def nullParameterWitness [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (vector : Coordinates3.Vector K)
    (null : (TernaryForm.minkowski oneNonzero).IsNull vector)
    (nonzero : vector ≠ Coordinates3.Vector.zero) :
      NullParameterWitness vector := by
  have nullEquation :
      vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 = 0 := by
    unfold Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.IsNull at null
    rw [TernaryForm.quadrance_minkowski] at null
    exact null
  by_cases chartZero : vector.s + vector.t = 0
  · have sEq : vector.s = -vector.t := by
      calc
        vector.s = vector.s + vector.t - vector.t := by ring1
        _ = -vector.t := by rw [chartZero]; ring1
    have rSquareZero : vector.r ^ 2 = 0 := by
      calc
        vector.r ^ 2 =
            vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 := by
          rw [sEq]
          ring1
        _ = 0 := nullEquation
    have rZero := square_eq_zero_readback vector.r
      rSquareZero
    have tNonzero : vector.t ≠ 0 := by
      intro tZero
      apply nonzero
      apply Coordinates3.Vector.ext
      · change vector.t = 0
        exact tZero
      · change vector.r = 0
        exact rZero
      · change vector.s = 0
        rw [sEq, tZero]
        ring1
    have negTNonzero : -vector.t ≠ 0 := by
      intro negTZero
      apply tNonzero
      calc
        vector.t = -(-vector.t) := by ring1
        _ = -0 := by rw [negTZero]
        _ = 0 := by ring1
    exact
      { first := 0
        second := vector.t
        factor := -vector.t
        parametersNonzero := Or.inr tNonzero
        factorNonzero := negTNonzero
        parameter_spec := by
          apply Coordinates3.Vector.ext
          · change 0 ^ 2 - vector.t ^ 2 =
              -vector.t * vector.t
            ring1
          · change 2 * 0 * vector.t = -vector.t * vector.r
            rw [rZero]
            ring1
          · change 0 ^ 2 + vector.t ^ 2 =
              -vector.t * vector.s
            rw [sEq]
            ring1 }
  · have factorNonzero : 2 * (vector.s + vector.t) ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero twoNonzero chartZero
    exact
      { first := vector.s + vector.t
        second := vector.r
        factor := 2 * (vector.s + vector.t)
        parametersNonzero := Or.inl chartZero
        factorNonzero := factorNonzero
        parameter_spec := by
          apply Coordinates3.Vector.ext
          · change
              (vector.s + vector.t) ^ 2 - vector.r ^ 2 =
                2 * (vector.s + vector.t) * vector.t
            calc
              (vector.s + vector.t) ^ 2 - vector.r ^ 2 =
                  2 * (vector.s + vector.t) * vector.t -
                    (vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2) := by
                ring1
              _ = 2 * (vector.s + vector.t) * vector.t := by
                rw [nullEquation]
                ring1
          · change
              2 * (vector.s + vector.t) * vector.r =
                2 * (vector.s + vector.t) * vector.r
            rfl
          · change
              (vector.s + vector.t) ^ 2 + vector.r ^ 2 =
                2 * (vector.s + vector.t) * vector.s
            calc
              (vector.s + vector.t) ^ 2 + vector.r ^ 2 =
                  2 * (vector.s + vector.t) * vector.s +
                    (vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2) := by
                ring1
              _ = 2 * (vector.s + vector.t) * vector.s := by
                rw [nullEquation]
                ring1 }
end
end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

/-- Package the executable two-chart parametrization of the Minkowski null conic.

The bundle retains nullity, nonvanishing on nonzero parameters, and parameters with an explicit nonzero scale for every
nonzero null vector. -/
def nullConicParametrization [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    NullConicParametrization oneNonzero twoNonzero where
  parameterNull := nullParameter_isNull oneNonzero
  parameterNonzero := nullParameter_nonzero twoNonzero
  covers := nullParameterWitness oneNonzero twoNonzero
end
end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end

public section

namespace Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Squares
open Purelib.Geometry.Projective.Line (Proj)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- Scaling the two homogeneous parameters scales their null vector by the scalar square. -/
theorem nullParameter_scale (factor first second : K) :
    nullParameter (factor * first) (factor * second) =
      Vector3.scale (factor ^ 2) (nullParameter first second) := by
  ext <;> unfold nullParameter Vector3.scale <;> ring1

/-- Null parameter vectors on the same line have equivalent homogeneous parameters.

Coordinate sums and differences recover the two parameter squares, and the
middle coordinate recovers their product. These identities force the square
of the projective cross difference to vanish without extracting roots.
-/
theorem nullParameter_projective_injective [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (left right : Proj K) (factor : K)
    (represents : nullParameter left.p left.q = Vector3.scale factor (nullParameter right.p right.q)) :
    left.Equivalent right := by
  have first := congrArg Vector3.t represents
  have middle := congrArg Vector3.r represents
  have last := congrArg Vector3.s represents
  change left.p ^ 2 - left.q ^ 2 = factor * (right.p ^ 2 - right.q ^ 2) at first
  change 2 * left.p * left.q = factor * (2 * right.p * right.q) at middle
  change left.p ^ 2 + left.q ^ 2 = factor * (right.p ^ 2 + right.q ^ 2) at last
  have firstSquare : left.p ^ 2 = factor * right.p ^ 2 := by
    apply ExplicitField.eq_of_mul_eq_mul_left twoNonzero
    calc
      2 * left.p ^ 2 = (left.p ^ 2 - left.q ^ 2) + (left.p ^ 2 + left.q ^ 2) := by ring1
      _ = 2 * (factor * right.p ^ 2) := by rw [first, last]; ring1
  have secondSquare : left.q ^ 2 = factor * right.q ^ 2 := by
    apply ExplicitField.eq_of_mul_eq_mul_left twoNonzero
    calc
      2 * left.q ^ 2 = (left.p ^ 2 + left.q ^ 2) - (left.p ^ 2 - left.q ^ 2) := by ring1
      _ = 2 * (factor * right.q ^ 2) := by rw [first, last]; ring1
  have product : left.p * left.q = factor * (right.p * right.q) := by
    apply ExplicitField.eq_of_mul_eq_mul_left twoNonzero
    calc
      2 * (left.p * left.q) = 2 * left.p * left.q := by ring1
      _ = factor * (2 * right.p * right.q) := middle
      _ = 2 * (factor * (right.p * right.q)) := by ring1
  have crossSquare : (left.p * right.q - right.p * left.q) ^ 2 = 0 := by
    calc
      _ = left.p ^ 2 * right.q ^ 2 + left.q ^ 2 * right.p ^ 2 -
          2 * (left.p * left.q) * (right.p * right.q) := by ring1
      _ = 0 := by rw [firstSquare, secondSquare, product]; ring1
  have crossZero := eq_zero_of_square_eq_zero _ crossSquare
  change left.p * right.q = right.p * left.q
  calc
    _ = (left.p * right.q - right.p * left.q) + right.p * left.q := by ring1
    _ = _ := by rw [crossZero, zero_add]

/-- Projective parameter equivalence is exactly equality of the represented nonzero null lines. -/
theorem nullParameter_sameLine_iff [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (left right : Proj K) (leftNonzero : left.Nonzero) (rightNonzero : right.Nonzero) :
    left.Equivalent right ↔ ∃ factor : K, factor ≠ 0 ∧
      nullParameter left.p left.q = Vector3.scale factor (nullParameter right.p right.q) := by
  constructor
  · intro equivalent
    let witness := Proj.scaleWitness right left rightNonzero leftNonzero equivalent.symm
    refine ⟨witness.1 ^ 2, ExplicitField.square_nonzero_of_nonzero witness.2.1, ?_⟩
    have first := congrArg Proj.p witness.2.2
    have second := congrArg Proj.q witness.2.2
    change left.p = witness.1 * right.p at first
    change left.q = witness.1 * right.q at second
    rw [first, second]
    exact nullParameter_scale witness.1 right.p right.q
  · rintro ⟨factor, _, represents⟩
    exact nullParameter_projective_injective twoNonzero left right factor represents

end Purelib.Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford

end
