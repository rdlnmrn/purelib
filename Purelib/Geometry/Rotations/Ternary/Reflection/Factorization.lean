module

public import Purelib.Geometry.Rotations.Ternary.Cayley.Anchor
public import Purelib.Geometry.Rotations.Ternary.Cayley.HalfTurn
import Purelib.Geometry.Quadratic.Ternary.Frame
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Geometry.Rotations.Ternary.Reflection
import Purelib.LinearAlgebra.Coordinates3.Vector

/-!
# First-mirror choices for retained ternary rotation factorizations

The original cached Clifford chart supplies the cap normalization or
half-turn axis. Any non-null perpendicular first direction completes a
factorization through that same chart, and a second admissible line proves
nonuniqueness without merely rescaling the first normal.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] {form : Form K} {rotation : form.SpecialOrthogonal}

/-- Complete a retained non-null perpendicular first direction using the original cached rotation chart.

The affine branch consumes the stored normalization and its exact
projective scale. The boundary branch consumes the stored non-null axis
and half-turn equation. Both return the original form-indexed two-half-turn
factorization, whose product is also the corresponding reflection product.
-/
@[expose] def factorizationFromPerpendicular (witness : RotationAxisSpreadWitness form rotation)
    (first : form.PerpendicularNonNullVectorWitness witness.axis) : form.TwoHalfTurnFactorization rotation := by
  let second : Σ' value : Vector3 K, Σ' nonNull : form.quadrance value ≠ 0,
      form.reflectionProductRotation first.value value first.nonNull nonNull = rotation := by
    cases witness.chart with
    | affine normalization =>
      have perpendicular : form.Perpendicular first.value normalization.anchor := by
        rcases normalization.equivalent with ⟨factor, factorNonzero, valueEqual⟩
        have vectors := congrArg Form.EvenClifford.vector valueEqual
        change witness.representative.vector = Vector3.scale factor normalization.anchor at vectors
        have pairing : form.bilinear first.value witness.representative.vector = 0 := by
          rw [← witness.axis_eq]
          exact first.perpendicular
        rw [vectors, form.bilinear_scale_right] at pairing
        exact ExplicitField.eq_zero_of_mul_eq_zero_left factorNonzero pairing
      exact ⟨form.capSecondMirror normalization.anchor first.value,
        form.capSecondMirror_nonNull normalization.anchor first.value normalization.defined
          first.nonNull perpendicular,
        (form.reflectionProduct_capSecondMirror normalization.anchor first.value normalization.defined
          first.nonNull perpendicular).trans (normalization.actionRotation_eq.trans witness.represents)⟩
    | atInfinity _scalarZero axisNonNull actionEqual =>
      have perpendicular : form.Perpendicular first.value witness.representative.vector := by
        rw [← witness.axis_eq]
        exact first.perpendicular
      exact ⟨form.halfTurnSecondMirror witness.representative.vector first.value,
        form.halfTurnSecondMirror_nonNull witness.representative.vector first.value axisNonNull
          first.nonNull perpendicular,
        (form.reflectionProduct_halfTurnSecondMirror witness.representative.vector first.value axisNonNull
          first.nonNull perpendicular).trans (actionEqual.symm.trans witness.represents)⟩
  exact
    { firstAxis := first.value
      firstNonNull := first.nonNull
      secondAxis := second.1
      secondNonNull := second.2.1
      rotation_eq := (form.halfTurnRotation_mul first.value second.1 first.nonNull second.2.1).trans second.2.2 }

/-- Completing the cached chart retains the exact supplied first direction. -/
theorem factorizationFromPerpendicular_firstAxis (witness : RotationAxisSpreadWitness form rotation)
    (first : form.PerpendicularNonNullVectorWitness witness.axis) :
    (witness.factorizationFromPerpendicular first).firstAxis = first.value := rfl

end Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm.RotationAxisSpreadWitness

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- Construct two factorizations of an original rotation with explicitly distinct first mirror lines.

One cached axis/spread witness supplies both original chart completions.
The alternate perpendicular direction retains non-nullness and a proof
that no nonzero scalar takes the first supplied direction to the second.
Both returned objects are indexed by the same requested rotation.
-/
@[expose] def distinctFirstMirrorFactorizations [DecidableEq K] (form : TernaryForm K)
    (rotation : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    Σ' first : form.TwoHalfTurnFactorization rotation, Σ' second : form.TwoHalfTurnFactorization rotation,
      ¬ ∃ factor : K, factor ≠ 0 ∧ second.firstAxis = Vector3.scale factor first.firstAxis := by
  let witness := rotationAxisSpreadWitness form rotation twoNonzero
  let first : form.PerpendicularNonNullVectorWitness witness.axis :=
    ⟨witness.perpendicular, witness.perpendicularToAxis, witness.perpendicularNonNull⟩
  let alternate := first.alternateDirection twoNonzero
  refine ⟨witness.factorizationFromPerpendicular first, witness.factorizationFromPerpendicular alternate.1, ?_⟩
  rw [RotationAxisSpreadWitness.factorizationFromPerpendicular_firstAxis,
    RotationAxisSpreadWitness.factorizationFromPerpendicular_firstAxis]
  exact alternate.2

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
