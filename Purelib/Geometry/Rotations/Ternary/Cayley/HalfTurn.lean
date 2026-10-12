module

public import Purelib.Geometry.Rotations.Ternary.Cayley
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.Tactic.Ring

/-!
# Half turns at the boundary of the ternary Cayley chart

Half spread one forces the scalar coordinate of the retained Clifford
representative to vanish. Its original vector coordinate is then non-null
and gives the half-turn axis without a spectral decomposition.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Squares
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

namespace NonNullEvenClifford

/-- Half spread one forces the original Clifford scalar coordinate to vanish. -/
theorem scalar_eq_zero_of_halfSpread_eq_one [DecidableEq K] {form : Form K}
    (value : form.NonNullEvenClifford) (twoNonzero : (2 : K) ≠ 0)
    (halfSpreadOne : rotationHalfSpread form (NonNullEvenClifford.actionRotation value) = 1) :
    value.toEvenClifford.scalar = 0 := by
  have ratioOne := NonNullEvenClifford.rotationHalfSpread_actionRotation value twoNonzero
  rw [halfSpreadOne] at ratioOne
  have weightedQuadrance : form.determinant * form.quadrance value.toEvenClifford.vector =
      EvenClifford.norm value.toEvenClifford := by
    calc
      _ = (form.determinant * form.quadrance value.toEvenClifford.vector /
          EvenClifford.norm value.toEvenClifford) * EvenClifford.norm value.toEvenClifford :=
        (ExplicitField.div_mul_cancel _ value.normNonzero).symm
      _ = _ := by rw [← ratioOne, one_mul]
  have scalarSquareZero : value.toEvenClifford.scalar ^ 2 = 0 := by
    calc
      _ = EvenClifford.norm value.toEvenClifford -
          form.determinant * form.quadrance value.toEvenClifford.vector := by
        unfold EvenClifford.norm
        ring1
      _ = 0 := by rw [weightedQuadrance]; ring1
  exact eq_zero_of_square_eq_zero _ scalarSquareZero

end NonNullEvenClifford

namespace RotationAxisSpreadWitness

/-- The retained axis is non-null when the original rotation has half spread one. -/
theorem axisNonNull_of_halfSpread_eq_one [DecidableEq K] {form : Form K}
    {rotation : form.SpecialOrthogonal} (witness : RotationAxisSpreadWitness form rotation)
    (twoNonzero : (2 : K) ≠ 0) (halfSpreadOne : rotationHalfSpread form rotation = 1) :
    form.quadrance witness.axis ≠ 0 := by
  have representedOne : rotationHalfSpread form (NonNullEvenClifford.actionRotation witness.representative) = 1 := by
    rw [witness.represents]
    exact halfSpreadOne
  have scalarZero := NonNullEvenClifford.scalar_eq_zero_of_halfSpread_eq_one
    witness.representative twoNonzero representedOne
  rw [witness.axis_eq]
  exact NonNullEvenClifford.vectorNonNull_of_scalar_eq_zero witness.representative scalarZero

/-- Half spread one identifies the original rotation with the half turn around its retained axis. -/
theorem halfTurn_eq_of_halfSpread_eq_one [DecidableEq K] {form : Form K}
    {rotation : form.SpecialOrthogonal} (witness : RotationAxisSpreadWitness form rotation)
    (twoNonzero : (2 : K) ≠ 0) (halfSpreadOne : rotationHalfSpread form rotation = 1) :
    form.halfTurnRotation witness.axis
      (witness.axisNonNull_of_halfSpread_eq_one twoNonzero halfSpreadOne) = rotation := by
  have representedOne : rotationHalfSpread form (NonNullEvenClifford.actionRotation witness.representative) = 1 := by
    rw [witness.represents]
    exact halfSpreadOne
  have scalarZero := NonNullEvenClifford.scalar_eq_zero_of_halfSpread_eq_one
    witness.representative twoNonzero representedOne
  have halfTurn := NonNullEvenClifford.actionRotation_eq_halfTurn_of_scalar_eq_zero
    witness.representative scalarZero
  have matrixEqual := congrArg (fun result : form.SpecialOrthogonal => result.matrix)
    (halfTurn.symm.trans witness.represents)
  apply Basic.TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  change form.halfTurn witness.axis _ = rotation.matrix
  change form.halfTurn witness.representative.toEvenClifford.vector _ = rotation.matrix at matrixEqual
  unfold Form.halfTurn Form.reflection at matrixEqual ⊢
  rw [witness.axis_eq]
  exact matrixEqual

/-- The complete fixed-vector space is the retained axis line when half spread is one. -/
theorem fixed_eq_projection_of_halfSpread_eq_one [DecidableEq K] {form : Form K}
    {rotation : form.SpecialOrthogonal} (witness : RotationAxisSpreadWitness form rotation)
    (twoNonzero : (2 : K) ≠ 0) (halfSpreadOne : rotationHalfSpread form rotation = 1) (vector : Vector3 K) :
    Matrix3.rowMul vector rotation.matrix = vector ↔
      vector = Vector3.scale (form.bilinear vector witness.axis / form.quadrance witness.axis) witness.axis := by
  have represents := witness.halfTurn_eq_of_halfSpread_eq_one twoNonzero halfSpreadOne
  have matricesEqual := congrArg (fun result : form.SpecialOrthogonal => result.matrix) represents
  rw [← matricesEqual]
  exact form.rowMul_halfTurn_eq_self_iff_projection witness.axis
    (witness.axisNonNull_of_halfSpread_eq_one twoNonzero halfSpreadOne) twoNonzero vector

end RotationAxisSpreadWitness

/-- Construct the non-null half-turn axis of a rotation with half spread one.

The cached axis/spread witness supplies the original factorization and
Clifford representative. The returned axis and equality retain those exact
data and the original rotation owner.
-/
@[expose] def halfTurnWitness [DecidableEq K] (form : Form K) (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) (halfSpreadOne : rotationHalfSpread form rotation = 1) :
    Σ' axis : Vector3 K, Σ' nonNull : form.quadrance axis ≠ 0,
      form.halfTurnRotation axis nonNull = rotation := by
  let witness := rotationAxisSpreadWitness form rotation twoNonzero
  exact ⟨witness.axis, witness.axisNonNull_of_halfSpread_eq_one twoNonzero halfSpreadOne,
    witness.halfTurn_eq_of_halfSpread_eq_one twoNonzero halfSpreadOne⟩

/-- Half spread one is equivalent to a non-null half-turn representation of the original rotation. -/
theorem halfSpread_eq_one_iff_halfTurn [DecidableEq K] (form : Form K)
    (rotation : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    rotationHalfSpread form rotation = 1 ↔
      ∃ axis : Vector3 K, ∃ nonNull : form.quadrance axis ≠ 0, form.halfTurnRotation axis nonNull = rotation := by
  constructor
  · intro halfSpreadOne
    let witness := halfTurnWitness form rotation twoNonzero halfSpreadOne
    exact ⟨witness.1, witness.2.1, witness.2.2⟩
  · rintro ⟨axis, nonNull, represents⟩
    rw [← represents]
    exact rotationHalfSpread_halfTurn form axis nonNull twoNonzero

/-- Every nonzero row-space vector of identity plus a half-spread-one rotation gives its original half turn.

The cached half-turn witness supplies the original non-null axis. The
literal projection coefficient identifies the supplied row-space vector
with a nonzero multiple of that axis, retaining the original rotation
and the computed vector's non-null certificate.
-/
@[expose] def halfTurnRowWitness [DecidableEq K] (form : Form K) (rotation : form.SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) (halfSpreadOne : rotationHalfSpread form rotation = 1)
    (input : Vector3 K)
    (nonzero : Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix) ≠ Vector3.zero) :
    Σ' nonNull : form.quadrance (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix)) ≠ 0,
      form.halfTurnRotation (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix))
        nonNull = rotation := by
  let witness := halfTurnWitness form rotation twoNonzero halfSpreadOne
  have matrixEquality := congrArg (fun value : form.SpecialOrthogonal => value.matrix) witness.2.2
  change form.halfTurn witness.1 witness.2.1 = rotation.matrix at matrixEquality
  have rowNonzero : Matrix3.rowMul input
      (Matrix3.add Matrix3.identity (form.halfTurn witness.1 witness.2.1)) ≠ Vector3.zero := by
    rw [matrixEquality]
    exact nonzero
  have nonNull : form.quadrance (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix)) ≠ 0 := by
    rw [← matrixEquality]
    exact form.quadrance_rowMul_identity_add_halfTurn_ne_zero witness.1 input witness.2.1 rowNonzero
  refine ⟨nonNull, ?_⟩
  have coefficientNonzero : 2 * form.bilinear input witness.1 / form.quadrance witness.1 ≠ 0 := by
    intro coefficientZero
    apply rowNonzero
    rw [form.rowMul_identity_add_halfTurn, coefficientZero, Vector3.zero_scale]
  have sameLine : form.halfTurn witness.1 witness.2.1 =
      form.halfTurn (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix)) nonNull := by
    apply (form.halfTurn_eq_iff_same_line _ _ witness.2.1 nonNull twoNonzero).mpr
    refine ⟨_, coefficientNonzero, ?_⟩
    rw [← matrixEquality, form.rowMul_identity_add_halfTurn]
  have sameRotation : form.halfTurnRotation witness.1 witness.2.1 =
      form.halfTurnRotation (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix)) nonNull :=
    Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.eq_of_matrix_eq _ _ sameLine
  exact sameRotation.symm.trans witness.2.2

end Purelib.Geometry.Rotations.Ternary.Cayley.TernaryForm

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- Construct the second mirror normal for a half turn from its axis and a supplied first normal. -/
@[expose] def halfTurnSecondMirror (form : TernaryForm K) (axis first : Vector3 K) : Vector3 K :=
  form.cliffordCross axis first

/-- The first and constructed half-turn normals are perpendicular. -/
theorem bilinear_halfTurnSecondMirror (form : TernaryForm K) (axis first : Vector3 K) :
    form.bilinear first (form.halfTurnSecondMirror axis first) = 0 := by
  unfold halfTurnSecondMirror
  rw [form.bilinear_comm, form.cliffordCross_perpendicular_right]

/-- A perpendicular first normal gives the second half-turn normal's determinant-weighted quadrance. -/
theorem quadrance_halfTurnSecondMirror (form : TernaryForm K) (axis first : Vector3 K)
    (perpendicular : form.Perpendicular first axis) :
    form.quadrance (form.halfTurnSecondMirror axis first) =
      form.determinant * (form.quadrance axis * form.quadrance first) := by
  unfold halfTurnSecondMirror
  rw [form.quadrance_cliffordCross, form.bilinear_comm axis first, perpendicular]
  ring1

/-- A non-null axis and non-null perpendicular first normal give a non-null second normal. -/
theorem halfTurnSecondMirror_nonNull (form : TernaryForm K) (axis first : Vector3 K)
    (axisNonNull : form.quadrance axis ≠ 0) (firstNonNull : form.quadrance first ≠ 0)
    (perpendicular : form.Perpendicular first axis) :
    form.quadrance (form.halfTurnSecondMirror axis first) ≠ 0 := by
  rw [form.quadrance_halfTurnSecondMirror axis first perpendicular]
  exact ExplicitField.mul_ne_zero form.determinantNonzero (ExplicitField.mul_ne_zero axisNonNull firstNonNull)

/-- The cross of the two constructed half-turn normals is the determinant-weighted first quadrance times the axis. -/
theorem cliffordCross_halfTurnSecondMirror (form : TernaryForm K) (axis first : Vector3 K)
    (perpendicular : form.Perpendicular first axis) :
    form.cliffordCross first (form.halfTurnSecondMirror axis first) =
      Vector3.scale (form.determinant * form.quadrance first) axis := by
  unfold halfTurnSecondMirror
  rw [form.cliffordCross_vector_triple, perpendicular]
  ext <;> unfold Vector3.sub Vector3.scale TernaryForm.quadrance <;> ring1

/-- Every non-null perpendicular first mirror yields a two-reflection factorization of the original half turn.

The two pure Clifford representatives multiply to a nonzero scalar multiple
of the original axis representative. Its action is the requested half turn,
with the supplied first normal and the computed second normal retained.
-/
theorem reflectionProduct_halfTurnSecondMirror (form : TernaryForm K) (axis first : Vector3 K)
    (axisNonNull : form.quadrance axis ≠ 0) (firstNonNull : form.quadrance first ≠ 0)
    (perpendicular : form.Perpendicular first axis) :
    form.reflectionProductRotation first (form.halfTurnSecondMirror axis first) firstNonNull
        (form.halfTurnSecondMirror_nonNull axis first axisNonNull firstNonNull perpendicular) =
      form.halfTurnRotation axis axisNonNull := by
  let second := form.halfTurnSecondMirror axis first
  let secondNonNull := form.halfTurnSecondMirror_nonNull axis first axisNonNull firstNonNull perpendicular
  let value := NonNullEvenClifford.mul (NonNullEvenClifford.halfTurnValue form first firstNonNull)
    (NonNullEvenClifford.halfTurnValue form second secondNonNull)
  have factorNonzero : -(form.determinant * form.quadrance first) ≠ 0 := by
    intro zero
    have productNonzero := ExplicitField.mul_ne_zero form.determinantNonzero firstNonNull
    apply productNonzero
    calc
      _ = -(-(form.determinant * form.quadrance first)) := by ring1
      _ = 0 := by rw [zero]; ring1
  have equivalent : NonNullEvenClifford.Equivalent
      (NonNullEvenClifford.halfTurnValue form axis axisNonNull) value := by
    refine ⟨-(form.determinant * form.quadrance first), factorNonzero, ?_⟩
    apply EvenClifford.ext
    · change 0 * 0 - form.determinant * form.bilinear first second =
        -(form.determinant * form.quadrance first) * 0
      rw [form.bilinear_halfTurnSecondMirror]
      ring1
    · change Vector3.sub (Vector3.add (Vector3.scale 0 second) (Vector3.scale 0 first))
        (form.cliffordCross first second) = Vector3.scale (-(form.determinant * form.quadrance first)) axis
      rw [form.cliffordCross_halfTurnSecondMirror axis first perpendicular]
      ext <;> unfold Vector3.sub Vector3.add Vector3.scale <;> ring1
  calc
    _ = NonNullEvenClifford.actionRotation value :=
      (form.halfTurnRotation_mul first second firstNonNull secondNonNull).symm.trans
        (NonNullEvenClifford.halfTurnRotation_mul form first second firstNonNull secondNonNull)
    _ = NonNullEvenClifford.actionRotation (NonNullEvenClifford.halfTurnValue form axis axisNonNull) :=
      (NonNullEvenClifford.actionRotation_respects_equivalent equivalent).symm
    _ = _ := NonNullEvenClifford.halfTurnValue_actionRotation form axis axisNonNull

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
