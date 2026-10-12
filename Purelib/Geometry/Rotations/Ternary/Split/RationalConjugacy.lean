module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Clifford.Split.Matrix
import Purelib.Geometry.Quadratic.Ternary.SplitNullConic
import Purelib.Geometry.Rotations.Ternary.Split.Parabolic
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Minkowski
public import Purelib.Geometry.Quadratic.Ternary.RationalNullBasis
import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.Geometry.Rotations.Ternary.Clifford
public import Purelib.Geometry.Rotations.Ternary.Theory
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Algebra.Clifford.Split.Matrix

open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.Geometry.Quadratic.Ternary.RationalNullBasis

open Purelib.Geometry.Quadratic.Ternary.RationalNullBasis.MinkowskiClifford

open Purelib.Geometry.Quadratic.Ternary.SplitNullConic

open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm

open Purelib.Geometry.Rotations.Ternary.Split.Parabolic

open Purelib.Geometry.Rotations.Ternary.Theory

open Purelib.LinearAlgebra

section
@[expose] public section

/-!
# Pairwise conjugacy of rational Minkowski parabolics

The split Clifford algebra is the displayed two-by-two matrix algebra.  For
one nonzero null-conic parameter pair this file constructs a finite basis in
which its nilpotent matrix is the standard upper-triangular nilpotent.  The
basis uses one decidable chart and has determinant `-1`.  Two such bases and
the two supplied nonzero parabolic parameters then give an explicit
invertible transport matrix.
-/

namespace Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy

variable {K : Type*} [ExplicitField K]

section MinkowskiClifford

section ParabolicConjugacy

set_option genInjectivity false in
/-- Cached finite transporter data, including its exact determinant and intertwining equation. -/
structure
  TransportMatrixData
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0)
    (leftParameterNonzero : leftParameter ≠ 0)
    (rightParameterNonzero : rightParameter ≠ 0) where
  /-- The cached two-by-two transport matrix. -/ matrix : Coordinates2.Matrix K
  /-- The retained matrix is exactly the explicit transport of the original conic coordinates and parameters. -/
    matrix_eq : matrix = ParabolicConjugacy.transportMatrix leftFirst leftSecond rightFirst
    rightSecond leftParameter rightParameter
  /-- The matrix determinant is the product of the original left and right parameters. -/ determinant_eq :
    Coordinates2.Matrix.determinant matrix = leftParameter * rightParameter
  /-- The retained transport matrix has nonzero determinant. -/ determinant_nonzero : Coordinates2.Matrix.determinant
    matrix ≠ 0
  /-- The retained matrix intertwines the original left and right displayed parabolic matrices. -/ intertwines :
    Coordinates2.Matrix.mul
        (MinkowskiClifford.toMatrix oneNonzero
          (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter leftFirst leftSecond)
            (MinkowskiClifford.nullParameter_isNull oneNonzero leftFirst leftSecond)
            leftParameter).toEvenClifford) matrix =
      Coordinates2.Matrix.mul matrix
        (MinkowskiClifford.toMatrix oneNonzero
          (MinkowskiClifford.parabolicAt oneNonzero (MinkowskiClifford.nullParameter rightFirst rightSecond)
            (MinkowskiClifford.nullParameter_isNull oneNonzero rightFirst rightSecond)
            rightParameter).toEvenClifford)

constructive_injectivity TransportMatrixData

/-- Compute and retain the transporter between two nonzero parameterized null-conic parabolics.

Both conic pairs and both parabolic parameters are nonzero; the output retains the matrix, exact nonzero determinant,
and intertwining identity. -/
def
  transportMatrixData
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0)
    (leftParameterNonzero : leftParameter ≠ 0)
    (rightParameterNonzero : rightParameter ≠ 0) :
    TransportMatrixData
      oneNonzero twoNonzero leftFirst leftSecond rightFirst
      rightSecond leftParameter rightParameter leftCoordinatesNonzero
      rightCoordinatesNonzero leftParameterNonzero rightParameterNonzero := by
  let matrix := ParabolicConjugacy.transportMatrix leftFirst leftSecond rightFirst rightSecond
    leftParameter rightParameter
  have determinantEq := ParabolicConjugacy.transportMatrix_determinant twoNonzero leftFirst
    leftSecond rightFirst rightSecond leftParameter rightParameter
    leftCoordinatesNonzero rightCoordinatesNonzero
  exact
    { matrix := matrix
      matrix_eq := rfl
      determinant_eq := determinantEq
      determinant_nonzero := by
        rw [determinantEq]
        exact ExplicitField.mul_ne_zero leftParameterNonzero
          rightParameterNonzero
      intertwines := ParabolicConjugacy.parabolicMatrix_mul_transportMatrix oneNonzero twoNonzero
        leftFirst leftSecond rightFirst rightSecond leftParameter
        rightParameter leftCoordinatesNonzero rightCoordinatesNonzero }

end ParabolicConjugacy
end MinkowskiClifford
end Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy

section
variable {K : Type*} [ExplicitField K]

namespace Purelib.Algebra.Clifford.Split.Matrix.MinkowskiClifford

open _root_.Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy
/-- The split Clifford matrix representation preserves scalar multiplication. -/
private theorem
  toMatrix_scale
  (oneNonzero : (1 : K) ≠ 0)
    (factor : K)
    (value : (TernaryForm.minkowski oneNonzero).EvenClifford) :
    MinkowskiClifford.toMatrix oneNonzero (EvenClifford.scale factor value) =
      Coordinates2.Matrix.scalarScale factor (MinkowskiClifford.toMatrix oneNonzero value) := by
  apply Coordinates2.Matrix.ext <;>
    unfold MinkowskiClifford.toMatrix EvenClifford.scale Coordinates2.Matrix.scalarScale
      Coordinates3.Vector.scale <;> ring1
end Purelib.Algebra.Clifford.Split.Matrix.MinkowskiClifford
end

namespace Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy

variable {K : Type*} [ExplicitField K]

section MinkowskiClifford

section ParabolicConjugacy

/-- Lift an explicitly invertible split matrix to a non-null Clifford value. The determinant certificate becomes the
cached reduced-norm certificate. -/
def
  nonNullFromMatrix
  (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (matrix : Coordinates2.Matrix K)
    (determinantNonzero : Coordinates2.Matrix.determinant matrix ≠ 0) :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford where
  toEvenClifford := MinkowskiClifford.fromMatrix oneNonzero matrix
  normNonzero := by
    have determinantEq := MinkowskiClifford.determinant_toMatrix oneNonzero
      (MinkowskiClifford.fromMatrix oneNonzero matrix)
    rw [MinkowskiClifford.toMatrix_fromMatrix oneNonzero twoNonzero matrix] at determinantEq
    rw [← determinantEq]
    exact determinantNonzero

/-- Reading the matrix of the lifted non-null Clifford value recovers the original invertible matrix. -/
theorem
  toMatrix_nonNullFromMatrix
  (oneNonzero : (1 : K) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) (matrix : Coordinates2.Matrix K)
    (determinantNonzero : Coordinates2.Matrix.determinant matrix ≠ 0) :
    MinkowskiClifford.toMatrix oneNonzero
        (nonNullFromMatrix
          oneNonzero twoNonzero matrix
          determinantNonzero).toEvenClifford = matrix :=
  MinkowskiClifford.toMatrix_fromMatrix oneNonzero twoNonzero matrix

/-- The matrix transporter, lifted to a non-null Clifford value, conjugates the left displayed parabolic to a
projectively equivalent representative of the right displayed parabolic. -/
theorem
  transported_parabolic_equivalent
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftFirst leftSecond rightFirst rightSecond leftParameter
      rightParameter : K)
    (leftCoordinatesNonzero : leftFirst ≠ 0 ∨ leftSecond ≠ 0)
    (rightCoordinatesNonzero : rightFirst ≠ 0 ∨ rightSecond ≠ 0)
    (leftParameterNonzero : leftParameter ≠ 0)
    (rightParameterNonzero : rightParameter ≠ 0) :
    let data :=
      transportMatrixData
      oneNonzero twoNonzero leftFirst
      leftSecond rightFirst rightSecond leftParameter rightParameter
      leftCoordinatesNonzero rightCoordinatesNonzero leftParameterNonzero
      rightParameterNonzero
    let conjugator :=
      nonNullFromMatrix
      oneNonzero twoNonzero data.matrix
      data.determinant_nonzero
    let left := MinkowskiClifford.parabolicAt oneNonzero
      (MinkowskiClifford.nullParameter leftFirst leftSecond)
      (MinkowskiClifford.nullParameter_isNull oneNonzero leftFirst leftSecond) leftParameter
    let right := MinkowskiClifford.parabolicAt oneNonzero
      (MinkowskiClifford.nullParameter rightFirst rightSecond)
      (MinkowskiClifford.nullParameter_isNull oneNonzero rightFirst rightSecond) rightParameter
    (NonNullEvenClifford.Equivalent right)
      (NonNullEvenClifford.mul
        (NonNullEvenClifford.mul (NonNullEvenClifford.conjugate conjugator) left)
        conjugator) := by
  let data :=
    transportMatrixData
    oneNonzero twoNonzero leftFirst
    leftSecond rightFirst rightSecond leftParameter rightParameter
    leftCoordinatesNonzero rightCoordinatesNonzero leftParameterNonzero
    rightParameterNonzero
  let conjugator :=
    nonNullFromMatrix oneNonzero
    twoNonzero data.matrix
    data.determinant_nonzero
  let left := MinkowskiClifford.parabolicAt oneNonzero
    (MinkowskiClifford.nullParameter leftFirst leftSecond)
    (MinkowskiClifford.nullParameter_isNull oneNonzero leftFirst leftSecond) leftParameter
  let right := MinkowskiClifford.parabolicAt oneNonzero
    (MinkowskiClifford.nullParameter rightFirst rightSecond)
    (MinkowskiClifford.nullParameter_isNull oneNonzero rightFirst rightSecond) rightParameter
  change (NonNullEvenClifford.Equivalent right)
    (NonNullEvenClifford.mul
      (NonNullEvenClifford.mul (NonNullEvenClifford.conjugate conjugator) left)
      conjugator)
  refine ⟨Coordinates2.Matrix.determinant data.matrix, data.determinant_nonzero, ?_⟩
  change EvenClifford.mul
      (EvenClifford.mul
        (EvenClifford.conjugate conjugator.toEvenClifford) left.toEvenClifford)
      conjugator.toEvenClifford =
    EvenClifford.scale (Coordinates2.Matrix.determinant data.matrix)
      right.toEvenClifford
  apply MinkowskiClifford.toMatrix_injective oneNonzero twoNonzero
  rw [MinkowskiClifford.toMatrix_mul, MinkowskiClifford.toMatrix_mul, MinkowskiClifford.toMatrix_conjugate,
    Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy.toMatrix_nonNullFromMatrix,
      Purelib.Algebra.Clifford.Split.Matrix.MinkowskiClifford.toMatrix_scale]
  calc
    Coordinates2.Matrix.mul
          (Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate data.matrix)
            (MinkowskiClifford.toMatrix oneNonzero left.toEvenClifford)) data.matrix =
        Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate data.matrix)
          (Coordinates2.Matrix.mul (MinkowskiClifford.toMatrix oneNonzero left.toEvenClifford)
            data.matrix) := Coordinates2.Matrix.mul_assoc _ _ _
    _ = Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate data.matrix)
        (Coordinates2.Matrix.mul data.matrix
          (MinkowskiClifford.toMatrix oneNonzero right.toEvenClifford)) := by
      rw [data.intertwines]
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.mul (Coordinates2.Matrix.adjugate data.matrix) data.matrix)
        (MinkowskiClifford.toMatrix oneNonzero right.toEvenClifford) :=
      (Coordinates2.Matrix.mul_assoc _ _ _).symm
    _ = Coordinates2.Matrix.mul
        (Coordinates2.Matrix.scalarScale (Coordinates2.Matrix.determinant data.matrix) Coordinates2.Matrix.identity)
        (MinkowskiClifford.toMatrix oneNonzero right.toEvenClifford) := by
      rw [Coordinates2.Matrix.adjugate_mul]
    _ = Coordinates2.Matrix.scalarScale (Coordinates2.Matrix.determinant data.matrix)
        (MinkowskiClifford.toMatrix oneNonzero right.toEvenClifford) :=
      Purelib.LinearAlgebra.Coordinates2.Matrix.scale_identity_mul _ _

set_option genInjectivity false in
/-- Fully cached constructive conjugacy data for two rational parabolic rotations. The witness retains the executable
split matrix, its determinant certificate, its Clifford lift, and the resulting special-orthogonal conjugator. -/
structure
  ParabolicConjugacyWitness
    (oneNonzero : (1 : K) ≠ 0)
    (left right :
      (TernaryForm.minkowski oneNonzero).SpecialOrthogonal) where
  /-- The cached invertible split matrix underlying the conjugator. -/ matrix : Coordinates2.Matrix K
  /-- The retained split matrix has nonzero determinant. -/ determinantNonzero : Coordinates2.Matrix.determinant matrix
    ≠ 0
  /-- The cached non-null Clifford lift of the retained split matrix. -/ conjugatorValue :
    (TernaryForm.minkowski oneNonzero).NonNullEvenClifford
  /-- The Clifford lift reads back exactly as the retained split matrix. -/ conjugatorMatrix :
    MinkowskiClifford.toMatrix oneNonzero conjugatorValue.toEvenClifford = matrix
  /-- The cached special orthogonal conjugating rotation. -/ conjugator : (TernaryForm.minkowski
    oneNonzero).SpecialOrthogonal
  /-- The retained conjugator is exactly the rotation action of the cached Clifford lift. -/ conjugator_eq : conjugator
    = (NonNullEvenClifford.actionRotation conjugatorValue)
  /-- Conjugation by the retained rotation takes the original left rotation to the original right rotation. -/
    conjugates :
    SpecialOrthogonal.mul
        (SpecialOrthogonal.mul
          (SpecialOrthogonal.inverse conjugator) left)
        conjugator = right

constructive_injectivity ParabolicConjugacyWitness

/-- Given any two complete parabolic classifications, compute a rational conjugator between their rotations. In
particular, the nonidentity split rational parabolics form one conjugacy class; no square-class or infinitary orbit
argument is needed. -/
def
  parabolicConjugacyWitness
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftRotation rightRotation :
      (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (leftClassification :
      MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero leftRotation)
    (rightClassification :
      MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero rightRotation) :
    ParabolicConjugacyWitness
      oneNonzero leftRotation rightRotation := by
  let leftFirst := leftClassification.coordinates.first
  let leftSecond := leftClassification.coordinates.second
  let rightFirst := rightClassification.coordinates.first
  let rightSecond := rightClassification.coordinates.second
  let leftParameter := leftClassification.parameter
  let rightParameter := rightClassification.parameter
  let data :=
    transportMatrixData
    oneNonzero twoNonzero leftFirst leftSecond
    rightFirst rightSecond leftParameter rightParameter
    leftClassification.coordinates.parametersNonzero
    rightClassification.coordinates.parametersNonzero
    leftClassification.parameterNonzero rightClassification.parameterNonzero
  let conjugatorValue :=
    nonNullFromMatrix oneNonzero
    twoNonzero data.matrix
    data.determinant_nonzero
  let leftNormal := MinkowskiClifford.parabolicAt oneNonzero
    (MinkowskiClifford.nullParameter leftFirst leftSecond)
    (MinkowskiClifford.nullParameter_isNull oneNonzero leftFirst leftSecond) leftParameter
  let rightNormal := MinkowskiClifford.parabolicAt oneNonzero
    (MinkowskiClifford.nullParameter rightFirst rightSecond)
    (MinkowskiClifford.nullParameter_isNull oneNonzero rightFirst rightSecond) rightParameter
  have equivalent : (NonNullEvenClifford.Equivalent rightNormal)
      (NonNullEvenClifford.mul
        (NonNullEvenClifford.mul
          (NonNullEvenClifford.conjugate conjugatorValue) leftNormal) conjugatorValue) := by
    exact
      transported_parabolic_equivalent
      oneNonzero twoNonzero leftFirst
      leftSecond rightFirst rightSecond leftParameter rightParameter
      leftClassification.coordinates.parametersNonzero
      rightClassification.coordinates.parametersNonzero
      leftClassification.parameterNonzero rightClassification.parameterNonzero
  have leftRotationEq : leftRotation = (NonNullEvenClifford.actionRotation leftNormal) :=
    leftClassification.rotation_eq
  have rightRotationEq : rightRotation = (NonNullEvenClifford.actionRotation rightNormal) :=
    rightClassification.rotation_eq
  have conjugates :
      SpecialOrthogonal.mul
          (SpecialOrthogonal.mul
            (SpecialOrthogonal.inverse
              (NonNullEvenClifford.actionRotation conjugatorValue)) leftRotation)
          (NonNullEvenClifford.actionRotation conjugatorValue) = rightRotation := by
    calc
      SpecialOrthogonal.mul
            (SpecialOrthogonal.mul
              (SpecialOrthogonal.inverse
                (NonNullEvenClifford.actionRotation conjugatorValue)) leftRotation)
            (NonNullEvenClifford.actionRotation conjugatorValue) =
          SpecialOrthogonal.mul
            (SpecialOrthogonal.mul
              (SpecialOrthogonal.inverse
                (NonNullEvenClifford.actionRotation conjugatorValue)) (NonNullEvenClifford.actionRotation leftNormal))
            (NonNullEvenClifford.actionRotation conjugatorValue) := by
        rw [leftRotationEq]
      _ = SpecialOrthogonal.mul
          (SpecialOrthogonal.mul
            (NonNullEvenClifford.actionRotation (NonNullEvenClifford.conjugate conjugatorValue))
            (NonNullEvenClifford.actionRotation leftNormal)) (NonNullEvenClifford.actionRotation conjugatorValue) := by
        rw [NonNullEvenClifford.actionRotation_conjugate]
      _ = (NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul
          (NonNullEvenClifford.mul
            (NonNullEvenClifford.conjugate conjugatorValue) leftNormal)
          conjugatorValue)) := by
        rw [NonNullEvenClifford.actionRotation_mul,
          NonNullEvenClifford.actionRotation_mul]
      _ = (NonNullEvenClifford.actionRotation rightNormal) :=
        (NonNullEvenClifford.actionRotation_respects_equivalent
          equivalent).symm
      _ = rightRotation := rightRotationEq.symm
  exact
    { matrix := data.matrix
      determinantNonzero := data.determinant_nonzero
      conjugatorValue := conjugatorValue
      conjugatorMatrix :=
        toMatrix_nonNullFromMatrix
        oneNonzero twoNonzero
        data.matrix data.determinant_nonzero
      conjugator := (NonNullEvenClifford.actionRotation conjugatorValue)
      conjugator_eq := rfl
      conjugates := conjugates }

/-- Paper-facing existence statement extracted from the executable witness: any two classified nonidentity rational
parabolics are conjugate inside the displayed split special-orthogonal group. -/
theorem
  parabolics_pairwise_conjugate
  [DecidableEq K]
    (oneNonzero : (1 : K) ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (leftRotation rightRotation :
      (TernaryForm.minkowski oneNonzero).SpecialOrthogonal)
    (leftClassification :
      MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero leftRotation)
    (rightClassification :
      MinkowskiClifford.ParabolicClassification oneNonzero twoNonzero rightRotation) :
    ∃ conjugator :
        (TernaryForm.minkowski oneNonzero).SpecialOrthogonal,
      SpecialOrthogonal.mul
          (SpecialOrthogonal.mul
            (SpecialOrthogonal.inverse conjugator) leftRotation)
          conjugator = rightRotation := by
  let witness :=
    parabolicConjugacyWitness
    oneNonzero twoNonzero leftRotation
    rightRotation leftClassification rightClassification
  exact ⟨witness.conjugator, witness.conjugates⟩

end ParabolicConjugacy

end MinkowskiClifford

end Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy

end
