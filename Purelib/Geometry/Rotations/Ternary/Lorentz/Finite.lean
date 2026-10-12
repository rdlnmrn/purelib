module

public import Purelib.Geometry.Projective.Matrix.Finite
public import Purelib.Geometry.Rotations.Ternary.Lorentz.Projective
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.Algebra.Clifford.Lorentz.Matrix
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Data.List.Nodup
import Purelib.LinearAlgebra.Coordinates2.Invertible
import Purelib.LinearAlgebra.Coordinates3.Vector

/-!
# Finite Lorentz rotation enumeration

The original canonical quaternion charts determine projective invertible
matrices through one retained splitting certificate. The Lorentz matrix
action transports that exact finite list to all time-first Lorentz rotations.
The two canonical projective-line factors enumerate the null proportions
directly through the same original Lorentz matrix decoder.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Finite.Odd.Presentation (FiniteOddFieldPresentation TwoSquareRepresentation)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Algebra.Clifford.Lorentz
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Data.List
open Purelib.Geometry.Projective
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)
    (presentation : FiniteOddFieldPresentation K) (split : TwoSquareRepresentation (-1 : K))

/-- Transport the retained projective matrix list to time-first Lorentz rotations.

The same splitting certificate is used for every source matrix. The
original finite list order is retained, and each output is the original
Lorentz Clifford action of its decoded non-null matrix.
-/
@[expose] def finiteRotations : List (Form.lorentz oneNonzero).SpecialOrthogonal :=
  (Matrix.Finite.representatives presentation split).map (matrixRotation oneNonzero presentation.twoNonzero)

/-- The transported finite Lorentz rotation list contains no duplicate rotations. -/
theorem finiteRotations_nodup : (finiteRotations oneNonzero presentation split).Nodup := by
  apply Pairwise.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ (Matrix.Finite.representatives_nodup presentation split)
  intro left right leftMember rightMember distinct equal
  exact distinct (Matrix.Finite.eq_of_equivalent presentation split leftMember rightMember
    ((matrixRotation_eq_iff_equivalent oneNonzero presentation.twoNonzero left right).mp equal))

/-- Every displayed Lorentz rotation occurs in the transported finite list.

Its original executable Clifford preimage is converted to an invertible
matrix and normalized in the retained finite charts. The exact matrix
scale witness preserves the original represented rotation.
-/
theorem finiteRotations_complete (value : (Form.lorentz oneNonzero).SpecialOrthogonal) :
    value ∈ finiteRotations oneNonzero presentation split := by
  letI : DecidableEq K := presentation.eqDecidable
  let representative := rotationMatrixRepresentative oneNonzero presentation.twoNonzero value
  let normalized := Matrix.Finite.normalize presentation split representative
  apply Map.mem_map.mpr
  refine ⟨normalized, Matrix.Finite.normalize_mem presentation split representative, ?_⟩
  calc
    matrixRotation oneNonzero presentation.twoNonzero normalized =
        matrixRotation oneNonzero presentation.twoNonzero representative :=
      (matrixRotation_eq_iff_equivalent oneNonzero presentation.twoNonzero normalized representative).mpr
        (Matrix.Finite.equivalent_normalize presentation split representative).symm
    _ = value := matrixRotation_rotationMatrixRepresentative oneNonzero presentation.twoNonzero value

/-- The complete duplicate-free Lorentz rotation list has order `q(q²-1)`.

The length is transported from the same canonical projective matrix list.
Completeness and duplicate-freeness therefore make this the actual rotation
count for the displayed odd finite field and original Lorentz form.
-/
theorem finiteRotations_length :
    (finiteRotations oneNonzero presentation split).length = presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1) :=
  (Map.length_map _ _).trans (Matrix.Finite.representatives_length presentation split)

/-- Decode the canonical singular matrices into original null Lorentz dihedrons.

The column and row projective charts fix one matrix per nonzero scalar
class. Each original matrix is decoded by its retained half-sums and
differences, with the same time-first Lorentz form owner.
-/
@[expose] def finiteNullProportions : List (Form.lorentz oneNonzero).EvenClifford :=
  (Geometry.Projective.Matrix.Finite.singularRepresentatives presentation).map (Matrix.fromMatrix oneNonzero)

/-- The listed null dihedrons have exactly `(q+1)²` distinct representatives. -/
theorem finiteNullProportions_length :
    (finiteNullProportions oneNonzero presentation).length =
      (presentation.carrier.length + 1) * (presentation.carrier.length + 1) :=
  (Map.length_map _ _).trans (Geometry.Projective.Matrix.Finite.singularRepresentatives_length presentation)

/-- The null-dihedron chart list has no repeated original Clifford records. -/
theorem finiteNullProportions_nodup : (finiteNullProportions oneNonzero presentation).Nodup := by
  apply Nodup.nodup_map_of_injective
  · intro left right equal
    calc
      left = Matrix.toMatrix oneNonzero (Matrix.fromMatrix oneNonzero left) :=
        (Matrix.toMatrix_fromMatrix oneNonzero presentation.twoNonzero left).symm
      _ = Matrix.toMatrix oneNonzero (Matrix.fromMatrix oneNonzero right) :=
        congrArg (Matrix.toMatrix oneNonzero) equal
      _ = right := Matrix.toMatrix_fromMatrix oneNonzero presentation.twoNonzero right
  · exact Geometry.Projective.Matrix.Finite.singularRepresentatives_nodup presentation

/-- Every listed null proportion is nonzero and has zero original Clifford norm.

The decoded matrix has an original nonzero entry and zero determinant.
Exact matrix recovery reflects nonzeroness, while the determinant identity
reads back the norm on that same original Clifford parent.
-/
theorem finiteNullProportions_nonzero_null {value : (Form.lorentz oneNonzero).EvenClifford}
    (member : value ∈ finiteNullProportions oneNonzero presentation) :
    value ≠ ⟨0, Vector3.zero⟩ ∧ EvenClifford.norm value = 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  rcases Map.mem_map.mp member with ⟨matrix, matrixMember, equal⟩
  have properties := Geometry.Projective.Matrix.Finite.singularRepresentatives_nonzero_singular
    presentation matrixMember
  have readback : Matrix.toMatrix oneNonzero value = matrix :=
    (congrArg (Matrix.toMatrix oneNonzero) equal.symm).trans
      (Matrix.toMatrix_fromMatrix oneNonzero presentation.twoNonzero matrix)
  constructor
  · intro zeroValue
    apply (Matrix2.isNonzero_iff_ne_zero matrix).mp properties.1
    calc
      matrix = Matrix.toMatrix oneNonzero value := readback.symm
      _ = Matrix.toMatrix oneNonzero ⟨0, Vector3.zero⟩ := congrArg (Matrix.toMatrix oneNonzero) zeroValue
      _ = ⟨0, 0, 0, 0⟩ := by
        apply Matrix2.ext
        · exact sub_self (0 : K)
        · exact sub_self (0 : K)
        · change -(0 : K) - 0 = 0
          rw [neg_zero]
          exact sub_self (0 : K)
        · exact zero_add (0 : K)
  · exact (Matrix.determinant_toMatrix oneNonzero value).symm.trans
      ((congrArg Matrix2.determinant readback).trans properties.2)

/-- Compute the listed null proportion of an original nonzero null Lorentz dihedron.

The exact original matrix is factored and its two projective factors are
normalized once. The retained product scale is reflected by matrix coordinate
recovery to the same original Lorentz Clifford parent.
-/
@[expose] def finiteNullNormalize (value : (Form.lorentz oneNonzero).EvenClifford)
    (nonzero : value ≠ ⟨0, Vector3.zero⟩) (null : EvenClifford.norm value = 0) :
    Σ' factor : K, Σ' representative : (Form.lorentz oneNonzero).EvenClifford, factor ≠ 0 ∧
      representative ∈ finiteNullProportions oneNonzero presentation ∧
      representative = EvenClifford.scale factor value := by
  letI : DecidableEq K := presentation.eqDecidable
  let normalized := Geometry.Projective.Matrix.Finite.singularNormalize presentation
    (Matrix.toMatrix oneNonzero value)
    (Matrix.toMatrix_nonzero oneNonzero presentation.twoNonzero value nonzero)
    ((Matrix.determinant_toMatrix oneNonzero value).trans null)
  refine ⟨normalized.1, Matrix.fromMatrix oneNonzero normalized.2.1, normalized.2.2.1, ?_, ?_⟩
  · exact Map.mem_map.mpr ⟨normalized.2.1, normalized.2.2.2.1, rfl⟩
  · apply Matrix.toMatrix_injective oneNonzero presentation.twoNonzero
    rw [Matrix.toMatrix_fromMatrix oneNonzero presentation.twoNonzero, Matrix.toMatrix_scale]
    exact normalized.2.2.2.2

/-- Listed Lorentz null proportions related by a nonzero homogeneous scale are equal.

The same original scale relates their singular matrices. The two canonical
projective-line factors determine the matrix class uniquely, and original
Lorentz coordinate recovery retains equality of the decoded parents.
-/
theorem finiteNullProportions_eq_of_scale {left right : (Form.lorentz oneNonzero).EvenClifford}
    (leftMember : left ∈ finiteNullProportions oneNonzero presentation)
    (rightMember : right ∈ finiteNullProportions oneNonzero presentation)
    (factor : K) (nonzero : factor ≠ 0) (represents : right = EvenClifford.scale factor left) : left = right := by
  rcases Map.mem_map.mp leftMember with ⟨leftMatrix, leftMatrixMember, leftEqual⟩
  rcases Map.mem_map.mp rightMember with ⟨rightMatrix, rightMatrixMember, rightEqual⟩
  have leftReadback : Matrix.toMatrix oneNonzero left = leftMatrix :=
    (congrArg (Matrix.toMatrix oneNonzero) leftEqual.symm).trans
      (Matrix.toMatrix_fromMatrix oneNonzero presentation.twoNonzero leftMatrix)
  have rightReadback : Matrix.toMatrix oneNonzero right = rightMatrix :=
    (congrArg (Matrix.toMatrix oneNonzero) rightEqual.symm).trans
      (Matrix.toMatrix_fromMatrix oneNonzero presentation.twoNonzero rightMatrix)
  have matricesEqual := Geometry.Projective.Matrix.Finite.singularRepresentatives_eq_of_scale
    presentation leftMatrixMember rightMatrixMember factor nonzero (by
      calc
        rightMatrix = Matrix.toMatrix oneNonzero right := rightReadback.symm
        _ = Matrix.toMatrix oneNonzero (EvenClifford.scale factor left) :=
          congrArg (Matrix.toMatrix oneNonzero) represents
        _ = Matrix2.scalarScale factor (Matrix.toMatrix oneNonzero left) := Matrix.toMatrix_scale _ _ _
        _ = Matrix2.scalarScale factor leftMatrix := congrArg (Matrix2.scalarScale factor) leftReadback)
  exact leftEqual.symm.trans ((congrArg (Matrix.fromMatrix oneNonzero) matricesEqual).trans rightEqual)

end Purelib.Geometry.Rotations.Ternary.Lorentz
