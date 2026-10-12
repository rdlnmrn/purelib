module

public import Purelib.Algebra.Quaternion.SplitMatrix
public import Purelib.Geometry.Projective.Quaternion.Finite.Enumeration
public import Purelib.Geometry.Projective.Line.Finite
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
public import Purelib.Data.List.Flatten
import Purelib.LinearAlgebra.Coordinates2.RankOne
import Purelib.Geometry.Rotations.FiniteField.Classification
import Purelib.LinearAlgebra.Coordinates2.Invertible

/-!
# Finite projective matrix representatives

The original odd-field quaternion charts are transported through a retained
splitting certificate. Normalization preserves the exact input matrix class,
and the resulting list contains precisely one representative of each class.
Nonzero singular classes are the outer products of two canonical projective
line pairs, with an executable normalization from their original factors.
-/

public section

namespace Purelib.Geometry.Projective.Matrix.Finite

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Finite.Odd.Presentation (FiniteOddFieldPresentation TwoSquareRepresentation)
open Purelib.Algebra.Quaternion
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.Data.List
open Purelib.Geometry.Projective.Line (Proj)
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

variable {K : Type*} [ExplicitField K] (presentation : FiniteOddFieldPresentation K)
    (split : TwoSquareRepresentation (-1 : K))

/-- Transport the original canonical non-null quaternion list to invertible matrices.

Every entry uses the same retained splitting certificate. The original
list order and original non-null proportions determine these representatives;
no matrix equality scan or quotient enumeration is performed.
-/
@[expose] def representatives : List (Matrix2.Invertible K) :=
  presentation.nonNullProjectiveRepresentatives.map (SplitMatrix.toInvertible split)

/-- Normalize an original invertible matrix using the retained quaternion charts.

The input is decoded once and its original canonicalization is retained
before matrix readback. Its explicit scale certificate identifies the
same original projective matrix class.
-/
@[expose] def normalize (value : Matrix2.Invertible K) : Matrix2.Invertible K :=
  let decoded := SplitMatrix.fromInvertible split presentation.twoNonzero value
  let normalized := presentation.canonicalize decoded
  SplitMatrix.toInvertible split normalized.representative

/-- The transported finite matrix list has no repeated matrix records. -/
theorem representatives_nodup : (representatives presentation split).Nodup :=
  Nodup.nodup_map_of_injective (fun _ _ equal =>
    SplitMatrix.toInvertible_injective split presentation.twoNonzero equal)
      presentation.nonNullProjectiveRepresentatives_nodup

/-- The computed matrix normalization belongs to the transported finite list. -/
theorem normalize_mem (value : Matrix2.Invertible K) :
    normalize presentation split value ∈ representatives presentation split :=
  Map.mem_map.mpr ⟨_, presentation.canonicalize_mem _, rfl⟩

/-- The normalized matrix retains an explicit nonzero scale from the original input matrix. -/
theorem equivalent_normalize (value : Matrix2.Invertible K) :
    value.Equivalent (normalize presentation split value) := by
  let decoded := SplitMatrix.fromInvertible split presentation.twoNonzero value
  have equivalent := (SplitMatrix.toInvertible_equivalent_iff split presentation.twoNonzero
    decoded (presentation.canonicalize decoded).representative).mpr
      (presentation.canonicalize decoded).equivalent
  rw [SplitMatrix.toInvertible_fromInvertible] at equivalent
  exact equivalent

/-- Two listed matrix representatives in the same projective class are equal.

The exact supplied scale is reflected to the original canonical quaternion
parents. Their first nonzero coordinate proves equality, and matrix readback
retains that same equality without a new normalization.
-/
theorem eq_of_equivalent {left right : Matrix2.Invertible K}
    (leftMember : left ∈ representatives presentation split)
    (rightMember : right ∈ representatives presentation split)
    (equivalent : left.Equivalent right) : left = right := by
  rcases Map.mem_map.mp leftMember with ⟨leftSource, leftSourceMember, leftEqual⟩
  rcases Map.mem_map.mp rightMember with ⟨rightSource, rightSourceMember, rightEqual⟩
  have sourceEquivalent := (SplitMatrix.toInvertible_equivalent_iff split presentation.twoNonzero
    leftSource rightSource).mp (by rw [leftEqual, rightEqual]; exact equivalent)
  have rawEqual := presentation.projective_eq_of_equivalent
    (presentation.raw_mem_of_nonNull_mem leftSourceMember)
    (presentation.raw_mem_of_nonNull_mem rightSourceMember) sourceEquivalent
  have sourceEqual : leftSource = rightSource := NonNullProportion.ext
    (congrArg Proportion.scalar rawEqual) (congrArg Proportion.vector rawEqual)
  exact leftEqual.symm.trans ((congrArg (SplitMatrix.toInvertible split) sourceEqual).trans rightEqual)

/-- The complete projective matrix representative list has order `q(q²-1)`.

The retained coordinate bijection transports the original canonical
quaternion enumeration. Its certified Euclidean rotation count supplies
the same length formula for these actual matrix representatives.
-/
theorem representatives_length :
    (representatives presentation split).length = presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1) := by
  calc
    _ = presentation.nonNullProjectiveRepresentatives.length := Map.length_map _ _
    _ = presentation.rotations.length := (Map.length_map _ _).symm
    _ = _ := presentation.rotationCarrierCount_formula_via_projectiveBijection

/-- Enumerate nonzero singular matrix classes by their two original projective-line factors.

The projective-line list is retained outside the entry-producing functions.
Each original column and row pair contributes its exact outer matrix, in
the rectangular order of the same two cached lists.
-/
@[expose] def singularRepresentatives : List (Matrix2 K) :=
  let points := Proj.finiteRepresentatives presentation
  points.flatMap fun column => points.map (Matrix2.outer column)

/-- The singular matrix representative list has exactly `(q+1)²` entries. -/
theorem singularRepresentatives_length :
    (singularRepresentatives presentation).length =
      (presentation.carrier.length + 1) * (presentation.carrier.length + 1) := by
  unfold singularRepresentatives
  rw [Flatten.flatMap_map_length, Proj.finiteRepresentatives_length]

/-- Every listed singular matrix retains a nonzero entry and determinant zero. -/
theorem singularRepresentatives_nonzero_singular {matrix : Matrix2 K}
    (member : matrix ∈ singularRepresentatives presentation) : matrix.IsNonzero ∧ matrix.determinant = 0 := by
  rcases Flatten.mem_flatMap.mp member with ⟨column, columnMember, rowMember⟩
  rcases Map.mem_map.mp rowMember with ⟨row, rowMember, equal⟩
  have columnNonzero := Proj.finiteRepresentatives_nonzero presentation columnMember
  have rowNonzero := Proj.finiteRepresentatives_nonzero presentation rowMember
  exact ⟨(congrArg Matrix2.IsNonzero equal).mp (Matrix2.outer_nonzero columnNonzero rowNonzero),
    (congrArg Matrix2.determinant equal).symm.trans (Matrix2.determinant_outer column row)⟩

/-- Canonical projective factors are determined by the nonzero scalar class of their original outer matrix. -/
private theorem canonical_factors_eq_of_scale {leftColumn leftRow rightColumn rightRow : Proj K}
    (leftColumnMember : leftColumn ∈ Proj.finiteRepresentatives presentation)
    (leftRowMember : leftRow ∈ Proj.finiteRepresentatives presentation)
    (rightColumnMember : rightColumn ∈ Proj.finiteRepresentatives presentation)
    (rightRowMember : rightRow ∈ Proj.finiteRepresentatives presentation)
    (factor : K) (nonzero : factor ≠ 0)
    (represents : Matrix2.outer rightColumn rightRow = Matrix2.scalarScale factor (Matrix2.outer leftColumn leftRow)) :
    leftColumn = rightColumn ∧ leftRow = rightRow := by
  have leftColumnNonzero := Proj.finiteRepresentatives_nonzero presentation leftColumnMember
  have leftRowNonzero := Proj.finiteRepresentatives_nonzero presentation leftRowMember
  have equal : Matrix2.outer (leftColumn.scale factor) leftRow = Matrix2.outer rightColumn rightRow :=
    (Matrix2.outer_scale_column leftColumn leftRow factor).trans represents.symm
  have columns := (Proj.equivalent_scale_left_iff leftColumn rightColumn factor nonzero).mp
    (Matrix2.outer_equal_columns leftRowNonzero equal)
  have rows := Matrix2.outer_equal_rows (Proj.scale_nonzero nonzero leftColumnNonzero) equal
  exact ⟨Proj.finiteRepresentatives_eq_of_equivalent presentation leftColumnMember rightColumnMember columns,
    Proj.finiteRepresentatives_eq_of_equivalent presentation leftRowMember rightRowMember rows⟩

/-- Listed singular matrices in the same nonzero scalar class are equal.

The original row and column factors determine their two projective labels.
Their canonical projective-line coordinates therefore agree, which recovers
the same retained outer matrix.
-/
theorem singularRepresentatives_eq_of_scale {left right : Matrix2 K}
    (leftMember : left ∈ singularRepresentatives presentation)
    (rightMember : right ∈ singularRepresentatives presentation) (factor : K) (nonzero : factor ≠ 0)
    (represents : right = Matrix2.scalarScale factor left) : left = right := by
  rcases Flatten.mem_flatMap.mp leftMember with ⟨leftColumn, leftColumnMember, leftRowMember⟩
  rcases Map.mem_map.mp leftRowMember with ⟨leftRow, leftRowMember, leftEqual⟩
  rcases Flatten.mem_flatMap.mp rightMember with ⟨rightColumn, rightColumnMember, rightRowMember⟩
  rcases Map.mem_map.mp rightRowMember with ⟨rightRow, rightRowMember, rightEqual⟩
  have factors := canonical_factors_eq_of_scale presentation leftColumnMember leftRowMember rightColumnMember
    rightRowMember factor nonzero (by rw [leftEqual, rightEqual]; exact represents)
  exact leftEqual.symm.trans ((congrArg (fun column => Matrix2.outer column leftRow) factors.1).trans
    ((congrArg (Matrix2.outer rightColumn) factors.2).trans rightEqual))

/-- The rectangular singular representative list has no duplicate matrices. -/
theorem singularRepresentatives_nodup : (singularRepresentatives presentation).Nodup := by
  let points := Proj.finiteRepresentatives presentation
  have rectangle : ∀ columns : List (Proj K), (∀ column ∈ columns, column ∈ points) → columns.Nodup →
      (columns.flatMap fun column => points.map (Matrix2.outer column)).Nodup := by
    intro columns
    induction columns with
    | nil => intro _ _; exact List.Pairwise.nil
    | cons head tail inductionHypothesis =>
        intro included nodup
        have headMember := included head List.mem_cons_self
        have headNonzero := Proj.finiteRepresentatives_nonzero presentation headMember
        apply Nodup.nodup_append
        · exact Nodup.nodup_map_of_injective (fun _ _ equal => Matrix2.outer_row_injective headNonzero equal)
            (Proj.finiteRepresentatives_nodup presentation)
        · exact inductionHypothesis (fun column member => included column (List.mem_cons_of_mem head member))
            (List.pairwise_cons.mp nodup).2
        · intro left leftMember right rightMember equal
          rcases Map.mem_map.mp leftMember with ⟨leftRow, leftRowMember, leftEqual⟩
          rcases Flatten.mem_flatMap.mp rightMember with ⟨rightColumn, rightColumnMember, rightRowMember⟩
          rcases Map.mem_map.mp rightRowMember with ⟨rightRow, rightRowMember, rightEqual⟩
          have columns := (canonical_factors_eq_of_scale presentation headMember leftRowMember
            (included rightColumn (List.mem_cons_of_mem head rightColumnMember)) rightRowMember
            1 presentation.one_ne_zero (by
              rw [leftEqual, rightEqual, Matrix2.scalarScale_one]
              exact equal.symm)).1
          exact (List.pairwise_cons.mp nodup).1 rightColumn rightColumnMember columns
  exact rectangle points (fun _ member => member) (Proj.finiteRepresentatives_nodup presentation)

/-- Compute the listed scalar class of an original nonzero singular matrix.

The original rank-one factorization is cached first. Each of its two
nonzero factors is normalized once, and the product of their retained
scales relates the listed outer matrix to the exact original input.
-/
@[expose] def singularNormalize (matrix : Matrix2 K) (nonzero : matrix.IsNonzero)
    (singular : matrix.determinant = 0) :
    Σ' factor : K, Σ' representative : Matrix2 K, factor ≠ 0 ∧
      representative ∈ singularRepresentatives presentation ∧ representative = Matrix2.scalarScale factor matrix := by
  letI : DecidableEq K := presentation.eqDecidable
  let factorization := Matrix2.rankOneFactorization matrix presentation.one_ne_zero nonzero singular
  let column := Proj.finiteNormalize presentation factorization.column factorization.columnNonzero
  let row := Proj.finiteNormalize presentation factorization.row factorization.rowNonzero
  refine ⟨column.1 * row.1, Matrix2.outer column.2.1 row.2.1,
    ExplicitField.mul_ne_zero column.2.2.1 row.2.2.1, ?_, ?_⟩
  · exact Flatten.mem_flatMap.mpr ⟨column.2.1, column.2.2.2.1,
      Map.mem_map.mpr ⟨row.2.1, row.2.2.2.1, rfl⟩⟩
  · calc
      Matrix2.outer column.2.1 row.2.1 = Matrix2.outer (factorization.column.scale column.1) row.2.1 :=
        congrArg (fun point => Matrix2.outer point row.2.1) column.2.2.2.2
      _ = Matrix2.outer (factorization.column.scale column.1) (factorization.row.scale row.1) :=
        congrArg (Matrix2.outer (factorization.column.scale column.1)) row.2.2.2.2
      _ = Matrix2.scalarScale (column.1 * row.1) (Matrix2.outer factorization.column factorization.row) :=
        Matrix2.outer_scale_both factorization.column factorization.row column.1 row.1
      _ = Matrix2.scalarScale (column.1 * row.1) matrix :=
        congrArg (Matrix2.scalarScale (column.1 * row.1)) factorization.reconstruction

end Purelib.Geometry.Projective.Matrix.Finite
