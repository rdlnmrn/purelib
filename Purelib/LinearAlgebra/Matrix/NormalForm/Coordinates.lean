module

public import Purelib.LinearAlgebra.Matrix.NormalForm.Basic
public import Purelib.Data.Vector.Split
import Purelib.LinearAlgebra.Matrix.Rectangular.Identity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Tactic.QuotientFreeOmega

/-!
# Coordinates of a retained rectangular normal form

The original inverse matrices construct kernel, image and complementary
vectors directly. Their coordinate readbacks and reconstruction laws retain
the original matrix and both original finite dimensions.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.NormalForm

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra.Matrix

variable {K : Type*} [CommRing K] {rows columns : Nat}
variable {matrix : Rectangular K rows columns} (normal : NormalForm matrix)

/-- Read a source vector in the retained reduced source coordinates. -/
@[expose] def sourceCoordinates (values : Vec K columns) : Vec K columns :=
  Rectangular.apply normal.sourceInverse.inverse values

/-- Read all target coordinates through the original retained target change. -/
@[expose] def targetCoordinates (values : Vec K rows) : Vec K rows :=
  Rectangular.apply normal.target values

/-- Read the free kernel coordinates of an original source vector. -/
@[expose] def kernelCoordinates (values : Vec K columns) : Vec K (columns - normal.rank) :=
  Split.drop normal.rank_le_columns (normal.sourceCoordinates values)

/-- Read the image coordinates of an original target vector. -/
@[expose] def imageCoordinates (values : Vec K rows) : Vec K normal.rank :=
  Split.take normal.rank_le_rows (normal.targetCoordinates values)

/-- Read the complementary target coordinates of an original target vector. -/
@[expose] def cokernelCoordinates (values : Vec K rows) : Vec K (rows - normal.rank) :=
  Split.drop normal.rank_le_rows (normal.targetCoordinates values)

/-- Construct the original kernel vector with the supplied free coordinates. -/
@[expose] def kernelVector (coordinates : Vec K (columns - normal.rank)) : Vec K columns :=
  Rectangular.apply normal.source
    (Split.join normal.rank_le_columns (vectorOfFn fun _ => 0) coordinates)

/-- Construct the original image vector with the supplied independent coordinates. -/
@[expose] def imageVector (coordinates : Vec K normal.rank) : Vec K rows :=
  Rectangular.apply normal.targetInverse.inverse
    (Split.join normal.rank_le_rows coordinates (vectorOfFn fun _ => 0))

/-- Construct the original complementary vector with the supplied coordinates. -/
@[expose] def complementVector (coordinates : Vec K (rows - normal.rank)) : Vec K rows :=
  Rectangular.apply normal.targetInverse.inverse
    (Split.join normal.rank_le_rows (vectorOfFn fun _ => 0) coordinates)

/-- Reconstruct an original target vector from both of its finite coordinate blocks. -/
@[expose] def reconstruct (image : Vec K normal.rank) (complement : Vec K (rows - normal.rank)) :
    Vec K rows :=
  Rectangular.apply normal.targetInverse.inverse (Split.join normal.rank_le_rows image complement)

/-- Applying the inverse source change recovers its original input coordinates. -/
theorem sourceCoordinates_source (values : Vec K columns) :
    normal.sourceCoordinates (Rectangular.apply normal.source values) = values := by
  unfold sourceCoordinates
  rw [← Rectangular.apply_mul]
  change Rectangular.apply (Multiplication.mul normal.sourceInverse.inverse normal.source) values = values
  rw [normal.sourceInverse.left_identity, normal.source_scalar]
  exact Rectangular.apply_unit values

/-- Applying the source change recovers the original source vector. -/
theorem source_sourceCoordinates (values : Vec K columns) :
    Rectangular.apply normal.source (normal.sourceCoordinates values) = values := by
  unfold sourceCoordinates
  rw [← Rectangular.apply_mul]
  change Rectangular.apply (Multiplication.mul normal.source normal.sourceInverse.inverse) values = values
  rw [normal.sourceInverse.right_identity, normal.source_scalar]
  exact Rectangular.apply_unit values

/-- The target change recovers coordinates passed through its retained inverse. -/
theorem targetCoordinates_inverse (values : Vec K rows) :
    normal.targetCoordinates (Rectangular.apply normal.targetInverse.inverse values) = values := by
  unfold targetCoordinates
  rw [← Rectangular.apply_mul]
  change Rectangular.apply (Multiplication.mul normal.target normal.targetInverse.inverse) values = values
  rw [normal.targetInverse.right_identity, normal.target_scalar]
  exact Rectangular.apply_unit values

/-- The retained inverse target change recovers the original target vector. -/
theorem inverse_targetCoordinates (values : Vec K rows) :
    Rectangular.apply normal.targetInverse.inverse (normal.targetCoordinates values) = values := by
  unfold targetCoordinates
  rw [← Rectangular.apply_mul]
  change Rectangular.apply (Multiplication.mul normal.targetInverse.inverse normal.target) values = values
  rw [normal.targetInverse.left_identity, normal.target_scalar]
  exact Rectangular.apply_unit values

/-- The reduced action selects exactly the initial identity coordinates. -/
theorem reduced_action (values : Vec K columns) (row : Fin rows) :
    Rectangular.apply normal.reduced values row =
      if inside : row.val < normal.rank then
        values ⟨row.val, Nat.lt_of_lt_of_le inside normal.rank_le_columns⟩ else 0 := by
  rw [Rectangular.apply_at]
  by_cases inside : row.val < normal.rank
  · rw [dif_pos inside]
    let selected : Fin columns := ⟨row.val, Nat.lt_of_lt_of_le inside normal.rank_le_columns⟩
    calc
      _ = sumFin (fun column => if column = selected then values column else 0) := by
        apply sumFin_congr
        intro column
        rw [normal.reduced_apply]
        by_cases equal : column = selected
        · cases equal
          rw [if_pos ⟨rfl, inside⟩, if_pos rfl, one_mul]
        · have different : ¬(row.val = column.val ∧ row.val < normal.rank) := by
            intro both
            exact equal (Fin.ext both.1.symm)
          rw [if_neg different, if_neg equal, zero_mul]
      _ = values selected := sumFin_ite_eq selected _
  · rw [dif_neg inside]
    calc
      _ = sumFin (fun _ : Fin columns => (0 : K)) := by
        apply sumFin_congr
        intro column
        rw [normal.reduced_apply, if_neg (fun both => inside both.2), zero_mul]
      _ = 0 := sumFin_zero

/-- Acting on reduced source coordinates uses the actual retained original matrix. -/
theorem matrix_source (values : Vec K columns) :
    Rectangular.apply matrix (Rectangular.apply normal.source values) =
      Rectangular.apply normal.targetInverse.inverse (Rectangular.apply normal.reduced values) := by
  have transformed : normal.targetCoordinates
      (Rectangular.apply matrix (Rectangular.apply normal.source values)) =
      Rectangular.apply normal.reduced values := by
    unfold targetCoordinates
    rw [normal.reduced_eq, Rectangular.apply_mul, Rectangular.apply_mul]
  exact (normal.inverse_targetCoordinates _).symm.trans
    (congrArg (Rectangular.apply normal.targetInverse.inverse) transformed)

/-- Original matrix action becomes the cached reduction in the retained coordinates. -/
theorem targetCoordinates_matrix (values : Vec K columns) :
    normal.targetCoordinates (Rectangular.apply matrix values) =
      Rectangular.apply normal.reduced (normal.sourceCoordinates values) := by
  rw [normal.reduced_eq, Rectangular.apply_mul, Rectangular.apply_mul,
    normal.source_sourceCoordinates]
  rfl

/-- Every constructed free-coordinate vector belongs to the original matrix kernel. -/
theorem matrix_kernelVector (coordinates : Vec K (columns - normal.rank)) :
    Rectangular.apply matrix (normal.kernelVector coordinates) = vectorOfFn (fun _ => 0) := by
  unfold kernelVector
  rw [normal.matrix_source]
  have reducedZero : Rectangular.apply normal.reduced
      (Split.join normal.rank_le_columns (vectorOfFn fun _ => 0) coordinates) =
      vectorOfFn (fun _ => 0) := by
    apply vector_ext
    intro row
    rw [normal.reduced_action, vectorOfFn_apply]
    split
    · rename_i inside
      exact (Split.join_apply_take normal.rank_le_columns _ _
        ⟨row.val, inside⟩).trans (vectorOfFn_apply _ _)
    · rfl
  rw [reducedZero, Rectangular.apply_zero]

/-- An original kernel vector has zero initial reduced source coordinates. -/
theorem source_prefix_zero (values : Vec K columns)
    (vanishes : Rectangular.apply matrix values = vectorOfFn (fun _ => 0)) :
    Split.take normal.rank_le_columns (normal.sourceCoordinates values) =
      vectorOfFn (fun _ => 0) := by
  have reducedZero : Rectangular.apply normal.reduced (normal.sourceCoordinates values) =
      vectorOfFn (fun _ => 0) := by
    rw [← normal.targetCoordinates_matrix, vanishes]
    exact Rectangular.apply_zero _
  apply vector_ext
  intro index
  have scalar := vector_eq_at reducedZero
    (⟨index.val, Nat.lt_of_lt_of_le index.isLt normal.rank_le_rows⟩ : Fin rows)
  rw [normal.reduced_action, dif_pos index.isLt, vectorOfFn_apply] at scalar
  rw [Split.take_apply, vectorOfFn_apply]
  exact scalar

/-- Every original kernel vector is reconstructed from its computed free coordinates. -/
theorem kernelVector_coordinates (values : Vec K columns)
    (vanishes : Rectangular.apply matrix values = vectorOfFn (fun _ => 0)) :
    normal.kernelVector (normal.kernelCoordinates values) = values := by
  unfold kernelVector kernelCoordinates
  rw [← normal.source_prefix_zero values vanishes, Split.join_split]
  exact normal.source_sourceCoordinates values

/-- Original kernel membership is exactly reconstruction from the free coordinates. -/
theorem kernel_iff (values : Vec K columns) :
    Rectangular.apply matrix values = vectorOfFn (fun _ => 0) ↔
      normal.kernelVector (normal.kernelCoordinates values) = values := by
  constructor
  · exact normal.kernelVector_coordinates values
  · intro reconstructed
    exact (congrArg (Rectangular.apply matrix) reconstructed).symm.trans
      (normal.matrix_kernelVector _)

/-- Reading back a constructed kernel vector returns its exact supplied coordinates. -/
theorem kernelCoordinates_kernelVector (coordinates : Vec K (columns - normal.rank)) :
    normal.kernelCoordinates (normal.kernelVector coordinates) = coordinates := by
  unfold kernelCoordinates kernelVector
  rw [normal.sourceCoordinates_source, Split.drop_join]

/-- Different free coordinate vectors give different original kernel vectors. -/
theorem kernelVector_injective (first second : Vec K (columns - normal.rank))
    (equal : normal.kernelVector first = normal.kernelVector second) : first = second := by
  have readback := congrArg normal.kernelCoordinates equal
  rw [normal.kernelCoordinates_kernelVector, normal.kernelCoordinates_kernelVector] at readback
  exact readback

/-- Reading back a reconstructed target vector returns its exact image coordinates. -/
theorem imageCoordinates_reconstruct (image : Vec K normal.rank) (complement : Vec K (rows - normal.rank)) :
    normal.imageCoordinates (normal.reconstruct image complement) = image := by
  unfold imageCoordinates reconstruct
  rw [normal.targetCoordinates_inverse, Split.take_join]

/-- Reading back a reconstructed target vector returns its exact complementary coordinates. -/
theorem cokernelCoordinates_reconstruct (image : Vec K normal.rank) (complement : Vec K (rows - normal.rank)) :
    normal.cokernelCoordinates (normal.reconstruct image complement) = complement := by
  unfold cokernelCoordinates reconstruct
  rw [normal.targetCoordinates_inverse, Split.drop_join]

/-- Both computed target coordinate blocks reconstruct the complete original vector. -/
theorem reconstruct_coordinates (values : Vec K rows) :
    normal.reconstruct (normal.imageCoordinates values) (normal.cokernelCoordinates values) = values := by
  unfold reconstruct imageCoordinates cokernelCoordinates
  rw [Split.join_split]
  exact normal.inverse_targetCoordinates values

/-- An original image vector has zero complementary target coordinates. -/
theorem cokernelCoordinates_matrix (values : Vec K columns) :
    normal.cokernelCoordinates (Rectangular.apply matrix values) = vectorOfFn (fun _ => 0) := by
  unfold cokernelCoordinates
  rw [normal.targetCoordinates_matrix]
  apply vector_ext
  intro index
  rw [Split.drop_apply, normal.reduced_action, dif_neg (by change ¬normal.rank + index.val < normal.rank; omega0),
    vectorOfFn_apply]

/-- The retained inverse target coordinates construct an explicit original source preimage. -/
@[expose] def imagePreimage (coordinates : Vec K normal.rank) : Vec K columns :=
  Rectangular.apply normal.source
    (Split.join normal.rank_le_columns coordinates (vectorOfFn fun _ => 0))

/-- The constructed image vector is the image of its explicit original source preimage. -/
theorem matrix_imagePreimage (coordinates : Vec K normal.rank) :
    Rectangular.apply matrix (normal.imagePreimage coordinates) = normal.imageVector coordinates := by
  unfold imagePreimage imageVector
  rw [normal.matrix_source]
  apply congrArg (Rectangular.apply normal.targetInverse.inverse)
  apply vector_ext
  intro row
  rw [normal.reduced_action]
  by_cases inside : row.val < normal.rank
  · rw [dif_pos inside]
    exact (Split.join_apply_take normal.rank_le_columns _ _ ⟨row.val, inside⟩).trans
      (Split.join_apply_take normal.rank_le_rows _ _ ⟨row.val, inside⟩).symm
  · rw [dif_neg inside]
    have after : normal.rank ≤ row.val := Nat.le_of_not_lt inside
    let index : Fin (rows - normal.rank) := ⟨row.val - normal.rank, by have := row.isLt; omega0⟩
    have position : (⟨normal.rank + index.val, by have := index.isLt; omega0⟩ : Fin rows) = row := by
      apply Fin.ext
      change normal.rank + (row.val - normal.rank) = row.val
      omega0
    rw [← position, Split.join_apply_drop, vectorOfFn_apply]

/-- Image coordinates of a constructed image vector recover the exact input block. -/
theorem imageCoordinates_imageVector (coordinates : Vec K normal.rank) :
    normal.imageCoordinates (normal.imageVector coordinates) = coordinates :=
  normal.imageCoordinates_reconstruct coordinates _

/-- Complement coordinates of a constructed complementary vector recover the exact input block. -/
theorem cokernelCoordinates_complementVector (coordinates : Vec K (rows - normal.rank)) :
    normal.cokernelCoordinates (normal.complementVector coordinates) = coordinates :=
  normal.cokernelCoordinates_reconstruct _ coordinates

/-- Different image coordinate blocks give different original image vectors. -/
theorem imageVector_injective (first second : Vec K normal.rank)
    (equal : normal.imageVector first = normal.imageVector second) : first = second := by
  have readback := congrArg normal.imageCoordinates equal
  rw [normal.imageCoordinates_imageVector, normal.imageCoordinates_imageVector] at readback
  exact readback

/-- Different complementary coordinate blocks give different original complementary vectors. -/
theorem complementVector_injective (first second : Vec K (rows - normal.rank))
    (equal : normal.complementVector first = normal.complementVector second) : first = second := by
  have readback := congrArg normal.cokernelCoordinates equal
  rw [normal.cokernelCoordinates_complementVector, normal.cokernelCoordinates_complementVector] at readback
  exact readback

/-- A target vector with zero complementary coordinates has its computed image reconstruction. -/
theorem imageVector_coordinates (values : Vec K rows)
    (vanishes : normal.cokernelCoordinates values = vectorOfFn (fun _ => 0)) :
    normal.imageVector (normal.imageCoordinates values) = values := by
  change normal.reconstruct (normal.imageCoordinates values) (vectorOfFn fun _ => 0) = values
  rw [← vanishes]
  exact normal.reconstruct_coordinates values

/-- Actual image membership is exactly vanishing of the computed complementary coordinates. -/
theorem image_iff (values : Vec K rows) :
    (∃ source : Vec K columns, Rectangular.apply matrix source = values) ↔
      normal.cokernelCoordinates values = vectorOfFn (fun _ => 0) := by
  constructor
  · rintro ⟨source, equal⟩
    rw [← equal]
    exact normal.cokernelCoordinates_matrix source
  · intro vanishes
    exact ⟨normal.imagePreimage (normal.imageCoordinates values),
      (normal.matrix_imagePreimage _).trans (normal.imageVector_coordinates values vanishes)⟩

/-- The actual kernel generators are the final columns of the retained source change. -/
@[expose] def kernelBasis : Rectangular K columns (columns - normal.rank) :=
  Rectangular.dropColumns normal.rank_le_columns normal.source

/-- The actual image generators are the initial columns of the retained inverse target change. -/
@[expose] def imageBasis : Rectangular K rows normal.rank :=
  Rectangular.takeColumns normal.rank_le_rows normal.targetInverse.inverse

/-- The actual complementary generators are the final columns of the inverse target change. -/
@[expose] def complementBasis : Rectangular K rows (rows - normal.rank) :=
  Rectangular.dropColumns normal.rank_le_rows normal.targetInverse.inverse

/-- Constructing a kernel vector is the literal finite combination of its retained kernel columns. -/
theorem kernelVector_eq_basis (coordinates : Vec K (columns - normal.rank)) :
    normal.kernelVector coordinates = Rectangular.apply normal.kernelBasis coordinates := by
  unfold kernelVector kernelBasis
  rw [Rectangular.apply_join, Rectangular.apply_zero]
  apply vector_ext
  intro row
  rw [vectorOfFn_apply, vectorOfFn_apply, zero_add]

/-- Constructing an image vector is the literal finite combination of its retained image columns. -/
theorem imageVector_eq_basis (coordinates : Vec K normal.rank) :
    normal.imageVector coordinates = Rectangular.apply normal.imageBasis coordinates := by
  unfold imageVector imageBasis
  rw [Rectangular.apply_join, Rectangular.apply_zero]
  apply vector_ext
  intro row
  rw [vectorOfFn_apply, vectorOfFn_apply, add_zero]

/-- Constructing a complementary vector is the finite combination of its retained complementary columns. -/
theorem complementVector_eq_basis (coordinates : Vec K (rows - normal.rank)) :
    normal.complementVector coordinates = Rectangular.apply normal.complementBasis coordinates := by
  unfold complementVector complementBasis
  rw [Rectangular.apply_join, Rectangular.apply_zero]
  apply vector_ext
  intro row
  rw [vectorOfFn_apply, vectorOfFn_apply, zero_add]

/-- Kernel columns admit unique complete coefficient vectors over the original coefficient ring. -/
theorem kernelBasis_independent (first second : Vec K (columns - normal.rank))
    (equal : Rectangular.apply normal.kernelBasis first = Rectangular.apply normal.kernelBasis second) :
    first = second := by
  rw [← normal.kernelVector_eq_basis, ← normal.kernelVector_eq_basis] at equal
  exact normal.kernelVector_injective first second equal

/-- Image columns admit unique complete coefficient vectors over the original coefficient ring. -/
theorem imageBasis_independent (first second : Vec K normal.rank)
    (equal : Rectangular.apply normal.imageBasis first = Rectangular.apply normal.imageBasis second) :
    first = second := by
  rw [← normal.imageVector_eq_basis, ← normal.imageVector_eq_basis] at equal
  exact normal.imageVector_injective first second equal

/-- Complementary columns admit unique complete coefficient vectors over the original coefficient ring. -/
theorem complementBasis_independent (first second : Vec K (rows - normal.rank))
    (equal : Rectangular.apply normal.complementBasis first = Rectangular.apply normal.complementBasis second) :
    first = second := by
  rw [← normal.complementVector_eq_basis, ← normal.complementVector_eq_basis] at equal
  exact normal.complementVector_injective first second equal

/-- Every finite combination of the actual kernel columns lies in the original matrix kernel. -/
theorem kernelBasis_kernel (coordinates : Vec K (columns - normal.rank)) :
    Rectangular.apply matrix (Rectangular.apply normal.kernelBasis coordinates) =
      vectorOfFn (fun _ => 0) := by
  rw [← normal.kernelVector_eq_basis]
  exact normal.matrix_kernelVector coordinates

/-- The actual kernel columns reconstruct every original kernel vector with computed coefficients. -/
theorem kernelBasis_complete (values : Vec K columns)
    (vanishes : Rectangular.apply matrix values = vectorOfFn (fun _ => 0)) :
    Rectangular.apply normal.kernelBasis (normal.kernelCoordinates values) = values := by
  rw [← normal.kernelVector_eq_basis]
  exact normal.kernelVector_coordinates values vanishes

/-- Every finite combination of the actual image columns has its retained explicit source preimage. -/
theorem imageBasis_image (coordinates : Vec K normal.rank) :
    Rectangular.apply matrix (normal.imagePreimage coordinates) =
      Rectangular.apply normal.imageBasis coordinates := by
  rw [← normal.imageVector_eq_basis]
  exact normal.matrix_imagePreimage coordinates

/-- The actual image columns reconstruct each original image vector with its computed coefficients. -/
theorem imageBasis_complete (values : Vec K rows)
    (belongs : ∃ source : Vec K columns, Rectangular.apply matrix source = values) :
    Rectangular.apply normal.imageBasis (normal.imageCoordinates values) = values := by
  rw [← normal.imageVector_eq_basis]
  exact normal.imageVector_coordinates values ((normal.image_iff values).mp belongs)

/-- The target reconstruction is the sum of its actual image and complementary vectors. -/
theorem reconstruct_eq_add (image : Vec K normal.rank) (complement : Vec K (rows - normal.rank)) :
    normal.reconstruct image complement = vectorOfFn (fun row =>
      normal.imageVector image row + normal.complementVector complement row) := by
  unfold reconstruct
  rw [Rectangular.apply_join]
  rw [normal.imageVector_eq_basis, normal.complementVector_eq_basis]
  rfl

/-- Both finite column families reconstruct every original target vector additively. -/
theorem target_basis_reconstruction (values : Vec K rows) :
    vectorOfFn (fun row =>
      Rectangular.apply normal.imageBasis (normal.imageCoordinates values) row +
      Rectangular.apply normal.complementBasis (normal.cokernelCoordinates values) row) = values := by
  rw [← normal.imageVector_eq_basis, ← normal.complementVector_eq_basis,
    ← normal.reconstruct_eq_add]
  exact normal.reconstruct_coordinates values

/-- The two target coefficient blocks are unique in their actual additive column reconstruction. -/
theorem target_basis_unique (firstImage secondImage : Vec K normal.rank)
    (firstComplement secondComplement : Vec K (rows - normal.rank))
    (equal : vectorOfFn (fun row => Rectangular.apply normal.imageBasis firstImage row +
        Rectangular.apply normal.complementBasis firstComplement row) =
      vectorOfFn (fun row => Rectangular.apply normal.imageBasis secondImage row +
        Rectangular.apply normal.complementBasis secondComplement row)) :
    firstImage = secondImage ∧ firstComplement = secondComplement := by
  rw [← normal.imageVector_eq_basis, ← normal.imageVector_eq_basis,
    ← normal.complementVector_eq_basis, ← normal.complementVector_eq_basis,
    ← normal.reconstruct_eq_add, ← normal.reconstruct_eq_add] at equal
  constructor
  · have readback := congrArg normal.imageCoordinates equal
    rw [normal.imageCoordinates_reconstruct, normal.imageCoordinates_reconstruct] at readback
    exact readback
  · have readback := congrArg normal.cokernelCoordinates equal
    rw [normal.cokernelCoordinates_reconstruct, normal.cokernelCoordinates_reconstruct] at readback
    exact readback

/-- The number of actual kernel columns in this retained reduction. -/
@[expose] def kernelDimension : Nat := columns - normal.rank

/-- The number of independent actual image columns in this retained reduction. -/
@[expose] def imageDimension : Nat := normal.rank

/-- The number of complementary actual target columns in this retained reduction. -/
@[expose] def cokernelDimension : Nat := rows - normal.rank

/-- The signed complementary-target minus kernel dimension of this reduction. -/
@[expose] def defect : Int := (normal.cokernelDimension : Int) - (normal.kernelDimension : Int)

/-- Kernel and image coordinate counts recover the complete original source dimension. -/
theorem source_dimension : normal.kernelDimension + normal.imageDimension = columns :=
  Nat.sub_add_cancel normal.rank_le_columns

/-- Image and complementary coordinate counts recover the complete original target dimension. -/
theorem target_dimension : normal.cokernelDimension + normal.imageDimension = rows :=
  Nat.sub_add_cancel normal.rank_le_rows

/-- The defect is the original rectangular target dimension minus its source dimension. -/
theorem defect_eq : normal.defect = (rows : Int) - (columns : Int) := by
  have sourceBound := normal.rank_le_columns
  have targetBound := normal.rank_le_rows
  unfold defect cokernelDimension kernelDimension
  omega0

end Purelib.LinearAlgebra.Matrix.NormalForm
