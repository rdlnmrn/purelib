module

public import Purelib.Data.Vector.Dependent
public import Purelib.Data.Fin.Product.Code

/-!
# Stored finite dependent matrices

One row-major dependent spine stores the original entry at every bounded
pair. Both indices and the complete entry type are preserved. Lookup never
reconstructs an entry or reruns its producer.
-/

public section

namespace Purelib.Data.Vector

open Purelib.Data.Fin.Product

universe u v

/-- A finite dependent matrix stored in one row-major spine at its original row and column types. -/
abbrev DependentMatrix {rows columns : Nat} (family : Fin rows → Fin columns → Type u) :=
  DependentVector (fun position : Fin (rows * columns) => family (Code.left position) (Code.right position))

namespace DependentMatrix

variable {rows columns : Nat} {family : Fin rows → Fin columns → Type u}

/-- Transport the whole original matrix entry along identities of its bounded row and column. -/
@[expose] def transportEntry {row nextRow : Fin rows} {column nextColumn : Fin columns}
    (value : family row column) (sameRow : row = nextRow) (sameColumn : column = nextColumn) :
    family nextRow nextColumn := sameRow ▸ sameColumn ▸ value

/-- Index transport preserves a complete entry supplied by the same original dependent producer. -/
theorem transportEntry_producer (producer : ∀ row column, family row column)
    {row nextRow : Fin rows} {column nextColumn : Fin columns}
    (sameRow : row = nextRow) (sameColumn : column = nextColumn) :
    transportEntry (producer row column) sameRow sameColumn = producer nextRow nextColumn := by
  cases sameRow
  cases sameColumn
  rfl

/-- A scalar reading of an entry is unchanged when its original matrix indices are identified. -/
theorem transportEntry_reading {K : Type v} (reading : ∀ row column, family row column → K)
    {row nextRow : Fin rows} {column nextColumn : Fin columns} (value : family row column)
    (sameRow : row = nextRow) (sameColumn : column = nextColumn) :
    reading nextRow nextColumn (transportEntry value sameRow sameColumn) = reading row column value := by
  cases sameRow
  cases sameColumn
  rfl

/-- Read the complete stored entry at its original bounded row and column. -/
@[expose] def get (matrix : DependentMatrix family) (row : Fin rows) (column : Fin columns) : family row column :=
  transportEntry (DependentVector.get matrix (Code.encode (row, column))) (Code.left_encode _) (Code.right_encode _)

/-- Materialize each original matrix entry once in increasing row-major order. -/
def ofFn (producer : ∀ row column, family row column) : DependentMatrix family :=
  DependentVector.ofFn (fun position => producer (Code.left position) (Code.right position))

/-- Materialize checked original matrix entries in their unchanged row-major order.

The continuation receives the actual stored spine and equality to the whole
original matrix. Each supplied entry is read once at its original bounded
row and column, with the reader's effects and failures preserved.
-/
def ofFnM {m : Type u → Type v} [Monad m] {α : Type u}
    (producer : ∀ row column, family row column)
    (load : ∀ row column, m {entry : family row column // entry = producer row column})
    (use : {matrix : DependentMatrix family // matrix = ofFn producer} → m α) : m α :=
  DependentVector.ofFnM (fun position => producer (Code.left position) (Code.right position))
    (fun position => load (Code.left position) (Code.right position)) use

/-- Reading a materialized matrix returns the complete original producer entry at the same bounded indices. -/
theorem ofFn_get (producer : ∀ row column, family row column) (row : Fin rows) (column : Fin columns) :
    get (ofFn producer) row column = producer row column := by
  unfold get ofFn
  rewrite [DependentVector.ofFn_get]
  exact transportEntry_producer producer (Code.left_encode _) (Code.right_encode _)

/-- A scalar matrix reading consumes the same original stored spine entry without rebuilding it. -/
theorem get_reading {K : Type v} (reading : ∀ row column, family row column → K)
    (matrix : DependentMatrix family) (row : Fin rows) (column : Fin columns) :
    reading row column (get matrix row column) =
      reading (Code.left (Code.encode (row, column))) (Code.right (Code.encode (row, column)))
        (DependentVector.get matrix (Code.encode (row, column))) :=
  transportEntry_reading reading _ _ _

/-- Fold the largest natural weight over the same stored matrix entries. -/
def maximum (matrix : DependentMatrix family) (weight : ∀ row column, family row column → Nat) : Nat :=
  DependentVector.maximum (fun position value => weight (Code.left position) (Code.right position) value) matrix

/-- Every original matrix entry's natural weight fits the maximum of the same retained entries. -/
theorem get_le_maximum (matrix : DependentMatrix family) (weight : ∀ row column, family row column → Nat)
    (row : Fin rows) (column : Fin columns) : weight row column (get matrix row column) ≤ maximum matrix weight :=
  (get_reading weight matrix row column).symm ▸
    (DependentVector.get_le_maximum
      (fun position value => weight (Code.left position) (Code.right position) value)
      matrix (Code.encode (row, column)))

/-- A ceiling for every original entry bounds the maximum of the same retained matrix. -/
theorem maximum_le (matrix : DependentMatrix family) (weight : ∀ row column, family row column → Nat)
    (ceiling : Nat) (bounded : ∀ row column, weight row column (get matrix row column) ≤ ceiling) :
    maximum matrix weight ≤ ceiling := by
  apply DependentVector.maximum_le
  intro position
  have same := (get_reading weight matrix (Code.left position) (Code.right position)).trans
    (congrArg (fun index => weight (Code.left index) (Code.right index) (DependentVector.get matrix index))
      (Code.encode_decode position))
  exact same ▸ bounded (Code.left position) (Code.right position)

end DependentMatrix

end Purelib.Data.Vector

end
