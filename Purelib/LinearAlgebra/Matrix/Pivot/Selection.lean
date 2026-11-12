module

public import Purelib.LinearAlgebra.Matrix.Pivot
public import Purelib.LinearAlgebra.Matrix.Permutation
public import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.Data.Fin.Permutation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained original pivot selections

The original nonzero-entry owner retains both original coordinates. Its
selection materializes the corresponding row and column transpositions once,
so inverse testing and Schur reduction consume the same cached rectangle.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Pivot

variable {K : Type*} [CommRing K] {rows columns : Nat}

set_option genInjectivity false in
/-- A selected original pivot retains its nonzero-entry parent and actual pivoted rectangle. -/
structure Selection (matrix : Rectangular K (rows + 1) (columns + 1)) where
  /-- The original bounded nonzero-entry owner. -/
  entry : Entry (fun row column => matrix row column)
  /-- The rectangle obtained by the two actual retained transpositions. -/
  pivoted : Rectangular K (rows + 1) (columns + 1)
  /-- The cached rectangle is the original table with precisely these transpositions. -/
  pivoted_eq : pivoted = Permutation.pivotMatrix matrix entry.row entry.column

constructive_injectivity Selection

namespace Selection

/-- Materialize the two original pivot transpositions once and retain their entry owner. -/
@[expose] def build (matrix : Rectangular K (rows + 1) (columns + 1))
    (entry : Entry (fun row column => matrix row column)) : Selection matrix where
  entry := entry
  pivoted := Permutation.pivotMatrix matrix entry.row entry.column
  pivoted_eq := rfl

/-- The cached leading coefficient is the same original selected nonzero entry. -/
theorem head_eq {matrix : Rectangular K (rows + 1) (columns + 1)}
    (selection : Selection matrix) :
    Blocks.head selection.pivoted = matrix selection.entry.row selection.entry.column := by
  rw [selection.pivoted_eq]
  dsimp only [Blocks.head, Permutation.pivotMatrix]
  rw [Permutation.swapColumns_apply, Permutation.swapRows_apply,
    Purelib.Data.Fin.swapZero_zero, Purelib.Data.Fin.swapZero_zero]

/-- The leading coefficient of the retained pivoted rectangle is nonzero. -/
theorem head_nonzero {matrix : Rectangular K (rows + 1) (columns + 1)}
    (selection : Selection matrix) : Blocks.head selection.pivoted ≠ 0 :=
  fun zero => selection.entry.nonzero (selection.head_eq.symm.trans zero)

end Selection

end Purelib.LinearAlgebra.Matrix.Pivot

end
