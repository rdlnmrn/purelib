module

import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Reduction.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Mathlib.Tactic.Linter.Lint
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
@[expose] public section

/-!
# Exact replay of integral pairing reductions

An untrusted producer supplies only oriented unit pivots. Each successful
stage retains its shear and reduced matrix; invalidity identifies a bad pivot
or an entry which fails the claimed final normal form. Rejection is only of
this submitted reduction, not of the existence of another integral basis.
-/

namespace Purelib.LinearAlgebra.Alternating

variable {n : Nat}

set_option genInjectivity false in
/-- A certified integral reduction to a disjoint signed handle matrix.

The record retains the actual reduction, coordinate disjointness and the exact entries of its computed output. -/
structure NormalForm (matrix :
  SquareMatrix.IntegralMatrix n) (raw : List (Handle.Basic.PivotIndices n)) where
  /-- The retained sequence of integral unit-pivot reductions. -/ reduction : Reduction matrix raw
  /-- No coordinate is reused among the retained handles. -/ disjoint : (Handle.Basic.handleIndices raw).Nodup
  /-- Every computed output entry equals the specified signed handle entry. -/ entries : ∀ row column, reduction.output
    row column = Handle.Basic.handleEntry raw row column

constructive_injectivity NormalForm

namespace NormalForm

open Purelib.LinearAlgebra.Alternating in
/-- A row outside the normal form handles is identically zero. -/
theorem unused_row {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (normal : NormalForm matrix raw) (row column : Fin n) (unused : row ∉ Handle.Basic.handleIndices
      raw) :
    normal.reduction.output row column = 0 := by
  rw [normal.entries]
  exact Handle.Basic.handleEntry_unused raw row column unused

end NormalForm
end Purelib.LinearAlgebra.Alternating

end
