module

import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Alternating.Reduction.Basic
public import Purelib.LinearAlgebra.Alternating.Reduction.Check
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.Check
import Purelib.Data.Vector.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

section
public section

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
/-- A concrete obstruction to the submitted integral normal-form claim.

The alternatives identify reused coordinates, a failed pivot reduction, or a mismatching output entry after a valid
reduction. -/
inductive NormalForm.Check.InvalidNormalForm (matrix :
  SquareMatrix.IntegralMatrix n) (raw : List (Handle.Basic.PivotIndices n)) where
  /-- The submitted handle list repeats a coordinate. -/ | repeated (invalid : ¬ (Handle.Basic.handleIndices raw).Nodup)
  /-- A specific stage of the submitted reduction has a non-unit pivot. -/ | reduction (invalid :
    Reduction.Check.InvalidReduction matrix raw)
  /-- A valid reduction has an output entry unequal to the claimed handle entry. -/ | entry (reduction :
    Reduction matrix raw) (row column : Fin n)
      (different : reduction.output row column ≠ Handle.Basic.handleEntry raw row column)

constructive_injectivity NormalForm.Check.InvalidNormalForm

open Purelib.LinearAlgebra.Alternating in
/-- Exhaustively check this finite normal-form claim. A rejected final entry
retains the entire valid reduction and the exact offending coordinates. -/
@[expose] def NormalForm.Check.checkNormalForm (matrix :
  SquareMatrix.IntegralMatrix n) (raw : List (Handle.Basic.PivotIndices n)) :
    Except (NormalForm.Check.InvalidNormalForm matrix raw) (NormalForm matrix raw) :=
  if disjoint : (Handle.Basic.handleIndices raw).Nodup then
    match Reduction.Check.checkReduction matrix raw with
    | .error invalid => .error (.reduction invalid)
    | .ok reduction =>
        match SquareMatrix.Integral.Check.checkEntries (fun row column => reduction.output row column)
          (Handle.Basic.handleEntry raw) with
        | .valid entries => .ok ⟨reduction, disjoint, entries⟩
        | .invalid row column different => .error (.entry reduction row column different)
  else .error (.repeated disjoint)

end Purelib.LinearAlgebra.Alternating

end
