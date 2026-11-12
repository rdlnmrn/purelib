module

import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Action
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
meta import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Action
meta import Purelib.LinearAlgebra.Matrix.Multiplication
meta import Purelib.Data.Gaussian.Basic
meta import Purelib.Data.Gaussian.Field
meta import Purelib.Data.Vector.Basic

/-! # Exact scaled-inverse actions, including vanishing pivots -/

namespace TestPurelib.LinearAlgebra.Matrix.Inverse.Scaled.Action

open Purelib
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Matrix.Inverse.Scaled
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector.Basic

example {K : Type*} [CommRing K] {n : Nat} (matrix : SquareMatrix K n)
    (right : Data.Vector K n) :
    (Action.compute matrix right).scalar = (Compute.scaledInverse matrix).scalar :=
  (Action.compute matrix right).scalar_eq

example {K : Type*} [CommRing K] {n : Nat} (matrix : SquareMatrix K n)
    (right : Data.Vector K n) :
    (Action.compute matrix right).values =
      SquareMatrix.Multiplication.matrixVector (Compute.scaledInverse matrix).inverse right :=
  (Action.compute matrix right).values_eq

/-- Compare an executed action to the original complete inverse computation. -/
private def checkAction {n : Nat} (matrix : SquareMatrix Canonical n) (right : Data.Vector Canonical n) : IO Unit := do
  let action := Action.compute matrix right
  let original := Compute.scaledInverse matrix
  let reference := SquareMatrix.Multiplication.matrixVector original.inverse right
  unless action.scalar = original.scalar ∧ (∀ row, action.values row = reference row) do
    throw (IO.userError "scaled-inverse action changed the original scalar or vector")

/-- Exercise the empty case, a zero scalar, a zero leading pivot, singularity and a nonsymmetric matrix. -/
private def checkActions : IO Unit := do
  checkAction (SquareMatrix.matrixOfFn (fun index : Fin 0 => Fin.elim0 index)) (.nil)
  let one : SquareMatrix Canonical 1 := .cons (.cons 0 .nil) .nil
  checkAction one (.cons 7 .nil)
  let zeroPivot : SquareMatrix Canonical 2 := .cons (.cons 0 (.cons 1 .nil))
    (.cons (.cons 2 (.cons 3 .nil)) .nil)
  checkAction zeroPivot (.cons 5 (.cons (-7) .nil))
  let singular : SquareMatrix Canonical 2 := .cons (.cons 1 (.cons 2 .nil))
    (.cons (.cons 2 (.cons 4 .nil)) .nil)
  checkAction singular (.cons 3 (.cons 8 .nil))
  let three : SquareMatrix Canonical 3 :=
    .cons (.cons 2 (.cons 3 (.cons (-1) .nil)))
      (.cons (.cons 7 (.cons 4 (.cons 5 .nil)))
        (.cons (.cons 6 (.cons (-2) (.cons 9 .nil))) .nil))
  checkAction three (.cons 4 (.cons (-5) (.cons 8 .nil)))

#eval checkActions

end TestPurelib.LinearAlgebra.Matrix.Inverse.Scaled.Action
