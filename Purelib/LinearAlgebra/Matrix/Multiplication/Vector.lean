module

public import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

/-! # Linearity of the original structural matrix-vector action

Every identity retains the original matrix, vectors and bounded coordinates.
The proofs compare finite scalar sums pointwise, then use structural vector
extensionality rather than identifying vectors with functions.
-/

public section

namespace Purelib.LinearAlgebra.Matrix.Multiplication

open Purelib.Algebra.FiniteSum.Fin
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector (zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext zipWith_apply)
open Purelib.LinearAlgebra renaming Matrix → Mat

variable {K : Type*} [CommRing K] {size : Nat}

/-- The original matrix action preserves structural vector addition. -/
theorem matrixVector_add_vector (matrix : Mat K size) (left right : Vec K size) :
    matrixVector matrix (zipWith (fun first last => first + last) left right) =
      zipWith (fun first last => first + last) (matrixVector matrix left) (matrixVector matrix right) := by
  apply vector_ext
  intro row
  calc
    _ = sumFin (fun column => matrix row column * (left column + right column)) :=
      (matrixVector_apply _ _ _).trans (sumFin_congr (fun column =>
        congrArg (fun value => matrix row column * value) (zipWith_apply _ left right column)))
    _ = sumFin (fun column => matrix row column * left column + matrix row column * right column) :=
      sumFin_congr (fun column => by ring1)
    _ = matrixVector matrix left row + matrixVector matrix right row :=
      (sumFin_add _ _).trans (congrArg₂ (fun first last : K => first + last)
        (matrixVector_apply matrix left row).symm (matrixVector_apply matrix right row).symm)
    _ = _ := (zipWith_apply _ _ _ row).symm

/-- The original matrix action preserves structural vector subtraction. -/
theorem matrixVector_sub (matrix : Mat K size) (left right : Vec K size) :
    matrixVector matrix (zipWith (fun first last => first - last) left right) =
      zipWith (fun first last => first - last) (matrixVector matrix left) (matrixVector matrix right) := by
  apply vector_ext
  intro row
  calc
    _ = sumFin (fun column => matrix row column * (left column - right column)) :=
      (matrixVector_apply _ _ _).trans (sumFin_congr (fun column =>
        congrArg (fun value => matrix row column * value) (zipWith_apply _ left right column)))
    _ = sumFin (fun column => matrix row column * left column - matrix row column * right column) :=
      sumFin_congr (fun column => by ring1)
    _ = matrixVector matrix left row - matrixVector matrix right row :=
      (sumFin_sub _ _).trans (congrArg₂ (fun first last : K => first - last)
        (matrixVector_apply matrix left row).symm (matrixVector_apply matrix right row).symm)
    _ = _ := (zipWith_apply _ _ _ row).symm

/-- The original matrix action sends the structural zero vector to the same structural zero vector. -/
theorem matrixVector_zero (matrix : Mat K size) :
    matrixVector matrix (vectorOfFn (fun _ : Fin size => (0 : K))) =
      vectorOfFn (fun _ : Fin size => (0 : K)) := by
  apply vector_ext
  intro row
  calc
    _ = sumFin (fun _ : Fin size => (0 : K)) :=
      (matrixVector_apply _ _ _).trans (sumFin_congr (fun column => by
        rewrite [vectorOfFn_apply]
        ring1))
    _ = 0 := sumFin_zero
    _ = _ := (vectorOfFn_apply (fun _ : Fin size => (0 : K)) row).symm

end Purelib.LinearAlgebra.Matrix.Multiplication

end
