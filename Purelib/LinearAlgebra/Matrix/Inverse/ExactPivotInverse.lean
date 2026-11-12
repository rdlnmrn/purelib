module
import Purelib.LinearAlgebra.Matrix.Permutation
meta import Purelib.Elab.ConstructiveInjectivity
-- Exposed scans retain the original dependent zero-entry certificates.
public import Purelib.LinearAlgebra.Matrix.Pivot
public import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Blocks
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Compute
import Purelib.LinearAlgebra.Matrix.Schur

public import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic

open Purelib

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

@[expose] public section

/-!
# A selected-pivot inverse for a fixed finite rational matrix

For a fixed exact matrix, decidable pivot selection is harmless.  Unlike the
polynomial all-pivot aggregation needed by the synchronized approximation
layer, this constructor follows only one nonzero pivot at each size.  Existing
finite Schur and unpivoting identities verify the result.  The approximation
algorithms and their continuity/movement guarantees are unchanged.
-/

namespace Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse

open Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse

open Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse in
/-- Select a nonzero entry of a nonempty matrix with trivial left kernel.

The finite scan supplies the retained indices; triviality rules out its all-zero outcome. -/
def selectPivot {size : Nat} (matrix :
  Square (size + 1))
    (trivial : LeftKernelTrivial matrix) :
      SquareMatrix.Pivot.Entry (fun row column => matrix row column) := by
  cases SquareMatrix.Pivot.scan (fun row column => matrix row column) with
  | found row column nonzero => exact ⟨row, column, nonzero⟩
  | zero allZero =>
      have impossible : False := by
        rcases exists_nonzero_entry_of_leftKernelTrivial matrix trivial with
          ⟨row, column, nonzero⟩
        exact nonzero (allZero row column)
      exact impossible.elim

set_option genInjectivity false in
/-- An exact finite inverse retains its scaled-inverse data and nonzero scalar.

The original matrix indexes both multiplication identities. Its same retained
scalar is certified nonzero, without changing the computed inverse entries. -/
structure NonzeroInverse {size : Nat}
  (matrix : Square size) where
  /-- The computed scaled inverse of the original matrix, with both multiplication identities. -/ inverse :
    ScaledInverse matrix
  /-- The retained inverse scalar is nonzero. -/ scalar_nonzero : inverse.scalar ≠ 0

constructive_injectivity NonzeroInverse

/-- One finite pivot scan and one smaller inverse per recursive stage.
Nonvanishing descends through the fraction-free Schur complement; no search
success or determinant-separation premise is left for the caller. -/
def invert : {size : Nat} -> (matrix :
  Square size) ->
    LeftKernelTrivial matrix ->
      NonzeroInverse matrix
  | 0, matrix, _ =>
      { inverse := Scaled.Compute.scaledInverse matrix
        scalar_nonzero := by change (1 : Gaussian) ≠ 0; decide }
  | size + 1, matrix, trivial => by
      let pivot := selectPivot matrix trivial
      let pivoted := SquareMatrix.Permutation.pivotMatrix matrix pivot.row pivot.column
      have pivotedTrivial : LeftKernelTrivial pivoted :=
        PivotedScaledInverse.leftKernelTrivial_pivotMatrix trivial pivot.row pivot.column
      have headNonzero : Blocks.head pivoted ≠ 0 := by
        simpa only [pivoted, Blocks.head,
          SquareMatrix.Permutation.pivotMatrix,
            SquareMatrix.Permutation.swapColumns_apply,
            SquareMatrix.Permutation.swapRows_apply,
            Data.Fin.swapZero_zero] using pivot.nonzero
      let smaller := ExactPivotInverse.invert
        (Schur.schur pivoted)
        (PivotedScaledInverse.leftKernelTrivial_schur_of_head_nonzero pivoted pivotedTrivial
          headNonzero)
      refine
        { inverse := PivotedScaledInverse.pivotBranch matrix pivot.row pivot.column smaller.inverse
          scalar_nonzero := ?_ }
      change Blocks.head pivoted * smaller.inverse.scalar ≠ 0
      exact Data.Gaussian.Field.mul_ne_zero_direct
        headNonzero smaller.scalar_nonzero

end Purelib.LinearAlgebra.Matrix.Inverse.ExactPivotInverse
