module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Alternating.NormalForm.Evaluation
import Purelib.LinearAlgebra.Alternating.Reduction.Reconstruction
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Pairing
public import Purelib.LinearAlgebra.Alternating.Handle.Solve
public import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Integral.RowSpan
import Purelib.LinearAlgebra.Vector.Unit
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.LinearAlgebra.Alternating.Reduction.Basic
public import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows
import Purelib.LinearAlgebra.Alternating.Reduction.Dual

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra.Vector

section
@[expose] public section

/-!
# Constructive integral row spanning from a retained unit normal form

Only the finitely many unused-coordinate kernel tests are required.
Transform the requested row, solve each disjoint unit handle, and apply
the retained transpose changes backwards. All coefficients are integers;
there is no field division, search, quotient, or choice of a preimage.
-/

namespace Purelib.LinearAlgebra.Alternating.NormalForm

variable {n : Nat}

/-- Each displayed unused cycle row is an actual integral kernel vector. -/
theorem unused_kernel {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (normal : NormalForm matrix raw) (index : Fin n) (unused : index ∉ Handle.Basic.handleIndices raw)
      (row : Fin n) :
    Weighted.weighted (matrix row) (normal.reduction.cycleRows index) = 0 := by
  rw [← Bilinear.Integral.pairing_left_unit, normal.reduction.cycleRows_apply, normal.pairing,
    normal.reduction.dualForward_dualBackward]
  exact Handle.Pairing.handlePairing_right_unused raw _ index unused

/-- The caller proves only the canonical finite kernel tests. Downstream
code consumes the cached coefficients and their exact original-row equation. -/
def rowSpan {matrix :
  SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}
    (normal : NormalForm matrix raw) (row : Data.Vector Int n)
    (annihilates : ∀ index, index ∉ Handle.Basic.handleIndices raw → Weighted.weighted row (normal.reduction.cycleRows
      index) = 0) : SquareMatrix.Integral.RowSpan matrix row := by
  let transformed := normal.reduction.forward row
  have supported : ∀ index, index ∉ Handle.Basic.handleIndices raw → transformed index = 0 := by
    intro index unused
    have zero := annihilates index unused
    rw [normal.reduction.cycleRows_apply, normal.reduction.weighted_dualBackward, Unit.weighted_right_unit] at zero
    exact zero
  let solved := Handle.Solve.handleSolve raw transformed
  let coefficients := normal.reduction.dualBackward solved
  refine ⟨coefficients, fun column => ?_⟩
  calc
    row column = Weighted.weighted row (Unit.unitVector column) := (Unit.weighted_right_unit row column).symm
    _ = Weighted.weighted transformed (normal.reduction.dualForward (Unit.unitVector column)) :=
      (normal.reduction.weighted_dualForward row _).symm
    _ = Handle.Pairing.handlePairing raw solved (normal.reduction.dualForward (Unit.unitVector column)) :=
      (Handle.Solve.handleSolve_pairing raw normal.disjoint transformed _ supported).symm
    _ = Bilinear.Integral.pairing matrix coefficients (Unit.unitVector column) := by
      rw [normal.pairing, normal.reduction.dualForward_dualBackward]
    _ = FiniteSum.Fin.sumFin (fun index => coefficients index * matrix index column) :=
      Bilinear.Integral.pairing_right_unit matrix coefficients column

end Purelib.LinearAlgebra.Alternating.NormalForm

end
