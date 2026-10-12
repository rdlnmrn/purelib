module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Vector.Unit
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.LinearAlgebra.Vector

section
@[expose] public section

/-!
# Pairing-preserving dual changes of coordinates

Congruence changes a matrix as `S C Sᵀ`; its arguments must change by
`S⁻ᵀ`, not by `S`. The formulas here use two cached finite weighted sums
per shear and work over any supplied commutative ring.
-/

namespace Purelib.LinearAlgebra.Bilinear.Integral

variable {K : Type*} [CommRing K] {n : Nat}

/-- Evaluate an integral matrix as a bilinear form over the supplied commutative ring.

Matrix entries are cast to the coefficient ring before the two finite coordinate sums. -/
def pairing (matrix : SquareMatrix.IntegralMatrix n) (left right :
  Data.Vector K n) : K :=
  Bilinear.Matrix.Basic.bilinear (fun row column => (matrix row column : K)) left right

end Purelib.LinearAlgebra.Bilinear.Integral

end

section
@[expose] public section

/-!
# Intersection of the computed integral cycle rows

The actual cycle change of basis has the same signed unit-handle form as
the reduced matrix. These finite integer identities do not assume a
geometric genus or a preassigned ordering of branch labels.
-/

namespace Purelib.LinearAlgebra.Bilinear.Integral

variable {n : Nat} {matrix : SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}

open Purelib.LinearAlgebra
/-- Negating the left integral vector negates the matrix pairing. -/
theorem pairing_neg_left (matrix : SquareMatrix.IntegralMatrix n)
  (first last : Data.Vector Int n) :
    pairing matrix (Data.Vector.Basic.vectorOfFn fun index => -first index) last =
      -pairing matrix first last := by
  unfold pairing Bilinear.Matrix.Basic.bilinear
  apply (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_neg _)
  intro row
  apply (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_neg _)
  intro column
  rw [Data.Vector.Basic.vectorOfFn_apply]
  ring1

/-- Negating the right integral vector negates the matrix pairing. -/
theorem pairing_neg_right (matrix : SquareMatrix.IntegralMatrix n)
  (first last : Data.Vector Int n) :
    pairing matrix first (Data.Vector.Basic.vectorOfFn fun index => -last index) =
      -pairing matrix first last := by
  unfold pairing Bilinear.Matrix.Basic.bilinear
  apply (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_neg _)
  intro row
  apply (FiniteSum.Fin.sumFin_congr ?_).trans (FiniteSum.Fin.sumFin_neg _)
  intro column
  rw [Data.Vector.Basic.vectorOfFn_apply]
  ring1
end Purelib.LinearAlgebra.Bilinear.Integral

end

section
@[expose] public section

/-!
# Constructive integral row spanning from a retained unit normal form

Only the finitely many unused-coordinate kernel tests are required.
Transform the requested row, solve each disjoint unit handle, and apply
the retained transpose changes backwards. All coefficients are integers;
there is no field division, search, quotient, or choice of a preimage.
-/

namespace Purelib.LinearAlgebra.Bilinear.Integral

variable {n : Nat}

open Purelib.LinearAlgebra
/-- A right coordinate unit extracts the weighted matrix column. -/
theorem pairing_right_unit (matrix : SquareMatrix.IntegralMatrix n)
  (weights : Data.Vector Int n) (column : Fin n) :
    pairing matrix weights (Unit.unitVector column) = FiniteSum.Fin.sumFin (fun row => weights row *
      matrix row column) := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  have select := Unit.weighted_right_unit (fun index => matrix row index * weights row) column
  exact select.trans (mul_comm _ _)

/-- A left coordinate unit extracts the weighted matrix row. -/
theorem pairing_left_unit (matrix : SquareMatrix.IntegralMatrix n)
  (row : Fin n) (values : Data.Vector Int n) :
    pairing matrix (Unit.unitVector row) values = Weighted.weighted (matrix row) values := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index => if index = row then Weighted.weighted (matrix index) values else 0) := by
      apply FiniteSum.Fin.sumFin_congr
      intro index
      by_cases same : index = row
      · rw [if_pos same]
        apply FiniteSum.Fin.sumFin_congr
        intro column
        rw [Unit.unitVector_apply, if_pos same, mul_one]
        exact congrArg (fun value : Int => value * values column) Int.cast_id
      · rw [if_neg same]
        exact (FiniteSum.Fin.sumFin_congr (fun column => by
          rw [Unit.unitVector_apply, if_neg same, mul_zero, zero_mul])).trans FiniteSum.Fin.sumFin_zero
    _ = _ := FiniteSum.Fin.sumFin_ite_eq row _
end Purelib.LinearAlgebra.Bilinear.Integral

end
