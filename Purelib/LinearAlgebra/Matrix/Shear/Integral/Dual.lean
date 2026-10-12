module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Matrix.Shear.Integral.Basic
import Purelib.LinearAlgebra.Vector.IntCast
import Purelib.LinearAlgebra.Vector.Update
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

section
public section

/-!
# Pairing-preserving dual changes of coordinates

Congruence changes a matrix as `S C Sᵀ`; its arguments must change by
`S⁻ᵀ`, not by `S`. The formulas here use two cached finite weighted sums
per shear and work over any supplied commutative ring.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral

open Purelib
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {K : Type*} [CommRing K] {n : Nat}
namespace Shear

variable {first last : Fin n}

/-- Apply the transpose shear using two retained finite weighted sums.

The two sums are computed once and added at the original bounded pivot coordinates. -/
@[expose] def transpose (shear : SquareMatrix.Integral.Shear first last) (values : Data.Vector
  K n) : Data.Vector K n :=
  let leftTotal := Weighted.weighted (fun index => (shear.left index : K)) values
  let rightTotal := Weighted.weighted (fun index => (shear.right index : K)) values
  Update.bump (Update.bump values first leftTotal) last rightTotal

/-- Apply the inverse transpose shear using two retained finite weighted sums.

The two sums are computed once and subtracted at the original bounded pivot coordinates. -/
@[expose] def dual (shear : SquareMatrix.Integral.Shear first last) (values : Data.Vector K n)
  : Data.Vector K n :=
  let leftTotal := Weighted.weighted (fun index => (shear.left index : K)) values
  let rightTotal := Weighted.weighted (fun index => (shear.right index : K)) values
  Update.bump (Update.bump values first (-leftTotal)) last (-rightTotal)

/-- Matrix congruence pairs with the transpose on its two arguments. -/
theorem pairing_transform (shear : SquareMatrix.Integral.Shear first last) (matrix :
  SquareMatrix.IntegralMatrix n) (left right : Data.Vector K n) :
    Bilinear.Integral.pairing (shear.transform matrix) left right = Bilinear.Integral.pairing matrix (shear.transpose
      left) (shear.transpose right) := open Purelib.Algebra in by
  have expanded (row column : Fin n) : (shear.transform matrix row column : K) =
      (matrix row column : K) + (shear.left row : K) * (matrix first column : K) +
      (shear.right row : K) * (matrix last column : K) +
      (matrix row first : K) * (shear.left column : K) +
      (shear.left row : K) * ((matrix first first : K) * (shear.left column : K)) +
      (shear.right row : K) * ((matrix last first : K) * (shear.left column : K)) +
      (matrix row last : K) * (shear.right column : K) +
      (shear.left row : K) * ((matrix first last : K) * (shear.right column : K)) +
      (shear.right row : K) * ((matrix last last : K) * (shear.right column : K)) := by
    rw [shear.transform_apply]
    simp only [Purelib.Algebra.Ring.IntCast.add, Ring.IntCast.intCast_mul]
    ring1
  unfold Bilinear.Integral.pairing
  rw [Bilinear.Matrix.Basic.bilinear_congr expanded left right]
  simp only [Bilinear.Matrix.Basic.bilinear_add, Bilinear.Matrix.Basic.bilinear_outer, Weighted.weighted_scale]
  rw [SquareMatrix.Integral.Shear.transpose, SquareMatrix.Integral.Shear.transpose,
    Bilinear.Matrix.Basic.bilinear_bump_right, Bilinear.Matrix.Basic.bilinear_bump_right,
    Bilinear.Matrix.Basic.bilinear_bump_left,
    Bilinear.Matrix.Basic.bilinear_bump_left, Weighted.weighted_bump, Weighted.weighted_bump, Weighted.weighted_bump,
      Weighted.weighted_bump]
  ring1

/-- Weights vanishing at both pivot coordinates are unchanged by the dual action. -/
private theorem weighted_dual (shear : SquareMatrix.Integral.Shear first last) (weights : Fin n → K)
    (firstZero : weights first = 0) (lastZero : weights last = 0) (values : Data.Vector K n) :
    Weighted.weighted weights (shear.dual values) = Weighted.weighted weights values := by
  rw [SquareMatrix.Integral.Shear.dual, Weighted.weighted_bump, Weighted.weighted_bump, firstZero, lastZero,
    mul_zero, mul_zero, add_zero, add_zero]

end Shear
end Purelib.LinearAlgebra.Matrix.Integral

namespace Purelib.LinearAlgebra.Matrix.Shear.Integral.Dual.Pairing

open Purelib
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {K : Type*} [CommRing K] {n : Nat} {first last : Fin n}

/-- Weights vanishing at both pivot coordinates are unchanged by the transpose action. -/
private theorem weighted_transpose (shear : SquareMatrix.Integral.Shear first last) (weights : Fin n → K)
    (firstZero : weights first = 0) (lastZero : weights last = 0) (values : Data.Vector K n) :
    Weighted.weighted weights (shear.transpose values) = Weighted.weighted weights values := by
  rw [SquareMatrix.Integral.Shear.transpose, Weighted.weighted_bump, Weighted.weighted_bump, firstZero,
    lastZero, mul_zero, mul_zero, add_zero, add_zero]

end Purelib.LinearAlgebra.Matrix.Shear.Integral.Dual.Pairing

namespace Purelib.LinearAlgebra.Matrix.Integral

open Purelib
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {K : Type*} [CommRing K] {n : Nat}
namespace Shear
variable {first last : Fin n}

/-- The transpose action undoes the dual action on every structural vector. -/
theorem transpose_dual (shear : SquareMatrix.Integral.Shear first last) (values : Data.Vector K
  n) : shear.transpose (shear.dual values) = values := by
  have left := shear.weighted_dual (fun index => (shear.left index : K))
    (by rw [shear.left_first, Purelib.Algebra.Ring.IntCast.cast_zero]) (by
        rw [shear.left_last, Purelib.Algebra.Ring.IntCast.cast_zero]) values
  have right := shear.weighted_dual (fun index => (shear.right index : K))
    (by rw [shear.right_first, Purelib.Algebra.Ring.IntCast.cast_zero]) (by
        rw [shear.right_last, Purelib.Algebra.Ring.IntCast.cast_zero]) values
  apply Data.Vector.Basic.vector_ext; intro index
  change Update.bump (Update.bump (shear.dual values) first _) last _ index = _
  rw [left, right, SquareMatrix.Integral.Shear.dual, Update.bump_apply, Update.bump_apply,
    Update.bump_apply, Update.bump_apply]
  by_cases atFirst : index = first
  · rw [if_pos atFirst, if_pos atFirst]
    by_cases atLast : index = last
    · rw [if_pos atLast, if_pos atLast]; ring1
    · rw [if_neg atLast, if_neg atLast]; ring1
  · rw [if_neg atFirst, if_neg atFirst]
    by_cases atLast : index = last
    · rw [if_pos atLast, if_pos atLast]; ring1
    · rw [if_neg atLast, if_neg atLast]; ring1

/-- The dual action undoes the transpose action on every structural vector. -/
theorem dual_transpose (shear : SquareMatrix.Integral.Shear first last) (values : Data.Vector K
  n) : shear.dual (shear.transpose values) = values := by
  have left := Matrix.Shear.Integral.Dual.Pairing.weighted_transpose shear (fun index => (shear.left
    index : K))
    (by rw [shear.left_first, Purelib.Algebra.Ring.IntCast.cast_zero]) (by
        rw [shear.left_last, Purelib.Algebra.Ring.IntCast.cast_zero]) values
  have right := Matrix.Shear.Integral.Dual.Pairing.weighted_transpose shear (fun index =>
    (shear.right index : K))
    (by rw [shear.right_first, Purelib.Algebra.Ring.IntCast.cast_zero]) (by
        rw [shear.right_last, Purelib.Algebra.Ring.IntCast.cast_zero]) values
  apply Data.Vector.Basic.vector_ext; intro index
  change Update.bump (Update.bump (shear.transpose values) first _) last _ index = _
  rw [left, right, SquareMatrix.Integral.Shear.transpose, Update.bump_apply, Update.bump_apply,
    Update.bump_apply, Update.bump_apply]
  by_cases atFirst : index = first
  · rw [if_pos atFirst, if_pos atFirst]
    by_cases atLast : index = last
    · rw [if_pos atLast, if_pos atLast]; ring1
    · rw [if_neg atLast, if_neg atLast]; ring1
  · rw [if_neg atFirst, if_neg atFirst]
    by_cases atLast : index = last
    · rw [if_pos atLast, if_pos atLast]; ring1
    · rw [if_neg atLast, if_neg atLast]; ring1

/-- Applying the dual shear to both vectors preserves the pairing with the transformed matrix. -/
theorem pairing_dual (shear : SquareMatrix.Integral.Shear first last) (matrix :
  SquareMatrix.IntegralMatrix n) (left right : Data.Vector K n) :
    Bilinear.Integral.pairing matrix left right = Bilinear.Integral.pairing (shear.transform matrix) (shear.dual left)
      (shear.dual right) := by
  rw [shear.pairing_transform, shear.transpose_dual, shear.transpose_dual]

end Shear

end Purelib.LinearAlgebra.Matrix.Integral

end

section
public section

/-!
# Integer weights of the actual transformed cycle rows

The inverse of the dual coordinate map is the transpose of the ordinary
basis change. Applying it to coordinate unit vectors therefore constructs
integer rows for linear combinations of cycles. Pairing those rows with the
original values evaluates the corresponding row of the final handle form.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral.Shear

open Purelib
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {K : Type*} [CommRing K] {n : Nat}

/-- Casting an integral vector commutes with the retained transpose shear. -/
theorem cast_transpose {first last : Fin n} (shear : SquareMatrix.Integral.Shear first last)
    (values : Data.Vector Int n) :
    IntCast.castVector (K := K) (shear.transpose values) = shear.transpose (IntCast.castVector values) := by
  unfold SquareMatrix.Integral.Shear.transpose
  simp only [Int.cast_id]
  rw [IntCast.cast_bump, IntCast.cast_bump, IntCast.cast_weighted, IntCast.cast_weighted]
end Purelib.LinearAlgebra.Matrix.Integral.Shear

end

section
public section

/-!
# Constructive integral row spanning from a retained unit normal form

Only the finitely many unused-coordinate kernel tests are required.
Transform the requested row, solve each disjoint unit handle, and apply
the retained transpose changes backwards. All coefficients are integers;
there is no field division, search, quotient, or choice of a preimage.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral.Shear

open Purelib
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {n : Nat}

/-- Move a transpose shear from the values to the weights in an integral weighted sum. -/
theorem weighted_transpose {first last : Fin n} (shear : SquareMatrix.Integral.Shear first last)
    (weights values : Data.Vector Int n) : Weighted.weighted weights (shear.transpose values) =
      Weighted.weighted (shear.apply weights) values := open Purelib.Algebra in by
  rw [SquareMatrix.Integral.Shear.transpose, Weighted.weighted_bump, Weighted.weighted_bump]
  have expanded : Weighted.weighted (shear.apply weights) values = Weighted.weighted weights values +
      Weighted.weighted shear.left values * weights first + Weighted.weighted shear.right values * weights last := by
    calc
      _ = FiniteSum.Fin.sumFin (fun index => weights index * values index +
          (shear.left index * values index) * weights first + (shear.right index * values index) * weights last) := by
        apply FiniteSum.Fin.sumFin_congr
        intro index
        rw [SquareMatrix.Integral.Shear.apply, Data.Vector.Basic.vectorOfFn_apply]
        ring1
      _ = _ := by
        rw [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_mul_right,
          FiniteSum.Fin.sumFin_mul_right];
        rfl
  exact expanded.symm
end Purelib.LinearAlgebra.Matrix.Integral.Shear

end
