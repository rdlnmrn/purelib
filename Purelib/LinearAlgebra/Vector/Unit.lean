module
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Matrix.Basic
public import Purelib.LinearAlgebra.Vector.IntCast
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Algebra.Ring.Int.Defs

section
public section

/-!
# Integer weights of the actual transformed cycle rows

The inverse of the dual coordinate map is the transpose of the ordinary
basis change. Applying it to coordinate unit vectors therefore constructs
integer rows for linear combinations of cycles. Pairing those rows with the
original values evaluates the corresponding row of the final handle form.
-/

namespace Purelib.LinearAlgebra.Vector.Unit

open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {K : Type*} [CommRing K] {n : Nat}

/-- Materialize the coordinate unit vector at a retained bounded index.

Its selected entry is one and all other entries are zero in the coefficient ring. -/
@[expose] def unitVector (index : Fin n) : Data.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun position => if position = index then 1 else 0

open Purelib.LinearAlgebra.Vector
/-- Read a coordinate unit as its equality indicator. -/
theorem unitVector_apply (index position : Fin n) :
    Unit.unitVector (K := K) index position = if position = index then 1 else 0 := Data.Vector.Basic.vectorOfFn_apply _
      position

/-- Casting an integral unit vector gives the unit vector over the coefficient ring. -/
theorem cast_unitVector (index : Fin n) : IntCast.castVector (Unit.unitVector (K := Int) index) = Unit.unitVector (K :=
  K) index := by
  apply Data.Vector.Basic.vector_ext; intro position
  rw [IntCast.castVector_apply, Unit.unitVector_apply, Unit.unitVector_apply]
  by_cases same : position = index
  · rw [if_pos same, if_pos same, Int.cast_one]
  · rw [if_neg same, if_neg same, Purelib.Algebra.Ring.IntCast.cast_zero]
end Purelib.LinearAlgebra.Vector.Unit

end

section
public section

/-! Exact reconstruction from the complete finite normal-form cycle rows. -/
namespace Purelib.LinearAlgebra.Vector.Unit

open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {n : Nat} {matrix : SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}

open Purelib.LinearAlgebra.Vector in
/-- A unit weight vector selects the corresponding integral value.

The original equality indicator isolates the retained bounded coordinate in the same finite weighted sum. -/
theorem weighted_left_unit (index : Fin n) (values : Data.Vector Int n) :
    Weighted.weighted (Unit.unitVector index) values = values index := open Purelib.Algebra in by
  calc
    _ = Weighted.weighted (fun position => if position = index then 1 else 0) values := by
      apply FiniteSum.Fin.sumFin_congr
      intro position
      rw [Unit.unitVector_apply]
    _ = _ := Weighted.weighted_unit index values

end Purelib.LinearAlgebra.Vector.Unit

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

namespace Purelib.LinearAlgebra.Vector.Unit

open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {n : Nat}

open Purelib.LinearAlgebra.Vector in
/-- An integral unit value vector selects the corresponding weight. -/
theorem weighted_right_unit (weights : Fin n → Int) (index : Fin n) :
    Weighted.weighted weights (Unit.unitVector index) = weights index := open Purelib.Algebra in by
  calc
    _ = FiniteSum.Fin.sumFin (fun position => if position = index then weights position else 0) := by
      apply FiniteSum.Fin.sumFin_congr
      intro position
      rw [Unit.unitVector_apply]
      by_cases same : position = index
      · rw [if_pos same, if_pos same, mul_one]
      · rw [if_neg same, if_neg same, mul_zero]
    _ = _ := FiniteSum.Fin.sumFin_ite_eq index _
end Purelib.LinearAlgebra.Vector.Unit

end
