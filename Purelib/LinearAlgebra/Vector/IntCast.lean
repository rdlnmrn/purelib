module
public import Purelib.LinearAlgebra.Vector.Weighted
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Vector.Update
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

namespace Purelib.LinearAlgebra.Vector.IntCast

open Purelib
open Purelib.LinearAlgebra.Vector

variable {K : Type*} [CommRing K] {n : Nat}

/-- Cast each entry of an integral structural vector into the coefficient ring.

The result keeps the original dimension and coordinate order. -/
@[expose] def castVector (values : Data.Vector Int n) : Data.Vector K n :=
  Data.Vector.Basic.vectorOfFn fun index => (values index : K)

open Purelib.LinearAlgebra.Vector
/-- Read an entry of the cast vector as the scalar integer cast. -/
theorem castVector_apply (values : Data.Vector Int n) (index : Fin n) :
    IntCast.castVector (K := K) values index = (values index : K) := Data.Vector.Basic.vectorOfFn_apply _ index

/-- Casting commutes with adding an integer amount at one vector coordinate.

The retained coordinate test and structural vector entries are unchanged; only their integer casts are transported. -/
theorem cast_bump (values : Data.Vector Int n) (index : Fin n) (amount : Int) :
    IntCast.castVector (K := K) (Update.bump values index amount) = Update.bump (IntCast.castVector values) index
      (amount : K) := by
  apply Data.Vector.Basic.vector_ext; intro position
  rw [IntCast.castVector_apply, Update.bump_apply, Update.bump_apply, IntCast.castVector_apply,
    Purelib.Algebra.Ring.IntCast.add]
  by_cases same : position = index
  · rw [if_pos same, if_pos same]
  · rw [if_neg same, if_neg same, Purelib.Algebra.Ring.IntCast.cast_zero]

/-- Casting an integral weighted sum casts its weights and vector entries.

Each original finite index contributes the product of its cast weight and its cast vector entry. -/
theorem cast_weighted (weights : Fin n → Int) (values : Data.Vector Int n) :
    ((Weighted.weighted weights values : Int) : K) = Weighted.weighted (fun index => (weights index : K))
      (IntCast.castVector values) := open Purelib.Algebra in by
  rw [Weighted.weighted, Purelib.Algebra.FiniteSum.Fin.cast_sum]
  apply FiniteSum.Fin.sumFin_congr; intro index
  rw [IntCast.castVector_apply, Ring.IntCast.intCast_mul]

end Purelib.LinearAlgebra.Vector.IntCast

end
