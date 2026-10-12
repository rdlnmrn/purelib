module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Mathlib.Algebra.Ring.Int.Defs

open Purelib.Algebra

open Purelib

open Purelib.LinearAlgebra.Alternating

@[expose] public section

/-! Read a retained handle list as a finite sum with its certified handle count. -/
namespace Purelib.LinearAlgebra.Alternating
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)

/-- Express the recursive handle pairing as a finite sum indexed by the retained list length.

Every summand is the signed two-coordinate determinant for that same bounded list entry. -/
theorem handlePairing_indexed {n : Nat} (raw : List (Handle.Basic.PivotIndices n))
    (left right : Data.Vector Int n) :
    Handle.Pairing.handlePairing raw left right = FiniteSum.Fin.sumFin (fun index : Fin raw.length =>
      left (raw[index.val]'index.isLt).1 * right (raw[index.val]'index.isLt).2 -
      left (raw[index.val]'index.isLt).2 * right (raw[index.val]'index.isLt).1) := by
  induction raw with
  | nil => rfl
  | cons pair rest ih =>
      rw [Handle.Pairing.handlePairing, FiniteSum.Fin.sumFin_succ, ih]
      rfl

/-- Transport the indexed handle pairing to a supplied equal handle count.

The length equality supplies bounds for the original list reads; no handle list is rebuilt. -/
theorem handlePairing_indexed_count {n count : Nat} (raw : List (Handle.Basic.PivotIndices n))
    (size : raw.length = count) (left right : Data.Vector Int n) :
    Handle.Pairing.handlePairing raw left right = FiniteSum.Fin.sumFin (fun index : Fin count =>
      left (raw[index.val]'(by rw [size]; exact index.isLt)).1 * right (raw[index.val]'(by
          rw [size];
          exact index.isLt)).2 -
      left (raw[index.val]'(by rw [size]; exact index.isLt)).2 * right (raw[index.val]'(by
          rw [size];
          exact index.isLt)).1) := by
  cases size
  exact handlePairing_indexed raw left right

end Purelib.LinearAlgebra.Alternating
