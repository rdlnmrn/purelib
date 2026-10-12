module
import Purelib.Algebra.Ring.IntCast
public import Purelib.Algebra.Group.Negation
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
public import Purelib.LinearAlgebra.Vector.Unit
import Purelib.LinearAlgebra.Vector.Weighted
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

section

open Purelib
open Purelib.Algebra

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Vector

section
public section

/-!
# Exact evaluation of an integral normal form

The dual coordinate changes retain the original bilinear value. The final
normal form evaluates to an explicit finite list of handle determinants.
-/

namespace Purelib.LinearAlgebra.Alternating.Handle.Pairing

variable {K : Type*} [CommRing K] {n : Nat}

/-- Sum the signed coordinate determinants of the retained ordered handles.

The finite recursion preserves the original handle order and evaluates both structural vectors at each pair. -/
@[expose] def handlePairing : List (Handle.Basic.PivotIndices n) → Data.Vector K n →
  Data.Vector K n → K
  | [], _, _ => 0
  | pair :: remaining, left, right => left pair.1 * right pair.2 - left pair.2 * right pair.1 +
    Purelib.LinearAlgebra.Alternating.Handle.Pairing.handlePairing remaining left right

/-- Casting an integer indicator into the coefficient ring preserves its zero-or-one value. -/
private theorem cast_indicator (predicate : Prop) [Decidable predicate] :
    ((if predicate then 1 else 0 : Int) : K) = if predicate then 1 else 0 := by
  by_cases truth : predicate
  · rw [if_pos truth, if_pos truth, Int.cast_one]
  · rw [if_neg truth, if_neg truth, Ring.IntCast.cast_zero]

/-- The indicator of a conjunction is the product of its two indicators. -/
private theorem indicator_and (first last : Prop) [Decidable first] [Decidable last] :
    (if first ∧ last then 1 else 0 : K) = (if first then 1 else 0) * (if last then 1 else 0) := by
  by_cases left : first
  · rw [if_pos left]
    by_cases right : last
    · rw [if_pos right, if_pos ⟨left, right⟩, one_mul]
    · rw [if_neg right, if_neg (fun both => right both.2), mul_zero]
  · rw [if_neg left, if_neg (fun both => left both.1), zero_mul]

open Purelib.LinearAlgebra.Alternating in
/-- The bilinear form of a handle-entry matrix equals its recursive handle pairing.

Integer entries are cast into the supplied commutative ring before evaluation. -/
theorem handleEntry_pairing (raw : List (Handle.Basic.PivotIndices n)) (left right : Data.Vector K n) :
    Bilinear.Matrix.Basic.bilinear (fun row column => (Handle.Basic.handleEntry raw row column : K)) left right =
      Handle.Pairing.handlePairing raw left right := open Purelib.LinearAlgebra.Vector in by
  induction raw with
  | nil =>
      exact (Bilinear.Matrix.Basic.bilinear_congr (fun _ _ => show ((0 : Int) : K) = 0 from Ring.IntCast.cast_zero) left
        right).trans (Bilinear.Matrix.Basic.bilinear_zero left right)
  | cons indices remaining ih =>
      have expanded (row column : Fin n) : (Handle.Basic.handleEntry (indices :: remaining) row column : K) =
          (if row = indices.1 then 1 else 0) * (if column = indices.2 then 1 else 0) -
          (if row = indices.2 then 1 else 0) * (if column = indices.1 then 1 else 0) +
          (Handle.Basic.handleEntry remaining row column : K) := by
        rw [Handle.Basic.handleEntry, Ring.IntCast.add, Ring.IntCast.sub, Handle.Pairing.cast_indicator,
          Handle.Pairing.cast_indicator, Handle.Pairing.indicator_and, Handle.Pairing.indicator_and]
      rw [Bilinear.Matrix.Basic.bilinear_congr expanded left right, Bilinear.Matrix.Basic.bilinear_add,
        Bilinear.Matrix.Basic.bilinear_sub, Bilinear.Matrix.Basic.bilinear_outer, Bilinear.Matrix.Basic.bilinear_outer,
        Weighted.weighted_unit, Weighted.weighted_unit, Weighted.weighted_unit, Weighted.weighted_unit, ih]
      rfl
end Purelib.LinearAlgebra.Alternating.Handle.Pairing

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

namespace Purelib.LinearAlgebra.Alternating.Handle.Pairing

variable {n : Nat}

open Purelib.LinearAlgebra.Alternating in
/-- A right unit vector at an unused coordinate pairs to zero with every vector. -/
theorem handlePairing_right_unused (raw : List (Handle.Basic.PivotIndices n)) (values : Data.Vector Int n)
  (column : Fin n)
    (unused : column ∉ Handle.Basic.handleIndices raw) : Handle.Pairing.handlePairing raw values (Unit.unitVector
      column) = 0 := by
  induction raw with
  | nil => rfl
  | cons pair rest ih =>
      have first : pair.1 ≠ column := fun same => unused (same ▸ List.mem_cons_self)
      have last : pair.2 ≠ column := fun same => unused (same ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have tail : column ∉ Handle.Basic.handleIndices rest := fun member => unused (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ member))
      rw [Handle.Pairing.handlePairing, Unit.unitVector_apply, Unit.unitVector_apply, if_neg last, if_neg first, ih
        tail]
      ring1
end Purelib.LinearAlgebra.Alternating.Handle.Pairing

end

end
