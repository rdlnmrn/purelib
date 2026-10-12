module
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Evaluation
import Purelib.LinearAlgebra.Alternating.Handle.Basic
public import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Alternating.Handle.UnitPairing
public import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Vector.Unit
import Mathlib.Algebra.Ring.Int.Defs
public import Purelib.LinearAlgebra.Alternating.Reduction.CycleRows

section
public section

/-!
# Intersection of the computed integral cycle rows

The actual cycle change of basis has the same signed unit-handle form as
the reduced matrix. These finite integer identities do not assume a
geometric genus or a preassigned ordering of branch labels.
-/

namespace Purelib.LinearAlgebra.Alternating.NormalForm

open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.Vector

variable {n : Nat} {matrix : SquareMatrix.IntegralMatrix n} {raw : List (Handle.Basic.PivotIndices n)}

/-- Pairing two retained cycle rows gives the handle pairing of their coordinate units. -/
theorem cycleRows_pairing (normal : NormalForm matrix raw) (first last : Fin n) :
    Bilinear.Integral.pairing matrix (normal.reduction.cycleRows first) (normal.reduction.cycleRows last) =
      Handle.Pairing.handlePairing raw (Unit.unitVector first) (Unit.unitVector last) := by
  rw [normal.reduction.cycleRows_apply, normal.reduction.cycleRows_apply,
    normal.pairing, normal.reduction.dualForward_dualBackward, normal.reduction.dualForward_dualBackward]

/-- The original form on two retained cycle rows equals the corresponding signed handle entry. -/
theorem cycleRows_entry (normal : NormalForm matrix raw) (first last : Fin n) :
    Bilinear.Integral.pairing matrix (normal.reduction.cycleRows first) (normal.reduction.cycleRows last) =
      Handle.Basic.handleEntry raw first last := open Purelib.LinearAlgebra in by
  rw [normal.cycleRows_pairing, ← Handle.Pairing.handleEntry_pairing]
  simp only [Int.cast_id]
  have same := Bilinear.Matrix.Basic.bilinear_congr (K := Int)
    (fun row column => (SquareMatrix.matrixOfFn_apply (Handle.Basic.handleEntry raw) row column).symm)
    (Unit.unitVector first) (Unit.unitVector last)
  rw [same]
  change Bilinear.Integral.pairing (SquareMatrix.matrixOfFn (Handle.Basic.handleEntry raw)) (Unit.unitVector
    first) (Unit.unitVector last) = _
  rw [Bilinear.Integral.pairing_left_unit, Unit.weighted_right_unit, SquareMatrix.matrixOfFn_apply]

/-- The normal form retains a duplicate-free list of pivot pairs. -/
theorem pivots_nodup (normal : NormalForm matrix raw) : raw.Nodup := by
  have finite : ∀ (pairs : List (Handle.Basic.PivotIndices n)), (Handle.Basic.handleIndices pairs).Nodup → pairs.Nodup
    := by
    intro pairs
    induction pairs with
    | nil => intro _; exact List.nodup_nil
    | cons head rest ih =>
        intro unique
        obtain ⟨firstClear, remaining⟩ := List.pairwise_cons.mp unique
        obtain ⟨_, tailUnique⟩ := List.pairwise_cons.mp remaining
        exact List.pairwise_cons.mpr ⟨fun pair member equal => firstClear pair.1
          (List.mem_cons_of_mem _ (Handle.Basic.handle_coordinate_mem pair member pair.1 List.mem_cons_self))
          (congrArg Prod.fst equal), ih tailUnique⟩
  exact finite raw normal.disjoint

/-- Take the negative last cycle row as the first oriented handle weight vector.

This fixes the orientation while preserving the original retained cycle row entries. -/
@[expose] def firstWeights (normal : NormalForm matrix raw) (pair : Handle.Basic.PivotIndices n) :
    Data.Vector Int n := Data.Vector.Basic.vectorOfFn fun index => -normal.reduction.cycleRows pair.2 index

/-- Take the first cycle row as the last oriented handle weight vector. -/
@[expose] def lastWeights (normal : NormalForm matrix raw) (pair : Handle.Basic.PivotIndices n) :
    Data.Vector Int n := normal.reduction.cycleRows pair.1

open Purelib.LinearAlgebra.Alternating
/-- Two first handle weight vectors pair to zero. -/
theorem first_first (normal : NormalForm matrix raw)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Bilinear.Integral.pairing matrix (normal.firstWeights first) (normal.firstWeights last) = 0 := open
      Purelib.LinearAlgebra.Alternating in by
  rw [firstWeights, firstWeights,
    Bilinear.Integral.pairing_neg_left, Bilinear.Integral.pairing_neg_right, neg_neg, normal.cycleRows_pairing,
    (Handle.UnitPairing.handlePairing_unit_handle raw normal.disjoint first firstMember (Unit.unitVector last.2)).2,
    Unit.unitVector_apply, if_neg (Handle.Basic.handle_first_ne_last normal.disjoint first last firstMember lastMember),
      neg_zero]

/-- Two last handle weight vectors pair to zero. -/
theorem last_last (normal : NormalForm matrix raw)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Bilinear.Integral.pairing matrix (normal.lastWeights first) (normal.lastWeights last) = 0 := open
      Purelib.LinearAlgebra.Alternating in by
  rw [lastWeights, lastWeights, normal.cycleRows_pairing,
    (Handle.UnitPairing.handlePairing_unit_handle raw normal.disjoint first firstMember (Unit.unitVector last.1)).1,
    Unit.unitVector_apply, if_neg (Ne.symm (Handle.Basic.handle_first_ne_last normal.disjoint last first lastMember
      firstMember))]

/-- First and last handle weight vectors pair to the equality indicator of their retained handles. -/
theorem first_last (normal : NormalForm matrix raw)
    (first last : Handle.Basic.PivotIndices n) (firstMember : first ∈ raw) (lastMember : last ∈ raw) :
    Bilinear.Integral.pairing matrix (normal.firstWeights first) (normal.lastWeights last) = if first = last then 1 else
      0 := open Purelib.LinearAlgebra.Alternating in by
  rw [firstWeights, lastWeights,
    Bilinear.Integral.pairing_neg_left, normal.cycleRows_pairing,
    (Handle.UnitPairing.handlePairing_unit_handle raw normal.disjoint first firstMember (Unit.unitVector last.1)).2,
    neg_neg, Unit.unitVector_apply]
  by_cases same : first = last
  · rw [if_pos same, if_pos (congrArg Prod.fst same)]
  · rw [if_neg same, if_neg (fun equal =>
      same ((Handle.Basic.handle_first_eq_first normal.disjoint first last firstMember lastMember).mp equal))]

end Purelib.LinearAlgebra.Alternating.NormalForm

end
