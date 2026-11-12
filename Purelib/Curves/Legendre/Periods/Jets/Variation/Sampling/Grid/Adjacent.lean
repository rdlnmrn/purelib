module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Grid
import Purelib.Approximation.AccuracyRequest
import Purelib.Tactic.QuotientFreeOmega

/-! # Exact local requests between consecutive retained positive grid nodes

Both node coordinates are original bounded occurrences. Their literal
Gaussian difference is the original rational-width increment, so their
local joint AccuracyRequest is the SAME original common grid request.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian

/-- Read the actual next positive-node occurrence with its retained original strict finite bound. -/
@[expose] def gridNextIndex (count : Nat) (index : Fin count) (inside : index.val + 1 < count) : Fin count :=
  ⟨index.val + 1, inside⟩

/-- The literal Gaussian difference of the SAME two retained consecutive positive-node offsets. -/
@[expose] def gridPositiveIncrement (count : Nat) (index : Fin count) (inside : index.val + 1 < count)
    (direction : Canonical) : Canonical :=
  gridOffset count (gridNextIndex count index inside).succ direction - gridOffset count index.succ direction

/-- The SAME two consecutive positive-node offsets differ by the literal original grid increment. -/
theorem gridPositiveOffset_difference (count : Nat) (index : Fin count) (inside : index.val + 1 < count)
    (direction : Canonical) :
    gridOffset count (gridNextIndex count index inside).succ direction - gridOffset count index.succ direction =
      gridIncrement count direction := by
  have previous : (gridNextIndex count index inside).castSucc = index.succ := Fin.ext rfl
  exact (congrArg (fun previous : Fin (count + 1) =>
    gridOffset count (gridNextIndex count index inside).succ direction - gridOffset count previous direction)
      previous).symm.trans (gridOffset_difference count (gridNextIndex count index inside) direction)

/-- The actual consecutive positive-node difference is nonzero for the SAME moving Gaussian direction. -/
theorem gridPositiveDifference_nonzero (count : Nat) (positive : 0 < count) (index : Fin count)
    (inside : index.val + 1 < count) (direction : Canonical) (moving : direction ≠ 0) :
    gridOffset count (gridNextIndex count index inside).succ direction - gridOffset count index.succ direction ≠ 0 :=
  fun zero => gridIncrement_nonzero count positive direction moving
    ((gridPositiveOffset_difference count index inside direction).symm.trans zero)

/-- The actual local difference request is the SAME whole original common grid AccuracyRequest.

The equality includes the positive proof field through the original
AccuracyRequest extensional law. No observation or preparation is assigned
a different tolerance, and no final model/sample comparison is supplied.
-/
theorem gridPositiveRequest_eq (count : Nat) (positive : 0 < count) (index : Fin count)
    (inside : index.val + 1 < count) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest) :
    spatial.minimum (incrementRequest
      (gridOffset count (gridNextIndex count index inside).succ direction - gridOffset count index.succ direction)
      (gridPositiveDifference_nonzero count positive index inside direction moving)) =
    spatial.minimum (incrementRequest (gridIncrement count direction)
      (gridIncrement_nonzero count positive direction moving)) := by
  apply AccuracyRequest.eq_of_tolerance_eq
  exact congrArg (fun increment : Canonical => min spatial.tolerance (Data.Gaussian.Norm.Basic.normSq increment ^ 2))
    (gridPositiveOffset_difference count index inside direction)

/-- Select the first actual positive-node occurrence of one ordered positive-positive grid edge. -/
@[expose] def gridPairIndex (count : Nat) (edge : Fin (count - 1)) : Fin count :=
  ⟨edge.val, Nat.lt_of_lt_of_le edge.isLt (Nat.sub_le count 1)⟩

/-- The next positive occurrence exists for every actual edge, including the empty zero/one-node cases. -/
theorem gridPairFollowing (count : Nat) (edge : Fin (count - 1)) :
    (gridPairIndex count edge).val + 1 < count := by
  have bound := edge.isLt
  change edge.val + 1 < count
  omega0

/-- The first original node position is the literal ordered edge position. -/
theorem gridPairIndex_val (count : Nat) (edge : Fin (count - 1)) :
    (gridPairIndex count edge).val = edge.val := rfl

/-- The second original node position is the literal successor of the ordered edge position. -/
theorem gridPairNext_val (count : Nat) (edge : Fin (count - 1)) :
    (gridNextIndex count (gridPairIndex count edge) (gridPairFollowing count edge)).val = edge.val + 1 := rfl

/-- The local positive-node difference has at most the original whole-direction quadrance. -/
theorem gridPositiveIncrement_normSq_le (count : Nat) (positive : 0 < count) (index : Fin count)
    (inside : index.val + 1 < count) (direction : Canonical) :
    Norm.Basic.normSq (gridPositiveIncrement count index inside direction) ≤
      Norm.Basic.normSq direction :=
  (congrArg Norm.Basic.normSq (gridPositiveOffset_difference count index inside direction)).trans_le
    ((gridIncrement_normSq_le count positive index direction).trans
      (gridOffset_normSq_le count positive index.succ direction))

end Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling

end
