module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Histogram
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

public section

/-! Exact singleton overlap and residual contents, retaining the original
consolidated union keys and all zero rows. No normalization is assumed. -/
namespace Purelib.Measure.Content.Overlap

open Purelib.Data.Rat

/-- Retain the key payload with weight equal to the minimum of its two original singleton masses. -/
@[expose] def overlapRow {α : Type} [DecidableEq α]
    (left right : Content α) (key : Weighted α) : Weighted α where
  item := key.item
  weight := min
    (left.measure (atomEvent key.item))
    (right.measure (atomEvent key.item))
  nonnegative := Fraction.Order.Basic.le_min
    (left.measure_nonneg (atomEvent key.item))
    (right.measure_nonneg (atomEvent key.item))

/-- Retain the key payload with the original left singleton mass minus its common minimum mass. -/
@[expose] def leftResidualRow {α : Type} [DecidableEq α]
    (left right : Content α) (key : Weighted α) : Weighted α where
  item := key.item
  weight := left.measure (atomEvent key.item) - min
    (left.measure (atomEvent key.item))
    (right.measure (atomEvent key.item))
  nonnegative := Fraction.Order.Arithmetic.sub_nonneg_direct (Fraction.Order.Basic.min_le_left _ _)

/-- Retain the key payload with the original right singleton mass minus its common minimum mass. -/
@[expose] def rightResidualRow {α : Type} [DecidableEq α]
    (left right : Content α) (key : Weighted α) : Weighted α where
  item := key.item
  weight := right.measure (atomEvent key.item) - min
    (left.measure (atomEvent key.item))
    (right.measure (atomEvent key.item))
  nonnegative := Fraction.Order.Arithmetic.sub_nonneg_direct (Fraction.Order.Basic.min_le_right _ _)

/-- Build the common content over the exact consolidated source-target keys using their singleton mass minima. -/
@[expose] def overlapContent {α : Type} [DecidableEq α] (left right : Content α) : Content α :=
  ⟨(left.radonNikodymKeys right).map (overlapRow left right)⟩

/-- Build the left residual over the same exact source-target keys after removing common singleton mass. -/
@[expose] def leftResidualContent {α : Type} [DecidableEq α] (left right : Content α) : Content α :=
  ⟨(left.radonNikodymKeys right).map (leftResidualRow left right)⟩

/-- Build the right residual over the same exact source-target keys after removing common singleton mass. -/
@[expose] def rightResidualContent {α : Type} [DecidableEq α] (left right : Content α) : Content α :=
  ⟨(left.radonNikodymKeys right).map (rightResidualRow left right)⟩

section
open Purelib.Data.Rat
/-- Common and left-residual weighted integrals on the same keys reconstruct the exact left singleton-mass sum. -/
private theorem overlap_add_leftResidual_keys {α : Type}
    [DecidableEq α] (left right : Content α)
    (value : α → Fraction.Rational) :
    ∀ keys : List (Weighted α),
      Distribution.expectationWeight
          (keys.map (overlapRow left right)) value +
        Distribution.expectationWeight
          (keys.map (leftResidualRow left right)) value =
      left.atomMassSum keys value
  | [] => by
      change (0 : Fraction.Rational) + 0 = 0
      ring1
  | key :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, Distribution.expectationWeight,
        Content.atomMassSum, overlapRow, leftResidualRow]
      calc
        min (left.measure (atomEvent key.item))
                (right.measure (atomEvent key.item)) * value key.item +
              Distribution.expectationWeight
                (remaining.map (overlapRow left right)) value +
            ((left.measure (atomEvent key.item) -
                  min (left.measure (atomEvent key.item))
                    (right.measure (atomEvent key.item))) *
                value key.item +
              Distribution.expectationWeight
                (remaining.map (leftResidualRow left right)) value) =
            (min (left.measure (atomEvent key.item))
                  (right.measure (atomEvent key.item)) * value key.item +
              (left.measure (atomEvent key.item) -
                  min (left.measure (atomEvent key.item))
                    (right.measure (atomEvent key.item))) *
                value key.item) +
              (Distribution.expectationWeight
                  (remaining.map (overlapRow left right)) value +
                Distribution.expectationWeight
                  (remaining.map (leftResidualRow left right)) value) := by
          ring1
        _ = (min (left.measure (atomEvent key.item))
                  (right.measure (atomEvent key.item)) * value key.item +
              (left.measure (atomEvent key.item) -
                  min (left.measure (atomEvent key.item))
                    (right.measure (atomEvent key.item))) *
                value key.item) +
              left.atomMassSum remaining value := by
          rw [overlap_add_leftResidual_keys left right value remaining]
        _ = left.measure (atomEvent key.item) *
              value key.item +
            left.atomMassSum remaining value := by
          ring1

/-- Common and right-residual weighted integrals on the same keys reconstruct the exact right singleton-mass sum. -/
private theorem overlap_add_rightResidual_keys {α : Type}
    [DecidableEq α] (left right : Content α)
    (value : α → Fraction.Rational) :
    ∀ keys : List (Weighted α),
      Distribution.expectationWeight
          (keys.map (overlapRow left right)) value +
        Distribution.expectationWeight
          (keys.map (rightResidualRow left right)) value =
      right.atomMassSum keys value
  | [] => by
      change (0 : Fraction.Rational) + 0 = 0
      ring1
  | key :: remaining => by
      simp only [-eq_self, -iff_self, List.map_cons, Distribution.expectationWeight,
        Content.atomMassSum, overlapRow, rightResidualRow]
      calc
        min (left.measure (atomEvent key.item))
                (right.measure (atomEvent key.item)) * value key.item +
              Distribution.expectationWeight
                (remaining.map (overlapRow left right)) value +
            ((right.measure (atomEvent key.item) -
                  min (left.measure (atomEvent key.item))
                    (right.measure (atomEvent key.item))) *
                value key.item +
              Distribution.expectationWeight
                (remaining.map (rightResidualRow left right)) value) =
            (min (left.measure (atomEvent key.item))
                  (right.measure (atomEvent key.item)) * value key.item +
              (right.measure (atomEvent key.item) -
                  min (left.measure (atomEvent key.item))
                    (right.measure (atomEvent key.item))) *
                value key.item) +
              (Distribution.expectationWeight
                  (remaining.map (overlapRow left right)) value +
                Distribution.expectationWeight
                  (remaining.map (rightResidualRow left right)) value) := by
          ring1
        _ = (min (left.measure (atomEvent key.item))
                  (right.measure (atomEvent key.item)) * value key.item +
              (right.measure (atomEvent key.item) -
                  min (left.measure (atomEvent key.item))
                    (right.measure (atomEvent key.item))) *
                value key.item) +
              right.atomMassSum remaining value := by
          rw [overlap_add_rightResidual_keys left right value remaining]
        _ = right.measure (atomEvent key.item) *
              value key.item +
            right.atomMassSum remaining value := by
          ring1

/-- The common content plus left residual reconstructs every integral of the original left content. -/
theorem overlap_integral_add_leftResidual_integral {α : Type}
    [DecidableEq α] (left right : Content α)
    (value : α → Fraction.Rational) :
    (overlapContent left right).integral value +
        (leftResidualContent left right).integral value =
      left.integral value := by
  unfold overlapContent leftResidualContent Content.integral
  change Distribution.expectationWeight
      ((left.radonNikodymKeys right).map
        (overlapRow left right)) value +
      Distribution.expectationWeight
        ((left.radonNikodymKeys right).map
          (leftResidualRow left right)) value =
    left.integral value
  rw [overlap_add_leftResidual_keys]
  exact left.atomMassSum_eq_integral value
    (left.radonNikodymKeys right)
    (left.radonNikodymKeys_noRepeated right)
    (left.payloadsCovered_radonNikodymKeys_left
      right)

/-- The common content plus right residual reconstructs every integral of the original right content. -/
theorem overlap_integral_add_rightResidual_integral {α : Type}
    [DecidableEq α] (left right : Content α)
    (value : α → Fraction.Rational) :
    (overlapContent left right).integral value +
        (rightResidualContent left right).integral value =
      right.integral value := by
  unfold overlapContent rightResidualContent Content.integral
  change Distribution.expectationWeight
      ((left.radonNikodymKeys right).map
        (overlapRow left right)) value +
      Distribution.expectationWeight
        ((left.radonNikodymKeys right).map
          (rightResidualRow left right)) value =
    right.integral value
  rw [overlap_add_rightResidual_keys]
  exact right.atomMassSum_eq_integral value
    (left.radonNikodymKeys right)
    (left.radonNikodymKeys_noRepeated right)
    (left.payloadsCovered_radonNikodymKeys_right
      right)

end

variable {α : Type} [DecidableEq α] {left right : Content α}

section
open Purelib.Data.Rat
/-- Require a retained mass to equal the original content's singleton measurement at the exact key payload. -/
@[expose, reducible] def SingletonEq (content : Content α) (key : Weighted α) (mass : Fraction.Rational) : Prop :=
  mass = content.measure (atomEvent key.item)
/-- Require the retained common mass to equal the minimum of the two retained marginal masses. -/
@[expose, reducible] def CommonEq (left right common : Fraction.Rational) : Prop := common = min left right

end

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Cache both original singleton masses and their common minimum for one exact retained key.

Every cached value carries its defining equality and nonnegativity proof. The common mass also keeps its comparisons to
the same two marginals, so residual rows can consume these exact cached readings. -/
structure MassRow (left right : Content α) where
  /-- The exact weighted key whose payload owns this cached mass row. -/ key : Weighted α
  /-- The cached original left singleton mass at the retained key payload. -/ leftMass : Fraction.Rational
  /-- The cached left mass equals its exact original singleton measurement. -/ left_eq : SingletonEq left key leftMass
  /-- The cached left singleton mass is nonnegative. -/ left_nonnegative : 0 ≤ leftMass
  /-- The cached original right singleton mass at the retained key payload. -/ rightMass : Fraction.Rational
  /-- The cached right mass equals its exact original singleton measurement. -/ right_eq : SingletonEq right key
    rightMass
  /-- The cached right singleton mass is nonnegative. -/ right_nonnegative : 0 ≤ rightMass
  /-- The cached minimum of this row's exact original left and right singleton masses. -/ common : Fraction.Rational
  /-- The cached common mass equals the minimum of this row's same retained marginal masses. -/ common_eq : CommonEq
    leftMass rightMass common
  /-- The cached common singleton mass is nonnegative. -/ common_nonnegative : 0 ≤ common
  /-- The same cached common mass is at most the cached left mass. -/ common_le_left : common ≤ leftMass
  /-- The same cached common mass is at most the cached right mass. -/ common_le_right : common ≤ rightMass

constructive_injectivity Purelib.Measure.Content.Overlap.MassRow

namespace MassRow

/-- Compute and certify the exact two singleton masses and their common minimum for the supplied original key. -/
@[expose] def ofKey (left right : Content α) (key : Weighted α) : MassRow left right :=
  let l := left.measure (atomEvent key.item)
  let r := right.measure (atomEvent key.item)
  let common := min l r
  ⟨key, l, rfl, left.measure_nonneg _, r, rfl, right.measure_nonneg _,
    common, rfl, Fraction.Order.Basic.le_min (left.measure_nonneg _) (right.measure_nonneg _),
    Fraction.Order.Basic.min_le_left _ _, Fraction.Order.Basic.min_le_right _ _⟩

/-- Read the retained key payload with its cached common weight and nonnegativity witness. -/
@[expose] def commonAtom (row : MassRow left right) : Weighted α :=
  ⟨row.key.item, row.common, row.common_nonnegative⟩
/-- Read the retained key payload with its cached left mass minus the same cached common mass. -/
@[expose] def leftAtom (row : MassRow left right) : Weighted α :=
  ⟨row.key.item, row.leftMass - row.common, Fraction.Order.Arithmetic.sub_nonneg_direct row.common_le_left⟩
/-- Read the retained key payload with its cached right mass minus the same cached common mass. -/
@[expose] def rightAtom (row : MassRow left right) : Weighted α :=
  ⟨row.key.item, row.rightMass - row.common, Fraction.Order.Arithmetic.sub_nonneg_direct row.common_le_right⟩

end MassRow

/-- Reading common atoms from the exact constructed cache rows gives the original overlap-row list. -/
theorem commonAtoms_readback (left right : Content α) :
    (keys : List (Weighted α)) →
      (keys.map (MassRow.ofKey left right)).map MassRow.commonAtom = keys.map (overlapRow left right)
  | [] => rfl
  | key :: keys => congrArg (List.cons (overlapRow left right key)) (commonAtoms_readback left right keys)

/-- Reading left residual atoms from the exact constructed cache rows gives the original left-residual-row list. -/
theorem leftAtoms_readback (left right : Content α) :
    (keys : List (Weighted α)) →
      (keys.map (MassRow.ofKey left right)).map MassRow.leftAtom = keys.map (leftResidualRow left right)
  | [] => rfl
  | key :: keys => congrArg (List.cons (leftResidualRow left right key)) (leftAtoms_readback left right keys)

/-- Reading right residual atoms from the exact constructed cache rows gives the original right-residual-row list. -/
theorem rightAtoms_readback (left right : Content α) :
    (keys : List (Weighted α)) →
      (keys.map (MassRow.ofKey left right)).map MassRow.rightAtom = keys.map (rightResidualRow left right)
  | [] => rfl
  | key :: keys => congrArg (List.cons (rightResidualRow left right key)) (rightAtoms_readback left right keys)

/-- Require the retained parent content to equal the original owner. -/
@[expose, reducible] def ParentEq (original parent : Content α) : Prop := parent = original
/-- Require the retained keys to equal the exact consolidated original left-right key list. -/
@[expose, reducible] def KeysEq (left right : Content α) (keys : List (Weighted α)) : Prop :=
  keys = left.radonNikodymKeys right
/-- Require the retained cache rows to be built from those exact keys and original content owners. -/
@[expose, reducible] def RowsEq (left right : Content α) (keys : List (Weighted α))
    (rows : List (MassRow left right)) : Prop := rows = keys.map (MassRow.ofKey left right)
/-- Require a cached content to equal its specified original construction. -/
@[expose, reducible] def ContentEq (original cached : Content α) : Prop := cached = original

set_option genInjectivity false in
/-- Retain both original content owners, their shared keys, cached mass rows and certified common/residual contents.

Defining equalities bind every cached object to the same two inputs and exact row construction. The stored common and
two residual contents retain distinct identities for reconstructing each original integral. -/
structure Comparison (left right : Content α) where
  /-- The retained original left content owner. -/ leftParent : Content α
  /-- The retained left parent equals the exact original left content. -/ leftParent_eq : ParentEq left leftParent
  /-- The retained original right content owner. -/ rightParent : Content α
  /-- The retained right parent equals the exact original right content. -/ rightParent_eq : ParentEq right rightParent
  /-- The exact retained shared finite payload keys. -/ keys : List (Weighted α)
  /-- The retained keys equal the original left-right consolidated key construction. -/ keys_eq : KeysEq left right keys
  /-- The retained cached mass rows for the same original content owners. -/ rows : List (MassRow left right)
  /-- The cached rows are built from exactly the retained shared keys. -/ rows_eq : RowsEq left right keys rows
  /-- The retained common content built from this comparison's original inputs. -/ common : Content α
  /-- The retained common object equals its exact specified minimum-mass construction. -/ common_eq : ContentEq
    (overlapContent left right) common
  /-- The retained content left after removing common singleton mass from the original left input. -/ leftResidual :
    Content α
  /-- The retained left residual equals the exact specified left-residual construction. -/ leftResidual_eq : ContentEq
    (leftResidualContent left right) leftResidual
  /-- The retained content left after removing common singleton mass from the original right input. -/ rightResidual :
    Content α
  /-- The retained right residual equals the exact specified right-residual construction. -/ rightResidual_eq :
    ContentEq (rightResidualContent left right) rightResidual

constructive_injectivity Purelib.Measure.Content.Overlap.Comparison

namespace Comparison

open Purelib.Measure in
/-- Construct one exact overlap comparison and derive all three contents from its retained cached mass rows.

Compute shared keys and rows once, then map their common and two residual atom readbacks. Keep equalities to the
original content constructions and both original parent identities. -/
@[expose] def realize (left right : Content α) : Comparison left right :=
  let keys := left.radonNikodymKeys right
  let rows := keys.map (MassRow.ofKey left right)
  let common : Content α := ⟨rows.map MassRow.commonAtom⟩
  let l : Content α := ⟨rows.map MassRow.leftAtom⟩
  let r : Content α := ⟨rows.map MassRow.rightAtom⟩
  { leftParent := left, leftParent_eq := rfl, rightParent := right, rightParent_eq := rfl
    keys := keys, keys_eq := rfl, rows := rows, rows_eq := rfl
    common := common, common_eq := congrArg Content.mk (Content.Overlap.commonAtoms_readback left right keys)
    leftResidual := l, leftResidual_eq := congrArg Content.mk (Content.Overlap.leftAtoms_readback left right keys)
    rightResidual := r, rightResidual_eq := congrArg Content.mk (Content.Overlap.rightAtoms_readback left right keys) }

variable (comparison : Comparison left right)

section
open Purelib.Data.Rat
/-- The retained comparison's common and left-residual integrals reconstruct the original left integral. -/
theorem reconstruct_left (value : α → Fraction.Rational) :
    comparison.common.integral value + comparison.leftResidual.integral value = left.integral value := by
  rw [comparison.common_eq, comparison.leftResidual_eq]
  exact overlap_integral_add_leftResidual_integral left right value

/-- The retained comparison's common and right-residual integrals reconstruct the original right integral. -/
theorem reconstruct_right (value : α → Fraction.Rational) :
    comparison.common.integral value + comparison.rightResidual.integral value = right.integral value := by
  rw [comparison.common_eq, comparison.rightResidual_eq]
  exact overlap_integral_add_rightResidual_integral left right value

end

/-- The retained comparison keys have no repeated payloads. -/
theorem keys_noRepeated : NoRepeatedPayloads comparison.keys := by
  rw [comparison.keys_eq]
  exact left.radonNikodymKeys_noRepeated right

/-- The retained comparison keys cover every original left-content payload. -/
theorem keys_cover_left : left.PayloadsCovered comparison.keys := by
  rw [comparison.keys_eq]
  exact left.payloadsCovered_radonNikodymKeys_left right

/-- The retained comparison keys cover every original right-content payload. -/
theorem keys_cover_right : right.PayloadsCovered comparison.keys := by
  rw [comparison.keys_eq]
  exact left.payloadsCovered_radonNikodymKeys_right right

end Comparison

end Purelib.Measure.Content.Overlap
