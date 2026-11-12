module

public import Purelib.Approximation.Rational.Grid.Basic
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Rat.Rounding.Nearest
import Purelib.Data.Int.Order
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.NatCast
import Purelib.Tactic.Ring

/-!
# Rational grids on the closed unit interval

The bounded node indices include both unit endpoints. Nearest rounding
retains its original upward half-integer tie convention and returns an
actual bounded index whose node is within half the same grid mesh.
-/

public section

namespace Purelib.Approximation.Rational.Grid.Unit

open Purelib.Data
open Purelib.Data.Rat
open Fraction.Order

/-- Read the rational node at a bounded index in a closed unit grid. -/
@[expose] def node (denominator : Nat) (index : Fin (denominator + 1)) : Fraction.Rational :=
  Fraction.Arithmetic.normalizedDiv (index.val : Fraction.Rational) (denominator : Fraction.Rational)

/-- Every node of a positive unit grid lies in the closed unit interval. -/
theorem node_bounds {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1)) :
    0 ≤ node denominator index ∧ node denominator index ≤ 1 := by
  have denominatorPositive := Fraction.Cast.Order.natCast_pos_direct positive
  have indexNonnegative : (0 : Fraction.Rational) ≤ (index.val : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.zero_le index.val)
  have indexUpper := Fraction.Cast.Order.natCast_le_direct (Nat.le_of_lt_succ index.isLt)
  rewrite [node, Fraction.Arithmetic.normalizedDiv_eq]
  constructor
  · exact Field.div_nonneg_direct indexNonnegative denominatorPositive.le
  · apply (Field.div_le_iff_pos denominatorPositive).mpr
    rewrite [Fraction.Field.one_mul]
    exact indexUpper

/-- Nearest rounding of a unit parameter selects an integer between zero and the grid denominator.

The same shifted floor is bounded below by the nonnegative scaled
parameter and above by the successor of the original denominator.
No clipping or alternative rounding operation is used.
-/
theorem nearestInteger_bounds (center : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) (inside : 0 ≤ center ∧ center ≤ 1) :
    0 ≤ Rounding.Nearest.nearestCoordinate ((denominator : Fraction.Rational) * center) ∧
      Rounding.Nearest.nearestCoordinate ((denominator : Fraction.Rational) * center) ≤ (denominator : Int) := by
  have denominatorPositive := Fraction.Cast.Order.natCast_pos_direct positive
  have scaledNonnegative := Arithmetic.mul_nonneg_direct denominatorPositive.le inside.1
  have scaledUpper := Arithmetic.mul_le_mul_of_nonneg_left_direct inside.2 denominatorPositive.le
  rewrite [show (denominator : Fraction.Rational) * 1 = (denominator : Fraction.Rational) by ring1] at scaledUpper
  constructor
  · apply (Rounding.Floor.intCast_le_iff_floor 0 _).mp
    exact Arithmetic.add_le_add_direct scaledNonnegative (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
  · apply Int.Order.le_of_not_lt
    intro reversed
    have successorBound : (denominator : Int) + 1 ≤
        Rounding.Floor.floor ((denominator : Fraction.Rational) * center + 1 / 2) := reversed
    have floorBound := (Rounding.Floor.intCast_le_iff_floor ((denominator : Int) + 1) _).mpr successorBound
    rewrite [Purelib.Algebra.Ring.IntCast.add, Int.cast_natCast, Int.cast_one] at floorBound
    have shiftedUpper := Arithmetic.add_le_add_right_direct scaledUpper (1 / 2 : Fraction.Rational)
    have strictUpper := Arithmetic.add_lt_add_left_direct (by decide : (1 / 2 : Fraction.Rational) < 1)
      (denominator : Fraction.Rational)
    exact (not_lt_of_ge floorBound) (shiftedUpper.trans_lt strictUpper)

/-- The original selected nearest integer is unchanged by its bounded natural readback. -/
theorem nearestInteger_toNat_cast (center : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) (inside : 0 ≤ center ∧ center ≤ 1) :
    ((Rounding.Nearest.nearestCoordinate ((denominator : Fraction.Rational) * center)).toNat : Int) =
      Rounding.Nearest.nearestCoordinate ((denominator : Fraction.Rational) * center) := by
  have nonnegative := (nearestInteger_bounds center positive inside).1
  cases selected : Rounding.Nearest.nearestCoordinate ((denominator : Fraction.Rational) * center) with
  | ofNat value => rfl
  | negSucc value =>
      rewrite [selected] at nonnegative
      cases nonnegative

/-- Compute the bounded nearest node index of a unit parameter in a positive rational grid.

The original nearest integer is read as a natural number with its exact
nonnegative identity. Its upper bound certifies the same retained finite
index, including both endpoints and upward midpoint ties.
-/
@[expose] def nearestIndex (center : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) (inside : 0 ≤ center ∧ center ≤ 1) : Fin (denominator + 1) :=
  ⟨(Rounding.Nearest.nearestCoordinate ((denominator : Fraction.Rational) * center)).toNat, by
    apply Nat.lt_succ_of_le
    apply Int.Order.natCast_le_iff.mp
    rewrite [nearestInteger_toNat_cast center positive inside]
    exact (nearestInteger_bounds center positive inside).2⟩

/-- The bounded nearest index retains the same integer selected by the original rounding operation. -/
theorem nearestIndex_intCast (center : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) (inside : 0 ≤ center ∧ center ≤ 1) :
    ((nearestIndex center positive inside).val : Int) =
      Rounding.Nearest.nearestCoordinate ((denominator : Fraction.Rational) * center) :=
  nearestInteger_toNat_cast center positive inside

/-- The selected bounded node is exactly the original nearest grid coordinate. -/
theorem nearestIndex_node (center : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) (inside : 0 ≤ center ∧ center ≤ 1) :
    node denominator (nearestIndex center positive inside) = Basic.gridCoordinate center denominator := by
  rewrite [node, Basic.gridCoordinate, Fraction.Arithmetic.normalizedMul_eq]
  apply congrArg (fun numerator : Fraction.Rational => Fraction.Arithmetic.normalizedDiv numerator denominator)
  rewrite [← Int.cast_natCast, nearestIndex_intCast center positive inside]
  rfl

/-- Every unit parameter lies within the half-mesh of its same selected bounded node.

The original nearest-coordinate bounds are translated around that
retained node. The weak bounds include upward midpoint ties without
changing the original selected integer.
-/
theorem nearestIndex_covers (center : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) (inside : 0 ≤ center ∧ center ≤ 1) :
    node denominator (nearestIndex center positive inside) - (1 / 2 : Fraction.Rational) / denominator ≤ center ∧
      center ≤ node denominator (nearestIndex center positive inside) +
        (1 / 2 : Fraction.Rational) / denominator := by
  rewrite [nearestIndex_node center positive inside]
  have bounds := Basic.gridCoordinate_bounds center positive
  constructor
  · have translated := Arithmetic.add_le_add_right_direct bounds.2 (-((1 / 2 : Fraction.Rational) / denominator))
    calc
      Basic.gridCoordinate center denominator - (1 / 2 : Fraction.Rational) / denominator ≤
        (center + (1 / 2 : Fraction.Rational) / denominator) -
          (1 / 2 : Fraction.Rational) / denominator := translated
      _ = center := by ring1
  · have translated := Arithmetic.add_le_add_right_direct bounds.1.le ((1 / 2 : Fraction.Rational) / denominator)
    calc
      center = (center - (1 / 2 : Fraction.Rational) / denominator) +
        (1 / 2 : Fraction.Rational) / denominator := by ring1
      _ ≤ Basic.gridCoordinate center denominator + (1 / 2 : Fraction.Rational) / denominator := translated

/-- Multiplying a unit-grid node by its positive denominator recovers its same bounded natural index. -/
theorem node_scaled {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1)) :
    node denominator index * (denominator : Fraction.Rational) = (index.val : Fraction.Rational) := by
  rewrite [node, Fraction.Arithmetic.normalizedDiv_eq]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (Fraction.Cast.Order.natCast_pos_direct positive).ne'

/-- The first bounded unit-grid node is exactly zero. -/
theorem node_zero {denominator : Nat} (index : Fin (denominator + 1)) (first : index.val = 0) :
    node denominator index = 0 := by
  rewrite [node, Fraction.Arithmetic.normalizedDiv_eq, first]
  exact Fraction.Field.zero_div_direct _

/-- The last bounded node of a positive unit grid is exactly one. -/
theorem node_one {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1))
    (last : index.val = denominator) : node denominator index = 1 := by
  rewrite [node, Fraction.Arithmetic.normalizedDiv_eq, last]
  exact Fraction.Field.mul_inv_cancel _ (Fraction.Cast.Order.natCast_pos_direct positive).ne'

/-- The grid half-mesh is paid by both endpoint half-distance caps at every original bounded node.

At a unit endpoint the corresponding cap is one. Every other node has
at least one grid spacing to that endpoint, so its half-distance cap
dominates the same half-mesh without modifying any node.
-/
theorem node_halfMesh_caps {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1)) :
    (1 / 2 : Fraction.Rational) / denominator ≤
        (if node denominator index = 0 then 1 else node denominator index / 2) ∧
      (1 / 2 : Fraction.Rational) / denominator ≤
        (if node denominator index = 1 then 1 else (1 - node denominator index) / 2) := by
  have denominatorPositive := Fraction.Cast.Order.natCast_pos_direct positive
  have oneLeDenominator : (1 : Fraction.Rational) ≤ (denominator : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct positive
  have halfMeshAtMostOne : (1 / 2 : Fraction.Rational) / denominator ≤ 1 := by
    apply (Field.div_le_iff_pos denominatorPositive).mpr
    rewrite [Fraction.Field.one_mul]
    exact (by decide : (1 / 2 : Fraction.Rational) ≤ 1).trans oneLeDenominator
  have halfMeshScaled := Fraction.Field.div_mul_cancel_of_ne (1 / 2 : Fraction.Rational)
    (denominator : Fraction.Rational) denominatorPositive.ne'
  constructor
  · by_cases first : node denominator index = 0
    · rewrite [if_pos first]
      exact halfMeshAtMostOne
    · rewrite [if_neg first]
      have indexPositive : 0 < index.val := Nat.zero_lt_of_ne_zero (fun zero => first (node_zero index zero))
      have oneLeIndex : (1 : Fraction.Rational) ≤ (index.val : Fraction.Rational) :=
        Fraction.Cast.Order.natCast_le_direct indexPositive
      apply (Field.le_div_iff_pos (by decide : (0 : Fraction.Rational) < 2)).mpr
      apply Arithmetic.le_of_mul_le_mul_right_direct (c := (denominator : Fraction.Rational)) _ denominatorPositive
      calc
        ((1 / 2 : Fraction.Rational) / denominator * 2) * denominator =
          ((1 / 2 : Fraction.Rational) / denominator * denominator) * 2 := by ring1
        _ = 1 := by rewrite [halfMeshScaled]; decide +kernel
        _ ≤ (index.val : Fraction.Rational) := oneLeIndex
        _ = node denominator index * denominator := (node_scaled positive index).symm
  · by_cases last : node denominator index = 1
    · rewrite [if_pos last]
      exact halfMeshAtMostOne
    · rewrite [if_neg last]
      have indexLess : index.val < denominator := Nat.lt_of_le_of_ne
        (Nat.le_of_lt_succ index.isLt) (fun equal => last (node_one positive index equal))
      have successorLe : ((index.val + 1 : Nat) : Fraction.Rational) ≤ (denominator : Fraction.Rational) :=
        Fraction.Cast.Order.natCast_le_direct indexLess
      rewrite [Purelib.Algebra.NatCast.add, Nat.cast_one] at successorLe
      apply (Field.le_div_iff_pos (by decide : (0 : Fraction.Rational) < 2)).mpr
      apply Arithmetic.le_of_mul_le_mul_right_direct (c := (denominator : Fraction.Rational)) _ denominatorPositive
      have translated := Arithmetic.sub_le_sub_right_direct successorLe (index.val : Fraction.Rational)
      calc
        ((1 / 2 : Fraction.Rational) / denominator * 2) * denominator =
          ((1 / 2 : Fraction.Rational) / denominator * denominator) * 2 := by ring1
        _ = 1 := by rewrite [halfMeshScaled]; decide +kernel
        _ = ((index.val : Fraction.Rational) + 1) - index.val := by ring1
        _ ≤ (denominator : Fraction.Rational) - index.val := translated
        _ = (1 - node denominator index) * denominator := by
          rewrite [sub_mul, Fraction.Field.one_mul, node_scaled positive index]
          rfl

/-- Compute the midpoint between two consecutive original bounded unit-grid nodes. -/
@[expose] def midpoint (denominator : Nat) (index : Fin denominator) : Fraction.Rational :=
  node denominator index.castSucc + (1 / 2 : Fraction.Rational) / denominator

/-- The original grid midpoint is half a mesh below its same right-hand node. -/
theorem midpoint_eq_right {denominator : Nat} (positive : 0 < denominator) (index : Fin denominator) :
    midpoint denominator index = node denominator index.succ - (1 / 2 : Fraction.Rational) / denominator := by
  have denominatorPositive := Fraction.Cast.Order.natCast_pos_direct positive
  have halfScaled := Fraction.Field.div_mul_cancel_of_ne (1 / 2 : Fraction.Rational)
    (denominator : Fraction.Rational) denominatorPositive.ne'
  apply Fraction.Field.mul_right_cancel_of_ne denominatorPositive.ne'
  rewrite [midpoint, add_mul, sub_mul, node_scaled positive index.castSucc,
    node_scaled positive index.succ, halfScaled]
  change (index.val : Fraction.Rational) + 1 / 2 = ((index.val + 1 : Nat) : Fraction.Rational) - 1 / 2
  rewrite [Purelib.Algebra.NatCast.add, Nat.cast_one]
  calc
    (index.val : Fraction.Rational) + 1 / 2 = index.val + (1 - 1 / 2 : Fraction.Rational) :=
      congrArg (fun value : Fraction.Rational => index.val + value) (by decide +kernel)
    _ = (index.val : Fraction.Rational) + 1 - 1 / 2 := by ring1

/-- Every consecutive-node midpoint lies in the original closed unit interval. -/
theorem midpoint_bounds {denominator : Nat} (positive : 0 < denominator) (index : Fin denominator) :
    0 ≤ midpoint denominator index ∧ midpoint denominator index ≤ 1 := by
  have halfNonnegative := (Field.div_pos_direct (by decide : (0 : Fraction.Rational) < 1 / 2)
    (Fraction.Cast.Order.natCast_pos_direct positive)).le
  constructor
  · exact Arithmetic.add_le_add_direct (node_bounds positive index.castSucc).1 halfNonnegative
  · rewrite [midpoint_eq_right positive index]
    calc
      node denominator index.succ - (1 / 2 : Fraction.Rational) / denominator ≤
        node denominator index.succ - 0 := Arithmetic.sub_le_sub_left_direct halfNonnegative _
      _ = node denominator index.succ := by ring1
      _ ≤ 1 := (node_bounds positive index.succ).2

/-- The original consecutive-node midpoint lies within half a mesh of both retained nodes. -/
theorem midpoint_near_nodes {denominator : Nat} (positive : 0 < denominator) (index : Fin denominator) :
    (node denominator index.castSucc - (1 / 2 : Fraction.Rational) / denominator ≤ midpoint denominator index ∧
      midpoint denominator index ≤ node denominator index.castSucc + (1 / 2 : Fraction.Rational) / denominator) ∧
    (node denominator index.succ - (1 / 2 : Fraction.Rational) / denominator ≤ midpoint denominator index ∧
      midpoint denominator index ≤ node denominator index.succ + (1 / 2 : Fraction.Rational) / denominator) := by
  have halfNonnegative := (Field.div_pos_direct (by decide : (0 : Fraction.Rational) < 1 / 2)
    (Fraction.Cast.Order.natCast_pos_direct positive)).le
  have around (center : Fraction.Rational) : center - (1 / 2 : Fraction.Rational) / denominator ≤
      center + (1 / 2 : Fraction.Rational) / denominator := by
    calc
      center - (1 / 2 : Fraction.Rational) / denominator ≤ center - 0 :=
        Arithmetic.sub_le_sub_left_direct halfNonnegative center
      _ = center + 0 := by ring1
      _ ≤ center + (1 / 2 : Fraction.Rational) / denominator := Arithmetic.add_le_add_direct le_rfl halfNonnegative
  constructor
  · exact ⟨around _, le_rfl⟩
  · rewrite [midpoint_eq_right positive index]
    exact ⟨le_rfl, around _⟩

/-- Half the original mesh of a positive unit grid is strictly positive. -/
theorem halfMesh_positive {denominator : Nat} (positive : 0 < denominator) :
    0 < (1 / 2 : Fraction.Rational) / denominator :=
  Field.div_pos_direct (by decide) (Fraction.Cast.Order.natCast_pos_direct positive)

/-- Compute the closed unit-grid cell centered at a bounded node and cut at the neighboring midpoints.

Half the original mesh supplies both distances from the retained node.
Clipping the displayed endpoints to zero and one includes the first
and last endpoint cells while keeping the same bounded node inside.
-/
@[expose] def cell {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1)) :
    Interval.Bounds :=
  let center := node denominator index
  let halfMesh := (1 / 2 : Fraction.Rational) / denominator
  let nonnegative := (halfMesh_positive positive).le
  let bounds := node_bounds positive index
  have lower : max 0 (center - halfMesh) ≤ center := Basic.max_le bounds.1 (by
    calc
      center - halfMesh ≤ center - 0 := Arithmetic.sub_le_sub_left_direct nonnegative center
      _ = center := by ring1)
  have upper : center ≤ min 1 (center + halfMesh) := Basic.le_min bounds.2 (by
    calc
      center = center + 0 := by ring1
      _ ≤ center + halfMesh := Arithmetic.add_le_add_direct le_rfl nonnegative)
  ⟨max 0 (center - halfMesh), min 1 (center + halfMesh), lower.trans upper⟩

/-- Containment in a unit-grid cell is exactly unit containment and proximity within half the original mesh. -/
theorem cell_contains_iff {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1))
    (parameter : Fraction.Rational) :
    (cell positive index).Contains parameter ↔
      (0 ≤ parameter ∧ parameter ≤ 1) ∧
        (node denominator index - (1 / 2 : Fraction.Rational) / denominator ≤ parameter ∧
          parameter ≤ node denominator index + (1 / 2 : Fraction.Rational) / denominator) := by
  change (max 0 (node denominator index - (1 / 2 : Fraction.Rational) / denominator) ≤ parameter ∧
    parameter ≤ min 1 (node denominator index + (1 / 2 : Fraction.Rational) / denominator)) ↔ _
  constructor
  · intro inside
    exact ⟨⟨(Basic.le_max_left _ _).trans inside.1, inside.2.trans (Basic.min_le_left _ _)⟩,
      (Basic.le_max_right _ _).trans inside.1, inside.2.trans (Basic.min_le_right _ _)⟩
  · intro ⟨unit, near⟩
    exact ⟨Basic.max_le unit.1 near.1, Basic.le_min unit.2 near.2⟩

/-- Every positive unit-grid cell is proper and lies in the original closed unit interval. -/
theorem cell_bounds {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1)) :
    0 ≤ (cell positive index).lower ∧ (cell positive index).lower < (cell positive index).upper ∧
      (cell positive index).upper ≤ 1 := by
  let center := node denominator index
  let halfMesh := (1 / 2 : Fraction.Rational) / denominator
  have halfPositive : 0 < halfMesh := Field.div_pos_direct (by decide)
    (Fraction.Cast.Order.natCast_pos_direct positive)
  have bounds := node_bounds positive index
  have lower : center - halfMesh < center := by
    calc
      center - halfMesh < center - 0 := Arithmetic.sub_lt_sub_left_direct halfPositive center
      _ = center := by ring1
  have upper : center < center + halfMesh := by
    calc
      center = center + 0 := by ring1
      _ < center + halfMesh := Arithmetic.add_lt_add_left_direct halfPositive center
  exact ⟨Basic.le_max_left _ _,
    Basic.lt_min (Basic.max_lt (by decide) (lower.trans_le bounds.2))
      (Basic.max_lt (bounds.1.trans_lt upper) (lower.trans upper)), Basic.min_le_left _ _⟩

/-- The first bounded unit-grid cell starts at the original endpoint zero. -/
theorem cell_lower_zero {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1))
    (first : index.val = 0) : (cell positive index).lower = 0 := by
  change max 0 (node denominator index - (1 / 2 : Fraction.Rational) / denominator) = 0
  rewrite [node_zero index first]
  apply Basic.max_eq_left
  have halfNonnegative := (Field.div_pos_direct (by decide : (0 : Fraction.Rational) < 1 / 2)
    (Fraction.Cast.Order.natCast_pos_direct positive)).le
  calc
    0 - (1 / 2 : Fraction.Rational) / denominator ≤ 0 - 0 :=
      Arithmetic.sub_le_sub_left_direct halfNonnegative 0
    _ = 0 := by ring1

/-- The last bounded unit-grid cell ends at the original endpoint one. -/
theorem cell_upper_one {denominator : Nat} (positive : 0 < denominator) (index : Fin (denominator + 1))
    (last : index.val = denominator) : (cell positive index).upper = 1 := by
  change min 1 (node denominator index + (1 / 2 : Fraction.Rational) / denominator) = 1
  rewrite [node_one positive index last]
  apply Basic.min_eq_left
  have halfNonnegative := (Field.div_pos_direct (by decide : (0 : Fraction.Rational) < 1 / 2)
    (Fraction.Cast.Order.natCast_pos_direct positive)).le
  calc
    (1 : Fraction.Rational) = 1 + 0 := by ring1
    _ ≤ 1 + (1 / 2 : Fraction.Rational) / denominator := Arithmetic.add_le_add_direct le_rfl halfNonnegative

/-- A unit-grid cell's right endpoint is the same midpoint shared with its consecutive cell. -/
theorem cell_upper_midpoint {denominator : Nat} (positive : 0 < denominator) (index : Fin denominator) :
    (cell positive index.castSucc).upper = midpoint denominator index :=
  Basic.min_eq_right (midpoint_bounds positive index).2

/-- A consecutive unit-grid cell's left endpoint is the same retained common midpoint. -/
theorem cell_lower_midpoint {denominator : Nat} (positive : 0 < denominator) (index : Fin denominator) :
    (cell positive index.succ).lower = midpoint denominator index := by
  change max 0 (node denominator index.succ - (1 / 2 : Fraction.Rational) / denominator) = _
  rewrite [← midpoint_eq_right positive index]
  exact Basic.max_eq_right (midpoint_bounds positive index).1

/-- Consecutive original unit-grid cells meet at their same retained endpoint. -/
theorem cell_adjacent {denominator : Nat} (positive : 0 < denominator) (index : Fin denominator) :
    (cell positive index.castSucc).upper = (cell positive index.succ).lower :=
  (cell_upper_midpoint positive index).trans (cell_lower_midpoint positive index).symm

/-- Every original unit parameter belongs to the cell at its same computed bounded nearest-node index. -/
theorem nearestIndex_cell_contains (parameter : Fraction.Rational) {denominator : Nat}
    (positive : 0 < denominator) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (cell positive (nearestIndex parameter positive inside)).Contains parameter :=
  (cell_contains_iff positive _ parameter).mpr ⟨inside, nearestIndex_covers parameter positive inside⟩

end Purelib.Approximation.Rational.Grid.Unit
