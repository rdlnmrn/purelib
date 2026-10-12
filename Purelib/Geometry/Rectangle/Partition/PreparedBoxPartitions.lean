module
public import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Content
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Separation

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Topology.PreparedObservationSurface
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Constructive dyadic partitions of checked surface boxes

Repeated quartering produces a finite covering list of proper rectangles with
disjoint interiors.  Exact area is preserved and squared diameters decay by
four at each level.  The partition retains the actual observation
box endpoints at every refinement level.
-/

namespace Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Geometry
open Purelib.Geometry.Rational.Box

/-- Rational coordinates for the dyadic box partition. -/
public abbrev Coordinate := Fraction.Rational
/-- Gaussian rational points in the box. -/
public abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- An axis-aligned rational box with ordered endpoints. -/
public abbrev Box := Rational.Box

/-- Two equal rational halves sum to the original value.

The denominator is the nonzero rational two. Multiplication by that denominator
recovers the supplied scalar exactly. -/
private theorem half_add_half (value : Coordinate) : value / 2 + value / 2 = value := by
  calc
    _ = value / 2 * 2 := by ring1
    _ = value := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- Midpoint written using the interval width, avoiding an unrelated origin. -/
@[expose] public def midpoint (lower upper : Coordinate) : Coordinate
  := lower + (upper - lower) / 2

/-- The midpoint lies between ordered endpoints.

The interval endpoints are weakly ordered. The nonnegative half-width places
the retained midpoint inside those same endpoints. -/
public theorem midpoint_between {lower upper : Coordinate} (ordered : lower <= upper) :
    lower <= midpoint lower upper ∧ midpoint lower upper <= upper := by
  have halfNonnegative := Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) (by decide : (0 : Coordinate) <= 2)
  refine ⟨le_add_of_nonneg_right halfNonnegative, ?_⟩
  calc
    midpoint lower upper <= midpoint lower upper + (upper - lower) / 2 :=
      le_add_of_nonneg_right halfNonnegative
    _ = lower + ((upper - lower) / 2 + (upper - lower) / 2) := by unfold midpoint; ring1
    _ = upper := by rw [half_add_half]; ring1

/-- The lower endpoint of the selected half interval. -/
@[expose] public def halfLower (lower upper : Coordinate) (high :
  Bool) : Coordinate :=
  if high then Geometry.Rectangle.Partition.PreparedBoxPartitions.midpoint lower upper else lower

/-- The upper endpoint of the selected half interval. -/
@[expose] public def halfUpper (lower upper : Coordinate) (high :
  Bool) : Coordinate :=
  if high then upper else Geometry.Rectangle.Partition.PreparedBoxPartitions.midpoint lower upper

/-- Each selected half has half the original interval width.

Either Boolean branch selects one of the two original midpoint halves. Both
branches retain exactly half the original endpoint difference. -/
public theorem half_width (lower upper : Coordinate) (high : Bool) :
    halfUpper lower upper high - halfLower lower upper high = (upper - lower) / 2 := by
  cases high with
  | false =>
      change (lower + (upper - lower) / 2) - lower = (upper - lower) / 2
      ring1
  | true =>
      change upper - (lower + (upper - lower) / 2) = (upper - lower) / 2
      calc
        _ = (upper - lower) - (upper - lower) / 2 := by ring1
        _ = ((upper - lower) / 2 + (upper - lower) / 2) - (upper - lower) / 2 := by
          rw [half_add_half]
        _ = _ := by ring1

/-- Halving preserves weakly ordered endpoints.

The original endpoint inequality makes the half-width nonnegative. Recovering
endpoint order from that difference certifies the selected half. -/
public theorem half_ordered {lower upper : Coordinate} (ordered : lower <= upper) (high : Bool) :
    halfLower lower upper high <= halfUpper lower upper high := by
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  rw [half_width]
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.sub_nonneg_direct ordered) (by decide)

/-- Each half lies inside the original interval.

Each Boolean branch keeps one original endpoint and the same midpoint. The
retained endpoint inequalities therefore hold for either selection. -/
public theorem half_refines {lower upper : Coordinate} (ordered : lower <= upper) (high : Bool) :
    lower <= halfLower lower upper high ∧ halfUpper lower upper high <= upper := by
  cases high
  · exact ⟨le_rfl, (midpoint_between ordered).2⟩
  · exact ⟨(midpoint_between ordered).1, le_rfl⟩

/-- Halving a proper interval preserves strict endpoint order.

Strict endpoint order makes the half-width positive. Both selected halves
consequently retain strict endpoint order. -/
public theorem half_proper {lower upper : Coordinate} (ordered : lower < upper) (high : Bool) :
    halfLower lower upper high < halfUpper lower upper high := by
  apply Fraction.Order.Arithmetic.lt_of_sub_pos_direct
  rw [half_width]
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.sub_pos_direct ordered) (by decide)

/-- Select a half by one rational comparison, including boundary points. -/
@[expose] public def highHalf (lower upper point : Coordinate) : Bool
  := decide (Geometry.Rectangle.Partition.PreparedBoxPartitions.midpoint lower upper < point)

/-- The comparison-selected half contains the bounded query point.

The comparison selects the upper half exactly when the query lies strictly
above the midpoint. Equality at the midpoint remains in the lower half. -/
public theorem highHalf_contains {lower upper point : Coordinate}
    (inside : lower <= point ∧ point <= upper) :
    halfLower lower upper (highHalf lower upper point) <= point ∧
      point <= halfUpper lower upper (highHalf lower upper point) := by
  unfold highHalf
  by_cases high : midpoint lower upper < point
  · have selected : decide (midpoint lower upper < point) = true := decide_eq_true high
    rewrite [selected]
    change midpoint lower upper ≤ point ∧ point ≤ upper
    exact ⟨high.le, inside.2⟩
  · have selected : decide (midpoint lower upper < point) = false := decide_eq_false high
    rewrite [selected]
    change lower ≤ point ∧ point ≤ midpoint lower upper
    exact ⟨inside.1, le_of_not_gt high⟩

/-- A quadrant, with two executable bits selecting its horizontal/vertical half.

The two Boolean selections retain the four half endpoints. Their order
certificates come from the original box endpoints. -/
@[expose] public def child (box : Box) (xHigh yHigh : Bool) :
  Box where
  xLower := Geometry.Rectangle.Partition.PreparedBoxPartitions.halfLower box.xLower box.xUpper xHigh
  xUpper := Geometry.Rectangle.Partition.PreparedBoxPartitions.halfUpper box.xLower box.xUpper xHigh
  yLower := Geometry.Rectangle.Partition.PreparedBoxPartitions.halfLower box.yLower box.yUpper yHigh
  yUpper := Geometry.Rectangle.Partition.PreparedBoxPartitions.halfUpper box.yLower box.yUpper yHigh
  x_valid := half_ordered box.x_valid xHigh
  y_valid := half_ordered box.y_valid yHigh

/-- Each quadrant box refines its parent box.

The selected horizontal and vertical halves retain their parent endpoint
bounds. These four bounds give refinement of the same stored box. -/
public theorem child_refines (box : Box) (xHigh yHigh : Bool) : (child box xHigh yHigh).Refines box :=
  ⟨(half_refines box.x_valid xHigh).1, (half_refines box.x_valid xHigh).2,
    (half_refines box.y_valid yHigh).1, (half_refines box.y_valid yHigh).2⟩

/-- Each quadrant of a proper box is proper.

Both original coordinate intervals are proper. Strict order survives each
chosen half independently. -/
public theorem child_proper {box : Box} (proper : box.Proper) (xHigh yHigh : Bool) :
    (child box xHigh yHigh).Proper :=
  ⟨half_proper proper.1 xHigh, half_proper proper.2 yHigh⟩

/-- The quadrant selected by the two midpoint comparisons contains the point.

The original point lies between both pairs of box endpoints. Each midpoint
comparison selects a half containing that same coordinate. -/
public theorem child_contains {box : Box} {point : Gaussian} (inside : box.Contains point) :
    (child box (highHalf box.xLower box.xUpper point.re)
      (highHalf box.yLower box.yUpper point.im)).Contains point :=
  let horizontal := highHalf_contains ⟨inside.1, inside.2.1⟩
  let vertical := highHalf_contains inside.2.2
  ⟨horizontal.1, horizontal.2, vertical.1, vertical.2⟩

/-- Each quadrant has half the parent's horizontal width.

The horizontal selection has half the original horizontal width. The vertical
selection leaves that equality unchanged. -/
public theorem child_widthX (box : Box) (xHigh yHigh : Bool) :
    (child box xHigh yHigh).widthX = box.widthX / 2 := half_width _ _ _

/-- Each quadrant has half the parent's vertical width.

The vertical selection has half the original vertical width. The horizontal
selection leaves that equality unchanged. -/
public theorem child_widthY (box : Box) (xHigh yHigh : Bool) :
    (child box xHigh yHigh).widthY = box.widthY / 2 := half_width _ _ _

/-- Each quadrant has one quarter of the parent's area.

Both retained widths are halved. Multiplying them divides the original rational
area by four. -/
public theorem child_content (box : Box) (xHigh yHigh : Bool) :
    Content.boxContent (child box xHigh yHigh) = Content.boxContent box / 4 := by
  unfold Content.boxContent
  rw [child_widthX, child_widthY]
  calc
    box.widthX / 2 * (box.widthY / 2) = (box.widthX * box.widthY) * ((2 : Coordinate)⁻¹) ^ 2 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = _ := by rw [show ((2 : Coordinate)⁻¹) ^ 2 = (4 : Coordinate)⁻¹ by decide]; rfl

/-- Each quadrant has one quarter of the parent's squared diagonal.

Each retained width is halved before squaring. Their squared sum is therefore
one quarter of the original squared diagonal. -/
public theorem child_diagonalSq (box : Box) (xHigh yHigh : Bool) :
    (child box xHigh yHigh).diagonalSq = box.diagonalSq / 4 := by
  change (child box xHigh yHigh).widthX ^ 2 + (child box xHigh yHigh).widthY ^ 2 = _
  rw [child_widthX, child_widthY]
  calc
    (box.widthX / 2) ^ 2 + (box.widthY / 2) ^ 2 =
        (box.widthX ^ 2 + box.widthY ^ 2) * ((2 : Coordinate)⁻¹) ^ 2 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = _ := by rw [show ((2 : Coordinate)⁻¹) ^ 2 = (4 : Coordinate)⁻¹ by decide]; rfl

/-- Left and right quadrants have separated interiors.

The left child ends at the same midpoint where the right child begins. The
independent vertical selections do not affect that horizontal separation. -/
public theorem child_horizontal_separated (box : Box) (leftY rightY : Bool) :
    (child box false leftY).InteriorSeparated (child box true rightY) := Or.inl le_rfl

/-- Lower and upper quadrants have separated interiors.

The lower child ends at the same midpoint where the upper child begins. The
independent horizontal selections do not affect that vertical separation. -/
public theorem child_vertical_separated (box : Box) (lowerX upperX : Bool) :
    (child box lowerX false).InteriorSeparated (child box upperX true) := Or.inr (Or.inr (Or.inl le_rfl))

/-- A complete finite dyadic cover in a fixed quadrant traversal order.

The recursion concatenates the four original quadrants in bottom-left, bottom-
right, top-left and top-right order. Every level retains that same finite
traversal. -/
@[expose] public def cells : Nat -> Box -> List
  Box
  | 0, box => [box]
  | depth + 1, box =>
      Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.cells depth
        (Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.child box false false) ++
        Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.cells depth
        (Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.child box true false) ++
        Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.cells depth
          (Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.child box false true) ++
          Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.cells depth
          (Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.child box true true)

/-- Depth n produces exactly four to the power n leaf boxes.

Each recursive step concatenates four depth-matched child lists. Their lengths
therefore multiply the original leaf count by four. -/
public theorem cells_length (depth : Nat) (box : Box) : (cells depth box).length = 4 ^ depth := by
  induction depth generalizing box with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [cells, Append.length_append, inductionHypothesis, pow_succ]
      omega

/-- Membership at the next depth is membership below one of the four children.

The existential Boolean pair identifies one of the four retained children.
Membership is transported through the original concatenation order. -/
public theorem mem_cells_succ {depth : Nat} {box small : Box} :
    small ∈ cells (depth + 1) box ↔
      ∃ xHigh yHigh : Bool, small ∈ cells depth (child box xHigh yHigh) := by
  constructor
  · intro member
    rcases Membership.mem_append.mp member with first | fourth
    · rcases Membership.mem_append.mp first with first | third
      · rcases Membership.mem_append.mp first with first | second
        · exact ⟨false, false, first⟩
        · exact ⟨true, false, second⟩
      · exact ⟨false, true, third⟩
    · exact ⟨true, true, fourth⟩
  · rintro ⟨xHigh, yHigh, member⟩
    cases xHigh <;> cases yHigh
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))
    · exact List.mem_append_left _ (List.mem_append_right _ member)
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member))
    · exact List.mem_append_right _ member

/-- Every leaf box refines the original box.

The base leaf is the original box. Each recursive leaf refines its selected
child, whose endpoints already refine the parent. -/
public theorem cells_refine (depth : Nat) (box : Box) {small : Box} (member : small ∈ cells depth box) :
    small.Refines box := by
  induction depth generalizing box with
  | zero =>
    have equal := Membership.mem_singleton.mp member; subst small; exact Rational.Box.refines_refl _
  | succ depth inductionHypothesis =>
      rcases mem_cells_succ.mp member with ⟨xHigh, yHigh, member⟩
      exact (inductionHypothesis _ member).trans (child_refines box xHigh yHigh)

/-- Every leaf below a proper box is proper.

The original box has strict endpoint order in both coordinates. Each selected
quadrant and every descendant retain those two inequalities. -/
public theorem cells_proper (depth : Nat) {box : Box} (proper : box.Proper)
    {small : Box} (member : small ∈ cells depth box) : small.Proper := by
  induction depth generalizing box with
  | zero => have equal := Membership.mem_singleton.mp member; subst small; exact proper
  | succ depth inductionHypothesis =>
      rcases mem_cells_succ.mp member with ⟨xHigh, yHigh, member⟩
      exact inductionHypothesis (child_proper proper xHigh yHigh) member

/-- Concatenate two separated lists when all cross pairs are separated.

Each list has pairwise separated interiors, and every left-to-right cross pair
is separated. These facts certify the same concatenated list. -/
private theorem pairwise_append {left right : List Box}
    (leftSeparated : left.Pairwise Rational.Box.InteriorSeparated)
    (rightSeparated : right.Pairwise Rational.Box.InteriorSeparated)
    (cross : forall first, first ∈ left -> forall second, second ∈ right -> first.InteriorSeparated second) :
    (left ++ right).Pairwise Rational.Box.InteriorSeparated := by
  induction leftSeparated with
  | nil => exact rightSeparated
  | @cons first rest firstSeparated restSeparated inductionHypothesis =>
      refine .cons ?_ (inductionHypothesis (fun first member second secondMember =>
        cross first (List.mem_cons_of_mem _ member) second secondMember))
      intro second member
      rcases Membership.mem_append.mp member with inRest | inRight
      · exact firstSeparated second inRest
      · exact cross first (List.mem_cons_self) second inRight

/-- Leaves of interior-separated parent boxes remain interior-separated.

The original parents have separated interiors. Refinement of both retained
leaves preserves their separation. -/
private theorem separated_leaves {first second : Box}
    (separated : first.InteriorSeparated second) (depth : Nat)
    {firstSmall secondSmall : Box}
    (firstMember : firstSmall ∈ cells depth first) (secondMember : secondSmall ∈ cells depth second) :
    firstSmall.InteriorSeparated secondSmall :=
  separated.of_refines (cells_refine depth first firstMember) (cells_refine depth second secondMember)

/-- Shared edges are allowed, but no two leaf interiors overlap.

Horizontal and vertical midpoint cuts separate the original child interiors.
Refinement and explicit cross-pair membership preserve that separation through
the full list. -/
public theorem cells_interiorSeparated (depth : Nat) (box : Box) :
    (cells depth box).Pairwise Rational.Box.InteriorSeparated := by
  induction depth generalizing box with
  | zero => exact .cons (fun _ member => (List.not_mem_nil member).elim) .nil
  | succ depth inductionHypothesis =>
      have bottom : (cells depth (child box false false) ++ cells depth (child box true false)).Pairwise
          Rational.Box.InteriorSeparated :=
        pairwise_append (inductionHypothesis _) (inductionHypothesis _)
          (fun _ firstMember _ secondMember =>
            separated_leaves (child_horizontal_separated box false false) depth firstMember secondMember)
      have top : (cells depth (child box false true) ++ cells depth (child box true true)).Pairwise
          Rational.Box.InteriorSeparated :=
        pairwise_append (inductionHypothesis _) (inductionHypothesis _)
          (fun _ firstMember _ secondMember =>
            separated_leaves (child_horizontal_separated box true true) depth firstMember secondMember)
      rw [cells, Append.append_assoc (cells depth (child box false false) ++ cells depth (child box true false))]
      apply pairwise_append bottom top
      intro first firstMember second secondMember
      rcases Membership.mem_append.mp firstMember with firstMember | firstMember <;>
        rcases Membership.mem_append.mp secondMember with secondMember | secondMember
      · exact separated_leaves (child_vertical_separated box false false) depth firstMember secondMember
      · exact separated_leaves (child_vertical_separated box false true) depth firstMember secondMember
      · exact separated_leaves (child_vertical_separated box true false) depth firstMember secondMember
      · exact separated_leaves (child_vertical_separated box true true) depth firstMember secondMember

/-- An executable covering witness, selected by two comparisons at each level.

Each level uses the two original midpoint comparisons to select a child. The
recursion follows that child without constructing a different covering list. -/
@[expose] public def locate (depth : Nat) (box : Box) (point
  : Gaussian) : Box :=
  match depth with
  | 0 => box
  | depth + 1 => Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.locate depth
      (Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.child box
        (Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.highHalf box.xLower box.xUpper point.re)
        (Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.highHalf box.yLower box.yUpper point.im)) point

/-- The recursive locator returns a member of the leaf list.

The locator selects one of the four retained children at every step. Its
recursively returned box belongs to the corresponding subtree list. -/
public theorem locate_mem (depth : Nat) (box : Box) (point : Gaussian) : locate depth box point ∈ cells depth box := by
  induction depth generalizing box with
  | zero => exact List.mem_singleton_self _
  | succ depth inductionHypothesis =>
      exact mem_cells_succ.mpr ⟨_, _, inductionHypothesis _⟩

/-- The recursive locator preserves containment of the query point.

Both midpoint comparisons preserve containment in the selected child. Repeating
that argument retains the original bounded point at the final depth. -/
public theorem locate_contains (depth : Nat) {box : Box} {point : Gaussian} (inside : box.Contains point) :
    (locate depth box point).Contains point := by
  induction depth generalizing box with
  | zero => exact inside
  | succ depth inductionHypothesis => exact inductionHypothesis (child_contains inside)

/-- Dividing the initial value by four advances the quarter-radius sequence one
step.

Both sides divide the same supplied rational by the corresponding finite power
of four. Their extra factor is the same nonzero denominator four. -/
private theorem quarterRadius_step (value : Coordinate) (depth : Nat) :
    Geometric.Basic.quarterRadius (value / 4) depth =
      Geometric.Basic.quarterRadius value (depth + 1) := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow,
    Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- The exact per-leaf squared diameter includes the full refinement depth.

The original squared diagonal is divided by four at every quadrant step. The
depth-zero leaf retains the original diagonal exactly. -/
public theorem cells_diagonalSq (depth : Nat) (box : Box) {small : Box} (member : small ∈ cells depth box) :
    small.diagonalSq = Geometric.Basic.quarterRadius box.diagonalSq depth := by
  induction depth generalizing box with
  | zero =>
      have equal := Membership.mem_singleton.mp member
      subst small
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, _root_.mul_one]
      exact Eq.refl _
  | succ depth inductionHypothesis =>
      rcases mem_cells_succ.mp member with ⟨xHigh, yHigh, member⟩
      rw [inductionHypothesis _ member, child_diagonalSq, quarterRadius_step]

/-- A finite structural sum, also used for exact area and error budgets.

The recursion accumulates each supplied scalar in the original box-list order.
Empty lists contribute zero. -/
@[expose] public def sumCells (value : Box ->
  Coordinate) : List
  Box ->
  Coordinate
  | [] => 0
  | box :: rest => value box + Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions.sumCells value rest

/-- The finite cell sum is additive over list concatenation.

The structural sum follows the supplied list order. Associativity of rational
addition combines the two retained partial sums. -/
public theorem sumCells_append (value : Box -> Coordinate) (left right : List Box) :
    sumCells value (left ++ right) = sumCells value left + sumCells value right := by
  induction left with
  | nil => simp only [List.nil_append, sumCells]; ring1
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, sumCells, inductionHypothesis]
      ring1

/-- Total area is unchanged even though there are `4^depth` leaves.

Each original quadrant has one quarter of its parent area. The four depth-
matched subtree sums recover that area exactly. -/
public theorem cells_content (depth : Nat) (box : Box) :
    sumCells Content.boxContent (cells depth box) = Content.boxContent box := by
  induction depth generalizing box with
  | zero => change _ + 0 = _; ring1
  | succ depth inductionHypothesis =>
      rw [cells]
      simp only [sumCells_append, inductionHypothesis, child_content]
      calc
        _ = (Content.boxContent box / 4) * 4 := by ring1
        _ = _ := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- A common right scalar factors out of the cell sum.

The factor is fixed across the supplied list. Scalar distributivity transports
the original structural accumulation without changing its entries. -/
public theorem sumCells_mul_right (value : Box -> Coordinate) (boxes : List Box) (factor : Coordinate) :
    sumCells (fun box => value box * factor) boxes = sumCells value boxes * factor := by
  induction boxes with
  | nil => change 0 = 0 * factor; ring1
  | cons box rest inductionHypothesis =>
      simp only [sumCells, inductionHypothesis]
      ring1

/-- A common left scalar factors out of the cell sum.

The factor is fixed across the supplied list. Scalar distributivity transports
the original structural accumulation without changing its entries. -/
public theorem sumCells_mul_left (value : Box -> Coordinate) (boxes : List Box) (factor : Coordinate) :
    sumCells (fun box => factor * value box) boxes = factor * sumCells value boxes := by
  induction boxes with
  | nil => change 0 = factor * 0; ring1
  | cons box rest inductionHypothesis =>
      simp only [sumCells, inductionHypothesis]
      ring1

/-- Pointwise equality on the actual cell list preserves its sum.

Equality is required only for entries belonging to the retained list. List
induction specializes that evidence at each head and preserves the unchanged
tail. -/
public theorem sumCells_congr (left right : Box -> Coordinate) (boxes : List Box)
    (equal : forall box, box ∈ boxes -> left box = right box) : sumCells left boxes = sumCells right boxes := by
  induction boxes with
  | nil => rfl
  | cons box rest inductionHypothesis =>
      rw [sumCells, sumCells, equal box List.mem_cons_self,
        inductionHypothesis (fun box member => equal box (List.mem_cons_of_mem _ member))]

/-- Pointwise upper bounds on the actual cell list bound its sum.

The supplied bound applies to every retained list entry. Rational addition
transports the specialized head bound and the recursive tail bound. -/
public theorem sumCells_mono (left right : Box -> Coordinate) (boxes : List Box)
    (bound : forall box, box ∈ boxes -> left box <= right box) : sumCells left boxes <= sumCells right boxes := by
  induction boxes with
  | nil => exact le_rfl
  | cons box rest inductionHypothesis =>
      exact Fraction.Order.Arithmetic.add_le_add_direct (bound box List.mem_cons_self)
        (inductionHypothesis (fun box member => bound box (List.mem_cons_of_mem _ member)))

/-- The structural cell sum equals the sum over the list's finite indices.

Each finite index reads the same retained list entry. The successor equation of
the finite sum agrees with the original head-and-tail accumulation. -/
public theorem sumCells_eq_sumFin (value : Box -> Coordinate) (boxes : List Box) :
    sumCells value boxes = FiniteSum.Fin.sumFin
      (fun index : Fin boxes.length => value boxes[index.val]) := by
  induction boxes with
  | nil => rfl
  | cons box rest inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ]
      change value box + sumCells value rest = value box + FiniteSum.Fin.sumFin
        (fun index : Fin rest.length => value rest[index.val])
      rw [inductionHypothesis]

/-- An explicit square-root-free upper bound for the Euclidean diameter. -/
@[expose] public def span (box : Box) : Coordinate := box.widthX +
  box.widthY

/-- The sum of the two box widths is nonnegative.

Both widths come from weakly ordered endpoints. Adding their nonnegative
differences gives the displayed width bound. -/
public theorem span_nonnegative (box : Box) : 0 <= span box :=
  add_nonneg box.widthX_nonneg box.widthY_nonneg

/-- The squared diagonal is bounded by the square of the width sum.

The two widths are nonnegative, so their cross product is nonnegative. Adding
twice that product gives the square of the same width sum. -/
public theorem diagonalSq_le_span_sq (box : Box) : box.diagonalSq <= span box ^ 2 := by
  calc
    box.diagonalSq <= box.diagonalSq + 2 * (box.widthX * box.widthY) :=
      le_add_of_nonneg_right (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct box.widthX_nonneg box.widthY_nonneg))
    _ = span box ^ 2 := by
      change (box.widthX ^ 2 + box.widthY ^ 2) + 2 * (box.widthX * box.widthY) = _
      unfold span
      ring1

/-- Each quadrant has half the parent's width sum.

The selected child halves both coordinate widths. Adding those retained widths
halves their original sum. -/
public theorem child_span (box : Box) (xHigh yHigh : Bool) : span (child box xHigh yHigh) = span box / 2 := by
  unfold span
  rw [child_widthX, child_widthY]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- The width sum of a leaf is the parent width sum times one half to the depth.

Each quadrant halves both widths. Repeated refinement therefore multiplies the
original width sum by the displayed finite power. -/
public theorem cells_span (depth : Nat) (box : Box) {small : Box} (member : small ∈ cells depth box) :
    span small = span box * (1 / 2 : Coordinate) ^ depth := by
  induction depth generalizing box with
  | zero => have equal := Membership.mem_singleton.mp member; subst small; rw [pow_zero, mul_one]
  | succ depth inductionHypothesis =>
      rcases mem_cells_succ.mp member with ⟨xHigh, yHigh, member⟩
      rw [inductionHypothesis _ member, child_span, pow_succ]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1

/-- The area-weighted local mesh width decays despite the growing leaf count.

Every leaf has the same depth-dependent width factor relative to the parent.
Factoring it out leaves the exact original total area. -/
public theorem totalAreaSpan_eq (depth : Nat) (box : Box) :
    sumCells (fun small => Content.boxContent small * span small) (cells depth box) =
      Content.boxContent box * span box * (1 / 2 : Coordinate) ^ depth := by
  calc
    _ = sumCells (fun small => Content.boxContent small *
        (span box * (1 / 2 : Coordinate) ^ depth)) (cells depth box) :=
      sumCells_congr _ _ _ (fun small member => by rw [cells_span depth box member])
    _ = _ := by rw [sumCells_mul_right, cells_content]; ring1

/-- Two spatial quarterings per request index give the standard quarter-rate total
error.

There are `16^index` rectangles, already accounted for in the area-weighted
finite sum. The two quarterings retain the original request index and scale. -/
public theorem totalAreaSpan_quarterRate (index : Nat) (box : Box) (scale : Coordinate) :
    sumCells (fun small => scale * (Content.boxContent small * span small)) (cells (2 * index) box) =
      Geometric.Basic.quarterRadius (scale * (Content.boxContent box * span box)) index := by
  rw [sumCells_mul_left, totalAreaSpan_eq, Geometric.Basic.quarterRadius_eq_mul_pow,
    pow_mul, show (1 / 2 : Coordinate) ^ 2 = 1 / 4 by decide]
  ring1

/-- A local area-times-width error bound gives the full global rate without
assuming that the number of faces stays fixed.

The supplied error is bounded on each actual retained leaf. Summing those
specialized bounds gives the original area-weighted quarter-radius allowance. -/
public theorem totalError_le_quarterRate (index : Nat) (box : Box) (scale : Coordinate)
    (error : Box -> Coordinate)
    (localBound : forall small, small ∈ cells (2 * index) box ->
      error small <= scale * (Content.boxContent small * span small)) :
    sumCells error (cells (2 * index) box) <=
      Geometric.Basic.quarterRadius (scale * (Content.boxContent box * span box)) index :=
  (sumCells_mono _ _ _ localBound).trans_eq (totalAreaSpan_quarterRate index box scale)

end Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
