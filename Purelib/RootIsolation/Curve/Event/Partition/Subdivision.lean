module

import Purelib.Data.List.Membership
import Purelib.Data.List.Fold
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Cut
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Guard
public import Purelib.RootIsolation.Curve.Event.Partition.Guard
public import Purelib.RootIsolation.Sturm.Count.Basic
import Purelib.RootIsolation.Sturm.Event.Guard
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

namespace Purelib.RootIsolation.Curve.Event.Partition

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RationalFunctions
open Purelib.RootIsolation

set_option genInjectivity false in
/-- One common safe split.  Its cut avoids every member of every reduced
chain used by the aligned classifiers.

The retained rational cut lies strictly inside its original proper cell.
Its common-guard nonvanishing and two child-width bounds concern that same
cut, event polynomial, curve, box and original interval. -/
public structure SafeSplit
    (event : Dense.Basic.RationalPolynomial) (curve : Curve.RationalCurve) (box : Box)
      (cell : Interval.Proper.Cell) where
  /-- The retained rational cut avoiding the common event guard. -/ cut : Fraction.Rational
  /-- The cut lies strictly above the original cell's lower endpoint. -/ lowerLt : cell.interval.lower < cut
  /-- The cut lies strictly below the original cell's upper endpoint. -/ upperLt : cut < cell.interval.upper
  /-- The common guard does not vanish at the retained cut. -/ guardNonzero : (commonGuard event curve box).eval cut ≠ 0
  /-- The left child width is strictly less than two thirds of the original width. -/ leftContracts :
    cut - cell.interval.lower <
      (2 / 3 : Fraction.Rational) * (Data.Rat.Interval.Bounds.width cell.interval)
  /-- The right child width is strictly less than two thirds of the original width. -/ rightContracts :
    cell.interval.upper - cut <
      (2 / 3 : Fraction.Rational) * (Data.Rat.Interval.Bounds.width cell.interval)

constructive_injectivity SafeSplit

namespace SafeSplit

/-- The proper left child of the original cell at the retained safe cut. -/
@[expose] public def leftCell
    {event : Dense.Basic.RationalPolynomial} {curve : Curve.RationalCurve} {box : Box}
      {cell : Interval.Proper.Cell}
    (split : SafeSplit event curve box cell) : Interval.Proper.Cell :=
  cell.left split.cut split.lowerLt

/-- The proper right child of the original cell at the retained safe cut. -/
@[expose] public def rightCell
    {event : Dense.Basic.RationalPolynomial} {curve : Curve.RationalCurve} {box : Box}
      {cell : Interval.Proper.Cell}
    (split : SafeSplit event curve box cell) : Interval.Proper.Cell :=
  cell.right split.cut split.upperLt

/-- The safe cut avoids the original main event polynomial's reduced-chain guard.

The main event guard is the first retained factor of the common
product. Nonvanishing of that same product at the stored cut supplies
nonvanishing of its original event factor. -/
public theorem avoidsEventGuard
    {event : Dense.Basic.RationalPolynomial} {curve : Curve.RationalCurve} {box : Box}
      {cell : Interval.Proper.Cell}
    (split : SafeSplit event curve box cell) :
    (Sturm.Event.polynomialEventGuard event).eval split.cut ≠ 0 := by
  apply eval_ne_zero_of_eventGuard (event := event) (curve := curve) (box := box)
  · exact List.mem_cons_self
  · exact split.guardNonzero

/-- The safe cut avoids every retained active box-condition polynomial's reduced-chain guard.

The supplied original active-condition occurrence identifies its
mapped guard factor in the common product. Product nonvanishing at the
retained cut then certifies that exact factor. -/
public theorem avoidsActiveConditionGuard
    {event : Dense.Basic.RationalPolynomial} {curve : Curve.RationalCurve} {box : Box}
      {cell : Interval.Proper.Cell}
    (split : SafeSplit event curve box cell) {condition : Dense.Basic.RationalPolynomial}
    (member : condition ∈
      Curve.Box.activeConditionPolynomials curve box) :
    (Sturm.Event.polynomialEventGuard condition).eval split.cut ≠ 0 := by
  apply eval_ne_zero_of_eventGuard (event := event) (curve := curve) (box := box)
  · exact List.mem_cons_of_mem _ (Data.List.Map.mem_map.mpr ⟨condition, member, rfl⟩)
  · exact split.guardNonzero

end SafeSplit

/-- Search the central third for a cut avoiding all retained event guards.

The returned rational cut retains strict endpoint bounds, common-guard nonvanishing and both two-thirds contraction
certificates. -/
@[expose] public def safeSplit
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) (cell : Interval.Proper.Cell) :
    SafeSplit event curve box cell := by
  let guard := commonGuard event curve box
  let cut := Dense.Rational.Nonzero.Search.Central.centralSearchValue guard
    guard.natDegree cell.proper
    (commonGuard_isZero_false eventNonzero curve box) (Nat.le_refl _)
  have specification :=
    Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec guard
      guard.natDegree cell.proper
      (commonGuard_isZero_false eventNonzero curve box) (Nat.le_refl _)
  have contraction :=
    Dense.Rational.Nonzero.Search.Central.centralSearchValue_contraction guard
      guard.natDegree cell.proper
      (commonGuard_isZero_false eventNonzero curve box) (Nat.le_refl _)
  exact
    { cut := cut
      lowerLt := specification.2.1
      upperLt := specification.2.2
      guardNonzero := specification.1
      leftContracts := contraction.1
      rightContracts := contraction.2 }

set_option genInjectivity false in
/-- Finite common binary subdivision syntax.

Each terminal constructor stores its original proper cell. Every split
retains the actual common safe-cut certificate and its two ordered child
trees, without replacing the event, curve or box owners. -/
public inductive Subdivision
    (event : Dense.Basic.RationalPolynomial) (curve : Curve.RationalCurve) (box : Box)
      where
  /-- A retained proper parameter cell at a leaf of the finite common subdivision. -/ | leaf (cell :
    Interval.Proper.Cell)
  /-- An original cell with its checked safe cut and two retained child subdivisions. -/ | split (cell :
    Interval.Proper.Cell) (data : SafeSplit event curve box cell)
      (left right : Purelib.RootIsolation.Curve.Event.Partition.Subdivision event curve box)

constructive_injectivity Subdivision

namespace Subdivision

/-- Build a finite common binary subdivision by repeatedly computing safe central-third cuts.

The natural depth fixes the number of rounds and the original event, curve and box determine every common guard. -/
@[expose] public def build
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box) :
    Nat → Interval.Proper.Cell → Subdivision event curve box
  | 0, cell => .leaf cell
  | depth + 1, cell =>
      let data := safeSplit event eventNonzero curve box cell
      .split cell data
        (Purelib.RootIsolation.Curve.Event.Partition.Subdivision.build event eventNonzero curve box depth data.leftCell)
        (Purelib.RootIsolation.Curve.Event.Partition.Subdivision.build event eventNonzero curve box depth
          data.rightCell)

/-- Read the retained leaf cells in left-to-right order from the finite subdivision.

A terminal cell contributes its single original occurrence. A split
concatenates its two retained child readbacks in their original order
and does not recompute any cut or child tree. -/
@[expose] public def leaves {event : Dense.Basic.RationalPolynomial} {curve : Curve.RationalCurve} {box :
  Box} :
    Subdivision event curve box → List Interval.Proper.Cell
  | .leaf cell => [cell]
  | .split _ _ left right => left.leaves ++ right.leaves

/-- Every leaf of the constructed common subdivision refines the original root cell.

The original leaf occurrence selects one retained child at each split.
Its child-to-root refinement composes with the recursively supplied
leaf refinement; zero depth identifies the original cell. -/
public theorem build_leaf_refines
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box)
    (depth : Nat) (root : Interval.Proper.Cell) {leaf : Interval.Proper.Cell}
    (member : leaf ∈
      (Subdivision.build event eventNonzero curve box depth root).leaves) :
    leaf.interval.Refines root.interval := by
  induction depth generalizing root with
  | zero =>
      change leaf ∈ [root] at member
      have sameCell := Data.List.Membership.mem_singleton.mp member
      cases sameCell
      exact ⟨le_rfl, le_rfl⟩
  | succ depth inductionHypothesis =>
      let data := safeSplit event eventNonzero curve box root
      change leaf ∈
        (Subdivision.build event eventNonzero curve box depth data.leftCell).leaves ++
          (Subdivision.build event eventNonzero curve box depth data.rightCell).leaves
        at member
      have childMember := Data.List.Membership.mem_append.mp member
      rcases childMember with leftMember | rightMember
      · have leafChild := inductionHypothesis data.leftCell leftMember
        have childRoot := Data.Rat.Interval.Bounds.leftChild_refines root.interval data.cut
          data.lowerLt.le data.upperLt.le
        exact ⟨childRoot.1.trans leafChild.1,
          leafChild.2.trans childRoot.2⟩
      · have leafChild := inductionHypothesis data.rightCell rightMember
        have childRoot := Data.Rat.Interval.Bounds.rightChild_refines root.interval data.cut
          data.lowerLt.le data.upperLt.le
        exact ⟨childRoot.1.trans leafChild.1,
          leafChild.2.trans childRoot.2⟩

/-- At depth `n`, each constructed leaf width is at most `(2/3)^n` times the original width.

Every retained safe cut bounds each original child width by two
thirds of the original width. The same positive contraction power
transports the finite recursive leaf bound at the requested depth. -/
public theorem build_leaf_width_le
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box)
    (depth : Nat) (root : Interval.Proper.Cell) {leaf : Interval.Proper.Cell}
    (member : leaf ∈
      (Subdivision.build event eventNonzero curve box depth root).leaves) :
    (Data.Rat.Interval.Bounds.width leaf.interval) ≤
      (2 / 3 : Fraction.Rational) ^ depth * (Data.Rat.Interval.Bounds.width root.interval) := by
  induction depth generalizing root with
  | zero =>
      change leaf ∈ [root] at member
      have sameCell := Data.List.Membership.mem_singleton.mp member
      cases sameCell
      change Data.Rat.Interval.Bounds.width leaf.interval ≤
        (1 : Fraction.Rational) * Data.Rat.Interval.Bounds.width leaf.interval
      have identity : (1 : Fraction.Rational) * Data.Rat.Interval.Bounds.width leaf.interval =
          Data.Rat.Interval.Bounds.width leaf.interval := by
        rw [Fraction.Field.mul_comm]
        exact Fraction.Field.mul_one_direct _
      exact le_of_eq identity.symm
  | succ depth inductionHypothesis =>
      let data := safeSplit event eventNonzero curve box root
      change leaf ∈
        (Subdivision.build event eventNonzero curve box depth data.leftCell).leaves ++
          (Subdivision.build event eventNonzero curve box depth data.rightCell).leaves
        at member
      have childMember := Data.List.Membership.mem_append.mp member
      have powerPositive : 0 < (2 / 3 : Fraction.Rational) ^ depth :=
        Fraction.Order.Arithmetic.pow_pos_direct (by decide) depth
      rcases childMember with leftMember | rightMember
      · exact (calc
          (Data.Rat.Interval.Bounds.width leaf.interval) ≤
              (2 / 3 : Fraction.Rational) ^ depth * (Data.Rat.Interval.Bounds.width data.leftCell.interval) :=
            inductionHypothesis data.leftCell leftMember
          _ < (2 / 3 : Fraction.Rational) ^ depth *
                ((2 / 3 : Fraction.Rational) * (Data.Rat.Interval.Bounds.width root.interval)) :=
            Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              powerPositive data.leftContracts
          _ = (2 / 3 : Fraction.Rational) ^ Nat.succ depth *
                (Data.Rat.Interval.Bounds.width root.interval) := by
            rw [pow_succ]
            ring1
        ).le
      · exact (calc
          (Data.Rat.Interval.Bounds.width leaf.interval) ≤
              (2 / 3 : Fraction.Rational) ^ depth * (Data.Rat.Interval.Bounds.width data.rightCell.interval) :=
            inductionHypothesis data.rightCell rightMember
          _ < (2 / 3 : Fraction.Rational) ^ depth *
                ((2 / 3 : Fraction.Rational) * (Data.Rat.Interval.Bounds.width root.interval)) :=
            Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              powerPositive data.rightContracts
          _ = (2 / 3 : Fraction.Rational) ^ Nat.succ depth *
                (Data.Rat.Interval.Bounds.width root.interval) := by
            rw [pow_succ]
            ring1
        ).le

/-- The root doubled Sturm count is the exact integer sum over every original subdivision leaf.

The original safe cut identifies the shared endpoint of its two
retained cells. Integer endpoint additivity and the exact ordered leaf
sum fold compose that finite count decomposition at every depth. -/
public theorem build_cellEventCount_sum
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box)
    (depth : Nat) (root : Interval.Proper.Cell) :
    Sturm.Count.Basic.cellCount2 event root =
      ((Subdivision.build event eventNonzero curve box depth root).leaves.map
        (Sturm.Count.Basic.cellCount2 event)).sum := by
  induction depth generalizing root with
  | zero =>
      change Sturm.Count.Basic.cellCount2 event root =
        Sturm.Count.Basic.cellCount2 event root + 0
      exact (Int.add_zero _).symm
  | succ depth inductionHypothesis =>
      let data := safeSplit event eventNonzero curve box root
      have splitCount : Sturm.Count.Basic.cellCount2 event root =
          Sturm.Count.Basic.cellCount2 event data.leftCell +
            Sturm.Count.Basic.cellCount2 event data.rightCell := by
        unfold Sturm.Count.Basic.cellCount2
        change Sturm.Count.Basic.sturmRootCount2 event root.interval.lower root.interval.upper =
          Sturm.Count.Basic.sturmRootCount2 event root.interval.lower data.cut +
            Sturm.Count.Basic.sturmRootCount2 event data.cut root.interval.upper
        exact Sturm.Count.Basic.sturmRootCount2_add event root.interval.lower data.cut
          root.interval.upper
      rw [splitCount, inductionHypothesis data.leftCell,
        inductionHypothesis data.rightCell]
      change
        ((Subdivision.build event eventNonzero curve box depth data.leftCell).leaves.map
          (Sturm.Count.Basic.cellCount2 event)).sum +
          ((Subdivision.build event eventNonzero curve box depth data.rightCell).leaves.map
            (Sturm.Count.Basic.cellCount2 event)).sum =
        (((Subdivision.build event eventNonzero curve box depth data.leftCell).leaves ++
          (Subdivision.build event eventNonzero curve box depth data.rightCell).leaves).map
            (Sturm.Count.Basic.cellCount2 event)).sum
      rw [Data.List.Map.map_append]
      exact (Data.List.Fold.sum_append Data.Int.Arithmetic.zero_add
        Data.Int.Arithmetic.add_assoc _ _).symm

set_option genInjectivity false in
/-- The retained result of the original deterministic leaf-location program.

The selected original leaf is retained together with its occurrence
in the exact built tree and containment of the requested rational
parameter. All original request owners and depth remain its indices. -/
public structure BuildLocation
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box)
    (depth : Nat) (root : Interval.Proper.Cell) (parameter : Fraction.Rational) where
  /-- The actual leaf selected by the deterministic parameter locator. -/ leaf : Interval.Proper.Cell
  /-- The selected leaf belongs to the exact constructed subdivision. -/ member : leaf ∈ (Subdivision.build event
    eventNonzero curve box depth root).leaves
  /-- The selected leaf contains the original requested parameter. -/ contains : leaf.interval.Contains parameter

constructive_injectivity BuildLocation

/-- Locate a displayed parameter by following the original finite common tree.

A parameter equal to the stored cut selects the original left child.
Each recursive request retains that child cell and its containment
evidence; the result stores its exact selected leaf and tree occurrence. -/
@[expose] public def locateBuild
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box)
    (depth : Nat) (root : Interval.Proper.Cell) (parameter : Fraction.Rational)
    (inside : root.interval.Contains parameter) :
    Subdivision.BuildLocation event eventNonzero curve box depth root parameter := by
  induction depth generalizing root with
  | zero =>
      exact ⟨root, List.Mem.head [], inside⟩
  | succ depth inductionHypothesis =>
      let data := safeSplit event eventNonzero curve box root
      by_cases left : parameter ≤ data.cut
      · let found := inductionHypothesis data.leftCell ⟨inside.1, left⟩
        exact ⟨found.leaf, by
          change found.leaf ∈
            (Subdivision.build event eventNonzero curve box depth data.leftCell).leaves ++
              (Subdivision.build event eventNonzero curve box depth data.rightCell).leaves
          exact List.mem_append_left _ found.member,
          found.contains⟩
      · have cutLower : data.cut ≤ parameter := (lt_of_not_ge left).le
        let found := inductionHypothesis data.rightCell ⟨cutLower, inside.2⟩
        exact ⟨found.leaf, by
          change found.leaf ∈
            (Subdivision.build event eventNonzero curve box depth data.leftCell).leaves ++
              (Subdivision.build event eventNonzero curve box depth data.rightCell).leaves
          exact List.mem_append_right _ found.member,
          found.contains⟩

/-- Every displayed parameter in a root cell belongs to a leaf of its requested finite subdivision.

The deterministic locator supplies its original selected leaf and
retained membership/containment evidence. That same finite observation
is the explicit witness of coverage. -/
public theorem build_covers
    (event : Dense.Basic.RationalPolynomial) (eventNonzero : event.isZero = false)
    (curve : Curve.RationalCurve) (box : Box)
    (depth : Nat) (root : Interval.Proper.Cell) (parameter : Fraction.Rational)
    (inside : root.interval.Contains parameter) :
    ∃ leaf,
      leaf ∈ (Subdivision.build event eventNonzero curve box depth root).leaves ∧
        leaf.interval.Contains parameter := by
  let found := Subdivision.locateBuild event eventNonzero curve box depth root
    parameter inside
  exact ⟨found.leaf, found.member, found.contains⟩

end Subdivision

end Purelib.RootIsolation.Curve.Event.Partition
