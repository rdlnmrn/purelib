module

import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Cut
import Purelib.Data.Rat.Interval.Width
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Rational

-- The retained nominal datatype intentionally repeats its module basename.

@[expose] public section

set_option genInjectivity false in
/-- Finite binary subdivision syntax.  Cells and cut certificates are stored
explicitly instead of in dependent indices, keeping elaboration inexpensive.

Each leaf stores its proper rational cell. Each internal node retains
the original safe cut certificate and its two displayed child trees,
without replacing their interval owners or recomputing any cut. -/
inductive Subdivision (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial) where
  /-- A terminal subdivision cell with its rational interval retained. -/ | leaf (cell : Interval.Proper.Cell)
  /-- An internal cell with its safe cut certificate and two displayed child subdivisions. -/ | split (cell :
    Interval.Proper.Cell) (data : CauchyIndex.EventPartition.Cut.SafeSplit numerator denominator cell)
      (left right : Subdivision numerator
        denominator)

constructive_injectivity Subdivision

namespace Subdivision.leaf

end Subdivision.leaf

namespace Subdivision.leaf

end Subdivision.leaf

namespace Subdivision.split

end Subdivision.split

namespace Subdivision.split

end Subdivision.split

end

namespace Subdivision

/-- Execute exactly the requested number of safe central-third rounds.

Zero depth retains the original cell as one leaf. Each successor depth
retains one actual safe split and recursively builds its two original
child cells at the preceding depth. -/
@[expose] public def build
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    Nat → Interval.Proper.Cell → Subdivision numerator denominator
  | 0, cell => .leaf cell
  | depth + 1, cell =>
      let data := CauchyIndex.EventPartition.Cut.safeSplit numerator denominator denominatorNonzero cell
      .split cell data
        (build numerator
          denominator denominatorNonzero depth data.leftCell)
        (build numerator
          denominator denominatorNonzero depth data.rightCell)

end Subdivision

namespace Subdivision

/-- Read the terminal cells in left-to-right order.

An internal node concatenates the two child leaf lists without recomputing any safe cut. -/
@[expose] public def leaves {numerator denominator : Dense.Rational.Basic.CoordinatePolynomial} :
    Subdivision numerator denominator → List Interval.Proper.Cell
  | .leaf cell => [cell]
  | .split _ _ left right => left.leaves ++ right.leaves

end Subdivision

namespace Subdivision

/-- Every leaf produced by a finite sequence of safe central-third cuts refines the original interval.

A zero-depth occurrence identifies the original cell. At a split, its
retained occurrence selects one child; that child refinement composes
with the recursively retained leaf refinement. -/
public theorem build_leaf_refines
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (depth : Nat) (root : Interval.Proper.Cell) {leaf : Interval.Proper.Cell}
    (member : leaf ∈
      (Subdivision.build numerator denominator denominatorNonzero depth root).leaves) :
    leaf.interval.Refines root.interval := by
  induction depth generalizing root with
  | zero =>
      change leaf ∈ [root] at member
      have sameCell := Data.List.Membership.mem_singleton.mp member
      cases sameCell
      exact ⟨le_rfl, le_rfl⟩
  | succ depth inductionHypothesis =>
      let data := CauchyIndex.EventPartition.Cut.safeSplit numerator denominator denominatorNonzero root
      change leaf ∈
        (Subdivision.build numerator denominator denominatorNonzero depth data.leftCell).leaves ++
          (Subdivision.build numerator denominator denominatorNonzero depth
            data.rightCell).leaves at member
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

end Subdivision

namespace Subdivision

/-- Every leaf built at a requested depth is at most the fixed `2/3`
contraction power times the initial width.

The retained safe split contracts each original child by less than
two thirds. The same positive contraction power transports the recursive
leaf width bound without altering the requested depth or cell owners. -/
public theorem build_leaf_width_le
    (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial)
    (denominatorNonzero : denominator.isZero = false)
    (depth : Nat) (root : Interval.Proper.Cell) {leaf : Interval.Proper.Cell}
    (member : leaf ∈
      (Subdivision.build numerator denominator denominatorNonzero depth root).leaves) :
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
      let data := CauchyIndex.EventPartition.Cut.safeSplit numerator denominator denominatorNonzero root
      change leaf ∈
        (Subdivision.build numerator denominator denominatorNonzero depth data.leftCell).leaves ++
          (Subdivision.build numerator denominator denominatorNonzero depth
            data.rightCell).leaves at member
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

end Subdivision

end Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition
