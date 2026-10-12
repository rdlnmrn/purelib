module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Cut
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Refinement
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.EventPartition.Cut
import Purelib.RootIsolation.Sturm.Count.Basic
public import Purelib.RootIsolation.Sturm.Track.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite nonzero-event refinement steps

The original state indexes the selected refined nonzero-event state. The exact finite refinement operation retains its
source relation and quantitative interval-width bound.
-/

public section

namespace Purelib.RootIsolation.Sturm.Track.Refinement

set_option genInjectivity false in
/-- One selected nonzero-count child and its geometric certificates.

The original state indexes the selected refined nonzero-event state. The exact finite refinement operation retains its
source relation and quantitative interval-width bound. -/
structure Step {polynomial : Dense.Rational.Basic.CoordinatePolynomial} (current : Sturm.Track.Basic.State polynomial)
  where
  /-- The selected proper child cell with its retained nonzero doubled Sturm count. -/ next : Sturm.Track.Basic.State
    polynomial
  /-- The selected child cell refines the original parameter cell. -/ refines : next.cell.interval.Refines
    current.cell.interval
  /-- The selected width is strictly less than two thirds of the original width. -/ contracts :
    (Data.Rat.Interval.Bounds.width next.cell.interval) <
    (2 / 3 : Fraction.Rational) * (Data.Rat.Interval.Bounds.width current.cell.interval)

constructive_injectivity Step

/-- Select the left nonzero-count child when available, otherwise the right
child.  Additivity proves that the fallback child is nonzero.

The original certified safe split gives left and right cells. The retained left count selects the left cell when
nonzero; finite additivity certifies the selected right cell otherwise. -/
@[expose] def step
    (polynomial : Dense.Rational.Basic.CoordinatePolynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : Sturm.Track.Basic.State polynomial) : Sturm.Track.Refinement.Step current := by
  let split := Dense.Rational.CauchyIndex.EventPartition.Cut.safeSplit
    (Dense.Derivative.derivative polynomial) polynomial
    polynomialNonzero current.cell
  let leftCount := Sturm.Count.Basic.sturmRootCount2 polynomial
    split.leftCell.interval.lower split.leftCell.interval.upper
  by_cases leftNonzero : leftCount ≠ 0
  · exact
      { next :=
          { cell := split.leftCell
            countNonzero := leftNonzero }
        refines := Data.Rat.Interval.Bounds.leftChild_refines current.cell.interval split.cut
          split.lowerLt.le split.upperLt.le
        contracts := split.leftContracts }
  · have leftZero : leftCount = 0 := Decidable.not_not.mp leftNonzero
    have rightNonzero : Sturm.Count.Basic.sturmRootCount2 polynomial
        split.rightCell.interval.lower split.rightCell.interval.upper ≠ 0 := by
      intro rightZero
      apply current.countNonzero
      rw [Sturm.Count.Basic.sturmRootCount2_add polynomial current.cell.interval.lower
        split.cut current.cell.interval.upper]
      change leftCount + Sturm.Count.Basic.sturmRootCount2 polynomial
        split.rightCell.interval.lower split.rightCell.interval.upper = 0
      rw [leftZero, rightZero]
      decide
    exact
      { next :=
          { cell := split.rightCell
            countNonzero := rightNonzero }
        refines := Data.Rat.Interval.Bounds.rightChild_refines current.cell.interval split.cut
          split.lowerLt.le split.upperLt.le
        contracts := split.rightContracts }

/-- Execute exactly the requested number of nonzero-event refinements.

Zero steps retain the original current cell. Each successor step uses the same nonzero-event refinement and passes its
actual returned state to the remaining finite iteration. -/
@[expose] def refineN
    (polynomial : Dense.Rational.Basic.CoordinatePolynomial) (polynomialNonzero : polynomial.isZero = false) :
    Sturm.Track.Basic.State polynomial → Nat → Sturm.Track.Basic.State polynomial
  | current, 0 => current
  | current, depth + 1 =>
      Purelib.RootIsolation.Sturm.Track.Refinement.refineN polynomial polynomialNonzero
        (Sturm.Track.Refinement.step polynomial polynomialNonzero current).next depth

/-- Every finite nonzero-event refinement remains within the original parameter cell. -/
theorem refineN_refines
    (polynomial : Dense.Rational.Basic.CoordinatePolynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : Sturm.Track.Basic.State polynomial) (depth : Nat) :
    (Sturm.Track.Refinement.refineN polynomial polynomialNonzero current depth).cell.interval.Refines
      current.cell.interval := by
  induction depth generalizing current with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ depth inductionHypothesis =>
      exact Data.Rat.Interval.Refinement.intervalRefines_trans
        (inductionHypothesis
          (Sturm.Track.Refinement.step polynomial polynomialNonzero current).next)
        (Sturm.Track.Refinement.step polynomial polynomialNonzero current).refines

/-- After `n` nonzero-event steps, the width is at most `(2/3)^n` times its original value. -/
theorem refineN_width_le
    (polynomial : Dense.Rational.Basic.CoordinatePolynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : Sturm.Track.Basic.State polynomial) (depth : Nat) :
    (Data.Rat.Interval.Bounds.width (Sturm.Track.Refinement.refineN polynomial polynomialNonzero current
      depth).cell.interval) ≤
      (2 / 3 : Fraction.Rational) ^ depth * (Data.Rat.Interval.Bounds.width current.cell.interval) := by
  induction depth generalizing current with
  | zero =>
      simp only [Sturm.Track.Refinement.refineN, pow_zero, one_mul]
      exact le_rfl
  | succ depth inductionHypothesis =>
      let next := (Sturm.Track.Refinement.step polynomial polynomialNonzero current).next
      have recursive := inductionHypothesis next
      have powerPositive : 0 < (2 / 3 : Fraction.Rational) ^ depth :=
        Fraction.Order.Arithmetic.pow_pos_direct (by decide) depth
      exact (calc
        (Data.Rat.Interval.Bounds.width (Sturm.Track.Refinement.refineN polynomial polynomialNonzero current
          (depth + 1)).cell.interval) =
            (Data.Rat.Interval.Bounds.width (Sturm.Track.Refinement.refineN polynomial polynomialNonzero next
              depth).cell.interval) :=
          rfl
        _ ≤ (2 / 3 : Fraction.Rational) ^ depth * (Data.Rat.Interval.Bounds.width next.cell.interval) :=
          recursive
        _ < (2 / 3 : Fraction.Rational) ^ depth *
              ((2 / 3 : Fraction.Rational) * (Data.Rat.Interval.Bounds.width current.cell.interval)) :=
          Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct powerPositive
            (Sturm.Track.Refinement.step polynomial polynomialNonzero current).contracts
        _ = (2 / 3 : Fraction.Rational) ^ Nat.succ depth *
              (Data.Rat.Interval.Bounds.width current.cell.interval) := by
          rw [pow_succ]
          ring1
      ).le

end Purelib.RootIsolation.Sturm.Track.Refinement

end
