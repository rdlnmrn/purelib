import mathlib.Tactic.QuotientFreeRing
import RFAP.Sturm.EventPartition

/-!
# Shrinking nonzero Sturm-event cells

A nonzero doubled Sturm count can be followed constructively without first
proving the stronger global nonnegativity theorem.  A safe cut splits the
parent count additively; testing the left integer count either selects that
child or proves that the right count remains nonzero.  Repeating the fixed
central-third contraction gives a total finite interval-refinement track for every
positive rational width request.

This is the reusable track-valued interface for finite boundary ownership.
It names no root and does not assume that the nonzero count has a particular
sign.
-/

namespace RFAP.SturmNonzeroEvent

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev Cell := RFAP.SturmEventPartition.Cell

open RFAP.SturmRootCount

/-- One proper rational cell carrying a nonzero doubled Sturm count. -/
structure State (polynomial : Polynomial) where
  cell : Cell
  countNonzero : sturmRootCount2 polynomial
    cell.interval.lower cell.interval.upper ≠ 0

/-- One selected nonzero-count child and its geometric certificates. -/
structure Step {polynomial : Polynomial} (current : State polynomial) where
  next : State polynomial
  refines : next.cell.interval.Refines current.cell.interval
  contracts : next.cell.interval.width <
    (2 / 3 : Coordinate) * current.cell.interval.width

/-- Select the left nonzero-count child when available, otherwise the right
child.  Additivity proves that the fallback child is nonzero. -/
def step
    (polynomial : Polynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) : Step current := by
  let split := RFAP.SturmEventPartition.safeSplit
    (RFAP.ComputableDerivative.derivative polynomial) polynomial
    polynomialNonzero current.cell
  let leftCount := sturmRootCount2 polynomial
    split.leftCell.interval.lower split.leftCell.interval.upper
  by_cases leftNonzero : leftCount ≠ 0
  · exact
      { next :=
          { cell := split.leftCell
            countNonzero := leftNonzero }
        refines := current.cell.interval.leftChild_refines split.cut
          split.lowerLt.le split.upperLt.le
        contracts := split.leftContracts }
  · have leftZero : leftCount = 0 := Decidable.not_not.mp leftNonzero
    have rightNonzero : sturmRootCount2 polynomial
        split.rightCell.interval.lower split.rightCell.interval.upper ≠ 0 := by
      intro rightZero
      apply current.countNonzero
      rw [sturmRootCount2_add polynomial current.cell.interval.lower
        split.cut current.cell.interval.upper]
      change leftCount + sturmRootCount2 polynomial
        split.rightCell.interval.lower split.rightCell.interval.upper = 0
      rw [leftZero, rightZero]
      decide
    exact
      { next :=
          { cell := split.rightCell
            countNonzero := rightNonzero }
        refines := current.cell.interval.rightChild_refines split.cut
          split.lowerLt.le split.upperLt.le
        contracts := split.rightContracts }

/-- Execute exactly the requested number of nonzero-event refinements. -/
def refineN
    (polynomial : Polynomial) (polynomialNonzero : polynomial.isZero = false) :
    State polynomial → Nat → State polynomial
  | current, 0 => current
  | current, depth + 1 =>
      refineN polynomial polynomialNonzero
        (step polynomial polynomialNonzero current).next depth

theorem intervalRefines_trans
    {inner middle outer : RFAP.PathClearance.Interval}
    (innerMiddle : inner.Refines middle)
    (middleOuter : middle.Refines outer) : inner.Refines outer :=
  ⟨middleOuter.1.trans innerMiddle.1,
    innerMiddle.2.trans middleOuter.2⟩

theorem refineN_refines
    (polynomial : Polynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) (depth : Nat) :
    (refineN polynomial polynomialNonzero current depth).cell.interval.Refines
      current.cell.interval := by
  induction depth generalizing current with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ depth inductionHypothesis =>
      exact intervalRefines_trans
        (inductionHypothesis
          (step polynomial polynomialNonzero current).next)
        (step polynomial polynomialNonzero current).refines

theorem refineN_width_le
    (polynomial : Polynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) (depth : Nat) :
    (refineN polynomial polynomialNonzero current depth).cell.interval.width ≤
      (2 / 3 : Coordinate) ^ depth * current.cell.interval.width := by
  induction depth generalizing current with
  | zero =>
      simp only [refineN, pow_zero, one_mul]
      exact le_rfl
  | succ depth inductionHypothesis =>
      let next := (step polynomial polynomialNonzero current).next
      have recursive := inductionHypothesis next
      have powerPositive : 0 < (2 / 3 : Coordinate) ^ depth :=
        RFAP.ConstructiveFraction.pow_pos_direct (by decide) depth
      exact (calc
        (refineN polynomial polynomialNonzero current (depth + 1)).cell.interval.width =
            (refineN polynomial polynomialNonzero next depth).cell.interval.width :=
          rfl
        _ ≤ (2 / 3 : Coordinate) ^ depth * next.cell.interval.width :=
          recursive
        _ < (2 / 3 : Coordinate) ^ depth *
              ((2 / 3 : Coordinate) * current.cell.interval.width) :=
          RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct powerPositive
            (step polynomial polynomialNonzero current).contracts
        _ = (2 / 3 : Coordinate) ^ Nat.succ depth *
              current.cell.interval.width := by
          rw [pow_succ]
          ring1
      ).le

/-- Explicit finite depth sufficient for a requested positive width. -/
def requestDepth (current : State polynomial) (epsilon : Coordinate) : Nat :=
  RFAP.SafeCandidates.geometricDepth
    current.cell.interval.width epsilon

/-- Total finite nonzero-event width request. -/
def request
    (polynomial : Polynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) (epsilon : Coordinate) : State polynomial :=
  refineN polynomial polynomialNonzero current (requestDepth current epsilon)

theorem request_refines
    (polynomial : Polynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) (epsilon : Coordinate) :
    (request polynomial polynomialNonzero current epsilon).cell.interval.Refines
      current.cell.interval :=
  refineN_refines polynomial polynomialNonzero current
    (requestDepth current epsilon)

theorem request_width_le
    (polynomial : Polynomial) (polynomialNonzero : polynomial.isZero = false)
    (current : State polynomial) (epsilon : Coordinate)
    (positive : 0 < epsilon) :
    (request polynomial polynomialNonzero current epsilon).cell.interval.width ≤
      epsilon := by
  exact (refineN_width_le polynomial polynomialNonzero current
    (requestDepth current epsilon)).trans
      (RFAP.SafeCandidates.geometricDepth_sufficient
        current.cell.interval.width_nonneg positive)

end RFAP.SturmNonzeroEvent
