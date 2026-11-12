module

import Purelib.Algebra.Ring.Normalization
import Purelib.Approximation.Gaussian.Sequence.Selection.Separation
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Data.Gaussian.Field
meta import Purelib.Approximation.Gaussian.Sequence.Selection.Separation
meta import Purelib.Approximation.Gaussian.Geometric
meta import Purelib.Data.Gaussian.Field

/-!
# Original candidate prefixes and retained tail separation

The two original programs agree at their first reading and separate later.
Actual cached pair certificates retain nonzero starting stages. Stable
selection and independent-start comparison use those same programs, while
the stored pair matrix supplies its own sufficient common stage and gap.
-/

namespace TestPurelib.Approximation.Gaussian.TailSelection

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat

/-- One original geometric program starts at zero and then retains the displayed quadrance-four point. -/
private def prefixed (value : Canonical) (quadrance : normSq value = 4) : Geometric.GeometricApproximation where
  sample := fun index => match index with | 0 => 0 | _ + 1 => value
  errorScale := 4
  errorScale_nonneg := by decide +kernel
  later_close := by
    intro earlier later order
    cases earlier with
    | zero =>
      cases later with
      | zero =>
        change normSq ((0 : Canonical) - 0) ≤ _
        rewrite [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
        exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide +kernel) _
      | succ later =>
        change normSq (value - 0) ≤ Approximation.Rational.Geometric.Basic.quarterRadius 4 0
        rewrite [Algebra.Ring.Normalization.sub_zero, quadrance]
        exact Fraction.Order.Basic.le_refl _
    | succ earlier =>
      cases later with
      | zero => exact (Nat.not_succ_le_zero _ order).elim
      | succ later =>
        change normSq (value - value) ≤ _
        rewrite [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
        exact Approximation.Rational.Geometric.Basic.quarterRadius_nonneg (by decide +kernel) _
  centerBound := 4
  centerBound_nonneg := by decide +kernel
  sample_bounded := by
    intro index
    cases index with
    | zero => exact (by decide +kernel : normSq (0 : Canonical) ≤ 4)
    | succ index => exact quadrance.le

/-- Both original programs have the same first reading and retain opposite later points. -/
private def candidates : Fin 2 → ApproximationData :=
  Fin.cases (prefixed 2 (by decide +kernel)).toApproximation
    (fun _ => (prefixed (-2) (by decide +kernel)).toApproximation)

/-- Every positive-index reading of the first original program is the same retained point two. -/
private theorem first_read {index : Nat} (positive : 0 < index) : (candidates 0).sample index = 2 := by
  cases index with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ index => rfl

/-- The actual pair procedure retains starts three/five and the original program readings at those starts. -/
private def bound (first second : Fin 2) : Selection.PairBound candidates first second :=
  if same : first = second then
    { leftIndex := 0
      rightIndex := 0
      gap := 1
      positive := by decide +kernel
      lower := fun different _ _ _ _ => (different same).elim }
  else
    { leftIndex := 3
      rightIndex := 5
      gap := 16
      positive := by decide +kernel
      lower := by
        intro different firstLater secondLater firstOrder secondOrder
        have firstPositive : 0 < firstLater := (show (0 : Nat) < 3 by decide).trans_le firstOrder
        have secondPositive : 0 < secondLater := (show (0 : Nat) < 5 by decide).trans_le secondOrder
        cases firstLater with
        | zero => exact (Nat.not_lt_zero _ firstPositive).elim
        | succ firstLater =>
          cases secondLater with
          | zero => exact (Nat.not_lt_zero _ secondPositive).elim
          | succ secondLater =>
            cases first using Fin.cases with
            | zero =>
              cases second using Fin.cases with
              | zero => exact (different rfl).elim
              | succ second =>
                change (16 : Fraction.Rational) ≤ normSq ((2 : Canonical) - -2)
                decide +kernel
            | succ first =>
              cases second using Fin.cases with
              | zero =>
                change (16 : Fraction.Rational) ≤ normSq ((-2 : Canonical) - 2)
                decide +kernel
              | succ second =>
                have equal : first = second := Fin.eq_of_val_eq (by
                  exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ first.isLt)).trans
                    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ second.isLt)).symm)
                exact (different (congrArg Fin.succ equal)).elim }

/-- Complete finite localization retains the first original candidate after its actual differing prefix. -/
private def coverage : Selection.Coverage (Geometric.GeometricApproximation.exact 2).toApproximation candidates where
  prepare current target positive :=
    { index := current + 2
      index_ge := Nat.le_add_right _ _
      locate := fun _ _ =>
        { owner := 0
          index := 1
          close := by
            intro later order
            change normSq ((candidates 0).sample later - 2) < target
            rewrite [first_read order, sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
            exact positive } }

/-- Execute original-prefix agreement, retained pair budgets and stable independent-start selection. -/
private def checkTailSelection : IO Unit := do
  let pairs := Selection.Pairs.ofFn bound
  unless (candidates 0).sample 0 = (candidates 1).sample 0 ∧
      (candidates 0).sample 1 ≠ (candidates 1).sample 1 do
    throw (IO.userError "original prefix agreement or later separation was changed")
  unless pairs.start = 5 ∧ pairs.gap = 1 ∧ (pairs.get 0 1).leftIndex = 3 ∧
      (pairs.get 0 1).rightIndex = 5 do
    throw (IO.userError "stored pair certificates did not supply their actual common start and gap")
  let reversed := (pairs.get 0 1).symm
  unless reversed.leftIndex = 5 ∧ reversed.rightIndex = 3 ∧ reversed.gap = (pairs.get 0 1).gap do
    throw (IO.userError "pair reversal replaced its original retained starts or gap")
  let anchor := Selection.Anchor.ofCoverage (Geometric.GeometricApproximation.exact 2).toApproximation
    pairs.separated coverage
  let comparison := (anchor.equivalent coverage).compare 4 6 (1 / 16) (by decide +kernel)
  unless anchor.nearby.owner = 0 ∧ comparison.leftIndex = 6 ∧ comparison.rightIndex = 6 do
    throw (IO.userError "tail-only separation failed stable original selection or independent start preservation")

#eval checkTailSelection

end TestPurelib.Approximation.Gaussian.TailSelection
