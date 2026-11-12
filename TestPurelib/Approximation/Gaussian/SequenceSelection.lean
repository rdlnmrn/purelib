module

import Purelib.Approximation.Gaussian.Sequence.Selection
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
meta import Purelib.Approximation.Gaussian.Sequence.Selection
meta import Purelib.Approximation.Gaussian.Geometric
meta import Purelib.Data.Gaussian.Field

/-! # Stable finite selection and independent comparison starts -/

namespace TestPurelib.Approximation.Gaussian.SequenceSelection

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat

/-- Two original exact approximation programs at the distinct Gaussian readings two and minus two. -/
private def candidates : Fin 2 → ApproximationData :=
  Fin.cases (Geometric.GeometricApproximation.exact 2).toApproximation
    (fun _ => (Geometric.GeometricApproximation.exact (-2)).toApproximation)

/-- Every pair of different original candidate programs is separated by squared distance sixteen. -/
private def separated : Selection.Separated candidates where
  gap := 16
  positive := by decide +kernel
  starts := fun _ => 0
  lower := by
    intro first second different firstIndex secondIndex firstOrder secondOrder
    cases first using Fin.cases with
    | zero =>
      cases second using Fin.cases with
      | zero => exact (different rfl).elim
      | succ second =>
        change (16 : Data.Rat.Fraction.Rational) ≤ normSq (2 - -2)
        decide +kernel
    | succ first =>
      cases second using Fin.cases with
      | zero =>
        change (16 : Data.Rat.Fraction.Rational) ≤ normSq (-2 - 2)
        decide +kernel
      | succ second =>
        have same : first = second := Fin.eq_of_val_eq (by
          have firstBound := first.isLt
          have secondBound := second.isLt
          exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ firstBound)).trans
            (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ secondBound)).symm)
        exact (different (congrArg Fin.succ same)).elim

/-- Finite localization retains the same original source and first candidate, with explicit stage advancement. -/
private def coverage : Selection.Coverage (Geometric.GeometricApproximation.exact 2).toApproximation candidates where
  prepare current target positive :=
    { index := current + 2
      index_ge := Nat.le_add_right _ _
      locate := fun _ _ =>
        { owner := 0
          index := current + 3
          close := by
            intro later order
            change normSq ((2 : Data.Gaussian.Basic.Canonical) - 2) < target
            rewrite [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
            exact positive } }

example (source : ApproximationData) {count : Nat} {family : Fin count → ApproximationData}
    (separation : Selection.Separated family) (coverage : Selection.Coverage source family)
    (leftStart rightStart : Nat) (target : Data.Rat.Fraction.Rational) (positive : 0 < target) :
    Equivalence.Comparison source
      (family (Selection.Anchor.ofCoverage source separation coverage).nearby.owner) leftStart rightStart target :=
  (Selection.Anchor.ofCoverage source separation coverage).equivalent coverage |>.compare
    leftStart rightStart target positive

/-- Execute actual stable selection and independent-start comparison through the original finite coverage procedure. -/
private def checkSelection : IO Unit := do
  let anchor := Selection.Anchor.ofCoverage (Geometric.GeometricApproximation.exact 2).toApproximation
    separated coverage
  unless anchor.index = 2 ∧ anchor.nearby.owner = 0 do
    throw (IO.userError "stable selection changed the original source stage or candidate owner")
  let comparison := (anchor.equivalent coverage).compare 5 11 (1 / 16) (by decide +kernel)
  unless comparison.leftIndex = 7 ∧ comparison.rightIndex = 11 do
    throw (IO.userError "independent starts lost the actual original coverage or candidate stage")
  let anchorRequest := coverage.request 0 (separated.gap / 16)
    (Fraction.Order.Field.div_pos_direct separated.positive (by decide))
  let anchorReading := anchorRequest.locate
  let retainedAnchor := Selection.Anchor.ofNearby (Geometric.GeometricApproximation.exact 2).toApproximation
    separated coverage anchorRequest ⟨anchorReading, rfl⟩
  unless retainedAnchor.index = anchor.index ∧ retainedAnchor.nearby.owner = anchor.nearby.owner ∧
      retainedAnchor.nearby.index = anchor.nearby.index do
    throw (IO.userError "retained nearby anchor changed an original source, owner or candidate stage")
  let target : Fraction.Rational := 1 / 16
  have positive : 0 < target := by decide +kernel
  let accuracy := min (separated.gap / 16) (target / 8)
  have accuracyPositive : 0 < accuracy := Fraction.Order.Basic.lt_min
    (Fraction.Order.Field.div_pos_direct separated.positive (by decide))
    (Fraction.Order.Field.div_pos_direct positive (by decide))
  let comparisonRequest := coverage.request (Nat.max 5 anchor.index) accuracy accuracyPositive
  let comparisonReading := comparisonRequest.locate
  let retainedComparison := anchor.compareFromNearby coverage 5 11 target positive comparisonRequest
    ⟨comparisonReading, rfl⟩
  unless retainedComparison.leftIndex = comparison.leftIndex ∧
      retainedComparison.rightIndex = comparison.rightIndex do
    throw (IO.userError "retained nearby comparison changed an original independent starting-stage payment")
  let later := coverage.prepare 20 (1 / 64) (by decide +kernel)
  let nearby := later.locate later.index (Nat.le_refl _)
  unless nearby.owner = anchor.nearby.owner do
    throw (IO.userError "finer localization changed the fixed original candidate")

#eval checkSelection

end TestPurelib.Approximation.Gaussian.SequenceSelection
