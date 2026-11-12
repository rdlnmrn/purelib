module
import Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples
import Purelib.Examples.Approximation.Gaussian.Process.Imaginary.DelayedUnit
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Requested
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.PositiveRunner
public import Purelib.Curves.Legendre.Acquisition.Signed.Gap

import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision
import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Control.FiniteRunner.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Curves.Legendre.FractionalWords.Periods
import Purelib.Curves.Legendre.GuaranteedFold
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Acquisition.Signed.Gap

open Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical

open Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision

open Purelib.Topology.Knot.Braid

namespace TestPurelib.Curves.Legendre.SignedGap

open _root_.Purelib.Approximation.Gaussian.Acquisition.State (initial)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples
  (input positive_gap negative_gap delayed_gap)
open Purelib.Examples.Approximation.Gaussian.Process.Imaginary

/-- The requested signed-gap report recognizes the positive unit input. -/
theorem requested_positive :
    (Requested.requested (input 1) (initial
      (input 1)) 1 (by decide) (positive_gap _)).2.isPositive = true :=
      by
  decide

/-- The requested signed-gap report recognizes the negative unit input. -/
theorem requested_negative :
    (Requested.requested (input (-1)) (initial
      (input (-1))) 1 (by decide) (negative_gap _)).2.isPositive =
      false := by decide

/-- The canonical signed-gap report for the delayed imaginary-unit input. -/
def delayedReport := Canonical.canonical DelayedUnit.name (initial
  DelayedUnit.name) 1 (by decide) (delayed_gap _)

/-- The canonical delayed report has the positive outcome. -/
theorem canonical_delayed_positive : delayedReport.outcome.isPositive = true := by decide

/-- The canonical delayed report retains the exact sufficient count four. -/
theorem canonical_delayed_count : delayedReport.count = 4 := by decide

/-- The computed sufficient budget is for the original runner, not just a new evaluator that assumes a passing state. -/
theorem original_runner_budget :
    ∃ certificate, Search.attempt DelayedUnit.name (initial
      DelayedUnit.name)
      (delayedReport.count + 1) = .ready certificate :=
  ⟨(CanonicalReport.finishPositive delayedReport (by decide)).val,
    (CanonicalReport.finishPositive delayedReport (by decide)).property⟩

/-- The canonical positive outcome prepares every finite braid word for transport. -/
theorem canonical_word_ready (word : ThreeStrand.Word) :
    ∃ result, Outcome.transport delayedReport.outcome word = .inl result := ⟨_, rfl⟩

/-- The canonical positive outcome prepares every finite braid word for folding. -/
theorem canonical_fold_ready (word : ThreeStrand.Word) :
    ∃ result, Outcome.fold delayedReport.outcome word = .inl result := ⟨_, rfl⟩

end TestPurelib.Curves.Legendre.SignedGap
