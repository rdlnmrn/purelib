module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Requested
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.PositiveRunner
public import Purelib.Curves.Legendre.Acquisition.Signed.Gap

import Test.Curves.Legendre.PositivityAcquisition
public import Test.Curves.Legendre.SignedAcquisition
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

@[expose] public section

namespace Test.Curves.Legendre.SignedGap

open _root_.Purelib.Approximation.Gaussian.Acquisition.State (initial)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Test.Curves.Legendre.SignedAcquisition (input delayed)

/-- The exact positive unit input has the retained signed gap one. -/
theorem positive_gap (state : Approximation.Gaussian.Acquisition.State (Test.Curves.Legendre.SignedAcquisition.input 1))
    : Approximation.Gaussian.Acquisition.Signed.Gap
  (Test.Curves.Legendre.SignedAcquisition.input 1) state 1 := by
  intro value possible
  change value = (⟨0, 1⟩ : Data.Gaussian.Basic.Canonical) at possible
  subst value
  exact .inr (by decide)

/-- The exact negative unit input has the retained signed gap one. -/
theorem negative_gap (state : Approximation.Gaussian.Acquisition.State (Test.Curves.Legendre.SignedAcquisition.input
    (-1))) : Approximation.Gaussian.Acquisition.Signed.Gap
  (Test.Curves.Legendre.SignedAcquisition.input (-1)) state 1 := by
  intro value possible
  change value = (⟨0, -1⟩ : Data.Gaussian.Basic.Canonical) at possible
  subst value
  exact .inl (by decide)

/-- The delayed imaginary-unit input has the retained signed gap one. -/
theorem delayed_gap (state : Approximation.Gaussian.Acquisition.State Test.Curves.Legendre.SignedAcquisition.delayed) :
    Approximation.Gaussian.Acquisition.Signed.Gap
  Test.Curves.Legendre.SignedAcquisition.delayed state 1 := by
  intro value possible
  change value = Test.Curves.Legendre.PositivityAcquisition.imaginaryUnit at possible
  subst value
  exact .inr (by decide)

/-- The requested signed-gap report recognizes the positive unit input. -/
theorem requested_positive :
    (Requested.requested (Test.Curves.Legendre.SignedAcquisition.input 1) (State.initial
      (Test.Curves.Legendre.SignedAcquisition.input 1)) 1 (by decide) (positive_gap _)).2.isPositive = true :=
      by
  decide

/-- The requested signed-gap report recognizes the negative unit input. -/
theorem requested_negative :
    (Requested.requested (Test.Curves.Legendre.SignedAcquisition.input (-1)) (State.initial
      (Test.Curves.Legendre.SignedAcquisition.input (-1))) 1 (by decide) (negative_gap _)).2.isPositive =
      false := by decide

/-- The canonical signed-gap report for the delayed imaginary-unit input. -/
def delayedReport := Gap.Canonical.canonical Test.Curves.Legendre.SignedAcquisition.delayed (State.initial
  Test.Curves.Legendre.SignedAcquisition.delayed) 1 (by decide) (delayed_gap _)

/-- The canonical delayed report has the positive outcome. -/
theorem canonical_delayed_positive : SignedGap.delayedReport.outcome.isPositive = true := by decide

/-- The canonical delayed report retains the exact sufficient count four. -/
theorem canonical_delayed_count : SignedGap.delayedReport.count = 4 := by decide

/-- The computed sufficient budget is for the original runner, not just a new evaluator that assumes a passing state. -/
theorem original_runner_budget :
    ∃ certificate, Search.attempt Test.Curves.Legendre.SignedAcquisition.delayed (State.initial
      Test.Curves.Legendre.SignedAcquisition.delayed)
      (SignedGap.delayedReport.count + 1) = .ready certificate :=
  ⟨(CanonicalReport.finishPositive delayedReport (by decide)).val,
    (CanonicalReport.finishPositive delayedReport (by decide)).property⟩

/-- The canonical positive outcome prepares every finite braid word for transport. -/
theorem canonical_word_ready (word : ThreeStrand.Word) :
    ∃ result, Outcome.transport SignedGap.delayedReport.outcome word = .inl result := ⟨_, rfl⟩

/-- The canonical positive outcome prepares every finite braid word for folding. -/
theorem canonical_fold_ready (word : ThreeStrand.Word) :
    ∃ result, Outcome.fold SignedGap.delayedReport.outcome word = .inl result := ⟨_, rfl⟩

end Test.Curves.Legendre.SignedGap
