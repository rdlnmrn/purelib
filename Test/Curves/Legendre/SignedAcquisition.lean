module
import Purelib.Topology.Knot.Braid.ThreeStrand.Word
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Curves.Legendre.Acquisition.Signed

public import Test.Curves.Legendre.PositivityAcquisition
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.Signed.Result
import Purelib.Approximation.Gaussian.Enclosure.Signed
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Curves.Legendre.Acquisition.Automatic.Basic
import Purelib.Curves.Legendre.FractionalWords.Periods
import Purelib.Curves.Legendre.GuaranteedFold
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Legendre.Acquisition.Signed

open Purelib.Data.Rat

open Purelib.Topology.Knot.Braid

@[expose] public section

/-!
# Signed acquisition regression clients

The centre-threshold equalities and a tiny positive input intentionally use
the near-boundary branch. Delayed positive discovery prepares arbitrary
finite words in both evaluator interfaces without supplied preparations.
-/

namespace Test.Curves.Legendre.SignedAcquisition

/-- The exact coherent Gaussian name with zero real coordinate and the supplied imaginary height. -/
def input (height : Fraction.Rational) :
    Coherent.CoherentNamed :=
  Coherence.exact ⟨0, height⟩

/-- Attempt signed acquisition at unit requested precision for the exact imaginary input. -/
def report (height : Fraction.Rational) :=
  Requested.acquire (SignedAcquisition.input height) (State.initial (SignedAcquisition.input height))
    1 (by decide)

/-- The exact height one produces the positive acquisition tag. -/
theorem positive_case : (SignedAcquisition.report 1).2.tag = 1 := by decide
/-- The exact height negative one produces the negative acquisition tag. -/
theorem negative_case : (SignedAcquisition.report (-1)).2.tag = 2 := by decide
/-- The exact zero height produces the near-boundary acquisition tag. -/
theorem zero_case : (SignedAcquisition.report 0).2.tag = 0 := by decide
/-- Equality at the upper half-unit threshold remains near the boundary. -/
theorem upper_threshold_case : (SignedAcquisition.report (1 / 2)).2.tag = 0 := by decide
/-- Equality at the lower half-unit threshold remains near the boundary. -/
theorem lower_threshold_case : (SignedAcquisition.report (-(1 / 2))).2.tag = 0 := by decide
/-- A positive tenth lies in the near-boundary acquisition region. -/
theorem tiny_positive_case : (SignedAcquisition.report (1 / 10)).2.tag = 0 := by decide

/-- The coherent imaginary input whose initial state delays its positive witness. -/
abbrev delayed := Test.Curves.Legendre.PositivityAcquisition.delayed

/-- The signed acquisition report for the delayed positive input. -/
def delayedReport := Requested.acquire SignedAcquisition.delayed (State.initial SignedAcquisition.delayed)
  1 (by decide)

/-- Signed acquisition eventually reports the delayed input as positive. -/
theorem delayed_positive : SignedAcquisition.delayedReport.2.tag = 1 := by decide

/-- The delayed report retains the refined source observation. -/
theorem delayed_refined : SignedAcquisition.delayedReport.retained.retained.source = true := rfl

/-- The delayed report retains its original next index zero. -/
theorem delayed_index_unchanged : SignedAcquisition.delayedReport.retained.retained.nextIndex = 0 := rfl

/-- The positive delayed report prepares transport for every finite braid word. -/
theorem delayed_transport_ready (word : ThreeStrand.Word) :
    ∃ result, Report.transport SignedAcquisition.delayedReport word = .ready result := ⟨_, rfl⟩

/-- The positive delayed report prepares folding for every finite braid word. -/
theorem delayed_fold_ready (word : ThreeStrand.Word) :
    ∃ result, Report.fold SignedAcquisition.delayedReport word = .ready result := ⟨_, rfl⟩

/-- Negative acquisition returns its retained negative certificate during word transport. -/
theorem negative_transport_evidence (word : ThreeStrand.Word) :
    ∃ certificate, Report.transport (SignedAcquisition.report (-1)) word = .negative certificate := ⟨_, rfl⟩

/-- Zero acquisition returns its retained near-boundary certificate during word transport. -/
theorem zero_transport_near (word : ThreeStrand.Word) :
    ∃ certificate, Report.transport (SignedAcquisition.report 0) word = .near certificate := ⟨_, rfl⟩

end Test.Curves.Legendre.SignedAcquisition
