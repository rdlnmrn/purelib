module
import Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples
public import Purelib.Examples.Approximation.Gaussian.Division.Gap.WorkedExamples

public import Purelib.Approximation.Gaussian.Division.Bounded.Interface
public import Purelib.Approximation.Gaussian.Division.Gap
public import Purelib.Approximation.Gaussian.Division.Search.State
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.GapDecision
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Division.Partial.Bounded
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small

@[expose] public section

/-! # Regression clients through the public finite-acquisition interface -/

namespace Purelib.Examples.Approximation.Gaussian.Acquisition.WorkedExamples

open Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples (oneInput tinyInput zeroInput)
open Purelib.Approximation.Gaussian.Division
open Purelib.Examples.Approximation.Gaussian.Division

/-- Bounded division by the exact name of one returns a ready quotient. -/
theorem bounded_one_ready :
    ∃ ready, (Bounded.Interface.boundedDivision Bounded.WorkedExamples.oneInput
        (Search.State.initial
      Bounded.WorkedExamples.oneInput) 1 (by decide)).2 = .inl ready :=
  ⟨_, rfl⟩

/-- Bounded division by the tiny input retains a smallness certificate. -/
theorem bounded_tiny_small :
    ∃ small, (Bounded.Interface.boundedDivision Bounded.WorkedExamples.oneInput
        (Search.State.initial
      Bounded.WorkedExamples.tinyInput) 1 (by decide)).2 = .inr small :=
  ⟨_, rfl⟩

/-- Bounded acquisition preserves the denominator's retry index. -/
theorem bounded_preserves_retry_index :
    (Bounded.Interface.boundedDivision Bounded.WorkedExamples.oneInput
        (Search.State.initial
      Bounded.WorkedExamples.tinyInput) 1 (by decide)).1.inspection.retained.nextIndex =
      (Search.State.initial Bounded.WorkedExamples.tinyInput).nextIndex :=
  (Bounded.Interface.BoundedResult.spec (Bounded.Interface.boundedDivision Bounded.WorkedExamples.oneInput
    (Search.State.initial Bounded.WorkedExamples.tinyInput) 1 (by decide))).2.1

/-- The certified unit gap identifies the exact zero denominator. -/
theorem gap_zero_excluded :
    (Gap.gapDivision (Search.State.initial Bounded.WorkedExamples.zeroInput) 1 (by
        decide)
      Gap.WorkedExamples.zero_gap).2.isPrepared = false := by decide

end Purelib.Examples.Approximation.Gaussian.Acquisition.WorkedExamples

end
