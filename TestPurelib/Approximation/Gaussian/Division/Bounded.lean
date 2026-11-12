module
import Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Division.Partial.Bounded
import Purelib.Approximation.Gaussian.Division.Partial.Step
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Division.Partial.Requirement
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Division.Partial.Ready

/-! Regression checks for the retained approximation gaussian division bounded contracts. -/

namespace TestPurelib.Approximation.Gaussian.Division.Bounded

open Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Approximation.Gaussian.Name
open Purelib.Data.Gaussian
open Purelib.Examples.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Process

/-- The delayed denominator inspection retains its refined Boolean source. -/
theorem delayed_source_refined :
    (SmallOrApart.acquire (Refinement.State.initial Partial.DelayedOne.delayedOne)
      1 (by decide)).inspection.retained.source = true := rfl

/-- The bounded inspection retains the original next-index counter. -/
theorem delayed_index_unchanged :
    (SmallOrApart.acquire (Refinement.State.initial Partial.DelayedOne.delayedOne)
      1 (by decide)).inspection.retained.nextIndex = 0 := rfl

end TestPurelib.Approximation.Gaussian.Division.Bounded
