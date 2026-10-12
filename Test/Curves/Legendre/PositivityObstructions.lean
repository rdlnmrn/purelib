module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction
import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
public import Test.Curves.Legendre.SignedAcquisition
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Control.FiniteRunner.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Positive

open Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction

open Purelib.Approximation.Gaussian.Acquisition.State

section
@[expose] public section

namespace Test.Curves.Legendre.PositivityObstructions

/-- The exact coherent Gaussian input with imaginary part negative one. -/
abbrev negativeInput := Test.Curves.Legendre.SignedAcquisition.input
  (-1)

/-- Every value retained by the exact negative input is nonpositive. -/
theorem negative_candidates (state :
    Approximation.Gaussian.Acquisition.State
  negativeInput) : Obstruction.Nonpositive
  negativeInput state := by
  intro value possible
  change value = (⟨0, -1⟩ : Data.Gaussian.Basic.Canonical) at possible
  rw [possible]
  decide

/-- Every finite positive-acquisition budget exhausts on the exact negative input. -/
theorem negative_all_budgets (state :
    Approximation.Gaussian.Acquisition.State
  negativeInput) (fuel : Nat) :
    Search.attempt negativeInput state fuel = .exhausted (Schedule.advanceN
      state fuel) :=
  Nonpositive.attempt_exhausts state (negative_candidates state) fuel
end Test.Curves.Legendre.PositivityObstructions

end
