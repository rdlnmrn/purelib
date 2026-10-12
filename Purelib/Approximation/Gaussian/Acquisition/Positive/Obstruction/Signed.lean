module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Acquisition.Positive.Search
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Acquisition.State.Schedule
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Control.FiniteRunner.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-!
# Persistent obstructions to upper-half-plane positivity

Nonpositive candidates refute positive enclosures only at the same source or
states with explicit provenance back to it. This does not refute arbitrary
fractional transformations, and does not assume nested enclosing balls.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction.Signed

open Purelib
open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Approximation.Gaussian.Acquisition.Positive
open Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction
open Purelib.Approximation.Gaussian.Acquisition.Signed
open Purelib.Approximation.Gaussian.Acquisition.State
open Purelib.Approximation.Gaussian.Name
open Purelib.Data.Rat

namespace Nonpositive
end Nonpositive

/-- The signed negative outcome supplies an actual obstruction to this positivity requirement, while retaining the
strictly negative margin. -/
theorem nonpositive_of_negative {tau : Coherent.CoherentNamed} {state : State tau} {delta : Fraction.Rational}
    (positive : 0 < delta)
    (negative : Certificate.Negative tau state delta) :
    Obstruction.Nonpositive tau state := by
  intro value possible
  have nonpositive : -(delta / 4) ≤ (0 : Fraction.Rational) := by
    simpa only [neg_zero] using Fraction.Order.Arithmetic.neg_le_neg_direct
      (Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive).le
  exact (negative.upper possible).trans nonpositive

end Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction.Signed

end

public section

namespace Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction.Signed

open Purelib
open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Approximation.Gaussian.Acquisition.Positive
open Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction
open Purelib.Approximation.Gaussian.Acquisition.Signed
open Purelib.Approximation.Gaussian.Acquisition.State
open Purelib.Approximation.Gaussian.Name
open Purelib.Data.Rat

/-- A certificate obtained by signed inspection itself obstructs all later positive discovery on that retained branch.
-/
theorem discovered_negative_all_budgets {tau : Coherent.CoherentNamed} {state : State tau}
    {delta : Fraction.Rational} (positive : 0 < delta)
    (negative : Certificate.Negative tau state delta) (fuel : Nat) :
    Search.attempt tau state fuel = .exhausted (Schedule.advanceN state fuel) :=
  Nonpositive.attempt_exhausts state
    (Approximation.Gaussian.Acquisition.Positive.Obstruction.Signed.nonpositive_of_negative positive negative) fuel

end Purelib.Approximation.Gaussian.Acquisition.Positive.Obstruction.Signed

end
