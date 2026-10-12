module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Observation.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Approximation.Observation.Rational.WorkedExamples

open Purelib
open Purelib.Data.Rat
open Purelib.Examples

/-- A rational observation whose sole possible value and spread are zero.

Keeps the explicit zero witness and pairwise squared-distance certificate. -/
def zeroObservation :
  Approximation.Observation Fraction.Rational (fun left right =>
    (left - right) ^ 2) where
  Possible value := value = 0
  witness := 0
  witness_possible := rfl
  spread := 0
  spread_nonnegative := le_rfl
  pairwise := by
    intro left right leftZero rightZero
    subst left
    subst right
    exact le_rfl

/-- Translation by one maps the exact zero observation to a possible value one.

Retains the original zero witness and the exact squared-distance identity under rational translation. -/
example : (zeroObservation.map
    (targetDistance := fun left right => (left - right) ^ 2)
    (fun value => value + 1) 1 (by decide)
    (by
      intro left right
      rw [show (left + 1 - (right + 1)) ^ 2 = (left - right) ^ 2 by ring1,
        one_mul])).Possible 1 :=
  ⟨0, rfl, by ring1⟩

end Purelib.Examples.Approximation.Observation.Rational.WorkedExamples

end
