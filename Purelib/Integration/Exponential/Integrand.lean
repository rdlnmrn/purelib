module

public import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Finite linear exponential integrands on the oriented unit segment -/

public section
namespace Purelib.Integration.Exponential

open Purelib.Data.Gaussian

set_option genInjectivity false in
/-- Finite linear combinations of one exponential integrand, retaining every coefficient occurrence. -/
inductive Integrand
  /-- The original exponential integrand on the segment from zero to one. -/
  | exponential
  /-- The sum of the two displayed integrand constructions. -/
  | add (left right : Integrand)
  /-- Negate the displayed integrand construction. -/
  | neg (input : Integrand)
  /-- Multiply the displayed integrand by this exact Gaussian coefficient. -/
  | scale (factor : Basic.Canonical) (input : Integrand)

constructive_injectivity Integrand

namespace Integrand

/-- Normalize a finite linear exponential integrand to its exact Gaussian coefficient. -/
@[expose] def coefficient : Integrand → Basic.Canonical
  | .exponential => 1
  | .add left right => left.coefficient + right.coefficient
  | .neg input => -input.coefficient
  | .scale factor input => factor * input.coefficient

/-- Evaluate the original finite integrand construction at one retained exponential reading. -/
@[expose] def evaluate (reading : Basic.Canonical) : Integrand → Basic.Canonical
  | .exponential => reading
  | .add left right => left.evaluate reading + right.evaluate reading
  | .neg input => -input.evaluate reading
  | .scale factor input => factor * input.evaluate reading

/-- The computed coefficient preserves every original finite integrand reading. -/
theorem evaluate_eq_coefficient (integrand : Integrand) (reading : Basic.Canonical) :
    integrand.evaluate reading = integrand.coefficient * reading := by
  induction integrand with
  | exponential => exact (Basic.one_mul reading).symm
  | add left right leftEq rightEq =>
    change left.evaluate reading + right.evaluate reading = (left.coefficient + right.coefficient) * reading
    rw [leftEq, rightEq]
    ring1
  | neg input inductionHypothesis =>
    change -input.evaluate reading = -input.coefficient * reading
    rw [inductionHypothesis]
    ring1
  | scale factor input inductionHypothesis =>
    change factor * input.evaluate reading = (factor * input.coefficient) * reading
    rw [inductionHypothesis, Basic.mul_assoc]

/-- Equal computed coefficients prove the supported integrand identity for every original reading. -/
theorem evaluate_eq_of_coefficients {left right : Integrand}
    (same : left.coefficient = right.coefficient) (reading : Basic.Canonical) :
    left.evaluate reading = right.evaluate reading := by
  rw [left.evaluate_eq_coefficient reading, right.evaluate_eq_coefficient reading, same]

end Integrand
end Purelib.Integration.Exponential
end
