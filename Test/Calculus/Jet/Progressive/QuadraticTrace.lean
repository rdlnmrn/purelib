module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Exponential.Horner.Sequence
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.CCL.Request
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Identity
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

open Purelib.Calculus.Jet.Progressive

open Purelib.Approximation

section
@[expose] public section

/-! Changing-input regressions for synchronized quadratic CCL traces and calculations. -/

namespace Test.Calculus.Jet.Progressive.QuadraticTrace
section Trace

/-- The finite exponential Horner approximation at the Gaussian point one.

Its successive samples provide the shared nonconstant input observations for the quadratic trace regression. -/
def exponentialWitnessApproximation :
  Gaussian.Sequence.ApproximationData :=
  Gaussian.Exponential.Horner.Sequence.approximation ⟨1, 0⟩ (by decide)

/-- A small executable regression witness whose input observations are the
successive finite exponential Horner samples. -/
def nonterminatingIdentity :
    Quadratic.Trace exponentialWitnessApproximation.sample :=
  Quadratic.Trace.identityOfGeometricApproximation
    exponentialWitnessApproximation 10
    (by decide) (by intro index; rfl)

/-- The witness really changes between finite stages, so its productive CCL
contract is not merely an exact terminating rational specialization. -/
theorem nonterminatingIdentity_changes :
    exponentialWitnessApproximation.sample 0 ≠
      exponentialWitnessApproximation.sample 1 := by
  decide

/-- Every positive target and finite output count have the retained bitstream and quadratic-law request contract for the
changing identity trace. -/
theorem nonterminatingIdentity_bitstream (target :
  Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    Quadratic.Trace.RequestContract nonterminatingIdentity 0 target positive
      count :=
  Quadratic.Trace.bitstream_and_quadratic_law nonterminatingIdentity 0 target positive count
end Trace

end Test.Calculus.Jet.Progressive.QuadraticTrace

end
