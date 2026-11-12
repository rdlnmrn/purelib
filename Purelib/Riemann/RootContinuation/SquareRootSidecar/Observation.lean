module

public import Purelib.Riemann.RootContinuation.SquareRootSidecar
public import Purelib.Approximation.Gaussian.Observation.Observer.Source
import Purelib.NumberTheory.SquareClass.Gaussian.Nonsquare

/-!
# Numerical projection of certified square-root channels

The numerical projection executes the original coherent channel's process
and initial state. Its finite transcript has a valid rational continuation.
The square identity and root owner remain separate retained source evidence;
a rational continuation does not acquire an exact square-root equation.
-/

public section

namespace Purelib.Riemann.RootContinuation.SquareRootSidecar

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.NumberTheory.SquareClass.Gaussian

namespace WithSidecar

/-- An exact Gaussian-rational channel cannot carry the operational square-root identity with coefficient two. -/
theorem excludes_exact_square_two (point : Basic.Canonical) :
    SquareRootProvenance.SquareIdentity (Name.Coherent.CoherentNamed.Coherence.exact point) 2 → False :=
  fun identity => Nonsquare.mul_self_ne_two point (SquareRootProvenance.squareIdentity_exact_eq identity)

/-- Execute finite numerical control on the original retained channel and construct its valid rational continuation. -/
def continueNumerically (input : WithSidecar) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    Observation.Observer.Source.RationalExecution input.channel.name.process input.channel.name.state
      control registers fuel :=
  Observation.Observer.Source.continueExecution input.channel.name.process input.channel.name.state
    control registers fuel

private theorem forget_execution_specification (input : WithSidecar)
    (control : List Observation.Observer.Frame) (registers : List Observation.Observer.Value) (fuel : Nat) :
    input.forget.continueNumerically control registers fuel =
      input.continueNumerically control registers fuel :=
  rfl

/-- Forgetting symbolic provenance preserves the complete numerical producer, trace and rational continuation. -/
theorem forget_execution (input : WithSidecar) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    input.forget.continueNumerically control registers fuel =
      input.continueNumerically control registers fuel :=
  forget_execution_specification input control registers fuel

/-- The numerical projection has the same complete adaptive execution at its constructed rational continuation. -/
theorem numerical_projection (input : WithSidecar) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    let result := input.continueNumerically control registers fuel
    Observation.Observer.execute control registers fuel result.continuation.code.interpret =
      result.execution.numerical :=
  (input.continueNumerically control registers fuel).same_execution

/-- A Gaussian-rational continuation of a square-root-of-two channel cannot retain its exact root equation. -/
theorem excludes_square_two (input : WithSidecar) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    let result := input.continueNumerically control registers fuel
    let point := result.continuation.code.point
    point * point ≠ (2 : Basic.Canonical) :=
  Nonsquare.mul_self_ne_two (input.continueNumerically control registers fuel).continuation.code.point

/-- The actual finite continuation name cannot retain the operational square-root identity with coefficient two. -/
theorem excludes_continuation_square_two (input : WithSidecar)
    (control : List Observation.Observer.Frame) (registers : List Observation.Observer.Value) (fuel : Nat) :
    let result := input.continueNumerically control registers fuel
    SquareRootProvenance.SquareIdentity (result.continuation.code.named result.continuation.valid) 2 → False := by
  intro result identity
  exact Nonsquare.mul_self_ne_two result.continuation.code.point
    (SquareRootProvenance.squareIdentity_constant_eq identity
      (result.continuation.code.named_sample result.continuation.valid))

end WithSidecar

end Purelib.Riemann.RootContinuation.SquareRootSidecar

end
