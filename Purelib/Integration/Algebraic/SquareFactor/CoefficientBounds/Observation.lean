module

public import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
public import Purelib.Computation.Query.Boundary
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Data.Gaussian.Field

/-!
# Displayed evaluations of the original square-factor integrand

The numerator and denominator evaluations used by `coefficient` are separate
requests. Their original path data, orientation and parameter remain fixed
control; each reply is consumed once in the exact successive divisions.
The supplied root is numerical control for this coefficient operation.
Root acquisition and transport have their separate owned interfaces.
-/

public section

namespace Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query

namespace Observation

set_option genInjectivity false in
/-- An original numerator or denominator evaluation at one retained rational path parameter. -/
inductive Question where
  /-- Evaluate the original numerator at this exact path parameter. -/ | numerator (parameter : Coordinate)
  /-- Evaluate the original denominator at this exact path parameter. -/ | denominator (parameter : Coordinate)
  deriving @[expose] DecidableEq

variable {polynomial : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request}
  {prepared : SquareFactor.Prepared polynomial request} {segment : PathInput.Segment}

/-- Read the original retained numerator or denominator evaluation at the displayed parameter. -/
@[expose] def answer (data : PathInput.Data prepared segment) : Question → SquareFactor.Gaussian
  | .numerator parameter => data.numerator.value parameter
  | .denominator parameter => data.denominator.value parameter

/-- Compile the original coefficient's two evaluator calls and consume their exact replies in order. -/
@[expose] def coefficient (parameter : Coordinate) (root : SquareFactor.Gaussian) :
    Protocol Question SquareFactor.Gaussian SquareFactor.Gaussian :=
  (Protocol.query (.numerator parameter)).bind fun numerator =>
    (Protocol.query (.denominator parameter)).map fun denominator => numerator / denominator / root

/-- The complete integrand execution returns the original coefficient and records both actual evaluator replies. -/
theorem recorded_execution (data : PathInput.Data prepared segment)
    (parameter : Coordinate) (root : SquareFactor.Gaussian) :
    (coefficient parameter root).run (answer data) =
      ⟨CoefficientBounds.coefficient data parameter root,
        [⟨.numerator parameter, data.numerator.value parameter⟩,
          ⟨.denominator parameter, data.denominator.value parameter⟩]⟩ := rfl

/-- Changes outside the consumed integrand evaluations preserve the exact coefficient and the complete ordered trace. -/
theorem payload_erasure {Payload : Type} (data : PathInput.Data prepared segment)
    (parameter : Coordinate) (root : SquareFactor.Gaussian) (payload : Payload)
    (outside : Payload → Question → SquareFactor.Gaussian) :
    let computation := coefficient parameter root
    computation.run (Boundary.Trace.overlay (computation.run (answer data)).trace (outside payload)) =
      computation.run (answer data) :=
  Protocol.annotation_erasure (coefficient parameter root) (answer data) payload outside

end Observation

end Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
