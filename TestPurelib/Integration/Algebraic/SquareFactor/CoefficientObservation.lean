module

import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds.Observation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field

/-! # Actual numerator and denominator requests of the retained integrand -/

namespace TestPurelib.Integration.Algebraic.SquareFactor.CoefficientObservation

open Purelib
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Computation.Query

/-- Execute the original prepared coefficient, retaining and replaying both hidden polynomial evaluations. -/
public def run : IO Unit := do
  match PathInput.prepare ⟨[1, 1, 0, 0]⟩ (.original 0) ⟨2, ⟨9 / 4, 0⟩⟩ with
  | .error _ => throw (IO.userError "integrand coverage fixture failed original path preparation")
  | .ok prepared =>
      let computation := CoefficientBounds.Observation.coefficient (1 / 2) ⟨3 / 2, 0⟩
      let original := computation.run (CoefficientBounds.Observation.answer prepared.data)
      let expected := CoefficientBounds.coefficient prepared.data (1 / 2) ⟨3 / 2, 0⟩
      unless decide (original.value = expected) && original.trace.length == 2 do
        throw (IO.userError "integrand lowering changed its original value or dropped evaluator requests")
      let changed := computation.run (Boundary.Trace.overlay original.trace (fun _ => 0))
      unless decide (changed.value = original.value) &&
          decide (changed.trace.map (fun entry => (entry.query, entry.reply)) =
            original.trace.map (fun entry => (entry.query, entry.reply))) do
        throw (IO.userError "outside evaluator changes altered the complete integrand execution")
      match computation.replayExact original.trace with
      | .ok value =>
          unless decide (value = expected) do
            throw (IO.userError "integrand replay lost the original coefficient")
      | .error _ => throw (IO.userError "integrand replay rejected its actual evaluator transcript")
      IO.print "integrand evaluator coverage: original path, both evaluations, exact replay and erasure passed\n"

end TestPurelib.Integration.Algebraic.SquareFactor.CoefficientObservation
