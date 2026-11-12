module

public import Purelib.Riemann.RootContinuation.SquareRootSidecar.Observation
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Approximation.Gaussian.Observation.Observer
import Purelib.Data.Gaussian.Basic

/-! # Symbolic square-root evidence is excluded from finite numerical rational replacement -/

namespace TestPurelib.RootIsolation.SquareRoot.Observation

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation.SquareRootSidecar

/-- Both actual isolated square-root-of-two sheets have valid finite numerical rational replacements. -/
public theorem numerical_projection (sheet : Fin 2) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    let input := WithSidecar.isolate 2 sheet
    let result := input.continueNumerically control registers fuel
    Observation.Observer.execute control registers fuel result.continuation.code.interpret =
      result.execution.numerical :=
  (WithSidecar.isolate 2 sheet).numerical_projection control registers fuel

/-- The rational witness reproducing either actual root's numerical trace cannot retain its exact root equation. -/
public theorem symbolic_exclusion (sheet : Fin 2) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    let result := (WithSidecar.isolate 2 sheet).continueNumerically control registers fuel
    let point := result.continuation.code.point
    point * point ≠ (2 : Data.Gaussian.Basic.Canonical) :=
  (WithSidecar.isolate 2 sheet).excludes_square_two control registers fuel

/-- Discarding the original root sidecar preserves its complete numerical execution and valid continuation. -/
public theorem forgetting_symbolic_evidence (sheet : Fin 2) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    let input := WithSidecar.isolate 2 sheet
    input.forget.continueNumerically control registers fuel =
      input.continueNumerically control registers fuel :=
  (WithSidecar.isolate 2 sheet).forget_execution control registers fuel

/-- The exact rational replacement cannot retain the same operational square identity as the isolated root. -/
public theorem operational_symbolic_exclusion (sheet : Fin 2) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    let result := (WithSidecar.isolate 2 sheet).continueNumerically control registers fuel
    Riemann.RootContinuation.SquareRootProvenance.SquareIdentity
      (Name.Coherent.CoherentNamed.Coherence.exact result.continuation.code.point) 2 → False :=
  WithSidecar.excludes_exact_square_two
    ((WithSidecar.isolate 2 sheet).continueNumerically control registers fuel).continuation.code.point

/-- The actual history-backed continuation name also excludes the original operational square identity. -/
public theorem retained_continuation_exclusion (sheet : Fin 2) (control : List Observation.Observer.Frame)
    (registers : List Observation.Observer.Value) (fuel : Nat) :
    let result := (WithSidecar.isolate 2 sheet).continueNumerically control registers fuel
    Riemann.RootContinuation.SquareRootProvenance.SquareIdentity
      (result.continuation.code.named result.continuation.valid) 2 → False :=
  (WithSidecar.isolate 2 sheet).excludes_continuation_square_two control registers fuel

end TestPurelib.RootIsolation.SquareRoot.Observation
