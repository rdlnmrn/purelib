module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Division.Partial.Run
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State

public import Purelib.Examples.Approximation.Gaussian.Provenance.Rational.Cancellation
import Purelib.Riemann.RootContinuation.SquareRootProvenance
public import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Examples.Approximation.Gaussian.Provenance.Rational

@[expose] public section

/-! Isolated square roots and transported exact cancellation provenance. -/

namespace Purelib.Examples.RootIsolation.SquareRoot.Provenance

open Purelib.Riemann.RootContinuation.SquareRootSidecar
open Purelib.Riemann.RootContinuation.SquareRootProvenance
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

/-- The exact Gaussian rational two. -/
def two : Gaussian := ⟨2, 0⟩

/-- The exact Gaussian rational two is nonzero. -/
theorem two_nonzero : two ≠ 0 := by
  decide

/-- The isolated square root retaining its two-sheet owner. -/
def rootTwo (sheet : Fin 2) := isolated
  two sheet

/-- The transported sidecar for an exactly cancelling square-root expression. -/
def cancellationSidecar :
    Sidecar Cancellation.cancellation :=
  zeroSidecar.transport
    Cancellation.cancellationSidecar.equivalent

/-- Every observation of the cancelling square-root expression is zero. -/
def cancellation_observation_zero : Zero.ZeroIdentity
    Cancellation.cancellation :=
  cancellationSidecar.observe.zero_of_small
    cancellationSidecar.square
    (cancellationSidecar.observe.small_of_parameter_zero rfl)

end Purelib.Examples.RootIsolation.SquareRoot.Provenance
