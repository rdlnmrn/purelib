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

section
@[expose] public section

/-!
# Algebraic provenance regressions

Cover the repeated-zero root, both independently isolated sheets of `Z² - 2`,
retained winding ownership, approximate nonzero candidates on an operationally
zero channel, coefficient-derived observation bounds, and compatibility with
ordinary/manual division. Tests use the proved isolation interface without
kernel-recomputing a large root-isolation trace.
-/

namespace Test.RootIsolation.SquareRoot.Sidecar

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

/-- The isolated square root retains the exact parameter two. -/
theorem rootTwo_parameter (sheet : Fin 2) :
  (rootTwo sheet).2.parameter = two :=
  isolated_parameter two sheet

/-- The nonzero parameter has a prepared square-root sidecar. -/
theorem rootTwo_prepared (sheet : Fin 2) :
    ∃ preparation, (rootTwo sheet).2.decide = .prepared preparation := by
  have nonzero : (rootTwo sheet).2.parameter ≠ 0 := by
    rw [rootTwo_parameter]
    exact two_nonzero
  exact ⟨_, decide_prepared (rootTwo sheet).2.square nonzero⟩

/-- The prepared square-root sidecar retains its isolation owner. -/
theorem rootTwo_retains_owner (sheet : Fin 2) :
    ∃ owner, (rootTwo sheet).2.owner = some owner := by
  unfold rootTwo isolated
  rw [dif_pos two_nonzero]
  exact ⟨_, rfl⟩

/-- The retained observation is not below its nonzero gap. -/
theorem rootTwo_not_small (sheet : Fin 2)
    (observation : Observation (rootTwo sheet).1
      (rootTwo sheet).2.parameter) :
    ¬ Data.Gaussian.Norm.Basic.normSq observation.value <
      separationGap (rootTwo sheet).2.parameter := by
  intro small
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at small
  have zero := observation.parameter_zero_of_small small
  rw [rootTwo_parameter] at zero
  exact two_nonzero zero

/-- The zero square-root request is explicitly excluded. -/
theorem zero_excluded :
    zeroSidecar.decide = .excluded (zero_of_square zeroSidecar.square) :=
  decide_excluded zeroSidecar.square

/-- The zero request has no simple-root owner. -/
theorem zero_has_no_simple_owner : zeroSidecar.owner = none := rfl

/-- The isolated square root of zero is exactly zero. -/
theorem isolated_zero (sheet : Fin 2) :
    (isolated 0 sheet).1 = Coherence.exact 0 := by
  unfold isolated
  rw [dif_neg (not_not_intro rfl)]

/-- Every positive tolerance bounds the zero observation. -/
theorem zero_observation_small :
    Data.Gaussian.Norm.Basic.normSq zeroSidecar.observe.value <
      separationGap zeroSidecar.parameter :=
  zeroSidecar.observe.small_of_parameter_zero rfl

/-- The transported sidecar for an exactly cancelling square-root expression. -/
def cancellationSidecar :
    Sidecar Cancellation.cancellation :=
  zeroSidecar.transport
    Cancellation.cancellationSidecar.equivalent

/-- A genuine nonzero finite candidate does not invalidate a proved zero identity. No pointwise candidate zero law is
smuggled into the sidecar. -/
theorem cancellation_has_nonzero_candidate :
    Cancellation.cancellation.name.process.Possible
      Cancellation.cancellation.name.state (1 : Data.Gaussian.Basic.Canonical) :=
  Cancellation.cancellation_has_nonzero_candidate

/-- The exact cancellation is excluded by the square decision. -/
theorem cancellation_square_excluded :
    ∃ identity, cancellationSidecar.decide = .excluded identity :=
  ⟨_, decide_excluded cancellationSidecar.square⟩

/-- Every observation of the cancelling square-root expression is zero. -/
def cancellation_observation_zero : Zero.ZeroIdentity
    Cancellation.cancellation :=
  cancellationSidecar.observe.zero_of_small
    cancellationSidecar.square
    (cancellationSidecar.observe.small_of_parameter_zero rfl)

/-- Every finite division budget for the cancelling expression is exhausted. -/
theorem cancellation_square_all_budgets (numerator :
  Coherent.CoherentNamed)
    (state : Approximation.Gaussian.Name.Coherent.Refinement.State
      Cancellation.cancellation) (fuel : Nat) :
    ∃ final reachable, Run.attempt numerator
      Cancellation.cancellation state fuel = .exhausted final reachable :=
  Obstruction.Zero.ZeroIdentity.attempt_exhausts cancellation_observation_zero
    numerator state fuel

/-- Forgetting the retained sidecar preserves every emitted observation prefix. -/
theorem forgetting_preserves_prefix (sheet : Fin 2) :
    (WithSidecar.forget ⟨(rootTwo sheet).1, some
      (rootTwo sheet).2⟩).channel.name.machine.emitted =
      (rootTwo sheet).1.name.machine.emitted := rfl

end Test.RootIsolation.SquareRoot.Sidecar

end
