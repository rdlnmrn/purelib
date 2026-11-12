module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Observation.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Basic
import Purelib.RootIsolation.Multiplicity.Observation.Index
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Progressive.Cursor.Request
public import Purelib.Data.CCL.Transducer.Machine.History
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Name
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Numerical
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (FactorObservation)
open Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic (ObservationCCL)
open Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Basic (ObservationPersistentState)
open Purelib.RootIsolation.Multiplicity.Observation.Index (ObservationIndex)
open Purelib.Data.CCL.Progressive

section
@[expose] public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Request

/-- Assemble the original persistent observation request from its exact retained numerical and cursor results.

Both replies retain this same observation, attachment, dependent site index,
predecessor, radius and bit count. The numerical validity law consumes the
returned state; neither original request is repeated by this constructor.
-/
def fromRefinements {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries} (observation : FactorObservation input context)
    (data : ObservationCCL observation) (index : ObservationIndex observation)
    (current : ObservationPersistentState observation data index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    (numerical : { state : Numerical.ObservationNumericalState observation data index //
      state = Numerical.refine observation data index current.numerical epsilon positive })
    (cursor : { state : Cursor.Request.State (Name.observationArithmeticName observation data index).process
        (Name.observationArithmeticName observation data index).state //
      state = current.cursor.request (epsilon ^ 2) (Fraction.Order.Arithmetic.pow_pos_direct positive 2) count }) :
    ObservationPersistentState observation data index :=
  { numerical := numerical.val
    numericalValid := by
      rewrite [numerical.property]
      exact Numerical.refine_valid observation data index current.numerical current.numericalValid epsilon positive
    cursor := cursor.val }

/-- One persistent zero/pole-site request. -/
def observationPersistentRequest
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation)
    (index : Multiplicity.Observation.Index.ObservationIndex observation)
    (current : Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState observation data index)
    (epsilon : Fraction.Rational)
      (positive : 0 < epsilon) (count : Nat) :
    Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState observation data index :=
  let epsilonSqPositive :=
    Fraction.Order.Arithmetic.pow_pos_direct positive 2
  let numerical := Numerical.refine observation data index current.numerical epsilon positive
  let cursor := current.cursor.request (epsilon ^ 2) epsilonSqPositive count
  fromRefinements observation data index current epsilon positive count ⟨numerical, rfl⟩ ⟨cursor, rfl⟩
end Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Request

end

public section

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Request

open Purelib.Data.CCL.Transducer (Machine)

variable {source opposite : CoefficientPolynomial} {input : PositiveSideInput source opposite}
  {context : PositiveContext input.entries}

/-- Exact retained numerical and cursor replies reconstruct the complete original persistent observation request. -/
theorem fromRefinements_eq_request (observation : FactorObservation input context) (data : ObservationCCL observation)
    (index : ObservationIndex observation) (current : ObservationPersistentState observation data index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    (numerical : { state : Numerical.ObservationNumericalState observation data index //
      state = Numerical.refine observation data index current.numerical epsilon positive })
    (cursor : { state : Cursor.Request.State (Name.observationArithmeticName observation data index).process
        (Name.observationArithmeticName observation data index).state //
      state = current.cursor.request (epsilon ^ 2) (Fraction.Order.Arithmetic.pow_pos_direct positive 2) count }) :
    fromRefinements observation data index current epsilon positive count numerical cursor =
      observationPersistentRequest observation data index current epsilon positive count := by
  rcases numerical with ⟨numerical, numericalEq⟩
  rcases cursor with ⟨cursor, cursorEq⟩
  cases numericalEq
  cases cursorEq
  rfl

/-- Handle the original indexed persistent observation request through its retained numerical action and cursor history.

Exact sites preserve their original unit numerical state without invoking a
root action. Higher sites consume their actual original track replies. The
returned state keeps this same observation, attachment and site index, while
the actual original history retains the cursor's source, caches and payment.
-/
def withRequest {m : Type → Type} [Monad m] {α : Type} {initial : Machine.Snapshot}
    (observation : FactorObservation input context) (data : ObservationCCL observation)
    (index : ObservationIndex observation) (execute : Numerical.Handler m observation data index)
    (current : ObservationPersistentState observation data index) (history : Machine.History initial)
    (cursorEq : history.current.machine = current.cursor.machine)
    (sourceEq : history.current.source = (Name.observationArithmeticName observation data index).process)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    (use : (next : ObservationPersistentState observation data index) →
      next = observationPersistentRequest observation data index current epsilon positive count →
      (retained : Machine.History initial) → retained.current.machine = next.cursor.machine →
        retained.current.source = (Name.observationArithmeticName observation data index).process → m α) : m α := do
  let numerical ← Numerical.refineWith observation data index execute current.numerical epsilon positive
  have epsilonSqPositive := Fraction.Order.Arithmetic.pow_pos_direct positive 2
  Machine.History.withRequest (Numerical.processStateHandler observation data index execute)
    (Numerical.processHandler observation data index execute) history sourceEq (epsilon ^ 2) epsilonSqPositive count
    fun retained same retainedSource =>
      have machineEq : retained.current.machine =
          (current.cursor.request (epsilon ^ 2) epsilonSqPositive count).machine :=
        ((congrArg (fun value : Machine.History initial => value.current.machine) same).trans
          (history.request_machine (epsilon ^ 2) epsilonSqPositive count)).trans
          (congrArg (fun machine => Cursor.Request.Machine.refineCylinder
            (Machine.Advance.advance machine count) (epsilon ^ 2) epsilonSqPositive) cursorEq)
      let cursor := current.cursor.ofRequestMachine (epsilon ^ 2) epsilonSqPositive count
        retained.current.machine machineEq
      let next := fromRefinements observation data index current epsilon positive count numerical cursor
      use next (fromRefinements_eq_request observation data index current epsilon positive count numerical cursor)
        retained (machineEq.trans (congrArg Cursor.Request.State.machine cursor.property).symm) retainedSource

end Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Request

end
