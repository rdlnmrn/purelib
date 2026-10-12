module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Observation.Basic
import Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Name
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Numerical
import Purelib.RootIsolation.Multiplicity.Observation.Index
import Purelib.Approximation.Gaussian.Name.Basic

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Basic

set_option genInjectivity false in
/-- Uniform persistent site state.  Its cursor is never restarted. -/
structure ObservationPersistentState
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation)
    (index : Multiplicity.Observation.Index.ObservationIndex observation) where
  /-- The actual numerical state at this retained observation index. -/ numerical :
    Multiplicity.Observation.CCL.Numerical.ObservationNumericalState observation data index
  /-- The retained numerical box refines its original initial box; exact sites have no box obligation. -/ numericalValid
    : Multiplicity.Observation.CCL.Numerical.ObservationNumericalValid observation data index numerical
  /-- The persistent cursor of the exact arithmetic process and starting state associated with this original site. -/
    cursor : Data.CCL.Progressive.Cursor.Request.State
    (Multiplicity.Observation.CCL.Name.observationArithmeticName observation data index).process
    (Multiplicity.Observation.CCL.Name.observationArithmeticName observation data index).state

constructive_injectivity ObservationPersistentState

/-- Initialize a persistent site from the retained numerical state and arithmetic process.

The cursor begins at the original process state, while the numerical component retains either the exact site or its
original indexed winding track. -/
@[expose] def observationPersistentInitial
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (data : Multiplicity.Observation.CCL.Basic.ObservationCCL observation)
    (index : Multiplicity.Observation.Index.ObservationIndex observation) :
    ObservationPersistentState observation data index := open
      Purelib.Geometry.Rational in by
  refine
    { numerical := Multiplicity.Observation.CCL.Numerical.observationNumericalInitial observation data index
      numericalValid := ?_
      cursor := Data.CCL.Progressive.Cursor.Request.State.initial
        (Multiplicity.Observation.CCL.Name.observationArithmeticName observation data index).process
        (Multiplicity.Observation.CCL.Name.observationArithmeticName observation data index).state }
  cases observation with
  | exact root degree oppositeAtRoot => exact True.intro
  | higher boxes degree => exact Box.refines_refl _
end Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Basic

end
