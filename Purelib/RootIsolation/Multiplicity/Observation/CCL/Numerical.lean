module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Observation.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.Index
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (FactorObservation)
open Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic (ObservationCCL)
open Purelib.RootIsolation.Multiplicity.Observation.Index (ObservationIndex)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL.Numerical

/-! ## Persistent per-observation requests -/

/-- Numerical component paired with one persistent arithmetic cursor.  Exact
rational sites need no shrinking box; higher sites retain the actual Paper-I
winding state. -/
def ObservationNumericalState
    {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation :
      FactorObservation input context)
    (data : ObservationCCL observation) :
    ObservationIndex observation → Type := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      intro _index
      exact Unit
  | higher boxes degree =>
      intro index
      exact State.WindingOne.Basic.WindingOneState
        context.focus.part.polynomial
        (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox context.focus.part.polynomial)

/-- Initialize the retained numerical component from the original site observation.

An exact site has the unit state; a higher site uses the actual initial winding-one state of its retained indexed track.
-/
def observationNumericalInitial
    {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation :
      FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) :
    ObservationNumericalState observation data index := by
  cases observation with
  | exact root degree oppositeAtRoot => exact Unit.unit
  | higher boxes degree => exact (data.trackAt index).initial

/-- The optional current box.  `none` means that the observation is already
an exact displayed rational site. -/
def observationNumericalBox?
    {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation :
      FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) :
    ObservationNumericalState observation data index → Option Box
      := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      intro _state
      exact none
  | higher boxes degree =>
      intro state
      exact some state.box

/-- Proof that a higher numerical component remains below its initial
isolating box.  The exact branch has no numerical obligation. -/
def ObservationNumericalValid
    {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation :
      FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation)
    (state : ObservationNumericalState observation data index) : Prop := by
  cases observation with
  | exact root degree oppositeAtRoot => exact True
  | higher boxes degree =>
      exact state.box.Refines (data.trackAt index).initial.box
end Purelib.RootIsolation.Multiplicity.Observation.CCL.Numerical

end
