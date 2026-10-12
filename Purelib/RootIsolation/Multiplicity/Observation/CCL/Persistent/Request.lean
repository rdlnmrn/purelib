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

section
@[expose] public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Request

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
    Multiplicity.Observation.CCL.Persistent.Basic.ObservationPersistentState observation data index := by
  let epsilonSqPositive :=
    Fraction.Order.Arithmetic.pow_pos_direct positive 2
  refine
    { numerical := ?_
      numericalValid := ?_
      cursor := current.cursor.request (epsilon ^ 2) epsilonSqPositive count }
  · cases observation with
    | exact root degree oppositeAtRoot => exact Unit.unit
    | higher boxes degree =>
        exact (data.trackAt index).refine current.numerical epsilon positive
  · cases observation with
    | exact root degree oppositeAtRoot => exact True.intro
    | higher boxes degree =>
        exact ((data.trackAt index).nested current.numerical epsilon positive).trans
          current.numericalValid
end Purelib.RootIsolation.Multiplicity.Observation.CCL.Persistent.Request

end
