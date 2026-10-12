module
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.RootIsolation.Multiplicity.Observation.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.Index
public import Purelib.RootIsolation.FTA.Squarefree.Approximation
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.FTA.Squarefree.Basic

open Purelib.Data.CCL.Transducer (Machine)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side (PositiveSideInput)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput (FactorObservation)
open Purelib.RootIsolation.Multiplicity.Observation.CCL.Basic (ObservationCCL)
open Purelib.RootIsolation.Multiplicity.Observation.Index (ObservationIndex)

open Purelib.Approximation.Gaussian

open Purelib

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

namespace Purelib.RootIsolation.Multiplicity.Observation.CCL.Name

/-- Turn either an exact rational site or one higher shrinking track into the
same productive arithmetic-name interface.  Exact sites use their displayed
rational point; no completed value is extracted from a higher track. -/
def observationArithmeticName
    {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation :
      FactorObservation input context)
    (data : ObservationCCL observation) :
    ObservationIndex observation →
      Name.Basic.Named := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      intro _site
      exact Name.Basic.Named.exact root.point
  | higher boxes degree =>
      intro index
      exact data.arithmeticNameAt index

/-- Advancing the retained arithmetic name by the requested count emits exactly that many symbols and preserves its
existing prefix. -/
theorem observationArithmeticName_productive
    {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation :
      FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) (count : Nat) :
    (observationArithmeticName observation data index).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (observationArithmeticName observation data index).machine
          count).emitted ∧
      (Machine.Advance.advance
        (observationArithmeticName observation data index).machine
        count).emitted.length = count :=
  (observationArithmeticName observation data index).productive count

/-- Every finite advance of the retained arithmetic name is an exact cursor of its original process and state. -/
theorem observationArithmeticName_exact
    {source opposite : CoefficientPolynomial}
    {input : PositiveSideInput source opposite}
    {context : PositiveContext input.entries}
    (observation :
      FactorObservation input context)
    (data : ObservationCCL observation)
    (index : ObservationIndex observation) (count : Nat) :
    let name := observationArithmeticName observation data index
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      name.process name.state
      (Machine.Advance.advance name.machine count) :=
  Name.CCL.Semantics.Named.advance_exact
    (observationArithmeticName observation data index) count
end Purelib.RootIsolation.Multiplicity.Observation.CCL.Name

end
