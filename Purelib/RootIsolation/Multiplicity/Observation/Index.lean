module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
public import Purelib.RootIsolation.Multiplicity.Observation.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.FTA.Squarefree.Basic

open Purelib.Polynomial

section
public section

/-!
# CCL-2 data for the rational-function argument principle

Paper I returns exact rational sites or independently shrinking zero/pole
tracks after finite cancellation.  This module adds CCL observations to those
existing results without duplicating any RFAP isolation or winding proof.
-/

namespace Purelib.RootIsolation.Multiplicity.Observation.Index

/-- Finite site index inside one factor observation.  A linear observation
has its single displayed rational site; a higher observation retains the
degree-indexed family of independently shrinking tracks. -/
@[expose] def ObservationIndex
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries} :
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context) →
      Type
  | .exact _ _ _ => Unit
  | .higher _ _ => Fin context.focus.part.polynomial.natDegree

open Purelib.RootIsolation
/-- Displayed finite enumeration of every site inside one exact or
higher-degree factor observation. -/
@[expose] def observationIndices
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context) :
    List (Multiplicity.Observation.Index.ObservationIndex observation) := by
  cases observation with
  | exact root degree oppositeAtRoot => exact [Unit.unit]
  | higher boxes degree => exact List.ofFn id

/-- The displayed observation index list contains every exact or higher
site. -/
theorem mem_observationIndices
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite}
    {context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext input.entries}
    (observation :
      Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput.FactorObservation input context)
    (index : Multiplicity.Observation.Index.ObservationIndex observation) :
    index ∈ Multiplicity.Observation.Index.observationIndices observation := by
  cases observation with
  | exact root degree oppositeAtRoot =>
      cases index
      change Unit.unit ∈ [Unit.unit]
      exact Purelib.Data.List.Membership.mem_singleton.mpr rfl
  | higher boxes degree =>
      change index ∈ List.ofFn id
      exact Purelib.Data.List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩
end Purelib.RootIsolation.Multiplicity.Observation.Index

end
