module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Multiplicity.Observation.Index
public import Purelib.RootIsolation.Multiplicity.Side.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.RootIsolation.Multiplicity.Family.Basic

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

namespace Purelib.RootIsolation.Multiplicity.Side.Index

/-- Finite dependent index of every exact or higher-track site on one reduced
cofactor side.  A constant side has no sites. -/
@[expose] def SideIndex
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} :
    (side : Multiplicity.Side.Basic.SideResult source opposite) → Type
  | .constant _ _ _ => Empty
  | .positive input family =>
      Sigma fun index : Fin input.contexts.length =>
        Multiplicity.Observation.Index.ObservationIndex (family.observationAt index)

/-- Displayed finite enumeration of every exact or higher-track site on one
reduced cofactor side. -/
@[expose] def sideIndices
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite) :
    List (Multiplicity.Side.Index.SideIndex side) := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact []
  | positive input family =>
      exact (List.ofFn id).flatMap fun index =>
        (Multiplicity.Observation.Index.observationIndices (family.observationAt index)).map fun site =>
          ⟨index, site⟩

/-- The displayed side index list contains every site on that side. -/
theorem mem_sideIndices
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite)
    (index : Multiplicity.Side.Index.SideIndex side) : index ∈ Multiplicity.Side.Index.sideIndices side := open Purelib
      in by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero => exact nomatch index
  | positive input family =>
      rcases index with ⟨factor, site⟩
      change _ ∈ (List.ofFn id).flatMap _
      apply Data.List.Flatten.mem_flatMap.mpr
      refine ⟨factor, ?_, ?_⟩
      · exact Purelib.Data.List.OfFn.Basic.mem_ofFn.mpr ⟨factor, rfl⟩
      · exact Data.List.Map.mem_map.mpr
          ⟨site, Multiplicity.Observation.Index.mem_observationIndices (family.observationAt factor) site,
            rfl⟩

/-- Multiplicity attached to a displayed exact or higher-track site.  Every
site inside one squarefree basis factor carries that factor's multiplicity. -/
@[expose] def sideMultiplicity
    {source opposite : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    (side : Multiplicity.Side.Basic.SideResult source opposite) :
    Multiplicity.Side.Index.SideIndex side → Nat := by
  cases side with
  | constant sourceNonzero degreeZero oppositeNonzero =>
      intro index
      exact nomatch index
  | positive input family =>
      intro index
      exact (input.contexts.get index.1).focus.multiplicity
end Purelib.RootIsolation.Multiplicity.Side.Index

end
