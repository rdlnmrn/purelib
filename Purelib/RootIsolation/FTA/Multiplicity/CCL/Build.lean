module
public import Purelib.Data.List.Map.Nonempty
import Purelib.Data.List.Pairwise
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
public import Purelib.RootIsolation.FTA.Multiplicity.CCL.Basic
public import Purelib.RootIsolation.FTA.Positive.CCL.Build
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.RootIsolation.FTA.Positive.Input

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

namespace Purelib.RootIsolation.FTA.Multiplicity.CCL.Build

/-- Isolate the original positive multiplicity factor and retain its exact occurrence count with the CCL-coupled result.
-/
def isolateCCLFactor (entry :
  Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry) :
  FTA.Multiplicity.CCL.Basic.CCLFactor :=
  { factor := entry.factor
    occurrenceCount := entry.multiplicity
    result := FTA.Positive.CCL.Build.provePositive
      { squarefree := entry.factor.squarefree
        degreePositive := entry.factor.degreePositive } }

/-- Run the CCL-coupled theorem once for each positive multiplicity-basis
factor. -/
def isolateWithCCL (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : FTA.Multiplicity.CCL.Basic.CCLResult p
    :=
  match _preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.preprocess p with
  | .zero certificate => .zero certificate
  | .constant nonzero degreeZero => .constant nonzero degreeZero
  | .positive positive =>
      let entries := positive.decomposition.positiveMultiplicityEntries
      .positive positive (entries.map isolateCCLFactor)
        (Data.List.Map.Nonempty.map_ne_nil isolateCCLFactor
          positive.decomposition.positiveMultiplicityEntries_nonempty)
        (by
          apply Data.List.Pairwise.pairwise_map.mpr
          apply List.Pairwise.imp (R := fun left right =>
            Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation left.part right.part) ?_
              positive.decomposition.positiveMultiplicityEntries_pairwise
          intro left right related
          simpa only [isolateCCLFactor,
            Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry.factor,
            Polynomial.Dense.Gaussian.Squarefree.Part.toFactor,
            Dense.Gaussian.Squarefree.Part.Factor.toPart, -eq_self, -iff_self] using related)

end Purelib.RootIsolation.FTA.Multiplicity.CCL.Build

end
