module
public import Purelib.Data.List.Map.Nonempty
import Purelib.Data.List.Pairwise
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
public import Purelib.RootIsolation.FTA.Multiplicity.Basic
public import Purelib.RootIsolation.FTA.Positive.Build
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
# Box-only general-polynomial isolation after squarefree preprocessing

This is the Paper-I general-polynomial layer.  It computes the exact
pairwise-coprime positive multiplicity basis and runs the standalone box
theorem once for every displayed basis factor.  No finite-name or cylinder
module is imported.
-/

namespace Purelib.RootIsolation.FTA.Multiplicity.Build

/-- Run the positive-degree box construction for the exact squarefree factor of a retained positive multiplicity entry.
-/
def isolateBoxFactor (entry :
  Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry) :
  FTA.Multiplicity.Basic.BoxFactor :=
  { entry := entry
    result := FTA.Positive.Build.provePositive
      { squarefree := entry.factor.squarefree
        degreePositive := entry.factor.degreePositive } }

/-- Run the standalone box theorem once for each positive multiplicity-basis
factor. -/
def isolateByBoxes (p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) :
  FTA.Multiplicity.Basic.BoxResult p :=
  match _preprocessing : Dense.Gaussian.Squarefree.Decomposition.Compute.preprocess p with
  | .zero certificate => .zero certificate
  | .constant nonzero degreeZero => .constant nonzero degreeZero
  | .positive positive =>
      let entries := positive.decomposition.positiveMultiplicityEntries
      .positive positive (entries.map isolateBoxFactor)
        (Data.List.Map.Nonempty.map_ne_nil isolateBoxFactor
          positive.decomposition.positiveMultiplicityEntries_nonempty)
        (by
          apply Data.List.Pairwise.pairwise_map.mpr
          apply List.Pairwise.imp (R := fun left right =>
            Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation left.part right.part) ?_
              positive.decomposition.positiveMultiplicityEntries_pairwise
          intro left right related
          simpa only [isolateBoxFactor, FTA.Multiplicity.Basic.BoxFactor.factor,
            Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry.factor,
            Polynomial.Dense.Gaussian.Squarefree.Part.toFactor,
            Dense.Gaussian.Squarefree.Part.Factor.toPart, -eq_self, -iff_self] using related)

end Purelib.RootIsolation.FTA.Multiplicity.Build

end
