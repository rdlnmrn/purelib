module
import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Init.Prelude

open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)

open Purelib

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition

open Purelib.Approximation.Gaussian.Name

open Purelib.LinearAlgebra.Matrix

section
@[expose] public section

/-!
# Resumable automatic acquisition for stepwise dual words

Each cursor retains completed head and suffix preparations, plus the exact
current denominator search state. Exhausting a budget preserves the cursor;
resumption neither reconstructs earlier outputs nor starts their searches
again. The final preparation is consumed directly by the existing arbitrary
finite-word period theorem.
-/

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached
open Purelib.Riemann.Integration.LegendreModularMonodromy hiding IntegralMatrix

/-- A denominator search with a cached integral matrix and its exact specification.

The retained equality ties the executable matrix to the requested matrix, and the search state is indexed by that
retained matrix and input name. -/
def CachedSearch (tau :
  Coherent.CoherentNamed) (specification : IntegralMatrix) :=
  State.StatePayload
    (fun matrix => matrix = specification) (fun matrix =>
        Approximation.Gaussian.FractionalAction.Integral.Acquisition.State matrix tau)

/-- Cache the requested matrix and initialize its denominator search at the coherent input. -/
def cachedInitial (tau :
  Coherent.CoherentNamed) (matrix : IntegralMatrix) :
  CachedSearch tau matrix :=
  { matrix := matrix
    matrix_eq := rfl
    search := State.initial matrix tau }

/-- Transport a completed cached search preparation to its specified matrix.

The retained matrix equality rebases the dependent denominator type without reconstructing the prepared process. -/
def cachedPreparation {tau :
  Coherent.CoherentNamed} {matrix : IntegralMatrix}
    (state : CachedSearch tau matrix)
    (preparation : Prepared.DenominatorPreparation (fractionalDenominator state.matrix tau)) :
    Prepared.DenominatorPreparation (fractionalDenominator matrix tau) := by
  rw [← state.matrix_eq]
  exact preparation
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Acquisition.Cached

end
