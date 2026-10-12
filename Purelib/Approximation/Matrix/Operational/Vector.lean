module
public import Purelib.Approximation.Gaussian.Vector.Operational.Basic
public import Purelib.Approximation.Matrix.Operational.Types
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Vector.Basic

open Purelib.Approximation.Gaussian.Vector.Operational.Basic (RawPeriodVector)

open Purelib

open Purelib.Approximation.Gaussian.Vector

open Purelib.Approximation.Matrix.Operational.Types

open Purelib.Riemann.Periods

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Approximation.Matrix.Operational.Vector

/-- Repeat a period vector as both columns of a square named matrix. This lets the existing synchronized square-matrix
algebra act on a vector without introducing a second matrix representation. -/
def replicatedPeriods (periods :
  RawPeriodVector) : NamedMatrix2 :=
  LinearAlgebra.Matrix.matrixOfFn fun row _ => periods row

/-- Every column of the replicated matrix retains the original period-vector entry. -/
@[simp] theorem replicatedPeriods_apply (periods :
  RawPeriodVector)
    (row column : Fin 2) : replicatedPeriods periods row column = periods row :=
  LinearAlgebra.Matrix.matrixOfFn_apply _ _ _

/-- Replicating pointwise equivalent period vectors gives equivalent named matrices. -/
def replicatedPeriods_respects {left right :
  RawPeriodVector}
    (equivalent : Operational.Basic.VectorEquivalent left right) :
    PeriodMatrix.MatrixEquivalent
      (replicatedPeriods left)
        (replicatedPeriods right) := by
  intro row column
  rw [replicatedPeriods_apply,
    replicatedPeriods_apply]
  exact equivalent row
end Purelib.Approximation.Matrix.Operational.Vector

end
