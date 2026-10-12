module

import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.Owner.Family.Basic
public import Purelib.RootIsolation.Owner.Family.FTA
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Progressive-coefficient polynomial roots

This file starts the effective algebraic-closure layer for coherent CCL
coefficients.  The first step is deliberately independent of root existence:
it packages finite simultaneous coefficient readings and proves the uniform
Horner estimate which turns coefficient accuracy into a constructive Rouché
certificate on a displayed rational box.

Every coefficient observation is an explicitly possible Gaussian-rational
reading of one finite process state.  No completed coefficient, completed
polynomial, root collection, or infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Owner.Family.Basic
open Purelib.Data.Gaussian
namespace OwnerFamily

/-- Degree-indexed owner family specialized to the coefficient table's
displayed degree. -/
def ofTableResult
    (table : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable)
    (result : FTA.Squarefree.AdapterResult table.polynomial) :
    Owner.Family.Basic.OwnerFamily table.polynomial table.degree := by
  rw [← table.polynomial_natDegree]
  exact Owner.Family.Basic.OwnerFamily.ofResult result
end OwnerFamily

end Purelib.RootIsolation.Owner.Family.Basic

end
