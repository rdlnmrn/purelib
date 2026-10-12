module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Relation
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.FTA.Squarefree.Basic
public import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.Target
public import Purelib.RootIsolation.Progressive.Owner.FTA
import Purelib.Tactic.Ring
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

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

namespace Purelib.RootIsolation.Progressive.Chamber.Basic
open Purelib.Data.Gaussian
namespace SimpleRootChamber

/-- Public chamber constructor from the complete Paper-I isolation result. -/
def ofResult
    (reference : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable) (degreeAtLeastTwo : 2 ≤
      reference.degree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate reference.polynomial)
    (result : FTA.Squarefree.AdapterResult reference.polynomial)
    (referenceSmall : Dense.Gaussian.Coefficient.Progressive.Table.CoefficientTable.AllowancesLt reference.entries
      (Progressive.Chamber.Target.simpleRootChamberTarget reference squarefree
        (Owner.Family.Basic.OwnerFamily.ofTableResult reference result))) :
    Progressive.Chamber.Basic.SimpleRootChamber reference where
  degreeAtLeastTwo := degreeAtLeastTwo
  squarefree := squarefree
  owners := Owner.Family.Basic.OwnerFamily.ofTableResult reference result
  referenceSmall := referenceSmall
  referenceMaximality := by
    intro familyCount family pairwise
    have bound := result.boxes.maximality family pairwise
    simpa only [reference.polynomial_natDegree] using bound

end SimpleRootChamber

end Purelib.RootIsolation.Progressive.Chamber.Basic

end
