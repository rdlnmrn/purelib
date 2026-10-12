module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Basic
public import Purelib.RootIsolation.Owner.Family.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Owner.Local.Basic
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

namespace Purelib.RootIsolation.Owner.Family.Basic
open Purelib.Data.Gaussian
namespace OwnerFamily

/-- Forget the global Paper-I support/remainder partition while retaining its
exact degree-indexed root-owner family. -/
def ofResult
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      FTA.Squarefree.AdapterResult p) :
    Owner.Family.Basic.OwnerFamily p p.natDegree where
  owner index :=
    { box := (result.trackAt index).initial.box
      proper := (result.trackAt index).initial.proper
      clearance := (result.trackAt index).initial.clearance
      rawWindingFour := (result.trackAt index).initial.rawWindingFour }
  pairwiseSeparated := result.trackAt_pairwiseSeparated
end OwnerFamily

end Purelib.RootIsolation.Owner.Family.Basic

end
