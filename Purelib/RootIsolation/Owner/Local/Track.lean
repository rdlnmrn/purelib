module

import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Tactic.Ring
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

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

namespace Purelib.RootIsolation.Owner.Local.Basic
open Purelib.Data.Gaussian
namespace LocalOwner

/-- Regard the local owner as a winding-one initial state whose ambient is
the owner box itself. -/
def initialState {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (owner : Owner.Local.Basic.LocalOwner p)
    :
    State.WindingOne.Basic.WindingOneState p owner.box where
  box := owner.box
  refinesAmbient := Box.refines_refl owner.box
  proper := owner.proper
  clearance := owner.clearance
  rawWindingFour := owner.rawWindingFour
  ambientLeftClearance := Clearance.Box.Boundary.Lines.leftOfBoundary owner.clearance
  ambientRightClearance := Clearance.Box.Boundary.Lines.rightOfBoundary owner.clearance
  ambientBottomClearance := Clearance.Box.Boundary.Lines.bottomOfBoundary owner.clearance
  ambientTopClearance := Clearance.Box.Boundary.Lines.topOfBoundary owner.clearance
end LocalOwner

end Purelib.RootIsolation.Owner.Local.Basic

end

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

namespace Purelib.RootIsolation.Owner.Local.Basic
open Purelib.Data.Gaussian
namespace LocalOwner

/-- Total finite shrinking program generated from one local owner. -/
def track
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (owner :
      Owner.Local.Basic.LocalOwner p)
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p) :
    Track.Basic.WindingOneTrack p owner.box :=
  let input : RootIsolation.FTA.Squarefree.Input p := ⟨squarefree, degreeAtLeastTwo⟩
  Track.Newton.Build.ofInitial degreeAtLeastTwo squarefree input.elimination
    owner.initialState

end LocalOwner

end Purelib.RootIsolation.Owner.Local.Basic

end
