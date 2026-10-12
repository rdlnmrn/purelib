module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Count

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Comparing complete CCL profile children with winding-one states

The complete profile refinement is parameterized by an arbitrary finite
pairwise-separated box family.  This module instantiates that interface with
the boxes carried by explicit finite winding-one states.  Every retained
profile child is then compared with the actual numerical states, not with an
unrelated list of boxes.

An owned result records only a displayed Gaussian-rational curve sample in
one state, together with its small polynomial residual and nonzero derivative.
The sample-owner comparison remains pointwise and is never promoted to root
existence.  A separate affine-family scan preserves the stronger semantics
already computed for each profile: either displayed rational factor zeros are
inside the dispatched box, or the complete rational non-pole event cylinder
is outside it.  Neither alternative asserts that a factor zero exists.
-/

namespace Purelib.RootIsolation.State.WindingOne.Comparison

/-! ## Finite winding and protected-interior geometry -/

/-- Two winding-one boxes strictly inside the same winding-one container
cannot be positively separated.  Otherwise finite winding additivity would
put winding at least eight in a box whose displayed winding is exactly four.
This compares only supplied finite numerical states. -/
theorem not_separated_inside_winding_one
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (container left right : State.WindingOne.Basic.WindingOneState p ambient)
    (leftInside : left.box.StrictInterior container.box)
    (rightInside : right.box.StrictInterior container.box) :
    ¬left.box.Separated right.box := by
  intro separated
  let region : Clearance.Box.Region.ClearRegion p ambient :=
    { box := container.box
      refinesAmbient := container.refinesAmbient
      proper := container.proper
      clearance := container.clearance }
  have atLeastEight :=
    State.WindingOne.Count.region_rawWinding_ge_eight_of_separated
      degreeAtLeastTwo squarefree elimination region left right leftInside
        rightInside separated
  have exactlyFour := container.rawWindingFour
  dsimp only [region] at atLeastEight
  rw [exactlyFour] at atLeastEight
  exact (by decide : ¬(8 : Int) ≤ 4) atLeastEight

end Purelib.RootIsolation.State.WindingOne.Comparison

end
