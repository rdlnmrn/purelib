module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Ownership
import Purelib.RootIsolation.Curve.Boundary.Event.Ownership
public import Purelib.RootIsolation.Curve.Boundary.Winding.Budget
import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Control
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data.Rat

open Purelib

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

namespace Purelib.RootIsolation.Curve.Boundary.Winding.Containment
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-- Once an initial rational sample selects a winding state with the common
target, every non-pole rational point in that complete retained child remains
inside the same state.  The proof combines the sample's clearance-quarter
residual margin with the child's direct projective diameter bound. -/
theorem controlledChild_inside_owner
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (classified : Curve.Boundary.Winding.Budget.ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      Curve.Boundary.Complete.Ownership.ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (Curve.Boundary.Winding.Budget.windingTarget (boundary := boundary) squarefree family)
          classified.entry)
    {parameter : Fraction.Rational}
    (parameterInside :
      classified.entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      classified.entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0) :
    (family.stateAtBoxIndex owner.index).box.Contains
      (classified.entry.parent.parent.chart.parameterization.curve.point
        parameter) := open Purelib.Data in by
  let state := family.stateAtBoxIndex owner.index
  let point := classified.entry.parent.parent.chart.parameterization.curve.point
    owner.parameter
  have pointInside : state.box.Contains point := by
    rw [← family.boxAt_eq owner.index]
    exact owner.pointInside
  have residualSmall : Data.Gaussian.Norm.Basic.normSq
      (p.eval point) < state.clearance.bound / 4 :=
    (owner.residual_lt
      (Curve.Boundary.Winding.Budget.windingTarget_pos (boundary := boundary) squarefree family)).trans_le
      ((Curve.Boundary.Winding.Budget.windingTarget_le_clearanceQuarter
          (boundary := boundary) squarefree family).trans
        (family.clearanceTarget_quarter_le_stateAt owner.index))
  have margins := state.clearance.residualInteriorMargins pointInside
    residualSmall
  exact
    Curve.Boundary.Event.Ownership.controlled_event_contains_of_uniform_strip
      (Curve.Boundary.Winding.Budget.windingTarget_pos (boundary := boundary) squarefree family)
      classified.entry state.box
      state.clearance.residualInteriorRadius_pos owner.parameter
      owner.parameterInside owner.denominatorNonzero pointInside margins.1
      margins.2.1 margins.2.2.1 margins.2.2.2
      ((Curve.Boundary.Winding.Budget.windingTarget_le_interiorGap
          (boundary := boundary) squarefree family).trans
        (family.interiorGapTarget_le_stateAt owner.index))
      parameterInside denominatorNonzero
end Boundary

end Purelib.RootIsolation.Curve.Boundary.Winding.Containment

end
