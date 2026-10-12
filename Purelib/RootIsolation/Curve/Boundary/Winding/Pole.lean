module
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Chordal.Box.Interior
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.RationalCharts.Box.Exclusion
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Basic
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Winding.Budget
import Purelib.RootIsolation.Curve.Event.Profile.Classification
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Denominator
import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Control
import Purelib.RootIsolation.Curve.Boundary.Complete.Ownership
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial.Dense.Rational.Factorization (ConditionRelation)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

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

namespace Purelib.RootIsolation.Curve.Boundary.Winding.Pole
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {reference : LinearAlgebra.Coordinates2.Matrix.GaussianMatrix} {current :
  Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-- If the finite denominator relation of a retained child is the equality
branch, every displayed rational non-pole parameter in that child lies
outside every finite winding box.  This uses only the explicit condition
factorization and a uniform rational residual bound; it does not assert that
the profile factor has a zero. -/
theorem pole_child_excludes_state
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (classified : Curve.Boundary.Winding.Budget.ClassifiedChild (boundary := boundary) squarefree family)
    (cofactor :
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (factorization :
      Polynomial.Dense.Rational.Factorization
        (Curve.Coordinates.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve)
        classified.entry.parent.event.1.profile.factor.polynomial cofactor)
    (relationEq :
      (Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
        classified.entry.parent.event.1).relation =
          ConditionRelation.equality
            cofactor factorization)
    (index : Fin family.boxes.length)
    (parameter : Fraction.Rational)
    (inside : classified.entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      classified.entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0) :
    ¬(family.stateAtBoxIndex index).box.Contains
      (classified.entry.parent.parent.chart.parameterization.curve.point
        parameter) := by
  let denominatorRelation :=
    Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
      classified.entry.parent.event.1
  have relationMember :
      (⟨Curve.Coordinates.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve,
        ConditionRelation.equality
          cofactor factorization⟩ :
        Curve.Event.Profile.Classification.ProfileRelation
          classified.entry.parent.event.1) ∈
        classified.entry.parent.event.1.profile.relations := by
    have member := denominatorRelation.member
    rw [relationEq] at member
    exact member
  have conditionSmall :=
    classified.entry.equality_condition_eval_sq_lt
      (Curve.Boundary.Winding.Budget.windingTarget_pos (boundary := boundary) squarefree family)
      (Curve.Coordinates.denominatorNormSq
        classified.entry.parent.parent.chart.parameterization.curve)
      cofactor factorization relationMember parameter inside
  have poleSmall :
      (Curve.Coordinates.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve).eval
            parameter ^ 2 <
        (classified.entry.parent.parent.chart.parameterization.weightLower *
          Geometry.Projective.Chordal.Box.Interior.infinityBoxGap
            (family.boxes.get index)) ^ 2 :=
    conditionSmall.trans_le
      ((Curve.Boundary.Winding.Budget.windingTarget_le_poleExclusion
          (boundary := boundary) squarefree family).trans
        (Curve.Boundary.Winding.Budget.poleExclusionTarget_le (boundary := boundary) family
          classified.entry.parent classified.entry.parentMember index))
  have excluded :=
    Geometry.Projective.RationalCharts.Box.Exclusion.denominator_residual_excludes_box
      classified.entry.parent.parent.chart (family.boxes.get index) parameter
      denominatorNonzero poleSmall
  rw [family.boxAt_eq index] at excluded
  exact excluded

/-- The same finite pole classification excludes the whole dispatched
boundary box.  This is the form consumed by the complete affine resolver. -/
theorem pole_child_excludes_current
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (family : State.WindingOne.Family.Basic.WindingFamily p ambient)
    (classified : Curve.Boundary.Winding.Budget.ClassifiedChild (boundary := boundary) squarefree family)
    (cofactor :
      Polynomial.Dense.BoundaryFactorization.CoefficientPolynomial)
    (factorization :
      Polynomial.Dense.Rational.Factorization
        (Curve.Coordinates.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve)
        classified.entry.parent.event.1.profile.factor.polynomial cofactor)
    (relationEq :
      (Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
        classified.entry.parent.event.1).relation =
          ConditionRelation.equality
            cofactor factorization)
    (parameter : Fraction.Rational)
    (inside : classified.entry.child.cell.interval.Contains parameter)
    (denominatorNonzero :
      classified.entry.parent.parent.chart.parameterization.curve.denominatorAt
        parameter ≠ 0) :
    ¬current.Contains
      (classified.entry.parent.parent.chart.parameterization.curve.point
        parameter) := by
  let denominatorRelation :=
    Curve.Event.Profile.Complete.Denominator.profileDenominatorRelation
      classified.entry.parent.event.1
  have relationMember :
      (⟨Curve.Coordinates.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve,
        ConditionRelation.equality
          cofactor factorization⟩ :
        Curve.Event.Profile.Classification.ProfileRelation
          classified.entry.parent.event.1) ∈
        classified.entry.parent.event.1.profile.relations := by
    have member := denominatorRelation.member
    rw [relationEq] at member
    exact member
  have conditionSmall :=
    classified.entry.equality_condition_eval_sq_lt
      (Curve.Boundary.Winding.Budget.windingTarget_pos (boundary := boundary) squarefree family)
      (Curve.Coordinates.denominatorNormSq
        classified.entry.parent.parent.chart.parameterization.curve)
      cofactor factorization relationMember parameter inside
  have poleSmall :
      (Curve.Coordinates.denominatorNormSq
          classified.entry.parent.parent.chart.parameterization.curve).eval
            parameter ^ 2 <
        (classified.entry.parent.parent.chart.parameterization.weightLower *
          Geometry.Projective.Chordal.Box.Interior.infinityBoxGap current) ^ 2 :=
    conditionSmall.trans_le
      ((Curve.Boundary.Winding.Budget.windingTarget_le_poleExclusion
          (boundary := boundary) squarefree family).trans
        (Curve.Boundary.Winding.Budget.poleExclusionTarget_le_current (boundary := boundary) family
          classified.entry.parent classified.entry.parentMember))
  exact
    Geometry.Projective.RationalCharts.Box.Exclusion.denominator_residual_excludes_box
      classified.entry.parent.parent.chart current parameter
      denominatorNonzero poleSmall
end Boundary

end Purelib.RootIsolation.Curve.Boundary.Winding.Pole

end
