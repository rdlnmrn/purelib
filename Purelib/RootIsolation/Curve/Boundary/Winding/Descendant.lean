module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.SmallWidth
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Family.Search
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Ownership
import Purelib.RootIsolation.Curve.Boundary.Complete.Sample
import Purelib.RootIsolation.Curve.Boundary.Profile.Control
import Purelib.RootIsolation.Curve.Boundary.Profile.Residual
public import Purelib.RootIsolation.Curve.Boundary.Winding.Budget
import Purelib.RootIsolation.Curve.Boundary.Winding.Containment
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Complete.Control
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Basic
import Purelib.RootIsolation.Curve.Event.Profile.Residual.Lift
import Purelib.RootIsolation.State.WindingOne.Family.Clearance

open Purelib.RootIsolation.Curve.Boundary.Complete.Basic (BoundaryCompleteRequestEntry)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.RootIsolation.State.WindingOne.Family.Basic (WindingFamily)

open Purelib.Data

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

namespace Purelib.RootIsolation.Curve.Boundary.Winding.Descendant
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-! ## Total strict-owner/outside classification on one descendant -/

/-- Descendant width whose original-polynomial residual target is the
candidate winding state's own positive boundary clearance. -/
def strictDescendantRequestWidth
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) : Fraction.Rational :=
  Curve.Boundary.Complete.Sample.descendantResidualRequestWidth
    entry windingState.box windingState.clearance.bound

/-- The descendant request tied to the retained state's positive boundary clearance has positive width. -/
theorem strictDescendantRequestWidth_pos
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) :
    0 < strictDescendantRequestWidth entry windingState :=
  Curve.Boundary.Complete.Sample.descendantResidualRequestWidth_pos
    entry windingState.box windingState.clearance.positive

/-- Executable non-pole sample on the selected descendant at the strict-owner
width. -/
def strictDescendantSample
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) :=
  Curve.Boundary.Complete.Sample.nonpoleCompleteRequestDescendantSample
    entry (strictDescendantRequestWidth entry windingState)

/-- Total finite result for one retained event branch and one candidate
winding container.  The inside branch is genuinely strict and carries the
actual residual bound; the outside branch retains the failed rational box
membership test. -/
inductive StrictDescendantClassification
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) where
  /-- The actual descendant sample lies strictly inside the candidate state and satisfies its boundary-clearance
    residual bound. -/ | inside
      (contains : windingState.box.Contains
        (entry.parent.parent.chart.parameterization.curve.point
          (strictDescendantSample entry windingState).parameter))
      (strict : windingState.box.StrictContains
        (entry.parent.parent.chart.parameterization.curve.point
          (strictDescendantSample entry windingState).parameter))
      (residual : Data.Gaussian.Norm.Basic.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          (strictDescendantSample entry windingState).parameter)) <
            windingState.clearance.bound)
  /-- The actual descendant sample fails membership in the candidate state box. -/ | outside
      (proof : ¬windingState.box.Contains
        (entry.parent.parent.chart.parameterization.curve.point
          (strictDescendantSample entry windingState).parameter))

/-- Execute the membership split and use the candidate's finite boundary
clearance to strengthen every owned sample to strict containment. -/
def classifyStrictDescendant
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (windingState : WindingOneState p ambient) :
    StrictDescendantClassification entry windingState := by
  let sample := strictDescendantSample entry windingState
  let point := entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  by_cases contains : windingState.box.Contains point
  · have residual :=
      Curve.Boundary.Complete.Sample.descendant_sample_residual_lt
        entry windingState.box windingState.clearance.positive sample contains
    exact .inside contains
      (windingState.clearance.strictContains_of_residual_lt contains residual)
      residual
  · exact .outside contains

/-! ## One shared strict descendant across the finite winding family -/

/-- One descendant width below every state-box residual width for an
arbitrary supplied positive target. -/
def targetedFamilyDescendantRequestWidth
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (target : Fraction.Rational) : Fraction.Rational :=
  Curve.Boundary.Profile.Control.profileResidualFamilyRequestWidth
    entry.parent family.boxes target

/-- The common family descendant request has positive width for a positive residual target. -/
theorem targetedFamilyDescendantRequestWidth_pos
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    {target : Fraction.Rational} (targetPositive : 0 < target) :
    0 < targetedFamilyDescendantRequestWidth entry family target :=
  Curve.Boundary.Profile.Control.profileResidualFamilyRequestWidth_pos
    entry.parent family.boxes targetPositive

/-- The common non-pole rational sample at an arbitrary family-wide residual
target. -/
def targetedFamilyDescendantSample
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (target : Fraction.Rational) :=
  Curve.Boundary.Complete.Sample.nonpoleCompleteRequestDescendantSample
    entry (targetedFamilyDescendantRequestWidth entry family target)

/-- If the targeted common sample meets a state, its exact original-
polynomial residual is below the caller's common target. -/
theorem targeted_family_descendant_sample_residual_lt
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length)
    {target : Fraction.Rational} (targetPositive : 0 < target)
    (sample :
      Curve.Boundary.Complete.Sample.NonpoleCompleteRequestDescendantSample
        entry (targetedFamilyDescendantRequestWidth entry family target))
    (contains : (family.stateAtBoxIndex index).box.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter)) < target := by
  let coefficient :=
    Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient
      entry.parent (family.stateAtBoxIndex index).box
  let commonWidth := targetedFamilyDescendantRequestWidth entry family target
  let boxWidth :=
    Curve.Boundary.Complete.Sample.descendantResidualRequestWidth
      entry (family.stateAtBoxIndex index).box target
  have commonLeBox : commonWidth ≤ boxWidth := by
    simpa only [commonWidth, boxWidth, targetedFamilyDescendantRequestWidth,
      Curve.Boundary.Complete.Sample.descendantResidualRequestWidth,
      Curve.Boundary.Profile.Control.boxResidualRequestWidth,
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient,
      coefficient, family.boxAt_eq index] using
      Curve.Boundary.Profile.Control.profileResidualFamilyRequestWidth_le_box
        entry.parent family.boxes target index
  have squareOrder : commonWidth ^ 2 ≤ boxWidth ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (targetedFamilyDescendantRequestWidth_pos entry family
        targetPositive).le commonLeBox 2
  have coefficientNonnegative : 0 ≤ coefficient := by
    simpa only [coefficient] using
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient_nonneg
        entry.parent (family.stateAtBoxIndex index).box
  have upper := sample.normSq_eval_point_le_of_inside
    (targetedFamilyDescendantRequestWidth_pos entry family targetPositive)
    (family.stateAtBoxIndex index).box contains
  have boxSmall : coefficient * boxWidth ^ 2 < target := by
    simpa only [boxWidth, coefficient,
      Curve.Boundary.Complete.Sample.descendantResidualRequestWidth,
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient]
      using
        Data.Rat.SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
          coefficientNonnegative targetPositive
  have commonSmall : coefficient * commonWidth ^ 2 < target :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareOrder
      coefficientNonnegative).trans_lt boxSmall
  have upperScaled :
      Data.Gaussian.Norm.Basic.normSq
          (p.eval (entry.parent.parent.chart.parameterization.curve.point
            sample.parameter)) ≤
        coefficient * commonWidth ^ 2 := by
    simpa only [coefficient, commonWidth,
      Curve.Boundary.Profile.Residual.BoundaryProfileEventEntry.affineResidualCoefficient]
      using upper
  exact upperScaled.trans_lt commonSmall

/-- A single descendant width below every owner-specific residual width when
the common target is the finite minimum of the state boundary clearances. -/
def familyStrictDescendantRequestWidth
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) : Fraction.Rational :=
  targetedFamilyDescendantRequestWidth entry family family.clearanceTarget

/-- The common strict-descendant request based on all retained family clearances has positive width. -/
theorem familyStrictDescendantRequestWidth_pos
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) :
    0 < familyStrictDescendantRequestWidth entry family :=
  targetedFamilyDescendantRequestWidth_pos entry family
    family.clearanceTarget_pos

/-- The one executable non-pole rational sample used for the complete finite
state scan. -/
def familyStrictDescendantSample
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) :=
  Curve.Boundary.Complete.Sample.nonpoleCompleteRequestDescendantSample
    entry (familyStrictDescendantRequestWidth entry family)

/-- If the common descendant sample meets one state, its original-polynomial
residual is strictly below that state's own boundary clearance. -/
theorem family_descendant_sample_residual_lt
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (index : Fin family.boxes.length)
    (sample :
      Curve.Boundary.Complete.Sample.NonpoleCompleteRequestDescendantSample
        entry (familyStrictDescendantRequestWidth entry family))
    (contains : (family.stateAtBoxIndex index).box.Contains
      (entry.parent.parent.chart.parameterization.curve.point
        sample.parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          sample.parameter)) <
      (family.stateAtBoxIndex index).clearance.bound := by
  have belowTarget := targeted_family_descendant_sample_residual_lt entry
    family index family.clearanceTarget_pos sample contains
  exact belowTarget.trans_le (family.clearanceTarget_le_stateAt index)

set_option genInjectivity false in
/-- Total classification of one common rational descendant sample.  The
owned branch identifies one actual winding state and proves strict
containment there; the outside branch rejects the same sample from every
state. -/
inductive FamilyStrictDescendantClassification
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) where
  /-- The actual common sample is strictly inside the indexed original state with a residual below that state's
    clearance. -/ | owned
      (index : Fin family.boxes.length)
      (contains : (family.stateAtBoxIndex index).box.Contains
        (entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample entry family).parameter))
      (strict : (family.stateAtBoxIndex index).box.StrictContains
        (entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample entry family).parameter))
      (residual : Data.Gaussian.Norm.Basic.normSq
        (p.eval (entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample entry family).parameter)) <
            (family.stateAtBoxIndex index).clearance.bound)
  /-- The actual common sample is outside every retained winding-state box. -/ | outside
      (proof : ∀ index : Fin family.boxes.length,
        ¬(family.stateAtBoxIndex index).box.Contains
          (entry.parent.parent.chart.parameterization.curve.point
            (familyStrictDescendantSample entry family).parameter))

constructive_injectivity FamilyStrictDescendantClassification

/-- Execute one finite membership scan for the common descendant sample and
strengthen any owner meeting with its exact clearance comparison. -/
def classifyFamilyStrictDescendant
    {epsilon : Fraction.Rational}
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient) :
    FamilyStrictDescendantClassification entry family := by
  let sample := familyStrictDescendantSample entry family
  let point := entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  match found :
      Box.Family.Search.findContainingBoxIndex
        family.boxes point with
  | some index =>
      have containsBox :=
        Box.Family.Search.findContainingBoxIndex_sound
          family.boxes point index found
      have contains : (family.stateAtBoxIndex index).box.Contains point := by
        rw [← family.boxAt_eq index]
        exact containsBox
      have residual := family_descendant_sample_residual_lt entry family index
        sample contains
      exact .owned index contains
        ((family.stateAtBoxIndex index).clearance.strictContains_of_residual_lt
          contains residual)
        residual
  | none =>
      have outsideBoxes :=
        Box.Family.Search.findContainingBoxIndex_none
          family.boxes point found
      exact .outside (by
        intro index contains
        apply outsideBoxes index
        rw [family.boxAt_eq index]
        exact contains)

/-! ## Persistence of an already selected finite owner index -/

/-- Once a displayed sample has selected an owner for one retained child, the
common strict descendant remains strictly in that same indexed state. -/
inductive OwnedChildDescendantResolution
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : Curve.Boundary.Winding.Budget.ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      Curve.Boundary.Complete.Ownership.ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (Curve.Boundary.Winding.Budget.windingTarget (boundary := boundary) squarefree family)
          classified.entry) where
  /-- The same selected owner strictly contains the descendant sample with the retained clearance residual bound. -/ |
    retained
      (strict : (family.stateAtBoxIndex owner.index).box.StrictContains
        (classified.entry.parent.parent.chart.parameterization.curve.point
          (familyStrictDescendantSample classified.entry family).parameter))
      (residual : Data.Gaussian.Norm.Basic.normSq
        (p.eval
          (classified.entry.parent.parent.chart.parameterization.curve.point
            (familyStrictDescendantSample classified.entry family).parameter)) <
          (family.stateAtBoxIndex owner.index).clearance.bound)

/-- Place the common strict descendant in its already selected owner using
whole-cylinder containment, then strengthen it with the descendant residual
request. -/
theorem resolveOwnedChildDescendant
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : Curve.Boundary.Winding.Budget.ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      Curve.Boundary.Complete.Ownership.ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (Curve.Boundary.Winding.Budget.windingTarget (boundary := boundary) squarefree family)
          classified.entry) :
    OwnedChildDescendantResolution squarefree family classified owner := by
  let sample := familyStrictDescendantSample classified.entry family
  let point := classified.entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  have descendantInside :
      classified.entry.child.cell.interval.Contains sample.parameter :=
    ⟨(classified.entry.child.request_refines
        (familyStrictDescendantRequestWidth classified.entry family)).1.trans
        sample.parameterInside.1,
      sample.parameterInside.2.trans
        (classified.entry.child.request_refines
          (familyStrictDescendantRequestWidth classified.entry family)).2⟩
  have contains : (family.stateAtBoxIndex owner.index).box.Contains point :=
    Curve.Boundary.Winding.Containment.controlledChild_inside_owner squarefree family classified owner
      descendantInside sample.denominatorNonzero
  have residual := family_descendant_sample_residual_lt classified.entry family
    owner.index sample contains
  exact .retained
    ((family.stateAtBoxIndex owner.index).clearance.strictContains_of_residual_lt
      contains residual)
    residual
end Boundary

end Purelib.RootIsolation.Curve.Boundary.Winding.Descendant

end
