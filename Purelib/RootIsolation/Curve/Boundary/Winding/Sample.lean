module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Ownership
import Purelib.RootIsolation.Curve.Boundary.Winding.Budget
public import Purelib.RootIsolation.Curve.Boundary.Winding.Descendant
import Purelib.RootIsolation.State.WindingOne.Family.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Control
import Purelib.RootIsolation.Curve.Boundary.Complete.Sample
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.RootIsolation.Curve.Boundary.Complete.Ownership (ControlledCompleteRequestMeeting)
open Purelib.RootIsolation.Curve.Boundary.Winding.Budget (ClassifiedChild)
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

namespace Purelib.RootIsolation.Curve.Boundary.Winding.Sample
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

set_option genInjectivity false in
/-- Safe finite comparison of one complete child with the actual winding
states.  The owner branch concerns its displayed rational sample only. -/
inductive ChildComparison
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family)
    where
  /-- The retained sample has an original winding owner, residual below the derivative threshold, and a nonzero
    derivative. -/ | owned
      (owner :
        ControlledCompleteRequestMeeting
          family.boxes family.boxes_pairwise
            (Curve.Boundary.Winding.Budget.windingTarget (boundary := boundary) squarefree family)
            classified.entry)
      (residual : Data.Gaussian.Norm.Basic.normSq
          (p.eval
            (classified.entry.parent.parent.chart.parameterization.curve.point
              owner.parameter)) <
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient)
      (derivativeNonzero :
        (Dense.Gaussian.GCD.derivative p).eval
          (classified.entry.parent.parent.chart.parameterization.curve.point
            owner.parameter) ≠ 0)
  /-- The actual retained child sample lies outside every winding-state box. -/ | outside (proof : ∀ index : Fin
    family.boxes.length,
      ¬(family.stateAtBoxIndex index).box.Contains
        (classified.entry.parent.parent.chart.parameterization.curve.point
          classified.sample.parameter))

constructive_injectivity ChildComparison

/-- Translate the computed box classifier to its aligned winding state and
attach the derivative-threshold consequences in the owner branch. -/
def compareChild
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family) :
    ChildComparison squarefree family classified := by
  cases classified.sampleClassification with
  | meeting owner =>
      exact .owned owner
        ((owner.residual_lt
            (Curve.Boundary.Winding.Budget.windingTarget_pos (boundary := boundary) squarefree family)).trans_le
          (Curve.Boundary.Winding.Budget.windingTarget_le_derivativeThreshold
            (boundary := boundary) squarefree family))
        (owner.derivative_ne_zero squarefree
          family.boxAt_refinesAmbient
          (Curve.Boundary.Winding.Budget.windingTarget_pos (boundary := boundary) squarefree family)
          (Curve.Boundary.Winding.Budget.windingTarget_le_derivativeThreshold
            (boundary := boundary) squarefree family))
  | outside proof =>
      exact .outside (by
        intro index contained
        apply proof index
        rw [family.boxAt_eq index]
        exact contained)

set_option genInjectivity false in
/-- One classified child together with its safe winding-state comparison. -/
structure ComparedChild
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) where
  /-- The original complete child with its retained finite classifications. -/ classified :
    ClassifiedChild (boundary := boundary) squarefree family
  /-- The winding-state comparison of this exact retained child and sample. -/ comparison :
    ChildComparison squarefree family classified

constructive_injectivity ComparedChild

/-- Compare every complete retained boundary child with the complete finite
winding family. -/
def compareWindingRequestFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    List (ComparedChild (boundary := boundary) squarefree family) :=
  (Curve.Boundary.Winding.Budget.classifiedWindingRequestFamily (boundary := boundary) squarefree family).map
    fun classified =>
      { classified := classified
        comparison := compareChild squarefree family classified }

/-- The displayed rational sample of one classified child is outside every
state in the winding family. -/
def SampleOutsideAllStates
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : ClassifiedChild (boundary := boundary) squarefree family) :
    Prop :=
  ∀ index : Fin family.boxes.length,
    ¬(family.stateAtBoxIndex index).box.Contains
      (classified.entry.parent.parent.chart.parameterization.curve.point
        classified.sample.parameter)

set_option genInjectivity false in
/-- Result of a complete finite scan of the child samples.  The first branch
retains a displayed sample owned by one state; the second proves that every
displayed sample in the list is outside every state. -/
inductive FamilySampleResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    List (ComparedChild (boundary := boundary) squarefree family) → Type
  /-- A retained member child has an owned sample with the original derivative and residual certificates. -/ | owned
      {values : List (ComparedChild (boundary := boundary) squarefree family)}
      (child : ComparedChild (boundary := boundary) squarefree family)
      (member : child ∈ values)
      (owner :
        ControlledCompleteRequestMeeting
          family.boxes family.boxes_pairwise
            (Curve.Boundary.Winding.Budget.windingTarget (boundary := boundary) squarefree family)
            child.classified.entry)
      (residual : Data.Gaussian.Norm.Basic.normSq
          (p.eval
            (child.classified.entry.parent.parent.chart.parameterization.curve.point
              owner.parameter)) <
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient)
      (derivativeNonzero :
        (Dense.Gaussian.GCD.derivative p).eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            owner.parameter) ≠ 0) :
      FamilySampleResolution squarefree family values
  /-- Every actual sample in the retained list lies outside every original winding-state box. -/ | outside
      {values : List (ComparedChild (boundary := boundary) squarefree family)}
      (proof : ∀ child ∈ values,
        SampleOutsideAllStates squarefree family child.classified) :
      FamilySampleResolution squarefree family values

constructive_injectivity FamilySampleResolution

/-- Execute the finite first-owned/outside-all scan over already compared
children. -/
def resolveComparedChildren
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    (values : List (ComparedChild (boundary := boundary) squarefree family)) →
      FamilySampleResolution squarefree family values
  | [] => .outside (by intro child member; exact (List.not_mem_nil member).elim)
  | head :: tail =>
      match head.comparison with
      | .owned owner residual derivativeNonzero =>
          .owned head List.mem_cons_self owner residual derivativeNonzero
      | .outside headOutside =>
          match resolveComparedChildren squarefree family tail with
          | .owned child member owner residual derivativeNonzero =>
              .owned child (List.mem_cons_of_mem head member) owner residual
                derivativeNonzero
          | .outside tailOutside =>
              .outside (by
                intro child member
                rcases Data.List.Membership.mem_cons.mp member with rfl | tailMember
                · exact headOutside
                · exact tailOutside child tailMember)

/-- Complete executable winding-state comparison for one dispatched curve
boundary at the squarefree derivative threshold. -/
def resolveWindingRequestFamily
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    FamilySampleResolution squarefree family
      (compareWindingRequestFamily (boundary := boundary) squarefree family) :=
  resolveComparedChildren squarefree family
    (compareWindingRequestFamily (boundary := boundary) squarefree family)

/-! ## Boundary-family owner/descendant resolution -/

set_option genInjectivity false in
/-- Complete finite result after selecting the first initially owned child
and following that very child to the one common strict descendant.  `retained`
keeps the original owner index; `initiallyOutside` records that no initial
sample selected an owner. -/
inductive FamilyDescendantResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) where
  /-- The first selected child's common descendant remains strictly in the same owner with its clearance residual bound.
  -/
  | retained
      (child : ComparedChild (boundary := boundary) squarefree family)
      (member : child ∈
        compareWindingRequestFamily (boundary := boundary) squarefree family)
      (owner :
        ControlledCompleteRequestMeeting
          family.boxes family.boxes_pairwise
            (Curve.Boundary.Winding.Budget.windingTarget (boundary := boundary) squarefree family)
            child.classified.entry)
      (initialResidual : Data.Gaussian.Norm.Basic.normSq
          (p.eval
            (child.classified.entry.parent.parent.chart.parameterization.curve.point
              owner.parameter)) <
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree ambient)
      (derivativeNonzero :
        (Dense.Gaussian.GCD.derivative p).eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            owner.parameter) ≠ 0)
      (strict : (family.stateAtBoxIndex owner.index).box.StrictContains
        (child.classified.entry.parent.parent.chart.parameterization.curve.point
          (Curve.Boundary.Winding.Descendant.familyStrictDescendantSample child.classified.entry family).parameter))
      (descendantResidual : Data.Gaussian.Norm.Basic.normSq
        (p.eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            (Curve.Boundary.Winding.Descendant.familyStrictDescendantSample child.classified.entry family).parameter)) <
          (family.stateAtBoxIndex owner.index).clearance.bound)
  /-- The initial finite scan found every retained child sample outside all winding-state boxes. -/ | initiallyOutside
      (proof : ∀ child ∈
        compareWindingRequestFamily (boundary := boundary) squarefree family,
          SampleOutsideAllStates squarefree family child.classified)

constructive_injectivity FamilyDescendantResolution

/-- Execute the initial first-owner scan and, only when it finds an owner,
follow the same retained child through the shared strict-descendant scan. -/
def resolveFamilyDescendant
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient) :
    FamilyDescendantResolution (boundary := boundary) squarefree family := by
  match resolveWindingRequestFamily (boundary := boundary) squarefree family with
  | .outside proof => exact .initiallyOutside proof
  | .owned child member owner initialResidual derivativeNonzero =>
      match Curve.Boundary.Winding.Descendant.resolveOwnedChildDescendant squarefree family child.classified owner with
      | .retained strict descendantResidual =>
          exact .retained child member owner initialResidual derivativeNonzero
            strict descendantResidual
end Boundary

end Purelib.RootIsolation.Curve.Boundary.Winding.Sample

end
