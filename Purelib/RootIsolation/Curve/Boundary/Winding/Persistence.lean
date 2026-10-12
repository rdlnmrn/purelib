module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Boundary.Complete.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Ownership
import Purelib.RootIsolation.Curve.Boundary.Complete.Sample
import Purelib.RootIsolation.Curve.Boundary.Winding.Budget
import Purelib.RootIsolation.Curve.Boundary.Winding.Containment
import Purelib.RootIsolation.Curve.Boundary.Winding.Descendant
public import Purelib.RootIsolation.Curve.Boundary.Winding.Sample
import Purelib.RootIsolation.Newton.Restart.Persistence
public import Purelib.RootIsolation.Newton.Restart.Uniform.Budget
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Family.Basic
public import Purelib.RootIsolation.State.WindingOne.Family.Later
public import Purelib.RootIsolation.State.WindingOne.Region
import Purelib.RootIsolation.Track.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.Curve.Boundary.Complete.Control
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Boundary.Profile.Boundary
import Purelib.RootIsolation.State.WindingOne.Family.Clearance

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.RootIsolation.Curve.Boundary.Complete.Basic (BoundaryCompleteRequestEntry)
open Purelib.RootIsolation.Curve.Boundary.Complete.Ownership (ControlledCompleteRequestMeeting)
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

namespace Purelib.RootIsolation.Curve.Boundary.Winding.Persistence
section Boundary

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
variable {denominatorMargin : Fraction.Rational}
variable {marginPositive : 0 < denominatorMargin}
variable {atom : Geometry.Projective.Hermitian.Atom}
variable {boundary : Curve.Boundary.Analysis.CurveBoundary p reference current denominatorMargin
  marginPositive atom}

/-! ## Uniform residual refinement into a supplied later state -/

/-- One positive target simultaneously below every family clearance and the
point-independent Newton budget for the selected owner and supplied later
state. -/
def persistentDescendantResidualTarget
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) : Fraction.Rational :=
  min family.clearanceTarget
    (Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget squarefree
      (State.WindingOne.Region.protectedAmbient (family.stateAtBoxIndex ownerIndex))
      (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p later.box
        later.clearance))

/-- The shared family-clearance and later-state Newton residual target is positive. -/
theorem persistentDescendantResidualTarget_pos
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :
    0 < persistentDescendantResidualTarget squarefree family ownerIndex later :=
  Fraction.Order.Basic.lt_min family.clearanceTarget_pos
    (Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget_pos
      squarefree (State.WindingOne.Region.protectedAmbient (family.stateAtBoxIndex ownerIndex))
      (Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p
        later.clearance later.proper))

/-- Family-wide descendant width at the selected owner's uniform later-state
Newton target. -/
def persistentDescendantRequestWidth
    {epsilon : Fraction.Rational}
    (squarefree : SquarefreeCertificate p)
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) : Fraction.Rational :=
  Curve.Boundary.Winding.Descendant.targetedFamilyDescendantRequestWidth entry family
    (persistentDescendantResidualTarget squarefree family ownerIndex later)

/-- The descendant request for the retained owner and actual later state has positive width. -/
theorem persistentDescendantRequestWidth_pos
    {epsilon : Fraction.Rational}
    (squarefree : SquarefreeCertificate p)
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :
    0 < persistentDescendantRequestWidth squarefree entry family ownerIndex later :=
  Curve.Boundary.Winding.Descendant.targetedFamilyDescendantRequestWidth_pos entry family
    (persistentDescendantResidualTarget_pos squarefree family ownerIndex later)

/-- The one non-pole rational event sample at the uniform later-state target. -/
def persistentDescendantSample
    {epsilon : Fraction.Rational}
    (squarefree : SquarefreeCertificate p)
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :=
  Curve.Boundary.Complete.Sample.nonpoleCompleteRequestDescendantSample
    entry
      (persistentDescendantRequestWidth squarefree entry family ownerIndex later)

/-- The computed descendant is not merely close to the dispatched atom
boundary: its displayed rational point lies exactly on that boundary.  This
uses only the rational parametrization and its explicit non-pole witness. -/
theorem persistentDescendantSample_onBoundary
    {epsilon : Fraction.Rational}
    (squarefree : SquarefreeCertificate p)
    (entry :
      BoundaryCompleteRequestEntry
        boundary epsilon)
    (family : WindingFamily p ambient)
    (ownerIndex : Fin family.boxes.length)
    (later : WindingOneState p ambient) :
    atom.form.eval
        (entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree entry family ownerIndex
            later).parameter) =
      0 :=
  entry.parent.parent.chart.parameterization.onBoundary
    (persistentDescendantSample squarefree entry family ownerIndex later).parameter
    (persistentDescendantSample squarefree entry family ownerIndex
      later).denominatorNonzero

/-- The selected event's uniform residual refinement supplies a rational
sample in the requested later numerical state, still strictly owned by the
original state. -/
inductive OwnedChildPersistentResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (classified : Curve.Boundary.Winding.Budget.ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (Curve.Boundary.Winding.Budget.windingTarget (boundary := boundary) squarefree family)
          classified.entry)
    (later : WindingOneState p ambient) where
  /-- The same descendant sample lies strictly in the original owner, meets its uniform residual target, and belongs to
    the supplied later state. -/ | retained
      (strict : (family.stateAtBoxIndex owner.index).box.StrictContains
        (classified.entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree classified.entry family
            owner.index later).parameter))
      (residual : Data.Gaussian.Norm.Basic.normSq
        (p.eval
          (classified.entry.parent.parent.chart.parameterization.curve.point
            (persistentDescendantSample squarefree classified.entry family
              owner.index later).parameter)) <
        Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget squarefree
          (State.WindingOne.Region.protectedAmbient (family.stateAtBoxIndex owner.index))
          (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p later.box
            later.clearance))
      (laterContains : later.box.Contains
        (classified.entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree classified.entry family
            owner.index later).parameter))

/-- Execute the uniform residual request inside the whole retained owner
cylinder; the uniform Newton theorem then places the displayed rational sample
in `later`. -/
theorem resolveOwnedChildPersistent
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (family : WindingFamily p ambient)
    (classified : Curve.Boundary.Winding.Budget.ClassifiedChild (boundary := boundary) squarefree family)
    (owner :
      ControlledCompleteRequestMeeting
        family.boxes family.boxes_pairwise
          (Curve.Boundary.Winding.Budget.windingTarget (boundary := boundary) squarefree family)
          classified.entry)
    (track : Track.Basic.WindingOneTrack p ambient)
    (later : WindingOneState p ambient)
    (laterRefines : later.box.Refines
      (family.stateAtBoxIndex owner.index).box) :
    OwnedChildPersistentResolution squarefree family classified owner later := by
  let target := persistentDescendantResidualTarget squarefree family
    owner.index later
  let sample := persistentDescendantSample squarefree classified.entry family
    owner.index later
  let point := classified.entry.parent.parent.chart.parameterization.curve.point
    sample.parameter
  have descendantInside :
      classified.entry.child.cell.interval.Contains sample.parameter :=
    ⟨(classified.entry.child.request_refines
        (persistentDescendantRequestWidth squarefree classified.entry family
          owner.index later)).1.trans sample.parameterInside.1,
      sample.parameterInside.2.trans
        (classified.entry.child.request_refines
          (persistentDescendantRequestWidth squarefree classified.entry family
            owner.index later)).2⟩
  have contains : (family.stateAtBoxIndex owner.index).box.Contains point :=
    Curve.Boundary.Winding.Containment.controlledChild_inside_owner squarefree family classified owner
      descendantInside sample.denominatorNonzero
  have residualTarget := Curve.Boundary.Winding.Descendant.targeted_family_descendant_sample_residual_lt
    classified.entry family owner.index
      (persistentDescendantResidualTarget_pos squarefree family owner.index
        later)
      sample contains
  have residualClearance :
      Data.Gaussian.Norm.Basic.normSq (p.eval point) <
        (family.stateAtBoxIndex owner.index).clearance.bound :=
    residualTarget.trans_le
      ((Fraction.Order.Basic.min_le_left _ _).trans
        (family.clearanceTarget_le_stateAt owner.index))
  have strict :=
    (family.stateAtBoxIndex owner.index).clearance.strictContains_of_residual_lt
      contains residualClearance
  have residualUniform :
      Data.Gaussian.Norm.Basic.normSq (p.eval point) <
        Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget
          squarefree (State.WindingOne.Region.protectedAmbient (family.stateAtBoxIndex owner.index))
          (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
            later.box later.clearance) :=
    residualTarget.trans_le (Fraction.Order.Basic.min_le_right _ _)
  have laterContains := Newton.Restart.Persistence.uniform_residual_sample_inside_later degreeAtLeastTwo
    squarefree elimination track (family.stateAtBoxIndex owner.index) later
    laterRefines point contains residualUniform
  exact .retained strict residualUniform laterContains

set_option genInjectivity false in
/-- Boundary-wide result at the selected owner's point-independent Newton
target.  The retained branch contains the computed rational sample in the
provider's actual later state; the other branch records that the initial
finite scan selected no owner. -/
inductive FamilyPersistentResolution
    (squarefree : SquarefreeCertificate p)
    (family : WindingFamily p ambient)
    (provider : State.WindingOne.Family.Later.LaterStateProvider family) where
  /-- The first selected child's descendant is retained in its original owner and the provider's actual later state. -/
    | retained
      (child : Curve.Boundary.Winding.Sample.ComparedChild (boundary := boundary) squarefree family)
      (member : child ∈
        Curve.Boundary.Winding.Sample.compareWindingRequestFamily (boundary := boundary) squarefree family)
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
          (persistentDescendantSample squarefree child.classified.entry family
            owner.index (provider.laterAt owner.index)).parameter))
      (residual : Data.Gaussian.Norm.Basic.normSq
        (p.eval
          (child.classified.entry.parent.parent.chart.parameterization.curve.point
            (persistentDescendantSample squarefree child.classified.entry family
              owner.index (provider.laterAt owner.index)).parameter)) <
        Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget squarefree
          (State.WindingOne.Region.protectedAmbient (family.stateAtBoxIndex owner.index))
          (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p
            (provider.laterAt owner.index).box
            (provider.laterAt owner.index).clearance))
      (laterContains : (provider.laterAt owner.index).box.Contains
        (child.classified.entry.parent.parent.chart.parameterization.curve.point
          (persistentDescendantSample squarefree child.classified.entry family
            owner.index (provider.laterAt owner.index)).parameter))
  /-- The initial finite sample scan selected no owner among the retained winding states. -/ | initiallyOutside
      (proof : ∀ child ∈
        Curve.Boundary.Winding.Sample.compareWindingRequestFamily (boundary := boundary) squarefree family,
          Curve.Boundary.Winding.Sample.SampleOutsideAllStates squarefree family child.classified)

constructive_injectivity FamilyPersistentResolution

/-- Execute the first-owner scan and request the selected child's residual at
the later state supplied for that exact owner index. -/
def resolveFamilyPersistent
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : SquarefreeCertificate p)
    {degreeBound : Nat}
    (elimination :
      Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (family : WindingFamily p ambient)
    (provider : State.WindingOne.Family.Later.LaterStateProvider family) :
    FamilyPersistentResolution (boundary := boundary) squarefree family
      provider := by
  match Curve.Boundary.Winding.Sample.resolveWindingRequestFamily (boundary := boundary) squarefree family with
  | .outside proof => exact .initiallyOutside proof
  | .owned child member owner initialResidual derivativeNonzero =>
      match resolveOwnedChildPersistent degreeAtLeastTwo squarefree elimination
          family child.classified owner (provider.trackAt owner.index)
          (provider.laterAt owner.index) (provider.laterRefines owner.index) with
      | .retained strict residual laterContains =>
          exact .retained child member owner initialResidual derivativeNonzero
            strict residual laterContains

end Boundary

end Purelib.RootIsolation.Curve.Boundary.Winding.Persistence

end
