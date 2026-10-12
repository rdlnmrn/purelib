module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive
import Purelib.Riemann.Topology.PreparedCycleSeedReplay
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Sample
public import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Topology.SquareRootContinuationChain

@[expose] public section

/-!
Reassemble the original cycle from exact adaptive bank selections.  These
inputs retain the original geometry and sheet owners before any banks are
forced.  The equations identify the full prepared objects, including depths
and ordered banks, rather than only the value of an integral.
-/

namespace Purelib.Riemann.Topology.PreparedCycleBankReplay

open PreparedCycleModels (PreparedBoundaryDoublePath PreparedDoublePath Owner Box Coordinate Gaussian)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (refinedState refinedTrackAnchor connectorAt connectorAt_withinAmbient)
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts (ownerBoundaryPath ownerBoundaryPath_withinAmbient)
open Purelib.RootIsolation.SquareRoot.Preparation.Bank.Adaptive (Task Selected)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Curves.Hyperelliptic in
open Purelib.Polynomial in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- Original owners and paths for a four-part boundary replay.

Retains both winding-one states, the clear connector and its containment, four distinct root owners and a positive
target root diameter. -/
structure BoundaryInput (curve : Basic.HyperellipticCurve genus) where
  /-- Original ambient box of the left winding-one state. -/ leftAmbient : Box
  /-- Original ambient box of the right winding-one state. -/ rightAmbient : Box
  /-- Ambient box for the retained clear connector. -/ connectorAmbient : Box
  /-- Actual left winding-one state. -/ leftState : State.WindingOne.Basic.WindingOneState curve.polynomial leftAmbient
  /-- Actual right winding-one state. -/ rightState : State.WindingOne.Basic.WindingOneState curve.polynomial
    rightAmbient
  /-- Original clear connector between the retained state anchors. -/ connector : Polynomial.Geometry.ClearPath
    curve.polynomial connectorAmbient leftState.box.anchor rightState.box.anchor
  /-- Containment certificate for the actual retained path. -/ within : connector.WithinAmbient
  /-- Original root owner at the forward path's start. -/ forwardOwner : Owner (curve.polynomial.eval
    leftState.box.anchor)
  /-- Original root owner for the right-state boundary. -/ rightOwner : Owner (curve.polynomial.eval
    rightState.box.anchor)
  /-- Original root owner at the backward path's start. -/ backwardOwner : Owner (curve.polynomial.eval
    rightState.box.anchor)
  /-- Original root owner for the left-state boundary. -/ leftOwner : Owner (curve.polynomial.eval leftState.box.anchor)
  /-- Requested positive root diameter. -/ diameter : Coordinate
  /-- Strict positivity of the retained diameter. -/ positive : 0 < diameter

constructive_injectivity BoundaryInput

namespace BoundaryInput

open Purelib.RootIsolation in
/-- Singleton adaptive task for the original forward connector and owner. -/
def forward (input : BoundaryInput curve) := [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath input.connector
  input.within input.forwardOwner]
section
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.RootIsolation
/-- Singleton adaptive task for the original right-state boundary and owner. -/
def right (input : BoundaryInput curve) :=
  [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath (BranchCutLifts.ownerBoundaryPath input.rightState)
    (BranchCutLifts.ownerBoundaryPath_withinAmbient input.rightState) input.rightOwner]
/-- Singleton adaptive task for the reversed connector and backward owner. -/
def backward (input : BoundaryInput curve) :=
  [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath (BranchCutLifts.ClearPath.reverse input.connector)
    (BranchCutLifts.ClearPath.reverse_withinAmbient input.connector input.within)
    input.backwardOwner]
/-- Singleton adaptive task for the original left-state boundary and owner. -/
def left (input : BoundaryInput curve) :=
  [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath (BranchCutLifts.ownerBoundaryPath input.leftState)
    (BranchCutLifts.ownerBoundaryPath_withinAmbient input.leftState) input.leftOwner]

end

/-- Construct the original four-part boundary from the retained input.

Uses its actual geometric path data, endpoint owners and positive diameter. -/
def original (input : BoundaryInput curve) : PreparedBoundaryDoublePath curve :=
  PreparedBoundaryDoublePath.total input.leftState input.rightState input.connector input.within
    input.forwardOwner input.rightOwner input.backwardOwner input.leftOwner input.diameter input.positive

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.RootIsolation in
/-- Restore the prepared four-part boundary from retained adaptive selections.

Keeps the four independently selected singleton banks and their separate depths, preserving the input geometry, original
root owners and selected executable banks. -/
def restore (input : BoundaryInput curve)
    (forward : SquareRoot.Preparation.Bank.Adaptive.Selected input.forward input.diameter input.positive)
    (right : SquareRoot.Preparation.Bank.Adaptive.Selected input.right input.diameter input.positive)
    (backward : SquareRoot.Preparation.Bank.Adaptive.Selected input.backward input.diameter input.positive)
    (left : SquareRoot.Preparation.Bank.Adaptive.Selected input.left input.diameter input.positive) :
      PreparedBoundaryDoublePath curve where
  leftAmbient := input.leftAmbient
  rightAmbient := input.rightAmbient
  connectorAmbient := input.connectorAmbient
  leftState := input.leftState
  rightState := input.rightState
  connector := input.connector
  rightBoundaryPath := BranchCutLifts.ownerBoundaryPath input.rightState
  leftBoundaryPath := BranchCutLifts.ownerBoundaryPath input.leftState
  forwardDepth := forward.depth
  rightBoundaryDepth := right.depth
  backwardDepth := backward.depth
  leftBoundaryDepth := left.depth
  rootDiameter := input.diameter
  rootDiameterPositive := input.positive
  forwardOwner := input.forwardOwner
  forwardChecked := forward.banks.head
  rightBoundaryOwner := input.rightOwner
  rightBoundaryChecked := right.banks.head
  backwardOwner := input.backwardOwner
  backwardChecked := backward.banks.head
  leftBoundaryOwner := input.leftOwner
  leftBoundaryChecked := left.banks.head

open Purelib.RootIsolation in
/-- The restored four-part boundary equals its original construction.

Requires exact equality of the supplied selections with the original adaptive selector results, preserving every
retained bank and depth. -/
theorem restore_eq (input : BoundaryInput curve)
    (forward : SquareRoot.Preparation.Bank.Adaptive.Selected input.forward input.diameter input.positive)
    (right : SquareRoot.Preparation.Bank.Adaptive.Selected input.right input.diameter input.positive)
    (backward : SquareRoot.Preparation.Bank.Adaptive.Selected input.backward input.diameter input.positive)
    (left : SquareRoot.Preparation.Bank.Adaptive.Selected input.left input.diameter input.positive)
    (forwardEq : forward = SquareRoot.Preparation.Bank.Adaptive.select input.forward input.diameter input.positive)
    (rightEq : right = SquareRoot.Preparation.Bank.Adaptive.select input.right input.diameter input.positive)
    (backwardEq : backward = SquareRoot.Preparation.Bank.Adaptive.select input.backward input.diameter input.positive)
    (leftEq : left = SquareRoot.Preparation.Bank.Adaptive.select input.left input.diameter input.positive) :
    input.restore forward right backward left = input.original := by
  cases forwardEq
  cases rightEq
  cases backwardEq
  cases leftEq
  rfl

open Purelib.Curves.Hyperelliptic.Branches in
/-- Build four-part boundary input from original refined branch owners.

Uses the branch bank at the supplied refinement and its exact connector containment, retaining the supplied root owners
and unit diameter. -/
def ofOwners (branches : BranchIsolation.Data curve) (higher : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches) (refinement : Nat)
    (forwardOwner : Owner (curve.polynomial.eval (Cuts.refinedTrackAnchor branches higher left refinement)))
    (rightOwner backwardOwner : Owner (curve.polynomial.eval (Cuts.refinedTrackAnchor branches higher right
      refinement)))
    (leftOwner : Owner (curve.polynomial.eval (Cuts.refinedTrackAnchor branches higher left refinement))) :
      BoundaryInput curve :=
  { leftAmbient := _, rightAmbient := _, connectorAmbient := _
    leftState := Cuts.refinedState branches higher left refinement
    rightState := Cuts.refinedState branches higher right refinement
    connector := Cuts.connectorAt branches higher left right refinement
    within := Cuts.connectorAt_withinAmbient branches higher left right refinement
    forwardOwner := forwardOwner, rightOwner := rightOwner, backwardOwner := backwardOwner, leftOwner := leftOwner
    diameter := 1, positive := by decide }

end BoundaryInput

open Purelib.Curves.Hyperelliptic in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Original two-direction bridge replay input.

Retains one clear path and its containment, distinct forward and backward endpoint owners, and a positive root diameter.
-/
structure BridgeInput (curve : Basic.HyperellipticCurve genus) where
  /-- Ambient box of the original bridge path. -/ ambient : Box
  /-- Original bridge start coordinate. -/ start : Gaussian
  /-- Original bridge finish coordinate. -/ finish : Gaussian
  /-- Actual clear bridge path with its retained endpoints. -/ path : Polynomial.Geometry.ClearPath curve.polynomial
    ambient start finish
  /-- Containment certificate for the actual retained path. -/ within : path.WithinAmbient
  /-- Original root owner at the forward path's start. -/ forwardOwner : Owner (curve.polynomial.eval start)
  /-- Original root owner at the backward path's start. -/ backwardOwner : Owner (curve.polynomial.eval finish)
  /-- Requested positive root diameter. -/ diameter : Coordinate
  /-- Strict positivity of the retained diameter. -/ positive : 0 < diameter

constructive_injectivity BridgeInput

namespace BridgeInput

open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.RootIsolation in
/-- Ordered forward and reversed adaptive tasks for the retained bridge.

Each task keeps its original endpoint owner and the exact path containment witness. -/
def tasks (input : BridgeInput curve) :=
  [SquareRoot.Preparation.Bank.Adaptive.Task.ofPath input.path input.within input.forwardOwner,
   SquareRoot.Preparation.Bank.Adaptive.Task.ofPath (BranchCutLifts.ClearPath.reverse input.path)
     (BranchCutLifts.ClearPath.reverse_withinAmbient input.path input.within) input.backwardOwner]

/-- Construct the original two-direction bridge from the retained input.

Uses its actual geometric path data, endpoint owners and positive diameter. -/
def original (input : BridgeInput curve) : PreparedDoublePath curve :=
  PreparedDoublePath.total input.path input.within input.forwardOwner input.backwardOwner input.diameter input.positive

section
open Purelib.RootIsolation
/-- Restore the prepared two-direction bridge from retained adaptive selections.

Keeps the two original tasks in one selected bank and their common depth, preserving the input geometry, original root
owners and selected executable banks. -/
def restore (input : BridgeInput curve) (selected : SquareRoot.Preparation.Bank.Adaptive.Selected input.tasks
  input.diameter input.positive) :
    PreparedDoublePath curve where
  ambient := input.ambient
  start := input.start
  finish := input.finish
  basePath := input.path
  depth := selected.depth
  rootDiameter := input.diameter
  rootDiameterPositive := input.positive
  forwardOwner := input.forwardOwner
  forwardChecked := selected.banks.head
  backwardOwner := input.backwardOwner
  backwardChecked := selected.banks.tail.head

/-- The restored two-direction bridge equals its original construction.

Requires exact equality of the supplied selections with the original adaptive selector results, preserving every
retained bank and depth. -/
theorem restore_eq (input : BridgeInput curve) (selected : SquareRoot.Preparation.Bank.Adaptive.Selected input.tasks
  input.diameter input.positive)
    (equal : selected = SquareRoot.Preparation.Bank.Adaptive.select input.tasks input.diameter input.positive) :
    input.restore selected = input.original := by
  cases equal
  rfl

end

open Purelib.Curves.Hyperelliptic.Branches in
/-- Build two-direction bridge input from original refined branch owners.

Uses the branch bank at the supplied refinement and its exact connector containment, retaining the supplied root owners
and unit diameter. -/
def ofOwners (branches : BranchIsolation.Data curve) (higher : 1 < curve.polynomial.natDegree)
    (left right : BranchIsolation.Data.Index branches) (refinement : Nat)
    (forwardOwner : Owner (curve.polynomial.eval (Cuts.refinedTrackAnchor branches higher left refinement)))
    (backwardOwner : Owner (curve.polynomial.eval (Cuts.refinedTrackAnchor branches higher right refinement))) :
      BridgeInput curve :=
  { ambient := _, start := _, finish := _
    path := Cuts.connectorAt branches higher left right refinement
    within := Cuts.connectorAt_withinAmbient branches higher left right refinement
    forwardOwner := forwardOwner, backwardOwner := backwardOwner, diameter := 1, positive := by decide }

end BridgeInput

end Purelib.Riemann.Topology.PreparedCycleBankReplay
