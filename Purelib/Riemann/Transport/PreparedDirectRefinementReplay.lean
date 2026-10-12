module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
public import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.RootIsolation.SquareRoot.Replay.PreparedTrackReplay

public section

namespace Purelib.Riemann.Transport.PreparedDirectRefinementReplay
open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedEdgeRecasting
  (CenteredEdge Endpoint Coordinate directRequest)
section
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
/-- Defer construction of a root equivalence until its comparison operation is called.

The retained comparison function is evaluated only when a requested pair of indices and positive amount needs its
original relation witness. -/
@[expose] def deferredRoot {first last : Basic.Named}
    (comparison : Unit → Gaussian.Equivalence.NamedEquivalent first last) :
    Gaussian.Equivalence.NamedEquivalent first last :=
  ⟨fun left right amount positive => (comparison ()).compare left right amount positive⟩

/-- The deferred root equivalence equals the supplied equivalence at the unit input.

Its complete comparison field is the same original function after evaluating the retained unit continuation. -/
theorem deferredRoot_eq {first last : Basic.Named}
    (comparison : Unit → Gaussian.Equivalence.NamedEquivalent first last) :
    deferredRoot comparison = comparison () := by
  unfold deferredRoot
  cases comparison ()
  rfl

end

open Purelib.Approximation.Rational.Geometric in
open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat in
open Purelib.Geometry.Path.Gaussian.Lifted in
open Purelib.Integration.Polynomial.Gaussian.Path.Basic in
open Purelib.Riemann in
/-- Build the original one-leaf local block using a retained center state.

The block retains the leaf's root relation, lifted path and exact endpoint equations, with separate geometric movement
and root-diameter error bounds. -/
@[expose] def localBlockAtCenter {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    (left right : Endpoint) (rootDiameter : Coordinate)
    (leaf : Integration.CheckedDirectGeometry.Leaf parent.edge left right rootDiameter)
    (localProper : left.parameter < right.parameter)
    (center : PreparedConstantModels.PreparedEdge.CenterState leaf.edge) :
    LocalBlock parent left right 0 rootDiameter := by
  let child : CenteredEdge curve differential := ⟨leaf.edge, center⟩
  have startEqual : child.model.start =
      parent.edge.segment.pointAt left.parameter := by
    change
      (PreparedModels.edge curve
        parent.edge.segment parent.edge.within left
          (directRequest right rootDiameter leaf.positive)).pointAt
          0 = parent.edge.segment.pointAt left.parameter
    unfold PreparedModels.edge
    simpa only [Branches.PreparedSheetContinuation.parameterAt_zero, -eq_self, -iff_self]
      using
        (Branches.PreparedSheetContinuation.pointAt_parameterAt
          parent.edge.segment parent.edge.within left
            (directRequest right rootDiameter leaf.positive) 0).symm
  have finishEqual : child.model.finish =
      parent.edge.segment.pointAt right.parameter := by
    change
      (PreparedModels.edge curve
        parent.edge.segment parent.edge.within left
          (directRequest right rootDiameter leaf.positive)).pointAt
          1 = parent.edge.segment.pointAt right.parameter
    unfold PreparedModels.edge
    simpa only [directRequest,
      Branches.PreparedSheetContinuation.parameterAt_one, -eq_self, -iff_self]
      using
        (Branches.PreparedSheetContinuation.pointAt_parameterAt
          parent.edge.segment parent.edge.within left
            (directRequest right rootDiameter leaf.positive) 1).symm
  have movementEqual : child.edge.pointMovement =
      geometricMovement parent.edge.segment left.parameter right.parameter := by
    unfold Integration.PreparedConstantModels.PreparedEdge.pointMovement geometricMovement
    change Basic.normSq
      (child.model.finish - child.model.start) = _
    rw [startEqual, finishEqual]
  let lifted : Basic.LiftedPath 2
      ({ coordinate := parent.edge.segment.pointAt left.parameter,
         sheet := parent.edge.sheet } : Basic.LiftedPoint 2)
      ({ coordinate := parent.edge.segment.pointAt right.parameter,
         sheet := parent.edge.sheet } : Basic.LiftedPoint 2) :=
    .cons
      (ClearSegment.liftOnSheet child.edge.sheet
        child.edge.localSegment)
      (.nil _)
  have childError : child.edge.modelErrorAllowance <=
      localModelErrorBound differential parent.edge.segment rootDiameter 0
        left.parameter right.parameter := by
    unfold localModelErrorBound
    apply child.edge.modelErrorAllowance_le_of_separate_targets
    · calc
        child.edge.pointMovement =
            geometricMovement parent.edge.segment left.parameter
              right.parameter :=
          movementEqual
        _ = Basic.quarterRadius
            (geometricMovement parent.edge.segment left.parameter
              right.parameter) 0 := by
          simp only [Basic.quarterRadius_eq_mul_pow, pow_zero,
            Fraction.Field.mul_one_direct, -eq_self, -iff_self]
          rfl
        _ <= Basic.quarterRadius
            (geometricMovement parent.edge.segment left.parameter
              right.parameter) 0 := le_rfl
    · exact child.edge.preparedRootDiameter_lt_requested.le
  exact LocalBlock.mk [child] rfl ⟨localProper, trivial⟩
    (.cons child (.nil _))
    (.cons
      { fraction := leaf.position.fraction
        inside := leaf.position.inside
        point_eq := (leaf.rootChildAt parent).point_eq
        rootEquivalent := deferredRoot (fun _ => (leaf.rootChildAt parent).rootEquivalent) } .nil)
    lifted
    (.cons startEqual finishEqual
      (child.edge.centeredValidCertificate curve differential child.center) (.nil _))
    (ChildMovementBound.cons (by
      rw [movementEqual]
      simpa only [Basic.quarterRadius_eq_mul_pow, pow_zero,
        Fraction.Field.mul_one_direct, -eq_self, -iff_self] using
          (le_refl (geometricMovement parent.edge.segment left.parameter right.parameter))) (ChildMovementBound.nil))
    (ChildModelErrorBound.cons childError (ChildModelErrorBound.nil))
    (by
      simp only [List.map_cons, List.map_nil,
        PathModel.displacementSum_cons,
        PathModel.displacementSum_nil, add_zero, -eq_self, -iff_self]
      exact Integration.PreparedSubdivisionModelCore.CenteredEdge.model_displacement child)

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
/-- A retained canonical center gives the exact original one-leaf local block. -/
theorem localBlockAtCenter_eq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} (parent : CenteredEdge curve differential)
    (left right : Endpoint) (diameter : Coordinate)
    (leaf : CheckedDirectGeometry.Leaf parent.edge left right diameter)
    (proper : left.parameter < right.parameter)
    (center : PreparedConstantModels.PreparedEdge.CenterState leaf.edge)
    (same : center = PreparedConstantModels.PreparedEdge.CenterState.canonical leaf.edge) :
    localBlockAtCenter parent left right diameter leaf proper center =
      localBlockOfLeaf parent left right diameter leaf proper := by
  cases same
  simp only [localBlockAtCenter, deferredRoot_eq, -eq_self, -iff_self]
  rfl

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
set_option genInjectivity false in
/-- Retained canonical center states indexed by an actual checked direct mesh.

Leaf certificates identify the full original centers, and split constructors preserve the exact left and right mesh
owners. -/
inductive Centers {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {parent :
      Purelib.Riemann.Integration.PreparedSubdivisionModelCore.PreparedEdge curve differential}
    {diameter : Coordinate} : {depth : Nat} → {left right : Endpoint} →
    CheckedDirectGeometry.Mesh parent diameter depth left right → Type
  /-- The retained center and canonical equality for one actual checked leaf. -/ | leaf {left right : Endpoint}
      (leaf : CheckedDirectGeometry.Leaf parent left right diameter)
      (proper : left.parameter < right.parameter)
      (center : PreparedConstantModels.PreparedEdge.CenterState leaf.edge)
      (equal : center = PreparedConstantModels.PreparedEdge.CenterState.canonical leaf.edge) :
      Centers (.leaf leaf proper)
  /-- Center certificates for the original left and right submeshes. -/ | split {depth : Nat} {left right : Endpoint}
      {first : CheckedDirectGeometry.Mesh parent diameter depth left (CheckedDirectGeometry.midpoint left right)}
      {last : CheckedDirectGeometry.Mesh parent diameter depth (CheckedDirectGeometry.midpoint left right) right}
      (head : Centers first) (tail : Centers last) : Centers (.split first last)

constructive_injectivity Centers

section
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Differentials
/-- Reconstruct a local block from the original mesh and its retained leaf centers.

Structural recursion preserves the original ordered split tree and appends the actual child blocks. -/
@[expose] def toLocal {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Basic.Differential genus}
    (parent : CenteredEdge curve differential) (diameter : Coordinate) :
    {depth : Nat} → {left right : Endpoint} →
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth left right) →
    Centers mesh → LocalBlock parent left right depth diameter
  | _, left, right, _, .leaf leaf proper center _ =>
      localBlockAtCenter parent left right diameter leaf proper center
  | depth + 1, left, right, .split first last, .split head tail =>
      localBlockAppend parent depth left right diameter
        (toLocal parent diameter first head) (toLocal parent diameter last tail)

/-- The center-based reconstruction equals the original checked local block. -/
theorem toLocal_eq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Basic.Differential genus}
    (parent : CenteredEdge curve differential) (diameter : Coordinate)
    {depth : Nat} {left right : Endpoint}
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth left right)
    (centers : Centers mesh) : toLocal parent diameter mesh centers =
      checkedLocalBlock parent diameter mesh := by
  induction centers with
  | leaf leaf proper center equal =>
      exact localBlockAtCenter_eq parent _ _ diameter leaf proper center equal
  | split head tail firstIH lastIH =>
      exact congrArg₂ (localBlockAppend parent _ _ _ diameter) firstIH lastIH

/-- Construct the original whole-parent block from its mesh and retained centers. -/
@[expose] def parentBlock {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Basic.Differential genus}
    (parent : CenteredEdge curve differential) {diameter : Coordinate} {depth : Nat}
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint)
    (centers : Centers mesh) : DirectParentBlock parent :=
  parentBlockOfLocal parent depth diameter (toLocal parent diameter mesh centers)

/-- Retained center reconstruction gives the exact original checked parent block. -/
theorem parentBlock_eq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Basic.Differential genus}
    (parent : CenteredEdge curve differential) {diameter : Coordinate} {depth : Nat}
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint)
    (centers : Centers mesh) : parentBlock parent mesh centers = checkedParentBlock parent mesh :=
  congrArg (parentBlockOfLocal parent depth diameter) (toLocal_eq parent diameter mesh centers)

end

open Purelib.Curves in
open Purelib.Curves.Hyperelliptic.Differentials in
set_option genInjectivity false in
/-- Canonical leaf centers indexed by the actual checked meshes of an ordered parent bank.

The dependent list preserves each original parent and mesh, including the common depth and diameter. -/
inductive BankCenters {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} {diameter : Coordinate} {depth : Nat} :
    {parents : List (CenteredEdge curve differential)} →
    CheckedDirectMeshes depth diameter parents → Type 2
  /-- The center bank for the empty checked mesh list. -/ | nil : BankCenters .nil
  /-- The retained centers for the actual first mesh and remaining mesh bank. -/ | cons {parent : CenteredEdge curve
    differential} {remaining : List (CenteredEdge curve differential)}
      {mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth parent.edge.left parent.edge.request.endpoint}
      {meshes : CheckedDirectMeshes depth diameter remaining}
      (head : Centers mesh) (tail : BankCenters meshes) : BankCenters (.cons mesh meshes)

constructive_injectivity BankCenters

section
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Differentials
/-- Reconstruct synchronized parent blocks from their actual mesh-indexed center bank.

Each block retains the original common depth and diameter, and the ordered parent bank is preserved structurally. -/
@[expose] def blocks {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Basic.Differential genus}
    {diameter : Coordinate} {depth : Nat} : {parents : List (CenteredEdge curve differential)} →
    (meshes : CheckedDirectMeshes depth diameter parents) → BankCenters meshes →
    SynchronizedDirectBlockRefinement depth diameter parents
  | [], .nil, .nil => .nil
  | parent :: _, .cons mesh meshes, .cons head tail =>
      .cons (parentBlock parent mesh head) rfl rfl (blocks meshes tail)

/-- The reconstructed block bank equals the original meshes' canonical block conversion. -/
theorem blocks_eq {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Basic.Differential genus}
    {diameter : Coordinate} {depth : Nat} {parents : List (CenteredEdge curve differential)}
    (meshes : CheckedDirectMeshes depth diameter parents) (centers : BankCenters meshes) :
    blocks meshes centers = meshes.toBlocks := by
  induction centers with
  | nil => rfl
  | cons head tail ih =>
      simp only [blocks, CheckedDirectMeshes.toBlocks, parentBlock_eq, ih, -eq_self, -iff_self]
      rfl

section
open Purelib.Riemann
open Purelib.RootIsolation.SquareRoot.Replay
/-- Root replay readiness is preserved by the exact direct query-owner transport. -/
theorem queryReady {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Basic.Differential genus}
    (parent : Integration.PreparedSubdivisionModelCore.PreparedEdge curve differential)
    (ready : QuadraticTrackReplay.Ready parent.cached.preparedOwner)
    (current : Endpoint) (position : Integration.PreparedSubdivisionModelCore.ParentPosition parent current) :
    QuadraticTrackReplay.Ready (CheckedDirectGeometry.queryOwnerAt parent current position) := by
  cases current with
  | mk parameter inside =>
      cases position with
      | mk fraction fractionInside equal =>
          dsimp only at equal
          subst parameter
          unfold CheckedDirectGeometry.queryOwnerAt
          exact QuadraticTrackReplay.transported _ ready _ _ _

/-- An actual checked leaf inherits root replay readiness from its original parent owner. -/
theorem leafReady {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Basic.Differential genus}
    {parent : Integration.PreparedSubdivisionModelCore.PreparedEdge curve differential} {diameter : Coordinate}
    (ready : QuadraticTrackReplay.Ready parent.cached.preparedOwner)
    {left right : Endpoint} (leaf : CheckedDirectGeometry.Leaf parent left right diameter) :
    QuadraticTrackReplay.Ready leaf.edge.cached.preparedOwner := by
  apply QuadraticTrackReplay.cached
  change QuadraticTrackReplay.Ready leaf.owner
  rw [leaf.owner_eq]
  exact queryReady parent ready left leaf.position

/-- Root replay readiness for every original prepared owner in a finite centered-edge bank. -/
@[expose] def AllReady {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source) →
      Prop
  | [] => True
  | parent :: parents => QuadraticTrackReplay.Ready parent.edge.cached.preparedOwner ∧ AllReady parents

end

open Purelib.Riemann in
/-- Appending two ready parent banks preserves readiness of every retained owner. -/
theorem AllReady.append {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} :
    ∀ {first second : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)},
      AllReady first → AllReady second → AllReady (first ++ second)
  | [], _, _, second => second
  | _ :: _, _, first, second => ⟨first.1, first.2.append second⟩

open Purelib.Riemann in
open Purelib.RootIsolation.SquareRoot.Replay in
/-- The reconstructed local block's actual child owners retain root replay readiness. -/
theorem toLocal_ready {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} (parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)
    (ready : QuadraticTrackReplay.Ready parent.edge.cached.preparedOwner)
    {diameter : Coordinate} {depth : Nat} {left right : Endpoint}
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth left right)
    (centers : Centers mesh) : AllReady (LocalBlock.children (toLocal parent diameter mesh centers)) := by
  induction centers with
  | leaf leaf proper center equal => exact ⟨leafReady ready leaf, trivial⟩
  | split head tail firstIH lastIH => exact firstIH.append lastIH

open Purelib.Riemann in
/-- Synchronized block reconstruction preserves readiness of all actual child owners. -/
theorem blocks_ready {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Basic.Differential genus} {diameter : Coordinate} {depth : Nat}
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve source)}
    (meshes : CheckedDirectMeshes depth diameter parents) (centers : BankCenters meshes)
    (ready : AllReady parents) : AllReady (blocks meshes centers).children := by
  induction centers with
  | nil => trivial
  | cons head tail ih =>
      exact (toLocal_ready _ ready.1 _ head).append (ih ready.2)

end

end Purelib.Riemann.Transport.PreparedDirectRefinementReplay

end
