module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay
public import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Integration.CheckedDirectGeometry
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Readings.BoundedPreparedSource
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

public section

/-! Exact deferred-refiner provenance through preparation. These proofs do
not execute the preparation a second time to classify its retained result. -/

namespace Purelib.Riemann.Transport.PreparedDeferredRecipeReplay

open Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay (Coordinate Gaussian Box)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Integration Purelib.Riemann.RootContinuation Purelib.Riemann.Branches Purelib.Riemann.Transport

open Purelib.RootIsolation in
/-- The quadratic sample recipe marks the given owner as deferred. -/
abbrev Deferred {parameter : Gaussian} (owner : Owner parameter) : Prop :=
  SquareRoot.Replay.QuadraticSampleReplay.Recipe.Matches .deferred owner

section
open Purelib.RootIsolation
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Coefficient-based strengthening produces an owner matching the deferred recipe. -/
private theorem coefficient {parameter : Gaussian} (owner : Owner parameter) :
    Deferred (QuadraticCoefficientClearance.strengthen owner) :=
  SquareRoot.Replay.QuadraticSampleReplay.matches_strengthen owner

/-- Exact quadratic strengthening preserves a deferred owner recipe.

Uses the strengthening procedure's exact source-or-deferred alternative for the original owner. -/
private theorem strengthened {parameter : Gaussian} (owner : Owner parameter) (ready : Deferred owner) :
    Deferred (ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner) := by
  rcases ExactQuadraticOwnerClearance.strengthenQuadraticOwner_source_or_deferred owner with same | ⟨_, _, same⟩
  · rw [same]; exact ready
  · rw [same]; exact SquareRoot.Replay.QuadraticSampleReplay.matches_ownerOfState _ _

end

open Purelib.RootIsolation in
/-- Recentering preserves the owner's deferred recipe.

Either retains the original owner or uses the reset's exact deferred-state certificate. -/
private theorem recentered {parameter : Gaussian} (owner : Owner parameter) (ready : Deferred owner) :
    Deferred (PreparedSheetContinuation.recentered owner) := by
  unfold PreparedSheetContinuation.recentered
  split
  · exact ready
  · rename_i reset _
    rw [reset.deferred]
    exact SquareRoot.Replay.QuadraticSampleReplay.matches_ownerOfState _ _

section Preparation

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {start finish : Gaussian} (segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start
    finish)
  (current : PreparedSheetContinuation.Endpoint)
  (owner : Owner (polynomial.eval (segment.pointAt current.parameter)))
  (request : PreparedSheetContinuation.StepRequest)

open Purelib.Riemann.Branches in
/-- Uniform preparation produces an owner matching the deferred recipe. -/
private theorem uniform : Deferred (PreparedSheetContinuation.uniformPrepared segment current owner request) :=
  coefficient _

open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- Baseline preparation preserves the incoming owner's deferred recipe.

Follows the original retained-owner, strengthening, checked-preparation and uniform-preparation branches. -/
private theorem baseline (ready : Deferred owner) :
    Deferred (PreparedSheetContinuation.baselinePrepared segment current owner request) := by
  unfold PreparedSheetContinuation.baselinePrepared
  split
  · split
    · exact ready
    · exact strengthened _ ready
  · split
    · rename_i accepted found
      exact SquareRoot.Replay.QuadraticSampleReplay.matches_checkedPreparation _ _ _ _ accepted found
    · exact uniform segment current owner request

section
open Purelib.Riemann.Branches
/-- A coefficient retry preserves the deferred recipe of its moved owner.

Uses the retry's retained origin witness to identify coefficient, moved-baseline or second-reset preparation. -/
private theorem retried
    (moved : Owner (polynomial.eval (segment.pointAt current.parameter))) (ready : Deferred moved)
    (retry : PreparedSheetContinuation.CoefficientRetry segment current owner request moved) :
    Deferred (PreparedSheetContinuation.CoefficientRetry.value retry) := by
  cases PreparedSheetContinuation.CoefficientRetry.origin retry with
  | coefficient equal => rw [equal]; exact coefficient _
  | movedCoefficient equal => rw [equal]; exact coefficient _
  | movedBaseline equal =>
      rw [equal]
      exact baseline segment current moved request ready
  | secondReset equal => rw [equal]; exact recentered _ ready

/-- Preparation with a finite retry count preserves a deferred recipe.

Induction follows the actual retry procedure, retaining recentering and coefficient-origin certificates at each step. -/
private theorem withRetries (ready : Deferred owner) (count : Nat) :
    Deferred (PreparedSheetContinuation.preparedWithRetries segment current owner request count) := by
  induction count generalizing owner with
  | zero =>
      unfold PreparedSheetContinuation.preparedWithRetries
      dsimp only
      split
      · exact baseline segment current owner request ready
      · exact uniform segment current owner request
  | succ count ih =>
      unfold PreparedSheetContinuation.preparedWithRetries
      dsimp only
      split
      · exact baseline segment current owner request ready
      · split
        · split
          · exact uniform segment current owner request
          · exact ih _ (recentered owner ready)
        · split
          · rename_i retry _
            exact retried segment current owner request _ (recentered owner ready) retry
          · exact ih _ (recentered owner ready)

end

/-- The original prepared continuation preserves a deferred incoming recipe.

Instantiates the finite retry invariant at the procedure's retained retry count. -/
theorem prepared (ready : Deferred owner) :
    Deferred (PreparedSheetContinuation.prepared segment current owner request) := by
  unfold PreparedSheetContinuation.prepared
  exact withRetries segment current owner request ready _

/-- A cached prepared source retains the deferred recipe of its incoming owner.

Uses the cache's exact prepared-owner identity and the preparation invariant. -/
theorem cached (ready : Deferred owner)
    (cache : PreparedSheetContinuation.CachedSource segment current owner request) :
    Deferred cache.preparedOwner := by
  rw [cache.preparedOwner_eq]
  exact prepared segment current owner request ready

end Preparation

open Purelib.RootIsolation in
/-- Successful checked owner transport yields a deferred recipe.

Retains the checked displacement, reserve and boundary-clearance identities of the actual carried state. -/
theorem carried {source target : Gaussian} {ambient : Box}
    {state : SquareRoot.Replay.PreparedOwnerTransportReplay.State source ambient} {reserve : Coordinate}
    (result : SquareRoot.Replay.PreparedOwnerTransportReplay.Checked state target reserve) : Deferred result.value := by
  rw [result.value_eq]
  rw [← SquareRoot.Replay.PreparedOwnerTransportReplay.carriedState_owner_eq_reservedTransport state
    result.sourceNonzero result.targetNonzero result.different result.small
    (by rw [← result.displacement_eq]; exact result.leftSmall)
    (by rw [← result.displacement_eq]; exact result.rightSmall)
    (by rw [← result.displacement_eq]; exact result.bottomSmall)
    (by rw [← result.displacement_eq]; exact result.topSmall)
    reserve (by rw [← result.carried_eq]; exact result.reserveSmall)]
  exact SquareRoot.Replay.QuadraticSampleReplay.matches_ownerOfState _ _

open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A retained obstruction to certifying an owner's deferred recipe.

Distinguishes an inherited owner with no recipe certificate from an explicit failed transport check on the original
state and target. -/
inductive Issue where
  /-- Original owner whose deferred recipe has no retained certificate. -/ | inherited {parameter : Gaussian} (owner :
    Owner parameter)
  /-- Original transport state, target and reserve together with the exact failed check. -/ | transport {source :
    Gaussian} {ambient : Box}
      (state : SquareRoot.Replay.PreparedOwnerTransportReplay.State source ambient) (target : Gaussian)
      (reserve : Coordinate) (failure : SquareRoot.Replay.PreparedOwnerTransportReplay.Failure state target reserve)

constructive_injectivity Issue

/-- A deferred-recipe certificate or its retained obstruction. -/
abbrev Outcome {parameter : Gaussian} (owner : Owner parameter) :=
  Except Issue (PLift (Deferred owner))

/-- A deferred computation of the recipe outcome for an exact owner. -/
abbrev History {parameter : Gaussian} (owner : Owner parameter) := Thunk (Outcome owner)

/-- Retain an uncertified owner's inherited issue as a deferred history. -/
@[expose] def History.inherited {parameter : Gaussian} (owner : Owner parameter) : History owner :=
  ⟨fun _ => .error (.inherited owner)⟩

/-- Retain an exact deferred-recipe certificate as a successful history. -/
@[expose] def History.deferred {parameter : Gaussian} (owner : Owner parameter) (same : Deferred owner) : History owner
  :=
  ⟨fun _ => .ok ⟨same⟩⟩

open Purelib.Data.Gaussian in
open Purelib.RootIsolation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Check the recipe outcome of the original reserved owner transport.

Reuses the supplied owner's captured initial state. Stationary transport consults its retained history; other failures
retain the exact check witness and successful transport yields its deferred certificate. -/
@[expose] def transport {source target : Gaussian} (owner : Owner source) (history : History owner)
    (nonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < owner.track.initial.clearance.bound)
    (reserve : Coordinate) :
    Outcome (ExactQuadraticOwnerClearance.reservedTransport owner nonzero small reserve) := by
  let restored : SquareRoot.Replay.PreparedRootStateReplay.Checked _ owner.ambient
      (SquareRoot.Replay.PreparedRootStateReplay.capture owner.track.initial) := ⟨owner.track.initial, rfl⟩
  match SquareRoot.Replay.PreparedOwnerTransportReplay.check restored.state target reserve with
  | .error failure =>
      cases failure with
      | stationary same =>
          exact match history.get with
          | .error issue => .error issue
          | .ok retained => .ok ⟨SquareRoot.Replay.QuadraticSampleReplay.matches_stationaryTransport
              .deferred owner retained.down nonzero small reserve same⟩
      | sourceZero zero => exact .error (.transport restored.state target reserve (.sourceZero zero))
      | targetZero zero => exact .error (.transport restored.state target reserve (.targetZero zero))
      | clearance field displacement equal failed =>
          exact .error (.transport restored.state target reserve (.clearance field displacement equal failed))
      | reserve displacement equal originalSmall bound boundEq failed =>
          exact .error (.transport restored.state target reserve
            (.reserve displacement equal originalSmall bound boundEq failed))
  | .ok result =>
      exact .ok ⟨by rw [← result.eq_original owner restored]; exact carried result⟩

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

open Purelib.Curves.Hyperelliptic in
/-- Check the recipe outcome for an exact direct query of a prepared edge.

Uses the cached prepared owner's history and the original query position, clearance and reserve data. -/
@[expose] def query {genus : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    (parent : PreparedEdge curve differential) (history : History parent.cached.preparedOwner)
    (fraction : Coordinate) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Outcome (parent.directQueryOwner fraction inside) :=
  transport parent.cached.preparedOwner history _ _ _

/-- Transport a deferred recipe along an equality of parameter indices. -/
private theorem deferred_cast_parameter (parameter : Coordinate → Gaussian)
    {first second : Coordinate} (same : first = second)
    (owner : Owner (parameter first)) (ready : Deferred owner) :
    Deferred (cast (congrArg (fun value => Owner (parameter value)) same) owner) := by
  cases same
  exact ready

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Integration
/-- The exact direct-query owner transport preserves a deferred recipe.

Uses the retained parent-position equation to cast the original owner without replacing its mathematical identity. -/
private theorem queryOwnerAt_deferred {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} (parent : PreparedEdge curve differential)
    (current : PreparedSheetContinuation.Endpoint)
    (position : PreparedSubdivisionModelCore.ParentPosition parent current)
    (ready : Deferred (parent.directQueryOwner position.fraction position.inside)) :
    Deferred (CheckedDirectGeometry.queryOwnerAt parent current position) := by
  unfold CheckedDirectGeometry.queryOwnerAt
  exact deferred_cast_parameter (fun value => curve.polynomial.eval (parent.segment.pointAt value))
    position.parameter_eq _ ready

/-- Build a deferred recipe history for a retained direct-refinement leaf.

Checks the parent's original direct query and transports its certificate through the leaf's owner identity and cached
preparation; check failures retain their original issue. -/
@[expose] def leafHistory {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus} {parent : PreparedEdge curve differential}
    {diameter : Coordinate} {left right : PreparedSheetContinuation.Endpoint}
    (history : History parent.cached.preparedOwner)
    (leaf : CheckedDirectGeometry.Leaf parent left right diameter) :
    History leaf.edge.cached.preparedOwner := ⟨fun _ =>
  match query parent history leaf.position.fraction leaf.position.inside with
  | .error issue => .error issue
  | .ok checked =>
      have incoming : Deferred leaf.owner := by
        rw [leaf.owner_eq]
        exact queryOwnerAt_deferred parent left leaf.position checked.down
      .ok ⟨cached parent.segment left leaf.owner
        (PreparedEdgeRecasting.directRequest right diameter leaf.positive)
        incoming leaf.prepared.cached⟩⟩

end

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Transport.PreparedDirectRefinementReplay (Centers BankCenters)

open Purelib.Curves.Hyperelliptic in
/-- Owner-indexed recipe histories for an ordered list of centered parents.

Stores one deferred outcome for each parent's actual cached prepared owner. -/
@[expose] def Histories {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source :
  Differentials.Basic.Differential genus} :
    List (CenteredEdge curve source) → Type
  | [] => Unit
  | parent :: parents => History parent.edge.cached.preparedOwner × Histories parents

open Purelib.Curves.Hyperelliptic
/-- Build inherited histories for every original centered parent.

The ordered history bank retains each parent's exact cached prepared owner as an uncertified inherited issue. -/
@[expose] def Histories.inherited {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source :
  Differentials.Basic.Differential genus} :
    (parents : List (CenteredEdge curve source)) → Histories parents
  | [] => ()
  | parent :: parents => ⟨History.inherited parent.edge.cached.preparedOwner, inherited parents⟩

/-- Append two ordered banks of owner-indexed recipe histories. -/
@[expose] def Histories.append {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source :
  Differentials.Basic.Differential genus} :
    {first second : List (CenteredEdge curve source)} →
    Histories first → Histories second → Histories (first ++ second)
  | [], _, _, second => second
  | _ :: _, _, first, second => ⟨first.1, append first.2 second⟩

/-- Replay histories through the original local checked refinement tree.

Leaf histories use the exact retained parent queries; split histories follow the same first/last child order and
supplied center witnesses. -/
@[expose] def Histories.toLocal {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source :
  Differentials.Basic.Differential genus}
    (parent : CenteredEdge curve source) (history : History parent.edge.cached.preparedOwner)
    {diameter : Coordinate} : {depth : Nat} → {left right : PreparedSheetContinuation.Endpoint} →
    (mesh : CheckedDirectGeometry.Mesh parent.edge diameter depth left right) →
    (centers : Centers mesh) →
    Histories (PreparedDirectDyadicRefinements.LocalBlock.children
      (PreparedDirectRefinementReplay.toLocal parent diameter mesh centers))
  | _, _, _, _, .leaf leaf _ _ _ => ⟨leafHistory history leaf, ()⟩
  | _, _, _, .split first last, .split head tail =>
      Histories.append (toLocal parent history first head) (toLocal parent history last tail)

/-- Replay recipe histories through a retained bank of checked direct meshes.

Pairs each original parent history with its actual mesh and center witnesses, preserving the resulting child-block
order. -/
@[expose] def Histories.blocks {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source :
  Differentials.Basic.Differential genus}
    {diameter : Coordinate} {depth : Nat} : {parents : List (CenteredEdge curve source)} →
    (meshes : PreparedDirectDyadicRefinements.CheckedDirectMeshes depth diameter parents) →
    (centers : BankCenters meshes) → Histories parents →
    Histories (PreparedDirectRefinementReplay.blocks meshes centers).children
  | [], .nil, .nil, _ => ()
  | parent :: _, .cons mesh meshes, .cons head tail, histories =>
      Histories.append (toLocal parent histories.1 mesh head) (blocks meshes tail histories.2)

end Purelib.Riemann.Transport.PreparedDeferredRecipeReplay

end
