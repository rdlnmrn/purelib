module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Geometry
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
public import Purelib.Riemann.Integration.PreparedSwitchedRefinements.CenteredState
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Linked
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.DependentProduct
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed

/-! # Root-closed states of the same actual transported member geometry

The retained shifted blocks already supply their actual covered parents,
endpoint Steps and open root chains. Their original join derives both the
geometric return and signed root return. Properness of each SAME covered
block supplies the existing refinement-state constructor; no source,
query, Point, root, subdivision or member is acquired again.

The new state is a view in the original root-safe refinement interface.
Its closed lift is the SAME whole representative used by every stage and
all six differential certificates of the retained member jet. Its centered
models are not substituted for the independently retained source models.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Closed (ClosedLiftedPath)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain allParentsProper_append)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements (DirectSwitchedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

/-- Properness of each original finite block is preserved by its literal ordered flattening. -/
private theorem proper_ofFn {genus : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus} :
    (size : Nat) → (words : Fin size → List (CenteredEdge curve basis)) →
      (∀ index, AllParentsProper (words index)) → AllParentsProper (List.ofFn words).flatten
  | 0, _, _ => True.intro
  | size + 1, words, proper => by
      rewrite [Data.List.OfFn.Basic.ofFn_succ]
      exact allParentsProper_append (proper 0)
        (proper_ofFn size (fun index => words index.succ) (fun index => proper index.succ))

variable {parameter offset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + offset)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    {admitted : Norm.Basic.normSq offset ≤ allocation.bound}

namespace Shifted

variable (retained : Shifted (target := target) source ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage)

/-- Every original shifted centered parent remains proper in the exact once-joined occurrence order.

The whole geometry factory identifies its literal flattened block word.
Each original CoveredSegment supplies properness even for stationary
physical displacements; repeated parents and their parameter slots are
not removed or merged.
-/
theorem parents_proper : AllParentsProper retained.geometry.parents := by
  have parentsEq := (congrArg ShiftedGeometry.parents retained.geometry_eq).trans
    (ShiftedGeometry.build_parents
    (parameter := parameter) (increment := offset) (frame := frame) (basis := basis) (target := target)
    (count := count) (firstParent := parent) (remaining := parents) (covered := covered) (floor := floor)
    (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
    source.prepared ranges allocation admitted widths retained.blocks chain roots)
  have proper : AllParentsProper
      (ShiftedGeometry.blockWords source.prepared ranges allocation admitted widths retained.blocks).flatten := by
    change AllParentsProper (List.ofFn (fun index =>
      (DependentProduct.get (parent :: parents) retained.blocks index).shifted.parents.covered.parents)).flatten
    exact proper_ofFn (parent :: parents).length _ (fun index =>
      (DependentProduct.get (parent :: parents) retained.blocks index).shifted.parents.covered.parents_proper)
  exact Eq.mpr (congrArg AllParentsProper parentsEq) proper

/-- Construct the existing root-closed state from the SAME retained joined geometry and signed root chain.

Both endpoint indices are the original source first lifted point. The root
name is the actual first parameter Step's root, and the existing joined
RootChain already returns to that very name. Only the centered-chain state
representation is constructed; no root/Point/source/member producer runs.
-/
def closedState :
    let first := DependentProduct.get (parent :: parents) retained.blocks 0
    RootClosedState (Fibre.frameCurve target) basis first.first.root.value.name :=
  ⟨DirectSwitchedState.ofCenteredPathChain retained.geometry.chain retained.parents_proper,
    rfl, retained.geometry.roots⟩

variable (state :
    let first := DependentProduct.get (parent :: parents) retained.blocks 0
    RootClosedState (Fibre.frameCurve target) basis first.first.root.value.name)
    (factory : state = retained.closedState)

include factory in
/-- A GIVEN retained closed-state value has exactly the original shifted geometry's parent list. -/
theorem closedState_parents : state.state.parents = retained.geometry.parents := by
  cases factory
  unfold closedState
  rfl

include factory in
/-- A GIVEN retained closed-state value follows the SAME complete ordered centered path. -/
theorem closedState_path : HEq state.state.path retained.geometry.chain.path := by
  cases factory
  unfold closedState
  exact heq_of_eq (DirectSwitchedState.ofCenteredPathChain_path retained.geometry.chain retained.parents_proper)

include factory in
/-- A GIVEN retained closed state stores the SAME complete original joined root chain. -/
theorem closedState_roots : HEq state.roots retained.geometry.roots := by
  cases factory
  unfold closedState
  rfl

include factory in
/-- The actual retained closed state's whole lift is the original joined representative at every finite stage. -/
theorem closedState_lift (stage : Nat) : state.state.closedLift state.closed =
    (constantCycle (parameter := parameter + offset) (frame := target) (basis := basis)
      retained.geometry.chain).liftedPath stage := by
  cases factory
  unfold closedState
  change (⟨startPoint parent,
      (DirectSwitchedState.ofCenteredPathChain retained.geometry.chain retained.parents_proper).path⟩ :
        ClosedLiftedPath 2) = ⟨startPoint parent, retained.geometry.chain.path⟩
  exact congrArg (fun path : LiftedPath 2 (startPoint parent) (startPoint parent) =>
    (⟨startPoint parent, path⟩ : ClosedLiftedPath 2))
    (DirectSwitchedState.ofCenteredPathChain_path retained.geometry.chain retained.parents_proper)

end Shifted

namespace LocalMember

variable (cached : LocalMember source ranges allocation roots widths
    targetCurrent targetFloor targetRootStage offset admitted)

/-- Construct the original root-closed state on this GIVEN complete member's actual target Frame and joined caches. -/
def closedState :
    let first := DependentProduct.get (parent :: parents) cached.member.blocks 0
    RootClosedState (Fibre.frameCurve cached.targetFrame) basis first.first.root.value.name :=
  cached.member.closedState

/-- The original member closed-state operation retains the SAME whole shifted-state constructor.

This equality is an owned readback of the once-bound representation. It
executes no member, source, root, stage or query construction and changes
none of the original dependent Frame or endpoint indices.
-/
theorem closedState_eq : cached.closedState = cached.member.closedState := by
  unfold closedState
  rfl

/-- Every actual jet stage has the SAME whole closed lift as a GIVEN once-bound member closed state.

The original member jet factory and cycle_at law identify its joined
geometry; the original shifted closed-state readback supplies the other
side. The actual value/first/second UniformPathCertificates therefore keep
that same geometry without changing any model or differential owner.
-/
theorem closedState_cycle
    (state :
      let first := DependentProduct.get (parent :: parents) cached.member.blocks 0
      RootClosedState (Fibre.frameCurve cached.targetFrame) basis first.first.root.value.name)
    (factory : state = cached.closedState) (stage : Nat) :
    cached.jet.cycle.liftedPath stage = state.state.closedLift state.closed :=
  (cached.cycle_at stage).trans
    (cached.member.closedState_lift state factory stage).symm

end LocalMember

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
