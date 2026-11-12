module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations

/-! # One global source-stage request on the actual joined shifted parents

The cached shifted geometry precedes allocation. One exact nonempty-list
view and original base-point transport supply the existing StageAttempt
constructor. It computes the count, Targets, source preparations and bank
once on that whole joined path. No local per-acquisition allocation is
retagged or reused as the global allocation.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Riemann.Topology

namespace StageAttempt

/-- Construct the existing single global attempt from the SAME complete nonempty cover and original closed chain. -/
def fromCovered {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) : StageAttempt covered chain index floor rootStage :=
  match covered with
  | .cons patch inside remaining => checkStage (frame := frame) patch inside remaining chain index floor rootStage

/-- The canonical covered-stage and retained-preparation factories have the same entire original attempt.

Only the original nonempty cover is eliminated. The equality preserves
its whole allocation, preparation product, first-match bank, checker data,
readiness decision and successful or unpaid StageResult without execution.
-/
theorem fromCovered_eq_ofPrepared
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :
    fromCovered covered chain index floor rootStage =
      ofPrepared covered chain (CellEndpoints.Targets.build chain.path index) rfl
        (prepareCovered covered floor (CellEndpoints.Targets.build chain.path index)) rootStage := by
  cases covered with
  | cons patch inside remaining =>
    exact checkStage_eq_ofPrepared (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) patch inside remaining chain index floor rootStage

/-- The retained whole covered-stage constructor uses the exact original prepareCovered output on its OWN Targets. -/
theorem fromCovered_prepared {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :
    (fromCovered covered chain index floor rootStage).2.1 =
      prepareCovered covered floor (fromCovered covered chain index floor rootStage).1.val := by
  cases covered with
  | cons patch inside remaining => exact checkStage_prepared patch inside remaining chain index floor rootStage

/-- The SAME complete source-factory equality retains its original prepared family without reexecuting that producer. -/
theorem prepared_of_factory {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)
    (factory : attempt = fromCovered covered chain index floor rootStage) :
    attempt.2.1 = prepareCovered covered floor attempt.1.val := by
  cases factory
  exact fromCovered_prepared covered chain index floor rootStage

/-- The actual covered-stage constructor retains the entire original checking product on its own caches. -/
theorem fromCovered_checks {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (index floor rootStage : Nat) :
    (fromCovered covered chain index floor rootStage).2.2.2.2.1 =
      checkParents covered (fromCovered covered chain index floor rootStage).2.1
        (fromCovered covered chain index floor rootStage).2.2.1.val rootStage := by
  cases covered with
  | cons patch inside remaining => exact checkStage_checks patch inside remaining chain index floor rootStage

/-- The exact whole original covered-stage factory retains the actual checking product without checking again. -/
theorem checks_of_factory {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count (parent :: parents))
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    {index floor rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)
    (factory : attempt = fromCovered covered chain index floor rootStage) :
    attempt.2.2.2.2.1 = checkParents covered attempt.2.1 attempt.2.2.1.val rootStage := by
  cases factory
  exact fromCovered_checks covered chain index floor rootStage

end StageAttempt

namespace ShiftedGeometry

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat} {point : LiftedPoint 2} {root : Named}
    (geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root)

/-- An actual first-parent view, original based chain and one complete global StageAttempt with its whole factory law.

The original joined geometry remains the owner. The shape equality changes
only the list index, retaining all patches and root chains. The stored
attempt allocates against the actual whole path and retains its original
bank and lookups, including every inconclusive finite Common request.
-/
@[expose] def Request (index floor rootStage : Nat) :=
  (shape : { value : CenteredEdge (Fibre.frameCurve target) basis ×
    List (CenteredEdge (Fibre.frameCurve target) basis) // geometry.parents = value.1 :: value.2 }) ×
  (chain : { value : CenteredPathChain (shape.val.1 :: shape.val.2)
    (start := PreparedParent.startPoint shape.val.1) (finish := PreparedParent.startPoint shape.val.1) //
    value = (geometry.chain.castParents shape.property).basedAtFirst }) ×
  { attempt : StageAttempt (frame := target) (geometry.covered.castParents shape.property)
      chain.val index floor rootStage //
    attempt = StageAttempt.fromCovered (frame := target) (geometry.covered.castParents shape.property)
      chain.val index floor rootStage }

namespace Request

variable {geometry}

/-- Cache one exact head view and one original global source-stage attempt on these already joined actual parents. -/
def build (geometry : ShiftedGeometry (target := target) (basis := basis) (count := count) point point root root)
    (nonempty : geometry.parents ≠ []) (index floor rootStage : Nat) : Request geometry index floor rootStage := by
  let shape : { value : CenteredEdge (Fibre.frameCurve target) basis ×
      List (CenteredEdge (Fibre.frameCurve target) basis) // geometry.parents = value.1 :: value.2 } :=
    match items : geometry.parents with
    | [] => False.elim (nonempty items)
    | parent :: parents => ⟨⟨parent, parents⟩, rfl⟩
  let chain := (geometry.chain.castParents shape.property).basedAtFirst
  let attempt := StageAttempt.fromCovered (frame := target) (geometry.covered.castParents shape.property)
    chain index floor rootStage
  exact ⟨shape, ⟨chain, rfl⟩, ⟨attempt, rfl⟩⟩

variable {index floor rootStage : Nat} (request : Request geometry index floor rootStage)

/-- Read the actual original first parent and unchanged remaining-list view of the joined shifted geometry. -/
@[expose] def shape :
    { value : CenteredEdge (Fibre.frameCurve target) basis ×
        List (CenteredEdge (Fibre.frameCurve target) basis) //
      geometry.parents = value.1 :: value.2 } := request.1

/-- Read the SAME global covering spine under its exact original head-view equality. -/
@[expose] def covered : CoveredParents count (request.shape.val.1 :: request.shape.val.2) :=
  geometry.covered.castParents request.shape.property

/-- Read the retained closed chain rebased at its actual first parent, without rebuilding any original cell. -/
@[expose] def chain : CenteredPathChain (request.shape.val.1 :: request.shape.val.2)
    (start := PreparedParent.startPoint request.shape.val.1)
    (finish := PreparedParent.startPoint request.shape.val.1) := request.2.1.val

/-- The actual whole global chain is the same joined chain transported only to its own original first base point. -/
theorem chain_eq : request.chain = (geometry.chain.castParents request.shape.property).basedAtFirst :=
  request.2.1.property

/-- Read the single retained global attempt with its original global Targets, source preparations, bank and lookups. -/
@[expose] def attempt : StageAttempt (frame := target) request.covered request.chain index floor rootStage :=
  request.2.2.val

/-- The exact original six-channel observation type at one retained global source occurrence and physical time.

This named type retains the complete original target frame, physical child,
prepared source cell, model, six requests and input fraction. It neither
queries a point nor copies any observation or preparation cache.
-/
@[expose] def Observation (sourceIndex : Fin (request.shape.val.1 :: request.shape.val.2).length)
    (input : Rational) :=
  CellModels.Observations target
    (PreparedParent.liftedCell ((request.shape.val.1 :: request.shape.val.2)[
      sourceIndex.val]'sourceIndex.isLt))
    (request.attempt.2.1.entry sourceIndex).preparation.cell.models
    (request.attempt.2.1.entry sourceIndex).preparation.query.requests input

/-- Read the identical global attempt's original first-match vertex bank, retaining its actual allocation. -/
@[expose] def bank := request.attempt.2.2.1.val

/-- The complete retained attempt executes the original global constructor on this SAME whole joined path. -/
theorem attempt_eq : request.attempt =
    StageAttempt.fromCovered (frame := target) request.covered request.chain index floor rootStage :=
  request.2.2.property

/-- The actual incoming request retains the canonical preparation at its own exact cached Targets.

The original whole attempt factory equation transports the original
fromCovered preparation law. No Targets, source preparation, bank or
checking cache is reconstructed or replaced.
-/
theorem prepared_eq : request.attempt.2.1 =
    prepareCovered request.covered floor request.attempt.1.val :=
  StageAttempt.prepared_of_factory (parameter := parameter + increment) (frame := target)
    (basis := basis) (count := count) (parent := request.shape.val.1) (parents := request.shape.val.2)
    (index := index) (floor := floor) (rootStage := rootStage)
    request.covered request.chain request.attempt request.attempt_eq

/-- Complete that exact actual global request from its own distinct bank and the already derived global closed roots.

Distinctness concerns this actual global first-match bank. Root connectivity
has already been derived from the original signed cycle and paid endpoint
Steps. Completion reuses all original ready Commons, requests and source
lists; it acquires additional Common data only for the original unpaid cases.
-/
def complete (distinct : Vertex.Bank.Distinct request.bank) :
    StageAttempt.Completed (frame := target) request.covered request.chain index floor rootStage :=
  let roots := PreparedBankRootChains.RootChain.castChildren request.shape.property geometry.roots
  StageAttempt.Completed.acquire (frame := target) request.attempt distinct roots

/-- Complete the SAME actual globally allocated request from its stored successful endpoint checks without Distinct.

The original attempt, bank, target allocation, preparations, signed source
occurrences and selected primitive samples remain unchanged. Its stored
successful Stage and all ready common-owner/admission caches are reused;
no shift, continuation, root request or Stage factory is run again.
-/
def completeReady
    (paid : request.attempt.Ready) :
    StageAttempt.Completed (frame := target) request.covered request.chain index floor rootStage :=
  StageAttempt.Completed.ofReady (frame := target) request.attempt paid

end Request

end ShiftedGeometry

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
