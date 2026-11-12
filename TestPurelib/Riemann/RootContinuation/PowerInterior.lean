module

import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power.Interior
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Algebraic
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Arithmetic
import TestPurelib.Riemann.RootReconditioning

namespace TestPurelib.Riemann.RootContinuation.PowerInterior

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.RootIsolation
open Purelib.RootIsolation.Progressive.Power
open Purelib.RootIsolation.Power.Unit.Move.Budget (UnitMoveSmall)
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Power

section

variable {source target : Canonical} (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    {index : (Interior.Source sourceUnit degree degreeTwo).Index}
    (original : Root (Interior.Source sourceUnit degree degreeTwo) index)
    (moved : Root (Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small)
      (Interior.movedIndex sourceUnit targetUnit degree degreeTwo small index))
    (selected : Root (Frame.Basic.chamberFrame (nonzero_of_normSq_eq_one targetUnit)
      degree degreeTwo) (Interior.selectedIndex sourceUnit targetUnit degree degreeTwo small index))
    (robust : Root (Unit.Frame.robustChamberFrame (nonzero_of_normSq_eq_one targetUnit)
      targetUnit degree degreeTwo) ((Interior.Robust targetUnit degree degreeTwo).matching.forward
        (Interior.selectedIndex sourceUnit targetUnit degree degreeTwo small index)))
    (bridges : Interior.Bridges sourceUnit targetUnit degree degreeTwo small index)

local notation "actual" => (Trace.cons (source := original) moved
  (Trace.cons selected (Trace.cons robust (Trace.nil robust))))
local notation "family" => (Interior.ofTrace sourceUnit targetUnit degree degreeTwo small actual bridges)

/-- All original path occurrences and their complete numerical roots remain in the assembled trace. -/
example : (family).original = actual := (family).original_eq

/-- The actual original source root remains the source of the pointwise family. -/
example : (family).source = original := (family).source_eq

/-- The first original moved occurrence is retained rather than reconstructed from an equation. -/
example : (family).first.target = moved := (family).first.target_eq

/-- The second selected occurrence is retained even though its defining polynomial is constant in time. -/
example : (family).remaining.first.target = selected := (family).remaining.first.target_eq

/-- The third original robust occurrence is retained with its own original numerical program. -/
example : (family).remaining.remaining.first.target = robust := (family).remaining.remaining.first.target_eq

/-- The first selected bridge remains the same complete actual original bridge cache. -/
example : (family).first.bridge.val = bridges.move.val :=
  (family).first.bridge.property.trans bridges.move.property.symm

/-- The second selected bridge remains its complete original same-polynomial refinement owner. -/
example : (family).remaining.first.bridge.val = bridges.rebase.val :=
  (family).remaining.first.bridge.property.trans bridges.rebase.property.symm

/-- The third selected bridge remains its independent original robust-source refinement owner. -/
example : (family).remaining.remaining.first.bridge.val = bridges.robust.val :=
  (family).remaining.remaining.first.bridge.property.trans bridges.robust.property.symm

/-- Every rational parameter uses its actual original bridge point owner, with no replacement by a fixed root. -/
example (time : Rational) (inside : InteriorStep.Inside time) :
    let piece := (family).remaining.first
    ((piece.caches time inside).owner.val).box = piece.bridge.val.box := by
  let piece := (family).remaining.first
  let cached := piece.caches time inside
  exact cached.owner_box

/-- Every first-piece numerical observation remains inside its actual selected original bridge. -/
example (time : Rational) (inside : InteriorStep.Inside time) (stage : Nat) :
    bridges.move.val.box.Contains (((family).first.caches time inside).root.approximation.sample stage) := by
  have contains := (family).first.sample_inside time inside stage
  have same := (family).first.bridge.property.trans bridges.move.property.symm
  exact (congrArg (fun bridge => bridge.box.Contains
    (((family).first.caches time inside).root.approximation.sample stage)) same).mp contains

end

section

open Purelib.Riemann.RootContinuation.CoherentRoot

/-- Retained coefficient views produce the identical complete original point cache. -/
example {left right : GaussianPolynomial} (bridge : Owner.Bridge.Basic.OwnerBridge left right)
    (inputs : InteriorStep.Inputs bridge) (first : { value : GaussianPolynomial // value = left })
    (second : { value : GaussianPolynomial // value = right }) (time : Rational) (inside : InteriorStep.Inside time) :
    InteriorStep.Cached.buildFromPolynomials bridge inputs first second time inside =
      InteriorStep.Cached.build bridge inputs time inside :=
  InteriorStep.Cached.buildFromPolynomials_eq bridge inputs first second time inside

end

section

private def degree : RootDegree := ⟨3, by decide⟩
private theorem degreeTwo : 2 ≤ degree.value := by decide

local notation "firstVertex" => TestPurelib.Riemann.RootReconditioning.sourceVertex degree degreeTwo
local notation "lastVertex" => TestPurelib.Riemann.RootReconditioning.targetVertex degree degreeTwo
local notation "small" => TestPurelib.Riemann.RootReconditioning.smallMove degree degreeTwo

/-- The actual nonstationary cubic source fixture accepts the genuine whole-parameter construction on its own trace. -/
example {index : (Interior.Source (firstVertex).unit degree degreeTwo).Index}
    {original : Root (Interior.Source (firstVertex).unit degree degreeTwo) index}
    (trace : Trace
      (Unit.Move.Path.unitSmallMovePath (firstVertex).unit (lastVertex).unit degree degreeTwo small) index original)
    (bridges : Interior.Bridges (firstVertex).unit (lastVertex).unit degree degreeTwo small index) :
    (Interior.ofTrace (firstVertex).unit (lastVertex).unit degree degreeTwo small trace bridges).original = trace :=
  (Interior.ofTrace (firstVertex).unit (lastVertex).unit degree degreeTwo small trace bridges).original_eq

end

section

variable {source target : Canonical} (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    {index : (Interior.Source sourceUnit degree degreeTwo).Index}
    {original : Root (Interior.Source sourceUnit degree degreeTwo) index}
    (trace : Trace (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small) index original)
    (caches : Interior.Bridges.Caches sourceUnit targetUnit degree degreeTwo small index)

local notation "actual" => Interior.prepare sourceUnit targetUnit degree degreeTwo small trace caches
local notation "bridges" => Interior.Bridges.fromCaches sourceUnit targetUnit degree degreeTwo small caches

/-- Runtime attachment retains the complete original numerical trace, including every source and endpoint cache. -/
example : (actual).original = trace := (actual).original_eq

/-- Runtime attachment physically retains the same complete source, matching refinement and robust source parents. -/
example : (actual).caches = caches :=
  Interior.prepare_caches sourceUnit targetUnit degree degreeTwo small trace caches

/-- The actual retained bridges are the once-computed original cache construction. -/
example : (actual).bridges = Interior.Bridges.fromCaches sourceUnit targetUnit degree degreeTwo small (actual).caches :=
  (actual).bridges_eq

/-- The actual interior uses those same retained bridges and the same original trace. -/
example : (actual).interior =
    Interior.ofTrace sourceUnit targetUnit degree degreeTwo small (actual).original (actual).bridges :=
  (actual).computed

/-- The exact selected occurrence is read from the actual retained complete matching once. -/
example : Unit.Rebase.Matching.Preparation.selected caches.selection =
    Unit.Rebase.Matching.unitRebaseMap sourceUnit targetUnit degree degreeTwo small
      (Interior.movedIndex sourceUnit targetUnit degree degreeTwo small index) :=
  Unit.Rebase.Matching.Preparation.selected_eq caches.selection

/-- The actual three cached bridges produce exactly the original ordered selected box list. -/
example : (Interior.Bridges.boxes sourceUnit targetUnit degree degreeTwo small bridges).val =
    (Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small).bridgeBoxes index :=
  (Interior.Bridges.boxes sourceUnit targetUnit degree degreeTwo small bridges).property

/-- Sharing the actual computed bridges preserves the complete original trace attachment result. -/
example : Interior.prepareWithBridges sourceUnit targetUnit degree degreeTwo small trace caches bridges rfl =
    Interior.prepare sourceUnit targetUnit degree degreeTwo small trace caches :=
  Interior.prepareWithBridges_eq sourceUnit targetUnit degree degreeTwo small trace caches bridges rfl

/-- The move bridge retains the actual original source box. -/
example : (bridges).move.val.box = caches.source.owner.box :=
  Interior.Bridges.fromCaches_move_box sourceUnit targetUnit degree degreeTwo small caches

/-- The second bridge retains the already computed matching refinement's box. -/
example : (bridges).rebase.val.box = caches.selection.val.refined.box :=
  Interior.Bridges.fromCaches_rebase_box sourceUnit targetUnit degree degreeTwo small caches

/-- The third bridge retains the exact original robust source's box at the selected occurrence. -/
example : (bridges).robust.val.box = caches.targetSource.val.box :=
  Interior.Bridges.fromCaches_robust_box sourceUnit targetUnit degree degreeTwo small caches

/-- Both original rebase endpoint clearances consume the actual saved matching state's bound. -/
example : (Unit.Rebase.Overlap.Preparation.fromSelection caches.selection).val.leftClearance.bound =
      caches.selection.val.refined.clearance.bound ∧
    (Unit.Rebase.Overlap.Preparation.fromSelection caches.selection).val.rightClearance.bound =
      caches.selection.val.refined.clearance.bound :=
  Unit.Rebase.Overlap.Preparation.fromSelection_bounds caches.selection

/-- Both robust rebase endpoint clearances consume the actual saved source's bound. -/
example : (Unit.Frame.Overlap.Preparation.fromSource (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo
      (Unit.Rebase.Matching.Preparation.selected caches.selection) caches.targetSource).val.leftClearance.bound =
      caches.targetSource.val.clearance.bound ∧
    (Unit.Frame.Overlap.Preparation.fromSource (nonzero_of_normSq_eq_one targetUnit) targetUnit degree degreeTwo
      (Unit.Rebase.Matching.Preparation.selected caches.selection) caches.targetSource).val.rightClearance.bound =
      caches.targetSource.val.clearance.bound :=
  Unit.Frame.Overlap.Preparation.fromSource_bounds _ _ _ _ _ caches.targetSource

end

section

open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)

/-- Reading an authenticated cached ambient retains the complete original residual and its numerical program. -/
example {frame : ChamberFrame} {index : frame.Index} (root : Root frame index)
    (box : Purelib.Geometry.Rational.Box) (same : box = (frame.owner index).box) :
    root.residualFromBox box same = root.certificate.residualCertificate := root.residualFromBox_eq box same

/-- The algebraic attachment consumes the actual initial box without changing its original samples. -/
example {frame : ChamberFrame} {index : frame.Index} (root : Root frame index) (stage : Nat) :
    root.algebraic.residual.source.sample stage = root.certificate.approximation.sample stage :=
  root.algebraic_sample stage

/-- Cached ambient arithmetic keeps both complete original root records even for distinct input frames. -/
example {firstFrame secondFrame : ChamberFrame} {firstIndex : firstFrame.Index} {secondIndex : secondFrame.Index}
    (operation : Purelib.Polynomial.Dense.Companion.Operation)
    (first : Root firstFrame firstIndex) (second : Root secondFrame secondIndex) :
    (first.arithmetic operation second).first = first.certificate ∧
      (first.arithmetic operation second).second = second.certificate :=
  ⟨(first.arithmetic operation second).first_eq, (first.arithmetic operation second).second_eq⟩

/-- Retained ambient arithmetic uses precisely the unchanged original root samples at every index. -/
example {firstFrame secondFrame : ChamberFrame} {firstIndex : firstFrame.Index} {secondIndex : secondFrame.Index}
    (operation : Purelib.Polynomial.Dense.Companion.Operation)
    (first : Root firstFrame firstIndex) (second : Root secondFrame secondIndex) (stage : Nat) :
    (first.arithmetic operation second).result.sample stage =
      operation.value (first.certificate.approximation.sample stage) (second.certificate.approximation.sample stage) :=
  (first.arithmetic operation second).result_sample stage

/-- The bounded endpoint reader identifies the actual original selected occurrence without another matching. -/
example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (trace : Trace path index source) :
    trace.finalIndex.val = path.finalIndex index := trace.finalIndex.property

/-- The empty cached trace supplies its exact stored original bounded index. -/
example {frame : ChamberFrame} {index : frame.Index} (source : Root frame index) :
    (Trace.nil source).finalIndex.val = index := rfl

/-- Starting-index transport leaves the exact original cache in an empty trace. -/
example {frame : ChamberFrame} {index other : frame.Index} (same : index = other) (source : Root frame index) :
    Trace.castIndex same (.nil source) = .nil (Root.transport same source) := Trace.castIndex_nil same source

/-- Reversing an actual retained trace returns the identical original source cache. -/
example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (trace : Trace path index source) :
    Root.transport (Trace.endpointIndex_reverse path index) trace.reverse.endpoint = source :=
  Trace.reverse_endpoint trace

/-- A retained box list reverses to exactly the original reverse path's selected boxes. -/
example {start finish : ChamberFrame} (path : ChamberPath start finish) (index : start.Index)
    (boxes : { value : List Purelib.Geometry.Rational.Box // value = path.bridgeBoxes index }) :
    (path.reverseBridgeBoxes index boxes).val = path.reverse.bridgeBoxes (path.finalIndex index) :=
  (path.reverseBridgeBoxes index boxes).property

/-- The empty prefix is the exact original source occurrence, even for an arbitrary retained remaining trace. -/
example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (trace : Trace path index source) : trace.empty = .nil source := trace.empty_eq

/-- The cached path is the whole original path, including its actual frame and overlap records. -/
example {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (trace : Trace path index source) : trace.path.val = path := trace.path.property

/-- Transporting an already computed trace to its actual path and back preserves the complete original cache tree. -/
example {start finish : ChamberFrame} {before after : ChamberPath start finish} {index : start.Index}
    {source : Root start index} (same : before = after) (trace : Trace before index source) :
    Trace.castPath same.symm (Trace.castPath same trace) = trace := Trace.castPath_inverse same trace

/-- Original prepared owner records survive both directions of the same whole-path index transport. -/
example {start finish : ChamberFrame} {before after : ChamberPath start finish} {index : start.Index}
    (same : before = after) (owners : Trace.Owners before index) :
    Trace.Owners.castPath same.symm (Trace.Owners.castPath same owners) = owners :=
  Trace.Owners.castPath_inverse same owners

/-- The saved complete target frame supplies the identical full original three-overlap path. -/
example {source target : Canonical} (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo) :
    (Unit.Move.Path.Preparation.fromFrame sourceUnit targetUnit degree degreeTwo small prepared).val =
      Unit.Move.Path.unitSmallMovePath sourceUnit targetUnit degree degreeTwo small :=
  (Unit.Move.Path.Preparation.fromFrame sourceUnit targetUnit degree degreeTwo small prepared).property

/-- Reading the saved count preserves the complete original robust overlap, including both map functions. -/
example {parameter : Canonical} (unit : normSq parameter = 1) (degree : RootDegree)
    (degreeTwo : 2 ≤ degree.value)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one unit) degree degreeTwo) :
    (Unit.Frame.Overlap.Preparation.fromFrame (nonzero_of_normSq_eq_one unit) unit degree degreeTwo prepared).val =
      prepared.frame_eq.symm ▸ Unit.Frame.Overlap.isolationRobustOverlap
        (nonzero_of_normSq_eq_one unit) unit degree degreeTwo :=
  (Unit.Frame.Overlap.Preparation.fromFrame (nonzero_of_normSq_eq_one unit) unit degree degreeTwo prepared).property

/-- Saved target-frame reuse preserves all three actual overlap occurrences. -/
example {source target : Canonical} (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (small : UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (prepared : Frame.Preparation.Prepared (nonzero_of_normSq_eq_one targetUnit) degree degreeTwo) :
    (Unit.Move.Path.Preparation.fromFrame sourceUnit targetUnit degree degreeTwo small prepared).val.stepCount = 3 :=
  Unit.Move.Path.Preparation.fromFrame_stepCount sourceUnit targetUnit degree degreeTwo small prepared

end

end TestPurelib.Riemann.RootContinuation.PowerInterior
