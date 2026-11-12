module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Sources.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.RootChain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Refinement.Spine.Geometry.Nonempty
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences.Point
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Original occurrence completion of the SAME nonempty global child source bank

The given actual child chain precedes its Targets and numeric source bank.
Original walk nonemptiness and strict prepared requests prove that this
same child list is nonempty. One flattened preparation product and one
genuine closed root chain are retained before the original stage attempt
and its complete occurrence outcome execute. Every source cell, Point,
query, signed root comparison and old check outcome keeps its owner.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner ownerName)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Purelib.Geometry.Rational.Box}
variable {grid : ClearGrid (Paths.polynomial parameter) ambient} {base : Canonical}
variable (owner : Owner ((Paths.polynomial parameter).eval base)) (closed : RootClosedWalk grid base owner)
variable {inputCenters : Centers (frame := frame) (basis := basis) (sheet := sheet) closed.traced.lineage}
variable {materialized : OwnerPath (Paths.polynomial parameter) base owner base
  (PreparedPathGluing.finishOwner closed.traced.prepared)}
variable {factory : materialized = closed.traced.lineage.ownerPath} {diameter : Rational} {positive : 0 < diameter}
variable (retained : Materialized.Geometry (count := count)
  diameter positive closed.traced.lineage inputCenters materialized factory)
variable (childChain : CenteredPathChain retained.parents (start := (⟨base, sheet⟩ : LiftedPoint 2))
  (finish := (⟨base, sheet⟩ : LiftedPoint 2)))

namespace Geometry.Sources

/-- The original occurrence outcome together with the SAME once-bound flattened preparations and closed roots.

This exact product retains the two actual cache factories and the complete
original StageAttempt/OccurrenceCompletion run. It is indexed by the
GIVEN full child chain, its actual Targets and the supplied whole numeric
bank, rather than a separately rebuilt source or geometric path.
-/
@[expose] def Occurrences (precision rootStage : Nat) (targets : CellEndpoints.Targets childChain.path precision)
    (computed : targets = CellEndpoints.Targets.build childChain.path precision)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (walkPositive : 0 < closed.walk.edgeCount) : Type 2 :=
  (prepared : {value : PreparedParents retained.covered floor targets //
    value = preparations retained sourceBank}) ×
  (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
    value = Geometry.closedRoots owner closed retained}) ×
  StageAttempt.OccurrenceCompletion.AtPoint retained.covered childChain precision floor rootStage
    targets computed prepared.val rooted.val (Geometry.parents_nonempty_of_walk owner closed retained walkPositive)

/-- Complete the original occurrence run using the supplied whole preparation and signed-root caches.

Both caches retain their original factories. The endpoint-bank attempt and
occurrence comparisons consume those exact values; an outer programme
construction can share the fixed geometric root chain across its requests.
-/
def completeOccurrencesFromCaches (precision rootStage : Nat)
    (targets : CellEndpoints.Targets childChain.path precision)
    (computed : targets = CellEndpoints.Targets.build childChain.path precision)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (walkPositive : 0 < closed.walk.edgeCount)
    (prepared : {value : PreparedParents retained.covered floor targets //
      value = preparations retained sourceBank})
    (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
      value = Geometry.closedRoots owner closed retained}) :
    Occurrences owner closed retained childChain precision rootStage targets computed sourceBank walkPositive :=
  let completed := StageAttempt.OccurrenceCompletion.ofPrepared retained.covered childChain
    precision floor rootStage targets computed prepared.val rooted.val
    (Geometry.parents_nonempty_of_walk owner closed retained walkPositive)
  ⟨prepared, rooted, completed⟩

/-- The occurrence run retains the exact supplied whole signed-root cache. -/
theorem completeOccurrencesFromCaches_rooted (precision rootStage : Nat)
    (targets : CellEndpoints.Targets childChain.path precision)
    (computed : targets = CellEndpoints.Targets.build childChain.path precision)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (walkPositive : 0 < closed.walk.edgeCount)
    (prepared : {value : PreparedParents retained.covered floor targets //
      value = preparations retained sourceBank})
    (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
      value = Geometry.closedRoots owner closed retained}) :
    (completeOccurrencesFromCaches owner closed retained childChain precision rootStage targets computed
      sourceBank walkPositive prepared rooted).2.1 = rooted := by
  unfold completeOccurrencesFromCaches
  rfl

/-- The occurrence run retains the exact supplied whole source-preparation cache. -/
theorem completeOccurrencesFromCaches_prepared (precision rootStage : Nat)
    (targets : CellEndpoints.Targets childChain.path precision)
    (computed : targets = CellEndpoints.Targets.build childChain.path precision)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (walkPositive : 0 < closed.walk.edgeCount)
    (prepared : {value : PreparedParents retained.covered floor targets //
      value = preparations retained sourceBank})
    (rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
      value = Geometry.closedRoots owner closed retained}) :
    (completeOccurrencesFromCaches owner closed retained childChain precision rootStage targets computed
      sourceBank walkPositive prepared rooted).1 = prepared := by
  unfold completeOccurrencesFromCaches
  rfl

/-- Complete occurrences once on the SAME given source bank, child chain and genuine original root return.

The literal flattened preparations and closedRoots are bound before the
old first-based endpoint bank/checks and occurrence comparisons execute.
Nonemptiness is derived from the original walk and actual strict child
count. The entire dependent construction passes through the full lifted
start equality, preserving both repeated and physically stationary slots.
-/
def completeOccurrences (precision rootStage : Nat) (targets : CellEndpoints.Targets childChain.path precision)
    (computed : targets = CellEndpoints.Targets.build childChain.path precision)
    (sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained)
    (walkPositive : 0 < closed.walk.edgeCount) :
    Occurrences owner closed retained childChain precision rootStage targets computed sourceBank walkPositive :=
  let prepared : {value : PreparedParents retained.covered floor targets //
    value = preparations retained sourceBank} := ⟨preparations retained sourceBank, rfl⟩
  let rooted : {value : RootChain retained.parents (ownerName owner) (ownerName owner) //
    value = Geometry.closedRoots owner closed retained} := ⟨Geometry.closedRoots owner closed retained, rfl⟩
  completeOccurrencesFromCaches owner closed retained childChain precision rootStage targets computed
    sourceBank walkPositive prepared rooted

namespace Occurrences

variable {owner closed retained childChain}
variable {precision rootStage : Nat} {targets : CellEndpoints.Targets childChain.path precision}
variable {computed : targets = CellEndpoints.Targets.build childChain.path precision}
variable {sourceBank : Sources (count := count) (floor := floor) (targets := targets) retained}
variable {walkPositive : 0 < closed.walk.edgeCount}
variable (completed : Occurrences owner closed retained childChain
  precision rootStage targets computed sourceBank walkPositive)

/-- Read the original occurrence-completed Stage at this SAME given lifted path and actual precision. -/
def stage : Stage parameter ⟨⟨base, sheet⟩, childChain.path⟩ precision := completed.2.2.stage

/-- The actual completed Stage retains exactly the source path on the SAME whole child bank and given chain. -/
theorem stage_sources : completed.stage.sources = sources retained sourceBank childChain := by
  unfold stage
  exact completed.2.2.stage_sources.trans
    (congrArg (fun values : PreparedParents retained.covered floor targets =>
      PreparedParents.sources retained.covered values childChain) completed.1.property)

/-- Every channel of the completed Stage has precisely the SAME ordered cells of the original whole bank. -/
theorem stage_cells (channel : Fin 6) :
    completed.stage.sources.cells channel = cells retained sourceBank channel :=
  (congrArg (fun actual : Path parameter childChain.path => actual.cells channel) completed.stage_sources).trans
    (cells_sources retained sourceBank childChain channel).symm

/-- The completed Stage reads the SAME supplied polynomial model, with no desired model equality as an input. -/
theorem model_eq_stage (channel : Fin 6) :
    model retained sourceBank channel = PathModel.mk (completed.stage.sources.cells channel) :=
  congrArg PathModel.mk (completed.stage_cells channel).symm

end Occurrences

end Geometry.Sources

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Refinement.Materialized

end
