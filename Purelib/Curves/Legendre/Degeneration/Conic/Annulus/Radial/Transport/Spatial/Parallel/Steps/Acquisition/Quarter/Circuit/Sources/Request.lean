module

import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank.Root

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Occurrence
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Entries
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Data.Fin
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # A fresh global stage on the same actual four-quarter source geometry

The actual nonempty closed source assembly precedes stage selection. The
single original StageAttempt.Requested producer accepts the SAME retained
old-or-fine source families and prepares their literal covered parents once. The local source families remain distinct
old inputs. Their own first-query comparisons connect the exact selected
first-match occurrence to the original local source without observation replay.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source (Vertex)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes

section ActualInputs

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable {execution : Execution.Cache initial secondInput thirdInput fourthInput}

variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Execution.Cache.Sources

variable (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

/-- One exact original head view, unchanged based closed chain and complete sufficient-stage source request.

All original local source families stay indices. The fresh original request
owns its actual new Targets, source preparations, bank, selected observations
and finite checking outcomes. No equality with the old local preparations
is asserted, even when their literal prepared edges coincide.
-/
@[expose] def Requested (current freshFloor rootStage : Nat) (accuracy : AccuracyRequest) :=
  (assembled : { value : Spine.Sources.Assembled (frame := frame) (basis := basis) (count := modelCount)
      (floor := floor) (sheet := sheet) (targets := sourceTargets)
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter) //
    value = assemble sources }) ×
  (shape : { value : CenteredEdge (Fibre.frameCurve frame) basis ×
      List (CenteredEdge (Fibre.frameCurve frame) basis) //
    assembled.val.geometry.parents = value.1 :: value.2 }) ×
  (chain : { value : CenteredPathChain (shape.val.1 :: shape.val.2)
      (start := PreparedParent.startPoint shape.val.1) (finish := PreparedParent.startPoint shape.val.1) //
    value = (assembled.val.geometry.chain.castParents shape.property).basedAtFirst }) ×
  { requested : PreparedParents.StageAttempt.Requested (frame := frame)
      (assembled.val.covered.castParents shape.property) chain.val current freshFloor rootStage accuracy //
    requested = PreparedParents.StageAttempt.Requested.build (frame := frame)
      (assembled.val.covered.castParents shape.property) chain.val current freshFloor rootStage accuracy }

namespace Requested

variable {sources}

/-- Acquire one genuinely new sufficiently accurate global source request on the SAME retained paid geometry.

The original four source families and literal closed assembly are retained.
The derived nonempty theorem justifies the head view; the existing original
stage selector then precedes every newly acquired source and bank observation.
Earlier local requests, observations and preparations are not retagged.
-/
def build (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)
    (current freshFloor rootStage : Nat) (accuracy : AccuracyRequest) :
    Requested sources current freshFloor rootStage accuracy := by
  let assembled := assemble sources
  let shape : { value : CenteredEdge (Fibre.frameCurve frame) basis ×
      List (CenteredEdge (Fibre.frameCurve frame) basis) //
      assembled.geometry.parents = value.1 :: value.2 } :=
    match items : assembled.geometry.parents with
    | [] => False.elim (assemble_parents_ne_nil sources items)
    | parent :: parents => ⟨⟨parent, parents⟩, rfl⟩
  let chain := (assembled.geometry.chain.castParents shape.property).basedAtFirst
  let requested := PreparedParents.StageAttempt.Requested.build (frame := frame)
    (assembled.covered.castParents shape.property) chain current freshFloor rootStage accuracy
  exact ⟨⟨assembled, rfl⟩, shape, ⟨chain, rfl⟩, ⟨requested, rfl⟩⟩

variable {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
variable (retained : Requested sources current freshFloor rootStage accuracy)

/-- Read the complete actual assembled source cache computed once before stage selection. -/
@[expose] def assembled := retained.1.val

/-- The whole retained global assembly is the original four-quarter factory on the SAME local source families. -/
theorem assembled_eq : retained.assembled = assemble sources := retained.1.property

/-- The stored global assembly retains the identical original ordered quarter parent list. -/
theorem parents_eq : retained.assembled.geometry.parents = (assemble sources).geometry.parents :=
  congrArg (fun value => value.geometry.parents) retained.assembled_eq

/-- Read the cached exact first-parent view of the SAME actual assembled source geometry. -/
@[expose] def shape := retained.2.1

/-- Read the SAME original covering patches under only the retained head-view index equality. -/
@[expose] def covered := retained.assembled.covered.castParents retained.shape.property

/-- Read the complete original closed chain transported only to its actual first retained parent. -/
@[expose] def chain := retained.2.2.1.val

/-- The cached based chain is the exact original endpoint/parent transport of the SAME closed source geometry. -/
theorem chain_eq : retained.chain =
    (retained.assembled.geometry.chain.castParents retained.shape.property).basedAtFirst := retained.2.2.1.property

/-- Read the whole sufficient-stage request and all its actual source, bank and finite-check caches. -/
@[expose] def requested : PreparedParents.StageAttempt.Requested (frame := frame) retained.covered retained.chain
    current freshFloor rootStage accuracy := retained.2.2.2.val

/-- The completed new request has the original total stage/acquisition factory on those SAME patches and chain. -/
theorem requested_eq : retained.requested =
    PreparedParents.StageAttempt.Requested.build (frame := frame) retained.covered retained.chain
      current freshFloor rootStage accuracy := retained.2.2.2.property

/-- Read the SAME actual global StageAttempt at its internally selected sufficient stage. -/
@[expose] def attempt := retained.requested.attempt

/-- Read the fresh request's actual original global Targets, without changing the local source-family indices. -/
@[expose] def targets := retained.requested.targets

/-- Read the complete freshly acquired source preparations on the SAME actual global parent occurrences. -/
@[expose] def prepared := retained.requested.prepared

/-- Read the actual first-match source bank retained by that SAME sufficient-stage attempt. -/
@[expose] def bank := retained.attempt.2.2.1.val

/-- Every actual newly acquired six-channel source cell pays the chosen accuracy on its own original allowance. -/
theorem cell_allowance_lt (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) (channel : Fin 6) :
    ((retained.prepared.entry index).preparation.cell.models.cell channel).localAllowance < accuracy.tolerance :=
  retained.requested.cell_allowance_lt index channel

/-- The freshly acquired endpoint request pays the SAME chosen accuracy before bank observations are used. -/
theorem endpoint_lt : retained.targets.endpoint < accuracy.tolerance := retained.requested.endpoint_lt

/-- Transport an actual fresh global source index to the SAME stored assembled parent position. -/
@[expose] def assembledIndex (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    Fin retained.assembled.geometry.parents.length :=
  ⟨index.val, Eq.mpr (congrArg (fun parents => index.val < parents.length) retained.shape.property) index.isLt⟩

/-- Change only the bound to the identical original global assembly factory's parent index. -/
@[expose] def originalIndex (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    Fin (assemble sources).geometry.parents.length :=
  ⟨index.val, Eq.mp (congrArg (fun parents => index.val < parents.length) retained.parents_eq)
    (retained.assembledIndex index).isLt⟩

/-- The complete fresh/local parent incidence follows only from the SAME retained original assembly head view. -/
theorem parent_eq (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    retained.assembled.geometry.parents[(retained.assembledIndex index).val]'
        (retained.assembledIndex index).isLt =
      (retained.shape.val.1 :: retained.shape.val.2)[index.val]'index.isLt :=
  getElem_congr retained.shape.property rfl (retained.assembledIndex index).isLt

/-- Compare actual independent old and fresh source samples at their identical literal signed prepared edge.

The original observations, requests and preparation caches remain distinct.
Each actual patch supplies its own first-query comparison. No equality of
sample values, preparation caches, allocations or visible radii is used.
-/
def firstEquivalent (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    NamedEquivalent
      (retained.assembled.prepared.entry (retained.assembledIndex index)).firstSample.certificate.value.name
      (retained.prepared.entry index).firstSample.certificate.value.name :=
  PreparedParent.firstEquivalentOfEdgeEq
    (retained.assembled.prepared.entry (retained.assembledIndex index)) (retained.prepared.entry index)
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge) (retained.parent_eq index))

variable {point : LiftedPoint 2} {found : Vertex.Bank.Found retained.bank point}
variable (position : Vertex.Bank.Position (.found found))

/-- Read the literal original source occurrence selected by the actual retained first-match lookup position. -/
@[expose] def foundSourceIndex : Fin (retained.shape.val.1 :: retained.shape.val.2).length :=
  retained.attempt.foundSourceIndex position

/-- Read that SAME first selected occurrence in the unchanged original four-quarter assembled geometry. -/
@[expose] def foundAssembledIndex : Fin (assemble sources).geometry.parents.length :=
  retained.originalIndex (retained.foundSourceIndex position)

/-- The selected occurrence keeps the actual first-match natural position, including repeated earlier values. -/
theorem foundAssembledIndex_val : (retained.foundAssembledIndex position).val = position.index.val :=
  retained.attempt.foundSourceIndex_val position

/-- Locate the literal first selected global source in the SAME original ordered quarter words exactly once. -/
def locateFound : Flatten.Occurrence (parentWords sources)
    (flattenedIndex sources (retained.foundAssembledIndex position)) :=
  locate sources (retained.foundAssembledIndex position)

/-- The retained selected source location uses the exact original finite flatten procedure on its actual index. -/
theorem locateFound_eq : retained.locateFound position =
    Flatten.locate (parentWords sources) (flattenedIndex sources (retained.foundAssembledIndex position)) :=
  locate_eq sources (retained.foundAssembledIndex position)

/-- Compare the SAME original locally assembled source sample to the actual first selected Found sample.

The stored first-match position chooses the real source occurrence. Whole
bank/entry readback identifies that particular fresh sample, and the two
patches supply their actual same-edge comparisons. No source is selected by
coordinate equality, sheet key, whole-loop closure or matrix action.
-/
def foundEquivalent :
    NamedEquivalent
      (retained.assembled.prepared.entry
        (retained.assembledIndex (retained.foundSourceIndex position))).firstSample.certificate.value.name
      found.original.sample.certificate.value.name :=
  NamedEquivalent.transport rfl (retained.attempt.found_source_name position).symm
    (retained.firstEquivalent (retained.foundSourceIndex position))

/-- Compare the exact selected original quarter source to THAT actual first global Found, retaining both old inputs.

The supplied retained location is the original finite geometric occurrence,
not an assumed root relation. The local/global and global/fresh patch
comparisons are derived separately and composed without observer replay.
This does not yet compare a different repeated visiting occurrence.
-/
def selectedEquivalent
    (located : Flatten.Occurrence (parentWords sources)
      (flattenedIndex sources (retained.foundAssembledIndex position))) :
    NamedEquivalent
      ((selected sources (retained.foundAssembledIndex position) located).2.prepared.entry
        (child sources (retained.foundAssembledIndex position) located)).firstSample.certificate.value.name
      found.original.sample.certificate.value.name := by
  let sourceIndex := retained.foundSourceIndex position
  let original := selected sources (retained.foundAssembledIndex position) located
  let localIndex := child sources (retained.foundAssembledIndex position) located
  have originalParent := getElem_congr (i := sourceIndex.val) (j := sourceIndex.val)
    retained.parents_eq rfl (retained.assembledIndex sourceIndex).isLt
  have localParent := Execution.Cache.Sources.parent_eq sources (retained.foundAssembledIndex position) located
  let compared := PreparedParent.firstEquivalentOfEdgeEq (original.2.prepared.entry localIndex)
    (retained.assembled.prepared.entry (retained.assembledIndex sourceIndex))
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge)
      (originalParent.trans localParent).symm)
  exact compared.trans (retained.foundEquivalent position)

/-- Compare the SAME original selected Block source sample to THAT literal first global Found sample.

Both supplied locations are retained outputs of the original finite flatten
worker. The two actual original parent-incidence laws and independent patch
comparisons derive the full-y operational relation. Every old Point, request,
observation, radius and original Block source family remains unchanged.
-/
def blockEquivalent
    (located : Flatten.Occurrence (parentWords sources)
      (flattenedIndex sources (retained.foundAssembledIndex position)))
    (inBlock : Flatten.Occurrence (blockWords sources (quarter sources (retained.foundAssembledIndex position) located))
      (blockFlattenedIndex sources (quarter sources (retained.foundAssembledIndex position) located)
        (child sources (retained.foundAssembledIndex position) located))) :
    NamedEquivalent
      ((blockSources sources (quarter sources (retained.foundAssembledIndex position) located)
        (child sources (retained.foundAssembledIndex position) located) inBlock).2.entry
          inBlock.2.val).firstSample.certificate.value.name
      found.original.sample.certificate.value.name :=
  let inQuarter := selected sources (retained.foundAssembledIndex position) located
  let localIndex := child sources (retained.foundAssembledIndex position) located
  let original := blockSources sources (quarter sources (retained.foundAssembledIndex position) located)
    localIndex inBlock
  let compared := PreparedParent.firstEquivalentOfEdgeEq (original.2.entry inBlock.2.val)
    (inQuarter.2.prepared.entry localIndex)
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge)
      (blockParent_eq sources (quarter sources (retained.foundAssembledIndex position) located)
        localIndex inBlock).symm)
  compared.trans (retained.selectedEquivalent position located)

section SignedRoots

open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology

/-- Read the signed chain of the SAME fresh Request's actual global parent occurrences.

The internally constructed four-quarter signed source chain is transported
by the retained whole assembly equation and head-view equation only. The
fresh preparations, bank, checking outcomes and literal selected Positions
stay unchanged. No RootChain, Ready or endpoint comparison is an input.
-/
def rootChain : RootChain (retained.shape.val.1 :: retained.shape.val.2)
    (ownerRootName sourceOwner.parameterNonzero sourceOwner)
    (ownerRootName sourceOwner.parameterNonzero sourceOwner) :=
  PreparedBankRootChains.RootChain.castChildren retained.shape.property
    (PreparedBankRootChains.RootChain.castChildren retained.parents_eq.symm
      (Execution.Cache.Sources.rootChain sources))

end SignedRoots

end Requested

end Execution.Cache.Sources

end ActualInputs

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter}
variable {firstReading : ReadingAt circuit.first.actual UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginal : Steps.Quarter circuit.first.actual circuit.first.regular
  UniformPrimitiveMesh.firstEndpoint firstReading firstOriginalOwner}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {agreement : InitialAgreement UniformPrimitiveMesh.firstEndpoint firstReading sourceOwner}
variable {initial : Quarter firstOriginal sourceOwner agreement}
variable {secondReading : ReadingAt circuit.second.actual UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
  UniformPrimitiveMesh.firstEndpoint secondReading secondOriginalOwner}
variable {thirdReading : ReadingAt circuit.third.actual UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginalOwner : OwnerAt site parameter .third (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginal : Steps.Quarter circuit.third.actual circuit.third.regular
  UniformPrimitiveMesh.firstEndpoint thirdReading thirdOriginalOwner}
variable {fourthReading : ReadingAt circuit.fourth.actual UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginalOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginal : Steps.Quarter circuit.fourth.actual circuit.fourth.regular
  UniformPrimitiveMesh.firstEndpoint fourthReading fourthOriginalOwner}
variable {execution : Execution initial secondOriginal thirdOriginal fourthOriginal}

variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Execution.Sources

variable (sources : Execution.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

/-- One exact original head view, unchanged based closed chain and complete sufficient-stage source request.

All original local source families stay indices. The fresh original request
owns its actual new Targets, source preparations, bank, selected observations
and finite checking outcomes. No equality with the old local preparations
is asserted, even when their literal prepared edges coincide.
-/
@[expose] def Requested (current freshFloor rootStage : Nat) (accuracy : AccuracyRequest) :=
  (assembled : { value : Spine.Sources.Assembled (frame := frame) (basis := basis) (count := modelCount)
      (floor := floor) (sheet := sheet) (targets := sourceTargets)
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter)
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter) //
    value = assemble sources }) ×
  (shape : { value : CenteredEdge (Fibre.frameCurve frame) basis ×
      List (CenteredEdge (Fibre.frameCurve frame) basis) //
    assembled.val.geometry.parents = value.1 :: value.2 }) ×
  (chain : { value : CenteredPathChain (shape.val.1 :: shape.val.2)
      (start := PreparedParent.startPoint shape.val.1) (finish := PreparedParent.startPoint shape.val.1) //
    value = (assembled.val.geometry.chain.castParents shape.property).basedAtFirst }) ×
  { requested : PreparedParents.StageAttempt.Requested (frame := frame)
      (assembled.val.covered.castParents shape.property) chain.val current freshFloor rootStage accuracy //
    requested = PreparedParents.StageAttempt.Requested.build (frame := frame)
      (assembled.val.covered.castParents shape.property) chain.val current freshFloor rootStage accuracy }

namespace Requested

variable {sources}

/-- Acquire one genuinely new sufficiently accurate global source request on the SAME retained paid geometry.

The original four source families and literal closed assembly are retained.
The derived nonempty theorem justifies the head view; the existing original
stage selector then precedes every newly acquired source and bank observation.
Earlier local requests, observations and preparations are not retagged.
-/
def build (sources : Execution.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)
    (current freshFloor rootStage : Nat) (accuracy : AccuracyRequest) :
    Requested sources current freshFloor rootStage accuracy := by
  let shared := Cache.Sources.Requested.build sources current freshFloor rootStage accuracy
  let assembled := shared.assembled
  have same : assembled = assemble sources :=
    shared.assembled_eq.trans (assemble_eq_shared sources).symm
  exact ⟨⟨assembled, same⟩, shared.shape, ⟨shared.chain, shared.chain_eq⟩,
    ⟨shared.requested, shared.requested_eq⟩⟩

variable {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
variable (retained : Requested sources current freshFloor rootStage accuracy)

/-- Read the complete actual assembled source cache computed once before stage selection. -/
@[expose] def assembled := retained.1.val

/-- The whole retained global assembly is the original four-quarter factory on the SAME local source families. -/
theorem assembled_eq : retained.assembled = assemble sources := retained.1.property

/-- The stored global assembly retains the identical original ordered quarter parent list. -/
theorem parents_eq : retained.assembled.geometry.parents = (assemble sources).geometry.parents :=
  congrArg (fun value => value.geometry.parents) retained.assembled_eq

/-- Read the cached exact first-parent view of the SAME actual assembled source geometry. -/
@[expose] def shape := retained.2.1

/-- Read the SAME original covering patches under only the retained head-view index equality. -/
@[expose] def covered := retained.assembled.covered.castParents retained.shape.property

/-- Read the complete original closed chain transported only to its actual first retained parent. -/
@[expose] def chain := retained.2.2.1.val

/-- The cached based chain is the exact original endpoint/parent transport of the SAME closed source geometry. -/
theorem chain_eq : retained.chain =
    (retained.assembled.geometry.chain.castParents retained.shape.property).basedAtFirst := retained.2.2.1.property

/-- Read the whole sufficient-stage request and all its actual source, bank and finite-check caches. -/
@[expose] def requested : PreparedParents.StageAttempt.Requested (frame := frame) retained.covered retained.chain
    current freshFloor rootStage accuracy := retained.2.2.2.val

/-- The completed new request has the original total stage/acquisition factory on those SAME patches and chain. -/
theorem requested_eq : retained.requested =
    PreparedParents.StageAttempt.Requested.build (frame := frame) retained.covered retained.chain
      current freshFloor rootStage accuracy := retained.2.2.2.property

/-- Read the SAME actual global StageAttempt at its internally selected sufficient stage. -/
@[expose] def attempt := retained.requested.attempt

/-- Read the fresh request's actual original global Targets, without changing the local source-family indices. -/
@[expose] def targets := retained.requested.targets

/-- Read the complete freshly acquired source preparations on the SAME actual global parent occurrences. -/
@[expose] def prepared := retained.requested.prepared

/-- Read the actual first-match source bank retained by that SAME sufficient-stage attempt. -/
@[expose] def bank := retained.attempt.2.2.1.val

/-- Every actual newly acquired six-channel source cell pays the chosen accuracy on its own original allowance. -/
theorem cell_allowance_lt (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) (channel : Fin 6) :
    ((retained.prepared.entry index).preparation.cell.models.cell channel).localAllowance < accuracy.tolerance :=
  retained.requested.cell_allowance_lt index channel

/-- The freshly acquired endpoint request pays the SAME chosen accuracy before bank observations are used. -/
theorem endpoint_lt : retained.targets.endpoint < accuracy.tolerance := retained.requested.endpoint_lt

/-- Transport an actual fresh global source index to the SAME stored assembled parent position. -/
@[expose] def assembledIndex (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    Fin retained.assembled.geometry.parents.length :=
  ⟨index.val, Eq.mpr (congrArg (fun parents => index.val < parents.length) retained.shape.property) index.isLt⟩

/-- Change only the bound to the identical original global assembly factory's parent index. -/
@[expose] def originalIndex (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    Fin (assemble sources).geometry.parents.length :=
  ⟨index.val, Eq.mp (congrArg (fun parents => index.val < parents.length) retained.parents_eq)
    (retained.assembledIndex index).isLt⟩

/-- The complete fresh/local parent incidence follows only from the SAME retained original assembly head view. -/
theorem parent_eq (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    retained.assembled.geometry.parents[(retained.assembledIndex index).val]'
        (retained.assembledIndex index).isLt =
      (retained.shape.val.1 :: retained.shape.val.2)[index.val]'index.isLt :=
  getElem_congr retained.shape.property rfl (retained.assembledIndex index).isLt

/-- Compare actual independent old and fresh source samples at their identical literal signed prepared edge.

The original observations, requests and preparation caches remain distinct.
Each actual patch supplies its own first-query comparison. No equality of
sample values, preparation caches, allocations or visible radii is used.
-/
def firstEquivalent (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    NamedEquivalent
      (retained.assembled.prepared.entry (retained.assembledIndex index)).firstSample.certificate.value.name
      (retained.prepared.entry index).firstSample.certificate.value.name :=
  PreparedParent.firstEquivalentOfEdgeEq
    (retained.assembled.prepared.entry (retained.assembledIndex index)) (retained.prepared.entry index)
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge) (retained.parent_eq index))

variable {point : LiftedPoint 2} {found : Vertex.Bank.Found retained.bank point}
variable (position : Vertex.Bank.Position (.found found))

/-- Read the literal original source occurrence selected by the actual retained first-match lookup position. -/
@[expose] def foundSourceIndex : Fin (retained.shape.val.1 :: retained.shape.val.2).length :=
  retained.attempt.foundSourceIndex position

/-- Read that SAME first selected occurrence in the unchanged original four-quarter assembled geometry. -/
@[expose] def foundAssembledIndex : Fin (assemble sources).geometry.parents.length :=
  retained.originalIndex (retained.foundSourceIndex position)

/-- The selected occurrence keeps the actual first-match natural position, including repeated earlier values. -/
theorem foundAssembledIndex_val : (retained.foundAssembledIndex position).val = position.index.val :=
  retained.attempt.foundSourceIndex_val position

/-- Locate the literal first selected global source in the SAME original ordered quarter words exactly once. -/
def locateFound : Flatten.Occurrence (parentWords sources)
    (flattenedIndex sources (retained.foundAssembledIndex position)) :=
  locate sources (retained.foundAssembledIndex position)

/-- The retained selected source location uses the exact original finite flatten procedure on its actual index. -/
theorem locateFound_eq : retained.locateFound position =
    Flatten.locate (parentWords sources) (flattenedIndex sources (retained.foundAssembledIndex position)) :=
  locate_eq sources (retained.foundAssembledIndex position)

/-- Compare the SAME original locally assembled source sample to the actual first selected Found sample.

The stored first-match position chooses the real source occurrence. Whole
bank/entry readback identifies that particular fresh sample, and the two
patches supply their actual same-edge comparisons. No source is selected by
coordinate equality, sheet key, whole-loop closure or matrix action.
-/
def foundEquivalent :
    NamedEquivalent
      (retained.assembled.prepared.entry
        (retained.assembledIndex (retained.foundSourceIndex position))).firstSample.certificate.value.name
      found.original.sample.certificate.value.name :=
  NamedEquivalent.transport rfl (retained.attempt.found_source_name position).symm
    (retained.firstEquivalent (retained.foundSourceIndex position))

/-- Compare the exact selected original quarter source to THAT actual first global Found, retaining both old inputs.

The supplied retained location is the original finite geometric occurrence,
not an assumed root relation. The local/global and global/fresh patch
comparisons are derived separately and composed without observer replay.
This does not yet compare a different repeated visiting occurrence.
-/
def selectedEquivalent
    (located : Flatten.Occurrence (parentWords sources)
      (flattenedIndex sources (retained.foundAssembledIndex position))) :
    NamedEquivalent
      ((selected sources (retained.foundAssembledIndex position) located).2.prepared.entry
        (child sources (retained.foundAssembledIndex position) located)).firstSample.certificate.value.name
      found.original.sample.certificate.value.name := by
  let sourceIndex := retained.foundSourceIndex position
  let original := selected sources (retained.foundAssembledIndex position) located
  let localIndex := child sources (retained.foundAssembledIndex position) located
  have originalParent := getElem_congr (i := sourceIndex.val) (j := sourceIndex.val)
    retained.parents_eq rfl (retained.assembledIndex sourceIndex).isLt
  have localParent := Execution.Sources.parent_eq sources (retained.foundAssembledIndex position) located
  let compared := PreparedParent.firstEquivalentOfEdgeEq (original.2.prepared.entry localIndex)
    (retained.assembled.prepared.entry (retained.assembledIndex sourceIndex))
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge)
      (originalParent.trans localParent).symm)
  exact compared.trans (retained.foundEquivalent position)

/-- Compare the SAME original selected Block source sample to THAT literal first global Found sample.

Both supplied locations are retained outputs of the original finite flatten
worker. The two actual original parent-incidence laws and independent patch
comparisons derive the full-y operational relation. Every old Point, request,
observation, radius and original Block source family remains unchanged.
-/
def blockEquivalent
    (located : Flatten.Occurrence (parentWords sources)
      (flattenedIndex sources (retained.foundAssembledIndex position)))
    (inBlock : Flatten.Occurrence (blockWords sources (quarter sources (retained.foundAssembledIndex position) located))
      (blockFlattenedIndex sources (quarter sources (retained.foundAssembledIndex position) located)
        (child sources (retained.foundAssembledIndex position) located))) :
    NamedEquivalent
      ((blockSources sources (quarter sources (retained.foundAssembledIndex position) located)
        (child sources (retained.foundAssembledIndex position) located) inBlock).2.entry
          inBlock.2.val).firstSample.certificate.value.name
      found.original.sample.certificate.value.name :=
  let inQuarter := selected sources (retained.foundAssembledIndex position) located
  let localIndex := child sources (retained.foundAssembledIndex position) located
  let original := blockSources sources (quarter sources (retained.foundAssembledIndex position) located)
    localIndex inBlock
  let compared := PreparedParent.firstEquivalentOfEdgeEq (original.2.entry inBlock.2.val)
    (inQuarter.2.prepared.entry localIndex)
    (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => parent.edge)
      (blockParent_eq sources (quarter sources (retained.foundAssembledIndex position) located)
        localIndex inBlock).symm)
  compared.trans (retained.selectedEquivalent position located)

section SharedFactory

variable (sources : Execution.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)
variable (current freshFloor rootStage : Nat) (accuracy : AccuracyRequest)

/-- The old-input builder retains the identical whole actual assembly from the single shared producer. -/
theorem build_assembled_eq_shared :
    (build sources current freshFloor rootStage accuracy).assembled =
      (Cache.Sources.Requested.build sources current freshFloor rootStage accuracy).assembled := by
  unfold build
  rfl

/-- The old-input builder retains the identical complete first-parent cache from the single shared producer. -/
theorem build_shape_heq_shared :
    HEq (build sources current freshFloor rootStage accuracy).shape
      (Cache.Sources.Requested.build sources current freshFloor rootStage accuracy).shape := by
  unfold build
  rfl

/-- The old-input builder retains the identical based-chain cache from the single shared producer. -/
theorem build_chain_heq_shared :
    HEq (build sources current freshFloor rootStage accuracy).chain
      (Cache.Sources.Requested.build sources current freshFloor rootStage accuracy).chain := by
  unfold build
  rfl

/-- The old-input builder retains the identical complete Stage acquisition and observations from the shared producer. -/
theorem build_requested_heq_shared :
    HEq (build sources current freshFloor rootStage accuracy).requested
      (Cache.Sources.Requested.build sources current freshFloor rootStage accuracy).requested := by
  unfold build
  rfl

end SharedFactory

end Requested

end Execution.Sources

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
