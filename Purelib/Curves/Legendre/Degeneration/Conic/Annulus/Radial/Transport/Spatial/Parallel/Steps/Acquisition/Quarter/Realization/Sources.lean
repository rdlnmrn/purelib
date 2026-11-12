module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Sources
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation.Source.Assembly
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains

/-! # Shared original source families for both actual retained quarter realizations

The original Steps branch retains its literal old Quarter.Sources family.
The genuine finer Layer branch retains source families of its SAME actual
paid Layer acquisitions. Only these existing parents determine the branch;
there is no dummy Steps execution, callback or equality to an old depth-seven
quarter. All later rows can consume one identical source family.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Input.Realization

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
  renaming Acquisition → LayerAcquisition

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {leg : Transport.Leg site parameter unitQuarter}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The original complete source family of the SAME actual quarter producer, independently of any selected row.

Each branch is its existing mathematical parent's family. The old branch
keeps the old Quarter literally; the new branch keeps the actual fine
paid fold and its exact nominal initial/terminal Owner indices.
-/
@[expose] def Sources : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    Realization input sourceOwner agreement → Type 1
  | .inl _original, _sourceOwner, _agreement, retained =>
      Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (sourceTargets := sourceTargets) retained
  | .inr fine, _sourceOwner, _agreement, retained =>
      LayerAcquisition.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (sourceTargets := sourceTargets) fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner _sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement _sourceOwner fine.numerical.layer_eq fine.numerical.queried _agreement)
        retained.paid

namespace Sources

/-- Prepare the actual producer's original source family once, shared by all six cell channels and primitive rows. -/
def build : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
      Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (sourceTargets := sourceTargets) retained
  | .inl _original, _sourceOwner, _agreement, retained => Quarter.Sources.build retained
  | .inr fine, _sourceOwner, _agreement, retained =>
      LayerAcquisition.Sources.build fine.numerical.finish fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner _sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement _sourceOwner fine.numerical.layer_eq fine.numerical.queried _agreement)
        retained.paid

/-- Assemble the SAME retained source preparations with only their original exact endpoint-index transports.

The numerical first-piece source equals its initial Piece's source by the
original decomposition factory law. The whole Assembled cache is transported
along that scalar equality; its Parents, observations, models and request
objects are not reconstructed from equal readings.
-/
def assemble : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained →
    Spine.Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := sourceTargets)
      (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint.parameter)
      (coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) retained.finishEndpoint.parameter)
  | .inl _original, _sourceOwner, _agreement, retained, sources =>
      Quarter.Sources.assemble retained sources
  | .inr fine, _sourceOwner, _agreement, retained, sources =>
      let assembled := LayerAcquisition.Sources.assemble fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner _sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement _sourceOwner fine.numerical.layer_eq fine.numerical.queried _agreement)
        retained.paid sources
      assembled.castEndpoints
        (congrArg (fun time => coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)
          (fine.numerical.parts.start_time fine.numerical.layer_eq)) rfl

/-- Read the SAME original per-Block parent words from the actual producer's unchanged source family. -/
@[expose] def parentWords : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained →
    List (List (CenteredEdge (Curves.Legendre.Periods.Fibre.frameCurve frame) basis))
  | .inl _original, _sourceOwner, _agreement, retained, sources =>
      Quarter.Sources.parentWords retained sources
  | .inr fine, _sourceOwner, _agreement, retained, sources =>
      LayerAcquisition.Sources.parentWords fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner _sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement _sourceOwner fine.numerical.layer_eq fine.numerical.queried _agreement)
        retained.paid sources

/-- The shared original source assembly preserves the exact ordered parent flattening in both actual branches. -/
theorem assemble_parents : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained) →
    (assemble retained sources).geometry.parents = (parentWords retained sources).flatten
  | .inl _original, _sourceOwner, _agreement, retained, sources =>
      Quarter.Sources.assemble_parents retained sources
  | .inr fine, _sourceOwner, _agreement, retained, sources => by
      unfold assemble
      rewrite [Spine.Sources.Assembled.castEndpoints_parents]
      exact LayerAcquisition.Sources.assemble_parents fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner _sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement _sourceOwner fine.numerical.layer_eq fine.numerical.queried _agreement)
        retained.paid sources

section OriginalReadbacks

open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Meshes

variable {current : Endpoint} {reading : ReadingAt leg.actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) current}
variable {original : Steps.Quarter leg.actual leg.regular current reading originalOwner}
variable {agreement : InitialAgreement current reading sourceOwner}
variable (atSource : current = UniformPrimitiveMesh.firstEndpoint)
variable (retained : Quarter original sourceOwner agreement)

/-- The shared producer executes literally the original old source-family factory on an original Steps input. -/
theorem build_ofSteps :
    build (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
        (sourceTargets := sourceTargets) (input := Input.ofSteps original atSource) retained =
      Quarter.Sources.build (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (sourceTargets := sourceTargets) retained := by
  unfold build
  rfl

/-- Shared old-input assembly is exactly the original assembler on the SAME complete source family. -/
theorem assemble_ofSteps
    (sources : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained) :
    assemble (input := Input.ofSteps original atSource) retained sources =
      Quarter.Sources.assemble retained sources := by
  unfold assemble
  rfl

/-- Shared old-input parent words are the literal original old source-family occurrence lists. -/
theorem parentWords_ofSteps
    (sources : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained) :
    parentWords (input := Input.ofSteps original atSource) retained sources =
      Quarter.Sources.parentWords retained sources := by
  unfold parentWords
  rfl

/-- Transport only an old-input occurrence bound to the SAME original old-quarter assembled parents.

The whole assembler equality preserves the exact natural index. No lookup,
source preparation, observation or original factory is rerun by this bound
transport. It does not identify unrelated Stage preparations.
-/
@[expose] def ofStepsIndex
    (sources : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained)
    (index : Fin (assemble (input := Input.ofSteps original atSource) retained sources).geometry.parents.length) :
    Fin (Quarter.Sources.assemble retained sources).geometry.parents.length :=
  ⟨index.val, Eq.mp (congrArg (fun assembled => index.val < assembled.geometry.parents.length)
    (assemble_ofSteps atSource retained sources)) index.isLt⟩

/-- Old-input index transport preserves the literal original natural occurrence coordinate. -/
theorem ofStepsIndex_val
    (sources : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained)
    (index : Fin (assemble (input := Input.ofSteps original atSource) retained sources).geometry.parents.length) :
    (ofStepsIndex atSource retained sources index).val = index.val := rfl

end OriginalReadbacks

section FineReadbacks

variable (fine : Input.Fine leg)
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl)
  fine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement fine.numerical.initial.lowerEndpoint fine.numerical.initial.source sourceOwner}
variable (retained : Realization (.inr fine) sourceOwner agreement)
variable (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (sourceTargets := sourceTargets) retained)

/-- Fine-input assembly is the exact endpoint transport of the SAME complete original Layer source cache.

The original decomposition's start-time law transports only its physical
endpoint index. The original paid realization, source family, Parents,
preparations, observations and all actual factory receipts are unchanged.
-/
theorem assemble_ofFine :
    assemble retained sources =
      (LayerAcquisition.Sources.assemble fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid sources).castEndpoints
        (congrArg (fun time => coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)
          (fine.numerical.parts.start_time fine.numerical.layer_eq)) rfl := by
  unfold assemble
  rfl

/-- Transport only the finite occurrence bound to the SAME underlying original fine-Layer assembled parents. -/
@[expose] def ofFineIndex
    (index : Fin (assemble retained sources).geometry.parents.length) :
    Fin (LayerAcquisition.Sources.assemble fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid sources).geometry.parents.length := by
  have same := (congrArg (fun assembled => assembled.geometry.parents)
    (assemble_ofFine fine retained sources)).trans
      (Spine.Sources.Assembled.castEndpoints_parents _ _ _)
  exact ⟨index.val, Eq.mp (congrArg (fun parents => index.val < parents.length) same) index.isLt⟩

/-- Fine-input occurrence transport preserves its exact natural coordinate in the original ordered source list. -/
theorem ofFineIndex_val (index : Fin (assemble retained sources).geometry.parents.length) :
    (ofFineIndex fine retained sources index).val = index.val := rfl

end FineReadbacks

section SignedRoots

open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology

/-- Derive the signed root chain of either SAME retained quarter source realization.

The old branch reads its literal paid Quarter. The genuine fine branch
reads its literal Layer acquisition; the original startOwner_name law and
whole assembled endpoint transport change only those exact nominal indices.
No old Steps execution or new source comparison is constructed.
-/
def rootChain : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained) →
    RootChain (assemble retained sources).geometry.parents
      (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName retained.finishOwner.parameterNonzero retained.finishOwner)
  | .inl _original, _sourceOwner, _agreement, retained, sources => by
      unfold assemble
      exact Quarter.Sources.rootChain retained sources
  | .inr fine, sourceOwner, agreement, retained, sources => by
      let original := LayerAcquisition.Sources.assemble fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid sources
      let actual := LayerAcquisition.Sources.rootChain fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid sources
      have names := fine.numerical.parts.startOwner_name sourceOwner fine.numerical.layer_eq
      have parents := Spine.Sources.Assembled.castEndpoints_parents original
        (congrArg (fun time => coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)
          (fine.numerical.parts.start_time fine.numerical.layer_eq)) rfl
      unfold assemble
      exact PreparedBankRootChains.RootChain.castChildren parents.symm
        (PreparedBankRootChains.RootChain.castNames names rfl actual)

end SignedRoots

end Sources

end Steps.Acquisition.Quarter.Input.Realization

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
