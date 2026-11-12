module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Sources
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Sources.Occurrence
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation.Source.Assembly
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.List.Flatten.Occurrence

/-! # Literal Block occurrence descent through both actual retained quarter source families

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
open Purelib.Data.List
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Meshes
open Steps.Acquisition.Observation
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

namespace Sources

/-- The selected Block view is its existing old-Steps or genuine fine-Layer cache family.

Both branches retain their actual complete paid Block and physical source
pair with its whole original input equation. No new context record, Owner,
geometry, acquisition, source observation or dummy old execution is built.
-/
@[expose] def BlockEntry : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained) →
    (outer : Fin (parentWords retained sources).length) → Type 1
  | .inl original, sourceOwner, agreement, retained, sources, outer =>
      Blocks.Sources.Entry retained.originalQuarter.cache.val original.current original.reading original.owner
        retained.originalQuarter.steps sourceOwner agreement retained.receipt sources outer
  | .inr fine, sourceOwner, agreement, retained, sources, outer =>
      LayerAcquisition.Sources.Entry fine.numerical.finish fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid sources outer

/-- Read the SAME whole actual Block/source input at its literal retained Block occurrence. -/
@[expose] def blockEntry : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained) →
    (outer : Fin (parentWords retained sources).length) → BlockEntry retained sources outer
  | .inl original, sourceOwner, agreement, retained, sources, outer =>
      Blocks.Sources.entry retained.originalQuarter.cache.val original.current original.reading original.owner
        retained.originalQuarter.steps sourceOwner agreement retained.receipt sources outer
  | .inr fine, sourceOwner, agreement, retained, sources, outer =>
      LayerAcquisition.Sources.entry fine.numerical.finish fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid sources outer

/-- Read the complete original selected Block covering/preparation pair, preserving its exact cached parents.

The existing branch-specific Entry.sources consumes the retained whole input
equation. All second-L-edge previous Reading/Samples and actual factor Fold
caches remain those of the supplied Block; no source is retagged or rerun.
-/
@[expose] def blockSources : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained) →
    (outer : Fin (parentWords retained sources).length) → BlockEntry retained sources outer →
    Blocks.Sources.SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sourceTargets := sourceTargets)
      ((parentWords retained sources)[outer.val]'outer.isLt)
  | .inl original, sourceOwner, agreement, retained, sources, outer, picked =>
      Blocks.Sources.Entry.sources retained.originalQuarter.cache.val original.current original.reading original.owner
        retained.originalQuarter.steps sourceOwner agreement retained.receipt sources outer picked
  | .inr fine, sourceOwner, agreement, retained, sources, outer, picked =>
      LayerAcquisition.Sources.Entry.sources fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid sources outer picked

variable {input : Input leg}
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint}
variable {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner}
variable (retained : Realization input sourceOwner agreement)
variable (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (sourceTargets := sourceTargets) retained)

/-- Read the literal natural occurrence coordinate in this SAME actual quarter's original Block flattening. -/
@[expose] def flattenedIndex (index : Fin (assemble retained sources).geometry.parents.length) :
    Fin (parentWords retained sources).flatten.length :=
  ⟨index.val, Eq.mp (congrArg (fun parents => index.val < parents.length)
    (assemble_parents retained sources)) index.isLt⟩

/-- Execute the original finite flatten locator on the SAME actual quarter occurrence once. -/
def locate (index : Fin (assemble retained sources).geometry.parents.length) :
    Flatten.Occurrence (parentWords retained sources) (flattenedIndex retained sources index) :=
  Flatten.locate (parentWords retained sources) (flattenedIndex retained sources index)

/-- The retained quarter location is the whole original finite locator result on the exact same input. -/
theorem locate_eq (index : Fin (assemble retained sources).geometry.parents.length) :
    locate retained sources index =
      Flatten.locate (parentWords retained sources) (flattenedIndex retained sources index) := by
  unfold locate
  rfl

variable (index : Fin (assemble retained sources).geometry.parents.length)
variable (position : Flatten.Occurrence (parentWords retained sources) (flattenedIndex retained sources index))

/-- Read the actual complete Block input from the supplied original aggregate quarter location without rescanning. -/
@[expose] def selected : BlockEntry retained sources position.1 := blockEntry retained sources position.1

/-- Read the SAME original Block covering/preparation pair, including every source request and six-channel model. -/
@[expose] def selectedSources :=
  blockSources retained sources position.1 (selected retained sources index position)

/-- The shared selected whole source pair reduces to the original Steps pair on the identical retained occurrence.

The only transport changes the original parent-list index bound. Both the
selected complete cover and prepared-source product are preserved; no source
or observation factory executes in this readback.
-/
theorem selectedSources_ofSteps {current : Endpoint} {reading : ReadingAt leg.actual current}
    {originalOwner originalSourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) current}
    {original : Steps.Quarter leg.actual leg.regular current reading originalOwner}
    {originalAgreement : InitialAgreement current reading originalSourceOwner}
    (atSource : current = UniformPrimitiveMesh.firstEndpoint)
    (originalRetained : Quarter original originalSourceOwner originalAgreement)
    (originalSources : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) originalRetained)
    (originalIndex : Fin (assemble (input := Input.ofSteps original atSource)
      originalRetained originalSources).geometry.parents.length)
    (originalPosition : Flatten.Occurrence
      (parentWords (input := Input.ofSteps original atSource) originalRetained originalSources)
      (flattenedIndex (input := Input.ofSteps original atSource) originalRetained originalSources originalIndex)) :
    selectedSources (input := Input.ofSteps original atSource) originalRetained originalSources
        originalIndex originalPosition =
      Quarter.Sources.selectedSources originalRetained originalSources
        (ofStepsIndex atSource originalRetained originalSources originalIndex) originalPosition := by
  rfl

/-- A quarter occurrence is exactly its selected Block child, independent of coordinate coincidences. -/
theorem parent_eq :
    (assemble retained sources).geometry.parents[index.val]'index.isLt =
      ((parentWords retained sources)[position.1.val]'position.1.isLt)[position.2.val.val]'position.2.val.isLt :=
  (getElem_congr (assemble_parents retained sources) rfl index.isLt).trans position.2.property.1

/-- Exact original endpoint-index transports retain the WHOLE selected Block PreparedParent in either actual branch.

The proof consumes whole original assembly/cache equations, literal finite
indices and existing PreparedParent incidence. It does not identify fresh
Stage preparations with local ones or infer a signed relation from a point.
-/
theorem prepared_heq :
    HEq ((assemble retained sources).prepared.entry index)
      ((selectedSources retained sources index position).2.entry position.2.val) := by
  cases input with
  | inl original =>
      let originalIndex := ofStepsIndex original.initial retained sources index
      have same := assemble_ofSteps original.initial retained sources
      exact (Spine.Sources.Assembled.entry_heq_of_eq _ _ same index originalIndex rfl).trans
        (Quarter.Sources.prepared_heq retained sources originalIndex position)
  | inr fine =>
      let raw := LayerAcquisition.Sources.assemble fine.numerical.finish
        fine.numerical.parts.remaining fine.numerical.parts.first
        (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
          fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
        (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
        (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
        retained.paid sources
      let startEqual := (congrArg (fun time => coordinate site parameter 2 unitQuarter (of_decide_eq_true rfl) time)
          (fine.numerical.parts.start_time fine.numerical.layer_eq))
      have same := assemble_ofFine fine retained sources
      let transported : Fin (raw.castEndpoints startEqual rfl).geometry.parents.length :=
        ⟨index.val, Eq.mp (congrArg (fun assembled => index.val < assembled.geometry.parents.length)
          same) index.isLt⟩
      let rawIndex := ofFineIndex fine retained sources index
      exact (Spine.Sources.Assembled.entry_heq_of_eq _ _ same index transported rfl).trans
        ((raw.castEndpoints_entry_heq startEqual rfl rawIndex transported rfl).trans
          (LayerAcquisition.Sources.prepared_heq fine.numerical.finish
            fine.numerical.parts.remaining fine.numerical.parts.first
            (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
              fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
            (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
            (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
            retained.paid sources rawIndex position))

end Sources

end Steps.Acquisition.Quarter.Input.Realization

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
