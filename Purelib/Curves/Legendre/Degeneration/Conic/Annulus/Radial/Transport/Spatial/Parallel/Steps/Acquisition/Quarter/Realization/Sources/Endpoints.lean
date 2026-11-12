module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Sources.Fine
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation.Source.Assembly.Endpoints
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Sources.Entry.Origin.Endpoints
import Purelib.Data.List.Flatten.Occurrence

/-! # Exact physical endpoint occurrences of either actual retained quarter

The shared old-or-fine source family selects its original whole BlockEntry.
The old branch follows the original paid/source tails; the fine branch reads
its real Origin. Existing retained fine-origin caches have a separate direct
getter, so their physical locator and factor origin are never read again.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Input.Realization.Sources

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Steps.Acquisition.Observation

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {leg : Transport.Leg site parameter unitQuarter}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate

/-- Read the actual physical Segment and child under one supplied complete original quarter BlockEntry.

The two branches are the existing mathematical parents. Exact whole-parent
incidence changes only the displayed parent index; no original Steps,
Layer, physical acquisition, factor observation or source product is built.
The literal Circuit closing OwnerJoin is outside this parent-word lookup.
-/
def physicalOccurrenceOf : {input : Input leg} →
    {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl) input.sourceEndpoint} →
    {agreement : InitialAgreement input.sourceEndpoint input.sourceReading sourceOwner} →
    (retained : Realization input sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (sourceTargets := sourceTargets) retained) →
    (index : Fin (assemble retained sources).geometry.parents.length) →
    (position : Flatten.Occurrence (parentWords retained sources) (flattenedIndex retained sources index)) →
    BlockEntry retained sources position.1 →
    Spine.Sources.ParentOccurrence (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := sourceTargets)
      ((assemble retained sources).geometry.parents[index.val]'index.isLt)
  | .inl original, sourceOwner, agreement, retained, sources, index, position, picked =>
      (Blocks.Sources.Entry.physicalOccurrence retained.originalQuarter.cache.val
        original.current original.reading original.owner retained.originalQuarter.steps
        sourceOwner agreement retained.receipt sources position.1 picked position.2.val).castParent
          (parent_eq retained sources index position).symm
  | .inr fine, _sourceOwner, _agreement, retained, sources, index, position, picked =>
      (fineOriginOf fine retained sources index position picked).physicalOccurrence

section Fine

variable {fine : Input.Fine leg}
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl)
  fine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement fine.numerical.initial.lowerEndpoint fine.numerical.initial.source sourceOwner}
variable {retained : Realization (.inr fine) sourceOwner agreement}
variable {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (sourceTargets := sourceTargets) retained}
variable {index : Fin (assemble retained sources).geometry.parents.length}
variable {position : Flatten.Occurrence (parentWords retained sources) (flattenedIndex retained sources index)}

namespace FineOriginCache

variable (cached : FineOriginCache fine retained sources index position)

/-- Read the physical endpoint occurrence from the SAME already retained whole fine-origin cache.

This operation does not call fineOriginOf, Entry.origin, blockEntry,
sourceOccurrence or any locator. The original full factory receipts and
previous-corner Reading/Samples remain those of cached.origin.
-/
@[expose] def physicalOccurrence : Spine.Sources.ParentOccurrence
    (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
    (targets := sourceTargets)
    ((assemble retained sources).geometry.parents[index.val]'index.isLt) :=
  cached.origin.physicalOccurrence

/-- The complete endpoint view is the original retained Origin view, without a repeated read-only factory. -/
theorem physicalOccurrence_eq : cached.physicalOccurrence = cached.origin.physicalOccurrence := by
  unfold physicalOccurrence
  rfl

/-- The selected physical endpoint occurrence retains the whole original Block occurrence under parent transport. -/
theorem physicalOccurrence_heq :
    HEq cached.physicalOccurrence cached.origin.occurrence.physicalOccurrence :=
  cached.origin.physicalOccurrence_heq

end FineOriginCache

end Fine

end Steps.Acquisition.Quarter.Input.Realization.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
