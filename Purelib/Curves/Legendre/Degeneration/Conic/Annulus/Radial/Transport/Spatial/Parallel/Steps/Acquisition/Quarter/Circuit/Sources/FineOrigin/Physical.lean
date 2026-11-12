module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.FineOrigin
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Sources.Endpoints
import Purelib.Data.Fin

/-! # Literal physical occurrences read from the retained global fine origins

Each finite branch reads the complete original SourceOccurrence already
inside its stored fine Origin. Whole-parent incidence changes only the
public index. No block locator, origin producer, observer or paid path is
run again, and no earlier-corner Reading or Samples owner is retagged.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source (Vertex)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Input.Realization.Sources (FineOriginCache)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine.Sources (ParentOccurrence)

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstFine : Input.Fine circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
  sourceOwner}
variable {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
variable {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
variable {fourthFine : Input.Fine circuit.fourth}
variable {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}
variable (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

namespace FineOrigin

variable {sources}

/-- Read the original physical occurrence held by the same literal retained quarter branch. -/
@[expose] def physicalOccurrence : (quarter : Fin 4) →
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length) →
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) →
    (cached : FineOrigin sources quarter index position) →
    ParentOccurrence (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (targets := sourceTargets) (parent quarter index position cached) :=
  Data.Fin.casesDependent
    (motive := fun selected : Fin 4 =>
      (index : Fin (quarterSource sources selected).2.geometry.parents.length) →
      (position : Flatten.Occurrence (blockWords sources selected) (blockFlattenedIndex sources selected index)) →
      (cached : FineOrigin sources selected index position) →
      ParentOccurrence (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
        (sheet := sheet) (targets := sourceTargets) (parent selected index position cached))
    (fun _index _position cached => cached.origin.occurrence.physicalOccurrence)
    (fun second => Data.Fin.casesDependent
      (motive := fun selected : Fin 3 =>
        (index : Fin (quarterSource sources selected.succ).2.geometry.parents.length) →
        (position : Flatten.Occurrence (blockWords sources selected.succ)
          (blockFlattenedIndex sources selected.succ index)) →
        (cached : FineOrigin sources selected.succ index position) →
        ParentOccurrence (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
          (sheet := sheet) (targets := sourceTargets) (parent selected.succ index position cached))
      (fun _index _position cached => cached.origin.occurrence.physicalOccurrence)
      (fun third => Data.Fin.casesDependent
        (motive := fun selected : Fin 2 =>
          (index : Fin (quarterSource sources selected.succ.succ).2.geometry.parents.length) →
          (position : Flatten.Occurrence (blockWords sources selected.succ.succ)
            (blockFlattenedIndex sources selected.succ.succ index)) →
          (cached : FineOrigin sources selected.succ.succ index position) →
          ParentOccurrence (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
            (sheet := sheet) (targets := sourceTargets) (parent selected.succ.succ index position cached))
        (fun _index _position cached => cached.origin.occurrence.physicalOccurrence)
        (fun _ : Fin 1 => fun _index _position cached => cached.origin.occurrence.physicalOccurrence) third) second)

/-- The first branch preserves the entire original physical occurrence from its stored SourceOccurrence. -/
theorem physicalOccurrence_first
    (index : Fin (quarterSource sources (0 : Fin 4)).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources (0 : Fin 4))
      (blockFlattenedIndex sources (0 : Fin 4) index))
    (cached : FineOrigin sources (0 : Fin 4) index position) :
    physicalOccurrence (0 : Fin 4) index position cached = cached.origin.occurrence.physicalOccurrence := rfl

/-- The second branch preserves the entire original physical occurrence from its stored SourceOccurrence. -/
theorem physicalOccurrence_second
    (index : Fin (quarterSource sources (1 : Fin 4)).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources (1 : Fin 4))
      (blockFlattenedIndex sources (1 : Fin 4) index))
    (cached : FineOrigin sources (1 : Fin 4) index position) :
    physicalOccurrence (1 : Fin 4) index position cached = cached.origin.occurrence.physicalOccurrence := rfl

/-- The third branch preserves the entire original physical occurrence from its stored SourceOccurrence. -/
theorem physicalOccurrence_third
    (index : Fin (quarterSource sources (2 : Fin 4)).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources (2 : Fin 4))
      (blockFlattenedIndex sources (2 : Fin 4) index))
    (cached : FineOrigin sources (2 : Fin 4) index position) :
    physicalOccurrence (2 : Fin 4) index position cached = cached.origin.occurrence.physicalOccurrence := rfl

/-- The fourth branch preserves the entire original physical occurrence from its stored SourceOccurrence. -/
theorem physicalOccurrence_fourth
    (index : Fin (quarterSource sources (3 : Fin 4)).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources (3 : Fin 4))
      (blockFlattenedIndex sources (3 : Fin 4) index))
    (cached : FineOrigin sources (3 : Fin 4) index position) :
    physicalOccurrence (3 : Fin 4) index position cached = cached.origin.occurrence.physicalOccurrence := rfl

end FineOrigin

namespace OriginAt

variable {sources}
variable {index : Fin (assemble sources).geometry.parents.length}
variable {position : Flatten.Occurrence (parentWords sources) (flattenedIndex sources index)}
variable (retained : OriginAt sources index position)

/-- Read the same whole physical view through the retained global and Block positions without locating again. -/
@[expose] def physicalOccurrence : ParentOccurrence (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (targets := sourceTargets) retained.parent :=
  FineOrigin.physicalOccurrence (quarter sources index position) (child sources index position)
    retained.inBlock retained.cached

/-- The global getter is the exact original finite branch read on the same stored fine cache. -/
theorem physicalOccurrence_eq : retained.physicalOccurrence =
    FineOrigin.physicalOccurrence (quarter sources index position) (child sources index position)
      retained.inBlock retained.cached := rfl

end OriginAt

namespace Requested.SourceOrigin

variable {sources} {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
variable {requested : Requested sources current freshFloor rootStage accuracy}
variable {index : Fin (requested.shape.val.1 :: requested.shape.val.2).length}
variable (retained : SourceOrigin requested index)

/-- Read the original acquired Segment view at this exact fresh-stage whole parent, preserving distinct preparations. -/
@[expose] def physicalOccurrence : ParentOccurrence (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (targets := sourceTargets)
    ((requested.shape.val.1 :: requested.shape.val.2)[index.val]'index.isLt) :=
  retained.origin.physicalOccurrence.castParent retained.parent_eq

/-- Whole-parent index transport retains the complete selected physical cache heterogeneously. -/
theorem physicalOccurrence_heq : HEq retained.physicalOccurrence retained.origin.physicalOccurrence :=
  retained.origin.physicalOccurrence.castParent_heq retained.parent_eq

end Requested.SourceOrigin

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
