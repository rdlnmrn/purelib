module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Sources.Occurrence
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial.Acquisition.Sources.Entry.Origin
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Repeat

/-! # Literal fine-quarter source origins from the same shared Block occurrence

One original shared quarter/Block position selects its complete Entry once.
The original fine Entry origin reader then retains the same Block, Piece,
source family and physical source occurrence. Whole factory equalities stay
beside both readonly results. Original decomposition membership derives the
actual Layer membership and its independently scheduled width payment.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Input.Realization.Sources

open Purelib
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
open Layer.Spatial renaming Acquisition → LayerAcquisition
open Layer.Spatial.Acquisition.Sources.Entry (Origin)

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {leg : Transport.Leg site parameter unitQuarter}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}
variable (fine : Input.Fine leg)
variable {sourceOwner : OwnerAt site parameter unitQuarter (of_decide_eq_true rfl)
  fine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement fine.numerical.initial.lowerEndpoint fine.numerical.initial.source sourceOwner}
variable (retained : Realization (.inr fine) sourceOwner agreement)
variable (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (sourceTargets := sourceTargets) retained)
variable (index : Fin (assemble retained sources).geometry.parents.length)
variable (position : Flatten.Occurrence (parentWords retained sources) (flattenedIndex retained sources index))

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The original fine Entry source-origin family at this SAME actual quarter parent and Piece decomposition. -/
@[expose] def FineOrigin :=
  LayerAcquisition.Sources.Entry.Origin (regular := leg.regular) (frame := frame) (basis := basis)
    (count := count) (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets)
    (fine.numerical.parts.first :: fine.numerical.parts.remaining)
    ((assemble retained sources).geometry.parents[index.val]'index.isLt)

/-- Derive the actual fine origin from a supplied SAME original BlockEntry without replaying its producer.

The complete original Block/source-pair equality changes only the physical
child bound. The shared quarter's whole parent-incidence law transports the
result to its actual quarter index, preserving all retained mathematical data.
-/
def fineOriginOf (picked : BlockEntry retained sources position.1) :
    FineOrigin fine retained sources index :=
  (LayerAcquisition.Sources.Entry.origin fine.numerical.finish
    fine.numerical.parts.remaining fine.numerical.parts.first
    (fun piece member => fine.numerical.layer.queried_of_factory fine.numerical.layer_eq
      fine.numerical.queried piece (fine.numerical.parts.remaining_member piece member))
    (fine.numerical.parts.startOwner sourceOwner fine.numerical.layer_eq)
    (fine.numerical.parts.startAgreement sourceOwner fine.numerical.layer_eq fine.numerical.queried agreement)
    retained.paid sources position.1 picked position.2.val).castParent
      (parent_eq retained sources index position).symm

/-- The SAME original shared BlockEntry and its derived actual fine source-origin cache, with both whole factory laws.

Only two readonly results are added to existing Sigma/subtype containers.
The original quarter, source family, position and all original owner/query
indices remain inputs; no numerical observation or paid acquisition is new.
-/
@[expose] def FineOriginCache :=
  Σ picked : { value : BlockEntry retained sources position.1 //
      value = blockEntry retained sources position.1 },
    { origin : FineOrigin fine retained sources index //
      origin = fineOriginOf fine retained sources index position picked.val }

/-- Read the original selected Entry once, then retain its actual fine origin and complete factory equality once. -/
def keepFineOrigin : FineOriginCache fine retained sources index position :=
  let picked := blockEntry retained sources position.1
  let origin := fineOriginOf fine retained sources index position picked
  ⟨⟨picked, rfl⟩, ⟨origin, rfl⟩⟩

namespace FineOriginCache

variable {fine retained sources index position}
variable (cached : FineOriginCache fine retained sources index position)

/-- Read the SAME complete original shared BlockEntry selected at this actual occurrence. -/
@[expose] def picked := cached.1.val

/-- The retained complete Entry is exactly the original shared readonly selector, including its whole input receipt. -/
theorem picked_eq : cached.picked = blockEntry retained sources position.1 := cached.1.property

/-- Read the SAME actual fine Origin retaining its Piece, Block, physical Sources and SourceOccurrence. -/
@[expose] def origin := cached.2.val

/-- The whole retained fine Origin is exactly the original Entry-origin reader on that SAME selected Entry. -/
theorem origin_eq : cached.origin = fineOriginOf fine retained sources index position cached.picked :=
  cached.2.property

/-- Whole original parent incidence is derived for the literal actual retained SourceOccurrence. -/
theorem parent_eq : cached.origin.occurrence.parent =
    (assemble retained sources).geometry.parents[index.val]'index.isLt := Origin.parent_eq cached.origin

/-- The selected Piece is a genuine member of the SAME actual Layer, including original decomposition transport. -/
theorem member : cached.origin.piece ∈ fine.numerical.layer.pieces :=
  Eq.mpr (congrArg (fun pieces => cached.origin.piece ∈ pieces) fine.numerical.parts.pieces_eq)
    (Origin.member cached.origin)

/-- The actual scheduled numerical depth pays this SAME selected Block's repeat-window width internally.

The depth argument is discharged by Numerical.scheduled_ten_le for a real
scheduled input. The old Piece and Block are unchanged; no old depth-seven
radius is strengthened by choosing an unrelated auxiliary request.
-/
theorem width (ten : 10 ≤ fine.numerical.depth) :
    (cached.origin.piece.span.lower - cached.origin.target.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10 :=
  cached.origin.block.width_eq.trans_le
    (fine.numerical.layer.width_le 10 ten cached.origin.piece cached.member)

section RepeatedSources

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {leftQuarter rightQuarter : UnitCircuitQuarter}
variable {leftLeg : Transport.Leg site parameter leftQuarter} {rightLeg : Transport.Leg site parameter rightQuarter}
variable {leftFine : Input.Fine leftLeg} {rightFine : Input.Fine rightLeg}
variable {leftOwner : OwnerAt site parameter leftQuarter (of_decide_eq_true rfl)
  leftFine.numerical.initial.lowerEndpoint}
variable {rightOwner : OwnerAt site parameter rightQuarter (of_decide_eq_true rfl)
  rightFine.numerical.initial.lowerEndpoint}
variable {leftAgreement : InitialAgreement leftFine.numerical.initial.lowerEndpoint leftFine.numerical.initial.source
  leftOwner}
variable {rightAgreement : InitialAgreement rightFine.numerical.initial.lowerEndpoint rightFine.numerical.initial.source
  rightOwner}
variable {leftPaid : Realization (.inr leftFine) leftOwner leftAgreement}
variable {rightPaid : Realization (.inr rightFine) rightOwner rightAgreement}
variable {leftSources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (sourceTargets := sourceTargets) leftPaid}
variable {rightSources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) (sourceTargets := sourceTargets) rightPaid}
variable {leftIndex : Fin (assemble leftPaid leftSources).geometry.parents.length}
variable {rightIndex : Fin (assemble rightPaid rightSources).geometry.parents.length}
variable {leftPosition : Flatten.Occurrence (parentWords leftPaid leftSources)
  (flattenedIndex leftPaid leftSources leftIndex)}
variable {rightPosition : Flatten.Occurrence (parentWords rightPaid rightSources)
  (flattenedIndex rightPaid rightSources rightIndex)}

/-- Compare the actual source queries of two original fine-origin caches at a repeated physical point.

Both original Piece/Block/SourceOccurrence inputs remain unchanged. Actual
Layer membership and the two supplied depth payments derive the Route widths;
the original half-open/window/cofactor comparison derives the signed full-y
relation. Coordinate equality alone is never used as root agreement.
-/
def queries_at_repeat
    (left : FineOriginCache leftFine leftPaid leftSources leftIndex leftPosition)
    (right : FineOriginCache rightFine rightPaid rightSources rightIndex rightPosition)
    (leftTen : 10 ≤ leftFine.numerical.depth) (rightTen : 10 ≤ rightFine.numerical.depth)
    (samePoint : (PreparedParent.startPoint left.origin.occurrence.parent).coordinate =
      (PreparedParent.startPoint right.origin.occurrence.parent).coordinate) :
    NamedEquivalent
      (left.origin.occurrence.parent.edge.rootName 0 left.origin.occurrence.parent.edge.baseInside)
      (right.origin.occurrence.parent.edge.rootName 0 right.origin.occurrence.parent.edge.baseInside) :=
  Steps.Acquisition.Block.SourceOccurrence.queries_at_repeat left.origin.occurrence right.origin.occurrence
    (left.width leftTen) (right.width rightTen)
    (left.origin.occurrence.point_start.trans
      (samePoint.trans right.origin.occurrence.point_start.symm))

end RepeatedSources

end FineOriginCache

end Steps.Acquisition.Quarter.Input.Realization.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
