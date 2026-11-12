module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Entries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.Chord
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections.ContinuedPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedConstantModels.Axis
import Purelib.Riemann.Paths.ClearBoxPaths.Chord
import Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Models
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Actual same-lineage chord lifts at strict source-piece endpoints

One original source crop supplies both cached RootedQuery answers. The
same selected View's retained all-source family constructs their direct
query path. Their existing sampleRoots construct the two real joins.
A genuinely new lower-Point Entry acquisition retains its own frames and
round-trip rows; original prefix transport proves its sheet agreement.
Sheet-index transport preserves the whole old domain before the original
Chord.ofAcquired constructs its actual corner and returned Entry caches.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.Entries.FaceModels (Entry)
open Face.Periods (PeriodDomain)
open Face.Entries.FaceModels.Entry (PointData)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets originalPath stage} {row : Row} {accuracy : AccuracyRequest}
    {prepared : PreparedParent patch count floor covered targets} {lower upper : Rational}
    {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
    {operation : PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside}
    {cropped : Crop (frame := frame) (basis := basis) (row := row)
      prepared lower upper lowerInside upperInside operation}
    {comparisonRequest requested : AccuracyRequest}
    {observed : cropped.Observation (accuracy := accuracy) comparisonRequest}
    (points : observed.Points requested)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank}
    (shared : Face.DomainBanks.FaceDomains rootFrames face)
    (prefixes : PreparedTraceBudget.Trace.CropFamily.Checked parent lower lowerInside)
    (ordered : lower ≤ upper) (firstInside : face.cell.box.Contains (parent.edge.point lower))
    (acquired : Entry.Acquisition shared.models firstInside points.samples.1.val.owner)
    (domain : PeriodDomain shared.models acquired.entry.sheet)

universe u

variable (families : PreparedTraceBudget.Trace.CropFamily.All parent)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    (position : Fin split.pieces.length)

include cropped in
/-- The same literal strict-child endpoints retain the axis of the original prepared parent.

The endpoint incidences are derived from the original source-model
readbacks and mapped unit bounds. No coordinate incidence, root equality,
sheet agreement or completed mesh-word conclusion is an input.
-/
theorem piece_axis :
    (auxiliaryPiece split position).firstPoint.im = (auxiliaryPiece split position).lastPoint.im ∨
      (auxiliaryPiece split position).firstPoint.re = (auxiliaryPiece split position).lastPoint.re := by
  let piece := auxiliaryPiece split position
  let firstUnit : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  let lastUnit : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  have firstEq := piece_first_eq (cropped := cropped) (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) position
  have lastEq := piece_last_eq (cropped := cropped) (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) position
  have axis := parent.edge.point_axis
    (Cell.Restriction.parameter lower upper piece.interval.lower)
    (Cell.Restriction.parameter lower upper piece.interval.upper)
    (Cell.Restriction.parameter_inside lowerInside upperInside firstUnit)
    (Cell.Restriction.parameter_inside lowerInside upperInside lastUnit)
  rcases axis with horizontalLine | verticalLine
  · exact Or.inl ((congrArg (fun point : Canonical => point.im) firstEq).trans
      (horizontalLine.trans (congrArg (fun point : Canonical => point.im) lastEq).symm))
  · exact Or.inr ((congrArg (fun point : Canonical => point.re) firstEq).trans
      (verticalLine.trans (congrArg (fun point : Canonical => point.re) lastEq).symm))

/-- The exact actual child-corner consumer, retaining every original Query, path, join and domain owner.

This names only a dependent function type. It introduces no replacement
context or counted-data record. Endpoint incidences and sheet agreement
are constructed internally before the callback receives the actual lift.
-/
@[expose] def ChildConsumer (Result : Type u) :=
  let piece := auxiliaryPiece split position
  let firstUnit : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  let lastUnit : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  let firstFraction := Cell.Restriction.parameter lower upper piece.interval.lower
  let lastFraction := Cell.Restriction.parameter lower upper piece.interval.upper
  let firstBound := Cell.Restriction.parameter_inside lowerInside upperInside firstUnit
  let lastBound := Cell.Restriction.parameter_inside lowerInside upperInside lastUnit
  let firstEq := piece_first_eq (cropped := cropped) (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) position
  let lastEq := piece_last_eq (cropped := cropped) (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) position
  let firstFace := Eq.mp (congrArg face.cell.box.Contains firstEq)
    ((domain.patch.cell_refines piece.column piece.row).contains piece.first_inside)
  let lastFace := Eq.mp (congrArg face.cell.box.Contains lastEq)
    ((domain.patch.cell_refines piece.column piece.row).contains piece.last_inside)
  (first : RootedQuery (frame := frame) prepared firstFraction firstBound) →
  first = cropped.queryAt piece.interval.lower firstUnit →
  (last : RootedQuery (frame := frame) prepared lastFraction lastBound) →
  last = cropped.queryAt piece.interval.upper lastUnit →
  (prefixPath : OwnerPath (Paths.polynomial parameter) (parent.edge.point lower) cropped.endpoints.1.direct.owner
    (parent.edge.point firstFraction) first.direct.owner) →
  prefixPath = prefixes.val firstFraction firstBound
    (Cell.Restriction.parameter_ge_left ordered firstUnit.1) cropped.endpoints.1.direct first.direct →
  (carried : Entry shared.models (parent.edge.point firstFraction) first.sample.owner) →
  carried.sheet = acquired.entry.sheet →
  (moving : OwnerPath (Paths.polynomial parameter) (parent.edge.point firstFraction) first.direct.owner
    (parent.edge.point lastFraction) last.direct.owner) →
  moving = (families firstFraction firstBound).val lastFraction lastBound
    (Cell.Restriction.parameter_le ordered piece.interval.ordered.le) first.direct last.direct →
  (vertices : moving.vertices = [parent.edge.point lastFraction]) →
  (sourceJoin : OwnerJoin first.sample.owner first.direct.owner) →
  sourceJoin = OwnerJoin.acquire first.sample.owner first.direct.owner first.sampleRoots.symm →
  (targetJoin : OwnerJoin last.direct.owner last.sample.owner) →
  targetJoin = OwnerJoin.acquire last.direct.owner last.sample.owner last.sampleRoots →
  (childAcquired : Entry.Acquisition shared.models firstFace first.sample.owner) →
  childAcquired = Entry.Acquisition.build shared.models firstFace first.sample.owner →
  (sameSheet : childAcquired.entry.sheet = acquired.entry.sheet) →
  (childDomain : PeriodDomain shared.models childAcquired.entry.sheet) →
  childDomain = PeriodDomain.castSheet sameSheet.symm domain →
  HEq childDomain domain →
  (geometry : ClearBoxPaths.Chord.Prepared face.clearance face.cell.box_proper
    (parent.edge.point firstFraction) (parent.edge.point lastFraction) firstFace lastFace) →
  geometry = ClearBoxPaths.Chord.prepare face.clearance face.cell.box_proper
    (parent.edge.point firstFraction) (parent.edge.point lastFraction) firstFace lastFace →
  (lifted : Face.PrimitiveData.Chord.Lifted (curve := Fibre.frameCurve frame)
    (basis := basis) (parent := parent.edge)
    (lower := firstFraction) (upper := lastFraction) (lowerInside := firstBound) (upperInside := lastBound)
    (firstInside := firstFace) (lastInside := lastFace)
    shared geometry (PointData.ofPoint (curve := Fibre.frameCurve frame) first.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := firstFraction) (inside := firstBound)))
      (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := lastFraction) (inside := lastBound)))
      moving vertices sourceJoin targetJoin
      childAcquired childDomain count) →
  lifted = Face.PrimitiveData.Chord.ofAcquired (curve := Fibre.frameCurve frame)
    (basis := basis) (parent := parent.edge)
    (lower := firstFraction) (upper := lastFraction) (lowerInside := firstBound) (upperInside := lastBound)
    (firstInside := firstFace) (lastInside := lastFace)
    shared geometry (PointData.ofPoint (curve := Fibre.frameCurve frame) first.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := firstFraction) (inside := firstBound)))
      (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := lastFraction) (inside := lastBound)))
      moving vertices sourceJoin targetJoin
      childAcquired childDomain count →
  piece.firstPoint = parent.edge.point firstFraction →
  piece.lastPoint = parent.edge.point lastFraction → Result

/-- Construct the geometric caches only after binding both complete original endpoint Query answers. -/
private def atEndpoints {Result : Type u} :
  let piece := auxiliaryPiece split position
  let firstUnit : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  let lastUnit : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  let firstFraction := Cell.Restriction.parameter lower upper piece.interval.lower
  let lastFraction := Cell.Restriction.parameter lower upper piece.interval.upper
  let firstBound := Cell.Restriction.parameter_inside lowerInside upperInside firstUnit
  let lastBound := Cell.Restriction.parameter_inside lowerInside upperInside lastUnit
  (first : RootedQuery (frame := frame) prepared firstFraction firstBound) →
  first = cropped.queryAt piece.interval.lower firstUnit →
  (last : RootedQuery (frame := frame) prepared lastFraction lastBound) →
  last = cropped.queryAt piece.interval.upper lastUnit →
  ChildConsumer (points := points) shared prefixes ordered firstInside acquired domain
    families split position Result → Result :=
  let piece := auxiliaryPiece split position
  let firstUnit : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  let lastUnit : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  let firstFraction := Cell.Restriction.parameter lower upper piece.interval.lower
  let lastFraction := Cell.Restriction.parameter lower upper piece.interval.upper
  let firstBound := Cell.Restriction.parameter_inside lowerInside upperInside firstUnit
  let lastBound := Cell.Restriction.parameter_inside lowerInside upperInside lastUnit
  let firstEq := piece_first_eq (cropped := cropped) (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) position
  let lastEq := piece_last_eq (cropped := cropped) (points := points) (firstInside := firstInside)
    (acquired := acquired) (domain := domain) (split := split) position
  let firstFace := Eq.mp (congrArg face.cell.box.Contains firstEq)
    ((domain.patch.cell_refines piece.column piece.row).contains piece.first_inside)
  let lastFace := Eq.mp (congrArg face.cell.box.Contains lastEq)
    ((domain.patch.cell_refines piece.column piece.row).contains piece.last_inside)
  fun first firstFactory last lastFactory consume =>
    let moving := (families firstFraction firstBound).val lastFraction lastBound
      (Cell.Restriction.parameter_le ordered piece.interval.ordered.le) first.direct last.direct
    have vertices : moving.vertices = [parent.edge.point lastFraction] :=
      (families firstFraction firstBound).property lastFraction lastBound
        (Cell.Restriction.parameter_le ordered piece.interval.ordered.le) first.direct last.direct
    let sourceJoin := OwnerJoin.acquire first.sample.owner first.direct.owner first.sampleRoots.symm
    let targetJoin := OwnerJoin.acquire last.direct.owner last.sample.owner last.sampleRoots
    let childAcquired := Entry.Acquisition.build shared.models firstFace first.sample.owner
    points.withQueryEntry prefixes firstInside acquired first
      (Cell.Restriction.parameter_ge_left ordered firstUnit.1) firstFace
      (fun prefixPath prefixEq carried carriedSheet =>
        let sameSheet := (childAcquired.entry.sheet_unique carried firstFace).trans carriedSheet
        let childDomain := PeriodDomain.castSheet sameSheet.symm domain
        let geometry := ClearBoxPaths.Chord.prepare face.clearance face.cell.box_proper
          (parent.edge.point firstFraction) (parent.edge.point lastFraction) firstFace lastFace
        let lifted := Face.PrimitiveData.Chord.ofAcquired (curve := Fibre.frameCurve frame)
          (basis := basis) (parent := parent.edge)
          (lower := firstFraction) (upper := lastFraction) (lowerInside := firstBound) (upperInside := lastBound)
          (firstInside := firstFace) (lastInside := lastFace)
          shared geometry (PointData.ofPoint (curve := Fibre.frameCurve frame) first.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := firstFraction) (inside := firstBound)))
            (PointData.ofPoint (curve := Fibre.frameCurve frame) last.sample
        (RootedQuery.sample_inside (frame := frame) (basis := basis) (prepared := prepared)
          (fraction := lastFraction) (inside := lastBound)))
            moving vertices sourceJoin targetJoin
            childAcquired childDomain count
        consume first firstFactory last lastFactory prefixPath prefixEq carried carriedSheet moving rfl vertices
          sourceJoin rfl targetJoin rfl childAcquired rfl sameSheet childDomain rfl
          (PeriodDomain.castSheet_heq sameSheet.symm domain) geometry rfl lifted rfl firstEq lastEq)

/-- Construct an actual chord lift for the SAME literal strict-child Query endpoints and old domain.

The original source queryAt executes once per endpoint and preserves its
zero/unit reuse branches. The moving crop consumes those actual direct
Owners through the retained same-View family. The new lower Entry's sheet
is proved from the original prefix transport and actual Entry uniqueness;
only this derived equality transports the entire old PeriodDomain. No
source model, preparation, selector or old observation is reconstructed,
and no geometric endpoint/primitive/period conclusion is an input.
-/
def withChildLift {Result : Type u}
    (consume : ChildConsumer (points := points) shared prefixes ordered firstInside acquired domain
      families split position Result) : Result :=
  let piece := auxiliaryPiece split position
  let firstUnit : 0 ≤ piece.interval.lower ∧ piece.interval.lower ≤ 1 :=
    ⟨piece.within.1, piece.interval.ordered.le.trans piece.within.2⟩
  let lastUnit : 0 ≤ piece.interval.upper ∧ piece.interval.upper ≤ 1 :=
    ⟨piece.within.1.trans piece.interval.ordered.le, piece.within.2⟩
  let first := cropped.queryAt piece.interval.lower firstUnit
  let last := cropped.queryAt piece.interval.upper lastUnit
  atEndpoints (points := points) shared prefixes ordered firstInside acquired domain
    families split position first rfl last rfl consume

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
