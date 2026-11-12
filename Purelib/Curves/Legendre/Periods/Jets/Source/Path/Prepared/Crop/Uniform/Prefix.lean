module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Uniform
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop.Entries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
import Purelib.Curves.Legendre.Periods.Jets.Source.Integrands
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Chord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic

/-! # Actual source-query entries from the same retained prefix

The original query result carries its SAME prefix with the producer's
one-endpoint law. The existing lower join and direct/sample root relation
construct its real face Entry without replay. The source observation's
operational root comparison consumes the original stored channel roots.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points.PieceReadings

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.Entries.FaceModels (Entry)
open Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets originalPath stage} {row : Row} {accuracy : AccuracyRequest}
    {prepared : PreparedParent patch count floor covered targets} {lower upper : Rational}
    {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
    {operation : PreparedSubdivisionTrace.PreparedTraceBudget.Trace.CropComparisons
      parent lower upper lowerInside upperInside}
    {cropped : Crop (frame := frame) (basis := basis) (row := row)
      prepared lower upper lowerInside upperInside operation}
    {comparisonRequest requested : AccuracyRequest}
    {observed : cropped.Observation (accuracy := accuracy) comparisonRequest}
    {points : observed.Points requested}
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank}
    {shared : Face.DomainBanks.FaceDomains rootFrames face}
    {firstInside : face.cell.box.Contains (parent.edge.point lower)}
    {acquired : Entry.Acquisition shared.models firstInside points.samples.1.val.owner}
    {domain : PeriodDomain shared.models acquired.entry.sheet}
    {split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper)}
    {position : Fin split.pieces.length}
    {channel : Fin 6} {targetIndex exponent : Nat}
    {oldBank : Bank (Paths.polynomial parameter) domain.geometry} {numerator targetSource : Polynomial}
    {gap : AccuracyRequest}
    (data : UniformPiece (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      channel oldBank numerator targetSource exponent targetIndex gap)

variable {input : Rational} {inside : 0 ≤ input ∧ input ≤ 1}
    (reading : PieceReadings (points := points) (firstInside := firstInside) (acquired := acquired)
      (domain := domain) (split := split) (position := position)
      channel data.restricted data.target.model input inside)

/-- The retained source observation lies at the physical point of its original twice-mapped query.

Both polynomial restrictions preserve the actual algebraic point. The
stored observation factory and original rooted-query readback then identify
that point without constructing another observation or Point owner.
-/
theorem point_eq : reading.2.2.1.val.algebraic.point =
    parent.edge.point (Cell.Restriction.parameter lower upper
      (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
        (auxiliaryPiece split position).interval.upper input)) := by
  have original := (pieceObservation_point (cropped := cropped) split position channel data.restricted input inside
    reading.1).trans (reading.1.point_eq channel)
  exact (congrArg (fun observed : UniformObservation (Fibre.frameCurve frame)
    (Specification.Table.forms parameter channel) (auxiliaryLift parent (auxiliaryPiece split position))
    (Cell.Restriction.model (cropped.models.cell channel) data.restricted) input =>
      observed.algebraic.point) reading.2.2.1.property).trans original

/-- Read the SAME original prefix path; its proof subtype introduces no new path execution. -/
@[expose] def prefixPath :
    OwnerPath (Paths.polynomial parameter) (parent.edge.point lower) cropped.endpoints.1.direct.owner
      (parent.edge.point (Cell.Restriction.parameter lower upper
        (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
          (auxiliaryPiece split position).interval.upper input))) reading.1.direct.owner := reading.2.1.val

/-- The actual stored prefix retains exactly its producer-certified endpoint occurrence. -/
theorem prefix_vertices : (prefixPath data reading).vertices =
    [parent.edge.point (Cell.Restriction.parameter lower upper
      (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
        (auxiliaryPiece split position).interval.upper input))] := reading.2.1.property

include data inside in
/-- The original query point lies in the original regular face, by the SAME retained piece coordinate. -/
private theorem query_inside : face.cell.box.Contains
    (parent.edge.point (Cell.Restriction.parameter lower upper
      (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
        (auxiliaryPiece split position).interval.upper input))) := by
  have physical := (piece_point (cropped := cropped) split position channel data.restricted data.coordinate input).trans
    (prepared.queryPoint_eq _)
  have pieceInside := data.coordinate.point_inside (auxiliaryPiece split position).first_inside
    (auxiliaryPiece split position).last_inside inside.1 inside.2
  exact Eq.mp (congrArg face.cell.box.Contains physical)
    ((domain.patch.cell_refines (auxiliaryPiece split position).column
      (auxiliaryPiece split position).row).contains pieceInside)

/-- Derive the actual original source Point Entry through its SAME stored prefix and original lower join.

The actual direct Query owner and sample owner remain distinct. Their
retained sampleRoots supplies the only final root transport. No query,
selector, frame, path, join or numerical preparation is executed again.
-/
def entry : Entry shared.models
    (parent.edge.point (Cell.Restriction.parameter lower upper
      (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
        (auxiliaryPiece split position).interval.upper input))) reading.1.sample.owner :=
  let first := acquired.entry.followJoin points.joins.1.val
  let reached := first.followQueryCrop parent.edge lower
    (Cell.Restriction.parameter lower upper
      (Cell.Restriction.parameter (auxiliaryPiece split position).interval.lower
        (auxiliaryPiece split position).interval.upper input)) lowerInside
    (Cell.Restriction.parameter_inside lowerInside upperInside
      (Cell.Restriction.parameter_inside
        ⟨(auxiliaryPiece split position).within.1,
          (auxiliaryPiece split position).interval.ordered.le.trans (auxiliaryPiece split position).within.2⟩
        ⟨(auxiliaryPiece split position).within.1.trans (auxiliaryPiece split position).interval.ordered.le,
          (auxiliaryPiece split position).within.2⟩ inside))
    (prefixPath data reading) (prefix_vertices data reading) firstInside (query_inside (inside := inside) data)
  reached.followEquivalent reading.1.sampleRoots

/-- The actual stored prefix and root attachment preserve the original lower Entry's face sheet. -/
theorem entry_sheet : (entry data reading).sheet = acquired.entry.sheet := by
  unfold entry
  refine (Entry.followEquivalent_sheet _ _).trans ?_
  refine (Entry.followQueryCrop_sheet _ _ _ _ _ _ _ _ _ _).trans ?_
  exact Entry.followJoin_sheet acquired.entry points.joins.1.val

/-- Compare the original source observation's root to the SAME retained Point through its actual stored query roots.

Only exact original restriction-name readbacks are transported. The two
operational comparisons are the given Query's sampleRoots and its stored
channel root; neither comparison nor any root owner is reconstructed.
-/
def roots : NamedEquivalent (ownerName reading.1.sample.owner)
    reading.2.2.1.val.algebraic.sheetValue.value.name := by
  have same := (congrArg (fun observed : UniformObservation (Fibre.frameCurve frame)
      (Specification.Table.forms parameter channel) (auxiliaryLift parent (auxiliaryPiece split position))
      (Cell.Restriction.model (cropped.models.cell channel) data.restricted) input =>
        observed.algebraic.sheetValue.value.name) reading.2.2.1.property).trans
      (pieceObservation_root_name (cropped := cropped) split position channel data.restricted input inside reading.1)
  exact NamedEquivalent.transport rfl same.symm
    ((RootedQuery.sampleRoots reading.1).symm.trans ((RootedQuery.roots reading.1).get channel))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points.PieceReadings

end
