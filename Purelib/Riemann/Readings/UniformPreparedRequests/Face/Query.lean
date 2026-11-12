module

public import Purelib.Riemann.Readings.UniformPreparedRequests.Query
public import Purelib.Riemann.Readings.UniformPreparedRequests.Face.Pieces
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

/-! # Retained query entries in original request Point comparisons

A supplied full face-entry acquisition belongs to the actual query Owner.
The same request and supplied Point derive the signed comparison to its
own Owner. The resulting Entry keeps the original selected sheet, so the
same retained domain and primitive polynomials pay the existing piece bound.
No point, query, face-entry acquisition or primitive bank is built here.
-/

public section

namespace Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face
open Face.Entries.FaceModels (Entry)
open Face.FragmentReadings (FragmentBounds)
open Face.InverseModels.BranchCellBank (FaceModels)
open Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Branches.RectangularSheetGauge
open Integration.PreparedConstantModels (PreparedEdge)
open Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Integration.RectangularPrimitiveModels (Primitives)
open Meshes.PuncturedGridFaces (RegularFace)
open Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Paths.RectangularSegmentSplitting (SegmentPiece SegmentSplit)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent : CenteredEdge curve differential} {target : Rational}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
variable {models : FaceModels frames face}
variable {fraction : Rational} {inside : 0 ≤ fraction ∧ fraction ≤ 1}
variable {faceInside : face.cell.box.Contains (parent.edge.point fraction)}

/-- Derive an Entry for the supplied Point from the same retained Query acquisition.

The actual acquisition retains both transport banks and its selected sheet.
Common-seed agreement compares the distinct Query and Point Owners; only
its reachability proof changes. Exposure lets dependent domain clients
reduce the unchanged selected-sheet projection at this original operation.
-/
@[expose] def retainedQueryEntry (request : LocalRequest parent count target)
    (query : PreparedEdge.Query parent.edge fraction inside)
    (sample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point fraction))
    (acquired : Entry.Acquisition models faceInside query.owner) :
    Entry models (parent.edge.point fraction) sample.owner :=
  ⟨acquired.entry.sheet, acquired.entry.reached.append (Entries.Reached.ofEquivalent
    (NamedEquivalent.transport query.name_eq rfl
      (request.retainedQueryEquivalent fraction inside query rfl (request.point_inside inside) sample)))⟩

variable (request : LocalRequest parent count target)
variable (query : PreparedEdge.Query parent.edge fraction inside)
variable (sample : ContinuedNeighborhood.Point request.neighborhood (parent.edge.point fraction))
variable (acquired : Entry.Acquisition models faceInside query.owner)

include sample in
/-- The same acquired query sheet and supplied domain pay the original primitive-piece discrepancy.

Both original primitive polynomials, the retained request index and the
actual oriented displacement remain in the unchanged piece charge. This
is an increment comparison on the supplied domain, with no absolute
primitive normalization or canonical period identification.
-/
theorem faceQuery_increment_le {last : Canonical}
    (domain : PeriodDomain models acquired.entry.sheet)
    (split : SegmentSplit domain.cuts (parent.edge.point fraction) last)
    (lastInside : request.neighborhood.box.Contains last)
    (bounds : FragmentBounds domain.patch differential)
    (piece : SegmentPiece domain.geometry (parent.edge.point fraction) last)
    (member : piece ∈ split.pieces) {index : Nat}
    (primitives : Primitives (Transitions.oriented (domain.patch.sheets.refine index).transitions
      (domain.patch.sheets.refine index).gauge) (PreparedPrimitiveSamples.differentialNumerator differential)) :
    normSq ((primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint) -
      (request.request.model.primitive.value.eval piece.lastPoint -
        request.request.model.primitive.value.eval piece.firstPoint)) ≤
      request.facePieceCharge domain bounds piece index :=
  request.facePiece_increment_le sample (request.retainedQueryEntry query sample acquired) domain split
    fraction inside rfl (request.point_inside inside) lastInside bounds piece member primitives

end Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

end
