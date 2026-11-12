module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners.Intersections.Readings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections.Primitive

/-! # Actual analytic source requests from the retained signed cut bank

Strict branches reuse their original complete Point/Entry and both
connection caches. Each route obtains a distinct numerical preparation
and retains either its paid same-data request or its computed missing
stage. Unit branches retain the original endpoint cache unchanged.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.TracedPoint (PrimitivePreparation)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Triangles
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {face : RegularFace bank}
variable {coarse : frames.CellRestriction face.cell face.member} {points : List Canonical}
variable {cuts : CutPartition face.cell.box points} {retained : CellRows old face coarse cuts}
variable {models : FaceModels frames face} {base : Canonical}
variable {stem : Walks.Walk retained.grid face.cell.box.anchor base}
variable {member : FromStates.ContainsVertex retained.grid base}
variable {oldCount : Nat} {oldNeighborhood : ContinuedNeighborhood curve.polynomial oldCount}
variable {oldSample : ContinuedNeighborhood.Point oldNeighborhood base}
variable {classified : retained.PointEntry models stem member oldSample}
variable {located : ClearGrid.CornerLocation retained.grid base} {vertices : VertexBank retained.grid}
variable (lifted : classified.CellLift located vertices)

variable {lineFirst lineLast : Canonical} {triangle : CoordinateTriangle}
variable {apex : AffineCut.Apex lineFirst lineLast triangle}
variable (crossing : AffineCut.CrossingCache lineFirst lineLast triangle apex) (position : Fin 2)
variable (factory : triangle =
  ⟨vertices.coordinate (lifted.cell.quad.faces position).first,
    vertices.coordinate (lifted.cell.quad.faces position).second,
    vertices.coordinate (lifted.cell.quad.faces position).third⟩)

namespace Resolved

variable {lifted crossing position factory} {side : Fin 2}
variable {available : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) side).finish)}
variable {count : Nat}
variable (resolved : lifted.Resolved crossing position factory side available count)
variable {domain : PeriodDomain models classified.entry.sheet} {differential : Differential genus} {stage : Nat}
variable (data : DomainPrimitives domain differential stage)
variable (readings : PointReadings data.anchors data.offsets crossing.coordinate)
variable (parentSheet : Fin 2) (target : Rational) (positive : 0 < target)

/-- The two actual strict source preparations and their requests retain the same original Point and connections. -/
abbrev StrictPrimitiveRequests
    (strict : Σ _ : {_value : Unit // crossing.time side < 1},
      {value : lifted.PreparedSide crossing position factory side count //
        value = lifted.prepareSide crossing position factory side count})
    (data : DomainPrimitives domain differential stage)
    (readings : PointReadings data.anchors data.offsets crossing.coordinate)
    (parentSheet : Fin 2) (target : Rational) (positive : 0 < target) : Type 2 :=
  Σ first : {value : strict.2.val.prepared.PrimitivePreparation
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).start)
      (lifted.cutStart (apex := apex) position side).val (lifted.cutStart (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside
      strict.2.val.first domain differential parentSheet //
    value = strict.2.val.prepared.preparePrimitives
      (lifted.cutStart (apex := apex) position side).val (lifted.cutStart (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside
      strict.2.val.first domain differential parentSheet},
  Σ last : {value : strict.2.val.prepared.PrimitivePreparation
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).finish)
      (lifted.cutFinish (apex := apex) position side).val (lifted.cutFinish (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside
      strict.2.val.last domain differential parentSheet //
    value = strict.2.val.prepared.preparePrimitives
      (lifted.cutFinish (apex := apex) position side).val (lifted.cutFinish (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside
      strict.2.val.last domain differential parentSheet},
  first.val.Requests data readings target positive × last.val.Requests data readings target positive

/-- The actual resolved branch retains both source preparations and their same-data finite request attempts.

Strict branches carry the SAME existing Point and source connections.
Unit branches preserve their original endpoint result verbatim; this
operation does not manufacture an analytic path request for that branch.
-/
abbrev PrimitiveRequests : Type 2 :=
  match resolved with
  | Sum.inl strict =>
      StrictPrimitiveRequests strict data readings parentSheet target positive
  | Sum.inr endpoint =>
      ULift.{2} {value : lifted.EndpointAt crossing position factory side available endpoint.1.property //
        value = endpoint.2}

/-- Prepare both actual strict source routes and attempt their same-old-data analytic requests once.

New work is two distinct covered traces, proper parent meshes, endpoint
selections and sufficient-stage controlled requests. Existing Points,
Entries, connection joins and old primitive readings are never replayed.
-/
def requestPrimitives : resolved.PrimitiveRequests data readings parentSheet target positive :=
  match resolved with
  | Sum.inl strict =>
      let first := strict.2.val.prepared.preparePrimitives
        (lifted.cutStart (apex := apex) position side).val (lifted.cutStart (apex := apex) position side).property
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside
        strict.2.val.first domain differential parentSheet
      let last := strict.2.val.prepared.preparePrimitives
        (lifted.cutFinish (apex := apex) position side).val (lifted.cutFinish (apex := apex) position side).property
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside
        strict.2.val.last domain differential parentSheet
      let firstRequests := first.request data readings target positive
      let lastRequests := last.request data readings target positive
      ⟨⟨first, rfl⟩, ⟨last, rfl⟩, firstRequests, lastRequests⟩
  | Sum.inr endpoint => .up ⟨endpoint.2, rfl⟩

section StrictLeading

variable (strict : Σ _ : {_value : Unit // crossing.time 0 < 1},
  {value : lifted.PreparedSide crossing position factory 0 count //
    value = lifted.prepareSide crossing position factory 0 count})
variable (requested : StrictPrimitiveRequests strict data readings parentSheet target positive)

/-- The actual leading source request pays the literal apex-to-cut increment on the old primitive bank.

The source coordinate is read from the original signed side indices.
The analytic estimate uses the request's retained primitive cache; the
signed Point/source Owners remain the original strict branch's inputs.
-/
theorem PrimitiveRequests.first_accurate
    (budget : Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy
      requested.1.val.entered.globalBounds requested.1.val.entered.domain.steps
      requested.1.val.entered.mesh.splits.pieceCount (target / 4))
    (later : budget.grid.index ≤ stage)
    (paid : requested.2.2.1.1.val.Request budget later) :
    Norm.Basic.normSq ((readings.values 1 - readings.values 0) - paid.val.request.primitiveSum) < target := by
  have firstEq := crossing.coordinate_zero.trans
    (congrArg Prod.fst (crossing.edge_coordinates vertices.coordinate
      (lifted.cell.quad.faces position) factory 0)).symm
  exact Entry.TracedPoint.PrimitivePreparation.Requests.accurate requested.2.2.1 budget later paid 0 1
    firstEq crossing.coordinate_one

/-- The other source request pays second-corner-to-cut; the literal cut-to-corner word retains the opposite sign.

This uses the actual reverse-side source trace without reversing an
arbitrary OwnerLink or identifying its Owner with the cut Point.
-/
theorem PrimitiveRequests.last_accurate
    (budget : Integration.Polynomial.Rectangle.Accuracy.Fragment.FragmentAccuracy
      requested.2.1.val.entered.globalBounds requested.2.1.val.entered.domain.steps
      requested.2.1.val.entered.mesh.splits.pieceCount (target / 4))
    (later : budget.grid.index ≤ stage)
    (paid : requested.2.2.2.1.val.Request budget later) :
    Norm.Basic.normSq ((readings.values 1 - readings.values 2) - paid.val.request.primitiveSum) < target := by
  have firstEq : crossing.coordinate 2 =
      vertices.coordinate (apex.edge (lifted.cell.quad.faces position) 0).finish := by
    rw [apex.edge_finish]
    exact (crossing.coordinate_two.trans (AffineCut.corner_one crossing.original).symm).trans
      (crossing.original_corner vertices.coordinate (lifted.cell.quad.faces position) factory 1)
  exact Entry.TracedPoint.PrimitivePreparation.Requests.accurate requested.2.2.2 budget later paid 2 1
    firstEq crossing.coordinate_one

end StrictLeading

end Resolved

variable (firstAvailable : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 0).finish))
variable (lastAvailable : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 1).finish))
variable (count : Nat)
variable (first : lifted.Resolved crossing position factory 0 firstAvailable count)
variable (last : lifted.Resolved crossing position factory 1 lastAvailable count)

namespace SourceBank.PrimitiveReadings

variable {lifted crossing position factory firstAvailable lastAvailable count first last}
variable {cached : lifted.SourceBank crossing position factory firstAvailable lastAvailable count first last}
variable {domain : PeriodDomain models classified.entry.sheet} {differential : Differential genus} {stage : Nat}
variable {data : DomainPrimitives domain differential stage}
variable (observed : cached.PrimitiveReadings data)

/-- Retain the whole source/primitive/reading cache and both literal resolved-source request results.

The two branches are read from the SAME stored resolved product. This
retains both signed source IDs, both Points/Entries and every actual
connection/join, including repeated or collapsed geometric occurrences.
-/
abbrev SourceRequests (parentSheet : Fin 2) (target : Rational) (positive : 0 < target) :=
  {value : cached.PrimitiveReadings data // value = observed} ×
  (Σ _leading : {value : observed.original.resolved.1.PrimitiveRequests data observed.readings
      parentSheet target positive //
    value = observed.original.resolved.1.requestPrimitives data observed.readings parentSheet target positive},
  {value : observed.original.resolved.2.PrimitiveRequests data observed.readings parentSheet target positive //
    value = observed.original.resolved.2.requestPrimitives data observed.readings parentSheet target positive})

/-- Acquire analytic requests from the actual retained resolved source slots, without resolving either cut again. -/
def requestSources (parentSheet : Fin 2) (target : Rational) (positive : 0 < target) :
    observed.SourceRequests parentSheet target positive :=
  let leading := observed.original.resolved.1.requestPrimitives data observed.readings parentSheet target positive
  let trailing := observed.original.resolved.2.requestPrimitives data observed.readings parentSheet target positive
  (⟨observed, rfl⟩, ⟨⟨leading, rfl⟩, ⟨trailing, rfl⟩⟩)

end SourceBank.PrimitiveReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

end
