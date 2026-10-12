module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
public import Purelib.Riemann.Integration.PreparedParentCacheRecasting
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonBlockArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonSignChain
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

/-! The second differential on an exterior occurrence consumes the first
occurrence's actual covered segment and parent geometry. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}

namespace AllSurfacePreparation

/-- Every retained exterior occurrence has both endpoints on the same original ambient rectangle side. -/
theorem occurrence_sameSide (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (occurrence :
      SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences) :
    Paths.PreparedBoundarySegments.SameSide (Hyperelliptic.Branches.Cuts.Ambient curve) occurrence.start
      occurrence.finish := open Purelib in by
  rw [prepared.occurrences_eq] at member
  obtain ⟨component, _, retained⟩ := Data.List.Flatten.mem_flatMap.mp member
  have indexed : occurrence.placement.indexed ∈ component.program.indexed :=
    component.prepared.occurrences_eq ▸ Data.List.Map.mem_map_of_mem retained
  have side := component.program.indexed_sameSide occurrence.placement.indexed indexed
  rw [occurrence.placement.start_eq, occurrence.placement.finish_eq] at side
  exact side

end AllSurfacePreparation
namespace SurfaceOccurrence

/-- Reuse the entry, domain and covered segment of the existing occurrence.
The second numerator gets its own fragment bounds and coefficient centers. -/
@[expose] def recastComparison (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (target : Hyperelliptic.Differentials.Basic.Differential genus) :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison occurrence.placement
      occurrence.piece target 0 :=
  let entered := Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath.ofEntry
    occurrence.compared.entered.entry occurrence.compared.entered.domain
    occurrence.piece.path occurrence.placement.inside target 0
    (Integration.PreparedParentCacheRecasting.recast occurrence.compared.entered.cache target)
  ⟨occurrence.compared.domains, entered, occurrence.compared.domain_eq, occurrence.compared.sheet_eq⟩

/-- Recasting the differential preserves the original retained route-domain alignment. -/
theorem recastComparison_aligned (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (target : Hyperelliptic.Differentials.Basic.Differential genus) :
    (occurrence.recastComparison target).domains = domains.atRoute occurrence.placement.location := occurrence.aligned

/-- The recast comparison's parents are exactly the original cached parents with their differential recast. -/
theorem recastComparison_parents (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (target : Hyperelliptic.Differentials.Basic.Differential genus) :
    (occurrence.recastComparison target).entered.cache.parents =
      occurrence.compared.entered.cache.parents.map (Integration.PreparedEdgeRecasting.recastCenteredEdge target) := rfl

/-- The new cap preparation retains exactly the original source segment,
root owner, sheet domain and parent subdivision under differential recasting. -/
@[expose] def pairedCap (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    (target : Hyperelliptic.Differentials.Basic.Differential genus) :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular
      (occurrence.recastComparison target) :=
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation.build regular
    (occurrence.recastComparison target)
    (prepared.occurrence_sameSide occurrence member)

/-- Request the second differential on that retained preparation. This can
be combined with an already acquired first-differential cap request. -/
@[expose] def pairedRequest (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    (target : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance areaTarget : Fraction.Rational)
    (positive : 0 < tolerance) (areaPositive : 0 < areaTarget) (floor : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest (occurrence.pairedCap
      prepared member target) tolerance areaTarget floor :=
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.build
    (occurrence.pairedCap prepared member target)
    tolerance areaTarget positive areaPositive floor

/-- Count-paid full bilinear area on the original occurrence and its recast
differential, including the polygon of parent totals. Each parent retains
both independently acquired covers. -/
@[expose] def pairedAreaRequest (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    (target : Hyperelliptic.Differentials.Basic.Differential genus) (tolerance : Fraction.Rational) (positive : 0 <
      tolerance) (floor : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular target
      occurrence.compared.entered.cache.parents tolerance floor :=
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.build regular target
    occurrence.cap.path.covers (occurrence.pairedCap prepared member target).path.covers
    occurrence.cap.path.proper
    tolerance positive floor

/-- Every paired parent on this occurrence uses the same sheet bit. The
actual cached path and its root chain discharge all cross-parent joins. -/
theorem paired_area_signs (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    {target : Hyperelliptic.Differentials.Basic.Differential genus} {tolerance : Fraction.Rational} {floor stage fine :
      Nat}
    {box otherBox : Rational.Box}
    {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular target
      occurrence.compared.entered.cache.parents tolerance floor}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target stage otherBox}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample
      fine) :
    ∀ entry ∈ evaluated.retained, entry.certified.shared.flip =
      Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.firstFlip evaluated.retained :=
  evaluated.shared_signs
    (by obtain ⟨chain⟩ := occurrence.compared.entered.cache.chain; exact ⟨chain.toDirectPathChain⟩)
  (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain occurrence.compared.entered.cache)

/-- The cached unsigned cap-total polygon equals the polygon of complete retained paired cap-path totals.

The original path and root chain supply common signs across every retained parent. -/
theorem paired_cap_polygon (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    {target : Hyperelliptic.Differentials.Basic.Differential genus} {tolerance : Fraction.Rational} {floor stage fine :
      Nat}
    {box otherBox : Rational.Box}
    {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular target
      occurrence.compared.entered.cache.parents tolerance floor}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target stage otherBox}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample
      fine) :
    Path.PairedIncrementArea.area (evaluated.retained.map (fun entry =>
      entry.certified.compared.secondSummary.totalValue)) =
      Path.PairedIncrementArea.area ((evaluated.pairs.map Prod.snd).map Path.PairedIncrementArea.total) :=
  evaluated.cap_polygon_unsigned
    (by obtain ⟨chain⟩ := occurrence.compared.entered.cache.chain; exact ⟨chain.toDirectPathChain⟩)
    (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain occurrence.compared.entered.cache)

/-- The occurrence's actual path and root chain close the full area budget;
no parent-total polygon correction is subtracted from the result. -/
theorem paired_area_error (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    {target : Hyperelliptic.Differentials.Basic.Differential genus} {tolerance : Fraction.Rational} {floor stage fine :
      Nat}
    {box otherBox : Rational.Box}
    {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular target
      occurrence.compared.entered.cache.parents tolerance floor}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target stage otherBox}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample
      fine) :
    evaluated.FullAreaError :=
  evaluated.full_area_error
    (by obtain ⟨chain⟩ := occurrence.compared.entered.cache.chain; exact ⟨chain.toDirectPathChain⟩)
    (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain occurrence.compared.entered.cache)

/-- The second evaluation reads the original occurrence's triangle edge on
its supplied shared bank; the cap's complete path total is retained. -/
theorem paired_triangle_error (prepared :
  AllSurfacePreparation
  regular domains differential)
    (occurrence :
      ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    {target : Hyperelliptic.Differentials.Basic.Differential genus} {tolerance areaTarget : Fraction.Rational} {floor :
      Nat}
    {allocated : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
      (occurrence.pairedCap prepared member target) tolerance areaTarget floor}
    {stage depth readingIndex : Nat} {box : Rational.Box}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target stage box}
    (evaluated :
      Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation allocated
      sample depth readingIndex)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank target stage domains} (readings :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
    (later : allocated.budget.grid.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (occurrence.placement.location.sourceEdge.increment readings.values - evaluated.right.total) < tolerance :=
  evaluated.triangle_error (occurrence.recastComparison_aligned target) later readings

/-- Endpoint coordinates, sheet labels and actual parent root names match
on the entire original subdivision, not merely on the triangle source. -/
theorem paired_parent_geometry (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential) (target : Hyperelliptic.Differentials.Basic.Differential genus) :
    (occurrence.recastComparison target).entered.cache.parents.map (fun parent =>
      (parent.edge.point 0, parent.edge.point 1, parent.edge.sheet, Paths.OwnerTraceReadings.ownerName
        parent.edge.owner)) =
    occurrence.compared.entered.cache.parents.map (fun parent =>
      (parent.edge.point 0, parent.edge.point 1, parent.edge.sheet, Paths.OwnerTraceReadings.ownerName
        parent.edge.owner)) :=
  Integration.PreparedParentCacheRecasting.recast_geometry occurrence.compared.entered.cache target

end SurfaceOccurrence
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
