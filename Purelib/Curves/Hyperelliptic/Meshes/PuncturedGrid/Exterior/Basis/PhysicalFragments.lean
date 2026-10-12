module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularSegmentRefinement
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
public import Purelib.Geometry.Rectangle.SourceIntervals
public import Purelib.Riemann.Paths.RectangularTraceParameterReadings
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Consume retained physical traces as common-basis source fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (OwnedReadings
  ownedValue)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover sourceData}
  {covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
  faceIndex}

namespace OwnedFragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest
/-- Transport the parameter coordinates only. Every basis-row point owner,
reading and the supplied area sample is retained from the physical trace. -/
def ofTrace (member : parent ∈ occurrence.compared.entered.cache.parents)
    {cuts : Paths.RectangularSegmentSplitting.GridCuts occurrence.compared.entered.domain.geometry}
    {split : Paths.RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1)}
    {interval : Rectangle.Partition.PreparedAxisPartitions.Interval} (located :
      Paths.RectangularSegmentRefinement.Subinterval split interval)
    {leftColumns leftRows rightColumns rightRows vertices : Nat}
    {leftGeometry : Normalization.RectangularInverseModels.Geometry leftColumns leftRows}
    {rightGeometry : Normalization.RectangularInverseModels.Geometry rightColumns rightRows}
    {physical : Paths.RectangularPairedSegments.PairedSegmentPiece leftGeometry rightGeometry}
    {trace : Integration.RectangularPairedPointBanks.Trace physical vertices}
    (forward : Bool)
    (transport : Paths.RectangularTraceParameterReadings.ParentParameters trace parent
      (if forward then interval.lower else interval.upper) (if forward then interval.upper else interval.lower))
    (increasing : ∀ edge : Fin vertices, trace.parameters edge.castSucc ≤ trace.parameters edge.succ)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget vertices
      allowance)
    (owners : OwnerRequest occurrence budget.tolerance)
      (later : owners.index ≤ faceIndex)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun vertex =>
      trace.points vertex))
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (transport.parameters vertex),
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (transport.parameters vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data :=
  { member := member, piece := located.piece, vertices := vertices, parameters := transport.parameters
    inside := by
      intro vertex
      apply located.contains
      cases forward with
      | true => exact transport.inside interval.ordered.le vertex
      | false => exact transport.inside_reverse interval.ordered.le vertex
    forward := forward
    ordered := by
      cases forward with
      | true => exact transport.ordered interval.ordered.le increasing
      | false => exact transport.ordered_reverse interval.ordered.le increasing
    allowance := allowance, budget := budget, owners := owners, later := later
    readings := fun row => transport.readings (readings row)
    owned := owned, source := source }

/-- Locate a mesh interval in the retained source split, with no primitive
reacquisition and no numerical search for an adequate error. -/
def ofMesh (member : parent ∈ occurrence.compared.entered.cache.parents)
    {cuts : Paths.RectangularSegmentSplitting.GridCuts occurrence.compared.entered.domain.geometry}
    (split : Paths.RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1))
    {meshBox : Rational.Box} (mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts meshBox)
    (retained : ∀ point ∈ split.points, point ∈ mesh.points)
    (vertical : Bool) (physical : Rectangle.Partition.PreparedAxisPartitions.Interval) (present : physical ∈
      Rectangle.SourceIntervals.axisIntervals mesh vertical)
    (interval : Rectangle.Partition.PreparedAxisPartitions.Interval) (within : 0 ≤ interval.lower ∧ interval.upper ≤ 1)
    (correspondence : Rectangle.SourceIntervals.AxisCorrespondence vertical
      (parent.edge.point 0) (parent.edge.point 1) interval physical)
    {vertices : Nat} (parameters : Fin (vertices + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, interval.lower ≤ parameters vertex ∧ parameters vertex ≤ interval.upper)
    (ordered : ∀ edge : Fin vertices, parameters edge.castSucc ≤ parameters edge.succ)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget vertices
      allowance)
    (owners : OwnerRequest occurrence budget.tolerance)
      (later : owners.index ≤ faceIndex)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun vertex =>
      parent.edge.point (parameters vertex)))
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters vertex),
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients (parameters vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data :=
  let located := Rectangle.SourceIntervals.locateSourceInterval mesh split retained vertical physical present interval
    within correspondence
  { member := member, piece := located.piece, vertices := vertices, parameters := parameters
    inside := fun vertex => located.contains (inside vertex)
    forward := true, ordered := ordered, allowance := allowance, budget := budget, owners := owners, later := later
    readings := readings, owned := owned, source := source }

/-- Keep both point owners at a coincident-coordinate junction, including
its actual nonzero numerical increment. -/
def atJunction (member : parent ∈ occurrence.compared.entered.cache.parents)
    {cuts : Paths.RectangularSegmentSplitting.GridCuts occurrence.compared.entered.domain.geometry}
    (split : Paths.RectangularSegmentSplitting.SegmentSplit cuts (parent.edge.point 0) (parent.edge.point 1))
    (parameter : Normalization.InverseRootPolynomial.Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget 1
      allowance)
    (owners : OwnerRequest occurrence budget.tolerance)
      (later : owners.index ≤ faceIndex)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest.OwnedReadings data (fun _ : Fin 2 =>
      parent.edge.point parameter))
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨ownedValue readings coefficients vertex, ownedValue readings coefficients vertex⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun _ : Fin 2 => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients parameter,
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveReadback.BasisSourceLocations.PrimitiveBank.value
        originals coefficients parameter⟩ : Topology.Polygon.Stokes.PrimitivePoint))) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data :=
  let located := Paths.RectangularSegmentSplitting.SegmentSplit.locate split parameter inside
  { member := member, piece := located.piece, vertices := 1, parameters := fun _ => parameter
    inside := fun _ => located.inside, forward := true, ordered := fun _ => le_rfl
    allowance := allowance, budget := budget, owners := owners, later := later
    readings := readings, owned := owned, source := source }

end OwnedFragment
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
