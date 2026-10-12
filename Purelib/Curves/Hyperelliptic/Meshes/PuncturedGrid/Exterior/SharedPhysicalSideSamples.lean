module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalReadingSample
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SharedPointReadings
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalReadingSample

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

@[expose] public section

/-! Read physical sides directly from the shared face bank, preserving cached values through domain transport. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {data : FirstData occurrence
  index} {otherData : SecondData
  occurrence other index}

open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)

namespace SharedPhysicalSide

/-- Read the original first-differential face data using its retained occurrence-domain alignment. -/
def firstData (firstBank : PrimitiveData.FacePrimitiveBank differential index domains) : PairedFragmentValues.FirstData
  occurrence index :=
  occurrence.compared.sharedData firstBank occurrence.aligned

/-- Read the original second-differential face data using its retained recast occurrence alignment. -/
def secondData (secondBank : PrimitiveData.FacePrimitiveBank other index domains) : PairedFragmentValues.SecondData
  occurrence other index :=
  (occurrence.recastComparison other).sharedData secondBank (occurrence.recastComparison_aligned other)

end SharedPhysicalSide

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
variable {cuts : GridCuts ((domains.get
  occurrence.sideOccurrence.position).domain occurrence.sideOccurrence.sheet).geometry}
  {meshBox : Purelib.Geometry.Rational.Box} {mesh :
    ObservationMesh cuts meshBox} {depth : Nat}

namespace SharedPhysicalHorizontalReadings
variable {firstRow secondRow : Fin mesh.partition.y.intervals.length}
  {height : Coordinate} {side :
    MatchedHorizontalSide mesh mesh firstRow
    secondRow height}

/-- Read the first differential's original cached aligned primitive value at the retained side-piece vertex. -/
def firstValue (trace : side.Trace depth) (firstBank : PrimitiveData.FacePrimitiveBank differential index domains)
    (vertex : side.Vertex depth) : Gaussian :=
  let cached := (firstBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  cached.anchors.alignedValue cached.offsets (side.pieces vertex.1).leftColumn
    (side.pieces vertex.1).leftRow (trace.point vertex)

/-- Read the second differential's original cached aligned primitive value at the same retained side-piece vertex. -/
def secondValue (trace : side.Trace depth) (secondBank : PrimitiveData.FacePrimitiveBank other index domains)
    (vertex : side.Vertex depth) : Gaussian :=
  let cached := (secondBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  cached.anchors.alignedValue cached.offsets (side.pieces vertex.1).leftColumn
    (side.pieces vertex.1).leftRow (trace.point vertex)

/-- A conjugate physical sample on the original horizontal side retaining both shared face-bank value readbacks. -/
def Data (trace : side.Trace depth) (firstBank : PrimitiveData.FacePrimitiveBank differential index domains)
    (secondBank : PrimitiveData.FacePrimitiveBank other index domains) :=
  PhysicalReadingSample (occurrence := occurrence)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples.SharedPhysicalSide.firstData
      (occurrence := occurrence) firstBank)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples.SharedPhysicalSide.secondData
      (occurrence := occurrence) secondBank)
    (fun vertex => trace.point (trace.vertices.indexed vertex))
    (fun vertex => ⟨firstValue trace firstBank (trace.vertices.indexed vertex),

        secondValue
        trace secondBank (trace.vertices.indexed vertex)⟩)

/-- Read and transport both original shared horizontal side banks, preserving their cached values when constructing the
conjugate centered sample. -/
def build (trace : side.Trace depth) (firstBank : PrimitiveData.FacePrimitiveBank differential index domains)
    (secondBank : PrimitiveData.FacePrimitiveBank other index domains) :
      Data
      trace firstBank secondBank := by
  let firstCached := (firstBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  let secondCached := (secondBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  let originalFirst := trace.leftReadings firstCached.anchors firstCached.offsets
  let originalSecond := trace.leftReadings secondCached.anchors secondCached.offsets
  let first := occurrence.compared.sharedReadings firstBank occurrence.aligned originalFirst
  let second := (occurrence.recastComparison other).sharedReadings secondBank
    (occurrence.recastComparison_aligned other) originalSecond
  apply PhysicalReadingSample.build first.val second.val
  · intro vertex
    exact (congrArg (fun values => values vertex) first.property).trans
      (trace.leftReadings_value firstCached.anchors firstCached.offsets vertex)
  · intro vertex
    exact (congrArg (fun values => values vertex) second.property).trans
      (trace.leftReadings_value secondCached.anchors secondCached.offsets vertex)

end SharedPhysicalHorizontalReadings

namespace SharedPhysicalVerticalReadings
variable {firstColumn secondColumn : Fin mesh.partition.x.intervals.length}
  {horizontal : Coordinate} {side :
    MatchedVerticalSide mesh mesh
    firstColumn secondColumn horizontal}

/-- Read the first differential's original cached aligned primitive value at the retained side-piece vertex. -/
def firstValue (trace : side.Trace depth) (firstBank : PrimitiveData.FacePrimitiveBank differential index domains)
    (vertex : side.Vertex depth) : Gaussian :=
  let cached := (firstBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  cached.anchors.alignedValue cached.offsets (side.pieces vertex.1).leftColumn
    (side.pieces vertex.1).leftRow (trace.point vertex)

/-- Read the second differential's original cached aligned primitive value at the same retained side-piece vertex. -/
def secondValue (trace : side.Trace depth) (secondBank : PrimitiveData.FacePrimitiveBank other index domains)
    (vertex : side.Vertex depth) : Gaussian :=
  let cached := (secondBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  cached.anchors.alignedValue cached.offsets (side.pieces vertex.1).leftColumn
    (side.pieces vertex.1).leftRow (trace.point vertex)

/-- A conjugate physical sample on the original vertical side retaining both shared face-bank value readbacks. -/
def Data (trace : side.Trace depth) (firstBank : PrimitiveData.FacePrimitiveBank differential index domains)
    (secondBank : PrimitiveData.FacePrimitiveBank other index domains) :=
  PhysicalReadingSample (occurrence := occurrence)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples.SharedPhysicalSide.firstData
      (occurrence := occurrence) firstBank)
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples.SharedPhysicalSide.secondData
      (occurrence := occurrence) secondBank)
    (fun vertex => trace.point (trace.vertices.indexed vertex))
    (fun vertex => ⟨firstValue trace firstBank (trace.vertices.indexed vertex),

        secondValue
        trace secondBank (trace.vertices.indexed vertex)⟩)

/-- Read and transport both original shared vertical side banks, preserving their cached values when constructing the
conjugate centered sample. -/
def build (trace : side.Trace depth) (firstBank : PrimitiveData.FacePrimitiveBank differential index domains)
    (secondBank : PrimitiveData.FacePrimitiveBank other index domains) :
      Data
      trace firstBank secondBank := by
  let firstCached := (firstBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  let secondCached := (secondBank.get occurrence.sideOccurrence.position).atSheet occurrence.sideOccurrence.sheet
  let originalFirst := trace.leftReadings firstCached.anchors firstCached.offsets
  let originalSecond := trace.leftReadings secondCached.anchors secondCached.offsets
  let first := occurrence.compared.sharedReadings firstBank occurrence.aligned originalFirst
  let second := (occurrence.recastComparison other).sharedReadings secondBank
    (occurrence.recastComparison_aligned other) originalSecond
  apply PhysicalReadingSample.build first.val second.val
  · intro vertex
    exact (congrArg (fun values => values vertex) first.property).trans
      (trace.leftReadings_value firstCached.anchors firstCached.offsets vertex)
  · intro vertex
    exact (congrArg (fun values => values vertex) second.property).trans
      (trace.leftReadings_value secondCached.anchors secondCached.offsets vertex)

end SharedPhysicalVerticalReadings

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SharedPhysicalSideSamples
