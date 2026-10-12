module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Integration.Surface.Sewn.Selection.Paired
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Riemann.RootContinuation.NewtonOriginalPairedPartition
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

open Purelib

public section

/-! Paired regular-region receipts for the literal occurrences of the
original exterior compiler, with cached cut corrections and polygon area. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularSamples

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion (PairedRegionRequest PairedRegionSample
  pairedValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- The original regular occurrence word is its retained subdivided face boundary on the actual arriving sheet. -/
private theorem paired_occurrence_word
    (occurrence :
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices) :
    occurrence.word = current.edges.indexedEdges current.vertices
      (grid.shrunk.included.resplit occurrence.location.face.boundary
        (occurrence.location.face.cell.anchor_mem occurrence.location.face.member)) occurrence.sheet := by
  rcases occurrence with ⟨cell, member, ⟨index, face, indexed, equal⟩, sheet, word, wordEqual⟩
  cases equal
  exact wordEqual

set_option genInjectivity false in
/-- A paid paired-area request tied to an original retained regular occurrence.

It retains the original region and cut words, together with both differential magnitude banks. -/
structure PairedRegularRequest
    (occurrence :
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)
    (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
    (error : Fraction.Rational) (floor : Nat) where
  /-- The original regular face region on the current Newton grid. -/ region :
    RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid occurrence.location.face
  /-- The original two cut words of the retained regular face. -/ words :
    Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords occurrence.location.face current
  /-- The paid paired-region request on those exact words and differential banks. -/ request :
    Hyperelliptic.Meshes.Newton.Regular.PairedRegion.PairedRegionRequest words leftFixed rightFixed error floor

constructive_injectivity PairedRegularRequest

namespace PairedRegularRequest

variable {occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices}
  {leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
    {rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
  {error : Fraction.Rational} {floor : Nat}

/-- Prepare the retained original regular region and its paired-area request at the supplied target and floor. -/
@[expose] def build (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)
    (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
      Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence leftFixed rightFixed error floor
      :=
  let region := RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces.build grid occurrence.location.face
  let words := Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords.build occurrence.location.face current
  ⟨region, words, Hyperelliptic.Meshes.Newton.Regular.PairedRegion.PairedRegionRequest.build words leftFixed rightFixed
    error positive floor⟩

set_option genInjectivity false in
/-- The actual paired regular-region receipt on the supplied shared numerical and sewn samples.

Its cached polygon uses the exact original occurrence word and both original differential readings. -/
structure Sample (prepared : Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence leftFixed
  rightFixed error floor)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      rightDifferential stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values) where
  /-- The original paired cut sample and all its retained corrections. -/ cut :
    Hyperelliptic.Meshes.Newton.Regular.PairedRegion.PairedRegionSample prepared.region prepared.words leftSurface
    rightSurface
  /-- The cached actual paired occurrence polygon. -/ polygon : Gaussian.Basic.Canonical
  /-- The polygon is the paired area of the original occurrence word with the supplied canonical readings. -/ polygon_eq
    : polygon = Path.PairedIncrementArea.area (occurrence.word.map (fun edge =>
    (⟨edgeValuation current.mesh leftReadings.values edge,
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))

constructive_injectivity Sample

namespace Sample

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence
  leftFixed rightFixed error floor}
  {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
    stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    rightDifferential stage domains}
  {leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh}
    {rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
    current.mesh}
  {leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values}
    {rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
    rightReadings.values}

/-- Cache the original paired cut sample and occurrence polygon from the supplied shared readings and sewn surfaces. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence
  leftFixed rightFixed error floor)
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values) :
    Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest.Sample prepared leftReadings rightReadings
      leftSurface rightSurface :=
  ⟨PairedRegionSample.build prepared.region prepared.words leftSurface rightSurface,
    Path.PairedIncrementArea.area (occurrence.word.map (fun edge =>
      (⟨edgeValuation current.mesh leftReadings.values edge,
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))), rfl⟩

/-- The corrected original paired region area minus twice its retained occurrence polygon. -/
@[expose] def residual (sample : Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest.Sample prepared
  leftReadings rightReadings leftSurface rightSurface) : Gaussian :=
  sample.cut.area - sample.cut.correction - (sample.polygon + sample.polygon)

/-- The retained original paired-area residual meets the requested bound above its sufficient stage. -/
theorem accurate (sample : Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest.Sample prepared
  leftReadings rightReadings leftSurface rightSurface)
    (later : prepared.request.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq sample.residual ≤ error := by
  unfold Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest.Sample.residual
  rw [sample.polygon_eq, Hyperelliptic.Meshes.Newton.PairedRegularSamples.paired_occurrence_word]
  exact Hyperelliptic.Meshes.Newton.Regular.PairedRegion.PairedRegionRequest.accurate prepared.request occurrence.sheet
    leftReadings rightReadings leftSurface rightSurface sample.cut later

/-- Transport only the cell label; the actual retained selection and paired
primitive values are unchanged. -/
theorem selected_area (sample : Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest.Sample prepared
  leftReadings rightReadings leftSurface rightSurface)
    (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current occurrence.cell)) :
    sample.cut.area = Topology.Polygon.Stokes.edgeListArea
      (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface rightSurface)
      (selected.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary) := open Purelib.Polynomial in by
  let primitive := Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface rightSurface
  have equal : occurrence.location.face.cell = occurrence.cell := occurrence.location.cell_eq
  let own : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
    (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current occurrence.location.face.cell)
    := sample.cut.balance.selected
  have compare (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))
      (left right : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
        (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)) :
      Topology.Polygon.Stokes.edgeListArea primitive (left.triangles.flatMap
        Topology.Polygon.Stokes.OrientedTriangle.boundary) =
        Topology.Polygon.Stokes.edgeListArea primitive (right.triangles.flatMap
          Topology.Polygon.Stokes.OrientedTriangle.boundary) :=
    (Surface.Sewn.Selection.Paired.paired_area_readback left primitive).trans
      (Surface.Sewn.Selection.Paired.paired_area_readback right primitive).symm
  have transported {first last : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
    curve)} (same : first = last)
      (value : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
        (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current first)) :
      Topology.Polygon.Stokes.edgeListArea primitive ((same ▸ value :
        Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
        (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current last)).triangles.flatMap
        Topology.Polygon.Stokes.OrientedTriangle.boundary) =
        Topology.Polygon.Stokes.edgeListArea primitive (value.triangles.flatMap
          Topology.Polygon.Stokes.OrientedTriangle.boundary) := by
    cases same
    rfl
  exact sample.cut.area_eq.trans ((transported equal own).symm.trans (compare occurrence.cell (equal ▸ own) selected))

end Sample
end PairedRegularRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularSamples
