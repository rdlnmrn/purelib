module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Integration.Surface.Sewn.Selection.Paired
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
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

/-! Actual compiler occurrences retain conjugate area receipts and their
original cut corrections on the common sewn pair. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularSamples

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion (ConjugateRegionSample)

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- The original regular occurrence word is exactly its subdivided face boundary on the retained arriving sheet. -/
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

namespace PairedRegularRequest

variable {occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices}
  {leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
    {rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
  {error : Fraction.Rational} {floor : Nat}
set_option genInjectivity false in
/-- The actual conjugate receipt for an original paired regular-region request.

It retains the original conjugate cut sample and the cached occurrence polygon on the same numerical readings and sewn
conjugate pair. -/
structure ConjugateSample (prepared : Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence
  leftFixed rightFixed error floor)
    {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
      stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      rightDifferential stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface) where
  /-- The original conjugate region sample with all retained cut corrections. -/ cut :
    Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion.ConjugateRegionSample prepared.region prepared.words leftSurface
    rightSurface pair
  /-- The cached actual conjugate occurrence polygon. -/ polygon : Gaussian.Basic.Canonical
  /-- The polygon uses the original occurrence word, conjugated left readings and actual right readings. -/ polygon_eq :
    polygon = Path.PairedIncrementArea.area (occurrence.word.map (fun edge =>
    (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
      leftReadings.values edge),
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)))

constructive_injectivity ConjugateSample

namespace ConjugateSample

variable {prepared : Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence leftFixed
  rightFixed error floor}
  {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential
    stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    rightDifferential stage domains}
  {leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh}
    {rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
    current.mesh}
  {leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values}
    {rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
    rightReadings.values}
  {pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface}

/-- Cache the original conjugate cut sample and occurrence polygon from the supplied shared readings and sewn pair. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence
  leftFixed rightFixed error floor)
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh)
    (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface) :
    Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.PairedRegularRequest.ConjugateSample prepared leftReadings
      rightReadings leftSurface rightSurface pair :=
  ⟨ConjugateRegionSample.build prepared.region prepared.words leftSurface rightSurface pair,
    Path.PairedIncrementArea.area (occurrence.word.map (fun edge =>
      (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
        leftReadings.values edge),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))), rfl⟩

/-- The corrected original conjugate region area minus twice its retained occurrence polygon. -/
@[expose] def residual (sample :
  Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.PairedRegularRequest.ConjugateSample prepared leftReadings
  rightReadings leftSurface rightSurface pair) : Gaussian :=
  sample.cut.area - sample.cut.correction - (sample.polygon + sample.polygon)

/-- The retained original conjugate residual meets the requested bound at every sufficient shared stage. -/
theorem accurate (sample : Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.PairedRegularRequest.ConjugateSample
  prepared leftReadings rightReadings leftSurface rightSurface pair)
    (later : prepared.request.index ≤ stage) : Data.Gaussian.Norm.Basic.normSq sample.residual ≤ error := by
  unfold Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.PairedRegularRequest.ConjugateSample.residual
  rw [sample.polygon_eq, Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.paired_occurrence_word]
  exact Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion.PairedRegionRequest.conjugate_accurate prepared.request
    occurrence.sheet leftReadings rightReadings leftSurface rightSurface pair sample.cut later

/-- Transport only the cell label; the actual retained selection and paired
primitive values are unchanged. -/
theorem selected_area (sample : Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.PairedRegularRequest.ConjugateSample
  prepared leftReadings rightReadings leftSurface rightSurface pair)
    (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current occurrence.cell)) :
    sample.cut.area = Topology.Polygon.Stokes.edgeListArea pair.values
      (selected.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary) := open Purelib.Polynomial in by
  let primitive := pair.values
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

end ConjugateSample
end PairedRegularRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularSamples
