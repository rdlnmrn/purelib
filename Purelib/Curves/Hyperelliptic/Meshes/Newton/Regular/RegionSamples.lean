module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.AreaRequest
public import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Cached requests and numerical receipts for the original compiler's
regular regions. Each cut pairing and offset readback is materialized once. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionSamples

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- The retained regular occurrence word is exactly its original face boundary subdivided on the current grid and
arriving sheet. -/
private theorem occurrence_word
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
/-- An area request tied to the original compiler's retained regular occurrence.

The original region, both cut words and their paid sewing request retain that occurrence's actual face and current
lifted grid. -/
structure RegularRegionRequest
    (occurrence :
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (floor : Nat) where
  /-- The original regular face region on the current Newton grid. -/ region :
    RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces grid occurrence.location.face
  /-- The original two cut boundary words for that retained face. -/ words :
    Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords occurrence.location.face current
  /-- The paid original regular-region area request. -/ request :
    AreaRequest words fixed error floor

constructive_injectivity RegularRegionRequest

namespace RegularRegionRequest

variable {occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices}
  {fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {error :
    Fraction.Rational} {floor : Nat}

/-- Prepare the original retained regular face region and its two cut words with a paid area request. -/
def build (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest occurrence fixed error floor :=
  let region := RootContinuation.NewtonOriginalRegularFaces.OriginalRegularFaces.build grid occurrence.location.face
  let words := Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords.build occurrence.location.face current
  ⟨region, words, AreaRequest.build words fixed error positive floor⟩

set_option genInjectivity false in
/-- The cached numerical receipt for one original regular-region request.

It retains the actual cut balance, complete pairing, both sheet readbacks and the original occurrence polygon. -/
structure Sample (prepared : Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest occurrence fixed
  error floor)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
    (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) where
  /-- The original cut balance on the supplied shared sewn sample. -/ balance :
    CutBalance prepared.region prepared.words surface
  /-- The complete original cut pairing evaluated on the sample's energy values. -/ pairing :
    Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample balance.complete.pairing
    surface.energyValues
  /-- The original sheet-zero cut-word area readback. -/ zero :
    Branches.NewtonCutPrimitiveArea.CutSourceWord.AreaReadback prepared.words.zero surface.sewn.values
  /-- The original sheet-one cut-word area readback. -/ one : Branches.NewtonCutPrimitiveArea.CutSourceWord.AreaReadback
    prepared.words.one surface.sewn.values
  /-- The cached area of the retained original occurrence word. -/ polygon : Gaussian.Basic.Canonical
  /-- The polygon uses exactly the original occurrence word and supplied canonical edge readings. -/ polygon_eq :
    polygon = Topology.Mesh.RetracingWords.wordArea
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values) occurrence.word

constructive_injectivity Sample

namespace Sample

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest occurrence
  fixed error floor}
  {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
    domains} {readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
    current.mesh}
  {surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values}

/-- Cache the original cut balance, pairing, sheet readbacks and occurrence polygon from the supplied shared numerical
sample. -/
def build (prepared : Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest occurrence fixed error
  floor)
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) :
    prepared.Sample readings surface :=
  let balance := CutBalance.build prepared.region prepared.words surface
  ⟨balance, Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample.build balance.complete.pairing
    surface.energyValues,
    Branches.NewtonCutPrimitiveArea.CutSourceWord.AreaReadback.build prepared.words.zero surface.sewn.values,
    Branches.NewtonCutPrimitiveArea.CutSourceWord.AreaReadback.build prepared.words.one surface.sewn.values,
    Topology.Mesh.RetracingWords.wordArea (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      current.mesh readings.values) occurrence.word, rfl⟩

/-- The complete original jump, defect and two sheet-offset correction. -/
def correction (sample : prepared.Sample readings surface) : Gaussian :=
  sample.pairing.jumpSum + sample.pairing.defectSum + sample.zero.correction + sample.one.correction

/-- The original selected region area after its complete retained correction. -/
def corrected (sample : prepared.Sample readings surface) : Gaussian := sample.balance.selected.area - sample.correction

/-- The corrected original region area minus twice its retained occurrence polygon. -/
def residual (sample : prepared.Sample readings surface) : Gaussian := sample.corrected - (sample.polygon +
  sample.polygon)

/-- Above the retained sufficient stage, the original corrected area residual meets the requested bound. -/
theorem accurate (sample : prepared.Sample readings surface) (later : prepared.request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq sample.residual ≤ error := by
  have estimate := prepared.request.accurate occurrence.sheet readings surface sample.balance sample.pairing sample.zero
    sample.one later
  have polygonEqual := sample.polygon_eq.trans (congrArg
    (Topology.Mesh.RetracingWords.wordArea (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
      current.mesh readings.values)) (Hyperelliptic.Meshes.Newton.Regular.RegionSamples.occurrence_word occurrence))
  have correctedEqual : sample.corrected = sample.balance.selected.area - sample.pairing.jumpSum -
    sample.pairing.defectSum -
      sample.zero.correction - sample.one.correction := by
    unfold
      Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest.Sample.corrected
      Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest.Sample.correction; ring1
  exact (congrArg₂ (fun value polygon => Data.Gaussian.Norm.Basic.normSq (value - (polygon + polygon)))
    correctedEqual polygonEqual).trans_le estimate

/-- Read another retained selection with the same certified cell mask;
the theorem equates cached scalars without running either producer again. -/
theorem selected_area (sample : prepared.Sample readings surface)
    (selected : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current occurrence.cell)) :
    sample.balance.selected.area = selected.area := by
  have equal : occurrence.location.face.cell = occurrence.cell := occurrence.location.cell_eq
  let own : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
    (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current occurrence.location.face.cell)
    := sample.balance.selected
  have compare (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve))
      (left right : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
        (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)) : left.area =
        right.area :=
    left.area_readback.trans right.area_readback.symm
  have transported {first last : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient
    curve)} (same : first = last)
      (value : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
        (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current first)) :
      (same ▸ value : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
        (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current last)).area = value.area :=
        by
    cases same
    rfl
  exact (transported equal own).symm.trans (compare occurrence.cell (equal ▸ own) selected)

end Sample
end RegularRegionRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionSamples
