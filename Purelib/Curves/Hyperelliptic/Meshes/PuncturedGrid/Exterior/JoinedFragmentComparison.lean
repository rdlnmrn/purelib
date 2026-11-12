module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.MatchedSourceJunctions
public import Purelib.Integration.Polynomial.Rectangle.SampleReadback
public import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.Paths.RectangularMatchedSideTrace
public import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Integration.Polynomial.Rectangle

open Purelib.Integration.Path.CenteredPathIncrements

public section

/-! The complete joined comparison consumes value-certified cached fragment
samples. Piece and junction order is structural; the block-total polygon is
retained in the existing full-path error bound. -/
section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : InverseRootPolynomial.Coordinate} {minimum stage fine index :
    Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}
  {evaluated : PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan
    sample otherSample fine}
  {data : PairedFragmentValues.FirstData occurrence index} {otherData :
    PairedFragmentValues.SecondData occurrence other index}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison

set_option genInjectivity false in
/-- A retained owned fragment with an exact sample readback on the supplied vertex values.

Equality of the cached increment lists preserves the original fragment's complete path data. -/
structure SampledFragment {count : Nat} (values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint) where
  /-- The original retained owned fragment. -/ fragment :
    PairedFragmentBlocks.OwnedFragment evaluated data otherData
  /-- The retained centered sample of the supplied vertex values. -/ reading : Periods.CenteredBilinearPath.Sample
    values
  /-- The sample's cached increments are exactly the original fragment's owned increments. -/ increments_eq :
    Sample.increments reading = Sample.increments fragment.owned

constructive_injectivity SampledFragment

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment

/-- Exact increment readback preserves the original fragment's centered area. -/
theorem reading_area {count : Nat} {values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint}
    (certified : SampledFragment (evaluated :=
      evaluated) (data := data) (otherData := otherData) values) :
    certified.reading.centeredArea = certified.fragment.owned.centeredArea :=
  (Sample.increments_area certified.reading).symm.trans
    ((congrArg Path.PairedIncrementArea.area certified.increments_eq).trans
      (Sample.increments_area certified.fragment.owned))

/-- Transport the original fragment sample to a supplied vertex-value readback with the same retained count. -/
@[expose] def ofReadback (fragment : PairedFragmentBlocks.OwnedFragment
  evaluated data otherData) {count : Nat}
    (equalCount : fragment.count = count) (values : Fin (count + 1) → Topology.Polygon.Stokes.PrimitivePoint)
    (equal : ∀ vertex, PairedOwnedFragments.ownedValues fragment.first
      fragment.second
      (Fin.cast (congrArg (· + 1) equalCount.symm) vertex) = values vertex) :
    SampledFragment (evaluated := evaluated) (data
      := data) (otherData := otherData) values :=
  ⟨fragment, SampleReadback.Sample.readback (SampleReadback.Sample.castCount
    equalCount fragment.owned) equal,
    SampleReadback.Sample.castCount_increments equalCount fragment.owned⟩

/-- Transport a certified sample to the exact vertex trace built from its original index map. -/
@[expose] def ofIndexed {Vertex : Type} {count : Nat} (vertices : Fin (count + 1) → Vertex) (values : Vertex →
  Topology.Polygon.Stokes.PrimitivePoint)
    (original : SampledFragment (evaluated :=
      evaluated) (data := data) (otherData := otherData)
      (fun vertex => values (vertices vertex))) :
    SampledFragment (evaluated := evaluated) (data
      := data) (otherData := otherData)
      (fun vertex => values ((Path.JoinedTrace.VertexTrace.ofIndexed vertices).indexed vertex)) :=
  ⟨original.fragment, SampleReadback.VertexTrace.ofIndexedSample vertices values original.reading,
    (SampleReadback.VertexTrace.ofIndexedSample_increments vertices values original.reading).trans
      original.increments_eq⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison.SampledFragment

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison

/-- Interleave original piece fragments with one junction between each adjacent pair. -/
@[expose] def interleaveFragments : {count : Nat} →
    (Fin (count + 1) → PairedFragmentBlocks.OwnedFragment evaluated data
      otherData) →
    (Fin count → PairedFragmentBlocks.OwnedFragment evaluated data
      otherData) → List (PairedFragmentBlocks.OwnedFragment evaluated data
      otherData)
  | 0, pieces, _ => [pieces 0]
  | _ + 1, pieces, junctions => pieces 0 :: junctions 0 ::
      JoinedFragmentComparison.interleaveFragments (fun
        position => pieces position.succ) (fun position => junctions position.succ)

/-- The interleaved original owned increment blocks are exactly the certified piece and junction samples. -/
theorem interleave_owned {Vertex : Type} (values : Vertex → Topology.Polygon.Stokes.PrimitivePoint) {count : Nat}
    (traces : Fin (count + 1) → Path.JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      SampledFragment (evaluated := evaluated)
      (data := data) (otherData := otherData)
      (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      SampledFragment (evaluated := evaluated)
      (data := data) (otherData := otherData)
      (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
        :
    ((JoinedFragmentComparison.interleaveFragments (fun position => (pieces
      position).fragment) (fun position => (junctions position).fragment)).map
      PairedFragmentBlocks.OwnedFragment.pair).map Prod.fst =
      JoinedSampleBlocks.sampledBlocks values traces (fun position => (pieces position).reading)
        (fun position => (junctions position).reading) := by
  induction count with
  | zero => exact congrArg (fun block => [block]) (pieces 0).increments_eq.symm
  | succ count ih =>
    change (Sample.increments (pieces 0).fragment.owned) ::
      (Sample.increments (junctions 0).fragment.owned) :: _ =
      (Sample.increments (pieces 0).reading) ::
        (Sample.increments (junctions 0).reading) :: _
    exact congrArg₂ List.cons (pieces 0).increments_eq.symm
      (congrArg₂ List.cons (junctions 0).increments_eq.symm
        (ih (fun position => traces position.succ) (fun position => pieces position.succ) (fun position => junctions
          position.succ)))

/-- The error controls the original whole-side cached area, including all
owner junctions and the cross-fragment polygon. No whole-path equality or
analytic estimate is supplied by the caller. -/
theorem joined_fragments_area_bound {Vertex : Type} (values : Vertex → Topology.Polygon.Stokes.PrimitivePoint) {count :
  Nat}
    (traces : Fin (count + 1) → Path.JoinedTrace.VertexTrace Vertex)
    (pieces : (position : Fin (count + 1)) →
      SampledFragment (evaluated := evaluated)
      (data := data) (otherData := otherData)
      (fun vertex => values ((traces position).indexed vertex)))
    (junctions : (position : Fin count) →
      SampledFragment (evaluated := evaluated)
      (data := data) (otherData := otherData)
      (JoinedSampleBlocks.JunctionValues values (traces position.castSucc) (traces position.succ)))
    {whole : Path.JoinedTrace.VertexTrace Vertex} (original : Periods.CenteredBilinearPath.Sample (fun vertex => values
      (whole.indexed vertex)))
    (traceEq : whole = Path.JoinedTrace.VertexTrace.concatenate traces) :
    let fragments := JoinedFragmentComparison.interleaveFragments (fun
      position => (pieces position).fragment) (fun position => (junctions position).fragment)
    Gaussian.Norm.Basic.normSq (original.centeredArea - Path.PairedIncrementArea.area ((fragments.map
      PairedFragmentBlocks.OwnedFragment.pair).map Prod.snd).flatten) ≤
      PairedFragmentBlocks.fragmentBlockError fragments := by
  intro fragments
  have bound := PairedFragmentBlocks.owned_fragments_area_bound fragments
  have owned := JoinedFragmentComparison.interleave_owned values traces
    pieces junctions
  change (fragments.map PairedFragmentBlocks.OwnedFragment.pair).map
    Prod.fst = _ at owned
  rw [owned, JoinedSampleBlocks.sampledBlocks_flatten values traces _ _ original traceEq,
    (Sample.increments_area original)] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison

section MatchedSides

variable {lc lr rc rr depth : Nat} {lg : RectangularInverseModels.Geometry lc lr} {rg :
  RectangularInverseModels.Geometry rc rr}
  {leftCuts : Paths.RectangularSegmentSplitting.GridCuts lg} {rightCuts : Paths.RectangularSegmentSplitting.GridCuts rg}
    {leftBox rightBox : Rational.Box}
  {left : Meshes.RectangularObservationMesh.ObservationMesh leftCuts leftBox} {right :
    Meshes.RectangularObservationMesh.ObservationMesh rightCuts rightBox}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison

/-- Bound the original whole horizontal-side sample against the retained source fragment path.

Certified piece and junction samples preserve the actual side order and its complete joining polygon. -/
theorem horizontal_fragments_area_bound
    {leftRow : Fin left.partition.y.intervals.length} {rightRow : Fin right.partition.y.intervals.length}
    {height : InverseRootPolynomial.Coordinate} {side :
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide left right leftRow rightRow
      height}
    (trace : side.Trace depth) (values : Fin (lc + 1) → Fin (lr + 1) → InverseRootPolynomial.Gaussian →
      Topology.Polygon.Stokes.PrimitivePoint)
    (pieces : (column : Fin (left.boundaryColumns + 1)) →
      SampledFragment (evaluated := evaluated)
        (data := data) (otherData := otherData)
        (fun vertex => trace.leftValue values ((side.pieceVertices depth column).indexed vertex)))
    (junctions : (column : Fin left.boundaryColumns) →
      SampledFragment (evaluated := evaluated)
        (data := data) (otherData := otherData)
        (JoinedSampleBlocks.JunctionValues (trace.leftValue values) (side.pieceVertices depth
          column.castSucc) (side.pieceVertices depth column.succ)))
    (original : Periods.CenteredBilinearPath.Sample (fun vertex => trace.leftValue values (trace.vertices.indexed
      vertex))) :
    let fragments := JoinedFragmentComparison.interleaveFragments (fun
      column => (pieces column).fragment) (fun column => (junctions column).fragment)
    Gaussian.Norm.Basic.normSq (original.centeredArea - Path.PairedIncrementArea.area ((fragments.map
      PairedFragmentBlocks.OwnedFragment.pair).map Prod.snd).flatten) ≤
      PairedFragmentBlocks.fragmentBlockError fragments :=
  JoinedFragmentComparison.joined_fragments_area_bound (trace.leftValue
    values) (side.pieceVertices depth) pieces junctions original trace.vertices_eq

/-- Bound the original whole vertical-side sample against the retained source fragment path.

Certified piece and junction samples preserve the actual side order and its complete joining polygon. -/
theorem vertical_fragments_area_bound
    {leftColumn : Fin left.partition.x.intervals.length} {rightColumn : Fin right.partition.x.intervals.length}
    {horizontal : InverseRootPolynomial.Coordinate} {side :
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide left right leftColumn rightColumn
      horizontal}
    (trace : side.Trace depth) (values : Fin (lc + 1) → Fin (lr + 1) → InverseRootPolynomial.Gaussian →
      Topology.Polygon.Stokes.PrimitivePoint)
    (pieces : (row : Fin (left.boundaryRows + 1)) →
      SampledFragment (evaluated := evaluated)
        (data := data) (otherData := otherData)
        (fun vertex => trace.leftValue values ((side.pieceVertices depth row).indexed vertex)))
    (junctions : (row : Fin left.boundaryRows) →
      SampledFragment (evaluated := evaluated)
        (data := data) (otherData := otherData)
        (JoinedSampleBlocks.JunctionValues (trace.leftValue values) (side.pieceVertices depth
          row.castSucc) (side.pieceVertices depth row.succ)))
    (original : Periods.CenteredBilinearPath.Sample (fun vertex => trace.leftValue values (trace.vertices.indexed
      vertex))) :
    let fragments := JoinedFragmentComparison.interleaveFragments (fun row
      => (pieces row).fragment) (fun row => (junctions row).fragment)
    Gaussian.Norm.Basic.normSq (original.centeredArea - Path.PairedIncrementArea.area ((fragments.map
      PairedFragmentBlocks.OwnedFragment.pair).map Prod.snd).flatten) ≤
      PairedFragmentBlocks.fragmentBlockError fragments :=
  JoinedFragmentComparison.joined_fragments_area_bound (trace.leftValue
    values) (side.pieceVertices depth) pieces junctions original trace.vertices_eq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison

end MatchedSides

end
