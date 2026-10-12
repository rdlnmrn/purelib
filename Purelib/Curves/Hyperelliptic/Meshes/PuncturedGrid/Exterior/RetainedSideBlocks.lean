module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.JoinedTraceIncrements
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
public import Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements
import Purelib.Integration.Polynomial.Rectangle.SampleReadback
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.RectangularTraceIncrementBlocks
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas
import Purelib.Integration.Path.PairedBlockComparison
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.BranchCellBank.LiftedMesh
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.JoinedTrace
open Purelib.Integration.Path.JoinedTraceIncrements
open Purelib.Integration.Polynomial.Rectangle.Perimeter
open Purelib.Integration.Polynomial.Rectangle.SampleReadback
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedHorizontalSide
open Purelib.Riemann.Paths.RectangularTraceIncrementBlocks.MatchedVerticalSide
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary.HandleAreaBounds
open Purelib.Riemann.Normalization

/-! Join the actual cached pieces and owner junctions in side order. The
whole-side area retains the polygon of block totals. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece

open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces bottomSelfSide topSelfSide leftSelfSide
  rightSelfSide)
open Purelib.Riemann.Integration.RectangularCenteredPerimeter (Centered)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Integration.Polynomial.Rectangle.Perimeter.RetainedIncrements (increments increments_eq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece (junction
  junction_eq junctionCount pieceIndex)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)

/-- Interleave the original piece-increment lists and singleton owner-junction increments in physical side order. -/
@[expose] def interleave : {count : Nat} → (Fin (count + 1) → List Stokes.PrimitivePoint) →
    (Fin count → Stokes.PrimitivePoint) → List (List Stokes.PrimitivePoint)
  | 0, pieces, _ => [pieces 0]
  | _ + 1, pieces, joins => pieces 0 :: [joins 0] ::
      interleave
        (fun i => pieces i.succ) (fun i => joins i.succ)

/-- Pair every original physical piece with its retained source increments and every intervening owner junction with an
empty source slot. -/
private def pairedBlocks : {count : Nat} → (Fin (count + 1) → List Stokes.PrimitivePoint) →
    (Fin count → Stokes.PrimitivePoint) → (Fin (count + 1) → List Stokes.PrimitivePoint) →
    List (List Stokes.PrimitivePoint × List Stokes.PrimitivePoint)
  | 0, pieces, _, source => [(pieces 0, source 0)]
  | _ + 1, pieces, joins, source => (pieces 0, source 0) :: ([joins 0], []) ::
      pairedBlocks
        (fun i => pieces i.succ) (fun i => joins i.succ) (fun i => source i.succ)

/-- The physical projection of the paired block list is exactly the original interleaving. -/
private theorem paired_left {count : Nat} (pieces : Fin (count + 1) → List Stokes.PrimitivePoint)
    (joins : Fin count → Stokes.PrimitivePoint) (source : Fin (count + 1) → List Stokes.PrimitivePoint) :
    (pairedBlocks pieces
      joins source).map Prod.fst =
      interleave pieces
      joins := by
  induction count with
  | zero => rfl
  | succ count ih =>
    exact congrArg (fun tail => pieces 0 :: [joins 0] :: tail)
      (ih (fun i => pieces i.succ) (fun i => joins i.succ) (fun i => source i.succ))

/-- Flattening the source projection recovers the complete original source-piece increment list. -/
private theorem paired_right {count : Nat} (pieces : Fin (count + 1) → List Stokes.PrimitivePoint)
    (joins : Fin count → Stokes.PrimitivePoint) (source : Fin (count + 1) → List Stokes.PrimitivePoint) :
    ((pairedBlocks pieces
      joins source).map Prod.snd).flatten = (List.ofFn source).flatten := by
  induction count with
  | zero =>
    simp only
      [pairedBlocks,
      List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      Data.List.Append.append_nil, OfFn.Basic.ofFn_succ, List.ofFn_zero, -eq_self, -iff_self]
    rfl
  | succ count ih =>
    rw [pairedBlocks,
      List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons,
      List.nil_append, OfFn.Basic.ofFn_succ, List.flatten_cons]
    exact congrArg (List.append (source 0)) (ih (fun i => pieces i.succ) (fun i => joins i.succ) (fun i => source
      i.succ))

/-- The paired assembly contains one block per original piece and owner junction. -/
private theorem paired_length {count : Nat} (pieces : Fin (count + 1) → List Stokes.PrimitivePoint)
    (joins : Fin count → Stokes.PrimitivePoint) (source : Fin (count + 1) → List Stokes.PrimitivePoint) :
    (pairedBlocks pieces
      joins source).length = 2 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (pairedBlocks
      (fun i => pieces i.succ) (fun i => joins i.succ) (fun i => source i.succ)).length + 1 + 1 = _
    rw [ih, Nat.mul_succ]

/-- A property verified for every original piece pair and junction pair holds throughout their retained assembly. -/
private theorem paired_all {count : Nat} (pieces : Fin (count + 1) → List Stokes.PrimitivePoint)
    (joins : Fin count → Stokes.PrimitivePoint) (source : Fin (count + 1) → List Stokes.PrimitivePoint)
    (P : List Stokes.PrimitivePoint × List Stokes.PrimitivePoint → Prop)
    (piece : ∀ i, P (pieces i, source i)) (join : ∀ i, P ([joins i], [])) :
    ∀ pair ∈ pairedBlocks
      pieces joins source, P pair := by
  induction count with
  | zero => intro pair member; exact (Data.List.Membership.mem_singleton.mp member) ▸ piece 0
  | succ count ih =>
    intro pair member
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact piece 0
    rcases Data.List.Membership.mem_cons.mp member with rfl | member
    · exact join 0
    exact ih (fun i => pieces i.succ) (fun i => joins i.succ) (fun i => source i.succ)
      (fun i => piece i.succ) (fun i => join i.succ) pair member

/-- The total of a singleton paired increment is that original increment. -/
private theorem single_total (point : Stokes.PrimitivePoint) : PairedIncrementArea.total [point] = point := by
  simp only [PairedIncrementArea.total, List.map_cons, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
    add_zero, -eq_self, -iff_self]
  rfl

/-- A singleton paired increment has zero internal polygon area. -/
private theorem single_area (point : Stokes.PrimitivePoint) : PairedIncrementArea.area [point] = 0 := by
  simp only [PairedIncrementArea.area, PairedIncrementArea.terms, PairedIncrementArea.total,
    List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, Stokes.edgeArea, mul_zero, zero_mul, sub_self,
      add_zero, -eq_self, -iff_self]
  rfl

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece in
/-- Assemble the paid piece and junction bounds into complete area and displacement bounds.

The estimate retains the full block-total polygon and its count-dependent cross terms; source junction slots remain
empty. -/
private theorem interleave_comparison {count : Nat} (pieces : Fin (count + 1) → List Stokes.PrimitivePoint)
    (joins : Fin count → Stokes.PrimitivePoint) (source : Fin (count + 1) → List Stokes.PrimitivePoint)
    {areaError totalError magnitude : InverseRootPolynomial.Coordinate}
    (areaNonnegative : 0 ≤ areaError) (totalNonnegative : 0 ≤ totalError) (magnitudeNonnegative : 0 ≤ magnitude)
    (areas : ∀ i, Data.Gaussian.Norm.Basic.normSq
      (PairedIncrementArea.area (pieces i) - PairedIncrementArea.area (source i)) ≤ areaError)
    (totals : ∀ i, (PrimitivePoint.Bounded ((PairedIncrementArea.total (pieces i)).sub (PairedIncrementArea.total
      (source i)))) totalError)
    (sources : ∀ i, (PrimitivePoint.Bounded (PairedIncrementArea.total (source i))) magnitude) (junctions : ∀ i,
      (PrimitivePoint.Bounded (joins i)) totalError) :
    Data.Gaussian.Norm.Basic.normSq
      (PairedIncrementArea.area
        (interleave pieces
        joins).flatten - PairedIncrementArea.area (List.ofFn source).flatten) ≤
      2 * (((2 * count + 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * areaError +
        16 * ((2 * count + 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * totalError * (2 * (magnitude + totalError)))
          ∧
    (PrimitivePoint.Bounded ((PairedIncrementArea.total
      (interleave pieces
      joins).flatten).sub
      (PairedIncrementArea.total (List.ofFn source).flatten)))
      (((2 * count + 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * totalError) := by
  let bound := 2 * (magnitude + totalError)
  have sumNonnegative := add_nonneg magnitudeNonnegative totalNonnegative
  have boundNonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) sumNonnegative
  have sumLe : magnitude + totalError ≤ bound :=
    (le_add_of_nonneg_right sumNonnegative).trans_eq (by dsimp only [bound]; ring1)
  have magnitudeLe : magnitude ≤ bound := (le_add_of_nonneg_right totalNonnegative).trans sumLe
  have errorLe : totalError ≤ bound := (le_add_of_nonneg_left magnitudeNonnegative).trans sumLe
  have estimate := PairedBlockComparison.blocks_area_difference_bound
    (pairedBlocks pieces
    joins source)
    totalNonnegative boundNonnegative
    (paired_all pieces
      joins source _
      areas
      (by
        intro i
        change Data.Gaussian.Norm.Basic.normSq
          (PairedIncrementArea.area [joins i] - PairedIncrementArea.area []) ≤ areaError
        rw [single_area]
        exact (Data.Gaussian.Norm.Basic.normSq_zero).le.trans areaNonnegative))
    (paired_all pieces
      joins source _
      totals
      (by
        intro i
        change (PrimitivePoint.Bounded ((PairedIncrementArea.total [joins i]).sub (PairedIncrementArea.total [])))
          totalError
        rw [single_total]
        simpa only [PairedIncrementArea.total, List.map_nil,
          Data.Gaussian.Norm.Sum.Basic.gaussianSum, PrimitivePoint.sub, Data.Gaussian.Basic.sub_zero, -eq_self,
            -iff_self] using junctions i))
    (paired_all pieces
      joins source _
      (fun i => PrimitivePoint.perturbation_bounded (sources i) (totals i))
      (by intro i; rw [single_total]; exact ⟨(junctions i).1.trans errorLe, (junctions i).2.trans errorLe⟩))
    (paired_all pieces
      joins source _
      (by intro i; exact ⟨(sources i).1.trans magnitudeLe, (sources i).2.trans magnitudeLe⟩)
      (by intro i; constructor <;> exact (Data.Gaussian.Norm.Basic.normSq_zero).le.trans boundNonnegative))
  rw [paired_left,
    paired_right,
    paired_length] at estimate
  have totalBounds :=
    paired_all pieces joins
    source
    (fun pair => (PrimitivePoint.Bounded ((PairedIncrementArea.total pair.1).sub
      (PairedIncrementArea.total pair.2))) totalError) totals (by
        intro i
        rw [single_total]
        simpa only [PairedIncrementArea.total, List.map_nil,
          Data.Gaussian.Norm.Sum.Basic.gaussianSum, PrimitivePoint.sub, Data.Gaussian.Basic.sub_zero, -eq_self,
            -iff_self] using junctions i)
  let pairs := pairedBlocks
    pieces joins source
  have totalEstimate := PairedIncrementArea.total_bound totalNonnegative
    (values := pairs.map (fun pair => (PairedIncrementArea.total pair.1).sub
      (PairedIncrementArea.total pair.2)))
    (by
      intro point member
      obtain ⟨pair, present, rfl⟩ := Map.mem_map.mp member
      exact totalBounds pair present)
    (count := pairs.length) (by rw [Data.List.Map.length_map])
  have difference := PairedIncrementComparison.total_differences
    (pairs.map (fun pair => (PairedIncrementArea.total pair.1, PairedIncrementArea.total pair.2)))
  rewrite [Data.List.Map.map_map, Data.List.Map.map_map, Data.List.Map.map_map] at difference
  dsimp only [Function.comp_def] at difference
  rw [difference] at totalEstimate
  have left := PairedAreaBlocks.total_flatten (pairs.map Prod.fst)
  have right := PairedAreaBlocks.total_flatten (pairs.map Prod.snd)
  rewrite [Data.List.Map.map_map] at left right
  dsimp only [Function.comp_def] at left right
  rw [← left, ← right] at totalEstimate
  dsimp only [pairs] at totalEstimate
  rw [paired_left,
    paired_right,
    paired_length] at totalEstimate
  exact ⟨estimate, totalEstimate⟩

/-- The original piece-and-junction interleaving equals the increment blocks of the retained joined vertex traces. -/
private theorem interleave_spec {Vertex : Type} (values : Vertex → Stokes.PrimitivePoint) {count : Nat}
    (traces : Fin (count + 1) → JoinedTrace.VertexTrace Vertex) (pieces : Fin (count + 1) → List Stokes.PrimitivePoint)
    (joins : Fin count → Stokes.PrimitivePoint)
    (pieceEq : ∀ i, pieces i = VertexTrace.increments (traces i) values)
    (joinEq : ∀ i, joins i = (values (traces i.succ).first).sub (values (traces i.castSucc).last)) :
    interleave pieces joins
      = VertexTrace.incrementBlocks values (traces 0)
      (List.ofFn (fun i : Fin count => traces i.succ)) := by
  induction count with
  | zero => exact congrArg (fun block => [block]) (pieceEq 0)
  | succ count ih =>
    rw [interleave,
      OfFn.Basic.ofFn_succ, VertexTrace.incrementBlocks]
    exact congrArg₂ List.cons (pieceEq 0) (congrArg₂ List.cons (congrArg (fun value => [value]) (joinEq 0))
      (ih (fun i => traces i.succ) (fun i => pieces i.succ) (fun i => joins i.succ)
        (fun i => pieceEq i.succ) (fun i => joinEq i.succ)))

/-- The centered increments of the original indexed values equal the increments of their retained indexed vertex trace.
-/
private theorem indexed_increments {Vertex : Type} {count : Nat} (vertices : Fin (count + 1) → Vertex)
    (values : Vertex → Stokes.PrimitivePoint) :
    CenteredPathIncrements.increments (fun vertex => values (vertices vertex)) =
      VertexTrace.increments (VertexTrace.ofIndexed vertices) values := by
  let sample := CenteredBilinearPath.Sample.build (fun vertex => values (vertices vertex))
  let indexed := VertexTrace.ofIndexedSample vertices values sample
  exact (CenteredPathIncrements.Sample.increments_raw sample).symm.trans ((VertexTrace.ofIndexedSample_increments
    vertices values sample).symm.trans
    ((CenteredPathIncrements.Sample.increments_raw indexed).trans (VertexTrace.indexed_increments (VertexTrace.ofIndexed
      vertices) values)))

variable {columns rows : Nat} {geometry : Geometry columns rows}
  {cuts : GridCuts geometry} {box :
  Purelib.Geometry.Rational.Box}
  {mesh : ObservationMesh cuts box} {traces :
    PerimeterTraces mesh}
  {values : Fin (columns + 1) → Fin (rows + 1) → Canonical →
    PrimitivePoint}

/-- Read the original side's cached physical piece increments and owner junctions in their retained traversal order. -/
@[expose] def blocks (samples : RectangularCenteredPerimeter.Centered traces values) (side :
  GridLiftedDualSteps.GridSide) : List (List Stokes.PrimitivePoint) :=
  interleave (fun i =>
    RetainedIncrements.increments samples side (RetainedPerimeterPiece.pieceIndex mesh side i))
    (RetainedPerimeterPiece.junction samples side)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedJunctions.RetainedPerimeterPiece
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece in
/-- Quantitative assembly retains every physical owner junction and pays the complete block-total polygon. Source
junction slots are empty; this is not an identification with the closed source path. -/
theorem blocks_comparison (samples : RectangularCenteredPerimeter.Centered traces values) (side :
  GridLiftedDualSteps.GridSide)
    (source : Fin (junctionCount mesh side + 1) → List Stokes.PrimitivePoint)
    {areaError totalError magnitude : InverseRootPolynomial.Coordinate}
    (areaNonnegative : 0 ≤ areaError) (totalNonnegative : 0 ≤ totalError) (magnitudeNonnegative : 0 ≤ magnitude)
    (areas : ∀ i, Data.Gaussian.Norm.Basic.normSq
      (PairedIncrementArea.area (RetainedIncrements.increments samples side (RetainedPerimeterPiece.pieceIndex mesh side
        i)) -
        PairedIncrementArea.area (source i)) ≤ areaError)
    (totals : ∀ i, (PrimitivePoint.Bounded ((PairedIncrementArea.total (RetainedIncrements.increments samples side
      (RetainedPerimeterPiece.pieceIndex mesh side i))).sub
      (PairedIncrementArea.total (source i)))) totalError)
    (sources : ∀ i, (PrimitivePoint.Bounded (PairedIncrementArea.total (source i))) magnitude)
    (junctions : ∀ i, (PrimitivePoint.Bounded (RetainedPerimeterPiece.junction samples side i)) totalError) :
    Data.Gaussian.Norm.Basic.normSq
      (PairedIncrementArea.area (blocks samples side).flatten - PairedIncrementArea.area (List.ofFn source).flatten) ≤
      2 * (((2 * junctionCount mesh side + 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * areaError +
        16 * ((2 * junctionCount mesh side + 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * totalError * (2 *
          (magnitude + totalError))) ∧
    (PrimitivePoint.Bounded ((PairedIncrementArea.total (blocks samples side).flatten).sub
      (PairedIncrementArea.total (List.ofFn source).flatten)))
      (((2 * junctionCount mesh side + 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * totalError) :=
  interleave_comparison
    (fun i => RetainedIncrements.increments samples side (RetainedPerimeterPiece.pieceIndex mesh side i))
    (RetainedPerimeterPiece.junction samples side) source
    areaNonnegative totalNonnegative magnitudeNonnegative areas totals sources junctions

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece in
/-- Flattening the retained side blocks returns the exact cached centered whole-side increment list. -/
theorem blocks_flatten (samples : RectangularCenteredPerimeter.Centered traces values) (side :
  GridLiftedDualSteps.GridSide) :
    (blocks samples side).flatten = match side with
      | .bottom => CenteredPathIncrements.Sample.increments samples.bottom
      | .top => CenteredPathIncrements.Sample.increments samples.top
      | .left => CenteredPathIncrements.Sample.increments samples.left
      | .right => CenteredPathIncrements.Sample.increments samples.right := by
  cases side with
  | bottom =>
    have exactBlocks :=
      interleave_spec
      (traces.bottom.leftValue values) ((RectangularPerimeterTraces.bottomSelfSide mesh).pieceVertices mesh.depth)
      (fun i => RetainedIncrements.increments samples .bottom (RetainedPerimeterPiece.pieceIndex mesh .bottom i))
        (RetainedPerimeterPiece.junction samples .bottom)
      (fun i => (RetainedIncrements.increments_eq samples .bottom (RetainedPerimeterPiece.pieceIndex mesh .bottom
        i)).trans
        (indexed_increments
          (fun vertex => (Fin.cast mesh.boundaryColumns_eq i, vertex)) (traces.bottom.leftValue values)))
      (by
          intro i;
          dsimp only [MatchedHorizontalSide.pieceVertices];
          rw [VertexTrace.ofIndexed_last]
          exact RetainedPerimeterPiece.junction_eq samples .bottom i)
    exact (congrArg List.flatten exactBlocks).trans
      ((congrArg List.flatten (Trace.incrementPartition traces.bottom values samples.bottom).blocks_eq.symm).trans
        (Trace.incrementPartition traces.bottom values samples.bottom).flatten_eq)
  | top =>
    have exactBlocks :=
      interleave_spec
      (traces.top.leftValue values) ((RectangularPerimeterTraces.topSelfSide mesh).pieceVertices mesh.depth)
      (fun i => RetainedIncrements.increments samples .top (RetainedPerimeterPiece.pieceIndex mesh .top i))
        (RetainedPerimeterPiece.junction samples .top)
      (fun i => (RetainedIncrements.increments_eq samples .top (RetainedPerimeterPiece.pieceIndex mesh .top i)).trans
        (indexed_increments
          (fun vertex => (Fin.cast mesh.boundaryColumns_eq i, vertex)) (traces.top.leftValue values)))
      (by
          intro i;
          dsimp only [MatchedHorizontalSide.pieceVertices];
          rw [VertexTrace.ofIndexed_last]
          exact RetainedPerimeterPiece.junction_eq samples .top i)
    exact (congrArg List.flatten exactBlocks).trans
      ((congrArg List.flatten (Trace.incrementPartition traces.top values samples.top).blocks_eq.symm).trans
        (Trace.incrementPartition traces.top values samples.top).flatten_eq)
  | left =>
    have exactBlocks :=
      interleave_spec
      (traces.left.leftValue values) ((RectangularPerimeterTraces.leftSelfSide mesh).pieceVertices mesh.depth)
      (fun i => RetainedIncrements.increments samples .left (RetainedPerimeterPiece.pieceIndex mesh .left i))
        (RetainedPerimeterPiece.junction samples .left)
      (fun i => (RetainedIncrements.increments_eq samples .left (RetainedPerimeterPiece.pieceIndex mesh .left i)).trans
        (indexed_increments
          (fun vertex => (Fin.cast mesh.boundaryRows_eq i, vertex)) (traces.left.leftValue values)))
      (by
          intro i;
          dsimp only [MatchedVerticalSide.pieceVertices];
          rw [VertexTrace.ofIndexed_last]
          exact RetainedPerimeterPiece.junction_eq samples .left i)
    exact (congrArg List.flatten exactBlocks).trans
      ((congrArg List.flatten (Trace.incrementPartition traces.left values samples.left).blocks_eq.symm).trans
        (Trace.incrementPartition traces.left values samples.left).flatten_eq)
  | right =>
    have exactBlocks :=
      interleave_spec
      (traces.right.leftValue values) ((RectangularPerimeterTraces.rightSelfSide mesh).pieceVertices mesh.depth)
      (fun i => RetainedIncrements.increments samples .right (RetainedPerimeterPiece.pieceIndex mesh .right i))
        (RetainedPerimeterPiece.junction samples .right)
      (fun i => (RetainedIncrements.increments_eq samples .right (RetainedPerimeterPiece.pieceIndex mesh .right
        i)).trans
        (indexed_increments
          (fun vertex => (Fin.cast mesh.boundaryRows_eq i, vertex)) (traces.right.leftValue values)))
      (by
          intro i;
          dsimp only [MatchedVerticalSide.pieceVertices];
          rw [VertexTrace.ofIndexed_last]
          exact RetainedPerimeterPiece.junction_eq samples .right i)
    exact (congrArg List.flatten exactBlocks).trans
      ((congrArg List.flatten (Trace.incrementPartition traces.right values samples.right).blocks_eq.symm).trans
        (Trace.incrementPartition traces.right values samples.right).flatten_eq)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.LiftedPuncturedGrid
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder (sideCenteredArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IncrementAreas.CenteredPerimeters (sideIncrements
  sideIncrements_area)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.PairedIncrementArea (area)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {target : Rational} {i j : Fin genus} {stage : Nat} {cache :
    Numerics domains stage}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

/-- The original cached side area is the sum of its retained block areas plus the complete polygon area of block totals.
-/
theorem CenteredPerimeters.retained_blocks_area (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (position : Fin base.faces.regulars.length) (sheet : Fin 2) (side : GridLiftedDualSteps.GridSide) :
    let blocks := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks
      ((samples.samples.get position).get sheet) side
    SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get sheet) side =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) + PairedIncrementArea.area
        (blocks.map PairedIncrementArea.total) := by
  intro blocks
  have same : blocks.flatten = CenteredPerimeters.sideIncrements samples position sheet side := by
    cases side <;> exact
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks_flatten
      ((samples.samples.get position).get sheet) _
  exact (CenteredPerimeters.sideIncrements_area samples position sheet side).symm.trans
    ((congrArg PairedIncrementArea.area same).symm.trans (PairedAreaBlocks.area_flatten blocks))

namespace ExteriorProgram.AllSurfacePreparation
variable {differential : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- The actual exterior correction is assembled from the pieces and owner junctions bounded by the Newton consumer. The
cross-block polygon remains. -/
theorem centeredSideArea_retained_blocks (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (samples : RequestedHoleCentering.CenteredPerimeters request cache i j) :
    prepared.centeredSideArea samples = Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun
      occurrence =>
      let blocks := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.RetainedPerimeterPiece.blocks
        ((samples.samples.get occurrence.sideOccurrence.position).get occurrence.sideOccurrence.sheet)
        occurrence.sideOccurrence.side
      SideOccurrence.oriented occurrence.sideOccurrence
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum (blocks.map PairedIncrementArea.area) + PairedIncrementArea.area
          (blocks.map PairedIncrementArea.total)))) := by
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Map.map_congr_left
  intro occurrence _
  exact congrArg (SideOccurrence.oriented occurrence.sideOccurrence)

      (CenteredPerimeters.retained_blocks_area
      samples occurrence.sideOccurrence.position occurrence.sideOccurrence.sheet occurrence.sideOccurrence.side)

end ExteriorProgram.AllSurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RetainedSideBlocks.LiftedPuncturedGrid
