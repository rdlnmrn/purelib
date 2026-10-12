module
import Purelib.Algebra.Group.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.WeightedPathArea
import Purelib.Integration.Path.WeightedPathComparison
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RegularClosedBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Integration.Path.OwnedPathComparison
import Purelib.Integration.Path.HomogeneousOwnedPathComparison
import Purelib.Integration.Path.CenteredPathIncrements
public import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SynchronizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Tactic.Ring

public section

/-! Fine face fragments compare with the source primitives of the actual
closed boundary bank, not a separately evaluated uniform-depth cap path. -/
section
section
section

open Purelib.Data.Rat

open Purelib.Algebra
open Purelib.Curves
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)

open
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  (ClosedBoundaryComparison)

open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
open Purelib.Riemann.Normalization

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}
  {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  (comparison : prepared.ClosedBoundaryComparison other requested minimum)
  (occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential) (i : Fin comparison.original.plans.length)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
namespace LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison

/-- The exact original parent at the supplied index of the retained closed-boundary request. -/
@[expose] def
  Parent
  := (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original i).parent

/-- A retained rectangular fragment of that original closed-boundary parent in the supplied occurrence geometry. -/
@[expose] def
  Piece
  := Paths.RectangularSegmentSplitting.SegmentPiece occurrence.compared.entered.domain.geometry

    ((Parent
    comparison i).edge.point 0)
    ((Parent
    comparison i).edge.point 1)

/-- Read both source primitive values already retained at the original closed-boundary parent index. -/
@[expose] def
  sourceValues
  (parameter : Normalization.InverseRootPolynomial.Coordinate) : PrimitivePoint :=
  Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues
    (comparison.entries.get i).source
    (comparison.entries.get i).otherSource parameter

/-- Read both aligned shared-face values on the same retained parent fragment and parameter. -/
@[expose] def
  faceValues
  (piece :
  Piece
  comparison occurrence i) {index : Nat}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) (second
      : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains)
    (parameter : Normalization.InverseRootPolynomial.Coordinate) : PrimitivePoint :=
  let left := occurrence.compared.sharedData first occurrence.aligned
  let right := (occurrence.recastComparison other).sharedData second (occurrence.recastComparison_aligned other)
  ⟨left.anchors.alignedValue left.offsets piece.column piece.row
    ((Parent
    comparison i).edge.point parameter),
    right.anchors.alignedValue right.offsets piece.column piece.row
      ((Parent
      comparison i).edge.point parameter)⟩

/-- The common density dominating both original closed-boundary source-to-face query errors. -/
@[expose] def
  queryDensity
  (piece :
  Piece
  comparison occurrence i) (index : Nat) : Coordinate :=
  max (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity occurrence.compared.entered.bounds
    piece.column piece.row (comparison.entries.get i).first.localRequest index)
    (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity
      (occurrence.recastComparison other).entered.bounds piece.column piece.row
      (comparison.entries.get i).second.localRequest index)

/-- The retained common closed-boundary query density is nonnegative at every stage. -/
theorem
  queryDensity_nonnegative
  (piece :
  Piece
  comparison occurrence i) (index : Nat) :
    0 ≤
      queryDensity
      comparison occurrence i piece index :=
  (Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity_nonnegative occurrence.compared.entered.bounds
    piece.column piece.row (comparison.entries.get i).first.localRequest index).trans (Fraction.Order.Basic.le_max_left
      _ _)

/-- Bound both face-to-source increment errors on one original closed-boundary fragment.

Parent membership, retained source polynomial identities and actual fragment geometry determine the common error bound.
-/
theorem
  query_error
  (member :
  Parent
  comparison i ∈ occurrence.compared.entered.cache.parents)
    (piece :
      Piece
      comparison occurrence i) {index : Nat}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) (second
      : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains)
    (a b : Normalization.InverseRootPolynomial.Coordinate) (aInside : piece.interval.lower ≤ a ∧ a ≤
      piece.interval.upper)
    (bInside : piece.interval.lower ≤ b ∧ b ≤ piece.interval.upper) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (((faceValues
      comparison occurrence i piece first second b).sub
      (faceValues
      comparison occurrence i piece first second a)).sub

        ((sourceValues
        comparison i b).sub
        (sourceValues
        comparison i a)))

        (queryDensity
        comparison occurrence i piece index * Data.Gaussian.Norm.Basic.normSq
        ((Parent
        comparison i).edge.point b -
        (Parent
        comparison i).edge.point a)) := by
  let left := occurrence.compared.sharedData first occurrence.aligned
  let right := (occurrence.recastComparison other).sharedData second (occurrence.recastComparison_aligned other)
  have leftBound := Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.query_increment_le
    occurrence.compared.entered.bounds (parent :=
      Parent
      comparison i)
    (count := genus) (target := comparison.original.allowance) piece left.primitives
    (occurrence.compared.entered.reached _ member) (comparison.entries.get i).first.localRequest a b aInside bInside
  rw [(comparison.entries.get i).first_eq] at leftBound
  have recastMember := Data.List.Map.mem_map_of_mem (f := Integration.PreparedEdgeRecasting.recastCenteredEdge other)
    member
  have rightBound := Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.query_increment_le
    (occurrence.recastComparison other).entered.bounds
    (parent := Integration.PreparedEdgeRecasting.recastCenteredEdge other
      (Parent
      comparison i)) (count := genus) (target := comparison.original.allowance)
    piece right.primitives ((occurrence.recastComparison other).entered.reached _ recastMember)
    (comparison.entries.get i).second.localRequest a b aInside bInside
  rw [(comparison.entries.get i).second_eq] at rightBound
  have recastPoint (parameter : Normalization.InverseRootPolynomial.Coordinate) :
      (Integration.PreparedEdgeRecasting.recastCenteredEdge other
        (Parent
        comparison i)).edge.point parameter =

          (Parent
          comparison i).edge.point parameter := rfl
  rw [recastPoint a, recastPoint b] at rightBound
  have leftLe : Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity occurrence.compared.entered.bounds
      piece.column piece.row (comparison.entries.get i).first.localRequest index ≤
        queryDensity
        comparison occurrence i piece index := Fraction.Order.Basic.le_max_left _ _
  have rightLe : Hyperelliptic.Meshes.PuncturedGrid.Face.FragmentQueries.queryDensity
      (occurrence.recastComparison other).entered.bounds piece.column piece.row
      (comparison.entries.get i).second.localRequest index ≤
        queryDensity
        comparison occurrence i piece index := Fraction.Order.Basic.le_max_right _ _
  constructor
  · have bound := leftBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct leftLe
      (Gaussian.Norm.Basic.normSq_nonneg _))
    change Fraction.Order.Basic.LessEqual _ _ at bound
    change Fraction.Order.Basic.LessEqual _ _
    simpa only
      [faceValues,
      sourceValues,
      Parent,
      left, Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues,
      Topology.Polygon.Stokes.PrimitivePoint.sub,
      Integration.RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue, Group.add_sub_add_left_eq_sub,
      Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  · have bound := rightBound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rightLe
      (Gaussian.Norm.Basic.normSq_nonneg _))
    change Fraction.Order.Basic.LessEqual _ _ at bound
    change Fraction.Order.Basic.LessEqual _ _
    simpa only
      [faceValues,
      sourceValues,
      Parent,
      right, Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues,
      Topology.Polygon.Stokes.PrimitivePoint.sub,
      Integration.RectangularPrimitiveGluing.PrimitiveAnchors.alignedValue, Group.add_sub_add_left_eq_sub,
      Gaussian.Norm.Basic.normSq_eq_canonical] using bound

/-- The common slope bound of both original source primitives at the retained parent index. -/
@[expose] def
  sourceDensity
  : Coordinate := max (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original
  i).data.sourceSlope
  (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original i).otherData.sourceSlope

/-- The common retained source slope is nonnegative. -/
theorem
  sourceDensity_nonnegative
  : 0 ≤
  sourceDensity
  comparison i :=
  (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original
    i).data.sourceSlope_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

/-- Both original source increments satisfy the common slope bound inside the retained fragment. -/
theorem
  source_increment
  (piece :
  Piece
  comparison occurrence i) (a b : Normalization.InverseRootPolynomial.Coordinate)
    (aInside : piece.interval.lower ≤ a ∧ a ≤ piece.interval.upper)
    (bInside : piece.interval.lower ≤ b ∧ b ≤ piece.interval.upper) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((sourceValues
      comparison i b).sub
      (sourceValues
      comparison i a))
      (sourceDensity
      comparison i * (b - a) ^ 2) := by
  have aUnit : 0 ≤ a ∧ a ≤ 1 := ⟨piece.within.1.trans aInside.1, aInside.2.trans piece.within.2⟩
  have bUnit : 0 ≤ b ∧ b ≤ 1 := ⟨piece.within.1.trans bInside.1, bInside.2.trans piece.within.2⟩
  have left := (comparison.entries.get i).source.increment_bound aUnit bUnit
  have right := (comparison.entries.get i).otherSource.increment_bound aUnit bUnit
  have leftBound := left.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Basic.le_max_left (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent
    comparison.original i).data.sourceSlope (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent
    comparison.original i).otherData.sourceSlope) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have rightBound := right.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Basic.le_max_right (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent
    comparison.original i).data.sourceSlope (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent
    comparison.original i).otherData.sourceSlope) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
  have recastPoint (parameter : Normalization.InverseRootPolynomial.Coordinate) :
      (Integration.PreparedEdgeRecasting.recastCenteredEdge other
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original i).parent).edge.point
        parameter =
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original i).parent.edge.point
          parameter := rfl
  rw [recastPoint a, recastPoint b] at rightBound
  constructor
  · change Fraction.Order.Basic.LessEqual _ _
    change Fraction.Order.Basic.LessEqual _ _ at leftBound
    simpa only
      [sourceValues,

        sourceDensity,
      Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues,
      Topology.Polygon.Stokes.PrimitivePoint.sub,
      Gaussian.Norm.Basic.normSq_eq_canonical] using leftBound
  · change Fraction.Order.Basic.LessEqual _ _
    change Fraction.Order.Basic.LessEqual _ _ at rightBound
    simpa only
      [sourceValues,

        sourceDensity,
      Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues,
      Topology.Polygon.Stokes.PrimitivePoint.sub,
      Gaussian.Norm.Basic.normSq_eq_canonical] using rightBound

/-- The complete paired trace density from original query error, parent movement and source slope. -/
@[expose] def
  traceDensity
  (piece :
  Piece
  comparison occurrence i) (index : Nat) : Coordinate :=
  2 *
    (queryDensity
    comparison occurrence i piece index *
    (Parent
    comparison i).edge.pointMovement +
    sourceDensity
    comparison i)

/-- The common query density weighted by the containing original cell's squared diagonal. -/
@[expose] def
  traceError
  (piece :
  Piece
  comparison occurrence i) (index : Nat) : Coordinate :=

    queryDensity
    comparison occurrence i piece index * (occurrence.compared.entered.domain.geometry.box piece.column
    piece.row).diagonalSq

end LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea

/-- The retained parent's squared point displacement equals its full movement times squared parameter displacement. -/
private theorem point_movement (a
  b : Normalization.InverseRootPolynomial.Coordinate) :
    Data.Gaussian.Norm.Basic.normSq
      ((ClosedBoundaryComparison.Parent
      comparison i).edge.point b -
      (ClosedBoundaryComparison.Parent
      comparison i).edge.point a) =

        (ClosedBoundaryComparison.Parent
        comparison i).edge.pointMovement * (b - a) ^ 2 := by
  have full :=
    (ClosedBoundaryComparison.Parent
    comparison i).edge.localSegment.normSq_pointAt_sub_pointAt 1 0
  have unitSquare : ((1 : Normalization.InverseRootPolynomial.Coordinate) - 0) ^ 2 = 1 := rfl
  simp only [-eq_self, -iff_self, unitSquare, Fraction.Field.one_mul] at full
  have segment :=
    (ClosedBoundaryComparison.Parent
    comparison i).edge.localSegment.normSq_pointAt_sub_pointAt b a
  exact segment.trans ((congrArg (fun value => (b - a) ^ 2 * value) full.symm).trans (Fraction.Field.mul_comm ..))

/-- The original retained source density is bounded by the complete trace density. -/
private theorem source_le_trace
  (piece :
  ClosedBoundaryComparison.Piece
  comparison occurrence i) (index : Nat) :

      ClosedBoundaryComparison.sourceDensity
      comparison i ≤
      ClosedBoundaryComparison.traceDensity
      comparison occurrence i piece index := by
  have extra : 0 ≤
    ClosedBoundaryComparison.queryDensity
    comparison occurrence i piece index *
    (ClosedBoundaryComparison.Parent
    comparison i).edge.pointMovement :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (ClosedBoundaryComparison.queryDensity_nonnegative
      comparison occurrence i piece index)
      (Gaussian.Norm.Basic.normSq_nonneg
        ((ClosedBoundaryComparison.Parent
        comparison i).edge.point 1 -
        (ClosedBoundaryComparison.Parent
        comparison i).edge.point 0))
  have nonnegative := add_nonneg extra
    (ClosedBoundaryComparison.sourceDensity_nonnegative
    comparison i)
  exact (le_add_of_nonneg_left extra).trans ((le_add_of_nonneg_right nonnegative).trans_eq (by
    unfold ClosedBoundaryComparison.traceDensity
    ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
namespace LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison

/-- Bound both aligned shared-face increments by the original trace density and squared parameter displacement. -/
theorem
  face_increment
  (member :
  Parent
  comparison i ∈ occurrence.compared.entered.cache.parents)
    (piece :
      Piece
      comparison occurrence i) {index : Nat}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) (second
      : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains)
    (a b : Normalization.InverseRootPolynomial.Coordinate) (aInside : piece.interval.lower ≤ a ∧ a ≤
      piece.interval.upper)
    (bInside : piece.interval.lower ≤ b ∧ b ≤ piece.interval.upper) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((faceValues
      comparison occurrence i piece first second b).sub
      (faceValues
      comparison occurrence i piece first second a))

        (traceDensity
        comparison occurrence i piece index * (b - a) ^ 2) := by
  have errors :=
    query_error
    comparison occurrence i member piece first second a b aInside bInside
  have sources :=
    source_increment
    comparison occurrence i piece a b aInside bInside
  rw [Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea.point_movement] at errors
  have scalar {x y : Normalization.InverseRootPolynomial.Gaussian}
      (error : Data.Gaussian.Norm.Basic.normSq (x - y) ≤
        queryDensity
        comparison occurrence i piece index *
        ((Parent
        comparison i).edge.pointMovement * (b - a) ^ 2))
      (source : Data.Gaussian.Norm.Basic.normSq y ≤
        sourceDensity
        comparison i * (b - a) ^ 2) : Data.Gaussian.Norm.Basic.normSq x ≤
        traceDensity
        comparison occurrence i piece index * (b - a) ^ 2 := by
    have estimate := Gaussian.Norm.Bounds.normSq_add_le_two (x - y) y
    rw [sub_add_cancel] at estimate
    exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct error source) (by decide)).trans_eq
      (by
        unfold traceDensity
        ring1))
  have oldBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have canonicalBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  exact ⟨canonicalBound (scalar (oldBound errors.1) (oldBound sources.1)),
    canonicalBound (scalar (oldBound errors.2) (oldBound sources.2))⟩

/-- Full fragment area comparison at arbitrary monotone retained parameters.
The only assignment premise is membership in the actual occurrence cache;
both analytic estimates come from this closed boundary's own source bank. -/
theorem
  fragment_area_bound
  (member :
  Parent
  comparison i ∈ occurrence.compared.entered.cache.parents)
    (piece :
      Piece
      comparison occurrence i) {index count : Nat}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) (second
      : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool) (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (grid : Periods.CenteredBilinearPath.Sample (fun vertex =>
      faceValues
      comparison occurrence i piece first second (parameters vertex)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      sourceValues
      comparison i (parameters vertex))) :
    Data.Gaussian.Norm.Basic.normSq (grid.centeredArea - source.centeredArea) ≤ 40 *
      traceError
      comparison occurrence i piece index *

        traceDensity
        comparison occurrence i piece index *
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0) (parameters
        (Fin.last count))) ^ 2 := by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total forward parameters]
  apply Path.WeightedPathComparison.Sample.weighted_full_comparison grid source
    (fun edge : Fin count => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    (fun edge => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative forward _ _
      (ordered edge))
  · intro vertex
    rw [grid.centered_eq, source.centered_eq]
    have errors :=
      query_error
      comparison occurrence i member piece first second (parameters 0) (parameters vertex) (inside 0) (inside vertex)
    have contained (v : Fin (count + 1)) : (occurrence.compared.entered.domain.geometry.box piece.column
      piece.row).Contains

          ((Parent
          comparison i).edge.point (parameters v)) := by
      exact (Integration.PreparedParentSplitting.prepared_point_eq
        (Parent
        comparison i) (parameters v)).symm ▸
        piece.contains_query _ (inside v)
    have distance := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).normSq_sub_le_diagonalSq
      (contained vertex) (contained 0)
    have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
      (queryDensity_nonnegative
      comparison occurrence i piece index)
    exact ⟨errors.1.trans upper, errors.2.trans upper⟩
  · intro edge
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
    exact
      face_increment
      comparison occurrence i member piece first second _ _ (inside edge.castSucc) (inside edge.succ)
  · intro edge
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
    have bound :=
      source_increment
      comparison occurrence i piece _ _ (inside edge.castSucc) (inside edge.succ)
    have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Exterior.BoundaryFragmentArea.source_le_trace comparison occurrence i piece
      index)
      (Fraction.Order.Arithmetic.sq_nonneg_direct (parameters edge.succ - parameters edge.castSucc))
    exact ⟨bound.1.trans upper, bound.2.trans upper⟩

end LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea

/-- Two parameters in one closed interval differ by at most the interval width in squared magnitude. -/
private theorem interval_square
  {lower upper a b : Normalization.InverseRootPolynomial.Coordinate}
    (ha : lower ≤ a ∧ a ≤ upper) (hb : lower ≤ b ∧ b ≤ upper) :
    (b - a) ^ 2 ≤ (upper - lower) ^ 2 := by
  rcases le_total a b with ordered | ordered
  · exact Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct ordered)
      (Fraction.Order.Arithmetic.sub_le_sub_direct hb.2 ha.1) 2
  · have bound := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Order.Arithmetic.sub_nonneg_direct ordered)
      (Fraction.Order.Arithmetic.sub_le_sub_direct ha.2 hb.1) 2
    exact (show (b - a) ^ 2 = (a - b) ^ 2 by ring1).trans_le bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
namespace LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison

/-- Every monotone sampling of a coarse source piece has a small full area.
The bound contains no fine vertex count. -/
theorem
  source_sample_area_bound
  (piece :
  Piece
  comparison occurrence i) {count : Nat}
    (range : Rectangle.Partition.PreparedAxisPartitions.Interval)
    (within : piece.interval.lower ≤ range.lower ∧ range.upper ≤ piece.interval.upper)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, range.lower ≤ parameters vertex ∧ parameters vertex ≤ range.upper)
    (forward : Bool) (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      sourceValues
      comparison i (parameters vertex))) :
    Data.Gaussian.Norm.Basic.normSq source.centeredArea ≤ 4 *
      (sourceDensity
      comparison i) ^ 2 *
      (range.upper - range.lower) ^ 4 := by
  have contained (vertex : Fin (count + 1)) :=
    And.intro (within.1.trans (inside vertex).1) ((inside vertex).2.trans within.2)
  have bound := Path.WeightedPathArea.Sample.centered_weighted_bound source
    (fun edge : Fin count => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    (magnitude :=
      sourceDensity
      comparison i * (range.upper - range.lower) ^ 2)
    (density :=
      sourceDensity
      comparison i)
    (fun edge => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative forward _ _
      (ordered edge))
    (fun vertex => by
      rw [source.centered_eq]
      have sourceBound :=
        source_increment
        comparison occurrence i piece _ _ (contained 0) (contained vertex)
      have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Exterior.BoundaryFragmentArea.interval_square (inside 0) (inside vertex))

          (sourceDensity_nonnegative
          comparison i)
      exact ⟨sourceBound.1.trans upper, sourceBound.2.trans upper⟩)
    (fun edge => by
      rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
      exact
        source_increment
        comparison occurrence i piece _ _ (contained edge.castSucc) (contained edge.succ))
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq] at bound
  have factorNonnegative : 0 ≤ 4 *
    (sourceDensity
    comparison i *
      (range.upper - range.lower) ^ 2) *
        sourceDensity
        comparison i :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (sourceDensity_nonnegative
        comparison i) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))

        (sourceDensity_nonnegative
        comparison i)
  exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Exterior.BoundaryFragmentArea.interval_square (inside 0) (inside (Fin.last
      count))) factorNonnegative).trans_eq (by ring1))

/-- Different fine samplings are compared through an automatic common
refinement. Their actual maximum step controls the area error, without a
fine-count factor; matching endpoints identify only their totals. -/
theorem
  source_resampling
  (piece :
  Piece
  comparison occurrence i) {count nextCount : Nat}
    (range : Rectangle.Partition.PreparedAxisPartitions.Interval)
    (within : piece.interval.lower ≤ range.lower ∧ range.upper ≤ piece.interval.upper)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate) (next : Fin (nextCount + 1) →
      Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, range.lower ≤ parameters vertex ∧ parameters vertex ≤ range.upper)
    (nextInside : ∀ vertex, range.lower ≤ next vertex ∧ next vertex ≤ range.upper)
    (forward : Bool)
    (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    (nextOrdered : ∀ edge : Fin nextCount, if forward then next edge.castSucc ≤ next edge.succ
      else next edge.succ ≤ next edge.castSucc)
    (first_eq : parameters 0 = next 0)
    (last_eq : parameters (Fin.last count) = next (Fin.last nextCount))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      sourceValues
      comparison i (parameters vertex)))
    (resampled : Periods.CenteredBilinearPath.Sample (fun vertex =>
      sourceValues
      comparison i (next vertex))) :
    Data.Gaussian.Norm.Basic.normSq (source.centeredArea - resampled.centeredArea) ≤
      16 *
        (sourceDensity
        comparison i) ^ 2 *
        (max (Path.Dyadic.SourceSampleResampling.meshWidth parameters forward)
          (Path.Dyadic.SourceSampleResampling.meshWidth next forward)) ^ 2 *
          (range.upper - range.lower) ^ 2 ∧
    Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments source) =
      Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments resampled) := by
  constructor
  · have unit {parameter : Normalization.InverseRootPolynomial.Coordinate} (inRange : range.lower ≤ parameter ∧
      parameter ≤ range.upper) :
        0 ≤ parameter ∧ parameter ≤ 1 :=
      ⟨piece.within.1.trans (within.1.trans inRange.1), (inRange.2.trans within.2).trans piece.within.2⟩
    have increment (a b : Normalization.InverseRootPolynomial.Coordinate) (al : 0 ≤ a) (au : a ≤ 1) (bl : 0 ≤ b) (bu : b
      ≤ 1) :
        Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
          ((sourceValues
          comparison i b).sub
          (sourceValues
          comparison i a))
          (sourceDensity
          comparison i * (b - a) ^ 2) := by
      have left := (comparison.entries.get i).source.increment_bound ⟨al, au⟩ ⟨bl, bu⟩
      have right := (comparison.entries.get i).otherSource.increment_bound ⟨al, au⟩ ⟨bl, bu⟩
      have leftBound := left.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Basic.le_max_left (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent
        comparison.original i).data.sourceSlope (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent
        comparison.original i).otherData.sourceSlope) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      have rightBound := right.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Basic.le_max_right (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent
        comparison.original i).data.sourceSlope (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent
        comparison.original i).otherData.sourceSlope) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      have recastPoint (parameter : Normalization.InverseRootPolynomial.Coordinate) :
          (Integration.PreparedEdgeRecasting.recastCenteredEdge other
            (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original
            i).parent).edge.point parameter =
            (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartParent comparison.original
              i).parent.edge.point parameter := rfl
      rw [recastPoint a, recastPoint b] at rightBound
      constructor
      · change Fraction.Order.Basic.LessEqual _ _
        change Fraction.Order.Basic.LessEqual _ _ at leftBound
        simpa only
          [sourceValues,

            sourceDensity,
          Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues,
          Topology.Polygon.Stokes.PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical] using leftBound
      · change Fraction.Order.Basic.LessEqual _ _
        change Fraction.Order.Basic.LessEqual _ _ at rightBound
        simpa only
          [sourceValues,

            sourceDensity,
          Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues,
          Topology.Polygon.Stokes.PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical] using rightBound
    have bound := Path.Dyadic.SourceSampleResampling.sample_bound
      (sourceValues
      comparison i) increment parameters next
      (fun vertex => unit (inside vertex)) (fun vertex => unit (nextInside vertex)) forward ordered nextOrdered first_eq
        last_eq
      (fun edge => (Path.Dyadic.SourceSampleResampling.step_le_meshWidth parameters forward edge).trans
        (Fraction.Order.Basic.le_max_left _ _))
      (fun edge => (Path.Dyadic.SourceSampleResampling.step_le_meshWidth next forward edge).trans
        (Fraction.Order.Basic.le_max_right _ _)) source resampled
    exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Exterior.BoundaryFragmentArea.interval_square (inside 0) (inside (Fin.last
      count)))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _)) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
  · rw [Path.CenteredPathIncrements.Sample.increments_total source, Path.CenteredPathIncrements.Sample.increments_total
      resampled, first_eq, last_eq]

end LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea

/-- Equal block totals cancel the cross-block polygon while length-weighted internal area errors sum.

Nonnegative weights retain the complete finite block order and give the square of their total weight. -/
private theorem
  equal_total_blocks {n : Nat}
  (left right : Fin n → List Topology.Polygon.Stokes.PrimitivePoint)
    (weights : Fin n → Normalization.InverseRootPolynomial.Coordinate) (nonnegative : ∀ j, 0 ≤ weights j)
    {error : Normalization.InverseRootPolynomial.Coordinate}
    (totals : ∀ j, Path.PairedIncrementArea.total (left j) = Path.PairedIncrementArea.total (right j))
    (bounded : ∀ j, Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (left j) -
      Path.PairedIncrementArea.area (right j)) ≤ error * (weights j) ^ 2) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (List.ofFn left).flatten -
      Path.PairedIncrementArea.area (List.ofFn right).flatten) ≤ error * (FiniteSum.Fin.sumFin weights) ^ 2 := by
  have sumOfFn {m : Nat} (values : Fin m → Normalization.InverseRootPolynomial.Gaussian) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn values) = FiniteSum.Fin.sumFin values := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Data.List.OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      exact congrArg (fun tail => values 0 + tail) (ih (fun j => values j.succ))
  have sumDifference {m : Nat} (a b : Fin m → Normalization.InverseRootPolynomial.Gaussian) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn (fun j => a j - b j)) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn a) -
          Data.Gaussian.Norm.Sum.Basic.gaussianSum (List.ofFn b) := by
    induction m with
    | zero => change (0 : Normalization.InverseRootPolynomial.Gaussian) = 0 - 0; ring1
    | succ m ih =>
      rw [Data.List.OfFn.Basic.ofFn_succ, Data.List.OfFn.Basic.ofFn_succ (function := a),
        Data.List.OfFn.Basic.ofFn_succ (function := b)]
      change (a 0 - b 0) + _ = (a 0 + _) - (b 0 + _)
      rw [ih]
      ring1
  have bound := Gaussian.Norm.Weighted.normSq_sumFin_weighted
    (fun j => Path.PairedIncrementArea.area (left j) - Path.PairedIncrementArea.area (right j)) weights nonnegative
      bounded
  rw [← sumOfFn, sumDifference] at bound
  rw [Path.PairedAreaBlocks.area_flatten, Path.PairedAreaBlocks.area_flatten,
    Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn,
    Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn]
  dsimp only [-eq_self, -iff_self, Function.comp_def]
  rw [Data.List.OfFn.Basic.ofFn_congr totals, Group.add_sub_add_right_eq_sub]
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
namespace LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison

/-- Join the resampled pieces of one original source parent. The polygon
of totals cancels exactly, while every internal area is paid by a length
weight. The actual maximum fine step, not a piece count, controls the error. -/
theorem
  source_resampling_family
  {n : Nat}
    (pieces : Fin n →
      Piece
      comparison occurrence i) (ranges : Fin n → Rectangle.Partition.PreparedAxisPartitions.Interval)
    (within : ∀ j, (pieces j).interval.lower ≤ (ranges j).lower ∧ (ranges j).upper ≤ (pieces j).interval.upper)
    (counts nextCounts : Fin n → Nat)
    (parameters : (j : Fin n) → Fin (counts j + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (next : (j : Fin n) → Fin (nextCounts j + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ j vertex, (ranges j).lower ≤ parameters j vertex ∧ parameters j vertex ≤ (ranges j).upper)
    (nextInside : ∀ j vertex, (ranges j).lower ≤ next j vertex ∧ next j vertex ≤ (ranges j).upper)
    (forward : Bool)
    (ordered : ∀ j (edge : Fin (counts j)), if forward then parameters j edge.castSucc ≤ parameters j edge.succ
      else parameters j edge.succ ≤ parameters j edge.castSucc)
    (nextOrdered : ∀ j (edge : Fin (nextCounts j)), if forward then next j edge.castSucc ≤ next j edge.succ
      else next j edge.succ ≤ next j edge.castSucc)
    (first_eq : ∀ j, parameters j 0 = next j 0)
    (last_eq : ∀ j, parameters j (Fin.last (counts j)) = next j (Fin.last (nextCounts j)))
    (source : (j : Fin n) → Periods.CenteredBilinearPath.Sample (fun vertex =>
      sourceValues
      comparison i (parameters j vertex)))
    (resampled : (j : Fin n) → Periods.CenteredBilinearPath.Sample (fun vertex =>
      sourceValues
      comparison i (next j vertex))) :
    let meshWidths := List.ofFn (fun j => max (Path.Dyadic.SourceSampleResampling.meshWidth (parameters j) forward)
      (Path.Dyadic.SourceSampleResampling.meshWidth (next j) forward))
    let mesh := Path.Dyadic.SourceSampleResampling.maximum meshWidths
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (List.ofFn (fun j =>
      (Path.CenteredPathIncrements.Sample.increments (source j)))).flatten -
      Path.PairedIncrementArea.area (List.ofFn (fun j => (Path.CenteredPathIncrements.Sample.increments (resampled
        j)))).flatten) ≤
        (16 *
          (sourceDensity
          comparison i) ^ 2 * mesh ^ 2) *
          (FiniteSum.Fin.sumFin (fun j => (ranges j).upper - (ranges j).lower)) ^ 2 := by
  intro meshWidths mesh
  have localBound (j : Fin n) :=
    source_resampling
    comparison occurrence i (pieces j) (ranges j) (within j)
    (parameters j) (next j) (inside j) (nextInside j) forward (ordered j) (nextOrdered j)
    (first_eq j) (last_eq j) (source j) (resampled j)
  apply Exterior.BoundaryFragmentArea.equal_total_blocks _ _ (fun j => (ranges
    j).upper - (ranges j).lower)
    (fun j => Fraction.Order.Arithmetic.sub_nonneg_direct (ranges j).ordered.le) (fun j => (localBound j).2)
  intro j
  rw [Path.CenteredPathIncrements.Sample.increments_area (source j), Path.CenteredPathIncrements.Sample.increments_area
    (resampled j)]
  have upper : max (Path.Dyadic.SourceSampleResampling.meshWidth (parameters j) forward)
      (Path.Dyadic.SourceSampleResampling.meshWidth (next j) forward) ≤ mesh :=
    Path.Dyadic.SourceSampleResampling.le_maximum (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨j, rfl⟩)
  have nonnegative : 0 ≤ max (Path.Dyadic.SourceSampleResampling.meshWidth (parameters j) forward)
      (Path.Dyadic.SourceSampleResampling.meshWidth (next j) forward) :=
    (Path.Dyadic.SourceSampleResampling.meshWidth_nonnegative (parameters j) forward).trans
      (Fraction.Order.Basic.le_max_left _ _)
  exact (localBound j).1.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.pow_le_pow_direct nonnegative
      upper 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
        16) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- The actual first point-owner readings at the retained closed-boundary parent parameters. -/
@[expose] def
  FirstReadings
  {index count : Nat} (first : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential
  index domains)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate) :=
  let data := occurrence.compared.sharedData first occurrence.aligned
  Readings.RectangularPointReadings.PointReadings data.anchors data.offsets
    (fun vertex =>
      (Parent
      comparison i).edge.point (parameters vertex))

/-- The actual recast second point-owner readings at those same retained parent parameters. -/
@[expose] def
  SecondReadings
  {index count : Nat} (second : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index
  domains)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate) :=
  let data := (occurrence.recastComparison other).sharedData second (occurrence.recastComparison_aligned other)
  Readings.RectangularPointReadings.PointReadings data.anchors data.offsets
    (fun vertex =>
      (Parent
      comparison i).edge.point (parameters vertex))

/-- The full owner and fixed-cell error, without a fine vertex-count factor. -/
@[expose] def
  ownedAreaError
  (piece :
  Piece
  comparison occurrence i) (index : Nat)
    (length allowance tolerance : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  2 * (40 * tolerance * (4 *
    traceDensity
    comparison occurrence i piece index + 3) *
      (length + allowance) ^ 2 + 40 *
        traceError
        comparison occurrence i piece index *

          traceDensity
          comparison occurrence i piece index * length ^ 2)

/-- Compact exact conclusion for consumers with deeply retained surface data. -/
@[expose] def
  OwnedAreaBound
  (piece :
  Piece
  comparison occurrence i) (index : Nat)
    (length allowance tolerance : Normalization.InverseRootPolynomial.Coordinate) (ownedArea sourceArea :
      Normalization.InverseRootPolynomial.Gaussian) : Prop :=
  Data.Gaussian.Norm.Basic.normSq (ownedArea - sourceArea) ≤
    ownedAreaError
    comparison occurrence i piece index length allowance tolerance

/-- Pay actual point-owner changes on the shared surface, retaining the
already sampled area and the closed boundary bank's source primitives. -/
theorem
  owned_fragment_area_bound
    (member :
      Parent
      comparison i ∈ occurrence.compared.entered.cache.parents)
    (piece :
      Piece
      comparison occurrence i) {index count : Nat}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) (second
      : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool) (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget count
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (left :
      FirstReadings
      comparison occurrence i first parameters)
    (right :
      SecondReadings
      comparison occurrence i second parameters)
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => (⟨left.values vertex, right.values vertex⟩ :
      Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      sourceValues
      comparison i (parameters vertex))) :

      OwnedAreaBound
      comparison occurrence i piece index
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0) (parameters
        (Fin.last count))) allowance budget.tolerance
      owned.centeredArea source.centeredArea := by
  dsimp only [-eq_self, -iff_self,
    OwnedAreaBound,
    ownedAreaError]
  let fixed := Periods.CenteredBilinearPath.Sample.build (fun vertex =>
    faceValues
    comparison occurrence i piece first second (parameters vertex))
  have contained (vertex : Fin (count + 1)) :
      (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains

          ((Parent
          comparison i).edge.point (parameters vertex)) :=
    (Integration.PreparedParentSplitting.prepared_point_eq
      (Parent
      comparison i) (parameters vertex)).symm ▸
      piece.contains_query _ (inside vertex)
  have nonnegative : 0 ≤
    traceDensity
    comparison occurrence i piece index :=

      (sourceDensity_nonnegative
      comparison i).trans (Exterior.BoundaryFragmentArea.source_le_trace comparison
      occurrence i piece index)
  have ownerError : Data.Gaussian.Norm.Basic.normSq (owned.centeredArea - fixed.centeredArea) ≤
      40 * budget.tolerance * (4 *
        traceDensity
        comparison occurrence i piece index + 3) *
        (FiniteSum.Fin.sumFin (fun edge : Fin count =>
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters
          edge.castSucc) (parameters edge.succ)) + allowance) ^ 2 := by
    have estimate := Path.HomogeneousOwnedPathComparison.LengthErrorBudget.homogeneous_reading_comparison
      (mass := (1 : Normalization.InverseRootPolynomial.Coordinate)) budget (by decide) owned fixed
      (fun edge : Fin count => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
        (parameters edge.castSucc) (parameters edge.succ))
      nonnegative (fun edge => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative
        forward _ _ (ordered edge))
      (fun vertex => by
        simp only [-eq_self, -iff_self, mul_one]
        constructor
        · have h := owners.first_bound later (occurrence.compared.sharedData first occurrence.aligned)
            left vertex piece.column piece.row (contained vertex)
          change Fraction.Order.Basic.LessEqual _ _ at h
          change Fraction.Order.Basic.LessEqual _ _
          simp only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] at h
          convert h using 1; rfl
        · have h := owners.second_bound later ((occurrence.recastComparison other).sharedData second
            (occurrence.recastComparison_aligned other)) right vertex piece.column piece.row (contained vertex)
          change Fraction.Order.Basic.LessEqual _ _ at h
          change Fraction.Order.Basic.LessEqual _ _
          simp only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] at h
          convert h using 1; rfl)
      (fun edge => by
        simp only [-eq_self, -iff_self, mul_one]
        rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
        exact
          face_increment
          comparison occurrence i member piece first second _ _ (inside edge.castSucc) (inside edge.succ))
    simpa only [Fraction.Field.one_mul, mul_one, one_pow] using estimate
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total] at ownerError
  have sourceError :=
    fragment_area_bound
    comparison occurrence i member piece first second parameters inside forward ordered fixed source
  rw [show owned.centeredArea - source.centeredArea =
    (owned.centeredArea - fixed.centeredArea) + (fixed.centeredArea - source.centeredArea) by ring1]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct ownerError
      sourceError) (by decide))

/-- The endpoint-total error combining owner tolerance with the smaller original displacement and cell-diagonal query
bounds. -/
@[expose] def
  ownedTotalError
  (piece :
  Piece
  comparison occurrence i) (index : Nat) (length tolerance : Normalization.InverseRootPolynomial.Coordinate) :
  Coordinate :=
  2 * (tolerance + min

      (queryDensity
      comparison occurrence i piece index *
      (Parent
      comparison i).edge.pointMovement * length ^ 2)

      (traceError
      comparison occurrence i piece index))

/-- The paired owned-to-source total error and the original source-total magnitude bound.

Both quantities retain their actual endpoints and use the same parent, fragment and stage. -/
@[expose] def
  OwnedTotalsBound
  (piece :
  Piece
  comparison occurrence i) (index : Nat) (length tolerance : Normalization.InverseRootPolynomial.Coordinate)
    (owned source : Topology.Polygon.Stokes.PrimitivePoint) : Prop :=
  Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (owned.sub source)
    (ownedTotalError
    comparison occurrence i piece index length tolerance) ∧
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded source
      (sourceDensity
      comparison i * length ^ 2)

end LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea

/-- Transfer two quarter-tolerance endpoint owner errors and a source increment error to the complete endpoint
difference. -/
private theorem endpoint_transfer
  {x₀ x₁ f₀ f₁ s₀ s₁ : Normalization.InverseRootPolynomial.Gaussian} {tolerance query :
  Normalization.InverseRootPolynomial.Coordinate}
    (first : Data.Gaussian.Norm.Basic.normSq (x₀ - f₀) ≤ tolerance / 4) (last : Data.Gaussian.Norm.Basic.normSq
      (x₁ - f₁) ≤ tolerance / 4)
    (source : Data.Gaussian.Norm.Basic.normSq ((f₁ - f₀) - (s₁ - s₀)) ≤ query) :
    Data.Gaussian.Norm.Basic.normSq ((x₁ - x₀) - (s₁ - s₀)) ≤ 2 * (tolerance + query) := by
  have owner : Data.Gaussian.Norm.Basic.normSq ((x₁ - x₀) - (f₁ - f₀)) ≤ tolerance := by
    rw [show (x₁ - x₀) - (f₁ - f₀) = (x₁ - f₁) - (x₀ - f₀) by ring1]
    exact (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct last
        first) (by decide)).trans_eq
        ((show 2 * (tolerance / 4 + tolerance / 4) = (tolerance / 4) * 4 by ring1).trans
          (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  rw [show (x₁ - x₀) - (s₁ - s₀) = ((x₁ - x₀) - (f₁ - f₀)) + ((f₁ - f₀) - (s₁ - s₀)) by ring1]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct owner
      source) (by decide))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
namespace LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison

/-- The same retained endpoint readings control block-total discrepancies.
These are the inputs needed for the cross-block polygon, independently of
the already established internal-area estimate. -/
theorem
  owned_fragment_totals_bound
    (member :
      Parent
      comparison i ∈ occurrence.compared.entered.cache.parents)
    (piece :
      Piece
      comparison occurrence i) {index count : Nat}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains) (second
      : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool) {tolerance : Normalization.InverseRootPolynomial.Coordinate} (owners :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other tolerance) (later :
      owners.index ≤ index)
    (left :
      FirstReadings
      comparison occurrence i first parameters)
    (right :
      SecondReadings
      comparison occurrence i second parameters)
    (owned : Periods.CenteredBilinearPath.Sample (fun vertex => (⟨left.values vertex, right.values vertex⟩ :
      Topology.Polygon.Stokes.PrimitivePoint)))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      sourceValues
      comparison i (parameters vertex))) :

      OwnedTotalsBound
      comparison occurrence i piece index
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0) (parameters
        (Fin.last count))) tolerance
      (Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments owned))
        (Path.PairedIncrementArea.total (Path.CenteredPathIncrements.Sample.increments source)) := by
  dsimp only [-eq_self, -iff_self,
    OwnedTotalsBound,
    ownedTotalError]
  rw [Path.CenteredPathIncrements.Sample.increments_total owned, Path.CenteredPathIncrements.Sample.increments_total
    source, Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
  have contained (vertex : Fin (count + 1)) :
      (occurrence.compared.entered.domain.geometry.box piece.column piece.row).Contains

          ((Parent
          comparison i).edge.point (parameters vertex)) :=
    (Integration.PreparedParentSplitting.prepared_point_eq
      (Parent
      comparison i) (parameters vertex)).symm ▸
      piece.contains_query _ (inside vertex)
  have leftError (vertex : Fin (count + 1)) := owners.first_bound later
    (occurrence.compared.sharedData first occurrence.aligned) left vertex piece.column piece.row (contained vertex)
  have rightError (vertex : Fin (count + 1)) := owners.second_bound later
    ((occurrence.recastComparison other).sharedData second (occurrence.recastComparison_aligned other))
    right vertex piece.column piece.row (contained vertex)
  have query :=
    query_error
    comparison occurrence i member piece first second
    (parameters 0) (parameters (Fin.last count)) (inside 0) (inside (Fin.last count))
  have distance := (occurrence.compared.entered.domain.geometry.box piece.column piece.row).normSq_sub_le_diagonalSq
    (contained (Fin.last count)) (contained 0)
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
    (queryDensity_nonnegative
    comparison occurrence i piece index)
  have trace : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
    (((faceValues
    comparison occurrence i piece first second (parameters (Fin.last count))).sub

        (faceValues
        comparison occurrence i piece first second (parameters 0))).sub

        ((sourceValues
        comparison i (parameters (Fin.last count))).sub
        (sourceValues
        comparison i (parameters 0))))

          (traceError
          comparison occurrence i piece index) := ⟨query.1.trans upper, query.2.trans upper⟩
  rw [Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryFragmentArea.point_movement,
    ← Fraction.Field.mul_assoc] at query
  have oldBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have canonicalBound {value : Gaussian.Basic.Canonical} {limit : Normalization.InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  exact ⟨⟨canonicalBound (Exterior.BoundaryFragmentArea.endpoint_transfer (leftError
    0) (leftError (Fin.last count)) (oldBound (le_min query.1
    trace.1))),
      canonicalBound (Exterior.BoundaryFragmentArea.endpoint_transfer (rightError 0)
        (rightError (Fin.last count)) (oldBound (le_min query.2 trace.2)))⟩,

      source_increment
      comparison occurrence i piece _ _ (inside 0) (inside (Fin.last count))⟩

end LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.ClosedBoundaryComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences

end
end
