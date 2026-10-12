module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.EnergyRibbonCombination
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamEndpoints
import Purelib.Integration.Path.EnergyRibbonReadback
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainMatchedEnergy
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamEndpoints

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.Integration.Path

open Purelib.Integration.Polynomial.Rectangle.Boundary

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open
  RectangularMatchedEnergyRibbons.RectangularInverseModels.ObservationMesh.MatchedHorizontalSide

open
  Purelib.Riemann.Readings.RectangularMatchedEnergyRibbons.RectangularInverseModels.ObservationMesh.MatchedVerticalSide

@[expose] public section

/-! Combined cached energy ribbons are the actual corrected seams of the
complete face assembly, with both owner joins and endpoints retained. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamRibbons

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : SurfacePartitions observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
    {depth : Nat}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixed error}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : ExteriorRequest.Assemblies energy
    cache coefficients} {perimeters : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters
    assemblies}
  {position : Fin grid.faces.regulars.length}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Basic (conj_add conj_mul)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Integration.Path.BoundaryRibbon (Ribbon)

/-- Conjugation distributes over the finite original coefficient-weighted Gaussian sum. -/
private theorem conjugate_combination {count : Nat} (coefficients values : Fin count → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin (fun row => coefficients row * values row)) =
      FiniteSum.Fin.sumFin (fun row => Data.Gaussian.Basic.conj (coefficients row) *
      Data.Gaussian.Basic.conj (values row)) := by
  induction count with
  | zero => rfl
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, Data.Gaussian.Basic.conj_add, Data.Gaussian.Basic.conj_mul, ih,
      FiniteSum.Fin.sumFin_succ]

/-- The actual left horizontal energy-ribbon vertex reads the retained original seam value with those same coefficients.
-/
private theorem horizontal_left_readback
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) (row : Fin (PieceIndices.rows (partitions.get
      position)))
    (trace : (MatchedSides.horizontalSeamSide energy position column row).Trace energy.depth)
    (ribbons : Data.Vector (BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ i, ribbons i = Trace.energyRibbon trace (cache.atDomain position sheet i).anchors
      (cache.atDomain position sheet i).offsets)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    Polygon.energyPrimitivePoint ((EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)).left
      vertex) =
      trace.leftValue (SeamAreas.seamValues (sheet := sheet) cache coefficients position) (trace.vertices.indexed
        vertex) := by
  let combined := EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)
  have scalar : combined.left vertex =
      FiniteSum.Fin.sumFin (fun i => coefficients i * (cache.atDomain position sheet i).anchors.alignedValue
        (cache.atDomain position sheet i).offsets
        ((MatchedSides.horizontalSeamSide energy position column row).pieces (trace.vertices.indexed
          vertex).1).leftColumn
        ((MatchedSides.horizontalSeamSide energy position column row).pieces (trace.vertices.indexed vertex).1).leftRow
        (trace.point (trace.vertices.indexed vertex))) := by
    rw [EnergyRibbonCombination.combine_left]
    apply FiniteSum.Fin.sumFin_congr
    intro i
    rw [readback i]
    change coefficients i * (trace.leftReadings _ _).values vertex = _
    rw [trace.leftReadings_value]
  refine (congrArg Polygon.energyPrimitivePoint scalar).trans ?_
  dsimp only [Polygon.energyPrimitivePoint]
  rw [conjugate_combination]
  rfl

/-- The actual right horizontal energy-ribbon vertex reads the retained original seam value with those same
coefficients. -/
private theorem horizontal_right_readback
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) (row : Fin (PieceIndices.rows (partitions.get
      position)))
    (trace : (MatchedSides.horizontalSeamSide energy position column row).Trace energy.depth)
    (ribbons : Data.Vector (BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ i, ribbons i = Trace.energyRibbon trace (cache.atDomain position sheet i).anchors
      (cache.atDomain position sheet i).offsets)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    Polygon.energyPrimitivePoint ((EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)).right
      vertex) =
      trace.rightValue (SeamAreas.seamValues (sheet := sheet) cache coefficients position) (trace.vertices.indexed
        vertex) := by
  let combined := EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)
  have scalar : combined.right vertex =
      FiniteSum.Fin.sumFin (fun i => coefficients i * (cache.atDomain position sheet i).anchors.alignedValue
        (cache.atDomain position sheet i).offsets
        ((MatchedSides.horizontalSeamSide energy position column row).pieces (trace.vertices.indexed
          vertex).1).rightColumn
        ((MatchedSides.horizontalSeamSide energy position column row).pieces (trace.vertices.indexed vertex).1).rightRow
        (trace.point (trace.vertices.indexed vertex))) := by
    rw [EnergyRibbonCombination.combine_right]
    apply FiniteSum.Fin.sumFin_congr
    intro i
    rw [readback i]
    change coefficients i * (trace.rightReadings _ _).values vertex = _
    rw [trace.rightReadings_value]
  refine (congrArg Polygon.energyPrimitivePoint scalar).trans ?_
  dsimp only [Polygon.energyPrimitivePoint]
  rw [conjugate_combination]
  rfl

/-- The original horizontal face ribbon difference is its actual vertical seam area minus the retained vertical endpoint
correction. -/
theorem FaceAssembly.horizontal_ribbon_difference (face : FaceAssembly perimeters position)
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) (row : Fin (PieceIndices.rows (partitions.get
      position)))
    (trace : (MatchedSides.horizontalSeamSide energy position column row).Trace energy.depth)
    (ribbons : Data.Vector (BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ i, ribbons i = Trace.energyRibbon trace (cache.atDomain position sheet i).anchors
      (cache.atDomain position sheet i).offsets) :
    (EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)).difference =
      Assembly.verticalSeam (Perimeters.faceSides perimeters position) column row -
        BilinearGridBoundary.verticalEndpoint face.corners column row := by
  have difference := EnergyRibbonReadback.difference_readback
    (EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i))
    (horizontal_left_readback column row trace ribbons readback)
    (horizontal_right_readback column row trace ribbons readback)
  exact difference.trans (congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a - b)
    (Perimeters.horizontal_trace_area perimeters position column row trace)
    (FaceAssembly.horizontal_trace_endpoint face column row trace))

/-- The actual left vertical energy-ribbon vertex reads the retained original seam value with those same coefficients.
-/
private theorem vertical_left_readback
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin ((PieceIndices.rows (partitions.get
      position)) + 1))
    (trace : (MatchedSides.verticalSeamSide energy position column row).Trace energy.depth)
    (ribbons : Data.Vector (BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ i, ribbons i = Trace.energyRibbon trace (cache.atDomain position sheet i).anchors
      (cache.atDomain position sheet i).offsets)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    Polygon.energyPrimitivePoint ((EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)).left
      vertex) =
      trace.leftValue (SeamAreas.seamValues (sheet := sheet) cache coefficients position) (trace.vertices.indexed
        vertex) := by
  let combined := EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)
  have scalar : combined.left vertex =
      FiniteSum.Fin.sumFin (fun i => coefficients i * (cache.atDomain position sheet i).anchors.alignedValue
        (cache.atDomain position sheet i).offsets
        ((MatchedSides.verticalSeamSide energy position column row).pieces (trace.vertices.indexed vertex).1).leftColumn
        ((MatchedSides.verticalSeamSide energy position column row).pieces (trace.vertices.indexed vertex).1).leftRow
        (trace.point (trace.vertices.indexed vertex))) := by
    rw [EnergyRibbonCombination.combine_left]
    apply FiniteSum.Fin.sumFin_congr
    intro i
    rw [readback i]
    change coefficients i * (trace.leftReadings _ _).values vertex = _
    rw [trace.leftReadings_value]
  refine (congrArg Polygon.energyPrimitivePoint scalar).trans ?_
  dsimp only [Polygon.energyPrimitivePoint]
  rw [conjugate_combination]
  rfl

/-- The actual right vertical energy-ribbon vertex reads the retained original seam value with those same coefficients.
-/
private theorem vertical_right_readback
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin ((PieceIndices.rows (partitions.get
      position)) + 1))
    (trace : (MatchedSides.verticalSeamSide energy position column row).Trace energy.depth)
    (ribbons : Data.Vector (BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ i, ribbons i = Trace.energyRibbon trace (cache.atDomain position sheet i).anchors
      (cache.atDomain position sheet i).offsets)
    (vertex : Fin (trace.vertices.rest.length + 1)) :
    Polygon.energyPrimitivePoint ((EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)).right
      vertex) =
      trace.rightValue (SeamAreas.seamValues (sheet := sheet) cache coefficients position) (trace.vertices.indexed
        vertex) := by
  let combined := EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)
  have scalar : combined.right vertex =
      FiniteSum.Fin.sumFin (fun i => coefficients i * (cache.atDomain position sheet i).anchors.alignedValue
        (cache.atDomain position sheet i).offsets
        ((MatchedSides.verticalSeamSide energy position column row).pieces (trace.vertices.indexed
          vertex).1).rightColumn
        ((MatchedSides.verticalSeamSide energy position column row).pieces (trace.vertices.indexed vertex).1).rightRow
        (trace.point (trace.vertices.indexed vertex))) := by
    rw [EnergyRibbonCombination.combine_right]
    apply FiniteSum.Fin.sumFin_congr
    intro i
    rw [readback i]
    change coefficients i * (trace.rightReadings _ _).values vertex = _
    rw [trace.rightReadings_value]
  refine (congrArg Polygon.energyPrimitivePoint scalar).trans ?_
  dsimp only [Polygon.energyPrimitivePoint]
  rw [conjugate_combination]
  rfl

/-- The original vertical face ribbon difference is its actual horizontal seam area minus the retained horizontal
endpoint correction. -/
theorem FaceAssembly.vertical_ribbon_difference (face : FaceAssembly perimeters position)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin ((PieceIndices.rows (partitions.get
      position)) + 1))
    (trace : (MatchedSides.verticalSeamSide energy position column row).Trace energy.depth)
    (ribbons : Data.Vector (BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ i, ribbons i = Trace.energyRibbon trace (cache.atDomain position sheet i).anchors
      (cache.atDomain position sheet i).offsets) :
    (EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i)).difference =
      Assembly.horizontalSeam (Perimeters.faceSides perimeters position) column row -
        BilinearGridBoundary.horizontalEndpoint face.corners column row := by
  have difference := EnergyRibbonReadback.difference_readback
    (EnergyRibbonCombination.combine (fun i => coefficients i) (fun i => ribbons i))
    (vertical_left_readback column row trace ribbons readback)
    (vertical_right_readback column row trace ribbons readback)
  exact difference.trans (congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a - b)
    (Perimeters.vertical_trace_area perimeters position column row trace)
    (FaceAssembly.vertical_trace_endpoint face column row trace))

/-- The retained horizontal face request pays the actual vertical seam area after its original endpoint correction.

The bound is homogeneous in the arbitrary coefficient vector and uses the same retained original energy ribbons and
numerical banks. -/
theorem FaceAssembly.horizontal_seam_bound (face : FaceAssembly perimeters position)
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) (row : Fin (PieceIndices.rows (partitions.get
      position)))
    (trace : (MatchedSides.horizontalSeamSide energy position column row).Trace energy.depth)
    {localTarget allowance : Fraction.Rational}
    (tolerance : DomainPrimitives.FaceExteriorTolerance (fixed.get position).get
      ((energy.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column row.succ))
        localTarget)
    (request : DomainMatchedEnergy.MatchedEnergyRequest (fixed.get position).get tolerance.slope
      ((energy.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column
        row.succ)).boundaryColumns trace.vertices.rest.length allowance)
    (later : request.models.index ≤ stage)
    (ribbons : Data.Vector (BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ i, ribbons i = Trace.energyRibbon trace (cache.atDomain position sheet i).anchors
      (cache.atDomain position sheet i).offsets) :
    Data.Gaussian.Norm.Basic.normSq
      (Assembly.verticalSeam (Perimeters.faceSides perimeters position) column row -
        BilinearGridBoundary.verticalEndpoint face.corners column row) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * allowance :=
        by
  have bound := request.horizontal_combination_bound tolerance trace later
    (fun i => cache.atDomain position sheet i) ribbons readback coefficients
  rw [Curves.Hyperelliptic.Meshes.Newton.Surface.SeamRibbons.FaceAssembly.horizontal_ribbon_difference face column row
    trace ribbons readback] at bound
  exact bound

/-- The retained vertical face request pays the actual horizontal seam area after its original endpoint correction.

The bound retains the original row schedule, energy ribbons, coefficient factors and common numerical bank. -/
theorem FaceAssembly.vertical_seam_bound (face : FaceAssembly perimeters position)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin ((PieceIndices.rows (partitions.get
      position)) + 1))
    (trace : (MatchedSides.verticalSeamSide energy position column row).Trace energy.depth)
    {localTarget allowance : Fraction.Rational}
    (tolerance : DomainPrimitives.FaceExteriorTolerance (fixed.get position).get
      ((energy.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column.castSucc row))
        localTarget)
    (request : DomainMatchedEnergy.MatchedEnergyRequest (fixed.get position).get tolerance.slope
      ((energy.meshes.get position).entries.get (PieceIndices.pieceIndex (partitions.get position) column.castSucc
        row)).boundaryRows trace.vertices.rest.length allowance)
    (later : request.models.index ≤ stage)
    (ribbons : Data.Vector (BoundaryRibbon.Ribbon trace.vertices.rest.length) genus)
    (readback : ∀ i, ribbons i = Trace.energyRibbon trace (cache.atDomain position sheet i).anchors
      (cache.atDomain position sheet i).offsets) :
    Data.Gaussian.Norm.Basic.normSq
      (Assembly.horizontalSeam (Perimeters.faceSides perimeters position) column row -
        BilinearGridBoundary.horizontalEndpoint face.corners column row) ≤
      (genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * allowance :=
        by
  have bound := request.vertical_combination_bound tolerance trace later
    (fun i => cache.atDomain position sheet i) ribbons readback coefficients
  rw [Curves.Hyperelliptic.Meshes.Newton.Surface.SeamRibbons.FaceAssembly.vertical_ribbon_difference face column row
    trace ribbons readback] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamRibbons
