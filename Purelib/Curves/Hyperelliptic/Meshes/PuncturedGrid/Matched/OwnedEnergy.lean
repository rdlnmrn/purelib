module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
public import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy
import Purelib.Riemann.Integration.RectangularMatchedCenteredPerimeters
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Integration.RectangularMatchedCornerReadback

public section

/-! Homogeneous contact requests control the actual retained owned perimeter
samples, using the same local primitive banks and all endpoint corrections. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Algebra
open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib
open Purelib.Data.Rat

open Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces (topOwned bottomOwned rightOwned leftOwned)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {firstSheet secondSheet
    : Fin 2}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

namespace OwnedEnergy.MatchedEnergy

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

/-- The homogeneous conjugate pair of aligned primitive readings on the same original domain and coefficient vector. -/
@[expose] def values {stage : Nat}
    (data : (i : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain
      (Periods.PeriodMatrix.standardDifferential i) stage)
    (coefficients : Fin genus → Gaussian.Basic.Canonical)
    (column row : Fin (leftDomain.steps + 1)) (point : Gaussian.Basic.Canonical) : PrimitivePoint :=
  ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj ((data
    i).anchors.alignedValue (data i).offsets column row point)),
    FiniteSum.Fin.sumFin (fun i => coefficients i * (data i).anchors.alignedValue (data i).offsets column row point)⟩

end OwnedEnergy.MatchedEnergy

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
attribute [local congr] FiniteSum.Fin.sumFin_congr

section
variable {leftBox rightBox : Rational.Box}
  {leftMesh : Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {coordinate : Normalization.InverseRootPolynomial.Coordinate}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide leftMesh rightMesh
    (Fin.cast leftMesh.boundaryRows_eq (Fin.last leftMesh.boundaryRows))
    (Fin.cast rightMesh.boundaryRows_eq 0) coordinate}
  {depth : Nat} {trace : side.Trace depth}
  {preparation : Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation trace}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The original horizontal contact request bounds the actual owned top-minus-bottom centered energy difference with the
same homogeneous coefficient factor. -/
theorem
  ConjugateEnergy.MatchedSidePreparation.EnergyRequest.owned_accurate
    (request : Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateEnergy.MatchedSidePreparation.EnergyRequest
      preparation target floor)
    {stage : Nat} (later : request.index ≤ stage)
    (leftData : (i : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain
      (Periods.PeriodMatrix.standardDifferential i) stage)
    (rightData : (i : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain
      (Periods.PeriodMatrix.standardDifferential i) stage)
    (coefficients : Fin genus → Gaussian.Basic.Canonical)
    (leftTraces : Paths.RectangularPerimeterTraces.PerimeterTraces leftMesh)
    (rightTraces : Paths.RectangularPerimeterTraces.PerimeterTraces rightMesh)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => let owner :=
      (Paths.RectangularOwnedPerimeterTraces.topOwned leftTraces).indexed vertex
      Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values leftData coefficients owner.column
        owner.row owner.point))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => let owner :=
      (Paths.RectangularOwnedPerimeterTraces.bottomOwned rightTraces).indexed vertex
      Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values rightData coefficients owner.column
        owner.row owner.point))
    (leftAssembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly leftMesh
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values leftData coefficients))
    (rightAssembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly rightMesh
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values rightData coefficients))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter)
    (leftDepth : depth = leftMesh.depth) (rightDepth : depth = rightMesh.depth)
    (leftEdge : coordinate = leftBox.yUpper) (rightEdge : coordinate = rightBox.yLower) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : Normalization.InverseRootPolynomial.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun i =>
        Data.Gaussian.Norm.Basic.normSq (coefficients i)))^2 * target := by
  let leftReading := Periods.CenteredBilinearPath.Sample.build (fun vertex => (⟨
    FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
      ((trace.leftReadings (leftData i).anchors (leftData i).offsets).values vertex)),
    FiniteSum.Fin.sumFin (fun i => coefficients i * (trace.leftReadings (leftData i).anchors (leftData
      i).offsets).values vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))
  let rightReading := Periods.CenteredBilinearPath.Sample.build (fun vertex => (⟨
    FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
      ((trace.rightReadings (rightData i).anchors (rightData i).offsets).values vertex)),
    FiniteSum.Fin.sumFin (fun i => coefficients i * (trace.rightReadings (rightData i).anchors (rightData
      i).offsets).values vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))
  let leftMatched := Periods.CenteredBilinearPath.Sample.build (fun vertex => trace.leftValue
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values leftData coefficients)
    (trace.vertices.indexed vertex))
  let rightMatched := Periods.CenteredBilinearPath.Sample.build (fun vertex => trace.rightValue
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values rightData coefficients)
    (trace.vertices.indexed vertex))
  have leftEq : leftReading.centeredArea = leftMatched.centeredArea := by
    apply Riemann.Periods.CenteredBilinearPath.Sample.centeredArea_congr
    intro vertex
    simp only [Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values,
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.leftValue,
      trace.leftReadings_value, -eq_self, -iff_self]
    rfl
  have rightEq : rightReading.centeredArea = rightMatched.centeredArea := by
    apply Riemann.Periods.CenteredBilinearPath.Sample.centeredArea_congr
    intro vertex
    simp only [Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values,
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide.Trace.rightValue,
      trace.rightReadings_value, -eq_self, -iff_self]
    rfl
  have leftOwned := Integration.RectangularMatchedCenteredPerimeters.MatchedHorizontalSide.Trace.left_centered_top trace
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values leftData coefficients) leftMatched
    leftTraces left leftAssembly leftPerimeter leftEdge leftDepth
  have rightOwned := Integration.RectangularMatchedCenteredPerimeters.MatchedHorizontalSide.Trace.right_centered_bottom
    trace (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values rightData coefficients)
    rightMatched
    rightTraces right rightAssembly rightPerimeter rightEdge rightDepth
  have bound := request.accurate later leftData rightData coefficients
    (fun _ _ => Periods.CenteredBilinearPath.Sample.build _) (fun _ _ => Periods.CenteredBilinearPath.Sample.build _)
      leftReading rightReading
  rw [leftEq, rightEq, leftOwned, rightOwned] at bound
  exact bound

end

section
variable {leftBox rightBox : Rational.Box}
  {leftMesh : Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {coordinate : Normalization.InverseRootPolynomial.Coordinate}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide leftMesh rightMesh
    (Fin.cast leftMesh.boundaryColumns_eq (Fin.last leftMesh.boundaryColumns))
    (Fin.cast rightMesh.boundaryColumns_eq 0) coordinate}
  {depth : Nat} {trace : side.Trace depth}
  {preparation : Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation.MatchedVerticalSidePreparation
    trace}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The original vertical contact request bounds the actual owned right-minus-left centered energy difference with the
same homogeneous coefficient factor. -/
theorem
  VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyRequest.owned_accurate
    (request :
      Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateEnergy.MatchedVerticalSidePreparation.EnergyRequest
      preparation target floor)
    {stage : Nat} (later : request.index ≤ stage)
    (leftData : (i : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain
      (Periods.PeriodMatrix.standardDifferential i) stage)
    (rightData : (i : Fin genus) → Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain
      (Periods.PeriodMatrix.standardDifferential i) stage)
    (coefficients : Fin genus → Gaussian.Basic.Canonical)
    (leftTraces : Paths.RectangularPerimeterTraces.PerimeterTraces leftMesh)
    (rightTraces : Paths.RectangularPerimeterTraces.PerimeterTraces rightMesh)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => let owner := (rightOwned leftTraces).indexed vertex
      Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values leftData coefficients owner.column
        owner.row owner.point))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => let owner := (leftOwned rightTraces).indexed vertex
      Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values rightData coefficients owner.column
        owner.row owner.point))
    (leftAssembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly leftMesh
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values leftData coefficients))
    (rightAssembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly rightMesh
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values rightData coefficients))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter)
    (leftDepth : depth = leftMesh.depth) (rightDepth : depth = rightMesh.depth)
    (leftEdge : coordinate = leftBox.xUpper) (rightEdge : coordinate = rightBox.xLower) :
    Data.Gaussian.Norm.Basic.normSq (left.centeredArea - right.centeredArea) ≤
      (genus : Normalization.InverseRootPolynomial.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun i =>
        Data.Gaussian.Norm.Basic.normSq (coefficients i)))^2 * target := by
  let leftReading := Periods.CenteredBilinearPath.Sample.build (fun vertex => (⟨
    FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
      ((trace.leftReadings (leftData i).anchors (leftData i).offsets).values vertex)),
    FiniteSum.Fin.sumFin (fun i => coefficients i * (trace.leftReadings (leftData i).anchors (leftData
      i).offsets).values vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))
  let rightReading := Periods.CenteredBilinearPath.Sample.build (fun vertex => (⟨
    FiniteSum.Fin.sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
      ((trace.rightReadings (rightData i).anchors (rightData i).offsets).values vertex)),
    FiniteSum.Fin.sumFin (fun i => coefficients i * (trace.rightReadings (rightData i).anchors (rightData
      i).offsets).values vertex)⟩ : Topology.Polygon.Stokes.PrimitivePoint))
  let leftMatched := Periods.CenteredBilinearPath.Sample.build (fun vertex => trace.leftValue
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values leftData coefficients)
    (trace.vertices.indexed vertex))
  let rightMatched := Periods.CenteredBilinearPath.Sample.build (fun vertex => trace.rightValue
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values rightData coefficients)
    (trace.vertices.indexed vertex))
  have leftEq : leftReading.centeredArea = leftMatched.centeredArea := by
    apply Riemann.Periods.CenteredBilinearPath.Sample.centeredArea_congr
    intro vertex
    simp only [Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values,
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.leftValue,
      trace.leftReadings_value, -eq_self, -iff_self]
    rfl
  have rightEq : rightReading.centeredArea = rightMatched.centeredArea := by
    apply Riemann.Periods.CenteredBilinearPath.Sample.centeredArea_congr
    intro vertex
    simp only [Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values,
      Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide.Trace.rightValue,
      trace.rightReadings_value, -eq_self, -iff_self]
    rfl
  have leftOwned := Integration.RectangularMatchedCenteredPerimeters.MatchedVerticalSide.Trace.left_centered_right trace
    (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values leftData coefficients) leftMatched
    leftTraces left leftAssembly leftPerimeter leftEdge leftDepth
  have rightOwned := Integration.RectangularMatchedCenteredPerimeters.MatchedVerticalSide.Trace.right_centered_left
    trace (Hyperelliptic.Meshes.PuncturedGrid.Matched.OwnedEnergy.MatchedEnergy.values rightData coefficients)
    rightMatched
    rightTraces right rightAssembly rightPerimeter rightEdge rightDepth
  have bound := request.accurate later leftData rightData coefficients
    (fun _ _ => Periods.CenteredBilinearPath.Sample.build _) (fun _ _ => Periods.CenteredBilinearPath.Sample.build _)
      leftReading rightReading
  rw [leftEq, rightEq, leftOwned, rightOwned] at bound
  exact bound

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
