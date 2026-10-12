module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences
public import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Paths.PreparedPathDecomposition
public import Purelib.Riemann.Paths.PreparedBoundarySegments
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.Newton.Band.Basic

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-! Newton density bounds on the actual fine perimeter vertices. The trace
owns its cell choices, including distinct readings at coincident junctions.
The supplied path reference retains its original preparation and root owner.
No new path, primitive model, or offset bank is constructed by these proofs. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonTraceReferences

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : Meshes.PuncturedGridFaces.RegularFace bank}
      {models
    : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames face}
  {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
  {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {entered : Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths.EnteredPath models piece.path differential
    parentSheet}
  {bandAmbient : Rational.Box} {current : State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {fixed : RootContinuation.NewtonBandDifferentials.DifferentialProfile profile differential.exponent}
  {target tolerance : Fraction.Rational}

variable {index : Nat} {cuts : Paths.RectangularSegmentSplitting.GridCuts entered.domain.geometry}
  {mesh : Meshes.RectangularObservationMesh.ObservationMesh cuts face.cell.box}

/-- Retain the squared subsegment length in the bottom perimeter estimate. -/
theorem newton_bottom_trace_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered tolerance)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives entered.domain differential index)
    (otherValues : Fin (entered.domain.steps + 1) → Fin (entered.domain.steps + 1) → Gaussian.Basic.Canonical →
      Gaussian.Basic.Canonical)
    (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh)
    (first last : Fin (traces.bottom.vertices.rest.length + 1))
    (firstEq : traces.bottom.point (traces.bottom.vertices.indexed first) = start)
    (lastEq : traces.bottom.point (traces.bottom.vertices.indexed last) = finish) :
    let values := fun column row point => (⟨otherValues column row point,
      data.anchors.alignedValue data.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq ((traces.bottom.leftValue values (traces.bottom.vertices.indexed last)).right -
      (traces.bottom.leftValue values (traces.bottom.vertices.indexed first)).right) ≤
        3 * tolerance + 4 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
          band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  intro values
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences.newton_point_density_bound reference band
    firstInside lastInside side later data
    (traces.bottom.leftReadings data.anchors data.offsets) first last firstEq lastEq
  rw [traces.bottom.leftReadings_value, traces.bottom.leftReadings_value] at estimate
  exact estimate

/-- Retain the squared subsegment length in the top perimeter estimate. -/
theorem newton_top_trace_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered tolerance)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives entered.domain differential index)
    (otherValues : Fin (entered.domain.steps + 1) → Fin (entered.domain.steps + 1) → Gaussian.Basic.Canonical →
      Gaussian.Basic.Canonical)
    (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh)
    (first last : Fin (traces.top.vertices.rest.length + 1))
    (firstEq : traces.top.point (traces.top.vertices.indexed first) = start)
    (lastEq : traces.top.point (traces.top.vertices.indexed last) = finish) :
    let values := fun column row point => (⟨otherValues column row point,
      data.anchors.alignedValue data.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq ((traces.top.leftValue values (traces.top.vertices.indexed last)).right -
      (traces.top.leftValue values (traces.top.vertices.indexed first)).right) ≤
        3 * tolerance + 4 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
          band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  intro values
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences.newton_point_density_bound reference band
    firstInside lastInside side later data
    (traces.top.leftReadings data.anchors data.offsets) first last firstEq lastEq
  rw [traces.top.leftReadings_value, traces.top.leftReadings_value] at estimate
  exact estimate

/-- Retain the squared subsegment length in the left perimeter estimate. -/
theorem newton_left_trace_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered tolerance)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives entered.domain differential index)
    (otherValues : Fin (entered.domain.steps + 1) → Fin (entered.domain.steps + 1) → Gaussian.Basic.Canonical →
      Gaussian.Basic.Canonical)
    (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh)
    (first last : Fin (traces.left.vertices.rest.length + 1))
    (firstEq : traces.left.point (traces.left.vertices.indexed first) = start)
    (lastEq : traces.left.point (traces.left.vertices.indexed last) = finish) :
    let values := fun column row point => (⟨otherValues column row point,
      data.anchors.alignedValue data.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq ((traces.left.leftValue values (traces.left.vertices.indexed last)).right -
      (traces.left.leftValue values (traces.left.vertices.indexed first)).right) ≤
        3 * tolerance + 4 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
          band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  intro values
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences.newton_point_density_bound reference band
    firstInside lastInside side later data
    (traces.left.leftReadings data.anchors data.offsets) first last firstEq lastEq
  rw [traces.left.leftReadings_value, traces.left.leftReadings_value] at estimate
  exact estimate

/-- Retain the squared subsegment length in the right perimeter estimate. -/
theorem newton_right_trace_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered tolerance)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives entered.domain differential index)
    (otherValues : Fin (entered.domain.steps + 1) → Fin (entered.domain.steps + 1) → Gaussian.Basic.Canonical →
      Gaussian.Basic.Canonical)
    (traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh)
    (first last : Fin (traces.right.vertices.rest.length + 1))
    (firstEq : traces.right.point (traces.right.vertices.indexed first) = start)
    (lastEq : traces.right.point (traces.right.vertices.indexed last) = finish) :
    let values := fun column row point => (⟨otherValues column row point,
      data.anchors.alignedValue data.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq ((traces.right.leftValue values (traces.right.vertices.indexed last)).right -
      (traces.right.leftValue values (traces.right.vertices.indexed first)).right) ≤
        3 * tolerance + 4 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
          band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  intro values
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.NewtonPointReferences.newton_point_density_bound reference band
    firstInside lastInside side later data
    (traces.right.leftReadings data.anchors data.offsets) first last firstEq lastEq
  rw [traces.right.leftReadings_value, traces.right.leftReadings_value] at estimate
  exact estimate

/-- The centered bottom sample uses the very owners and values of the fine
perimeter. The other differential's cached values are arbitrary and retained. -/
theorem newton_bottom_centered_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered tolerance)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives entered.domain differential index)
    (otherValues : Fin (entered.domain.steps + 1) → Fin (entered.domain.steps + 1) → Gaussian.Basic.Canonical →
      Gaussian.Basic.Canonical)
    {traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh}
    (samples : Integration.RectangularCenteredPerimeter.Centered traces (fun column row point =>
      ⟨otherValues column row point, data.anchors.alignedValue data.offsets column row point⟩))
    (vertex : Fin (traces.bottom.vertices.rest.length + 1))
    (firstEq : traces.bottom.point (traces.bottom.vertices.indexed 0) = start)
    (lastEq : traces.bottom.point (traces.bottom.vertices.indexed vertex) = finish) :
    Data.Gaussian.Norm.Basic.normSq (samples.bottom.centered vertex).right ≤
      3 * tolerance + 4 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
        band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  rw [samples.bottom.centered_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonTraceReferences.newton_bottom_trace_density_bound reference band
    firstInside lastInside side later data
    otherValues traces 0 vertex firstEq lastEq

/-- The centered top sample uses the very owners and values of the fine
perimeter. The other differential's cached values are arbitrary and retained. -/
theorem newton_top_centered_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered tolerance)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives entered.domain differential index)
    (otherValues : Fin (entered.domain.steps + 1) → Fin (entered.domain.steps + 1) → Gaussian.Basic.Canonical →
      Gaussian.Basic.Canonical)
    {traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh}
    (samples : Integration.RectangularCenteredPerimeter.Centered traces (fun column row point =>
      ⟨otherValues column row point, data.anchors.alignedValue data.offsets column row point⟩))
    (vertex : Fin (traces.top.vertices.rest.length + 1))
    (firstEq : traces.top.point (traces.top.vertices.indexed 0) = start)
    (lastEq : traces.top.point (traces.top.vertices.indexed vertex) = finish) :
    Data.Gaussian.Norm.Basic.normSq (samples.top.centered vertex).right ≤
      3 * tolerance + 4 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
        band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  rw [samples.top.centered_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonTraceReferences.newton_top_trace_density_bound reference band
    firstInside lastInside side later data
    otherValues traces 0 vertex firstEq lastEq

/-- The centered left sample uses the very owners and values of the fine
perimeter. The other differential's cached values are arbitrary and retained. -/
theorem newton_left_centered_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered tolerance)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives entered.domain differential index)
    (otherValues : Fin (entered.domain.steps + 1) → Fin (entered.domain.steps + 1) → Gaussian.Basic.Canonical →
      Gaussian.Basic.Canonical)
    {traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh}
    (samples : Integration.RectangularCenteredPerimeter.Centered traces (fun column row point =>
      ⟨otherValues column row point, data.anchors.alignedValue data.offsets column row point⟩))
    (vertex : Fin (traces.left.vertices.rest.length + 1))
    (firstEq : traces.left.point (traces.left.vertices.indexed 0) = start)
    (lastEq : traces.left.point (traces.left.vertices.indexed vertex) = finish) :
    Data.Gaussian.Norm.Basic.normSq (samples.left.centered vertex).right ≤
      3 * tolerance + 4 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
        band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  rw [samples.left.centered_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonTraceReferences.newton_left_trace_density_bound reference band
    firstInside lastInside side later data
    otherValues traces 0 vertex firstEq lastEq

/-- The centered right sample uses the very owners and values of the fine
perimeter. The other differential's cached values are arbitrary and retained. -/
theorem newton_right_centered_density_bound (reference :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference entered tolerance)
    (band : RootContinuation.PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : Paths.PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ index)
    (data : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives entered.domain differential index)
    (otherValues : Fin (entered.domain.steps + 1) → Fin (entered.domain.steps + 1) → Gaussian.Basic.Canonical →
      Gaussian.Basic.Canonical)
    {traces : Paths.RectangularPerimeterTraces.PerimeterTraces mesh}
    (samples : Integration.RectangularCenteredPerimeter.Centered traces (fun column row point =>
      ⟨otherValues column row point, data.anchors.alignedValue data.offsets column row point⟩))
    (vertex : Fin (traces.right.vertices.rest.length + 1))
    (firstEq : traces.right.point (traces.right.vertices.indexed 0) = start)
    (lastEq : traces.right.point (traces.right.vertices.indexed vertex) = finish) :
    Data.Gaussian.Norm.Basic.normSq (samples.right.centered vertex).right ≤
      3 * tolerance + 4 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed
        band.error * Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  rw [samples.right.centered_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.NewtonTraceReferences.newton_right_trace_density_bound reference band
    firstInside lastInside side later data
    otherValues traces 0 vertex firstEq lastEq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonTraceReferences
