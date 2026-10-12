module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

open Purelib

@[expose] public section

/-! The actual standard-period programs in one antisymmetric surface-edge
valuation. All chart changes are paid by requests made before the shared
bank. The cut formula retains physical and signed-face terms only. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow
    lifted integral index}
  {minimum : Nat} {target : Fraction.Rational} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {extraPoints : List Gaussian.Basic.Canonical}

/-- Four consecutive Gaussian errors below one sixteenth of a target compose to an error below that target. -/
private theorem compose {value corner mesh original sample : Gaussian.Basic.Canonical} {target : Fraction.Rational}
    (chart : Data.Gaussian.Norm.Basic.normSq (value - corner) < target / 16)
    (corners : Data.Gaussian.Norm.Basic.normSq (corner - mesh) < target / 16)
    (routes : Data.Gaussian.Norm.Basic.normSq (original - mesh) < target / 16)
    (period : Data.Gaussian.Norm.Basic.normSq (original - sample) < target / 16) :
      Data.Gaussian.Norm.Basic.normSq (value - sample) < target := by
  have reversed : Data.Gaussian.Norm.Basic.normSq (mesh - original) < target / 16 := by
    rw [show mesh - original = -(original - mesh) by ring1, Gaussian.Norm.Basic.normSq_neg]
    exact routes
  have left := (Gaussian.Norm.Bounds.normSq_add_le_two (value - corner) (corner - mesh)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct chart corners))
  have right := (Gaussian.Norm.Bounds.normSq_add_le_two (mesh - original) (original - sample)).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct reversed period))
  have equal : value - sample = ((value - corner) + (corner - mesh)) + ((mesh - original) + (original - sample)) := by
    ring1
  rw [equal]
  have paid := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct left right))
  exact paid.trans_eq ((by ring1 : _ = (target / 16) * 16).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- The retained canonical a-cycle chart charge is below its allocated sixteenth of the target. -/
theorem a_canonical_charge
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential
      minimum target domains extraPoints) :
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow.StandardBoundaryReadings.a_cutReading
      readings (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse lifted.mesh
        readings.triangles.values)).charge < target / 16 := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow.CutReading.charge_eq,
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow.CutReading.changes_eq]
  simpa only [Meshes.GridLiftedMesh.LiftedMesh.PathFaces.routeSpine_values] using
    readings.aCharts.charge_lt readings.aCharts_later readings.triangles

/-- The actual canonical a-cycle word and retained charted corner value differ by less than their allocated chart
allowance. -/
private theorem a_chart_error
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential
      minimum target domains extraPoints) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
      row.pair.aFaces.geometry.indexed -
      readings.a.cornerValue) < target / 16 := by
  rw [readings.a.cornerValue_eq_triangles readings.triangles]
  rw [show Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
    row.pair.aFaces.geometry.indexed -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (row.pair.aFaces.geometry.values fun _ route =>
        route.sourceEdge.increment readings.triangles.values) =
    -(Data.Gaussian.Norm.Sum.Basic.gaussianSum (row.pair.aFaces.geometry.values fun _ route =>
      route.sourceEdge.increment readings.triangles.values) -
      Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
        row.pair.aFaces.geometry.indexed) by ring1,
    Gaussian.Norm.Basic.normSq_neg, ←
      Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.PathFaces.valuation_difference]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le _).trans_lt
    (by
        simpa only [Meshes.GridLiftedMesh.LiftedMesh.PathFaces.routeSpine_values]
          using readings.aCharts.charge_lt readings.aCharts_later readings.triangles)

/-- The retained canonical b-cycle chart charge is below its allocated sixteenth of the target. -/
theorem b_canonical_charge
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential
      minimum target domains extraPoints) :
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow.StandardBoundaryReadings.b_cutReading
      readings (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse lifted.mesh
        readings.triangles.values)).charge < target / 16 := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow.CutReading.charge_eq,
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow.CutReading.changes_eq]
  simpa only [Meshes.GridLiftedMesh.LiftedMesh.PathFaces.routeSpine_values] using
    readings.bCharts.charge_lt readings.bCharts_later readings.triangles

/-- The actual canonical b-cycle word and retained charted corner value differ by less than their allocated chart
allowance. -/
private theorem b_chart_error
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings row differential
      minimum target domains extraPoints) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
      row.pair.bFaces.geometry.indexed -
      readings.b.cornerValue) < target / 16 := by
  rw [readings.b.cornerValue_eq_triangles readings.triangles]
  rw [show Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
    row.pair.bFaces.geometry.indexed -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (row.pair.bFaces.geometry.values fun _ route =>
        route.sourceEdge.increment readings.triangles.values) =
    -(Data.Gaussian.Norm.Sum.Basic.gaussianSum (row.pair.bFaces.geometry.values fun _ route =>
      route.sourceEdge.increment readings.triangles.values) -
      Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
        row.pair.bFaces.geometry.indexed) by ring1,
    Gaussian.Norm.Basic.normSq_neg, ←
      Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.PathFaces.valuation_difference]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le _).trans_lt
    (by
        simpa only [Meshes.GridLiftedMesh.LiftedMesh.PathFaces.routeSpine_values]
          using readings.bCharts.charge_lt readings.bCharts_later readings.triangles)

variable
  {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
  (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
  (period : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
  (periodEq : period = (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
    branches).rows index)

/-- Actual indexed edge valuation approximates the original A program,
with no caller valuation, antisymmetry proof, chart error, or floor. -/
theorem a_valuation_accurate
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal
      index period periodEq)
      differential minimum target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
        (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal
          index period periodEq).pair.aFaces.geometry.indexed -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential
        index).integral.model stage).integralSample) < target := by
  apply Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut.compose
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut.a_chart_error readings) (readings.a.accurate.trans_lt
    readings.a_small)
  · rw [Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.StandardBoundaryReadings.a_routes_value_ofPeriod
      normal period periodEq readings]
    exact readings.a_routes_accurate
  · exact readings.a_original_accurate stage later

/-- Full standard A cut-coordinate formula. Physical generators and
signed face corrections remain explicit; the chart-change error is paid. -/
theorem a_spanning_accurate
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal
      index period periodEq)
      differential minimum target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    let row := Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral
      normal index period periodEq
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values
    Data.Gaussian.Norm.Basic.normSq ((Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine
      row.span.a.coefficients (fun index => Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine
      (integral.paired index)
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine row.span.a.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
        row.coordinates.routes.a.correction) -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential
        index).integral.model stage).integralSample) < target := by
  dsimp only
  rw [← (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal
    index period periodEq).span.a_value
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse lifted.mesh
      readings.triangles.values)]
  exact Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut.a_valuation_accurate normal period periodEq readings
    stage later

/-- Actual indexed edge valuation approximates the original B program,
with no caller valuation, antisymmetry proof, chart error, or floor. -/
theorem b_valuation_accurate
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal
      index period periodEq)
      differential minimum target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
        (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal
          index period periodEq).pair.bFaces.geometry.indexed -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential
        index).integral.model stage).integralSample) < target := by
  apply Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut.compose
    (Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut.b_chart_error readings) (readings.b.accurate.trans_lt
    readings.b_small)
  · rw [Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedReadings.StandardBoundaryReadings.b_routes_value_ofPeriod
      normal period periodEq readings]
    exact readings.b_routes_accurate
  · exact readings.b_original_accurate stage later

/-- Full standard B cut-coordinate formula. Physical generators and
signed face corrections remain explicit; the chart-change error is paid. -/
theorem b_spanning_accurate
    (readings : Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings.StandardBoundaryReadings
      (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal
      index period periodEq)
      differential minimum target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    let row := Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral
      normal index period periodEq
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values
    Data.Gaussian.Norm.Basic.normSq ((Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine
      row.span.b.coefficients (fun index => Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine
      (integral.paired index)
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine row.span.b.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value
        row.coordinates.routes.b.correction) -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential
        index).integral.model stage).integralSample) < target := by
  dsimp only
  rw [← (Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow.ofPeriod lifted integral normal
    index period periodEq).span.b_value
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.triangles.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse lifted.mesh
      readings.triangles.values)]
  exact Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut.b_valuation_accurate normal period periodEq readings
    stage later

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut
