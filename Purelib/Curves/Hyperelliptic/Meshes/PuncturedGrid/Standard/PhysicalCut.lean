module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CanonicalCut
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChordPeriods
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
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
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

open Purelib

public section

/-! Actual standard periods in cut coordinates after paying signed-face
corrections. The physical row remains explicit and is not inferred to vanish
from a root-closed or coordinate-closed period path. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalCut

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row : TourIntersection.IntersectionRow
    lifted integral index}
  {minimum : Nat} {target : Fraction.Rational} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {extraPoints : List Gaussian.Basic.Canonical}

/-- Pay removal of the complete signed-face correction from a Gaussian comparison using its retained smallness bound. -/
private theorem remove_faces {value faces sample : Gaussian.Basic.Canonical} {inner : Fraction.Rational}
    (positive : 0 < inner) (original : Gaussian.Norm.Basic.normSq (value + faces - sample) < inner)
    (small : Gaussian.Norm.Basic.normSq faces < inner / 16) : Gaussian.Norm.Basic.normSq (value -
      sample) < 4 * inner := by
  have reversed : Gaussian.Norm.Basic.normSq (-faces) < inner / 16 := by
    rw [Gaussian.Norm.Basic.normSq_neg]
    exact small
  have equal : value - sample = (value + faces - sample) + -faces := by ring1
  rw [equal]
  have bounded := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct original reversed))
  have allowance : inner / 16 ≤ inner := Fraction.Order.Field.divide_le_self positive.le (by decide)
  exact bounded.trans_le ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show inner + inner / 16 ≤ inner + inner from add_le_add le_rfl allowance) (by
        decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))

/-- The actual a-cycle signed-face correction meets its allocated sixteenth of the target. -/
theorem a_faces_small (readings : BoundaryReadings.StandardBoundaryReadings
  row differential minimum target domains extraPoints) :
    Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.faceValue
      lifted.mesh.triangulation.faces (CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values)
      row.coordinates.routes.a.correction) < target / 16 :=
  readings.aFaceRequest.accurate readings.aFaces_later readings.triangles

/-- The actual b-cycle signed-face correction meets its allocated sixteenth of the target. -/
theorem b_faces_small (readings : BoundaryReadings.StandardBoundaryReadings
  row differential minimum target domains extraPoints) :
    Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.faceValue
      lifted.mesh.triangulation.faces (CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values)
      row.coordinates.routes.b.correction) < target / 16 :=
  readings.bFaceRequest.accurate readings.bFaces_later readings.triangles

variable
  {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
  (normal : NormalForm integral.paired raw)
  (period : PreparedCycleModels.RootClosedPeriodRow curve)
  (periodEq : period = (PreparedCycleModels.RootClosedPeriodBank.ofData curve
    branches).rows index)

/-- A quarter-sized internal request pays both original standard-period
comparison and the entire actual signed-face correction below the target. -/
theorem a_physical_spanning_accurate
    (readings : BoundaryReadings.StandardBoundaryReadings
      (TourIntersection.IntersectionRow.ofPeriod lifted integral normal
      index period periodEq)
      differential minimum (target / 4) domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    let row := TourIntersection.IntersectionRow.ofPeriod lifted integral
      normal index period periodEq
    let value := CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values
    Gaussian.Norm.Basic.normSq ((WordCoordinates.combine
      row.span.a.coefficients (fun index => WordCoordinates.combine
      (integral.paired index)
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
      WordCoordinates.combine row.span.a.physical
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential
        index).integral.model stage).integralSample) < target := by
  have bounded := PhysicalCut.remove_faces readings.positive
    (CanonicalCut.a_spanning_accurate normal period periodEq readings stage
      later) (PhysicalCut.a_faces_small readings)
  exact bounded.trans_eq ((by ring1 : 4 * (target / 4) = (target / 4) * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- A quarter-sized internal request pays both original standard-period
comparison and the entire actual signed-face correction below the target. -/
theorem b_physical_spanning_accurate
    (readings : BoundaryReadings.StandardBoundaryReadings
      (TourIntersection.IntersectionRow.ofPeriod lifted integral normal
      index period periodEq)
      differential minimum (target / 4) domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    let row := TourIntersection.IntersectionRow.ofPeriod lifted integral
      normal index period periodEq
    let value := CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values
    Gaussian.Norm.Basic.normSq ((WordCoordinates.combine
      row.span.b.coefficients (fun index => WordCoordinates.combine
      (integral.paired index)
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
      WordCoordinates.combine row.span.b.physical
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential
        index).integral.model stage).integralSample) < target := by
  have bounded := PhysicalCut.remove_faces readings.positive
    (CanonicalCut.b_spanning_accurate normal period periodEq readings stage
      later) (PhysicalCut.b_faces_small readings)
  exact bounded.trans_eq ((by ring1 : 4 * (target / 4) = (target / 4) * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- The same estimate consumes the actual chord-program bank used in the
normal-form area assembly, including its corrected physical coefficients. -/
theorem a_chord_chain_accurate
    {source : Differentials.Basic.Differential genus}
    {prepared : Cut.CyclePrograms.CutChordPrograms lifted source}
    {components : Cut.ChainPeriods.ComponentSamples prepared.programs differential}
    (periods : TourChordPeriods.ChordPeriods
      (TourIntersection.IntersectionRow.ofPeriod lifted integral normal
        index period periodEq).span prepared components)
    (readings : BoundaryReadings.StandardBoundaryReadings
      (TourIntersection.IntersectionRow.ofPeriod lifted integral normal
      index period periodEq)
      differential minimum (target / 4) domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    let value := CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values
    Gaussian.Norm.Basic.normSq ((Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue periods.a.chain value
      + WordCoordinates.combine periods.aGeometry.physical
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential
        index).integral.model stage).integralSample) < target := by
  have original := CanonicalCut.a_valuation_accurate normal period periodEq
    readings stage later
  rw [periods.a_value (CanonicalEdgeValues.edgeValuation lifted.mesh
    readings.triangles.values)
    (CanonicalEdgeValues.edgeValuation_reverse lifted.mesh
      readings.triangles.values)] at original
  have bounded := PhysicalCut.remove_faces readings.positive original
    (PhysicalCut.a_faces_small readings)
  exact bounded.trans_eq ((by ring1 : 4 * (target / 4) = (target / 4) * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- The same estimate consumes the actual chord-program bank used in the
normal-form area assembly, including its corrected physical coefficients. -/
theorem b_chord_chain_accurate
    {source : Differentials.Basic.Differential genus}
    {prepared : Cut.CyclePrograms.CutChordPrograms lifted source}
    {components : Cut.ChainPeriods.ComponentSamples prepared.programs differential}
    (periods : TourChordPeriods.ChordPeriods
      (TourIntersection.IntersectionRow.ofPeriod lifted integral normal
        index period periodEq).span prepared components)
    (readings : BoundaryReadings.StandardBoundaryReadings
      (TourIntersection.IntersectionRow.ofPeriod lifted integral normal
      index period periodEq)
      differential minimum (target / 4) domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    let value := CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.triangles.values
    Gaussian.Norm.Basic.normSq ((Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue periods.b.chain value
      + WordCoordinates.combine periods.bGeometry.physical
        (fun column => value (OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential
        index).integral.model stage).integralSample) < target := by
  have original := CanonicalCut.b_valuation_accurate normal period periodEq
    readings stage later
  rw [periods.b_value (CanonicalEdgeValues.edgeValuation lifted.mesh
    readings.triangles.values)
    (CanonicalEdgeValues.edgeValuation_reverse lifted.mesh
      readings.triangles.values)] at original
  have bounded := PhysicalCut.remove_faces readings.positive original
    (PhysicalCut.b_faces_small readings)
  exact bounded.trans_eq ((by ring1 : 4 * (target / 4) = (target / 4) * 4).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PhysicalCut
