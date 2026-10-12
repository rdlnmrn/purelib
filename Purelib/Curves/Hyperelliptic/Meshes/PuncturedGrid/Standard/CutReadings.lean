module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedBoundary
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Rational.Budget.Aggregate
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-! Standard period samples read in the actual cut coordinates. Physical,
signed-face and chart-change terms remain separate executable caches.
Chart-change charges record the actual retained occurrences; they are not
assumed to vanish when a coordinate path closes. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.PathFaces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (PathFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Canonical} {path
    : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}

/-- The finite sum of retained route discrepancies is the reading sum minus the indexed edge-word value. -/
theorem valuation_difference (assigned : LiftedMesh.PathFaces mesh path)
    (reading : (edge : Stokes.OrientedEdge vertices.count) → MeshPathWalks.EdgeRoute mesh edge →
      Data.Gaussian.Basic.Canonical)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun edge route => reading edge route - value edge) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values reading) - SewingRetraction.wordValue value
        assigned.indexed := by
  induction assigned with
  | nil => change (0 : Data.Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons first rest ih =>
      change (_ - _) + _ = (_ + _) - (_ + _)
      rw [ih]
      ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.PathFaces

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings (StandardBoundaryReadings)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedRefinementPrograms (rawPeriodDataOfData)
open Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
open Purelib.Topology.Surface.Sewing.VertexSewing.OrientedEdge (map)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.GroupedBoundary (a_boundary_error_ofPeriod
  b_boundary_error_ofPeriod)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row :
    IntersectionRow lifted integral index}
  {minimum : Nat} {target : Rational} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {extraPoints : List Gaussian}

set_option genInjectivity false in
/-- One corrected cut-coordinate reading. The full occurrence list and its finite Cauchy--Schwarz charge are retained
for the subsequent seam budget. -/
structure CutReading (handle physical faces : Gaussian) (increments : List Gaussian)
    (expected : Gaussian) where
  /-- The retained chart-change increments in their original occurrence order. -/ changes : List Gaussian
  /-- The retained changes are exactly the supplied increments. -/ changes_eq : changes = increments
  /-- The cached total chart-change correction. -/ correction : Gaussian
  /-- The correction is the Gaussian sum of the retained changes. -/ correction_eq : correction =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum changes
  /-- The cached finite squared-norm charge for the chart changes. -/ charge : Fraction.Rational
  /-- The charge is the occurrence count times the sum of squared increment norms. -/ charge_eq : charge =
    (changes.length : Fraction.Rational) * Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum changes
  /-- The squared norm of the correction is at most its retained finite charge. -/ correction_bound :
    Data.Gaussian.Norm.Basic.normSq correction ≤ charge
  /-- The cached complete corrected cut-coordinate value. -/ total : Gaussian
  /-- The total retains handle, physical, signed-face and chart-change contributions separately. -/ total_eq : total =
    handle + physical + faces + correction
  /-- The complete corrected value equals the original expected reading. -/ expected_eq : total = expected

constructive_injectivity CutReading

/-- Removing the chart correction costs its retained finite charge. The physical and signed-face terms are still part of
the cut expression. -/
theorem CutReading.comparison_bound {handle physical faces expected sample : Gaussian}
    {increments : List Gaussian} (reading :
      CutReading handle physical faces
      increments expected)
    {target : Fraction.Rational} (accurate : Data.Gaussian.Norm.Basic.normSq (expected - sample) < target) :
    Data.Gaussian.Norm.Basic.normSq (handle + physical + faces - sample) < 2 * (reading.charge + target) := by
  have equal : handle + physical + faces - sample =
      -reading.correction + (expected - sample) := by
    calc
      _ = -reading.correction + (handle + physical + faces + reading.correction - sample) := by ring1
      _ = _ := congrArg (fun scalar => -reading.correction + (scalar - sample))
        (reading.total_eq.symm.trans reading.expected_eq)
  rw [equal]
  have correction := reading.correction_bound
  have bounded := Data.Gaussian.Norm.Bounds.normSq_add_le_two
    (-reading.correction) (expected - sample)
  rw [Data.Gaussian.Norm.Basic.normSq_neg] at bounded
  apply bounded.trans_lt
  apply Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
  exact (Fraction.Order.Arithmetic.add_le_add_right_direct correction _).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct accurate reading.charge)

namespace StandardBoundaryReadings

variable (readings :
  StandardBoundaryReadings row differential
  minimum target domains extraPoints)
  (value : Purelib.Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian)
  (anti : ∀ edge, value edge.reverse = -value edge)

/-- Read the actual A spanning coefficients, physical row and signed face correction together with the retained
primitive-chart changes. -/
@[expose] def a_cutReading :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow.CutReading
      (WordCoordinates.combine row.span.a.coefficients (fun index => WordCoordinates.combine (integral.paired index)
        (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)))))
      (WordCoordinates.combine row.span.a.physical
        (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column))))
      (SewingRetraction.faceValue lifted.mesh.triangulation.faces value row.coordinates.routes.a.correction)
      (row.pair.aFaces.geometry.values fun edge route => route.sourceEdge.increment readings.triangles.values - value
        edge)
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (row.pair.aFaces.geometry.values fun _ route =>
        route.sourceEdge.increment readings.triangles.values)) := by
  let changes := row.pair.aFaces.geometry.values fun edge route => route.sourceEdge.increment readings.triangles.values
    - value edge
  let correction := Data.Gaussian.Norm.Sum.Basic.gaussianSum changes
  refine ⟨changes, rfl, correction, rfl,
    (changes.length : Fraction.Rational) * Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum changes, rfl,
    (by
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
          using Data.Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le changes), _, rfl, ?_⟩
  rw [← row.span.a_value value anti]
  have equal := Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.PathFaces.valuation_difference
    row.pair.aFaces.geometry
    (fun _ route => route.sourceEdge.increment readings.triangles.values) value
  change SewingRetraction.wordValue value row.pair.aFaces.geometry.indexed +
    Data.Gaussian.Norm.Sum.Basic.gaussianSum changes = _
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum changes = _ at equal
  rw [equal]
  ring1

/-- Read the actual B spanning coefficients, physical row and signed face correction together with the retained
primitive-chart changes. -/
@[expose] def b_cutReading :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow.CutReading
      (WordCoordinates.combine row.span.b.coefficients (fun index => WordCoordinates.combine (integral.paired index)
        (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)))))
      (WordCoordinates.combine row.span.b.physical
        (fun column => value (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column))))
      (SewingRetraction.faceValue lifted.mesh.triangulation.faces value row.coordinates.routes.b.correction)
      (row.pair.bFaces.geometry.values fun edge route => route.sourceEdge.increment readings.triangles.values - value
        edge)
      (Data.Gaussian.Norm.Sum.Basic.gaussianSum (row.pair.bFaces.geometry.values fun _ route =>
        route.sourceEdge.increment readings.triangles.values)) := by
  let changes := row.pair.bFaces.geometry.values fun edge route => route.sourceEdge.increment readings.triangles.values
    - value edge
  let correction := Data.Gaussian.Norm.Sum.Basic.gaussianSum changes
  refine ⟨changes, rfl, correction, rfl,
    (changes.length : Fraction.Rational) * Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum changes, rfl,
    (by
        simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
          using Data.Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le changes), _, rfl, ?_⟩
  rw [← row.span.b_value value anti]
  have equal := Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.PathFaces.valuation_difference
    row.pair.bFaces.geometry
    (fun _ route => route.sourceEdge.increment readings.triangles.values) value
  change SewingRetraction.wordValue value row.pair.bFaces.geometry.indexed +
    Data.Gaussian.Norm.Sum.Basic.gaussianSum changes = _
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum changes = _ at equal
  rw [equal]
  ring1

variable
  {raw : List (Purelib.LinearAlgebra.Alternating.Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
  (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
  (period : Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodRow curve)
  (periodEq : period =
    (Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve
    branches).rows index)

/-- The complete corrected cut expression approximates the original standard A program on every later stage. No
transport equality is requested. -/
theorem a_cutReading_accurate
    (readings : BoundaryReadings.StandardBoundaryReadings (IntersectionRow.ofPeriod lifted integral normal index period
      periodEq)
      differential minimum target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      ((a_cutReading
      readings value anti).total -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential index).integral.model
        stage).integralSample) < target := by
  rw
    [(a_cutReading
    readings value anti).expected_eq]
  exact GroupedBoundary.a_boundary_error_ofPeriod normal period periodEq readings stage later

/-- The complete corrected cut expression approximates the original standard B program on every later stage. No
transport equality is requested. -/
theorem b_cutReading_accurate
    (readings : BoundaryReadings.StandardBoundaryReadings (IntersectionRow.ofPeriod lifted integral normal index period
      periodEq)
      differential minimum target domains extraPoints)
    (stage : Nat) (later : readings.original.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      ((b_cutReading
      readings value anti).total -
      (((PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential index).integral.model
        stage).integralSample) < target := by
  rw
    [(b_cutReading
    readings value anti).expected_eq]
  exact GroupedBoundary.b_boundary_error_ofPeriod normal period periodEq readings stage later

end StandardBoundaryReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CutReadings.IntersectionRow
