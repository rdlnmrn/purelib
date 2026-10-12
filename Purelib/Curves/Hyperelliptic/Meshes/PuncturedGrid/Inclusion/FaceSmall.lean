module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.List.Permutation
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FacePeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PathChartRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.ClearGrid.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.WordPoints.ClearGrid.RegularPrimitiveSplits

public section

/-! The actual subdivided original regular boundary has arbitrarily small
canonical integral on a supplied shared primitive bank. Its polygon area
is deliberately not asserted to vanish. -/

section
open Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib

open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FacePeriods
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.LiftedReadings.BranchCellBank
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

open Purelib.Riemann.Meshes (FramedPuncturedGrid)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {base : FramedPuncturedGrid curve branches higher} {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid}
  {vertices : SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    SquareRoot.Grid.RootEdgeBank frames}

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

/-- Every geometric, scalar, routing, corner, chart and zero-period budget
is acquired internally. The selected sheet is the original circuit's
actual arriving sheet in the enlarged frame bank. -/
theorem included_canonical_small (face : RegularFace bank)
    (included : Geometry.Grid.Extension.CoordinateInclusion bank.grid base.bank.grid)
    (mesh : LiftedMesh vertices edges base.faces) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (sheet : Fin 2) (source : Hyperelliptic.Differentials.Basic.Differential genus) (differential : Fin genus)
    (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    let member := face.cell.anchor_mem face.member
    let walk := included.resplit face.boundary member
    let assigned := Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.walkFaces mesh walk sheet
    let quarter := target / 4
    let quarterPositive : 0 < quarter := Fraction.Order.Field.div_pos_direct positive (by
        decide +kernel : (0 : Fraction.Rational) < 4)
    let part := quarter / 32
    let partPositive : 0 < part := Fraction.Order.Field.div_pos_direct quarterPositive (by
        decide +kernel : (0 : Fraction.Rational) < 32)
    let inner := Rational.Budget.Aggregate.perTerm part assigned.indexed.length
    let innerPositive := Rational.Budget.Aggregate.perTerm_positive partPositive assigned.indexed.length
    let request := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest.IncludedRequest.build face included frames
      sheet source differential minimum inner innerPositive domains
    let sources :=
      SheetEntries.LiftedSources.build
      mesh request.entries
    let route := Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.RouteRequest.build
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.RegularPrimitiveSplits.SheetEntries.LiftedSources.pieces
      sources) Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.canonicalRoute part partPositive
    let charts := Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests.RouteChartRequest.build assigned.routeSpine
      (standardDifferential differential) domains part partPositive
    let numericalFloor := max
      (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index request.scalars)
      (max route.index charts.index)
    ∀ numericalIndex (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (standardDifferential differential) numericalIndex domains)
      (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics mesh),
        numericalFloor ≤ numericalIndex →
      Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh triangles.values)
        (edges.indexedEdges vertices walk sheet)) < target := by
  intro member walk assigned quarter quarterPositive part partPositive inner innerPositive request sources route charts
    numericalFloor numericalIndex numerics triangles later
  let faces := face.includedFaces included frames mesh sheet
  have scalarLater := (Data.Nat.Order.le_max_left _ _).trans later
  have routeLater := (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
  have chartLater := (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
  let readings := request.readWith innerPositive (List.ofFn vertices.coordinate) numerics scalarLater
  have vertexPoints : ∀ vertex, vertices.coordinate vertex ∈ request.points (List.ofFn vertices.coordinate) := by
    intro vertex
    exact List.mem_append_right _ (Data.List.Permutation.ofFn_mem _ vertex)
  let corners := Hyperelliptic.Meshes.PuncturedGrid.Face.MeshWords.LiftedMesh.PathFaces.MeshWordReadings.build
    readings.meshes vertexPoints assigned
  let zero := face.includedZeroTail included frames sheet source differential quarter quarterPositive minimum
  let stage := max request.fragments.comparison.stage zero.leftIndex
  let sample := (((face.includedPeriod included frames sheet source).period.program differential).integral.model
    stage).integralSample
  have sampleSmall : Data.Gaussian.Norm.Basic.normSq sample < quarter := face.included_sample_small included frames
    sheet source differential
    quarter quarterPositive minimum stage (Data.Nat.Order.le_max_right _ _)
  have canonical : Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh triangles.values) assigned.indexed -
        sample) < quarter := by
    apply Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical.period_accurate corners quarterPositive charts
      chartLater triangles sample readings.sum.value
    · exact (readings.accurate stage (Data.Nat.Order.le_max_left _ _)).trans_le
        (Rational.Budget.Aggregate.perTerm_le partPositive.le _)
    · have routed := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodRoutes.routed_accurate sources member included
        faces part partPositive
        readings.meshes readings.sum routeLater (by
          intro piece present
          have ends :=
            SheetEntries.LiftedSources.endpoints_mem
            sources piece present
          exact ⟨List.mem_append_left _ ends.1, List.mem_append_left _ ends.2⟩)
      rw [corners.value_eq, corners.values_eq]
      exact routed
    · rw [corners.bound_eq, corners.count_eq]
      exact Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical.requested_corner_bound partPositive
        assigned.indexed.length request.pieces
  have bound := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct canonical sampleSmall))
  rw [sub_add_cancel, Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.walkFaces_indexed] at bound
  have equal : 2 * (quarter + quarter) = target := by
    change 2 * (target / 4 + target / 4) = target
    rw [show 2 * (target / 4 + target / 4) = target / 4 * 4 by ring1]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact bound.trans_eq equal

end Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

end
