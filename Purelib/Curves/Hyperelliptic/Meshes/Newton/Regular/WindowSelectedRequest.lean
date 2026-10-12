module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowConnectors
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FinePolygonAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowSelectedTriangles
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

public section

open Purelib.Data

/-! A constructed common threshold compares the original regular-cell
boundary on both sheets with its complete selected fine triangle sum. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowSelectedRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedFullTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces (OriginalRegularFaces)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors (PolarizedConnectorRequest)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FinePolygonAggregate (finePolygonRequests fineTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowConnectors (fineCompiler)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowTriangles (fine_triangles_accurate)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowSelectedTriangles (fine_triangles_selected)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {face : RegularFace original}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}

/-- The success certificate applies to every later shared numerical cache. All fine polygons and connector errors are
paid on both initial sheets. -/
@[expose] def selectedTriangleRequest (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    { threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh),
        threshold ≤ stage →
        let boundary := fun sheet => BilinearPolarization.extract (fun coefficient => current.edges.chainArea
          current.vertices
          (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation current.mesh left.values)
            (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
          (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet)
        Data.Gaussian.Norm.Basic.normSq (boundary 0 + boundary 1 -
          SelectedTrianglePartition.selectedFullTriangleArea left right (fun position =>
          decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines face.cell.box))) < error } := by
  let part := error / 4
  have partPositive : 0 < part := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have localPositive : 0 < part / 4 := Fraction.Order.Field.div_pos_direct partPositive (by
      decide : (0 : Fraction.Rational) < 4)
  let threshold := fun sheet : Fin 2 =>
    let compiled := WindowConnectors.fineCompiler (current := current) region sheet
    let connectors := PolarizedConnectorRequest.build compiled current.mesh first second (part / 4) localPositive floor
    let polygons := FinePolygonAggregate.finePolygonRequests current.mesh first second (Aggregate.perTerm (part / 4)
      compiled.regulars.length)
      (Aggregate.perTerm_positive localPositive _) floor compiled.regulars
    max (max floor connectors.index) polygons.val
  have bounds (sheet : Fin 2) : floor ≤ threshold sheet ∧
      ∀ stage (cache : RegularMeshes.Numerics domains stage)
        (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
          TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh),
        threshold sheet ≤ stage →
        Data.Gaussian.Norm.Basic.normSq (BilinearPolarization.extract (fun coefficient =>
          current.edges.chainArea current.vertices
          (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation current.mesh left.values)
            (CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
          (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet) -
          CellBoundary.sumValues (FinePolygonAggregate.fineTriangleArea left right) (WindowConnectors.fineCompiler
            (current := current) region sheet).regulars) < part :=
    WindowTriangles.fine_triangles_accurate region sheet first second part partPositive floor
  refine ⟨max (threshold 0) (threshold 1), (bounds 0).1.trans (Nat.Order.le_max_left _ _), ?_⟩
  intro stage cache left right later boundary
  let triangles := fun sheet => CellBoundary.sumValues (FinePolygonAggregate.fineTriangleArea left right)
    (WindowConnectors.fineCompiler (current := current) region sheet).regulars
  have zero := (bounds 0).2 stage cache left right ((Nat.Order.le_max_left _ _).trans later)
  have one := (bounds 1).2 stage cache left right ((Nat.Order.le_max_right _ _).trans later)
  change Data.Gaussian.Norm.Basic.normSq (boundary 0 - triangles 0) < part at zero
  change Data.Gaussian.Norm.Basic.normSq (boundary 1 - triangles 1) < part at one
  have selected := WindowSelectedTriangles.fine_triangles_selected region left right
  change triangles 0 + triangles 1 = _ at selected
  rw [← selected]
  have equal : boundary 0 + boundary 1 - (triangles 0 + triangles 1) =
      (boundary 0 - triangles 0) + (boundary 1 - triangles 1) := by ring1
  rw [equal]
  have sumBound := (Fraction.Order.Arithmetic.add_le_add_direct zero.le (le_refl
    (Data.Gaussian.Norm.Basic.normSq (boundary 1 - triangles 1)))).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct one part)
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      sumBound).trans_eq
      ((by ring1 : 2 * (part + part) = error / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowSelectedRequest
