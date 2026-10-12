module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateWindowTriangles
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
public import Purelib.Riemann.RootContinuation.NewtonBandConjugateWindowSelectedTriangles
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FinePolygonAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! A constructed common threshold compares the Newton-band boundary minus its retained hole circuits on both
sheets with the complete selected fine triangle sum. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateWindowSelectedRequest

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {current : Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars} {i j
    : Fin genus}

/-- The success certificate applies to every later shared numerical cache.
All fine polygons and connector errors are paid on both initial sheets. -/
@[expose] def selectedConjugateTriangleRequest (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid
  index)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    { threshold : Nat // floor ≤ threshold ∧
      ∀ stage (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
        (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i)
          current.mesh) (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
          (cache.get j) current.mesh),
        threshold ≤ stage →
        let boundary := fun sheet =>
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
          current.edges.chainArea current.vertices
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
            Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            current.mesh left.values edge))
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values)
              coefficient)
          region.boundary sheet -
          Topology.Mesh.RetracingWords.wordArea
            (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
            Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            current.mesh left.values edge))
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values)
              coefficient)
            (RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := current) region sheet).word)
        Data.Gaussian.Norm.Basic.normSq (boundary 0 + boundary 1 -
          Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun
          position =>
          decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index)))) < error }
            := by
  let part := error / 4
  have partPositive : 0 < part := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have localPositive : 0 < part / 4 := Fraction.Order.Field.div_pos_direct partPositive (by
      decide : (0 : Fraction.Rational) < 4)
  let threshold := fun sheet : Fin 2 =>
    let compiled := RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := current) region sheet
    let connectors := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.build
      compiled current.mesh first second (part / 4) localPositive floor
    let polygons := Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fineConjugatePolygonRequests
      current.mesh first second (Rational.Budget.Aggregate.perTerm (part / 4) compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive localPositive _) floor compiled.regulars
    max (max floor connectors.index) polygons.val
  have bounds (sheet : Fin 2) : floor ≤ threshold sheet ∧
      ∀ stage (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
        (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i)
          current.mesh) (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
          (cache.get j) current.mesh),
        threshold sheet ≤ stage →
        Data.Gaussian.Norm.Basic.normSq
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
          current.edges.chainArea current.vertices
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
            Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            current.mesh left.values edge))
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values)
              coefficient)
          region.boundary sheet -
          Topology.Mesh.RetracingWords.wordArea
            (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
            Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
            current.mesh left.values edge))
            (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values)
              coefficient)
            (RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := current) region sheet).word) -
          Geometry.Grid.CellBoundary.sumValues
            (Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fineConjugateTriangleArea left right)
            (RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := current) region sheet).regulars) < part
            :=
    Hyperelliptic.Meshes.Newton.BandConjugateWindowTriangles.fine_conjugate_triangles_accurate region sheet first second
      part partPositive floor
  refine ⟨max (threshold 0) (threshold 1), (bounds 0).1.trans (Data.Nat.Order.le_max_left _ _), ?_⟩
  intro stage cache left right later boundary
  let triangles := fun sheet => Geometry.Grid.CellBoundary.sumValues
    (Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fineConjugateTriangleArea left right)
    (RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := current) region sheet).regulars
  have zero := (bounds 0).2 stage cache left right ((Data.Nat.Order.le_max_left _ _).trans later)
  have one := (bounds 1).2 stage cache left right ((Data.Nat.Order.le_max_right _ _).trans later)
  change Data.Gaussian.Norm.Basic.normSq (boundary 0 - triangles 0) < part at zero
  change Data.Gaussian.Norm.Basic.normSq (boundary 1 - triangles 1) < part at one
  have selected := RootContinuation.NewtonBandConjugateWindowSelectedTriangles.fine_conjugate_triangles_selected region
    left right
  change triangles 0 + triangles 1 = _ at selected
  rw [← selected]
  have equal : boundary 0 + boundary 1 - (triangles 0 + triangles 1) =
      (boundary 0 - triangles 0) + (boundary 1 - triangles 1) := by ring1
  rw [equal]
  have sumBound := (Fraction.Order.Arithmetic.add_le_add_direct zero.le (le_refl (Data.Gaussian.Norm.Basic.normSq
    (boundary 1 - triangles 1)))).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct one part)
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      sumBound).trans_eq
      ((by ring1 : 2 * (part + part) = error / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateWindowSelectedRequest
