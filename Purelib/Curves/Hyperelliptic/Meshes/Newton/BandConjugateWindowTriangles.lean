module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateWindowConnectors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate
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
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
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

/-! The Newton-band polygon minus its retained hole polygon is
compared with the fine triangle wedges on the actual arriving sheets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateWindowTriangles

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

/-- Both error allocations use the same magnitude banks and every later
shared cache. The sum retains the compiler's actual fine-face occurrences. -/
theorem fine_conjugate_triangles_accurate (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index)
  (sheet : Fin 2)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let compiled := RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := current) region sheet
    let partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
    let connectors := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.build
      compiled current.mesh first second (error / 4) partPositive floor
    let polygons := Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fineConjugatePolygonRequests
      current.mesh first second (Rational.Budget.Aggregate.perTerm (error / 4) compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let threshold := max (max floor connectors.index) polygons.val
    floor ≤ threshold ∧ ∀ stage (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
      domains stage)
      (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
        (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j)
        current.mesh),
      threshold ≤ stage →
      Data.Gaussian.Norm.Basic.normSq
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        current.edges.chainArea current.vertices
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
          Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          current.mesh left.values edge)) (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          current.mesh right.values) coefficient)
        region.boundary sheet -
        Topology.Mesh.RetracingWords.wordArea
          (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix (fun edge =>
          Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
          current.mesh left.values edge))
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
            compiled.word) -
        Geometry.Grid.CellBoundary.sumValues
          (Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fineConjugateTriangleArea left right)
          compiled.regulars) < error := by
  intro compiled partPositive connectors polygons threshold
  constructor
  · exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)
  intro stage cache left right later
  let value := fun coefficient => Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
    (fun edge => Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
    current.mesh left.values edge))
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient
  let boundary := fun coefficient => current.edges.chainArea current.vertices (value coefficient)
    region.boundary sheet -
    Topology.Mesh.RetracingWords.wordArea (value coefficient) compiled.word
  let finePolygons := fun coefficient => Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
    Topology.Mesh.RetracingWords.wordArea (value coefficient) occurrence.word) compiled.regulars
  let triangles := Geometry.Grid.CellBoundary.sumValues
    (Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fineConjugateTriangleArea left right)
    compiled.regulars
  have connectorBound := (Hyperelliptic.Meshes.Newton.BandConjugateWindowConnectors.fine_conjugate_polygons_accurate
    region sheet first second (error / 4) partPositive floor).2
    stage (cache.get i) (cache.get j) left right ((Data.Nat.Order.le_max_left _ _).trans later)
  have polygonBound :=
    (Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fine_conjugate_polygons_sum_accurate current.mesh
    first second (error / 4) partPositive floor compiled.regulars).2
    stage cache left right ((Data.Nat.Order.le_max_right _ _).trans later)
  change Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
    boundary coefficient - finePolygons coefficient)) ≤ error / 4 at connectorBound
  rw [PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_sub] at connectorBound
  change Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract finePolygons - triangles) <
    error / 4 at polygonBound
  change Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract boundary - triangles) <
    error
  have equal : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract boundary -
    triangles =
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract boundary -
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract finePolygons) +
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract finePolygons -
        triangles) := by ring1
  rw [equal]
  have sumBound := (Fraction.Order.Arithmetic.add_le_add_direct connectorBound (le_refl
    (Data.Gaussian.Norm.Basic.normSq
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract finePolygons -
    triangles)))).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct polygonBound (error / 4))
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      sumBound).trans_eq
      ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateWindowTriangles
