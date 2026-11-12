module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandWindowConnectors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FinePolygonAggregate
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! The Newton-band polygon minus its retained hole polygon is
compared with the fine triangle wedges on the actual arriving sheets. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.BandWindowTriangles

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Branches.BranchIsolation.Data.Index branches}
  {current : Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars} {i j
    : Fin genus}

/-- Polarization extraction distributes over the pointwise difference of two coefficient-indexed areas. -/
private theorem extract_sub (first second : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) :
    BilinearPolarization.extract (fun coefficient => first
      coefficient - second coefficient) =
      BilinearPolarization.extract first -
      BilinearPolarization.extract second := by
  unfold BilinearPolarization.extract
  ring1

/-- Both error allocations use the same magnitude banks and every later
shared cache. The sum retains the compiler's actual fine-face occurrences. -/
theorem fine_triangles_accurate (region : Annulus.Faces.AnnularFaces grid index) (sheet :
  Fin 2)
    (first : PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let compiled := RootContinuation.NewtonBandWindowCircuits.fineCompiler (current := current) region sheet
    let partPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
    let connectors := PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.build
      compiled current.mesh first second (error / 4) partPositive floor
    let polygons := PuncturedGrid.FinePolygonAggregate.finePolygonRequests current.mesh first
      second (Rational.Budget.Aggregate.perTerm (error / 4) compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive partPositive _) floor compiled.regulars
    let threshold := max (max floor connectors.index) polygons.val
    floor ≤ threshold ∧ ∀ stage (cache : PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
      domains stage)
      (left : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
        (right : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j)
        current.mesh),
      threshold ≤ stage →
      Gaussian.Norm.Basic.normSq
        (BilinearPolarization.extract (fun coefficient =>
        current.edges.chainArea current.vertices
        (BilinearPolarization.mix
          (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
          (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
        region.boundary sheet -
        Topology.Mesh.RetracingWords.wordArea
          (BilinearPolarization.mix
          (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
          (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient)
            compiled.word) -
        Geometry.Grid.CellBoundary.sumValues (PuncturedGrid.FinePolygonAggregate.fineTriangleArea
          left right) compiled.regulars) < error := by
  intro compiled partPositive connectors polygons threshold
  constructor
  · exact (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _)
  intro stage cache left right later
  let value := fun coefficient => BilinearPolarization.mix
    (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh left.values)
    (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh right.values) coefficient
  let boundary := fun coefficient => current.edges.chainArea current.vertices (value coefficient)
    region.boundary sheet -
    Topology.Mesh.RetracingWords.wordArea (value coefficient) compiled.word
  let finePolygons := fun coefficient => Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
    Topology.Mesh.RetracingWords.wordArea (value coefficient) occurrence.word) compiled.regulars
  let triangles := Geometry.Grid.CellBoundary.sumValues
    (PuncturedGrid.FinePolygonAggregate.fineTriangleArea left right) compiled.regulars
  have connectorBound := (BandWindowConnectors.fine_polygons_accurate region sheet first
    second (error / 4) partPositive floor).2
    stage (cache.get i) (cache.get j) left right ((Nat.Order.le_max_left _ _).trans later)
  have polygonBound := (PuncturedGrid.FinePolygonAggregate.fine_polygons_sum_accurate current.mesh
    first second (error / 4) partPositive floor compiled.regulars).2
    stage cache left right ((Nat.Order.le_max_right _ _).trans later)
  change Gaussian.Norm.Basic.normSq
    (BilinearPolarization.extract (fun coefficient =>
    boundary coefficient - finePolygons coefficient)) ≤ error / 4 at connectorBound
  rw [BandWindowTriangles.extract_sub] at connectorBound
  change Gaussian.Norm.Basic.normSq
    (BilinearPolarization.extract finePolygons - triangles) <
    error / 4 at polygonBound
  change Gaussian.Norm.Basic.normSq
    (BilinearPolarization.extract boundary - triangles) <
    error
  have equal : BilinearPolarization.extract boundary -
    triangles =
      (BilinearPolarization.extract boundary -
        BilinearPolarization.extract finePolygons) +
        (BilinearPolarization.extract finePolygons -
        triangles) := by ring1
  rw [equal]
  have sumBound := (Fraction.Order.Arithmetic.add_le_add_direct connectorBound (le_refl
    (Gaussian.Norm.Basic.normSq
    (BilinearPolarization.extract finePolygons -
    triangles)))).trans_lt
    (Fraction.Order.Arithmetic.add_lt_add_left_direct polygonBound (error / 4))
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      sumBound).trans_eq
      ((by ring1 : 2 * (error / 4 + error / 4) = error / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.BandWindowTriangles
