module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.Grid.FromStates

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Topology.Mesh

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-! An automatic shared numerical threshold removes the original ordered
connector area correction while preserving every regular polygon area. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {included : Geometry.Grid.Extension.CoordinateInclusion bank.grid base.bank.grid}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Fin genus}

/-- The supplied canonical edge reading is bounded by four times the original retained magnitude-bank bound. -/
public theorem Inclusion.ConnectorRequest.CircuitPartition.edge_bounded (fixed : Face.MagnitudeBank.FaceMagnitudeBank
  domains
  (Periods.PeriodMatrix.standardDifferential differential))
    {stage : Nat} (later : fixed.index ≤ stage)
    {numerics : Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings numerics mesh) (edge :
      Topology.Polygon.Stokes.OrientedEdge vertices.count) :
    Gaussian.Norm.Basic.normSq (CanonicalEdgeValues.edgeValuation mesh
      triangles.values edge) ≤ 4 * fixed.bound := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := Readings.SourceChartComparison.ownerFromMesh mesh) fixed later
      triangles
  exact Readings.WordObservations.edge_bounded retainedMagnitude edge
/-- All magnitudes and regular-loop requests are computed before the
supplied numerical read. No analytic smallness premise remains. -/
def
  OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled.connectorRequest
    (compiled : OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      (faces := faces) included edges vertices member partition sheet)
    (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (fixed : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    (source : Differentials.Basic.Differential genus) (target : Fraction.Rational) (positive : 0 < target)
      (minimum : Nat) :
    { floor : Nat // ∀ stage
      (numerics : Face.PrimitiveData.FacePrimitiveBank
        (Periods.PeriodMatrix.standardDifferential differential) stage domains)
      (triangles : TrianglePrimitiveReadings.TriangleReadings numerics mesh), floor ≤
        stage →
      Gaussian.Norm.Basic.normSq (RetracingWords.AreaTerm.total
        (CanonicalEdgeValues.edgeValuation mesh triangles.values) compiled.areaTerms
        -
        Geometry.Grid.CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea
          (CanonicalEdgeValues.edgeValuation mesh triangles.values) occurrence.word)
          compiled.regulars) < target } := by
  let edgeBound := 4 * fixed.bound
  let part := Rational.Budget.Aggregate.perTerm target compiled.connectorTerms.length
  have partPositive := Rational.Budget.Aggregate.perTerm_positive positive compiled.connectorTerms.length
  let allowance := Rational.Budget.Weighted.allowance part (compiled.connectorWeight edgeBound)
  have allowancePositive := Rational.Budget.Weighted.allowance_positive partPositive
    (compiled.connectorWeight_nonnegative edgeBound)
  let requests :=
    OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests mesh
    domains source differential allowance allowancePositive minimum compiled.regulars
  refine ⟨max fixed.index requests.val, ?_⟩
  intro stage numerics triangles later
  have fixedLater := (Nat.Order.le_max_left _ _).trans later
  have regularLater := (Nat.Order.le_max_right _ _).trans later
  exact compiled.connector_small _
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative)
    (Inclusion.ConnectorRequest.CircuitPartition.edge_bounded fixed fixedLater
      triangles) positive
    (fun occurrence present => (requests.property stage numerics triangles regularLater occurrence present).le)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorRequest.Ordered

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {frames : SquareRoot.Grid.RootFrames next.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    next.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {domains :
    Face.DomainBanks.FaceDomainBank frames next.faces.regulars} {differential : Fin
    genus}

/-- One actual numerical stage pays both original exterior corrections.
The branch word and all regular polygon areas are those of the original
ordered compiler, evaluated on the identical supplied triangle cache. -/
def resplitExteriorRequest (ordered :
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet)
    (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (reference : ∀ point, Geometry.Grid.FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    {newSheet : Fin 2}
    (compiled : OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices (BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank)
      ordered.prepared.partition newSheet)
    (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges next.faces)
    (fixed : Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    (source : Differentials.Basic.Differential genus) (target : Fraction.Rational) (positive : 0 < target)
      (minimum : Nat) :
    { floor : Nat // ∀ stage
      (numerics : Face.PrimitiveData.FacePrimitiveBank
        (Periods.PeriodMatrix.standardDifferential differential) stage domains)
      (triangles : TrianglePrimitiveReadings.TriangleReadings numerics mesh), floor ≤
        stage →
      let value := CanonicalEdgeValues.edgeValuation mesh triangles.values
      Gaussian.Norm.Basic.normSq (edges.chainValue vertices value (included.resplit base.bank.exterior
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
        Topology.Surface.Sewing.SewingRetraction.wordValue value compiled.word) < target ∧
      Gaussian.Norm.Basic.normSq (edges.chainArea vertices value (included.resplit base.bank.exterior
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
        (RetracingWords.wordArea value compiled.word + Geometry.Grid.CellBoundary.sumValues (fun
          occurrence => RetracingWords.wordArea value occurrence.word) compiled.regulars)) < target } :=
          by
  let integrals :=
    OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests mesh
    domains source differential (Rational.Budget.Aggregate.perTerm target compiled.regulars.length)
    (Rational.Budget.Aggregate.perTerm_positive positive _) minimum compiled.regulars
  let areas := compiled.connectorRequest mesh fixed source target positive minimum
  refine ⟨max integrals.val areas.val, ?_⟩
  intro stage numerics triangles later value
  constructor
  · exact ordered.resplit_exterior_integral_accurate included reference compiled mesh domains source differential target
      positive minimum
      stage numerics triangles ((Nat.Order.le_max_left _ _).trans later)
  · have bounded := areas.property stage numerics triangles ((Nat.Order.le_max_right _ _).trans later)
    rw [ordered.resplit_exterior_areas included edges vertices reference compiled value
      (CanonicalEdgeValues.edgeValuation_reverse mesh triangles.values)]
    rw [show RetracingWords.wordArea value compiled.word + RetracingWords.AreaTerm.total
      value compiled.areaTerms -
        (RetracingWords.wordArea value compiled.word + Geometry.Grid.CellBoundary.sumValues (fun
          occurrence => RetracingWords.wordArea value occurrence.word) compiled.regulars) =
        RetracingWords.AreaTerm.total value compiled.areaTerms -
          Geometry.Grid.CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea value
            occurrence.word) compiled.regulars by ring1]
    exact bounded

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorRequest.Ordered
