module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

@[expose] public section

/-! Pay the regular-integral discrepancy between the terminal exterior
total and the actual physical exterior on the same numerical cache. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {current :
    Meshes.LiftedPuncturedGrid next}
  (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames next.faces.regulars}
    {differential : Fin genus}

/-- The squared original walk length times its retained fourfold edge magnitude bound. -/
public def walkMagnitude (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  (Periods.PeriodMatrix.standardDifferential differential))
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk next.bank.grid start finish) :
      Fraction.Rational :=
  (walk.edgeCount : Fraction.Rational)^2 * (4 * fixed.bound)

/-- The original walk magnitude bound is nonnegative. -/
public theorem walkMagnitude_nonnegative (fixed :
  Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  (Periods.PeriodMatrix.standardDifferential differential))
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk next.bank.grid start finish) : 0 ≤
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.walkMagnitude fixed walk :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      fixed.nonnegative)

open Purelib.Topology.Surface.Sewing in
/-- The actual cached word observation is bounded by its original squared edge count and magnitude bank. -/
private theorem walk_bounded (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  (Periods.PeriodMatrix.standardDifferential differential))
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk next.bank.grid start finish) (newSheet :
      Fin 2)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (later : fixed.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Purelib.Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      (current.edges.indexedEdges current.vertices walk newSheet)) ≤
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.walkMagnitude fixed walk := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh current.mesh) fixed later
      readings
  let observation := Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.realize retainedMagnitude
    (current.edges.indexedEdges current.vertices walk newSheet)
  have cached := observation.bounded
  change Data.Gaussian.Norm.Basic.normSq observation.total ≤ observation.bound at cached
  rw [observation.total_readback, observation.bound_readback,
    Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.BoundSpecification] at cached
  change Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
    (current.edges.indexedEdges current.vertices walk newSheet)) ≤
    ((current.edges.indexedEdges current.vertices walk newSheet).length : Fraction.Rational) ^ 2 * (4 * fixed.bound)
      at cached
  rw [current.edges.indexedEdges_length] at cached
  exact cached
/-- The exterior factor bound, twice the sum of the actual reference and paired-prefix walk bounds. -/
public def factorBound (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  (Periods.PeriodMatrix.standardDifferential differential)) : Fraction.Rational :=
  2 * (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.walkMagnitude fixed (included.resplit
    (bank.rows.get paired.split.ending.reference).reference.walk
    (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) +
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.walkMagnitude fixed (included.resplit
      (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)))

/-- The exterior factor bound is nonnegative. -/
public theorem factorBound_nonnegative (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains (Periods.PeriodMatrix.standardDifferential differential)) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.factorBound (paired := paired) included fixed
      :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.walkMagnitude_nonnegative fixed _)
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.walkMagnitude_nonnegative fixed _))

/-- The original exterior factor meets its bound for both odd and even terminal words. -/
public theorem factor_bounded (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  (Periods.PeriodMatrix.standardDifferential differential)) (newSheet : Fin 2)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (later : fixed.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor (paired := paired) included
      current.edges current.vertices newSheet
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)) ≤
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.factorBound (paired := paired) included fixed
        := by
  have referenceBound := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.walk_bounded fixed
    (included.resplit (bank.rows.get paired.split.ending.reference).reference.walk
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet readings
      later
  have prefixBound := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.walk_bounded fixed
    (included.resplit (bank.loopProduct (paired.split.pairs.flatMap (fun pair => [pair.1, pair.2])))
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
    newSheet readings later
  rw [bank.resplit_pairs_value included current.edges current.vertices] at prefixBound
  have nonnegative := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.factorBound_nonnegative (paired
    := paired) included fixed
  unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitExteriorFactor
  cases endingEq : paired.split.ending with
  | odd index => exact Gaussian.Norm.Basic.normSq_zero.trans_le nonnegative
  | even first last =>
      have referenceEq : paired.split.ending.reference = first := congrArg
        Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.PairEnding.reference endingEq
      rw [referenceEq] at referenceBound
      have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
          referenceBound prefixBound) (by decide))
      unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.factorBound
      rw [endingEq]
      exact estimate

open Purelib.Integration in
/-- The computed threshold controls replacement of the terminal branch
total by the physical exterior. It does not make the exterior itself small. -/
def exteriorTotalRequest
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    {newSheet : Fin 2}
    (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included current.edges current.vertices
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
      ordered.prepared.partition newSheet)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    (source : Hyperelliptic.Differentials.Basic.Differential genus) (error : Fraction.Rational) (positive : 0 < error)
      (floor : Nat) :
    { index : Nat // ∀ stage (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
      (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh),
        index ≤ stage →
      let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values
      Data.Gaussian.Norm.Basic.normSq
        (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired)
        included current.edges current.vertices newSheet value -
        Hyperelliptic.Meshes.PuncturedGrid.Inclusion.TerminalCorrection.resplitExteriorCorrection (paired := paired)
          included current.edges current.vertices newSheet value) ≤ error } := by
  let weight := 4 * Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.factorBound (paired :=
    paired) included fixed
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.factorBound_nonnegative (paired := paired)
    included fixed)
  let tolerance := Rational.Budget.Weighted.allowance error weight
  have tolerancePositive := Rational.Budget.Weighted.allowance_positive positive weightNonnegative
  let requests :=
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests
    current.mesh domains source differential
    (Rational.Budget.Aggregate.perTerm tolerance compiled.regulars.length) (Rational.Budget.Aggregate.perTerm_positive
      tolerancePositive _) floor compiled.regulars
  refine ⟨max fixed.index requests.val, ?_⟩
  intro stage shared readings later value
  have regular :=
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regulars_aggregate_small
    current.mesh domains source differential tolerance tolerancePositive floor
    compiled.regulars stage shared readings ((Nat.Order.le_max_right _ _).trans later)
  have bounded := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest.factor_bounded (paired :=
    paired) included fixed newSheet readings ((Nat.Order.le_max_left _ _).trans later)
  have read := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal.resplit_physical_exterior_difference (paired
    := paired) included current.edges current.vertices reference compiled value
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse current.mesh readings.values)
  have estimate := (Path.BoundaryRibbon.area_bound _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (by
      decide)) regular.le
      (Gaussian.Norm.Basic.normSq_nonneg _) weightNonnegative)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq read).trans_le (estimate.trans
    (Rational.Budget.Weighted.mul_allowance_le positive.le weightNonnegative))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotalRequest
