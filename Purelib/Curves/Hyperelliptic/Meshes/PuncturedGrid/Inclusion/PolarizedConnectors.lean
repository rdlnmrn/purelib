module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Geometry.Grid.FromStates

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PolarizationBound
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-! Pay the polarized connector error on a retained resplit compiler.
Only connector terms with their certified regular-loop factors are made small;
no diagonal surface energy is discarded. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors

open Purelib.Riemann.Periods

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (mix extract
  imaginary extract_normSq_le)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {included : Geometry.Grid.Extension.CoordinateInclusion bank.grid base.bank.grid}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {start : Gaussian.Basic.Canonical} {member : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start}
  {tree : Geometry.Grid.RowCircuitOrder.CellCircuits bank.grid start} {partition :
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition faces tree} {sheet : Fin 2}
  {firstIndex secondIndex : Fin genus}

namespace PolarizedConnectorRequest

/-- A unit-coefficient mixed Gaussian value is bounded by twice the sum of its retained component bounds. -/
private theorem mixed_bound (a b coefficient : Gaussian.Basic.Canonical) {left right : Fraction.Rational}
    (unit : Data.Gaussian.Norm.Basic.normSq coefficient = 1) (leftBound : Data.Gaussian.Norm.Basic.normSq a ≤
      left) (rightBound : Data.Gaussian.Norm.Basic.normSq b ≤ right) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj a + coefficient * b) ≤ 2 * (left + right) := by
  have estimate := Gaussian.Norm.Bounds.normSq_add_le_two (Data.Gaussian.Basic.conj a) (coefficient * b)
  rw [Gaussian.Norm.Basic.normSq_conj, Gaussian.Norm.Basic.normSq_mul, unit, _root_.one_mul] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct leftBound rightBound) (by decide))

/-- The supplied canonical edge reading meets the original magnitude bank's fourfold bound. -/
private theorem edge_bounded {differential : Fin genus}
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential differential))
    {stage : Nat} (later : fixed.index ≤ stage)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) (edge :
      Topology.Polygon.Stokes.OrientedEdge vertices.count) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh
      readings.values edge) ≤ 4 * fixed.bound := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh mesh) fixed later readings
  exact Hyperelliptic.Meshes.PuncturedGrid.Readings.WordObservations.edge_bounded retainedMagnitude edge
/-- The retained common bound for the mixed canonical edge readings. -/
@[expose] def edgeBound (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)) : Fraction.Rational :=
  2 * (4 * first.bound + 4 * second.bound)

/-- The retained mixed-edge bound is nonnegative. -/
private theorem edgeBound_nonnegative
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)) : 0 ≤
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.edgeBound first second
      :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) first.nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) second.nonnegative))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest in
/-- A sufficient stage and exact smallness certificate for the original regular loops at the weighted polarized
connector allowance. -/
@[expose] def RegularRequest (compiled :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled included
  edges vertices member partition sheet)
    (differential : Fin genus) (error weight : Fraction.Rational) :=
  { index : Nat //
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.RegularsSmallAt mesh
    domains differential
      (Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm (error / 16)
        compiled.connectorTerms.length) weight / 4) compiled.regulars index }

end PolarizedConnectorRequest

set_option genInjectivity false in
/-- A paid polarized connector request on the original resplit compiler.

It retains both differential magnitude banks, the actual connector weight and two original regular-loop thresholds;
regular polygon areas remain explicit. -/
structure PolarizedConnectorRequest (compiled :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled included
  edges vertices member partition sheet)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex)) (error : Fraction.Rational) where
  /-- The requested whole polarized connector error is positive. -/ positive : 0 < error
  /-- The cached original resplit compiler's connector weight. -/ weight : Fraction.Rational
  /-- The weight uses exactly the retained mixed-edge magnitude bound. -/ weight_eq : weight = compiled.connectorWeight
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.edgeBound first second)
  /-- The original first-differential regular-loop threshold and certificate. -/ left :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.RegularRequest (mesh :=
    mesh) (domains := domains) compiled firstIndex error weight
  /-- The original second-differential regular-loop threshold and certificate. -/ right :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.RegularRequest (mesh :=
    mesh) (domains := domains) compiled secondIndex error weight

constructive_injectivity PolarizedConnectorRequest

namespace PolarizedConnectorRequest

variable {compiled :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled included
  edges vertices member partition sheet}
  {first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Periods.PeriodMatrix.standardDifferential secondIndex)} {error : Fraction.Rational}

/-- Prepare both original regular-loop thresholds using one retained connector weight and the supplied stage floor. -/
@[expose] def build (compiled :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled included
  edges vertices member partition sheet)
    (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential firstIndex))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (minimum : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest (mesh := mesh) compiled
      first second error :=
  let weight := compiled.connectorWeight
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.edgeBound first second)
  let tolerance := Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm (error / 16)
    compiled.connectorTerms.length) weight / 4
  have tolerancePositive : 0 < tolerance := Fraction.Order.Field.div_pos_direct
    (Rational.Budget.Weighted.allowance_positive (Rational.Budget.Aggregate.perTerm_positive
      (Fraction.Order.Field.div_pos_direct positive (by decide)) _)
      (compiled.connectorWeight_nonnegative _)) (by decide)
  ⟨positive, weight, rfl,
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests mesh
      domains (Periods.PeriodMatrix.standardDifferential firstIndex) firstIndex tolerance tolerancePositive minimum
      compiled.regulars,
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests mesh
      domains (Periods.PeriodMatrix.standardDifferential secondIndex) secondIndex tolerance tolerancePositive minimum
      compiled.regulars⟩

/-- The common sufficient stage for both original magnitude banks and both regular-loop requests. -/
@[expose] def index (request :
  Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest (mesh := mesh) compiled
  first second error) : Nat :=
  max (max first.index second.index) (max request.left.val request.right.val)

/-- Every unit polarization direction meets its paid sixteenth-target connector bound on the same retained numerical
readings. -/
private theorem direction_accurate (request :
  Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest (mesh := mesh) compiled
  first second error)
    (coefficient : Gaussian.Basic.Canonical) (unit : Data.Gaussian.Norm.Basic.normSq coefficient = 1)
    {stage : Nat} {leftShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftShared mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightShared mesh)
    (later : request.index ≤ stage) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh leftReadings.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh rightReadings.values) coefficient
    Data.Gaussian.Norm.Basic.normSq (Topology.Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms -
      Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea value
        occurrence.word) compiled.regulars) < error / 16 := by
  intro value
  have fixedLater := (Nat.Order.le_max_left _ _).trans later
  have requestsLater := (Nat.Order.le_max_right _ _).trans later
  apply compiled.connector_small value
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.edgeBound_nonnegative
    first second) ?_
    (Fraction.Order.Field.div_pos_direct request.positive (by decide)) ?_
  · intro edge
    exact Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.mixed_bound _ _
      coefficient unit
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.edge_bounded first
        ((Nat.Order.le_max_left _ _).trans fixedLater) leftReadings edge)
      (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.edge_bounded second
        ((Nat.Order.le_max_right _ _).trans fixedLater) rightReadings edge)
  · intro occurrence present
    have leftSmall := (request.left.property stage leftShared leftReadings
      ((Nat.Order.le_max_left _ _).trans requestsLater) occurrence present).le
    have rightSmall := (request.right.property stage rightShared rightReadings
      ((Nat.Order.le_max_right _ _).trans requestsLater) occurrence present).le
    change Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix _ _ coefficient)
      occurrence.word) ≤ _
    rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix]
    have estimate :=
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest.mixed_bound _ _
      coefficient unit leftSmall rightSmall
    refine estimate.trans_eq ?_
    rw [← request.weight_eq]
    exact (by ring1 : 2 * (Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm (error / 16)
      compiled.connectorTerms.length) request.weight / 4 +
      Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm (error / 16) compiled.connectorTerms.length)
        request.weight / 4) =
      (Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm (error / 16)
        compiled.connectorTerms.length) request.weight / 4) * 4).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization in
/-- One cached weight and two regular-loop thresholds pay all four connector
directions on the same sample. The bound concerns only the signed connector
residual, retaining all regular polygon areas in the expression. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors.PolarizedConnectorRequest
  (mesh := mesh) compiled first second error)
    {stage : Nat} {leftShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftShared mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightShared mesh)
    (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh leftReadings.values)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh rightReadings.values) coefficient
      Topology.Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms -
        Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea value
          occurrence.word) compiled.regulars)) ≤ error := by
  let residual := fun coefficient =>
    let value := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh leftReadings.values)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh rightReadings.values) coefficient
    Topology.Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms - Geometry.Grid.CellBoundary.sumValues (fun
      occurrence => Topology.Mesh.RetracingWords.wordArea value occurrence.word) compiled.regulars
  have one : Data.Gaussian.Norm.Basic.normSq (residual 1) ≤ error / 16 :=
    (request.direction_accurate 1 (by decide) leftReadings rightReadings later).le
  have negOne : Data.Gaussian.Norm.Basic.normSq (residual (-1)) ≤ error / 16 :=
    (request.direction_accurate (-1) (by decide) leftReadings rightReadings later).le
  have imaginary : Data.Gaussian.Norm.Basic.normSq (residual
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary) ≤ error / 16 :=
    (request.direction_accurate _ (by decide) leftReadings rightReadings later).le
  have negImaginary : Data.Gaussian.Norm.Basic.normSq (residual
    (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) ≤ error / 16 :=
    (request.direction_accurate _ (by decide) leftReadings rightReadings later).le
  have canonicalBound {value : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have oldBound {value : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (bound : Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_normSq_le
    (value := residual)
    (residual 1) (residual (-1)) (residual
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary) (residual
      (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary))
    rfl rfl rfl rfl
  apply oldBound
  refine estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (canonicalBound one) (canonicalBound negOne)) (canonicalBound
      imaginary)) (canonicalBound negImaginary))
    (by decide : (0 : Fraction.Rational) ≤ 4)).trans_eq ?_)
  exact (by ring1 : 4 * (error / 16 + error / 16 + error / 16 + error / 16) = error / 16 * 16).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

end PolarizedConnectorRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors
