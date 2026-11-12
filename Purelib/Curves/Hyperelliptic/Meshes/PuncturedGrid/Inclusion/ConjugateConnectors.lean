module
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

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PolarizationBound
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

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedConnectors
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison

open Purelib.Topology

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-! The existing connector requests pay the conjugate/value extraction
while retaining all regular polygon areas in the signed expression. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateConnectors

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib.Riemann.Periods
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

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
  {start : Gaussian.Basic.Canonical} {member : Geometry.Grid.FromStates.ContainsVertex bank.grid start}
  {tree : Geometry.Grid.RowCircuitOrder.CellCircuits bank.grid start} {partition :
    OrderedBranchCircuits.BranchCellBank.CircuitPartition faces tree} {sheet : Fin 2}
  {firstIndex secondIndex : Fin genus}

namespace PolarizedConnectorRequest

/-- Conjugating each edge value conjugates the complete retained word value. -/
private theorem word_conj {count : Nat} (value : Polygon.Stokes.OrientedEdge count → Gaussian.Basic.Canonical)
  (word : List (Polygon.Stokes.OrientedEdge count)) :
    Surface.Sewing.SewingRetraction.wordValue (fun edge => Gaussian.Basic.conj (value edge))
      word =
      Gaussian.Basic.conj (Surface.Sewing.SewingRetraction.wordValue value word) := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
      change Gaussian.Basic.conj (value edge) + Surface.Sewing.SewingRetraction.wordValue _ rest =
        Gaussian.Basic.conj (value edge + Surface.Sewing.SewingRetraction.wordValue value rest)
      rw [ih, Gaussian.Basic.conj_add]

/-- A unit-coefficient mixture of a conjugated left value and a right value has squared norm at most twice their bound
sum. -/
private theorem mixed_bound (a b coefficient : Gaussian.Basic.Canonical) {left right : Fraction.Rational}
    (unit : Gaussian.Norm.Basic.normSq coefficient = 1) (leftBound : Gaussian.Norm.Basic.normSq a ≤
      left) (rightBound : Gaussian.Norm.Basic.normSq b ≤ right) :
    Gaussian.Norm.Basic.normSq (Gaussian.Basic.conj a + coefficient * b) ≤ 2 * (left + right) := by
  have estimate := Gaussian.Norm.Bounds.normSq_add_le_two (Gaussian.Basic.conj a) (coefficient * b)
  rw [Gaussian.Norm.Basic.normSq_conj, Gaussian.Norm.Basic.normSq_mul, unit, _root_.one_mul] at estimate
  exact estimate.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct leftBound rightBound) (by decide))

/-- The original magnitude bank bounds every retained canonical edge reading by four times its magnitude bound. -/
private theorem edge_bounded {differential : Fin genus}
    (fixed : Face.MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential differential))
    {stage : Nat} (later : fixed.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank
      (PeriodMatrix.standardDifferential differential) stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) (edge :
      Polygon.Stokes.OrientedEdge vertices.count) :
    Gaussian.Norm.Basic.normSq (CanonicalEdgeValues.edgeValuation mesh
      readings.values edge) ≤ 4 * fixed.bound := by
  let retainedMagnitude := Readings.EdgeMagnitude.ofBank
    (owner := Readings.SourceChartComparison.ownerFromMesh mesh) fixed later readings
  exact Readings.WordObservations.edge_bounded retainedMagnitude edge
/-- The retained common connector edge bound is nonnegative. -/
private theorem edgeBound_nonnegative
    (first : Face.MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential firstIndex))
    (second : Face.MagnitudeBank.FaceMagnitudeBank domains
      (PeriodMatrix.standardDifferential secondIndex)) : 0 ≤
      PolarizedConnectors.PolarizedConnectorRequest.edgeBound first second
      :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Arithmetic.mul_nonneg_direct (by decide) first.nonnegative)
      (Arithmetic.mul_nonneg_direct (by decide) second.nonnegative))

variable {compiled :
  ResplitCompiled included
  edges vertices member partition sheet}
  {first : Face.MagnitudeBank.FaceMagnitudeBank domains
    (PeriodMatrix.standardDifferential firstIndex)}
  {second : Face.MagnitudeBank.FaceMagnitudeBank domains
    (PeriodMatrix.standardDifferential secondIndex)} {error : Fraction.Rational}
open Purelib.Approximation in
/-- The original connector request pays one unit-coefficient conjugate polarization direction.

At every sufficient shared stage the signed connector residual retains all regular polygon areas and has squared norm
below one sixteenth of the target. -/
private theorem conjugate_direction_accurate (request :
  PolarizedConnectors.PolarizedConnectorRequest (mesh := mesh) compiled
  first second error)
    (coefficient : Gaussian.Basic.Canonical) (unit : Gaussian.Norm.Basic.normSq coefficient = 1)
    {stage : Nat} {leftShared : Face.PrimitiveData.FacePrimitiveBank
      (PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightShared : Face.PrimitiveData.FacePrimitiveBank
      (PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftShared mesh)
      (rightReadings : TrianglePrimitiveReadings.TriangleReadings rightShared mesh)
    (later : request.index ≤ stage) :
    let value := BilinearPolarization.mix (fun edge =>
      Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation mesh
      leftReadings.values edge))
      (CanonicalEdgeValues.edgeValuation mesh rightReadings.values) coefficient
    Gaussian.Norm.Basic.normSq (Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms -
      Geometry.Grid.CellBoundary.sumValues (fun occurrence => Mesh.RetracingWords.wordArea value
        occurrence.word) compiled.regulars) < error / 16 := by
  intro value
  have fixedLater := (Nat.Order.le_max_left _ _).trans later
  have requestsLater := (Nat.Order.le_max_right _ _).trans later
  apply compiled.connector_small value
    (PolarizedConnectorRequest.edgeBound_nonnegative
    first second) ?_
    (Field.div_pos_direct request.positive (by decide)) ?_
  · intro edge
    exact PolarizedConnectorRequest.mixed_bound _ _
      coefficient unit
      ((Gaussian.Norm.Basic.normSq_conj _).trans_le
        (PolarizedConnectorRequest.edge_bounded first
        ((Nat.Order.le_max_left _ _).trans fixedLater) leftReadings edge))
      (PolarizedConnectorRequest.edge_bounded second
        ((Nat.Order.le_max_right _ _).trans fixedLater) rightReadings edge)
  · intro occurrence present
    have leftSmall := (request.left.property stage leftShared leftReadings
      ((Nat.Order.le_max_left _ _).trans requestsLater) occurrence present).le
    have rightSmall := (request.right.property stage rightShared rightReadings
      ((Nat.Order.le_max_right _ _).trans requestsLater) occurrence present).le
    change Gaussian.Norm.Basic.normSq (Surface.Sewing.SewingRetraction.wordValue
      (BilinearPolarization.mix _ _ coefficient)
      occurrence.word) ≤ _
    rw [BilinearPolarization.word_mix,
      PolarizedConnectorRequest.word_conj]
    have estimate :=
      PolarizedConnectorRequest.mixed_bound _ _
      coefficient unit ((Gaussian.Norm.Basic.normSq_conj _).trans_le leftSmall) rightSmall
    refine estimate.trans_eq ?_
    rw [← request.weight_eq]
    exact (by ring1 : 2 * (Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm (error / 16)
      compiled.connectorTerms.length) request.weight / 4 +
      Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm (error / 16) compiled.connectorTerms.length)
        request.weight / 4) =
      (Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm (error / 16)
        compiled.connectorTerms.length) request.weight / 4) * 4).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

/-- One cached weight and two regular-loop thresholds pay all four connector
directions on the same sample. The bound concerns only the signed connector
residual, retaining all regular polygon areas in the expression. -/
theorem conjugate_accurate (request :
  PolarizedConnectors.PolarizedConnectorRequest (mesh := mesh) compiled
  first second error)
    {stage : Nat} {leftShared : Face.PrimitiveData.FacePrimitiveBank
      (PeriodMatrix.standardDifferential firstIndex) stage domains}
    {rightShared : Face.PrimitiveData.FacePrimitiveBank
      (PeriodMatrix.standardDifferential secondIndex) stage domains}
    (leftReadings : TrianglePrimitiveReadings.TriangleReadings leftShared mesh)
      (rightReadings : TrianglePrimitiveReadings.TriangleReadings rightShared mesh)
    (later : request.index ≤ stage) :
    Gaussian.Norm.Basic.normSq
      (BilinearPolarization.extract (fun coefficient =>
      let value := BilinearPolarization.mix (fun edge =>
        Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation mesh
        leftReadings.values edge))
        (CanonicalEdgeValues.edgeValuation mesh rightReadings.values) coefficient
      Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms -
        Geometry.Grid.CellBoundary.sumValues (fun occurrence => Mesh.RetracingWords.wordArea value
          occurrence.word) compiled.regulars)) ≤ error := by
  let residual := fun coefficient =>
    let value := BilinearPolarization.mix (fun edge =>
      Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation mesh
      leftReadings.values edge))
      (CanonicalEdgeValues.edgeValuation mesh rightReadings.values) coefficient
    Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms - Geometry.Grid.CellBoundary.sumValues (fun
      occurrence => Mesh.RetracingWords.wordArea value occurrence.word) compiled.regulars
  have one : Gaussian.Norm.Basic.normSq (residual 1) ≤ error / 16 :=

      (conjugate_direction_accurate
      request 1 (by decide) leftReadings rightReadings later).le
  have negOne : Gaussian.Norm.Basic.normSq (residual (-1)) ≤ error / 16 :=

      (conjugate_direction_accurate
      request (-1) (by decide) leftReadings rightReadings later).le
  have imaginary : Gaussian.Norm.Basic.normSq (residual
    BilinearPolarization.imaginary) ≤ error / 16 :=

      (conjugate_direction_accurate
      request _ (by decide) leftReadings rightReadings later).le
  have negImaginary : Gaussian.Norm.Basic.normSq (residual
    (-BilinearPolarization.imaginary)) ≤ error / 16 :=

      (conjugate_direction_accurate
      request _ (by decide) leftReadings rightReadings later).le
  have canonicalBound {value : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (bound : Gaussian.Norm.Basic.normSq value ≤ limit) :
      Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Basic.LessEqual _ _ at bound ⊢
    simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have oldBound {value : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (bound : Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Basic.LessEqual _ _ at bound ⊢
    simpa only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] using bound
  have estimate := BilinearPolarization.extract_normSq_le
    (value := residual)
    (residual 1) (residual (-1)) (residual
      BilinearPolarization.imaginary) (residual
      (-BilinearPolarization.imaginary))
    rfl rfl rfl rfl
  apply oldBound
  refine estimate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Arithmetic.add_le_add_direct
      (Arithmetic.add_le_add_direct (canonicalBound one) (canonicalBound negOne)) (canonicalBound
      imaginary)) (canonicalBound negImaginary))
    (by decide : (0 : Fraction.Rational) ≤ 4)).trans_eq ?_)
  exact (by ring1 : 4 * (error / 16 + error / 16 + error / 16 + error / 16) = error / 16 * 16).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

end PolarizedConnectorRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConjugateConnectors
