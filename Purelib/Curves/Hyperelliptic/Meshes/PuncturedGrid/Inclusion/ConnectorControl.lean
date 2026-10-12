module
import Purelib.Data.List.Flatten
import Purelib.Algebra.Group.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorBounds
import Purelib.Integration.Path.IncrementArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

public section

/-! Pay every connector cross term using its certified regular factor.
Actual word lengths, regular multiplicities and connector counts are kept. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Data.Rat

open Purelib.Algebra

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
  (ResplitCompiled RegularFactor RegularConnector ResplitRegularOccurrence)

/-- Compute the original cross-term payment from its signed coefficient, both word lengths, edge bound and regular
multiplicity. -/
@[expose] def Inclusion.ConnectorControl.connectorWeight (edgeBound : Fraction.Rational) (regularCount : Nat) :
  Topology.Mesh.RetracingWords.AreaTerm count → Fraction.Rational
  | .polygon _ => 0
  | .cross coefficient first last =>
      Data.Gaussian.Norm.Basic.normSq (coefficient : Gaussian.Basic.Canonical) * 4 *
        (((first.length + last.length : Nat) : Fraction.Rational) ^ 2 * edgeBound) * (regularCount : Fraction.Rational)
          ^ 2

/-- An original edge valuation bound controls each retained word by its certified length squared. -/
private theorem Inclusion.ConnectorControl.word_bound (value : Topology.Polygon.Stokes.OrientedEdge count →
  Gaussian.Basic.Canonical) {bound :
  Fraction.Rational}
    (nonnegative : 0 ≤ bound) (bounded : ∀ edge, Data.Gaussian.Norm.Basic.normSq (value edge) ≤ bound)
    (word : List (Topology.Polygon.Stokes.OrientedEdge count)) {length : Nat} (short : word.length ≤ length) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value word) ≤ (length :
      Fraction.Rational) ^ 2 * bound := by
  rw [← Topology.Mesh.RetracingWords.sum_map_eq_wordValue]
  apply Path.IncrementArea.sum_bound_of_length nonnegative
  · intro reading present
    obtain ⟨edge, _, equal⟩ := Data.List.Map.mem_map.mp present
    exact equal ▸ bounded edge
  · rw [Data.List.Map.length_map]
    exact short

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve)}
  {included : Geometry.Grid.Extension.CoordinateInclusion bank.grid grid}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
    {vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid}

/-- A retained regular factor is bounded by the original regular-occurrence count squared times their common bound. -/
private theorem Inclusion.ConnectorControl.regular_factor_bound
    {regulars : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := faces) included edges vertices)}
    {word : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)} (factor :
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.RegularFactor included
      edges vertices regulars word)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) {target :
      Fraction.Rational} (nonnegative : 0 ≤ target)
    (small : ∀ occurrence ∈ regulars, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value occurrence.word) ≤ target) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value word) ≤
      (regulars.length : Fraction.Rational) ^ 2 * target := by
  obtain ⟨selected, present, equal⟩ := factor
  have readback : Topology.Surface.Sewing.SewingRetraction.wordValue value (selected.flatMap
    OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence.word)
    =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (selected.map (fun occurrence =>
        Topology.Surface.Sewing.SewingRetraction.wordValue value occurrence.word)) := by
    clear present equal
    induction selected with
    | nil => rfl
    | cons occurrence rest ih =>
        rw [Data.List.Flatten.flatMap_cons, Topology.Surface.Sewing.SewingRetraction.wordValue_append]
        exact congrArg (Topology.Surface.Sewing.SewingRetraction.wordValue value occurrence.word + ·) ih
  rw [equal, readback]
  apply Path.IncrementArea.sum_bound_of_length nonnegative
  · intro reading member
    obtain ⟨occurrence, inSelected, same⟩ := Data.List.Map.mem_map.mp member
    exact same ▸ small occurrence (present.subset inSelected)
  · rw [Data.List.Map.length_map]
    exact present.length_le

/-- The original connector's certified regular factor bounds its area by the retained connector weight times the regular
target. -/
private theorem Inclusion.ConnectorControl.connector_weight_bound
    {regulars : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := faces) included edges vertices)}
    {term : Topology.Mesh.RetracingWords.AreaTerm vertices.count} (regular :
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.RegularConnector included
      edges vertices regulars term)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) {target edgeBound :
      Fraction.Rational}
    (nonnegative : 0 ≤ target) (edgeNonnegative : 0 ≤ edgeBound)
    (bounded : ∀ edge, Data.Gaussian.Norm.Basic.normSq (value edge) ≤ edgeBound)
    (small : ∀ occurrence ∈ regulars, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value occurrence.word) ≤ target) :
    Data.Gaussian.Norm.Basic.normSq (term.evaluate value) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl.connectorWeight edgeBound regulars.length term *
      target := by
  cases term with
  | polygon => exact regular.elim
  | cross coefficient first last =>
      let magnitude := (((first.length + last.length : Nat) : Fraction.Rational) ^ 2 * edgeBound)
      let localBound := (regulars.length : Fraction.Rational) ^ 2 * target
      have magnitudeNonnegative : 0 ≤ magnitude := Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
          edgeNonnegative
      have localNonnegative : 0 ≤ localBound := Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
          nonnegative
      have product : Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value
        first) * Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value last) ≤
        magnitude * localBound := by
        rcases regular with left | right
        · have estimate := Fraction.Order.Arithmetic.mul_le_mul_direct
            (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl.regular_factor_bound left value nonnegative
            small)
            (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl.word_bound value edgeNonnegative bounded last
              (Nat.le_add_left last.length first.length)) (Gaussian.Norm.Basic.normSq_nonneg _) localNonnegative
          exact estimate.trans_eq (by change localBound * magnitude = magnitude * localBound; ring1)
        · exact Fraction.Order.Arithmetic.mul_le_mul_direct
            (word_bound value edgeNonnegative bounded first
            (Nat.le_add_right first.length last.length))
            (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl.regular_factor_bound right value nonnegative
              small) (Gaussian.Norm.Basic.normSq_nonneg _) magnitudeNonnegative
      change Data.Gaussian.Norm.Basic.normSq ((coefficient : Gaussian.Basic.Canonical) * Path.BoundaryRibbon.area
        (Topology.Surface.Sewing.SewingRetraction.wordValue value first)
        (Topology.Surface.Sewing.SewingRetraction.wordValue value last)) ≤ _
      rw [Gaussian.Norm.Basic.normSq_mul]
      have area := (Path.BoundaryRibbon.area_bound (Topology.Surface.Sewing.SewingRetraction.wordValue value first)
        (Topology.Surface.Sewing.SewingRetraction.wordValue value last)).trans
        ((show 4 * Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value first)
          * Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value last) =
          4 * (Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value first) *
            Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value last)) by
            ring1).trans_le
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)))
      exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct area (Gaussian.Norm.Basic.normSq_nonneg
        _)).trans_eq (by
        unfold Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl.connectorWeight
        dsimp only [-eq_self, -iff_self, magnitude, localBound]
        ring1)

variable {start : Gaussian.Basic.Canonical} {member : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid
  start}
  {tree : Geometry.Grid.RowCircuitOrder.CellCircuits bank.grid start} {partition :
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition faces tree} {sheet : Fin 2}

/-- Take the nonnegative maximum of the original compiled connector weights at the supplied edge bound. -/
@[expose] def
  OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled.connectorWeight
  (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
  included edges vertices member partition sheet)
    (edgeBound : Fraction.Rational) : Fraction.Rational :=
  max 0 (Path.Dyadic.SourceSampleResampling.maximum (compiled.connectorTerms.map
    (Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl.connectorWeight edgeBound compiled.regulars.length)))

/-- The retained compiled connector-weight maximum is nonnegative. -/
theorem
  OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled.connectorWeight_nonnegative
    (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices member partition sheet) (edgeBound : Fraction.Rational) :
    0 ≤ compiled.connectorWeight edgeBound := Fraction.Order.Basic.le_max_left _ _

/-- The requested regular-cell error pays the full connector area residual.
The only remaining numerical premise is a uniform bound on the supplied
edge valuation, discharged by the shared face magnitude bank. -/
theorem
  OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled.connector_small
    (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices member partition sheet)
    (value : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) {edgeBound target :
      Fraction.Rational}
    (edgeNonnegative : 0 ≤ edgeBound) (bounded : ∀ edge, Data.Gaussian.Norm.Basic.normSq (value edge) ≤ edgeBound)
    (positive : 0 < target)
    (small : ∀ occurrence ∈ compiled.regulars, Data.Gaussian.Norm.Basic.normSq
      (Topology.Surface.Sewing.SewingRetraction.wordValue value occurrence.word) ≤
      Rational.Budget.Weighted.allowance (Rational.Budget.Aggregate.perTerm target compiled.connectorTerms.length)
        (compiled.connectorWeight edgeBound)) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Mesh.RetracingWords.AreaTerm.total value compiled.areaTerms -
      Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea value
        occurrence.word) compiled.regulars) < target := by
  let perTerm := Rational.Budget.Aggregate.perTerm target compiled.connectorTerms.length
  have termPositive := Rational.Budget.Aggregate.perTerm_positive positive compiled.connectorTerms.length
  have weightNonnegative := compiled.connectorWeight_nonnegative edgeBound
  have allowancePositive := Rational.Budget.Weighted.allowance_positive termPositive weightNonnegative
  have total : Topology.Mesh.RetracingWords.AreaTerm.total value compiled.connectorTerms =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (compiled.connectorTerms.map
        (Topology.Mesh.RetracingWords.AreaTerm.evaluate value)) := by
    induction compiled.connectorTerms with
    | nil => rfl
    | cons term rest ih => exact congrArg (term.evaluate value + ·) ih
  rw [compiled.area_split, Group.add_sub_cancel_left, total]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro reading present
  obtain ⟨term, inTerms, equal⟩ := Data.List.Map.mem_map.mp present
  rw [← equal, Data.List.Map.length_map]
  have bound := Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl.connector_weight_bound
    (compiled.connector_factors term inTerms) value allowancePositive.le edgeNonnegative bounded small
  have weightLe : Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorControl.connectorWeight edgeBound
    compiled.regulars.length term ≤ compiled.connectorWeight edgeBound :=
    (Path.Dyadic.SourceSampleResampling.le_maximum (Data.List.Map.mem_map_of_mem inTerms)).trans
      (Fraction.Order.Basic.le_max_right _ _)
  exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct weightLe allowancePositive.le).trans
    (Rational.Budget.Weighted.mul_allowance_le termPositive.le weightNonnegative))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

end
