module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
public import Purelib.Integration.Path.Dyadic.SourceSampleResampling
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Polynomial.Dense.Basic
import Purelib.Algebra.Group.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! Quantitative control of the retained connector correction. The bound
pays the actual cached term count twice and uses only cross products;
the regular polygons remain outside the error estimate. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
  (IsConnectorTerm ResplitCompiled)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_mul normSq_nonneg)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

/-- The explicit squared-norm envelope of an actual retained cross term, using its coefficient and both original word
values. -/
def Inclusion.ConnectorBounds.connectorEstimate (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical) :
  RetracingWords.AreaTerm
  count → Fraction.Rational
  | .polygon _ => 0
  | .cross coefficient first last =>
      Data.Gaussian.Norm.Basic.normSq (coefficient : Data.Gaussian.Basic.Canonical) * (4 *
        Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value first) *
        Data.Gaussian.Norm.Basic.normSq (SewingRetraction.wordValue value last))

/-- An actual certified connector cross term satisfies its retained coefficient-and-word magnitude envelope. -/
private theorem Inclusion.ConnectorBounds.connector_estimate (value : Stokes.OrientedEdge count →
  Data.Gaussian.Basic.Canonical) (term :
  RetracingWords.AreaTerm count)
    (cross : CircuitPartition.IsConnectorTerm term) : Data.Gaussian.Norm.Basic.normSq (term.evaluate value) ≤
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorBounds.connectorEstimate value term := by
  cases term with
  | polygon => exact cross.elim
  | cross coefficient first last =>
      change Data.Gaussian.Norm.Basic.normSq ((coefficient : Data.Gaussian.Basic.Canonical) *
        BoundaryRibbon.area (SewingRetraction.wordValue value first) (SewingRetraction.wordValue value last)) ≤ _
      rw [Data.Gaussian.Norm.Basic.normSq_mul]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (BoundaryRibbon.area_bound _ _) (Data.Gaussian.Norm.Basic.normSq_nonneg _)

/-- Evaluating the retained area-term list gives exactly the Gaussian sum of its actual term readings. -/
private theorem Inclusion.ConnectorBounds.total_eq (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical)
  (terms : List
  (RetracingWords.AreaTerm count)) :
    AreaTerm.total value terms = Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (AreaTerm.evaluate value)) :=
      by
  induction terms with
  | nil => rfl
  | cons term tail ih => exact congrArg (term.evaluate value + ·) ih

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {grid :
    Polynomial.Geometry.Grid.ClearGrid curve.polynomial (Ambient
    curve)}
  {included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion bank.grid grid}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid}
  {start : Purelib.Data.Gaussian.Basic.Canonical} {member :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start}
  {tree : Purelib.Polynomial.Geometry.Grid.RowCircuitOrder.CellCircuits bank.grid start} {partition :
    CircuitPartition faces tree}
    {sheet : Fin 2}

/-- An explicit finite bound for the actual residual after retaining all regular polygon areas. It is not a vanishing
assertion: the displayed cross-factor envelope must still be paid by the analytic requests. -/
theorem
  OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled.connector_error_bound
    (compiled : CircuitPartition.ResplitCompiled included edges vertices member partition sheet)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (AreaTerm.total value compiled.areaTerms -
      CellBoundary.sumValues (fun occurrence => RetracingWords.wordArea value occurrence.word) compiled.regulars) ≤
      (compiled.connectorTerms.length : Fraction.Rational) * ((compiled.connectorTerms.length : Fraction.Rational) *
        SourceSampleResampling.maximum (compiled.connectorTerms.map
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorBounds.connectorEstimate value))) := by
  rw [compiled.area_split, Algebra.Group.add_sub_cancel_left,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorBounds.total_eq]
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (compiled.connectorTerms.map (AreaTerm.evaluate value))
    (SourceSampleResampling.maximum (compiled.connectorTerms.map
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorBounds.connectorEstimate value))) (by
      intro reading belongs
      obtain ⟨term, termMember, equal⟩ := Map.mem_map.mp belongs
      rw [← equal]
      exact (Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ConnectorBounds.connector_estimate value term
        (compiled.connector_only term termMember)).trans
        (SourceSampleResampling.le_maximum (Map.mem_map_of_mem termMember)))
  simpa only [Data.List.Map.length_map] using bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
