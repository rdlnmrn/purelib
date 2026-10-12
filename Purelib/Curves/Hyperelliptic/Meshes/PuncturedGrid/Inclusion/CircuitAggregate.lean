module

import Purelib.Algebra.Group.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Polynomial.Geometry.Grid.FromStates

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
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitZero
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

public section

/-! One computed threshold pays the entire original regular-cell period
correction on the enlarged mesh. Both term-count factors are included. -/

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Data.List
open Purelib.Algebra

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {included : Geometry.Grid.Extension.CoordinateInclusion bank.grid base.bank.grid}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

/-- A compact exact bound for a retained list; the executable payload is
the common stage, computed from the individual certified requests. -/
@[expose] def RegularsSmallAt (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
      (differential : Fin genus)
    (target : Fraction.Rational) (occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := faces) included edges vertices))
    (floor : Nat) : Prop :=
  ∀ numericalIndex (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
    (Periods.PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics mesh), floor ≤
      numericalIndex →
    ∀ occurrence ∈ occurrences,
      Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh triangles.values) occurrence.word) <
        target

/-- Compute one sufficient stage for every original regular occurrence's zero-integral request.

The dependent receipt certifies each original word at every later shared numerical stage. -/
@[expose] def regularZeroRequests (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (source :
      Hyperelliptic.Differentials.Basic.Differential genus)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    (occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := faces) included edges vertices)) →
      { floor : Nat //
        Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.RegularsSmallAt mesh
        domains differential target occurrences floor }
  | [] => ⟨minimum, fun _ _ _ _ _ member => (List.not_mem_nil member).elim⟩
  | occurrence :: rest =>
      let first := occurrence.zeroRequest mesh domains source differential target positive minimum
      let last :=
        regularZeroRequests
        mesh domains source differential target positive minimum rest
      ⟨max first.val last.val, by
        intro stage numerics triangles later entry member
        rcases Membership.mem_cons.mp member with rfl | member
        · exact first.property stage numerics triangles ((Data.Nat.Order.le_max_left _ _).trans later)
        · exact last.property stage numerics triangles ((Data.Nat.Order.le_max_right _ _).trans later) entry member⟩

/-- Summing a finite list through the grid boundary sum equals the Gaussian sum of its mapped values. -/
private theorem sumValues_eq {Alpha : Type} (value : Alpha → Gaussian.Basic.Canonical) (entries : List Alpha) :
    Geometry.Grid.CellBoundary.sumValues value entries = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (entries.map value) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => exact congrArg (value entry + ·) ih

/-- The sum of all original regular-occurrence integral corrections meets the whole target above the computed common
stage.

The retained per-term allocation pays both factors of the actual occurrence count. -/
theorem regulars_aggregate_small (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (source :
      Hyperelliptic.Differentials.Basic.Differential genus)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat)
    (occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := faces) included edges vertices)) :
    let request :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests mesh
      domains source differential (Rational.Budget.Aggregate.perTerm target occurrences.length)
      (Rational.Budget.Aggregate.perTerm_positive positive _) minimum occurrences
    ∀ stage (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
      (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics mesh),
        request.val ≤ stage →
      Data.Gaussian.Norm.Basic.normSq (Geometry.Grid.CellBoundary.sumValues (fun occurrence =>
        Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh triangles.values)
        occurrence.word) occurrences) < target := by
  intro request stage numerics triangles later
  rw [Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.sumValues_eq]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro value member
  obtain ⟨occurrence, present, equal⟩ := Data.List.Map.mem_map.mp member
  rw [← equal, Map.length_map]
  exact (request.property stage numerics triangles later occurrence present).le

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition

end

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered

open Purelib.Algebra

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib
open Purelib.Data.List

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base next : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames next.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    next.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered in
/-- The original physical exterior's integral differs from the retained
branch word by less than the requested error, at every later shared stage.
This consumes the exact ordered compiler identity, not coordinate closure. -/
theorem resplit_exterior_integral_accurate (ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet)
    (included : Geometry.Grid.Extension.CoordinateInclusion base.bank.grid next.bank.grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex next.bank.grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    {newSheet : Fin 2}
    (compiled : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitCompiled
      included edges vertices (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember
      base.bank)
      ordered.prepared.partition newSheet)
    (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges next.faces)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames next.faces.regulars) (source :
      Hyperelliptic.Differentials.Basic.Differential genus)
    (differential : Fin genus) (target : Fraction.Rational) (positive : 0 < target) (minimum : Nat) :
    let request :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regularZeroRequests mesh
      domains source differential (Rational.Budget.Aggregate.perTerm target compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive positive _) minimum compiled.regulars
    ∀ stage (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      (Periods.PeriodMatrix.standardDifferential differential) stage domains)
      (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics mesh),
        request.val ≤ stage →
      Data.Gaussian.Norm.Basic.normSq (edges.chainValue vertices
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh triangles.values)
        (included.resplit base.bank.exterior
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) newSheet -
        Topology.Surface.Sewing.SewingRetraction.wordValue
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh triangles.values) compiled.word) <
          target := by
  intro request stage numerics triangles later
  rw [ordered.resplit_exterior_values included edges vertices reference compiled _
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse mesh triangles.values),
      Group.add_sub_cancel_left]
  exact
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.regulars_aggregate_small
    mesh domains source differential target positive minimum
    compiled.regulars stage numerics triangles later

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered
