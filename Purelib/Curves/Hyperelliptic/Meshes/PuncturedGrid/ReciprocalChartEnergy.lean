module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RamifiedReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Shared-depth odd energy on the retained surface chart evaluation

Regular data on an odd curve can only describe an empty parent bank.
Ramified data uses the existing chart energy with supplied shared bounds
and radial parameters. Its endpoint potential correction remains explicit.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
    InverseRootPolynomial.Coordinate} {minimum index depth readingIndex : Nat}
  {box : Rational.Box} {sample : Cap.Primitives.Sample cap differential
    index box}
  {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
    UniformReciprocalCover.ParentCovers parents}
  {prepared : ParentJoins.SideBank regular covers} {requests :
    SideRequests.SideBank.Requests sourceTarget reciprocalTarget coefficientTarget
    totalTarget areaTarget minimum prepared}
  {plans : Plans requests} {evaluated :
    SideRequests.SideBank.Evaluations sample depth readingIndex requests}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- This handles the empty regular branch without assuming a degree field
that the original request does not store. -/
theorem pairs_nil_of_branch (results : Results plans evaluated)
  (branch : HyperellipticReciprocal.originOrder curve = 1) :
    results.pairs = [] := by
  cases evaluated with
  | nil => rfl
  | cons first rest => exact Nat.noConfusion (plans.1.regular_chart.symm.trans branch)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Results

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
namespace Plan

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {start finish : Gaussian.Basic.Canonical} {segment : Geometry.ClearPath.ClearSegment curve.polynomial
    (Branches.Cuts.Ambient curve) start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : SegmentComparison placement piece
    differential parentSheet}
  {prepared : CapPreparation regular
    compared} {target areaTarget chartTarget : InverseRootPolynomial.Coordinate} {floor : Nat}

variable {request : CapRequest
  prepared target areaTarget floor} {charts :
  ChartRequest request chartTarget}
  {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {plan :
    Plan charts sample}

namespace Data

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
/-- The energy request on this exact chart datum, trivial for a regular chart and retained connected energy for a
ramified chart. -/
@[expose] def EnergyPreparation (data :
  Data plan depth
  readingIndex) (energyTarget : InverseRootPolynomial.Coordinate) (energyFloor : Nat) : Type 1 :=
  match request, charts, plan, data with
  | .regular _, _, _, _ => PUnit
  | .ramified _ _, _, _, data => Charts.Reciprocal.Disk.ConnectedEnergy.EnergyPreparation data
    energyTarget energyFloor

/-- Prepare the chart datum's actual energy request with the supplied radius, positive target and stage floor. -/
@[expose] def prepareEnergy (data :
  Data plan depth
  readingIndex)
    (bounds : Charts.Reciprocal.Cap.EnergyBounds sample
      RootContinuation.RootRadialGeometry.domain)
    (energyTarget : InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
      EnergyPreparation
      data energyTarget energyFloor :=
  match request, charts, plan, data with
  | .regular _, _, _, _ => ⟨⟩
  | .ramified _ _, _, _, data => Charts.Reciprocal.Disk.ConnectedEnergy.Evaluation.prepareEnergy data
    bounds energyTarget positive energyFloor

/-- The evaluated energy data on this exact retained chart preparation and shared reading stage. -/
@[expose] def EnergyData (data :
  Data plan depth
  readingIndex) (energyTarget : InverseRootPolynomial.Coordinate) (energyFloor energyDepth : Nat) : Type 1
  :=
  match request, charts, plan, data with
  | .regular _, _, _, _ => PUnit
  | .ramified _ _, _, _, data =>
      { energy : Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy data energyTarget energyFloor //
        energy.depth = energyDepth }

end

variable {data :
  Data plan depth
  readingIndex} {energyTarget : InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

/-- The sufficient reading stage retained by the chart's energy preparation. -/
@[expose] def EnergyPreparation.minimum (preparation :
  EnergyPreparation
  data energyTarget energyFloor) : Nat :=
  match request, charts, plan, data, preparation with
  | .regular _, _, _, _, _ => energyFloor
  | .ramified _ _, _, _, _, preparation =>
    Charts.Reciprocal.Disk.ConnectedEnergy.EnergyPreparation.minimum preparation

/-- Evaluate the retained ramified energy preparation at the supplied common stage; regular data retain the trivial
witness. -/
@[expose] def EnergyPreparation.evaluate (preparation :
  EnergyPreparation
  data energyTarget energyFloor)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (oriented : ∀ parent ∈ compared.entered.cache.parents, 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0)
      (parent.edge.point 1))
    (parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth) (later : preparation.minimum ≤ energyDepth) :
    EnergyData
      data energyTarget energyFloor energyDepth := by
  cases request with
  | regular original => exact ⟨⟩
  | ramified degree original =>
      exact ⟨Charts.Reciprocal.Disk.ConnectedEnergy.EnergyPreparation.evaluate preparation branch oriented
        parameters later, rfl⟩

namespace EnergyData

/-- The actual ramified energy reading, or zero for the regular chart case. -/
@[expose] def value (energy :
  EnergyData
  data energyTarget energyFloor energyDepth) : Gaussian :=
  match request, charts, plan, data, energy with
  | .regular _, _, _, _, _ => 0
  | .ramified _ _, _, _, _, energy => energy.val.connected.energy

/-- Retain the shifted potentials and the trace-origin term, with their signs. -/
@[expose] def boundary (energy :
  EnergyData
  data energyTarget energyFloor energyDepth) : Gaussian :=
  match request, charts, plan, data, energy with
  | .regular _, _, _, _, _ => 0
  | .ramified _ _, _, _, data, energy =>
      -Path.BoundaryRibbon.area
        (Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest.Plan.Evaluation.original data).firstValue
        data.connected.summary.total + energy.val.connected.boundary

/-- The evaluated ramified energy is nonnegative, as is the zero regular-chart reading. -/
theorem lower (energy :
  EnergyData
  data energyTarget energyFloor energyDepth) (positive : 0 < energyTarget) :
    -energyTarget < energy.value.im / 4 := by
  cases request with
  | regular original =>
      change -energyTarget < (0 : InverseRootPolynomial.Coordinate) / 4
      rw [Fraction.Field.zero_div_direct]
      exact (Arithmetic.neg_lt_neg_direct positive).trans_eq (by ring1)
  | ramified degree original => exact energy.val.lower

open
  Data.EnergyData
  in
/-- In the ramified case, the evaluated energy pays a quarter of the supplied squared coordinate magnitude. -/
private theorem quarter_le {value : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ value) : value /
  4 ≤ value := by
  apply (Field.div_le_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 4)).mpr
  exact (show value = value * 1 by ring1).trans_le
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide) nonnegative)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- The estimate applies to the literal path retained by the surface chart.
No independent source or endpoint evaluation is substituted. -/
theorem boundary_close (energy :
  EnergyData
  data energyTarget energyFloor energyDepth)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (positive : 0 <
      chartTarget) :
    Gaussian.Norm.Basic.normSq (energy.value - (-data.summary.area + energy.boundary)) < 256 * (4 * chartTarget
      + target) := by
  cases request with
  | regular original =>
      have empty := data.cap.parents.pairs_nil_of_branch branch
      change Gaussian.Norm.Basic.normSq (0 - (-data.cap.cap.area + 0)) < _
      rw [data.cap.cap.area_eq, empty]
      change Gaussian.Norm.Basic.normSq (0 - (-(0 : Gaussian.Basic.Canonical) + 0)) < _
      rw [neg_zero, Gaussian.Basic.add_zero, Gaussian.Basic.sub_zero, Gaussian.Norm.Basic.normSq_zero]
      exact Arithmetic.mul_pos_direct (by decide +kernel)
        ((by ring1 : (0 : InverseRootPolynomial.Coordinate) = 0 + 0).trans_lt
          (Arithmetic.add_lt_add_direct (Arithmetic.mul_pos_direct (by
              decide : (0 : InverseRootPolynomial.Coordinate) < 4) positive) original.positive))
  | ramified degree original =>
      have one := Field.div_pos_direct original.positive (by
          decide : (0 : InverseRootPolynomial.Coordinate) < 4)
      have two := Field.div_pos_direct one (by
          decide : (0 : InverseRootPolynomial.Coordinate) < 4)
      have three := Field.div_pos_direct two (by
          decide : (0 : InverseRootPolynomial.Coordinate) < 4)
      have paid :=
        (quarter_le
        three.le).trans
        ((quarter_le
        two.le).trans
        ((quarter_le
        one.le).trans
        (quarter_le
        original.positive.le)))
      have bound := energy.val.boundary_close
      have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_rfl : 4 * chartTarget ≤ 4 * chartTarget) paid) (by
            decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 256)
      change Gaussian.Norm.Basic.normSq (energy.val.connected.energy - (-data.connected.summary.area +
        (-Path.BoundaryRibbon.area
          (Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest.Plan.Evaluation.original data).firstValue
          data.connected.summary.total +
          energy.val.connected.boundary))) < _
      exact (congrArg Gaussian.Norm.Basic.normSq (by ring1)).trans_lt (bound.trans_le scaled)

end EnergyData
end Data

namespace Evaluation

variable (evaluated :
  Evaluation plan
  depth readingIndex)

/-- Semantic equality between the cached summary and its retained data. -/
theorem data_area : evaluated.summary.area = evaluated.data.summary.area := by
  rw [evaluated.summary.area_eq, evaluated.path_eq, evaluated.data.summary.area_eq]

/-- The original evaluated chart total equals the boundary reading of its exact retained energy datum. -/
theorem data_total : evaluated.summary.total = evaluated.data.summary.total := by
  rw [evaluated.summary.total_eq, evaluated.path_eq, evaluated.data.summary.total_eq]

end Evaluation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan
