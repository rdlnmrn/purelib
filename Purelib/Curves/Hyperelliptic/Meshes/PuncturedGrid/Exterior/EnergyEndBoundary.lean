module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartEnergy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyEndAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SegmentNonempty
import Purelib.Riemann.Paths.SegmentGapArea
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RamifiedReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Boundary readback from the retained exterior energy endpoints

The endpoint-bank boundary is a specification of existing cached energy
terms. Append and budget weakening preserve those same values and potentials.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {index readingIndex energyDepth : Nat} {box :
    Rational.Box}
  {sample : Cap.Primitives.Sample cap differential index box} {target :
    InverseRootPolynomial.Coordinate}

section EnergyEndBank

/-- The original endpoint-potential jumps and joining areas, accumulated from a supplied preceding value. -/
@[expose] def boundary : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} →
      EnergyEndBank sample readingIndex energyDepth target
      prepared → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian
  | _, _, _, .nil, _ => 0
  | _, _, _, .cons head tail, previous =>
      head.lastPotential - head.firstPotential + Path.BoundaryRibbon.area previous head.firstValue +
        boundary tail
        head.lastValue

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
  UniformReciprocalCover.ParentCovers parents}
  {prepared : ParentJoins.SideBank regular covers}

/-- The retained endpoint boundary equals the final potential minus the initial potential and the exact original error
sum. -/
theorem boundary_identity (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared) (value potential : InverseRootPolynomial.Gaussian) :
    ends.boundary value = ends.lastPotential potential - potential - Gaussian.Norm.Sum.Basic.gaussianSum
      (ends.errors value potential) := by
  induction ends generalizing value potential with
  | nil => change (0 : InverseRootPolynomial.Gaussian) = potential - potential - 0; ring1
  | cons head tail ih =>
      change head.lastPotential - head.firstPotential + Path.BoundaryRibbon.area value head.firstValue + tail.boundary
        head.lastValue =
        tail.lastPotential head.lastPotential - potential -
          ((head.firstPotential - potential - Path.BoundaryRibbon.area value head.firstValue) +
            Gaussian.Norm.Sum.Basic.gaussianSum (tail.errors head.lastValue head.lastPotential))
      rw [ih head.lastValue head.lastPotential]
      ring1

/-- Changing the preceding value adds exactly its area against the original first endpoint. -/
theorem boundary_translate (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared) (previous next : InverseRootPolynomial.Gaussian) :
    ends.boundary previous = ends.boundary next + Path.BoundaryRibbon.area (previous - next) ends.firstValue := by
  cases ends with
  | nil =>
    simp only [-eq_self, -iff_self, boundary,
      firstValue,
      Path.IncrementArea.area_zero_right, Gaussian.Basic.add_zero]; rfl
  | cons head tail =>
      simp only [-eq_self, -iff_self,
        boundary,
        firstValue]
      have split : Path.BoundaryRibbon.area previous head.firstValue = Path.BoundaryRibbon.area next head.firstValue +
        Path.BoundaryRibbon.area (previous - next) head.firstValue := by
        rw [← Path.IncrementArea.area_add_left, show next + (previous - next) = previous by ring1]
      rw [split]
      ring1

/-- The original residual is the retained endpoint boundary plus its closing endpoint chord. -/
theorem residual_eq (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared) :
    ends.residual = ends.boundary ends.firstValue + Path.BoundaryRibbon.area (ends.lastValue ends.firstValue)
      ends.firstValue := by
  rw [residual,
    boundary_identity ends ends.firstValue
    ends.firstPotential]
  ring1

/-- Increasing the allowed error preserves the original first endpoint value. -/
theorem weaken_firstValue (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    {larger : InverseRootPolynomial.Coordinate} (le : target ≤ larger) : (ends.weaken le).firstValue =
      ends.firstValue := by
  cases ends <;> rfl

/-- Increasing the allowed error preserves the original last endpoint value. -/
theorem weaken_lastValue (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    {larger : InverseRootPolynomial.Coordinate} (le : target ≤ larger) (previous :
      InverseRootPolynomial.Gaussian) :
    (ends.weaken le).lastValue previous = ends.lastValue previous := by
  induction ends generalizing previous with
  | nil => rfl
  | cons head tail ih => exact ih head.lastValue

/-- Increasing the allowed error preserves every original boundary value. -/
theorem weaken_boundary (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    {larger : InverseRootPolynomial.Coordinate} (le : target ≤ larger) (previous :
      InverseRootPolynomial.Gaussian) :
    (ends.weaken le).boundary previous = ends.boundary previous := by
  induction ends generalizing previous with
  | nil => rfl
  | cons head tail ih => exact congrArg (_ + ·) (ih head.lastValue)

/-- A nonempty original endpoint bank has a last value independent of the supplied preceding value. -/
theorem lastValue_independent (ends : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    (nonempty : parents ≠ []) (previous next : InverseRootPolynomial.Gaussian) : ends.lastValue previous =
      ends.lastValue next := by
  cases ends with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => rfl

variable {otherParents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {otherCovers :
  UniformReciprocalCover.ParentCovers otherParents}
  {other : ParentJoins.SideBank regular otherCovers}

/-- The concatenated bank boundary is the first boundary plus the second boundary started at the actual retained last
value. -/
theorem append_boundary (left : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    (right : EnergyEndBank sample readingIndex energyDepth
      target other) (previous : InverseRootPolynomial.Gaussian) :
    (left.append right).boundary previous = left.boundary previous + right.boundary (left.lastValue previous) := by
  induction left generalizing previous with
  | nil => change right.boundary previous = 0 + right.boundary previous; ring1
  | cons head tail ih =>
    simp only [-eq_self, -iff_self, append,
      boundary,
      lastValue, ih]; ring1

/-- The concatenated bank's last value is the second bank's last value after the original first bank. -/
theorem append_lastValue (left : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    (right : EnergyEndBank sample readingIndex energyDepth
      target other) (previous : InverseRootPolynomial.Gaussian) :
    (left.append right).lastValue previous = right.lastValue (left.lastValue previous) := by
  induction left generalizing previous with
  | nil => rfl
  | cons head tail ih => exact ih head.lastValue

/-- Concatenation preserves the first endpoint of a nonempty original first bank. -/
theorem append_firstValue (left : EnergyEndBank sample
  readingIndex energyDepth target prepared)
    (right : EnergyEndBank sample readingIndex energyDepth
      target other) (nonempty : parents ≠ []) :
    (left.append right).firstValue = left.firstValue := by
  cases left with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => rfl

end EnergyEndBank

namespace SideBank.ChartReplacements.EnergyData

variable {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget energyTarget :
  InverseRootPolynomial.Coordinate}
  {minimum depth energyFloor : Nat}
  {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
    UniformReciprocalCover.ParentCovers parents}
  {prepared : ParentJoins.SideBank regular covers}
  {requests : SideRequests.SideBank.Requests sourceTarget reciprocalTarget
    coefficientTarget totalTarget areaTarget minimum prepared}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- The actual odd-degree endpoint bank reads exactly the original cached chart-replacement energy boundary terms. -/
theorem endBank_boundary (evaluated : SideRequests.SideBank.Evaluations sample
  depth readingIndex requests) (charts : SideChartRequests.ChartReplacements target
  evaluated)
    (energies : SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth
      evaluated charts)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (previous :
      InverseRootPolynomial.Gaussian) :
    (EnergyEndReadback.ChartReplacements.EnergyData.endBank branch evaluated charts
      energies).boundary previous = Gaussian.Norm.Sum.Basic.gaussianSum
      (SideEnergy.EnergyData.boundaryTerms evaluated charts energies previous) :=
      by
  induction evaluated generalizing previous with
  | nil => cases charts; rfl
  | cons first rest ih =>
      cases charts with
      | cons replacement head tail =>
          exact congrArg (_ + ·) (ih tail energies.2 first.cap.joined.lastValue)

end SideBank.ChartReplacements.EnergyData
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
namespace Plan
namespace Data.EnergyData

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest.Plan
  renaming Evaluation -> ChartEvaluation

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
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {compared : SegmentComparison placement piece
    differential parentSheet}
  {prepared : CapPreparation regular
    compared} {target areaTarget chartTarget : InverseRootPolynomial.Coordinate} {floor : Nat}

variable {request : CapRequest
  prepared target areaTarget floor} {charts :
  ChartRequest request chartTarget}
  {index depth readingIndex energyFloor energyDepth : Nat} {box : Rational.Box}
  {sample : Cap.Primitives.Sample cap differential index box} {plan :
    Plan charts sample}
  {data : Data plan
    depth readingIndex} {energyTarget : InverseRootPolynomial.Coordinate}

/-- In odd degree, retained regular-side plans can contain no original parents. -/
private theorem regular_parents_nil
    {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
      InverseRootPolynomial.Coordinate} {minimum : Nat}
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {covers : UniformReciprocalCover.ParentCovers parents} {bank :
      ParentJoins.SideBank regular covers}
    {requests : SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum bank}
    (plans : RegularSides.Plans requests) (branch :
      HyperellipticReciprocal.originOrder curve = 1) : parents = [] := by
  cases requests with
  | nil => rfl
  | cons head tail => exact Nat.noConfusion (plans.1.regular_chart.symm.trans branch)

/-- The chart total is the displacement between the very same retained endpoints. -/
theorem endBank_total (energy :
  EnergyData
  data energyTarget energyFloor energyDepth)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (nonempty :
      compared.entered.cache.parents ≠ []) :
    data.summary.total = (energy.endBank branch).lastValue (energy.endBank branch).firstValue -
      (energy.endBank branch).firstValue := by
  cases request with
  | regular original => exact False.elim (nonempty
    (regular_parents_nil
    original.request.plans branch))
  | ramified degree original =>
      obtain ⟨energy, sameDepth⟩ := energy
      cases sameDepth
      change data.connected.summary.total = _
      rw
        [endBank,
        EnergyEndBank.weaken_firstValue,
        EnergyEndBank.weaken_lastValue,
        EnergyEndReadback.ChartReplacements.EnergyData.endBank_firstValue,
          EnergyEndReadback.ChartReplacements.EnergyData.endBank_lastValue,
        data.total_eq, (ChartEvaluation.original
          data).total_eq, (ChartEvaluation.original
          data).lastValue_eq,
          (ChartEvaluation.original
          data).firstValue_eq]

/-- Read the local cached energy boundary as endpoint-bank boundary minus
its endpoint chord. No new fan or primitive evaluation is performed. -/
theorem endBank_boundary (energy :
  EnergyData
  data energyTarget energyFloor energyDepth)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (nonempty :
      compared.entered.cache.parents ≠ []) :
    energy.boundary = (energy.endBank branch).boundary (energy.endBank branch).firstValue -
      Path.BoundaryRibbon.area (energy.endBank branch).firstValue
        ((energy.endBank branch).lastValue (energy.endBank branch).firstValue) := by
  cases request with
  | regular original => exact False.elim (nonempty
    (regular_parents_nil
    original.request.plans branch))
  | ramified degree original =>
      obtain ⟨energy, sameDepth⟩ := energy
      cases sameDepth
      change -Path.BoundaryRibbon.area
        (ChartEvaluation.original data).firstValue
        data.connected.summary.total + energy.connected.boundary = _
      rw
        [endBank,
        EnergyEndBank.weaken_firstValue,
        EnergyEndBank.weaken_lastValue,
        EnergyEndBank.weaken_boundary,
        EnergyEndReadback.ChartReplacements.EnergyData.endBank_firstValue,
          EnergyEndReadback.ChartReplacements.EnergyData.endBank_lastValue,
        EnergyEndBank.SideBank.ChartReplacements.EnergyData.endBank_boundary,
          energy.connected.boundary_eq,
        data.total_eq, (ChartEvaluation.original
          data).total_eq, (ChartEvaluation.original
          data).lastValue_eq,
          (ChartEvaluation.original
          data).firstValue_eq,
        Path.BoundaryRibbon.area_sub_self_right]
      ring1

end Data.EnergyData
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan
