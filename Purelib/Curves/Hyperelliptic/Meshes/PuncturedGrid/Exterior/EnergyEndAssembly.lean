module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergyData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartAcquisition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalChartEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RamifiedReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
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

open Purelib

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Actual surface energy endpoints on the original joined parent bank

Concatenate retained endpoint packets across heterogeneous segment budgets.
The resulting bank uses exactly the original surface occurrences and owners;
root-return requests can therefore consume it without another preparation.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {index readingIndex energyDepth : Nat} {box :
    Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {target :
    Normalization.InverseRootPolynomial.Coordinate}

namespace EnergyEndBank

/-- Concatenate the actual endpoint packets of two original side banks while retaining their common sample, stage and
target. -/
@[expose] def append : {first last : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve
  differential)} →
    {firstCovers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers first} → {lastCovers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers last} →
    {left : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular firstCovers} → {right :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular lastCovers} →
    EnergyEndBank sample readingIndex energyDepth target
      left → EnergyEndBank sample readingIndex energyDepth
      target right →
    EnergyEndBank sample readingIndex energyDepth target
      (left.append right)
  | _, _, _, _, _, _, .nil, right => right
  | _, _, _, _, _, _, .cons head tail, right => .cons head (append tail right)

end EnergyEndBank

namespace RegularSides.Plans

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- In odd degree, regular request data has no parents to contribute. -/
@[expose] def emptyEndBank
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
      Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat} :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    Hyperelliptic.Charts.Reciprocal.Disk.RegularSides.Plans requests →
      EnergyEndBank sample readingIndex energyDepth target
      prepared
  | _, _, _, .nil, _ => .nil
  | _, _, _, .cons _ _, plans => Nat.noConfusion (plans.1.regular_chart.symm.trans branch)

end RegularSides.Plans

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
namespace Plan
namespace Data.EnergyData

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {start finish : Gaussian.Basic.Canonical} {segment : Geometry.ClearPath.ClearSegment curve.polynomial
    (Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
    differential parentSheet}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation regular
    compared} {target areaTarget chartTarget : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
  prepared target areaTarget floor} {charts :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest request chartTarget}
  {index depth readingIndex energyFloor energyDepth : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {plan :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan charts sample}
  {data : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data plan
    depth readingIndex} {energyTarget : Normalization.InverseRootPolynomial.Coordinate}

/-- Only retained endpoint data are transported through the common-depth
certificate; the chart, source samples and parent owners stay unchanged. -/
@[expose] def endBank (energy :
  Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data.EnergyData
  data energyTarget energyFloor energyDepth)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    Charts.Reciprocal.Disk.EnergyEndBank sample readingIndex energyDepth
      chartTarget prepared.path.bank := by
  cases request with
  | regular original => exact original.request.plans.emptyEndBank branch
  | ramified degree original =>
      obtain ⟨energy, sameDepth⟩ := energy
      cases sameDepth
      let retained := Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest.Plan.Evaluation.original data
      let ends := Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank
        branch retained.separated.parents data.replacements energy.parents
      have paid : charts.parentTarget ≤ chartTarget := by
        rw [charts.parentTarget_eq]
        exact Rational.Budget.Aggregate.perTerm_le charts.positive.le _
      exact ends.weaken paid

end Data.EnergyData
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Normalization.InverseRootPolynomial.Coordinate} {floor index depth readingIndex :
    Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}

variable {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

/-- Concatenate the retained chart-entry energy endpoints on the exact original occurrence spine in odd degree. -/
@[expose] def endBank (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget floor)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget energyFloor
      energyDepth entries →
    Charts.Reciprocal.Disk.EnergyEndBank sample readingIndex energyDepth
      chartTarget

        (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
        (entries.map (fun entry => entry.entry.occurrence))).bank
  | [], _ => .nil
  | _ :: tail, energies => (energies.1.endBank branch).append
    (endBank branch tail
    energies.2)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    ExteriorProgram.SurfacePreparation
    regular domains program}

set_option genInjectivity false in
/-- All cross-occurrence and closing stages are selected from the original
root-return bank before evaluating any chart endpoint readings. -/
structure EnergyRootRequest (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program) (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained joined cap bank of the original surface preparation. -/ joined :
    JoinedCap
    prepared
  /-- The positive root-return allowance bounded by the supplied target and one. -/ allowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The allowance is exactly the minimum of the target and one. -/ allowance_eq : allowance = min target 1
  /-- The retained root-return allowance is positive. -/ positive : 0 < allowance
  /-- The retained allowance is at most one. -/ small : allowance ≤ 1
  /-- The original root-return requests for every retained inter-parent junction. -/ junctions :
    Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests allowance floor joined.spine.bank joined.links
  /-- The original closing root-return request on the same joined bank. -/ closing :
    Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest allowance floor joined.spine.bank joined.closing
  /-- The cached common sufficient root-return reading index. -/ index : Nat
  /-- The index is exactly the maximum of the retained junction and closing stages. -/ index_eq : index = max
    junctions.maximum closing.maximum

constructive_injectivity EnergyRootRequest

namespace EnergyRootRequest

variable {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Prepare the original joined component bank, bounded positive allowance and root-junction and closing requests before
choosing their common stage. -/
@[expose] def build (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program) (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor :
  Nat) :

      SurfacePreparation.EnergyRootRequest
      prepared target floor :=
  let joined :=
    JoinedCap.build
    prepared
  let allowance := min target 1
  have allowancePositive : 0 < allowance := Fraction.Order.Basic.lt_min positive (by decide)
  let junctions := Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.JunctionRequests.build allowance
    allowancePositive floor joined.spine.bank joined.links
  let closing := Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest.build allowance allowancePositive
    floor joined.spine.bank joined.closing
  ⟨joined, allowance, rfl, allowancePositive, Fraction.Order.Basic.min_le_right _ _, junctions, closing, max
    junctions.maximum closing.maximum, rfl⟩

variable {index depth readingIndex energyFloor energyDepth : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
  {localTarget localArea chartTarget energyTarget : Normalization.InverseRootPolynomial.Coordinate} {sourceFloor : Nat}

/-- Equality transport changes only the dependent bank index. -/
@[expose] def transportEnds {first last : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)} (same : first = last)
    {spine : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Retained regular (last.map (fun item =>
      item.compared.entered.cache.parents)).flatten}
    (spineEq : spine =
      SurfaceOccurrence.capSpine
      last)
    (ends : Charts.Reciprocal.Disk.EnergyEndBank sample readingIndex energyDepth
      chartTarget
      (SurfaceOccurrence.capSpine
      first).bank) :
    Charts.Reciprocal.Disk.EnergyEndBank sample readingIndex energyDepth
      chartTarget spine.bank := by
  cases same
  cases spineEq
  exact ends

/-- Transport along the original occurrence and spine equalities preserves the retained endpoint residual exactly. -/
theorem transportEnds_residual {first last : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)} (same : first = last)
    {spine : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Retained regular (last.map (fun item =>
      item.compared.entered.cache.parents)).flatten}
    (spineEq : spine =
      SurfaceOccurrence.capSpine
      last)
    (ends : Charts.Reciprocal.Disk.EnergyEndBank sample readingIndex energyDepth
      chartTarget
      (SurfaceOccurrence.capSpine
      first).bank) :

      (transportEnds
      same spineEq ends).residual = ends.residual := by
  cases same
  cases spineEq
  rfl

/-- Transport the exact retained endpoints to this original component bank. -/
@[expose] def endBank (request :
  SurfacePreparation.EnergyRootRequest
  prepared target floor)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget sourceFloor))
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (occurrences : entries.map (fun entry => entry.entry.occurrence) = prepared.occurrences) :
    Charts.Reciprocal.Disk.EnergyEndBank sample readingIndex energyDepth
      chartTarget request.joined.spine.bank := by
  exact
    transportEnds
    occurrences request.joined.spine_eq (energies.endBank branch entries)

/-- Reading endpoints through the component request preserves the exact original chart-entry residual. -/
theorem endBank_residual (request :
  SurfacePreparation.EnergyRootRequest
  prepared target floor)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget sourceFloor))
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (occurrences : entries.map (fun entry => entry.entry.occurrence) = prepared.occurrences) :
    (request.endBank entries energies branch occurrences).residual = (energies.endBank branch entries).residual :=

    transportEnds_residual
    occurrences request.joined.spine_eq _

/-- The retained component endpoint residual satisfies the original parent-count, chart-target and root-return allowance
bound at a sufficient stage. -/
theorem endBank_bound (request :
  SurfacePreparation.EnergyRootRequest
  prepared target floor)
    (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (regular := regular) sample
      shared depth readingIndex localTarget localArea chartTarget sourceFloor))
    (energies : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData energyTarget
      energyFloor energyDepth entries)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (occurrences : entries.map (fun entry => entry.entry.occurrence) = prepared.occurrences)
    (nonnegative : 0 ≤ chartTarget) (later : request.index ≤ readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (request.endBank entries energies branch occurrences).residual ≤
      2 * (((((prepared.occurrences.map (fun item => item.compared.entered.cache.parents)).flatten.length : Nat) :
        Normalization.InverseRootPolynomial.Coordinate) *
        ((((prepared.occurrences.map (fun item => item.compared.entered.cache.parents)).flatten.length : Nat) :
          Normalization.InverseRootPolynomial.Coordinate) * (80 * chartTarget + 2 * request.allowance))) +
          (80 * chartTarget + 2 * request.allowance)) :=
  (request.endBank entries energies branch occurrences).residual_bound branch nonnegative request.positive.le
    request.small request.junctions
    ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)) request.closing ((Data.Nat.Order.le_max_right _
      _).trans (request.index_eq ▸ later))

end EnergyRootRequest
end SurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
