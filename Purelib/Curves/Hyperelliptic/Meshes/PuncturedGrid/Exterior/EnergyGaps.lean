module
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyEndAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergyData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.SegmentGapArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyPolygon
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank.SideBank

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open
  ExteriorProgram.SurfacePreparation

open Purelib.Data.Rat

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.Paths

public section

/-!
# Original root requests control every retained surface segment gap

All inequalities read the acquired primitive endpoints at the selected
common stage. Grouping removes internal parent gaps but preserves each
cross-occurrence gap and the original final root-return gap.
-/

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Normalization

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank.EnergyEnds

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank (EnergyEnds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JunctionRequests (Request)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parent : CenteredEdge curve differential} {patch :
    PreparedPatch parent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Cover data}
  {index readingIndex energyDepth : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {target
    joining : Coordinate} {joinFloor : Nat}

variable {prepared : Preparation regular cover}

variable {otherCount : Nat} {otherParent : CenteredEdge curve
  differential}
  {otherPatch : PreparedPatch otherParent}
  {otherData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
    {otherCover : Cover otherData}
  {next : Preparation regular otherCover}

/-- The original paid junction request bounds the actual primitive-value gap between two retained energy endpoints. -/
theorem gap_bound (left : EnergyEndBank.EnergyEnds sample readingIndex energyDepth target prepared)
    (right : EnergyEndBank.EnergyEnds sample readingIndex energyDepth target next)
    {joined : ArcOwners.Join prepared.boundary.last.point next.boundary.first.point}
    (request : JunctionRequests.Request prepared.boundary.last.bounds joined joining joinFloor)
    (later : request.index ≤ readingIndex) : Data.Gaussian.Norm.Basic.normSq (right.firstValue -
      left.lastValue) ≤ joining := by
  have gap := request.accurate left.last right.first later later
  rw [left.last_value, right.first_value] at gap
  exact gap.le

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank.EnergyEnds

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank

open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank (EnergyEnds)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank (Links)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections (JunctionRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins (LastJoin ClosingJoin)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests (LastRequest ClosingRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {index readingIndex energyDepth
    : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {target :
    Coordinate}

variable {joining : Coordinate} {joinFloor : Nat}

/-- The complete squared-norm gap bounds along an actual retained parent energy bank.

The dependent chain includes the gap from the supplied previous point and the final gap to the supplied finish point. -/
@[expose] def GapChain : {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
  UniformReciprocalCover.ParentCovers parents} →
    {prepared : ParentJoins.SideBank regular covers} → EnergyEndBank sample readingIndex energyDepth target
      prepared → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian → InverseRootPolynomial.Coordinate →
      Prop
  | _, _, _, .nil, previous, finish, error => Data.Gaussian.Norm.Basic.normSq (finish - previous) ≤ error
  | _, _, _, .cons head tail, previous, finish, error =>
      Data.Gaussian.Norm.Basic.normSq (head.firstValue - previous) ≤ error ∧
        GapChain tail
        head.lastValue finish error

/-- The original paid last-parent request controls the actual final gap back to the retained destination's first value.
-/
private theorem last_gap {count : Nat} {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data : UniformReciprocalModels.Data patch count}
    {cover : UniformReciprocalCover.Cover data} {destination : ParentComparison.Preparation regular cover}
    (first : EnergyEndBank.EnergyEnds sample readingIndex energyDepth target destination) :
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      UniformReciprocalCover.ParentCovers parents} → {prepared : ParentJoins.SideBank regular covers} →
    (ends : EnergyEndBank sample readingIndex energyDepth target prepared) → {joined : ClosingJoins.LastJoin
      destination prepared} →
    (request : ClosingRequests.LastRequest destination joining joinFloor prepared joined) → request.maximum ≤
      readingIndex → parents ≠ [] →
    (previous : InverseRootPolynomial.Gaussian) → Data.Gaussian.Norm.Basic.normSq (first.firstValue -
      ends.lastValue previous) ≤ joining
  | _, _, _, .nil, _, _, _, nonempty, _ => False.elim (nonempty rfl)
  | _, _, _, .cons head tail, _, request, later, _, previous => by
      cases tail with
      | nil =>
          have gap := JunctionRequests.Request.accurate request head.last first.first later later
          rw [head.last_value, first.first_value] at gap
          exact gap.le
      | cons next rest =>
        exact last_gap
          first (.cons next rest) request later (by intro same; cases same) head.lastValue

/-- The paid original junction requests extend supplied first and final bounds to the complete retained parent gap
chain. -/
private theorem internal_gaps
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
      UniformReciprocalCover.ParentCovers parents} {prepared : ParentJoins.SideBank regular covers}
    (ends : EnergyEndBank sample readingIndex energyDepth target prepared) {links : SideBank.Links prepared}
    (requests : SideConnections.JunctionRequests joining joinFloor prepared links) (later : requests.maximum ≤
      readingIndex)
    (previous finish : InverseRootPolynomial.Gaussian) (first : Data.Gaussian.Norm.Basic.normSq
      (ends.firstValue - previous) ≤ joining)
    (closing : Data.Gaussian.Norm.Basic.normSq (finish - ends.lastValue previous) ≤ joining) : ends.GapChain
      previous finish joining := by
  induction ends generalizing previous with
  | nil => exact closing
  | cons head tail ih =>
      change Data.Gaussian.Norm.Basic.normSq (head.firstValue - previous) ≤ joining ∧ tail.GapChain
        head.lastValue finish joining
      refine ⟨first, ?_⟩
      cases tail with
      | nil => exact closing
      | cons next rest =>
          cases links with
          | cons joined remaining =>
              exact ih requests.2 ((Data.Nat.Order.le_max_right _ _).trans later) head.lastValue
                (head.gap_bound next requests.1 ((Data.Nat.Order.le_max_left _ _).trans later)) closing

variable {parents : List (CenteredEdge curve differential)}
  {covers : ParentCovers parents}
  {prepared : SideBank regular covers}

/-- The original internal and closing requests bound every gap in the complete closed retained parent bank. -/
theorem closed_gaps (ends : EnergyEndBank sample readingIndex energyDepth target prepared) (nonnegative : 0 ≤
  joining)
    {links : SideBank.Links prepared} (requests : SideConnections.JunctionRequests joining joinFloor prepared links)
      (later : requests.maximum ≤ readingIndex)
    {joined : ClosingJoins.ClosingJoin prepared} (closing : ClosingRequests.ClosingRequest joining joinFloor prepared
      joined) (closingLater : closing.maximum ≤ readingIndex) :
    ends.GapChain ends.firstValue ends.firstValue joining := by
  have last : Data.Gaussian.Norm.Basic.normSq (ends.firstValue - ends.lastValue ends.firstValue) ≤ joining :=
    by
    cases ends with
    | nil =>
      simpa only [EnergyEndBank.firstValue, EnergyEndBank.lastValue, Data.Gaussian.Basic.sub_self,
        Data.Gaussian.Norm.Basic.normSq_zero] using nonnegative
    | cons head tail =>
      exact last_gap
        head (.cons head tail) closing closingLater (by intro same; cases same) head.firstValue
  exact internal_gaps ends requests
    later _ _ (by rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]; exact nonnegative) last

/-- A nonempty retained parent gap chain bounds its actual first primitive value from the supplied previous value. -/
theorem first_gap (ends : EnergyEndBank sample readingIndex energyDepth target prepared)
    (nonempty : parents ≠ []) {previous finish : InverseRootPolynomial.Gaussian} {error :
      InverseRootPolynomial.Coordinate}
    (gaps : ends.GapChain previous finish error) : Data.Gaussian.Norm.Basic.normSq (ends.firstValue - previous)
      ≤ error := by
  cases ends with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail => exact gaps.1

/-- Restricting a retained appended gap chain to its right bank preserves the actual left-bank last value as the new
previous point. -/
theorem append_gaps_tail {otherParents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {otherCovers : UniformReciprocalCover.ParentCovers otherParents} {other : ParentJoins.SideBank regular otherCovers}
    (left : EnergyEndBank sample readingIndex energyDepth target prepared)
    (right : EnergyEndBank sample readingIndex energyDepth target other)
    {previous finish : InverseRootPolynomial.Gaussian} {error : InverseRootPolynomial.Coordinate} (gaps : (left.append
      right).GapChain previous finish error) :
    right.GapChain (left.lastValue previous) finish error := by
  induction left generalizing previous with
  | nil => exact gaps
  | cons head tail ih => exact ih gaps.2

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples (ChartedEntry)
open Purelib.Integration.Path.IncrementArea (Summary)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Coordinate} {floor index
    depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    FacePrimitiveBank differential index domains}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison (CapRequest)

open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)

variable {energyTarget : Coordinate} {energyFloor energyDepth : Nat}

/-- Grouping uses nonempty original occurrences, so every next endpoint is an actual retained endpoint, including after
the last parent of a segment. -/
theorem segments_gaps (branch : HyperellipticReciprocal.originOrder curve = 1)
    (entries : List (ChartSamples.ChartedEntry (regular := regular) sample shared depth readingIndex localTarget
      localArea chartTarget floor))
    (energies : ChartedEntry.EnergyData energyTarget energyFloor energyDepth entries)
    (nonempty : ∀ entry ∈ entries, entry.entry.occurrence.compared.entered.cache.parents ≠ [])
    {previous finish : InverseRootPolynomial.Gaussian} {error : InverseRootPolynomial.Coordinate}
    (gaps : (energies.endBank branch entries).GapChain previous finish error) :
    Data.Gaussian.Norm.Basic.normSq (SegmentGapArea.first (energies.segments branch entries) finish - previous)
      ≤ error ∧
      SegmentGapArea.GapsSmall (energies.segments branch entries) finish error := by
  induction entries generalizing previous with
  | nil => exact ⟨gaps, True.intro⟩
  | cons head tail ih =>
      have present := nonempty head (List.mem_cons_self ..)
      have remaining := fun entry member => nonempty entry (List.mem_cons_of_mem head member)
      let left := energies.1.endBank branch
      let right := energies.2.endBank branch tail
      change (left.append right).GapChain previous finish error at gaps
      have first := (left.append right).first_gap
        (by
          intro empty
          cases shape : head.entry.occurrence.compared.entered.cache.parents with
          | nil => exact present shape
          | cons first rest => simp only [shape, List.cons_append] at empty; cases empty) gaps
      rw [left.append_firstValue right present] at first
      have later := left.append_gaps_tail right gaps
      rw [left.lastValue_independent present previous left.firstValue] at later
      exact ⟨first, ih energies.2 remaining later⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry.EnergyData

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation.EnergyRootRequest

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples (ChartedEntry)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples (ChartedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples.ChartedEntry (EnergyData)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {program : ExteriorProgram lifted
    differential} {prepared :
    ExteriorProgram.SurfacePreparation
    regular domains program}

variable {target : Coordinate} {floor : Nat}

variable {index depth readingIndex energyFloor energyDepth : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    FacePrimitiveBank differential index domains}
  {localTarget localArea chartTarget energyTarget : Coordinate}
    {sourceFloor : Nat}

/-- Transport along exact retained occurrence and spine equalities preserves the complete closed endpoint-gap
proposition. -/
theorem transportEnds_closedGaps {first last : List (ExteriorProgram.SurfaceOccurrence regular domains differential)}
  (same : first = last)
    {spine : SideBank.Retained regular (last.map (fun item => item.compared.entered.cache.parents)).flatten}
    (spineEq : spine = SurfaceOccurrence.capSpine last)
    (ends : Charts.Reciprocal.Disk.EnergyEndBank sample readingIndex energyDepth chartTarget (SurfaceOccurrence.capSpine
        first).bank)
      (error : InverseRootPolynomial.Coordinate) :
    (EnergyRootRequest.transportEnds same spineEq ends).GapChain (EnergyRootRequest.transportEnds same spineEq
      ends).firstValue
      (EnergyRootRequest.transportEnds same spineEq ends).firstValue error ↔ ends.GapChain ends.firstValue
        ends.firstValue error := by
  cases same
  cases spineEq
  rfl

/-- The paid original surface root request bounds every actual retained parent gap at the selected common reading stage.
-/
theorem retained_gaps (request : SurfacePreparation.EnergyRootRequest prepared target floor)
    (entries : List (ChartSamples.ChartedEntry (regular := regular) sample shared depth readingIndex localTarget
      localArea chartTarget sourceFloor))
    (energies : ChartedEntry.EnergyData energyTarget energyFloor energyDepth entries)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (occurrences : entries.map (fun entry => entry.entry.occurrence) = prepared.occurrences)
    (later : request.index ≤ readingIndex) :
    (energies.endBank branch entries).GapChain (energies.endBank branch entries).firstValue
      (energies.endBank branch entries).firstValue request.allowance := by
  have gaps := (request.endBank entries energies branch occurrences).closed_gaps request.positive.le
    request.junctions ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later))
    request.closing ((Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later))
  exact
    (transportEnds_closedGaps
    occurrences request.joined.spine_eq _ request.allowance).mp gaps

end SurfacePreparation.EnergyRootRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest
namespace RootEnergyAcquisition

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples (ChartedEntry)
open Purelib.Integration.Path.IncrementArea (Summary)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Coordinate} {floor index
    depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    FacePrimitiveBank differential index domains}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Request)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest
  (RootEnergyAcquisition)

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : Coordinate}
  {request : Request prepared target areaTarget floor} {charts : Request.ChartRequest request chartTarget}

variable {component :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
  regular domains differential} {joining energyTarget : Coordinate}
  {depthFloor energyFloor : Nat}

/-- The actual root-return requests discharge every segment gap. -/
theorem segment_gaps (acquired : ChartRequest.RootEnergyAcquisition charts component joining energyTarget depthFloor
  energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    SegmentGapArea.GapsSmall (acquired.energy.data.segments branch acquired.evaluated.samples.values)
      (SegmentGapArea.first (acquired.energy.data.segments branch acquired.evaluated.samples.values) 0)
        acquired.roots.allowance := by
  have gaps := acquired.roots.retained_gaps acquired.evaluated.samples.values acquired.energy.data branch
    acquired.occurrences_eq
    (acquired.readingIndex_eq ▸ Data.Nat.Order.le_max_right _ _)
  rw [acquired.energy.data.segments_first branch acquired.evaluated.samples.values acquired.energy.occurrences_nonempty]
    at gaps
  exact (acquired.energy.data.segments_gaps branch acquired.evaluated.samples.values
    acquired.energy.occurrences_nonempty gaps).2

/-- This finite bound pays the original segment count, independently of all target-dependent parent-child refinement
counts. -/
@[expose] def correctionBound (acquired : ChartRequest.RootEnergyAcquisition charts component joining energyTarget
  depthFloor energyFloor) : Coordinate :=
  2 * (16 * (request.count : InverseRootPolynomial.Coordinate) ^ 4 * acquired.roots.allowance *
    (2 * (2 * (request.slope + 1) + acquired.roots.allowance)) +
      (request.count : InverseRootPolynomial.Coordinate) ^ 2 * (4 * (2 * (request.slope + 1)) *
        acquired.roots.allowance))

/-- The acquired original segment gap requests bound the difference between the physical energy boundary and retained
endpoint residual. -/
theorem boundary_correction_bound (acquired : ChartRequest.RootEnergyAcquisition charts component joining energyTarget
  depthFloor energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq (acquired.energy.boundary - acquired.ends.residual) ≤
      acquired.correctionBound := by
  rw [acquired.ends_eq branch, acquired.roots.endBank_residual]
  have scalar := acquired.energy.boundary_residual_bound branch acquired.roots.positive.le (acquired.segment_gaps
    branch)
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

/-- The actual acquired physical energy boundary satisfies the computed original-parent-count and gap-correction bound.
-/
theorem boundary_bound (acquired : ChartRequest.RootEnergyAcquisition charts component joining energyTarget depthFloor
  energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq acquired.energy.boundary ≤ 2 *
      (2 * ((component.program.cache.parents.length : InverseRootPolynomial.Coordinate) *
        ((component.program.cache.parents.length : InverseRootPolynomial.Coordinate) * (80 * charts.localChart + 2 *
          acquired.roots.allowance)) +
          (80 * charts.localChart + 2 * acquired.roots.allowance)) + acquired.correctionBound) := by
  have estimate := (Data.Gaussian.Norm.Bounds.normSq_add_le_two acquired.ends.residual (acquired.energy.boundary -
    acquired.ends.residual)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct acquired.residual_bound (acquired.boundary_correction_bound branch))
        (by decide))
  rw [show acquired.ends.residual + (acquired.energy.boundary - acquired.ends.residual) = acquired.energy.boundary by
    ring1] at estimate
  exact estimate

/-- The physical comparison now has a computed boundary allowance. The original internal-area correction is retained
with its required sign. -/
theorem surface_energy_bound (acquired : ChartRequest.RootEnergyAcquisition charts component joining energyTarget
  depthFloor energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) :
    Data.Gaussian.Norm.Basic.normSq (acquired.energy.energy + (acquired.evaluated.original.surface.area +
      acquired.evaluated.original.internalArea)) <
      2 * (2 * (256 * (4 * chartTarget + target) + 2 * (areaTarget + chartTarget)) +
        2 * (2 * ((component.program.cache.parents.length : InverseRootPolynomial.Coordinate) *
          ((component.program.cache.parents.length : InverseRootPolynomial.Coordinate) * (80 * charts.localChart + 2 *
            acquired.roots.allowance)) +
            (80 * charts.localChart + 2 * acquired.roots.allowance)) + acquired.correctionBound)) := by
  have estimate := Data.Gaussian.Norm.Bounds.normSq_add_le_two
    (acquired.energy.energy - (-(acquired.evaluated.original.surface.area + acquired.evaluated.original.internalArea) +
      acquired.energy.boundary))
    acquired.energy.boundary
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    ((Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) (acquired.boundary_bound branch)).trans_lt
      (Fraction.Order.Arithmetic.add_lt_add_right_direct acquired.energy.surface_close _))
  have same : acquired.energy.energy - (-(acquired.evaluated.original.surface.area +
    acquired.evaluated.original.internalArea) + acquired.energy.boundary) +
      acquired.energy.boundary = acquired.energy.energy + (acquired.evaluated.original.surface.area +
        acquired.evaluated.original.internalArea) := by ring1
  rw [same] at estimate
  exact estimate.trans_lt paid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest.RootEnergyAcquisition
