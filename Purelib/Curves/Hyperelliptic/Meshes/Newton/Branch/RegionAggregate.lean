module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

public section

/-! All original branch regions, budgeted on the same cache as the regular
regions. Reindexing uses actual branch completeness and uniqueness. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A dependent bank of original annular branch-region requests in retained excision order.

Each entry keeps its original hole, selected arriving sheet, magnitude bank, local error and stage floor. -/
inductive BranchRegionRequests (bank :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (sheet :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (floor : Nat) :
    List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current) → Type 3 where
  /-- The request bank for an empty original annular entry list. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor
    []
  /-- Prepend one original annular branch request to its retained dependent tail. -/ | cons {entry rest} (head :
    Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest bank entry (sheet entry.hole.index) fixed error
    floor)
      (tail : Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed
        error floor rest) :
      Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error
        floor (entry :: rest)

constructive_injectivity BranchRegionRequests

namespace BranchRegionRequests

variable {sheet : Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2}
  {fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {error :
    Fraction.Rational} {floor : Nat}
  {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)}

/-- Prepare each retained original annular branch request with its supplied branch sheet and local allowance. -/
@[expose] def build (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted) (sheet : Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    (entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)) →
      Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor entries
  | [] => .nil
  | entry :: rest => .cons (Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest.build bank entry (sheet
    entry.hole.index) fixed error positive floor)
      (Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.build bank sheet fixed
        error positive floor rest)

/-- The maximum sufficient stage of all retained requests, including the supplied empty-bank floor. -/
@[expose] def index : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor entries → Nat
  | _, .nil => floor
  | _, .cons head tail => max head.index tail.index

set_option genInjectivity false in
/-- The actual original branch-region receipts on one shared numerical bank and sewn surface. -/
inductive Samples {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) :
    {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
      Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor entries →
      Type 3 where
  /-- The numerical receipts for an empty original branch request bank. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface .nil
  /-- Prepend the original head sample to the retained dependent tail samples. -/ | cons {entry rest} {head :
    Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest bank entry (sheet entry.hole.index) fixed error
    floor}
      {tail : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor rest}
      (first : head.Sample readings surface) (last :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface
        tail) : Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings
        surface (.cons head tail)

constructive_injectivity Samples

namespace Samples

variable {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential
  stage domains} {readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
  current.mesh}
  {surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values}
    {requests : Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed
    error floor entries}

/-- Cache every original branch-region sample using the same supplied readings and sewn surface. -/
@[expose] def build (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
  current.mesh) (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
  readings.values) :
    {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} → (requests :
      Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor entries) →
      Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface requests
  | _, .nil => .nil
  | _, .cons head tail => .cons (Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest.Sample.build head
    readings surface)
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples.build readings
    surface tail)

/-- Sum the actual cached original selected branch-region areas. -/
@[expose] def areas : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  {requests : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor
  entries} →
    Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface requests →
      Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.balance.selected.area + last.areas

/-- Sum every retained original branch-region correction. -/
@[expose] def corrections : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  {requests : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor
  entries} →
    Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface requests →
      Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.correction + last.corrections

/-- Sum the cached original branch-excursion polygons. -/
@[expose] def polygons : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  {requests : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor
  entries} →
    Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface requests →
      Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.polygon + last.polygons

/-- List all corrected original branch-region residuals in retained excision order. -/
@[expose] def residuals : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  {requests : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed error floor
  entries} →
    Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface requests → List
      Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first last => first.residual :: last.residuals

/-- There is one cached residual for each retained original annular entry. -/
theorem residuals_length (samples : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples
  readings surface requests) : samples.residuals.length = entries.length := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- Every original branch residual meets the common local bound at every sufficient shared stage. -/
theorem residuals_small (samples : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples
  readings surface requests) (later : requests.index ≤ stage) :
    ∀ residual ∈ samples.residuals, Data.Gaussian.Norm.Basic.normSq residual ≤ error := by
  induction samples with
  | nil => intro residual member; exact (List.not_mem_nil member).elim
  | cons first last ih =>
      intro residual member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact first.accurate ((Data.Nat.Order.le_max_left _ _).trans later)
      · exact ih ((Data.Nat.Order.le_max_right _ _).trans later) residual member

/-- The residual sum is exactly the selected area total minus all corrections and twice the cached polygon total. -/
theorem residuals_sum (samples : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples
  readings surface requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.residuals = samples.areas - samples.corrections - (samples.polygons
      + samples.polygons) := by
  induction samples with
  | nil => change 0 = 0 - 0 - (0 + 0); ring1
  | cons first last ih =>
      change first.residual + Data.Gaussian.Norm.Sum.Basic.gaussianSum last.residuals =
        (first.balance.selected.area + last.areas) - (first.correction + last.corrections) -
          ((first.polygon + last.polygons) + (first.polygon + last.polygons))
      rw [ih, Hyperelliptic.Meshes.Newton.Branch.RegionSamples.BranchRegionRequest.Sample.residual]
      ring1

/-- The cached area total equals any original retained selections with the same branch-cell masks. -/
theorem areas_eq (samples : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings
  surface requests)
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)) :
    samples.areas = Geometry.Grid.CellBoundary.sumValues (fun entry => (selected (base.bank.cell
      entry.hole.index)).area) entries := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) (first.selected_area (selected _)) ih

/-- The cached polygon total uses the exact original resplit reference walks and retained arriving sheets. -/
theorem polygons_eq (samples : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings
  surface requests) :
    samples.polygons = Geometry.Grid.CellBoundary.sumValues (fun entry => Topology.Mesh.RetracingWords.wordArea
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      (current.edges.indexedEdges current.vertices
        (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
        (sheet entry.hole.index))) entries := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) first.polygon_eq ih

/-- The original branch-region residual total meets the whole target when the local allowance pays both actual
entry-count factors. -/
theorem aggregate_accurate {target : Fraction.Rational} (positive : 0 < target)
    {requests : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests bank sheet fixed
      (Rational.Budget.Aggregate.perTerm target entries.length) floor entries}
    (samples : Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.BranchRegionRequests.Samples readings surface
      requests) (later : requests.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (samples.areas - samples.corrections - (samples.polygons + samples.polygons)) <
      target := by
  rw [← samples.residuals_sum]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro residual member
  rw [samples.residuals_length]
  exact samples.residuals_small later residual member

end Samples
end BranchRegionRequests

namespace Ordered

/-- A finite indicator sum over distinct original keys selects the supplied value when its requested key occurs. -/
private theorem sum_unique {Item : Type} {count : Nat} (key : Item → Fin count) (index : Fin count) (value :
  Gaussian.Basic.Canonical) :
    ∀ (entries : List Item), entries.Pairwise (fun first second => key first ≠ key second) →
      (∃ entry ∈ entries, key entry = index) → Geometry.Grid.CellBoundary.sumValues (fun entry => if key entry = index
        then value else 0) entries = value
  | [], _, found => by obtain ⟨_, member, _⟩ := found; cases member
  | head :: tail, unique, found => by
      by_cases same : key head = index
      · rw [Geometry.Grid.CellBoundary.sumValues, if_pos same]
        have zero : Geometry.Grid.CellBoundary.sumValues (fun entry => if key entry = index then value else 0) tail = 0
          := by
          rw [Geometry.Grid.CellBoundary.sumValues_congr _ (fun _ => 0) tail (by
            intro entry member
            have different : key entry ≠ index := fun equal =>
              (List.pairwise_cons.mp unique).1 entry member (same.trans equal.symm)
            rw [if_neg different]), Geometry.Grid.CellBoundary.sumValues_zero]
        rw [zero, add_zero]
      · rw [Geometry.Grid.CellBoundary.sumValues, if_neg same, zero_add]
        apply Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.Ordered.sum_unique key index value tail
          (List.pairwise_cons.mp unique).2
        obtain ⟨entry, member, equal⟩ := found
        rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact (same equal).elim
        · exact ⟨entry, member, equal⟩

/-- Reindex the existing excision payloads, not newly located branch roots. -/
theorem branch_entries_sum {sheet : Fin 2} (ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet)
    (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current) (value :
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Gaussian.Basic.Canonical) :
    Geometry.Grid.CellBoundary.sumValues value ordered.prepared.labels = Geometry.Grid.CellBoundary.sumValues (fun entry
      => value entry.hole.index) excision.entries := by
  have unique : excision.entries.Pairwise (fun first last => first.hole.index ≠ last.hole.index) := by
    have holes := grid.faces.holes_pairwise
    rw [← excision.holes_eq] at holes
    exact (Data.List.Pairwise.pairwise_map (function := Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.hole)
      (relation := fun first last => first.index ≠ last.index)).mp holes
  have complete (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) : ∃ entry ∈ excision.entries,
    entry.hole.index = index := by
    obtain ⟨hole, member, equal⟩ := grid.faces.hole_complete index
    rw [← excision.holes_eq] at member
    obtain ⟨entry, belongs, same⟩ := Data.List.Map.mem_map.mp member
    exact ⟨entry, belongs, (congrArg (fun hole => hole.index) same).trans equal⟩
  have expand (index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches) : value index =
      Geometry.Grid.CellBoundary.sumValues (fun entry => if entry.hole.index = index then value index else 0)
        excision.entries :=
    (Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.Ordered.sum_unique (fun entry => entry.hole.index) index _
      excision.entries unique (complete index)).symm
  rw [Geometry.Grid.CellBoundary.sumValues_congr _ _ ordered.prepared.labels (fun index _ => expand index),
    Geometry.Grid.CellBoundary.sumValues_swap]
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro entry _
  have scalar : Geometry.Grid.CellBoundary.sumValues (fun index => if entry.hole.index = index then value index else 0)
    ordered.prepared.labels =
      Geometry.Grid.CellBoundary.sumValues (fun index => if index = entry.hole.index then value entry.hole.index else 0)
        ordered.prepared.labels := by
    apply Geometry.Grid.CellBoundary.sumValues_congr
    intro index _
    by_cases same : index = entry.hole.index
    · cases same; rw [if_pos rfl]
    · rw [if_neg same, if_neg (Ne.symm same)]
  exact scalar.trans (Hyperelliptic.Meshes.Newton.Branch.RegionAggregate.Ordered.sum_unique (fun index => index)
    entry.hole.index _ ordered.prepared.labels ordered.prepared.unique
    ⟨entry.hole.index, ordered.complete entry.hole.index, rfl⟩)

end Ordered
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
