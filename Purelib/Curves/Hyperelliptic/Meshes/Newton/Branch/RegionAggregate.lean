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

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Polynomial.Geometry.Grid

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

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A dependent bank of original annular branch-region requests in retained excision order.

Each entry keeps its original hole, selected arriving sheet, magnitude bank, local error and stage floor. -/
inductive BranchRegionRequests (bank :
  PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (sheet :
  Data.Index branches → Fin 2)
    (fixed : PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (floor : Nat) :
    List (AllHoles.Excision.AnnularEntry grid current) → Type 3 where
  /-- The request bank for an empty original annular entry list. -/ | nil :
    BranchRegionRequests bank sheet fixed error floor
    []
  /-- Prepend one original annular branch request to its retained dependent tail. -/ | cons {entry rest} (head :
    RegionSamples.BranchRegionRequest bank entry (sheet entry.hole.index) fixed error
    floor)
      (tail : BranchRegionRequests bank sheet fixed
        error floor rest) :
      BranchRegionRequests bank sheet fixed error
        floor (entry :: rest)

constructive_injectivity BranchRegionRequests

namespace BranchRegionRequests

variable {sheet : Data.Index branches → Fin 2}
  {fixed : PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {error :
    Fraction.Rational} {floor : Nat}
  {entries : List (AllHoles.Excision.AnnularEntry grid current)}

/-- Prepare each retained original annular branch request with its supplied branch sheet and local allowance. -/
@[expose] def build (bank : PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted) (sheet : Data.Index branches → Fin 2)
    (fixed : PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    (entries : List (AllHoles.Excision.AnnularEntry grid current)) →
      BranchRegionRequests bank sheet fixed error floor entries
  | [] => .nil
  | entry :: rest => .cons (RegionSamples.BranchRegionRequest.build bank entry (sheet
    entry.hole.index) fixed error positive floor)
      (BranchRegionRequests.build bank sheet fixed
        error positive floor rest)

/-- The maximum sufficient stage of all retained requests, including the supplied empty-bank floor. -/
@[expose] def index : {entries : List (AllHoles.Excision.AnnularEntry grid current)} →
  BranchRegionRequests bank sheet fixed error floor entries → Nat
  | _, .nil => floor
  | _, .cons head tail => max head.index tail.index

set_option genInjectivity false in
/-- The actual original branch-region receipts on one shared numerical bank and sewn surface. -/
inductive Samples {stage : Nat} {shared : PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  differential stage domains}
    (readings : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) :
    {entries : List (AllHoles.Excision.AnnularEntry grid current)} →
      BranchRegionRequests bank sheet fixed error floor entries →
      Type 3 where
  /-- The numerical receipts for an empty original branch request bank. -/ | nil :
    Samples readings surface .nil
  /-- Prepend the original head sample to the retained dependent tail samples. -/ | cons {entry rest} {head :
    RegionSamples.BranchRegionRequest bank entry (sheet entry.hole.index) fixed error
    floor}
      {tail : BranchRegionRequests bank sheet fixed error floor rest}
      (first : head.Sample readings surface) (last :
        Samples readings surface
        tail) : Samples readings
        surface (.cons head tail)

constructive_injectivity Samples

namespace Samples

variable {stage : Nat} {shared : PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential
  stage domains} {readings : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
  current.mesh}
  {surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values}
    {requests : BranchRegionRequests bank sheet fixed
    error floor entries}

/-- Cache every original branch-region sample using the same supplied readings and sewn surface. -/
@[expose] def build (readings : PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
  current.mesh) (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
  readings.values) :
    {entries : List (AllHoles.Excision.AnnularEntry grid current)} → (requests :
      BranchRegionRequests bank sheet fixed error floor entries) →
      Samples readings surface requests
  | _, .nil => .nil
  | _, .cons head tail => .cons (RegionSamples.BranchRegionRequest.Sample.build head
    readings surface)
    (Samples.build readings
    surface tail)

/-- Sum the actual cached original selected branch-region areas. -/
@[expose] def areas : {entries : List (AllHoles.Excision.AnnularEntry grid current)} →
  {requests : BranchRegionRequests bank sheet fixed error floor
  entries} →
    Samples readings surface requests →
      Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.balance.selected.area + last.areas

/-- Sum every retained original branch-region correction. -/
@[expose] def corrections : {entries : List (AllHoles.Excision.AnnularEntry grid current)} →
  {requests : BranchRegionRequests bank sheet fixed error floor
  entries} →
    Samples readings surface requests →
      Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.correction + last.corrections

/-- Sum the cached original branch-excursion polygons. -/
@[expose] def polygons : {entries : List (AllHoles.Excision.AnnularEntry grid current)} →
  {requests : BranchRegionRequests bank sheet fixed error floor
  entries} →
    Samples readings surface requests →
      Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.polygon + last.polygons

/-- List all corrected original branch-region residuals in retained excision order. -/
@[expose] def residuals : {entries : List (AllHoles.Excision.AnnularEntry grid current)} →
  {requests : BranchRegionRequests bank sheet fixed error floor
  entries} →
    Samples readings surface requests → List
      Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first last => first.residual :: last.residuals

/-- There is one cached residual for each retained original annular entry. -/
theorem residuals_length (samples : Samples
  readings surface requests) : samples.residuals.length = entries.length := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- Every original branch residual meets the common local bound at every sufficient shared stage. -/
theorem residuals_small (samples : Samples
  readings surface requests) (later : requests.index ≤ stage) :
    ∀ residual ∈ samples.residuals, Gaussian.Norm.Basic.normSq residual ≤ error := by
  induction samples with
  | nil => intro residual member; exact (List.not_mem_nil member).elim
  | cons first last ih =>
      intro residual member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact first.accurate ((Nat.Order.le_max_left _ _).trans later)
      · exact ih ((Nat.Order.le_max_right _ _).trans later) residual member

/-- The residual sum is exactly the selected area total minus all corrections and twice the cached polygon total. -/
theorem residuals_sum (samples : Samples
  readings surface requests) :
    Gaussian.Norm.Sum.Basic.gaussianSum samples.residuals = samples.areas - samples.corrections - (samples.polygons
      + samples.polygons) := by
  induction samples with
  | nil => change 0 = 0 - 0 - (0 + 0); ring1
  | cons first last ih =>
      change first.residual + Gaussian.Norm.Sum.Basic.gaussianSum last.residuals =
        (first.balance.selected.area + last.areas) - (first.correction + last.corrections) -
          ((first.polygon + last.polygons) + (first.polygon + last.polygons))
      rw [ih, RegionSamples.BranchRegionRequest.Sample.residual]
      ring1

/-- The cached area total equals any original retained selections with the same branch-cell masks. -/
theorem areas_eq (samples : Samples readings
  surface requests)
    (selected : (cell : ClearGrid.Cell curve.polynomial (Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)) :
    samples.areas = CellBoundary.sumValues (fun entry => (selected (base.bank.cell
      entry.hole.index)).area) entries := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) (first.selected_area (selected _)) ih

/-- The cached polygon total uses the exact original resplit reference walks and retained arriving sheets. -/
theorem polygons_eq (samples : Samples readings
  surface requests) :
    samples.polygons = CellBoundary.sumValues (fun entry => Topology.Mesh.RetracingWords.wordArea
      (PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      (current.edges.indexedEdges current.vertices
        (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk
          (PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
        (sheet entry.hole.index))) entries := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) first.polygon_eq ih

/-- The original branch-region residual total meets the whole target when the local allowance pays both actual
entry-count factors. -/
theorem aggregate_accurate {target : Fraction.Rational} (positive : 0 < target)
    {requests : BranchRegionRequests bank sheet fixed
      (Rational.Budget.Aggregate.perTerm target entries.length) floor entries}
    (samples : Samples readings surface
      requests) (later : requests.index ≤ stage) :
    Gaussian.Norm.Basic.normSq (samples.areas - samples.corrections - (samples.polygons + samples.polygons)) <
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
      (∃ entry ∈ entries, key entry = index) → CellBoundary.sumValues (fun entry => if key entry = index
        then value else 0) entries = value
  | [], _, found => by obtain ⟨_, member, _⟩ := found; cases member
  | head :: tail, unique, found => by
      by_cases same : key head = index
      · rw [CellBoundary.sumValues, if_pos same]
        have zero : CellBoundary.sumValues (fun entry => if key entry = index then value else 0) tail = 0
          := by
          rw [CellBoundary.sumValues_congr _ (fun _ => 0) tail (by
            intro entry member
            have different : key entry ≠ index := fun equal =>
              (List.pairwise_cons.mp unique).1 entry member (same.trans equal.symm)
            rw [if_neg different]), CellBoundary.sumValues_zero]
        rw [zero, add_zero]
      · rw [CellBoundary.sumValues, if_neg same, zero_add]
        apply Ordered.sum_unique key index value tail
          (List.pairwise_cons.mp unique).2
        obtain ⟨entry, member, equal⟩ := found
        rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact (same equal).elim
        · exact ⟨entry, member, equal⟩

/-- Reindex the existing excision payloads, not newly located branch roots. -/
theorem branch_entries_sum {sheet : Fin 2} (ordered :
  PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet)
    (excision : AllHoles.Excision.AllHoleExcision grid current) (value :
      Data.Index branches → Gaussian.Basic.Canonical) :
    CellBoundary.sumValues value ordered.prepared.labels = CellBoundary.sumValues (fun entry
      => value entry.hole.index) excision.entries := by
  have unique : excision.entries.Pairwise (fun first last => first.hole.index ≠ last.hole.index) := by
    have holes := grid.faces.holes_pairwise
    rw [← excision.holes_eq] at holes
    exact (List.Pairwise.pairwise_map (function := AllHoles.Excision.AnnularEntry.hole)
      (relation := fun first last => first.index ≠ last.index)).mp holes
  have complete (index : Data.Index branches) : ∃ entry ∈ excision.entries,
    entry.hole.index = index := by
    obtain ⟨hole, member, equal⟩ := grid.faces.hole_complete index
    rw [← excision.holes_eq] at member
    obtain ⟨entry, belongs, same⟩ := Data.List.Map.mem_map.mp member
    exact ⟨entry, belongs, (congrArg (fun hole => hole.index) same).trans equal⟩
  have expand (index : Data.Index branches) : value index =
      CellBoundary.sumValues (fun entry => if entry.hole.index = index then value index else 0)
        excision.entries :=
    (Ordered.sum_unique (fun entry => entry.hole.index) index _
      excision.entries unique (complete index)).symm
  rw [CellBoundary.sumValues_congr _ _ ordered.prepared.labels (fun index _ => expand index),
    CellBoundary.sumValues_swap]
  apply CellBoundary.sumValues_congr
  intro entry _
  have scalar : CellBoundary.sumValues (fun index => if entry.hole.index = index then value index else 0)
    ordered.prepared.labels =
      CellBoundary.sumValues (fun index => if index = entry.hole.index then value entry.hole.index else 0)
        ordered.prepared.labels := by
    apply CellBoundary.sumValues_congr
    intro index _
    by_cases same : index = entry.hole.index
    · cases same; rw [if_pos rfl]
    · rw [if_neg same, if_neg (Ne.symm same)]
  exact scalar.trans (Ordered.sum_unique (fun index => index)
    entry.hole.index _ ordered.prepared.labels ordered.prepared.unique
    ⟨entry.hole.index, ordered.complete entry.hole.index, rfl⟩)

end Ordered
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
