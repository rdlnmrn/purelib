module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.AreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

@[expose] public section

/-! A single all-later budget for every regular occurrence in the original
ordered exterior compiler, with cached cut corrections and polygon reads. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A dependent bank of original regular-region requests in the exact retained occurrence order.

Every entry keeps its original face, cut words, common error allocation and supplied stage floor. -/
inductive RegularRegionRequests (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (error : Fraction.Rational) (floor : Nat) :
    List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices) → Type 3 where
  /-- The request bank for an empty original occurrence list. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error
    floor []
  /-- Prepend one original occurrence request to its retained dependent tail. -/ | cons {occurrence rest} (head :
    Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest occurrence fixed error floor)
      (tail : Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed
        error floor rest) :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error
        floor (occurrence :: rest)

constructive_injectivity RegularRegionRequests

namespace RegularRegionRequests

variable {fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {error :
  Fraction.Rational} {floor : Nat}
  {occurrences : List
    (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
    (faces := base.faces) grid.shrunk.included current.edges current.vertices)}

/-- Prepare one original regular-region request per retained occurrence without changing their order. -/
def build (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error
  : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    (occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)) →
      Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor occurrences
  | [] => .nil
  | occurrence :: rest => .cons (Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest.build occurrence
    fixed error positive floor)
      (Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build fixed
        error positive floor rest)

/-- The maximum sufficient stage of all retained requests, with the supplied floor for an empty bank. -/
def index : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor occurrences →
      Nat
  | _, .nil => floor
  | _, .cons head tail => max head.request.index tail.index

set_option genInjectivity false in
/-- The actual numerical receipts for the retained request bank on one shared reading bank and sewn surface. -/
inductive Samples {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) :
    {occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
      Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor occurrences
        → Type 3 where
  /-- The numerical receipts for an empty original request bank. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples readings
    surface .nil
  /-- Prepend the actual sample of the original head request to the retained tail samples. -/ | cons {occurrence rest}
    {head : Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest occurrence fixed error floor}
      {tail : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor
        rest}
      (first : head.Sample readings surface) (last :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
        readings surface tail) :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
        readings surface (.cons head tail)

constructive_injectivity Samples

namespace Samples

variable {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential
  stage domains} {readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
  current.mesh}
  {surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values}
    {requests : Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests
    fixed error floor occurrences}

/-- Cache each original region's numerical receipt using the same supplied readings and sewn surface. -/
def build (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
  (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values) :
    {occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
      (requests : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor
        occurrences) → Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
        readings surface requests
  | _, .nil => .nil
  | _, .cons head tail => .cons (Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest.Sample.build
    head readings surface)
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples.build
    readings surface tail)

/-- Sum the cached original selected region areas in retained occurrence order. -/
def areas : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor
      occurrences} → Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
      readings surface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.balance.selected.area + last.areas

/-- Sum every original retained cut correction in occurrence order. -/
def corrections : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor
      occurrences} → Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
      readings surface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.correction + last.corrections

/-- Sum the cached actual original occurrence polygons. -/
def polygons : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor
      occurrences} → Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
      readings surface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.polygon + last.polygons

/-- List the corrected original region residuals in retained occurrence order. -/
def residuals : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed error floor
      occurrences} → Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
      readings surface requests → List Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first last => first.residual :: last.residuals

/-- There is exactly one cached residual for each original occurrence. -/
theorem residuals_length (samples :
  Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples readings surface
  requests) : samples.residuals.length = occurrences.length := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- Every retained residual meets the common local bound above the bank's sufficient stage. -/
theorem residuals_small (samples :
  Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples readings surface
  requests) (later : requests.index ≤ stage) :
    ∀ residual ∈ samples.residuals, Data.Gaussian.Norm.Basic.normSq residual ≤ error := by
  induction samples with
  | nil => intro residual member; exact (List.not_mem_nil member).elim
  | cons first last ih =>
      intro residual member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact first.accurate ((Data.Nat.Order.le_max_left _ _).trans later)
      · exact ih ((Data.Nat.Order.le_max_right _ _).trans later) residual member

/-- The sum of cached residuals equals the selected areas minus all corrections and twice all retained polygons. -/
theorem residuals_sum (samples :
  Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples readings surface
  requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.residuals = samples.areas - samples.corrections - (samples.polygons
      + samples.polygons) := by
  induction samples with
  | nil => change 0 = 0 - 0 - (0 + 0); ring1
  | cons first last ih =>
      change first.residual + Data.Gaussian.Norm.Sum.Basic.gaussianSum last.residuals =
        (first.balance.selected.area + last.areas) - (first.correction + last.corrections) -
          ((first.polygon + last.polygons) + (first.polygon + last.polygons))
      rw [ih, Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest.Sample.residual,
        Hyperelliptic.Meshes.Newton.Regular.RegionSamples.RegularRegionRequest.Sample.corrected]
      ring1

/-- The cached region-area total equals any retained selections with the same original cell masks. -/
theorem areas_eq (samples : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
  readings surface requests)
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)) :
    samples.areas = Geometry.Grid.CellBoundary.sumValues (fun occurrence => (selected occurrence.cell).area) occurrences
      := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) (first.selected_area (selected _)) ih

/-- The cached polygon total is exactly the sum of the original occurrence word areas. -/
theorem polygons_eq (samples :
  Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples readings surface
  requests) :
    samples.polygons = Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Mesh.RetracingWords.wordArea
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh readings.values)
      occurrence.word) occurrences := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) first.polygon_eq ih

/-- Both factors of the actual original-region count are paid. This
retains every signed cut correction and the literal cached polygon words. -/
theorem aggregate_accurate {target : Fraction.Rational} (positive : 0 < target)
    {requests : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests fixed
      (Rational.Budget.Aggregate.perTerm target occurrences.length) floor occurrences}
    (samples : Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples readings
      surface requests) (later : requests.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (samples.areas - samples.corrections - (samples.polygons + samples.polygons)) <
      target := by
  rw [← samples.residuals_sum]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro residual member
  rw [samples.residuals_length]
  exact samples.residuals_small later residual member

end Samples
end RegularRegionRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.Ordered

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {originalLifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank originalLifted} {sheet : Fin
    2}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- Consume the exact whole-surface partition and all regular-region
requests together. Only the actual original branch-region areas and the
retained cut corrections remain for the global assembly. -/
theorem regular_regions_accurate (ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet) (newSheet
  : Fin 2)
    (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential) (error :
      Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let reference := fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop
    let compiled :=
      Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit
      grid.shrunk.included current.edges current.vertices
      reference (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
        ordered.prepared.partition newSheet
    let requests := Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.build fixed
      (Rational.Budget.Aggregate.perTerm error compiled.regulars.length)
      (Rational.Budget.Aggregate.perTerm_positive positive _) floor compiled.regulars
    ∀ stage (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains) (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      current.mesh)
      (surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
        requests.index ≤ stage →
      let samples := Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples.build
        readings surface requests
      ∀ selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
        Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection surface
        (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell),
      Data.Gaussian.Norm.Basic.normSq (surface.boundaryArea - Geometry.Grid.CellBoundary.sumValues (fun index =>
        (selected (base.bank.cell index)).area) ordered.prepared.labels -
        samples.corrections - (samples.polygons + samples.polygons)) < error := by
  intro reference compiled requests stage shared readings surface later samples selected
  have partition := RootContinuation.NewtonOriginalRegionPartition.Ordered.original_regions_area_partition ordered
    newSheet surface selected
  have areaEq := samples.areas_eq selected
  have total : surface.boundaryArea - Geometry.Grid.CellBoundary.sumValues (fun index => (selected (base.bank.cell
    index)).area) ordered.prepared.labels =
      samples.areas := by
    rw [← partition, ← areaEq, add_sub_cancel_right]
  exact (congrArg (fun area => Data.Gaussian.Norm.Basic.normSq (area - samples.corrections - (samples.polygons +
    samples.polygons))) total).trans_lt
    (samples.aggregate_accurate positive later)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.Ordered

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.RegionAggregate.NewtonGrid.RegularRegionRequests.Samples
