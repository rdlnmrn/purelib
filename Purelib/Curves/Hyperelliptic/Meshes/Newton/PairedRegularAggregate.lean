module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

public section

/-! A single all-later budget for every regular occurrence in the original
ordered exterior compiler, with cached cut corrections and polygon reads. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- A dependent request bank for the exact original regular-occurrence list and both retained differential magnitude
banks. -/
inductive PairedRegularRequests (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains leftDifferential) (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains rightDifferential) (error : Fraction.Rational) (floor : Nat) :
    List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices) → Type 3 where
  /-- The paired request bank for an empty original occurrence list. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
    floor []
  /-- Prepend one original paired regular-region request to its retained tail. -/ | cons {occurrence rest} (head :
    Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence leftFixed rightFixed error floor)
      (tail : Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed
        rightFixed error floor rest) :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed
        error floor (occurrence :: rest)

constructive_injectivity PairedRegularRequests

namespace PairedRegularRequests

variable {leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
  {rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
  {error : Fraction.Rational} {floor : Nat}
  {occurrences : List
    (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
    (faces := base.faces) grid.shrunk.included current.edges current.vertices)}

/-- Prepare each original occurrence's paired region request at the same local target and supplied floor. -/
@[expose] def build (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  leftDifferential) (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  rightDifferential) (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    (occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)) →
      Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor
        occurrences
  | [] => .nil
  | occurrence :: rest => .cons (Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest.build occurrence
    leftFixed rightFixed error positive floor)
      (Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.build leftFixed
        rightFixed error positive floor rest)

/-- The maximum sufficient stage of the original paired requests, retaining the empty-bank floor. -/
@[expose] def index : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor
      occurrences → Nat
  | _, .nil => floor
  | _, .cons head tail => max head.request.index tail.index

/-- The common sufficient stage respects the original supplied floor. -/
theorem floor_le (requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed
  rightFixed error floor occurrences) : floor ≤ requests.index := by
  cases requests with
  | nil => exact Nat.le_refl _
  | cons head tail => exact head.request.floor_le.trans (Nat.Order.le_max_left _ _)

set_option genInjectivity false in
/-- The actual original paired region samples on the supplied shared reading banks and sewn surfaces. -/
inductive Samples {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  leftDifferential stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  rightDifferential stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh) (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values) :
    {occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
      Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor
        occurrences → Type 3 where
  /-- The paired samples for an empty original request bank. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
    rightReadings leftSurface rightSurface .nil
  /-- Prepend the actual original head sample to the retained dependent tail. -/ | cons {occurrence rest} {head :
    Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence leftFixed rightFixed error floor}
      {tail : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor
        rest}
      (first : head.Sample leftReadings rightReadings leftSurface rightSurface) (last :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
        rightReadings leftSurface rightSurface tail) :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
        rightReadings leftSurface rightSurface (.cons head tail)

constructive_injectivity Samples

namespace Samples

variable {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  leftDifferential stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  rightDifferential stage domains} {leftReadings :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh} {rightReadings :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh}
  {leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values}
    {rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
    rightReadings.values} {requests :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
    floor occurrences}

/-- Cache all original paired-region receipts using the same supplied readings and sewn surfaces. -/
@[expose] def build (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  leftBank current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  rightBank current.mesh) (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
  current.cutPolygon.patch leftReadings.values) (rightSurface :
  Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightReadings.values) :
    {occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
      (requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
        floor occurrences) → Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples
        leftReadings rightReadings leftSurface rightSurface requests
  | _, .nil => .nil
  | _, .cons head tail => .cons (Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest.Sample.build head
    leftReadings rightReadings leftSurface rightSurface)
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples.build leftReadings
    rightReadings leftSurface rightSurface tail)

/-- Sum the actual cached paired selected region areas. -/
@[expose] def areas : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
      floor occurrences} → Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
      rightReadings leftSurface rightSurface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.cut.area + last.areas

/-- Sum every original paired cut correction in retained occurrence order. -/
@[expose] def corrections : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
      floor occurrences} → Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
      rightReadings leftSurface rightSurface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.cut.correction + last.corrections

/-- Sum the cached actual original paired occurrence polygons. -/
@[expose] def polygons : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
      floor occurrences} → Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
      rightReadings leftSurface rightSurface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.polygon + last.polygons

/-- List all corrected original paired-region residuals. -/
@[expose] def residuals : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
      floor occurrences} → Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
      rightReadings leftSurface rightSurface requests → List Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first last => first.residual :: last.residuals

/-- There is one retained paired residual for each original occurrence. -/
theorem residuals_length (samples : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests) : samples.residuals.length = occurrences.length := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- Every original paired residual meets the local bound above the common sufficient stage. -/
theorem residuals_small (samples : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests) (later : requests.index ≤ stage) :
    ∀ residual ∈ samples.residuals, Data.Gaussian.Norm.Basic.normSq residual ≤ error := by
  induction samples with
  | nil => intro residual member; exact (List.not_mem_nil member).elim
  | cons first last ih =>
      intro residual member
      rcases List.Membership.mem_cons.mp member with rfl | member
      · exact first.accurate ((Nat.Order.le_max_left _ _).trans later)
      · exact ih ((Nat.Order.le_max_right _ _).trans later) residual member

/-- The retained residual sum equals the paired area total minus every correction and twice the polygon total. -/
theorem residuals_sum (samples : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.residuals = samples.areas - samples.corrections - (samples.polygons
      + samples.polygons) := by
  induction samples with
  | nil => change 0 = 0 - 0 - (0 + 0); ring1
  | cons first last ih =>
      change first.residual + Data.Gaussian.Norm.Sum.Basic.gaussianSum last.residuals =
        (first.cut.area + last.areas) - (first.cut.correction + last.corrections) -
          ((first.polygon + last.polygons) + (first.polygon + last.polygons))
      rw [ih, Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest.Sample.residual]
      ring1

/-- The cached paired area total equals any retained selections with the same original cell masks and actual paired
primitive values. -/
theorem areas_eq (samples : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests)
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)) :
    samples.areas = Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Polygon.Stokes.edgeListArea
      (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface rightSurface) ((selected
      occurrence.cell).triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary)) occurrences := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) (first.selected_area (selected _)) ih

/-- The cached paired polygon total is exactly the sum over the original occurrence words and both supplied edge
readings. -/
theorem polygons_eq (samples : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests) :
    samples.polygons = Geometry.Grid.CellBoundary.sumValues (fun occurrence => Path.PairedIncrementArea.area
      (occurrence.word.map (fun edge =>
      (⟨edgeValuation current.mesh leftReadings.values edge,
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint)))) occurrences := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) first.polygon_eq ih

/-- Both factors of the actual original-region count are paid. This
retains every signed cut correction and the literal cached polygon words. -/
theorem aggregate_accurate {target : Fraction.Rational} (positive : 0 < target)
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed
      (Rational.Budget.Aggregate.perTerm target occurrences.length) floor occurrences}
    (samples : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests.Samples leftReadings
      rightReadings leftSurface rightSurface requests) (later : requests.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (samples.areas - samples.corrections - (samples.polygons + samples.polygons)) <
      target := by
  rw [← samples.residuals_sum]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro residual member
  rw [samples.residuals_length]
  exact samples.residuals_small later residual member

end Samples
end PairedRegularRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
