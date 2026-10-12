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

public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.PairedRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Riemann.RootContinuation.NewtonOriginalRegionPartition
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Integration.Surface.Sewn.Selection.Paired
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.RegionAggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

public section

/-! All original branch regions, budgeted on the same cache as the regular
regions. Reindexing uses actual branch completeness and uniqueness. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
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
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- The dependent bank of requests for the original paired branch annuli.

Each entry keeps its branch sheet, both original magnitude banks, the common local target and the supplied stage floor.
-/
inductive PairedBranchRequests (bank :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (sheet :
  Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2)
    (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
      (error : Fraction.Rational) (floor : Nat) :
    List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current) → Type 3 where
  /-- The paired branch requests for an empty original annulus list. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed
    rightFixed error floor []
  /-- Prepend the actual head annulus request to its original tail. -/ | cons {entry rest} (head :
    Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry (sheet entry.hole.index) leftFixed
    rightFixed error floor)
      (tail : Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed
        rightFixed error floor rest) :
      Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed
        rightFixed error floor (entry :: rest)

constructive_injectivity PairedBranchRequests

namespace PairedBranchRequests

variable {sheet : Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2}
  {leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
    {rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
    {error : Fraction.Rational} {floor : Nat}
  {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)}

/-- Prepare both original branch readings at each retained annulus with the common target and floor. -/
@[expose] def build (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted) (sheet : Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2)
    (leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential)
      (rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential)
      (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    (entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)) →
      Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor
      entries
  | [] => .nil
  | entry :: rest => .cons (Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest.build bank entry (sheet
    entry.hole.index) leftFixed rightFixed error positive floor)
      (Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.build bank sheet leftFixed
        rightFixed error positive floor rest)

/-- The maximum sufficient stage for all retained paired branch requests, including the empty-bank floor. -/
@[expose] def index : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor
  entries → Nat
  | _, .nil => floor
  | _, .cons head tail => max head.index tail.index

/-- The retained paired branch threshold is at least its supplied floor. -/
theorem floor_le (requests : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed
  rightFixed error floor entries) : floor ≤ requests.index := by
  cases requests with
  | nil => exact Nat.le_refl _
  | cons head tail => exact head.floor_le.trans (Data.Nat.Order.le_max_left _ _)

set_option genInjectivity false in
/-- The paired branch receipts at one shared stage and on the supplied two sewn surfaces.

The dependent bank preserves each original annulus, actual cut correction and cached original paired polygon. -/
inductive Samples {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  leftDifferential stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  rightDifferential stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh) (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values) :
    {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
      Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor
      entries → Type 3 where
  /-- The receipts for an empty original branch request bank. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings
    rightReadings leftSurface rightSurface .nil
  /-- Prepend the actual head paired annulus sample to its retained tail. -/ | cons {entry rest} {head :
    Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest bank entry (sheet entry.hole.index) leftFixed
    rightFixed error floor}
      {tail : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed
        error floor rest}
      (first : head.Sample leftReadings rightReadings leftSurface rightSurface) (last :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings
        rightReadings leftSurface rightSurface tail) :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings
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
    Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed
    rightFixed error floor entries}

/-- Cache all original paired branch receipts using the supplied common readings and sewn surfaces. -/
@[expose] def build (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  leftBank current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  rightBank current.mesh) (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
  current.cutPolygon.patch leftReadings.values) (rightSurface :
  Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightReadings.values) :
    {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} → (requests :
      Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor
      entries) →
      Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings rightReadings
        leftSurface rightSurface requests
  | _, .nil => .nil
  | _, .cons head tail => .cons (Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest.Sample.build head
    leftReadings rightReadings leftSurface rightSurface)
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples.build leftReadings
    rightReadings leftSurface rightSurface tail)

/-- Sum the cached actual paired branch region areas. -/
@[expose] def areas : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  {requests : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed
  error floor entries} →
    Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings rightReadings
      leftSurface rightSurface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.cut.area + last.areas

/-- Sum the complete retained cut corrections for the original paired branch regions. -/
@[expose] def corrections : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  {requests : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed
  error floor entries} →
    Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings rightReadings
      leftSurface rightSurface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.cut.correction + last.corrections

/-- Sum the cached original paired branch reference polygons. -/
@[expose] def polygons : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  {requests : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed
  error floor entries} →
    Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings rightReadings
      leftSurface rightSurface requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.polygon + last.polygons

/-- List the corrected paired branch residuals in original annulus order. -/
@[expose] def residuals : {entries : List (Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current)} →
  {requests : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed
  error floor entries} →
    Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings rightReadings
      leftSurface rightSurface requests → List Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first last => first.residual :: last.residuals

/-- There is exactly one paired residual for each original annulus. -/
theorem residuals_length (samples : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests) : samples.residuals.length = entries.length := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- Every cached original paired branch residual meets the common local target at every sufficient stage. -/
theorem residuals_small (samples : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests) (later : requests.index ≤ stage) :
    ∀ residual ∈ samples.residuals, Data.Gaussian.Norm.Basic.normSq residual ≤ error := by
  induction samples with
  | nil => intro residual member; exact (List.not_mem_nil member).elim
  | cons first last ih =>
      intro residual member
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · exact first.accurate ((Data.Nat.Order.le_max_left _ _).trans later)
      · exact ih ((Data.Nat.Order.le_max_right _ _).trans later) residual member

/-- The residual sum equals the retained branch area total minus all cut corrections and twice the polygon total. -/
theorem residuals_sum (samples : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.residuals = samples.areas - samples.corrections - (samples.polygons
      + samples.polygons) := by
  induction samples with
  | nil => change 0 = 0 - 0 - (0 + 0); ring1
  | cons first last ih =>
      change first.residual + Data.Gaussian.Norm.Sum.Basic.gaussianSum last.residuals =
        (first.cut.area + last.areas) - (first.cut.correction + last.corrections) -
          ((first.polygon + last.polygons) + (first.polygon + last.polygons))
      rw [ih, Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest.Sample.residual]
      ring1

/-- The cached branch area total agrees with retained selections having the same original cell masks and primitive
values. -/
theorem areas_eq (samples : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings
  rightReadings leftSurface rightSurface requests)
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)) :
    samples.areas = Geometry.Grid.CellBoundary.sumValues (fun entry => Topology.Polygon.Stokes.edgeListArea
      (Hyperelliptic.Meshes.Newton.Regular.PairedRegion.pairedValues leftSurface rightSurface) ((selected
      (base.bank.cell entry.hole.index)).triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary)) entries
      := by
  induction samples with
  | nil => rfl
  | cons first last ih =>
      apply congrArg₂ (· + ·) ?_ ih
      exact first.cut.area_eq.trans ((Surface.Sewn.Selection.Paired.paired_area_readback first.balance.selected _).trans
        (Surface.Sewn.Selection.Paired.paired_area_readback (selected _) _).symm)

/-- The cached paired polygon total is computed from the original resplit words with their supplied incoming branch
sheets. -/
theorem polygons_eq (samples : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples
  leftReadings rightReadings leftSurface rightSurface requests) :
    samples.polygons = Geometry.Grid.CellBoundary.sumValues (fun entry => Path.PairedIncrementArea.area
      ((current.edges.indexedEdges current.vertices
        (grid.shrunk.included.resplit (bank.rows.get entry.hole.index).reference.walk
          (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
        (sheet entry.hole.index)).map (fun edge =>
          (⟨edgeValuation current.mesh leftReadings.values edge,
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh rightReadings.values edge⟩
              : Topology.Polygon.Stokes.PrimitivePoint)))) entries := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) first.polygon_eq ih

/-- The actual annulus count pays the complete paired branch residual bound.

The local per-term allocation is summed over the retained original annuli, preserving all cut corrections and paired
polygon terms. -/
theorem aggregate_accurate {target : Fraction.Rational} (positive : 0 < target)
    {requests : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed
      (Rational.Budget.Aggregate.perTerm target entries.length) floor entries}
    (samples : Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests.Samples leftReadings rightReadings
      leftSurface rightSurface requests) (later : requests.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (samples.areas - samples.corrections - (samples.polygons + samples.polygons)) <
      target := by
  rw [← samples.residuals_sum]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro residual member
  rw [samples.residuals_length]
  exact samples.residuals_small later residual member

end Samples
end PairedBranchRequests

end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
