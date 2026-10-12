module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularSamples
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
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.ConjugateRegion
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

/-! All original regular regions share one conjugate pair and retain
their cached polygons and corrections in the finite aggregate estimate. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation base.bank.toBranchCellBank}
    {target radius : Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {current :
    Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames grid.faces.regulars}
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}

namespace PairedRegularRequests

variable {leftFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains leftDifferential}
  {rightFixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains rightDifferential}
  {error : Fraction.Rational} {floor : Nat}
  {occurrences : List
    (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
    (faces := base.faces) grid.shrunk.included current.edges current.vertices)}
set_option genInjectivity false in
/-- The original regular-region sample bank on one retained pair of sewn conjugate surfaces.

Every receipt keeps its original occurrence, cached conjugate polygon and complete cut correction. -/
inductive ConjugateSamples {stage : Nat} {leftBank :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank leftDifferential stage domains} {rightBank :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank rightDifferential stage domains}
    (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh)
      (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank
      current.mesh) (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
      leftReadings.values) (rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
      current.cutPolygon.patch rightReadings.values)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface) :
    {occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
      Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor
        occurrences → Type 3 where
  /-- The conjugate receipts for an empty original regular request bank. -/ | nil :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
    leftReadings rightReadings leftSurface rightSurface pair .nil
  /-- Prepend the actual original head conjugate sample to its retained tail. -/ | cons {occurrence rest} {head :
    Hyperelliptic.Meshes.Newton.PairedRegularSamples.PairedRegularRequest occurrence leftFixed rightFixed error floor}
      {tail : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor
        rest}
      (first : Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.PairedRegularRequest.ConjugateSample head
        leftReadings rightReadings leftSurface rightSurface pair) (last :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
        leftReadings rightReadings leftSurface rightSurface pair tail) :
        Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
        leftReadings rightReadings leftSurface rightSurface pair (.cons head tail)

constructive_injectivity ConjugateSamples

namespace ConjugateSamples

variable {stage : Nat} {leftBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  leftDifferential stage domains} {rightBank : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
  rightDifferential stage domains} {leftReadings :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh} {rightReadings :
  Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh}
  {leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch leftReadings.values}
    {rightSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch
    rightReadings.values}
  {pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface} {requests :
    Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error floor
    occurrences}

/-- Cache every original regular-region conjugate receipt using the same supplied readings and sewn pair. -/
@[expose] def build (leftReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  leftBank current.mesh) (rightReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  rightBank current.mesh) (leftSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample
  current.cutPolygon.patch leftReadings.values) (rightSurface :
  Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch rightReadings.values)
    (pair : Topology.Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface) :
    {occurrences : List
      (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
      (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
      (requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
        floor occurrences) →
        Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples leftReadings
        rightReadings leftSurface rightSurface pair requests
  | _, .nil => .nil
  | _, .cons head tail => .cons
    (Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.PairedRegularRequest.ConjugateSample.build head leftReadings
    rightReadings leftSurface rightSurface pair)
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples.build
    leftReadings rightReadings leftSurface rightSurface pair tail)

/-- Sum the cached actual conjugate selected region areas. -/
@[expose] def areas : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
      floor occurrences} → Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
      leftReadings rightReadings leftSurface rightSurface pair requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.cut.area + last.areas

/-- Sum all original retained conjugate cut corrections. -/
@[expose] def corrections : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
      floor occurrences} → Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
      leftReadings rightReadings leftSurface rightSurface pair requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.cut.correction + last.corrections

/-- Sum the cached original conjugate occurrence polygons. -/
@[expose] def polygons : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
      floor occurrences} → Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
      leftReadings rightReadings leftSurface rightSurface pair requests → Gaussian.Basic.Canonical
  | _, _, .nil => 0
  | _, _, .cons first last => first.polygon + last.polygons

/-- List the corrected original conjugate residuals in retained occurrence order. -/
@[expose] def residuals : {occurrences : List
  (Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.ResplitRegularOccurrence
  (faces := base.faces) grid.shrunk.included current.edges current.vertices)} →
    {requests : Hyperelliptic.Meshes.Newton.PairedRegularAggregate.PairedRegularRequests leftFixed rightFixed error
      floor occurrences} → Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
      leftReadings rightReadings leftSurface rightSurface pair requests → List Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first last => first.residual :: last.residuals

/-- There is exactly one conjugate residual for every original occurrence. -/
theorem residuals_length (samples :
  Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples leftReadings
  rightReadings leftSurface rightSurface pair requests) : samples.residuals.length = occurrences.length := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- Each original conjugate residual meets the local target at every sufficient shared stage. -/
theorem residuals_small (samples :
  Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples leftReadings
  rightReadings leftSurface rightSurface pair requests) (later : requests.index ≤ stage) :
    ∀ residual ∈ samples.residuals, Data.Gaussian.Norm.Basic.normSq residual ≤ error := by
  induction samples with
  | nil => intro residual member; exact (List.not_mem_nil member).elim
  | cons first last ih =>
      intro residual member
      rcases List.Membership.mem_cons.mp member with rfl | member
      · exact first.accurate ((Nat.Order.le_max_left _ _).trans later)
      · exact ih ((Nat.Order.le_max_right _ _).trans later) residual member

/-- The retained residual sum equals the conjugate area total minus every correction and twice the polygon total. -/
theorem residuals_sum (samples :
  Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples leftReadings
  rightReadings leftSurface rightSurface pair requests) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum samples.residuals = samples.areas - samples.corrections - (samples.polygons
      + samples.polygons) := by
  induction samples with
  | nil => change 0 = 0 - 0 - (0 + 0); ring1
  | cons first last ih =>
      change first.residual + Data.Gaussian.Norm.Sum.Basic.gaussianSum last.residuals =
        (first.cut.area + last.areas) - (first.cut.correction + last.corrections) -
          ((first.polygon + last.polygons) + (first.polygon + last.polygons))
      rw [ih, Hyperelliptic.Meshes.Newton.ConjugateRegularSamples.PairedRegularRequest.ConjugateSample.residual]
      ring1

/-- The cached conjugate area total equals any retained selections with the same original cell masks and actual
conjugate primitive values. -/
theorem areas_eq (samples : Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples
  leftReadings rightReadings leftSurface rightSurface pair requests)
    (selected : (cell : Geometry.Grid.ClearGrid.Cell curve.polynomial (Hyperelliptic.Branches.Cuts.Ambient curve)) →
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection leftSurface
      (RootContinuation.NewtonOriginalRegionPartition.NewtonGrid.originalCellMask current cell)) :
    samples.areas = Geometry.Grid.CellBoundary.sumValues (fun occurrence => Topology.Polygon.Stokes.edgeListArea
      pair.values ((selected occurrence.cell).triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary))
      occurrences := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg₂ (· + ·) (first.selected_area (selected _)) ih

/-- The cached conjugate polygon total uses the original occurrence words and the supplied left-conjugated and right
edge readings. -/
theorem polygons_eq (samples :
  Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples leftReadings
  rightReadings leftSurface rightSurface pair requests) :
    samples.polygons = Geometry.Grid.CellBoundary.sumValues (fun occurrence => Path.PairedIncrementArea.area
      (occurrence.word.map (fun edge =>
      (⟨Data.Gaussian.Basic.conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation current.mesh
        leftReadings.values edge),
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
    (samples : Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests.ConjugateSamples leftReadings
      rightReadings leftSurface rightSurface pair requests) (later : requests.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (samples.areas - samples.corrections - (samples.polygons + samples.polygons)) <
      target := by
  rw [← samples.residuals_sum]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro residual member
  rw [samples.residuals_length]
  exact samples.residuals_small later residual member

end ConjugateSamples
end PairedRegularRequests
end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate
