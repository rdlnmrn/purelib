module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedWalk
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWalkAreaRequests
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchFaceClassification
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.StemAggregate
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueStemRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleAggregate
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleGeometry

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Domains MagnitudeBank PrimitiveBank
  TriangleCache Source Sources Nonloop)

/-!
# Value-parameterized physical-hole requests

`HoleAreaRequest`, `HoleRowRequest`, `HoleRequestBank` and
`HoleAggregateRequest` compare each corrected single lap with the actual
physical hole boundary for one differential. A mixed value has no
differential, but every one of those statements is a word-area identity once
the chart and area comparisons are the mixed ones. This module replays the
hole layer on a mixed value.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueHoleRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole HoleLocation)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_direct
  mul_le_mul_of_nonneg_left_direct add_le_add_direct)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}
  {domains : Domains owner}

/-- Canonical readings of the original physical source word equal the sum of its actual retained primitive increments.
-/
private theorem physical_word_value
    (sources : Sources owner)
    (physical : ∀ source ∈ sources, source.project owner.lifted.mesh.triangulation.faces ∈
      owner.lifted.boundaryLoops.flatten)
    (values : Fin owner.lifted.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh values)
        (sources.map (fun source => source.project owner.lifted.mesh.triangulation.faces)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.map (fun source => source.increment values)) := by
  induction sources with
  | nil => rfl
  | cons source sources inductionHypothesis =>
      change Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh values
        (source.project owner.lifted.mesh.triangulation.faces) + _ =
        source.increment values + _
      exact congrArg₂ (fun first last : Gaussian.Basic.Canonical => first + last)
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary.canonical_physical_source source (physical source
          List.mem_cons_self) values)
        (inductionHypothesis (fun next member => physical next (List.mem_cons_of_mem _ member)))

/-- The mixed two-sheet hole request bounds the physical hole boundary word. -/
theorem value_canonical_hole_accurate (hole : BranchHole owner.base.bank.toBranchCellBank)
    (retained : hole ∈ owner.base.faces.holes)
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {coefficient :
      Gaussian.Basic.Canonical} {target : Fraction.Rational}
    (request : Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedWalk.ValuePairedWalkRequest (owner := owner)
      leftDifferential rightDifferential domains coefficient hole.inwardBoundary target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage) :
    normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient))
      (hole.liftedBoundary owner.lifted.vertices owner.lifted.edges)) < target := by
  have physical : ∀ source ∈ request.left.sources,
      source.project owner.lifted.mesh.triangulation.faces ∈ owner.lifted.boundaryLoops.flatten := by
    intro source member
    apply Topology.Surface.Sewing.SimpleBoundaryCycles.mem_flatten.mpr
    refine ⟨_, Data.List.Membership.mem_append.mpr (Or.inr (Data.List.Map.mem_map_of_mem retained)), ?_⟩
    rw [← Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation.cancellation_sources_project hole request.left]
    exact Data.List.Map.mem_map_of_mem member
  have equal := (congrArg (Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
    (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)))
    (Hyperelliptic.Meshes.PuncturedGrid.BranchHoleCancellation.cancellation_sources_project hole
      request.left)).symm.trans
    (physical_word_value request.left.sources physical _)
  exact (congrArg normSq equal).trans_lt (request.accurate leftReadings rightReadings later)

set_option genInjectivity false in
/-- The mixed single-lap area request. -/
structure ValueHoleAreaRequest {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential
  genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Gaussian.Basic.Canonical)
    (hole : BranchHole owner.base.bank.toBranchCellBank) (target : Fraction.Rational) where
  /-- The whole mixed hole-area target is positive. -/ positive : 0 < target
  /-- The cached original lap magnitude for the mixed value. -/ magnitude : Fraction.Rational
  /-- The magnitude retains the squared original edge count and both original magnitude banks through their actual
    mixing coefficient. -/ magnitude_eq : magnitude = (hole.inwardBoundary.edgeCount : Fraction.Rational) ^ 2 *
    (4 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient)
  /-- The paid mixed total-increment allowance. -/ totalTarget : Fraction.Rational
  /-- The total allowance pays one quarter of the area target against four times the retained lap magnitude. -/
    totalTarget_eq : totalTarget = Rational.Budget.Weighted.allowance (target / 4) (4 * magnitude)
  /-- The actual original paired inward hole walk. -/ paired :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk owner.lifted.mesh hole.inwardBoundary
  /-- The mixed paired-area request on that same retained walk. -/ areas :
    Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWalkAreaRequests.ValueAreaRequest (owner := owner) leftFixed
    rightFixed coefficient paired (target / 4)
  /-- The mixed total-increment request on the original inward boundary. -/ total :
    Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedWalk.ValuePairedWalkRequest (owner := owner)
    leftDifferential rightDifferential domains coefficient hole.inwardBoundary totalTarget
  /-- The common sufficient stage of the retained area and total requests. -/ index : Nat
  /-- The common stage is exactly the maximum of the original area and total stages. -/ index_eq : index = max
    areas.index total.index

constructive_injectivity ValueHoleAreaRequest

namespace ValueHoleAreaRequest

variable {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {coefficient :
  Gaussian.Basic.Canonical}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential}
  {hole : BranchHole owner.base.bank.toBranchCellBank} {target : Fraction.Rational}

/-- Prepare the original mixed hole area and total-increment requests with one retained lap magnitude and paid target.
-/
@[expose] def build (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Gaussian.Basic.Canonical)
    (hole : BranchHole owner.base.bank.toBranchCellBank) (target : Fraction.Rational) (positive : 0 < target) :
    ValueHoleAreaRequest (owner := owner) leftFixed rightFixed coefficient hole target :=
  let magnitude := (hole.inwardBoundary.edgeCount : Fraction.Rational) ^ 2 *
    (4 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient)
  let totalTarget := Rational.Budget.Weighted.allowance (target / 4) (4 * magnitude)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  have magnitudeNonnegative : 0 ≤ magnitude :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (EdgeMagnitude.mixBound_nonnegative leftFixed.nonnegative rightFixed.nonnegative coefficient))
  let paired := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.build owner.lifted.mesh
    hole.inwardBoundary
  let areas := Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWalkAreaRequests.ValueAreaRequest.build (owner := owner)
    leftFixed rightFixed coefficient
    paired (target / 4) quarterPositive
  let total := Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedWalk.ValuePairedWalkRequest.build (owner := owner)
    leftDifferential rightDifferential
    domains coefficient hole.inwardBoundary totalTarget
    (Rational.Budget.Weighted.allowance_positive quarterPositive
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitudeNonnegative))
  ⟨positive, magnitude, rfl, totalTarget, rfl, paired, areas, total, max areas.index total.index, rfl⟩

open Purelib.Integration in
/-- Twice either actual mixed inward lap area differs from the full physical hole area by at most the paid target.

The retained total request pays the original cross ribbon, using both original magnitude banks and the actual mixing
coefficient. -/
theorem lap_accurate (request : ValueHoleAreaRequest (owner := owner) leftFixed rightFixed coefficient hole target)
    (retained : hole ∈ owner.base.faces.holes)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage)
      (sheet : Fin 2) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    let lap := owner.lifted.edges.indexedEdges owner.lifted.vertices hole.inwardBoundary sheet
    normSq (Topology.Mesh.RetracingWords.wordArea value lap + Topology.Mesh.RetracingWords.wordArea value lap -
      Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary owner.lifted.vertices owner.lifted.edges)) ≤
        target := by
  intro value lap
  have areaLater := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have totalLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have leftFixedLater : leftFixed.index ≤ stage :=
    (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.areas.index_eq ▸ areaLater))
  have rightFixedLater : rightFixed.index ≤ stage :=
    (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.areas.index_eq ▸
      areaLater))
  let leftMagnitude := EdgeMagnitude.ofBank (owner := owner) leftFixed leftFixedLater leftReadings
  let rightMagnitude := EdgeMagnitude.ofBank (owner := owner) rightFixed rightFixedLater rightReadings
  let mixedMagnitude := EdgeMagnitude.mix (owner := owner) leftMagnitude rightMagnitude coefficient
  have magnitudeBound : mixedMagnitude.bound =
      EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient := rfl
  have areaError := request.areas.accurate leftReadings rightReadings areaLater 0 1 (by decide)
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords.hole_lap_values hole retained request.paired,
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords.hole_lap_values hole retained request.paired] at areaError
  have total := (value_canonical_hole_accurate hole retained request.total leftReadings rightReadings totalLater).le
  rw [hole.liftedBoundary_eq, Topology.Surface.Sewing.SewingRetraction.wordValue_append] at total
  let zero := owner.lifted.edges.indexedEdges owner.lifted.vertices hole.inwardBoundary 0
  let one := owner.lifted.edges.indexedEdges owner.lifted.vertices hole.inwardBoundary 1
  have magnitudeRaw : Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value
    zero) ≤
      (hole.inwardBoundary.edgeCount : Fraction.Rational) ^ 2 * (4 * mixedMagnitude.bound) := by
    rw [← Topology.Mesh.RetracingWords.sum_map_eq_wordValue]
    apply Path.IncrementArea.sum_bound_of_length (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      mixedMagnitude.nonnegative) ?_ ?_
    · intro entry member
      obtain ⟨edge, inWord, equal⟩ := Data.List.Map.mem_map.mp member
      rw [← equal]
      change edge ∈ owner.lifted.edges.indexedEdges owner.lifted.vertices hole.inwardBoundary 0 at inWord
      change Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation
        owner.lifted.mesh
        (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient) edge) ≤
        4 * mixedMagnitude.bound
      have supported := Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedWalk_supported
        owner.lifted.mesh hole.inwardBoundary 0 edge inWord
      rw [← Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value owner.lifted.mesh edge supported]
      exact mixedMagnitude.source_bounded (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute
        owner.lifted.mesh edge supported).sourceEdge
    · rw [Data.List.Map.length_map, owner.lifted.edges.indexedEdges_length]
  have magnitude : Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue value zero) ≤
    request.magnitude := by
    rw [request.magnitude_eq]
    exact magnitudeRaw
  have oldBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : normSq point ≤ limit) : Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have canonicalBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) : normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have cross : normSq (Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value zero)
    (Topology.Surface.Sewing.SewingRetraction.wordValue value one)) ≤ target / 4 := by
    rw [show Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value zero)
      (Topology.Surface.Sewing.SewingRetraction.wordValue value one) =
      Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value zero)
        (Topology.Surface.Sewing.SewingRetraction.wordValue value zero +
        Topology.Surface.Sewing.SewingRetraction.wordValue value one) by
        rw [Path.IncrementArea.area_add_right, Path.IncrementArea.area_self, _root_.zero_add]]
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    have nonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸
      Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (EdgeMagnitude.mixBound_nonnegative leftFixed.nonnegative rightFixed.nonnegative coefficient))
    have product := Fraction.Order.Arithmetic.mul_le_mul_direct magnitude (oldBound total)
      (Gaussian.Norm.Basic.normSq_nonneg _) nonnegative
    have estimate := (Path.BoundaryRibbon.area_bound (Topology.Surface.Sewing.SewingRetraction.wordValue value zero)
      (Topology.Surface.Sewing.SewingRetraction.wordValue value zero +
      Topology.Surface.Sewing.SewingRetraction.wordValue value one)).trans
      ((_root_.mul_assoc _ _ _).le.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)))
    apply estimate.trans
    rw [show 4 * (request.magnitude * request.totalTarget) = (4 * request.magnitude) * request.totalTarget by ring1,
      request.totalTarget_eq]
    exact Rational.Budget.Weighted.mul_allowance_le
      (Fraction.Order.Field.div_nonneg_direct request.positive.le (by decide))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative)
  have finish (first second : Gaussian.Basic.Canonical) (bound : Data.Gaussian.Norm.Basic.normSq first ≤ target / 4)
    (other : Data.Gaussian.Norm.Basic.normSq second ≤ target / 4) :
      normSq (first - second) ≤ target :=
    canonicalBound (((Gaussian.Norm.Bounds.normSq_sub_le_two first second).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct bound
      other) (by decide))).trans_eq
      ((by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  have cases : sheet = 0 ∨ sheet = 1 := by
    have bound := sheet.isLt
    by_cases zero : sheet.val = 0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (by change sheet.val = 1; omega))
  rw [hole.liftedBoundary_eq, Topology.Mesh.RetracingWords.wordArea_append]
  rcases cases with rfl | rfl
  · have equal (a b c : Gaussian.Basic.Canonical) : a + a - (a + b + c) = (a - b) - c := by ring1
    exact (congrArg normSq (equal (Topology.Mesh.RetracingWords.wordArea value zero)
      (Topology.Mesh.RetracingWords.wordArea value one) _)).trans_le
      (finish _ _ (oldBound areaError) (oldBound cross))
  · have reversed : Data.Gaussian.Norm.Basic.normSq (Topology.Mesh.RetracingWords.wordArea value one -
      Topology.Mesh.RetracingWords.wordArea value zero) ≤ target / 4 := by
      rw [show Topology.Mesh.RetracingWords.wordArea value one - Topology.Mesh.RetracingWords.wordArea value zero =
        -(Topology.Mesh.RetracingWords.wordArea value zero - Topology.Mesh.RetracingWords.wordArea value one) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
      exact oldBound areaError
    have equal (a b c : Gaussian.Basic.Canonical) : b + b - (a + b + c) = (b - a) - c := by ring1
    exact (congrArg normSq (equal (Topology.Mesh.RetracingWords.wordArea value zero)
      (Topology.Mesh.RetracingWords.wordArea value one) _)).trans_le
      (finish _ _ reversed (oldBound cross))

open Purelib.RootIsolation in
/-- The mixed single lap contributes minus one half of the physical hole
boundary, up to the requested error. -/
theorem corrected_accurate (request : ValueHoleAreaRequest (owner := owner) leftFixed rightFixed coefficient hole
  target)
    (retained : hole ∈ owner.base.faces.holes) (bank :
      Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted) (sheet : Fin
      2)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    normSq (bank.holeArea value hole.index sheet + bank.holeArea value hole.index sheet +
      Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary owner.lifted.vertices owner.lifted.edges)) ≤
        target := by
  intro value
  rw [bank.holeArea_reverse hole sheet _ (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse
    owner.lifted.mesh _)]
  have bound := request.lap_accurate retained leftReadings rightReadings later
    (Hyperelliptic.Branches.BranchCutLifts.otherSheet (SquareRoot.Grid.EdgeBank.RootEdgeBank.target owner.lifted.edges
      (bank.rows.get hole.index).stem sheet))
  rw [show ∀ a b : Gaussian.Basic.Canonical, -a + -a + b = -(a + a - b) by intros; ring1,
    Gaussian.Basic.Canonical.normSq_neg]
  exact bound

end ValueHoleAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueHoleRequests

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueHoleRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Topology.Polygon.Stokes

open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole HoleLocation)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct add_le_add_direct)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted}
  {domains : Domains owner}

set_option genInjectivity false in
/-- One mixed hole request per actual retained branch. -/
structure ValueHoleRowRequest {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential
  genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Gaussian.Basic.Canonical)
    (target : Fraction.Rational) (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches) where
  /-- The actual original physical-hole location for the retained branch label. -/ location : HoleLocation
    owner.base.faces.holes (owner.base.bank.cell branch)
  /-- The retained physical hole has the requested branch label. -/ branch_eq : location.hole.index = branch
  /-- The mixed area request on that exact original physical hole. -/ request : ValueHoleAreaRequest (owner := owner)
    leftFixed rightFixed coefficient location.hole target

constructive_injectivity ValueHoleRowRequest

namespace ValueHoleRowRequest

variable {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {coefficient :
  Gaussian.Basic.Canonical}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential} {target : Fraction.Rational}
  {branch : Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches}

/-- Locate the original branch hole and prepare its mixed area request without changing its retained owner. -/
@[expose] def build (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Gaussian.Basic.Canonical)
    (target : Fraction.Rational) (positive : 0 < target) (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index
      owner.branches) :
    ValueHoleRowRequest (owner := owner) leftFixed rightFixed coefficient target branch :=
  match owner.base.faces.locateCell (owner.base.bank.cell branch) (owner.base.bank.cell_mem branch) with
  | .regular found => (found.face.unassigned branch found.cell_eq).elim
  | .hole found => ⟨found, Hyperelliptic.Branches.BranchFaceClassification.FaceKind.branch_unique found.hole.cell_eq
    found.cell_eq,
      ValueHoleAreaRequest.build (owner := owner) leftFixed rightFixed coefficient found.hole target positive⟩

/-- The selected physical hole belongs to the original complete hole list. -/
theorem retained (row : ValueHoleRowRequest (owner := owner) leftFixed rightFixed coefficient target branch) :
    row.location.hole ∈ owner.base.faces.holes :=
  row.location.indexed ▸ List.getElem_mem row.location.index.isLt

/-- Original holes with equal branch labels have the same lifted physical boundary. -/
private theorem boundary_eq {first last : BranchHole owner.base.bank.toBranchCellBank} (same : first.index = last.index)
  :
    first.liftedBoundary owner.lifted.vertices owner.lifted.edges = last.liftedBoundary owner.lifted.vertices
      owner.lifted.edges := by
  rcases first with ⟨index, cell, member, cellEq, state, boxEq⟩
  rcases last with ⟨other, otherCell, otherMember, otherEq, otherState, otherBoxEq⟩
  change index = other at same
  cases same
  cases cellEq
  cases otherEq
  rfl

/-- The selected hole boundary equals that of any original hole with the same branch label. -/
theorem boundary_readback (row : ValueHoleRowRequest (owner := owner) leftFixed rightFixed coefficient target branch)
    (hole : BranchHole owner.base.bank.toBranchCellBank) (same : hole.index = branch) :
    row.location.hole.liftedBoundary owner.lifted.vertices owner.lifted.edges = hole.liftedBoundary
      owner.lifted.vertices owner.lifted.edges :=
  boundary_eq (row.branch_eq.trans same.symm)

/-- Twice the original corrected mixed hole area plus its actual physical boundary area meets the requested target at
every sufficient stage. -/
theorem accurate (row : ValueHoleRowRequest (owner := owner) leftFixed rightFixed coefficient target branch)
    (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted) (sheet
      : Fin 2)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : row.request.index ≤ stage)
      :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    normSq (bank.holeArea value branch sheet + bank.holeArea value branch sheet +
      Topology.Mesh.RetracingWords.wordArea value (row.location.hole.liftedBoundary owner.lifted.vertices
        owner.lifted.edges)) ≤ target := by
  intro value
  have bound := row.request.corrected_accurate row.retained bank sheet leftReadings rightReadings later
  dsimp only at bound ⊢
  rw [row.branch_eq] at bound
  change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bound

end ValueHoleRowRequest

set_option genInjectivity false in
/-- One mixed request per retained branch, cached before sampling. -/
structure ValueHoleRequestBank {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential
  genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Gaussian.Basic.Canonical) (target :
      Fraction.Rational) where
  /-- The dependent mixed request bank indexed by original branch labels. -/ rows : Data.Vector.DependentVector (fun
    branch : Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches =>
    ValueHoleRowRequest (owner := owner) leftFixed rightFixed coefficient target branch)
  /-- The cached common sufficient stage. -/ index : Nat
  /-- The stage is exactly the maximum of the retained row request stages. -/ index_eq : index = rows.maximum (fun _ row
    => row.request.index)

constructive_injectivity ValueHoleRequestBank

namespace ValueHoleRequestBank

variable {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {coefficient :
  Gaussian.Basic.Canonical}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential} {target : Fraction.Rational}

/-- Prepare one mixed request per original branch hole and cache their common sufficient stage. -/
@[expose] def build (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Gaussian.Basic.Canonical)
    (target : Fraction.Rational) (positive : 0 < target) :
    ValueHoleRequestBank (owner := owner) leftFixed rightFixed coefficient target :=
  let rows := Data.Vector.DependentVector.ofFn (ValueHoleRowRequest.build (owner := owner) leftFixed rightFixed
    coefficient target positive)
  ⟨rows, rows.maximum (fun _ row => row.request.index), rfl⟩

/-- Every original row request is ready by the common bank stage. -/
theorem index_ge (requests : ValueHoleRequestBank (owner := owner) leftFixed rightFixed coefficient target)
    (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches) :
    (requests.rows.get branch).request.index ≤ requests.index := by
  rw [requests.index_eq]
  exact requests.rows.get_le_maximum (fun _ row => row.request.index) branch

/-- Read the original physical boundary area of the retained hole for a branch label. -/
@[expose] def physicalArea (requests : ValueHoleRequestBank (owner := owner) leftFixed rightFixed coefficient target)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches) : Gaussian :=
  Topology.Mesh.RetracingWords.wordArea value ((requests.rows.get branch).location.hole.liftedBoundary
    owner.lifted.vertices owner.lifted.edges)

/-- A finite indicator sum over distinct retained keys returns the supplied value when the requested key occurs. -/
private theorem sum_unique {Alpha : Type} {count : Nat} (key : Alpha → Fin count) (index : Fin count) (value :
  Gaussian.Basic.Canonical) :
    ∀ (entries : List Alpha), entries.Pairwise (fun first second => key first ≠ key second) →
      (∃ entry ∈ entries, key entry = index) →
      Geometry.Grid.CellBoundary.sumValues (fun entry => if key entry = index then value else 0) entries = value
  | [], _, found => by obtain ⟨_, member, _⟩ := found; cases member
  | head :: tail, unique, found => by
      by_cases same : key head = index
      · rw [Geometry.Grid.CellBoundary.sumValues, if_pos same]
        have tailZero : Geometry.Grid.CellBoundary.sumValues (fun entry => if key entry = index then value else 0) tail
          = 0 := by
          rw [Geometry.Grid.CellBoundary.sumValues_congr _ (fun _ => 0) tail (by
            intro entry member
            have different : key entry ≠ index := fun equal =>
              (List.pairwise_cons.mp unique).1 entry member (same.trans equal.symm)
            rw [if_neg different]), Geometry.Grid.CellBoundary.sumValues_zero]
        rw [tailZero, Gaussian.Basic.add_zero]
      · rw [Geometry.Grid.CellBoundary.sumValues, if_neg same, zero_add]
        apply sum_unique key index value tail (List.pairwise_cons.mp unique).2
        obtain ⟨entry, member, equal⟩ := found
        rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact (same equal).elim
        · exact ⟨entry, member, equal⟩

/-- The original ordered branch-label sum equals the complete physical-hole area sum by retained completeness and
uniqueness. -/
theorem physical_sum (requests : ValueHoleRequestBank (owner := owner) leftFixed rightFixed coefficient target)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical)
    {bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet
      : Fin 2} (ordered :
      Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet) :
    Geometry.Grid.CellBoundary.sumValues (requests.physicalArea value) ordered.prepared.labels =
      Geometry.Grid.CellBoundary.sumValues (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary
        owner.lifted.vertices owner.lifted.edges)) owner.base.faces.holes := by
  have expand (branch : Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches) :
      requests.physicalArea value branch = Geometry.Grid.CellBoundary.sumValues
        (fun hole => if hole.index = branch then requests.physicalArea value branch else 0) owner.base.faces.holes :=
    (sum_unique (fun hole => hole.index) branch _ owner.base.faces.holes owner.base.faces.holes_pairwise
      (owner.base.faces.hole_complete branch)).symm
  rw [Geometry.Grid.CellBoundary.sumValues_congr _ _ ordered.prepared.labels (fun branch _ => expand branch),
    Geometry.Grid.CellBoundary.sumValues_swap]
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro hole _
  have scalar : Geometry.Grid.CellBoundary.sumValues (fun branch => if hole.index = branch then requests.physicalArea
    value branch else 0)
      ordered.prepared.labels = Geometry.Grid.CellBoundary.sumValues
      (fun branch => if branch = hole.index then requests.physicalArea value hole.index else 0) ordered.prepared.labels
        := by
    apply Geometry.Grid.CellBoundary.sumValues_congr
    intro branch _
    by_cases same : branch = hole.index
    · cases same; rw [if_pos rfl]
    · rw [if_neg same, if_neg (Ne.symm same)]
  rw [scalar, sum_unique (fun branch => branch) hole.index _ ordered.prepared.labels ordered.prepared.unique
    ⟨hole.index, ordered.complete hole.index, rfl⟩]
  exact congrArg (Topology.Mesh.RetracingWords.wordArea value) ((requests.rows.get hole.index).boundary_readback hole
    rfl)

end ValueHoleRequestBank

namespace Ordered.Paired.Prepared

variable {sheet : Fin 2} {ordered :
  Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet} {paired :
  Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

set_option genInjectivity false in
/-- The value-generic physical-hole aggregate. -/
structure ValueHoleAggregateRequest (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Gaussian.Basic.Canonical) (target :
      Fraction.Rational) where
  /-- The whole mixed hole-area target is positive. -/ positive : 0 < target
  /-- The original ordered branch labels with their actual arriving sheets. -/ labels : List
    (Hyperelliptic.Branches.BranchIsolation.Data.Index owner.branches × Fin 2)
  /-- The labels are exactly those retained by the prepared original stem excursions. -/ labels_eq : labels =
    prepared.stemLabels
  /-- The local mixed hole-area allowance. -/ allowance : Fraction.Rational
  /-- The allowance pays both factors of the actual retained label count. -/ allowance_eq : allowance =
    Rational.Budget.Aggregate.perTerm target labels.length
  /-- The original dependent physical-hole request bank at the local allowance. -/ holes : ValueHoleRequestBank (owner
    := owner) leftFixed rightFixed coefficient allowance
  /-- The cached common sufficient stage. -/ index : Nat
  /-- The stage is exactly the retained physical-hole bank's stage. -/ index_eq : index = holes.index

constructive_injectivity ValueHoleAggregateRequest

namespace ValueHoleAggregateRequest

variable {prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired} {leftDifferential
  rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential} {coefficient : Gaussian.Basic.Canonical} {target :
    Fraction.Rational}

/-- Prepare the mixed physical-hole bank with the original excursion labels and aggregate allowance. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (leftFixed :
  MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Gaussian.Basic.Canonical)
    (target : Fraction.Rational) (positive : 0 < target) :
    ValueHoleAggregateRequest (owner := owner) prepared leftFixed rightFixed coefficient target :=
  let labels := prepared.stemLabels
  let allowance := Rational.Budget.Aggregate.perTerm target labels.length
  let holes := ValueHoleRequestBank.build (owner := owner) leftFixed rightFixed coefficient allowance
    (Rational.Budget.Aggregate.perTerm_positive positive _)
  ⟨positive, labels, rfl, allowance, rfl, holes, holes.index, rfl⟩

/-- The mixed physical sum contains every retained hole exactly once, while
the single-lap terms use the actual sheet of each corrected excursion. -/
theorem accurate (request : ValueHoleAggregateRequest (owner := owner) prepared leftFixed rightFixed coefficient target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank)
    (rightReadings : TriangleCache owner rightDifferential stage domains rightBank) (later : request.index ≤ stage) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    let single := paired.rows.holeAreas value + paired.ending.holeAreas value
    normSq (single + single + Geometry.Grid.CellBoundary.sumValues
      (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary owner.lifted.vertices
        owner.lifted.edges)) owner.base.faces.holes) < target := by
  intro value single
  let errors := request.labels.map (fun entry => bank.holeArea value entry.1 entry.2 +
    bank.holeArea value entry.1 entry.2 + request.holes.physicalArea value entry.1)
  have estimate : normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum errors) < target := by
    apply Gaussian.Budget.Aggregate.normSq_sum_lt _ request.positive
    intro error member
    obtain ⟨entry, _, equal⟩ := Data.List.Map.mem_map.mp member
    rw [← equal, Data.List.Map.length_map]
    have bound := (request.holes.rows.get entry.1).accurate bank entry.2 leftReadings rightReadings
      ((request.holes.index_ge entry.1).trans (request.index_eq ▸ later))
    exact bound.trans_eq request.allowance_eq
  have holes : Geometry.Grid.CellBoundary.sumValues (fun entry => bank.holeArea value entry.1 entry.2) request.labels =
      paired.rows.holeAreas value + paired.ending.holeAreas value := by
    rw [request.labels_eq, Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared.stemLabels,
      Geometry.Grid.CellBoundary.sumValues_append, ← paired.rows.holeAreas_eq,
      ← paired.ending.holeAreas_eq]
  have physical : Geometry.Grid.CellBoundary.sumValues (fun entry => request.holes.physicalArea value entry.1)
    request.labels =
      Geometry.Grid.CellBoundary.sumValues (fun hole => Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary
        owner.lifted.vertices owner.lifted.edges)) owner.base.faces.holes := by
    rw [← Geometry.Grid.CellBoundary.sumValues_map (request.holes.physicalArea value) Prod.fst, request.labels_eq,
      prepared.stemLabels_first]
    exact request.holes.physical_sum value ordered
  change normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.labels.map _)) < target at estimate
  rw [← Geometry.Grid.CellBoundary.sumValues_eq_gaussianSum_map, Geometry.Grid.CellBoundary.sumValues_add,
    Geometry.Grid.CellBoundary.sumValues_add, holes, physical] at estimate
  exact estimate

end ValueHoleAggregateRequest
end Ordered.Paired.Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueHoleRequests
