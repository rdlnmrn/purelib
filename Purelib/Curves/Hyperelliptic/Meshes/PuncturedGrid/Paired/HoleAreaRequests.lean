module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchRemainders
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleGeometry

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

public section

/-! Compare a corrected single-lap hole area with half of the actual
two-lap physical boundary. Both the opposite-sheet area discrepancy and
the cross term of the two lap totals are paid on one shared numerical tail.
This is a boundary comparison, not a claim that a fixed hole has zero area. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleAreaRequests

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests (AreaRequest)

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}

/-- The retained squared-edge-count magnitude bound for one original inward hole lap. -/
@[expose] def holeLapMagnitude (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (hole : BranchHole base.bank.toBranchCellBank) : Fraction.Rational :=
  (hole.inwardBoundary.edgeCount : Fraction.Rational) ^ 2 * (4 * fixed.bound)

/-- The original hole lap magnitude is nonnegative. -/
public theorem magnitude_nonnegative (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank
  domains differential) (hole : BranchHole base.bank.toBranchCellBank) :
    0 ≤ holeLapMagnitude fixed hole :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.pow_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) fixed.nonnegative)

/-- The actual retained source summary of either original hole lap is bounded by the cached hole magnitude. -/
private theorem lap_magnitude (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (hole : BranchHole base.bank.toBranchCellBank)
    (retained : hole ∈ base.faces.holes) (paired : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk
      lifted.mesh hole.inwardBoundary)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (later : fixed.index ≤ stage) (sheet : Fin 2)
    (observations : Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.SourceObservations
      (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh lifted.mesh)
        readings.values (paired.sources sheet)) :
    normSq (Purelib.Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
      (lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary sheet)) ≤
      holeLapMagnitude fixed hole := open Purelib.Integration in by
  let magnitude := Readings.EdgeMagnitude.ofBank
    (owner := Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.ownerFromMesh lifted.mesh) fixed later
      readings
  have count : observations.increments.length = hole.inwardBoundary.edgeCount := by
    rw [observations.increments_eq, Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.IncrementList,
      Data.List.Map.length_map]
    have retainedCount := congrArg List.length (paired.sources_project sheet)
    rw [Data.List.Map.length_map, lifted.edges.indexedEdges_length] at retainedCount
    exact retainedCount
  have cached : Data.Gaussian.Norm.Basic.normSq observations.summary.total ≤ holeLapMagnitude fixed hole := by
    rw [observations.summary.total_eq]
    apply Path.IncrementArea.sum_bound_of_length
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) magnitude.nonnegative) ?_ ?_
    · intro value member
      rw [observations.increments_eq] at member
      obtain ⟨source, _, equal⟩ := Data.List.Map.mem_map.mp member
      rw [← equal]
      have h := magnitude.source_bounded source
      change Fraction.Order.Basic.LessEqual _ _ at h ⊢
      exact h
    · exact count.le
  rw [observations.summary.total_eq, observations.increments_eq] at cached
  rw [← Topology.Mesh.RetracingWords.sum_map_eq_wordValue, ←
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords.hole_lap_values hole retained paired]
  rw [Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison.IncrementList] at cached
  change Fraction.Order.Basic.LessEqual _ _ at cached ⊢
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
  exact cached

set_option genInjectivity false in
/-- A paid area and total-increment request on the original paired inward hole walk.

It retains the same paired observations for the area and total comparisons, the original lap magnitude and a common
sufficient stage. -/
structure HoleAreaRequest (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential)
    (hole : BranchHole base.bank.toBranchCellBank) (target : Fraction.Rational) where
  /-- The requested whole hole-area error is positive. -/ positive : 0 < target
  /-- The cached magnitude of an original inward hole lap. -/ magnitude : Fraction.Rational
  /-- The magnitude is exactly the retained squared-edge-count bound. -/ magnitude_eq : magnitude = holeLapMagnitude
    fixed hole
  /-- The local total-increment allowance paid against four times the lap magnitude. -/ totalTarget : Fraction.Rational
  /-- The total allowance is the weighted allowance for one quarter of the original area target. -/ totalTarget_eq :
    totalTarget = Rational.Budget.Weighted.allowance (target / 4) (4 * magnitude)
  /-- The original paired request on the actual inward hole walk. -/ paired :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk lifted.mesh hole.inwardBoundary
  /-- The area comparison on that same paired walk at one quarter of the target. -/ areas : AreaRequest fixed paired
    (target / 4)
  /-- The total-increment comparison on the same paired walk and retained allowance. -/ total :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := lifted.mesh) domains
    differential hole.inwardBoundary totalTarget
  /-- The common sufficient stage for the original area and total requests. -/ index : Nat
  /-- The sufficient stage is exactly the maximum of the retained area and total stages. -/ index_eq : index = max
    areas.index total.index

constructive_injectivity HoleAreaRequest

namespace HoleAreaRequest

variable {fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains differential} {hole :
  BranchHole base.bank.toBranchCellBank} {target : Fraction.Rational}

/-- Prepare one original paired inward walk and reuse it for the paid area and total-increment requests. -/
@[expose] def build (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential) (hole : BranchHole base.bank.toBranchCellBank)
    (target : Fraction.Rational) (positive : 0 < target) : HoleAreaRequest fixed hole target :=
  let magnitude := holeLapMagnitude fixed hole
  let totalTarget := Rational.Budget.Weighted.allowance (target / 4) (4 * magnitude)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let paired := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.build lifted.mesh
    hole.inwardBoundary
  let areas := AreaRequest.build fixed paired (target / 4) quarterPositive
  let total := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest.ofPaired paired domains
    differential totalTarget
    (Rational.Budget.Weighted.allowance_positive quarterPositive (Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide) (magnitude_nonnegative fixed hole)))
  ⟨positive, magnitude, rfl, totalTarget, rfl, paired, areas, total, max areas.index total.index, rfl⟩

open Purelib.Integration in
/-- Twice the actual area of either original hole lap differs from the complete paired physical hole area by at most the
requested target.

The estimate retains the original lap magnitude and pays the cross ribbon with the total-increment allowance. -/
theorem lap_accurate (request : HoleAreaRequest fixed hole target) (retained : hole ∈ base.faces.holes)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (later : request.index ≤ stage) (sheet : Fin 2) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values
    let lap := lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary sheet
    normSq (Topology.Mesh.RetracingWords.wordArea value lap + Topology.Mesh.RetracingWords.wordArea value lap -
      Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary lifted.vertices lifted.edges)) ≤ target := by
  have areaLater := (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have totalLater := (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have fixedLater := (Data.Nat.Order.le_max_left _ _).trans (request.areas.index_eq ▸ areaLater)
  let areaComparison := request.areas.realize readings areaLater 0 1 (by decide)
  have areaError := areaComparison.pay
  rw [areaComparison.area_readback] at areaError
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords.hole_lap_values hole retained request.paired,
    Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleWords.hole_lap_values hole retained request.paired] at areaError
  have total := (Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary.canonical_hole_accurate hole retained
    request.total readings totalLater).le
  rw [hole.liftedBoundary_eq, Topology.Surface.Sewing.SewingRetraction.wordValue_append] at total
  let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values
  let zero := lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary 0
  let one := lifted.edges.indexedEdges lifted.vertices hole.inwardBoundary 1
  have magnitude := lap_magnitude fixed hole retained request.paired readings fixedLater 0 areaComparison.leftSources
  rw [← request.magnitude_eq] at magnitude
  have oldBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : normSq point ≤ limit) : Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have canonicalBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) : normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using h
  have cross : normSq (Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value zero)
    (Topology.Surface.Sewing.SewingRetraction.wordValue value one)) ≤ target / 4 := by
    have equal : Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value zero)
      (Topology.Surface.Sewing.SewingRetraction.wordValue value one) =
        Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value zero)
          (Topology.Surface.Sewing.SewingRetraction.wordValue value zero +
          Topology.Surface.Sewing.SewingRetraction.wordValue value one) := by
      rw [Path.IncrementArea.area_add_right, Path.IncrementArea.area_self, Gaussian.Basic.zero_add]
    rw [equal]
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    have nonnegative : 0 ≤ request.magnitude := request.magnitude_eq ▸ magnitude_nonnegative fixed hole
    have product := Fraction.Order.Arithmetic.mul_le_mul_direct (oldBound magnitude) total
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
  have cases : sheet = 0 ∨ sheet = 1 := by
    have bound := sheet.isLt
    by_cases zero : sheet.val = 0
    · exact Or.inl (Fin.ext zero)
    · exact Or.inr (Fin.ext (by change sheet.val = 1; omega))
  have finish (first second : Gaussian.Basic.Canonical) (bound : Data.Gaussian.Norm.Basic.normSq first ≤ target / 4)
    (other : Data.Gaussian.Norm.Basic.normSq second ≤ target / 4) :
      normSq (first - second) ≤ target :=
    canonicalBound (((Gaussian.Norm.Bounds.normSq_sub_le_two first second).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct bound
      other) (by decide))).trans_eq
      ((by ring1 : 2 * (target / 4 + target / 4) = target / 4 * 4).trans
        (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))))
  dsimp only
  rw [hole.liftedBoundary_eq, Topology.Mesh.RetracingWords.wordArea_append]
  rcases cases with rfl | rfl
  · have equal (a b c : Gaussian.Basic.Canonical) : a + a - (a + b + c) = (a - b) - c := by ring1
    have bounded := finish
      (Topology.Mesh.RetracingWords.wordArea value zero - Topology.Mesh.RetracingWords.wordArea value one)
      (Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value zero)
        (Topology.Surface.Sewing.SewingRetraction.wordValue value one))
      (oldBound areaError) (oldBound cross)
    exact (congrArg normSq (equal (Topology.Mesh.RetracingWords.wordArea value zero)
      (Topology.Mesh.RetracingWords.wordArea value one) _)).trans_le
      bounded
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
/-- The factor two and orientation sign are explicit: a corrected hole
contributes minus one half of its full clockwise physical boundary, up to
the requested error. No zero-area assertion is made for that boundary. -/
theorem corrected_accurate (request : HoleAreaRequest fixed hole target) (retained : hole ∈ base.faces.holes)
    (bank : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (sheet : Fin
      2)
    {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
      domains} (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared
      lifted.mesh)
    (later : request.index ≤ stage) :
    let value := Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh readings.values
    normSq (bank.holeArea value hole.index sheet + bank.holeArea value hole.index sheet +
      Topology.Mesh.RetracingWords.wordArea value (hole.liftedBoundary lifted.vertices lifted.edges)) ≤ target := by
  dsimp only
  rw [bank.holeArea_reverse hole sheet _ (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation_reverse
    lifted.mesh readings.values)]
  have bound := request.lap_accurate retained readings later
    (Hyperelliptic.Branches.BranchCutLifts.otherSheet (SquareRoot.Grid.EdgeBank.RootEdgeBank.target lifted.edges
      (bank.rows.get hole.index).stem sheet))
  rw [show ∀ a b : Gaussian.Basic.Canonical, -a + -a + b = -(a + a - b) by intros; ring1,
    Gaussian.Basic.Canonical.normSq_neg]
  exact bound

end HoleAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HoleAreaRequests
