module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.PairedSources

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison

import Purelib.Integration.Path.AreaComparison

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedWalk
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.AreaComparison

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Surface.Sewing

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Domains MagnitudeBank PrimitiveBank
  TriangleCache Source Sources Nonloop)

/-!
# Value-parameterized paired edge requests

`FramedPuncturedGrid.PairedWalk.Requests` pays one whole-edge comparison per
retained grid edge. A mixed value has no differential, but its per-edge
defect is the conjugate-linear combination of the two sides' defects. This
module caches both single-differential per-edge requests and exposes the
combined defect bound used by the opposite-sheet area comparison.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Riemann.Meshes.PuncturedEdgeFaces (RegularEdgeCell)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk (EdgeRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}
  {domains : Domains owner}

set_option genInjectivity false in
/-- One whole-edge request for each differential on the same retained edge. -/
inductive ValueRequests (leftDifferential rightDifferential : Differentials.Basic.Differential genus)
    (domains : Domains owner) (coefficient : Data.Gaussian.Basic.Canonical) (target : Fraction.Rational) :
    {start finish : Data.Gaussian.Basic.Canonical} → {walk : Walks.Walk owner.base.bank.grid start finish} →
      WalkOccurrences.PairedWalk owner.mesh walk → Type where
  /-- The empty original paired walk carries no edge requests. -/ | nil (point : Data.Gaussian.Basic.Canonical) :
    ValueRequests leftDifferential rightDifferential domains coefficient target (.nil point)
  /-- Retain both original differential requests on the actual paired head edge and the dependent request bank on its
    unchanged tail. -/ | cons {start middle finish : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge
    owner.base.bank.grid start middle}
      {walk : Walks.Walk owner.base.bank.grid middle finish} {head : Paired.EdgeOccurrences owner.mesh edge}
      {tail : WalkOccurrences.PairedWalk owner.mesh walk}
      (left : PairedWalk.EdgeRequest domains leftDifferential head target)
      (right : PairedWalk.EdgeRequest domains rightDifferential head target)
      (remaining : ValueRequests leftDifferential rightDifferential domains coefficient target tail) :
      ValueRequests leftDifferential rightDifferential domains coefficient target (.cons head tail)

constructive_injectivity ValueRequests

namespace ValueRequests

variable {leftDifferential rightDifferential : Differential genus}
  {coefficient : Purelib.Data.Gaussian.Basic.Canonical}
  {target : Rational}

/-- The maximum stage of both original per-edge requests over the entire retained paired walk. -/
@[expose] def index : ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start
  finish}
    {paired : WalkOccurrences.PairedWalk owner.mesh walk}, ValueRequests leftDifferential rightDifferential domains
      coefficient target paired → Nat
  | _, _, _, _, .nil _ => 0
  | _, _, _, _, .cons left right tail => max left.index (max right.index tail.index)

/-- Prepare both differential requests on every actual original paired edge while preserving the retained walk spine. -/
@[expose] def build (domains : Domains owner)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) (coefficient :
      Data.Gaussian.Basic.Canonical)
    (target : Fraction.Rational) (positive : 0 < target) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
      (paired : WalkOccurrences.PairedWalk owner.mesh walk),
      ValueRequests leftDifferential rightDifferential domains coefficient target paired
  | _, _, _, .nil point => .nil point
  | _, _, _, .cons head tail =>
      .cons (head.request domains leftDifferential target positive)
        (head.request domains rightDifferential target positive)
        (build domains leftDifferential rightDifferential coefficient target positive tail)

end ValueRequests

/-- The original ordered source-increment pairs, negating the second sheet and transporting both sheet indices along
each retained edge. -/
@[expose] def incrementPairs (values : Fin owner.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    {start finish : Data.Gaussian.Basic.Canonical} → {walk : Walks.Walk owner.base.bank.grid start finish} →
      WalkOccurrences.PairedWalk owner.mesh walk → Fin 2 → Fin 2 → List (Data.Gaussian.Basic.Canonical ×
        Data.Gaussian.Basic.Canonical)
  | _, _, _, .nil _, _, _ => []
  | _, _, _, .cons (edge := edge) head tail, left, right =>
      ((head.source left).increment values, -(head.source right).increment values) ::
        incrementPairs values tail ((owner.edges.edge edge).forward.target left) ((owner.edges.edge edge).forward.target
          right)

/-- The protected scalar walk specification reads the same acquired source pairs. -/
theorem incrementPairs_sources (values : Values owner) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
      (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2),
      (PairedSources.pairs (owner := owner) paired left right).map
        (fun pair => (pair.1.increment values, -pair.2.increment values)) = incrementPairs values paired left right
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons (edge := edge) head tail, left, right =>
      congrArg (List.cons ((head.source left).increment values, -(head.source right).increment values))
        (incrementPairs_sources values tail ((owner.edges.edge edge).forward.target left)
          ((owner.edges.edge edge).forward.target right))

/-- The two distinct original sheet increments sum to the retained zero-sheet plus one-sheet source increments. -/
private theorem source_sum {start finish : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge owner.base.bank.grid start
  finish}
    (head : Paired.EdgeOccurrences owner.mesh edge) (values : Fin owner.mesh.triangles.length →
      PrimitiveSewing.PrimitiveValues 3)
    (left right : Fin 2) (different : left ≠ right) :
    (head.source left).increment values + (head.source right).increment values =
      head.zeroSource.increment values + head.oneSource.increment values := by
  rcases left with ⟨leftValue, leftBound⟩
  rcases right with ⟨rightValue, rightBound⟩
  cases leftValue with
  | zero =>
      cases rightValue with
      | zero => exact (different rfl).elim
      | succ rightValue =>
          cases rightValue with
          | zero => rfl
          | succ rightValue =>
              exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ
                (Nat.lt_of_succ_lt_succ rightBound))).elim
  | succ leftValue =>
      cases leftValue with
      | succ leftValue =>
          exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ
            (Nat.lt_of_succ_lt_succ leftBound))).elim
      | zero =>
          cases rightValue with
          | zero => exact _root_.add_comm _ _
          | succ rightValue =>
              cases rightValue with
              | zero => exact (different rfl).elim
              | succ rightValue =>
                  exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ
                    (Nat.lt_of_succ_lt_succ rightBound))).elim

/-- Every retained edge defect of the mixed value is bounded by the combined per-edge targets of the two
single-differential requests. -/
theorem pair_errors {sampleIndex : Nat}
    {leftBank : PrimitiveBank owner leftDifferential sampleIndex domains}
    {rightBank : PrimitiveBank owner rightDifferential sampleIndex domains}
    (leftReadings : TriangleCache owner leftDifferential sampleIndex domains leftBank) (rightReadings : TriangleCache
      owner rightDifferential sampleIndex domains rightBank) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
      (paired : WalkOccurrences.PairedWalk owner.mesh walk)
      (requests : ValueRequests leftDifferential rightDifferential domains coefficient target paired)
      (left right : Fin 2), left ≠ right → requests.index ≤ sampleIndex →
      ∀ pair ∈ incrementPairs (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
        coefficient)
        paired left right,
        normSq (pair.1 - pair.2) ≤ 2 * (1 + normSq coefficient) * target
  | _, _, _, .nil _, .nil _, _, _, _, _, _, member => (List.not_mem_nil member).elim
  | _, _, _, .cons (edge := edge) head tail, .cons leftRequest rightRequest remaining,
      left, right, different, later, pair, member => by
      rcases Data.List.Membership.mem_cons.mp member with rfl | member
      · change normSq ((head.source left).increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
          rightReadings.values coefficient) -
          -(head.source right).increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
            rightReadings.values coefficient)) ≤
          2 * (1 + normSq coefficient) * target
        have expand : (head.source left).increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
          rightReadings.values coefficient) +
            (head.source right).increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
              rightReadings.values coefficient) =
            conj (head.zeroSource.increment leftReadings.values +
              head.oneSource.increment leftReadings.values) +
              coefficient * (head.zeroSource.increment rightReadings.values +
                head.oneSource.increment rightReadings.values) := by
          rw [source_sum head _ left right different]
          simp only [EdgeMagnitude.source_increment_mixValues (owner := owner),
            Data.Gaussian.Basic.conj_eq_canonical,
            Data.Gaussian.Basic.Canonical.conj_add]
          ring1
        have removeNeg : (head.source left).increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
          rightReadings.values coefficient) -
            -(head.source right).increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
              rightReadings.values coefficient) =
            (head.source left).increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
              rightReadings.values coefficient) +
              (head.source right).increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values
                rightReadings.values coefficient) := by ring1
        rw [removeNeg, expand]
        have leftLater : leftRequest.index ≤ sampleIndex :=
          (Data.Nat.Order.le_max_left _ _).trans later
        have rightLater : rightRequest.index ≤ sampleIndex :=
          (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)
        have leftHead := (head.accurate leftReadings leftReadings leftRequest leftLater leftLater).le
        have rightHead := (head.accurate rightReadings rightReadings rightRequest rightLater rightLater).le
        have estimate : normSq (conj (head.zeroSource.increment leftReadings.values +
            head.oneSource.increment leftReadings.values) + coefficient *
              (head.zeroSource.increment rightReadings.values + head.oneSource.increment rightReadings.values)) ≤
            2 * (normSq (head.zeroSource.increment leftReadings.values +
              head.oneSource.increment leftReadings.values) + normSq coefficient *
              normSq (head.zeroSource.increment rightReadings.values + head.oneSource.increment rightReadings.values))
                := by
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical,
            Data.Gaussian.Basic.conj_eq_canonical] using
            EdgeMagnitude.normSq_conj_add_mul
              (head.zeroSource.increment leftReadings.values + head.oneSource.increment leftReadings.values)
              (head.zeroSource.increment rightReadings.values + head.oneSource.increment rightReadings.values)
              coefficient
        have leftHead' : normSq (head.zeroSource.increment leftReadings.values +
            head.oneSource.increment leftReadings.values) ≤ target := by
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using leftHead
        have rightHead' : normSq (head.zeroSource.increment rightReadings.values +
            head.oneSource.increment rightReadings.values) ≤ target := by
          simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using rightHead
        refine estimate.trans ?_
        have inner : normSq (head.zeroSource.increment leftReadings.values +
            head.oneSource.increment leftReadings.values) +
            normSq coefficient * normSq (head.zeroSource.increment rightReadings.values +
              head.oneSource.increment rightReadings.values) ≤ target + normSq coefficient * target :=
          Fraction.Order.Arithmetic.add_le_add_direct leftHead'
            (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightHead'
              (Data.Gaussian.Basic.Canonical.normSq_nonneg coefficient))
        have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inner (by
            decide : (0 : Fraction.Rational) ≤ 2)
        exact scaled.trans_eq (by ring1)
      · have injective := ((owner.edges.edge edge).bijection
          (BranchCellBank.referenceAt owner.base.bank.toBranchCellBank _ edge.vertices.1).toLoop
          (BranchCellBank.referenceAt owner.base.bank.toBranchCellBank _ edge.vertices.2).toLoop).forward_injective
        exact pair_errors leftReadings rightReadings tail remaining _ _ (fun equal => different (injective equal))
          ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans later)) pair member

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk (EdgeRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (negative_area pathArea pathArea_cons)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}
  {domains : Domains owner}

/-- The actual retained increment-pair count equals the original walk's edge count. -/
private theorem pairs_length (values : Fin owner.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
      (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2),
      (incrementPairs values paired left right).length = walk.edgeCount
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons _ tail, _, _ => congrArg Nat.succ (pairs_length values tail _ _)

/-- The first projection of the retained increment pairs is exactly the original left-sheet source increment list. -/
private theorem pairs_first (values : Fin owner.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
      (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2),
      (incrementPairs values paired left right).map Prod.fst =
        (paired.sources left).map (fun source => source.increment values)
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons _ tail, _, _ => congrArg (List.cons _) (pairs_first values tail _ _)

/-- The second projection of the retained increment pairs is exactly the negated original right-sheet source increment
list. -/
private theorem pairs_second (values : Fin owner.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
      (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2),
      (incrementPairs values paired left right).map Prod.snd =
        (paired.sources right).map (fun source => -source.increment values)
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons _ tail, _, _ => congrArg (List.cons _) (pairs_second values tail _ _)

open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
  (SourceObservations)

/-- The retained original paired source occurrences on both selected sheets of the exact walk. -/
@[expose, reducible] def OppositeSelection
    {start finish : Data.Gaussian.Basic.Canonical}
    {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2) :=
  PairedSources.Selection (owner := owner) paired left right

/-- Compact exact pair specification, retaining the original walk algorithm. -/
@[expose, reducible] def OppositePairs (values : Values owner)
    {start finish : Data.Gaussian.Basic.Canonical}
    {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2) :=
  incrementPairs values paired left right

/-- The cached original source increments and summary for one selected sheet of the retained walk. -/
@[expose, reducible] def OppositeSources (values : Values owner)
    {start finish : Data.Gaussian.Basic.Canonical}
    {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (sheet : Fin 2) :=
  SourceObservations values (paired.sources sheet)

/-- Exact equality with the original signed increment-pair specification on the retained paired walk. -/
@[expose, reducible] def OppositePairIdentity (values : Values owner)
    {start finish : Data.Gaussian.Basic.Canonical}
    {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2)
    (pairs : List (Data.Gaussian.Basic.Canonical × Data.Gaussian.Basic.Canonical)) : Prop :=
  pairs = OppositePairs values paired left right

set_option genInjectivity false in
/-- Actual cached pair observations shared with the two source/chart clients. -/
structure OppositeComparison (values : Values owner)
    {start finish : Data.Gaussian.Basic.Canonical}
    {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2)
    (error bound : Fraction.Rational) where
  /-- The actual retained source-pair selection in original walk order. -/ sourceSelection : OppositeSelection paired
    left right
  /-- The cached actual ordered source increment pairs with the second component negated. -/ pairs : List
    (Data.Gaussian.Basic.Canonical × Data.Gaussian.Basic.Canonical)
  /-- The retained increment pairs are exactly the original signed walk specification. -/ pairs_eq :
    OppositePairIdentity values paired left right pairs
  /-- The cached executable summary of the actual first pair projection. -/ firstSummary : AreaComparison.FirstSummary
    pairs
  /-- The cached executable summary of the actual negated second pair projection. -/ secondSummary :
    AreaComparison.SecondSummary pairs
  /-- The original left-sheet source cache using the retained first projection summary. -/ leftSources : OppositeSources
    values paired left
  /-- The left source increments are exactly the retained first pair projection. -/ leftIncrements_eq :
    leftSources.increments = pairs.map Prod.fst
  /-- The left source area is exactly the cached first projection area. -/ leftArea_eq : leftSources.summary.area =
    firstSummary.area
  /-- The original right-sheet source cache transported from the retained negated second summary. -/ rightSources :
    OppositeSources values paired right
  /-- The right source increments are exactly the negation of the retained second pair projection. -/ rightIncrements_eq
    : rightSources.increments = (pairs.map Prod.snd).map (fun value => -value)
  /-- The right source area equals the retained second summary area. -/ rightArea_eq : rightSources.summary.area =
    secondSummary.area
  /-- The actual numerical comparison bound on the exact retained pairs and both cached projection summaries. -/ numeric
    : AreaComparison.Cached pairs error bound firstSummary secondSummary

constructive_injectivity OppositeComparison

namespace OppositeComparison

variable {values : Values owner}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {walk : Purelib.Polynomial.Geometry.Grid.Walks.Walk owner.base.bank.grid start finish}
  {paired : PairedWalk owner.mesh walk} {left
    right : Fin 2} {error bound : Rational}

/-- Negating every entry of the original negated value list recovers the original value list structurally. -/
private theorem unnegative_map {α : Type} (value : α → Data.Gaussian.Basic.Canonical) (entries : List α) :
    (entries.map (fun entry => -value entry)).map (fun entry => -entry) = entries.map value := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
      change -(-value head) :: ((tail.map (fun entry => -value entry)).map (fun entry => -entry)) =
        value head :: tail.map value
      rw [neg_neg]
      exact congrArg (List.cons (value head)) ih

/-- Source increments are acquired once in original walk order. The forward right source summary is transported from the
retained negative second summary; neither source path is traversed again to calculate its area. -/
@[expose] def realizeSupplied (values : Values owner) (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right
  : Fin 2)
    (selection : OppositeSelection paired left right)
    (error bound : Fraction.Rational) (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : AreaComparison.PairErrors (OppositePairs values paired left right) error)
    (leftBound : ∀ source ∈ paired.sources left, normSq (source.increment values) ≤ bound)
    (rightBound : ∀ source ∈ paired.sources right, normSq (source.increment values) ≤ bound) :
    OppositeComparison values paired left right error bound :=
  let pairs := selection.entries.map (fun pair => (pair.1.increment values, -pair.2.increment values))
  have canonical : pairs = OppositePairs values paired left right := by
    change selection.entries.map (fun pair => (pair.1.increment values, -pair.2.increment values)) = _
    rw [selection.entries_eq]
    exact incrementPairs_sources values paired left right
  let firstIncrements := pairs.map Prod.fst
  let secondIncrements := pairs.map Prod.snd
  let firstSummary := IncrementArea.Summary.build firstIncrements
  let secondSummary := IncrementArea.Summary.build secondIncrements
  let leftSources : OppositeSources values paired left :=
    { increments := firstIncrements
      increments_eq := by
        change pairs.map Prod.fst = _
        rw [canonical, OppositePairs]
        exact pairs_first values paired left right
      summary := firstSummary }
  let rightIncrements := secondIncrements.map (fun value => -value)
  have rightCanonical : rightIncrements =
      (paired.sources right).map (fun source => source.increment values) := by
    change (pairs.map Prod.snd).map (fun value => -value) = _
    rw [canonical, OppositePairs, pairs_second]
    exact unnegative_map (fun source => source.increment values) (paired.sources right)
  let rightSources : OppositeSources values paired right :=
    { increments := rightIncrements
      increments_eq := rightCanonical
      summary := IncrementArea.Summary.negate secondSummary }
  have first : AreaComparison.FirstBounds pairs bound := by
    intro pair member
    have mapped : pair.1 ∈ pairs.map Prod.fst :=
      Map.mem_map_of_mem member
    rw [canonical, OppositePairs, pairs_first] at mapped
    obtain ⟨source, inSources, equal⟩ := Map.mem_map.mp mapped
    rw [← equal]
    exact leftBound source inSources
  have second : AreaComparison.SecondBounds pairs bound := by
    intro pair member
    have mapped : pair.2 ∈ pairs.map Prod.snd :=
      Map.mem_map_of_mem member
    rw [canonical, OppositePairs, pairs_second] at mapped
    obtain ⟨source, inSources, equal⟩ := Map.mem_map.mp mapped
    rw [← equal, Data.Gaussian.Basic.Canonical.normSq_neg]
    exact rightBound source inSources
  { sourceSelection := selection
    pairs := pairs
    pairs_eq := canonical
    firstSummary := firstSummary
    secondSummary := secondSummary
    leftSources := leftSources
    leftIncrements_eq := rfl
    leftArea_eq := rfl
    rightSources := rightSources
    rightIncrements_eq := rfl
    rightArea_eq := rfl
    numeric := Cached.realize pairs error bound
      firstSummary secondSummary errorNonnegative boundNonnegative
        (by rw [canonical]; exact errors) first second }

/-- Retain the original paired source selection and realize its numerical comparison using the supplied complete error
and magnitude bounds. -/
@[expose] def realize (values : Values owner) (paired : WalkOccurrences.PairedWalk owner.mesh walk) (left right : Fin 2)
    (error bound : Fraction.Rational) (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : AreaComparison.PairErrors (OppositePairs values paired left right) error)
    (leftBound : ∀ source ∈ paired.sources left, normSq (source.increment values) ≤ bound)
    (rightBound : ∀ source ∈ paired.sources right, normSq (source.increment values) ≤ bound) :
    OppositeComparison values paired left right error bound :=
  realizeSupplied values paired left right
    (PairedSources.realize (owner := owner) paired left right)
    error bound errorNonnegative boundNonnegative errors leftBound rightBound

/-- The cached difference of the two actual retained source path areas. -/
@[expose] def residual (comparison : OppositeComparison values paired left right error bound) :=
  comparison.numeric.residual

/-- The cached fourth-power edge-count bound for the actual opposite-sheet area residual. -/
@[expose] def areaBound (comparison : OppositeComparison values paired left right error bound) :=
  comparison.numeric.areaBound

/-- The cached residual equals the difference of the original retained left and right source summary areas. -/
theorem residual_eq (comparison : OppositeComparison values paired left right error bound) :
    comparison.residual = comparison.leftSources.summary.area - comparison.rightSources.summary.area := by
  rw [comparison.leftArea_eq, comparison.rightArea_eq]
  exact comparison.numeric.residual_eq

/-- The area bound is exactly the original edge-count fourth-power expression with the retained error and magnitude
budgets. -/
theorem areaBound_eq (comparison : OppositeComparison values paired left right error bound) :
    comparison.areaBound = 16 * (walk.edgeCount : Fraction.Rational) ^ 4 * error * bound := by
  rw [areaBound, comparison.numeric.areaBound_eq, comparison.pairs_eq]
  rw [OppositePairs, pairs_length]

/-- The cached residual reads the difference of the two actual original source polygon areas. -/
theorem area_readback (comparison : OppositeComparison values paired left right error bound) :
    comparison.residual =
      IncrementArea.pathArea ((paired.sources left).map (fun source => source.increment values)) -
      IncrementArea.pathArea ((paired.sources right).map (fun source => source.increment values)) := by
  rw [comparison.residual_eq, comparison.leftSources.area_readback, comparison.rightSources.area_readback]

/-- A paid cached area bound controls the squared norm of the actual retained opposite-sheet residual. -/
theorem pay (comparison : OppositeComparison values paired left right error bound) {target : Fraction.Rational}
    (paid : comparison.areaBound ≤ target) : normSq comparison.residual ≤ target :=
  comparison.numeric.pay paid

end OppositeComparison

/-- The mixed opposite-sheet source area difference obeys the same fourth-power count law, with the combined per-edge
error and the mixed magnitude bound. -/
theorem value_area_difference_bound {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    {coefficient : Data.Gaussian.Basic.Canonical} {target bound : Fraction.Rational} {sampleIndex : Nat}
    {leftBank : PrimitiveBank owner leftDifferential sampleIndex domains}
    {rightBank : PrimitiveBank owner rightDifferential sampleIndex domains}
    (leftReadings : TriangleCache owner leftDifferential sampleIndex domains leftBank) (rightReadings : TriangleCache
      owner rightDifferential sampleIndex domains rightBank)
    {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk)
    (requests : ValueRequests leftDifferential rightDifferential domains coefficient target paired)
    (left right : Fin 2) (different : left ≠ right) (later : requests.index ≤ sampleIndex)
    (targetNonnegative : 0 ≤ 2 * (1 + normSq coefficient) * target) (boundNonnegative : 0 ≤ bound)
    (leftBound : ∀ source ∈ paired.sources left,
      normSq (source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
        coefficient)) ≤ bound)
    (rightBound : ∀ source ∈ paired.sources right,
      normSq (source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
        coefficient)) ≤ bound) :
    normSq (IncrementArea.pathArea ((paired.sources left).map (fun source =>
        source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
          coefficient))) -
      IncrementArea.pathArea ((paired.sources right).map (fun source =>
        source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
          coefficient)))) ≤
      16 * (walk.edgeCount : Fraction.Rational) ^ 4 * (2 * (1 + normSq coefficient) * target) * bound := by
  let comparison := OppositeComparison.realize
    (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    paired left right (2 * (1 + normSq coefficient) * target) bound
    targetNonnegative boundNonnegative
    (pair_errors leftReadings rightReadings paired requests left right different later) leftBound rightBound
  have estimate := comparison.numeric.bounded
  change normSq comparison.residual ≤ comparison.areaBound at estimate
  rw [comparison.area_readback, comparison.areaBound_eq] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests
