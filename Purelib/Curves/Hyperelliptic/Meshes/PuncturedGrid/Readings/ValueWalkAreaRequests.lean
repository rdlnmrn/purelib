module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Domains MagnitudeBank PrimitiveBank
  TriangleCache Source Sources Nonloop)

/-!
# Value-parameterized walk area and increment requests

`FramedPuncturedGrid.PairedWalk.AreaRequest` controls the opposite-sheet
source polygons and `IncrementRequest` controls the two-sheet word
increment. Both are single-differential. This module caches one of each per
differential and exposes the conjugate-linear mixed bounds consumed by the
stem and hole aggregates.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWalkAreaRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (pathArea)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests (ValueRequests
  value_area_difference_bound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkIncrementRequests.FramedPuncturedGrid.PairedWalk
  (IncrementRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}
  {domains : Domains owner}

set_option genInjectivity false in
/-- A paid opposite-sheet area request for the conjugate-linear combination of two original differential readings.

The retained magnitude references and complete paired walk determine a single per-edge allowance and common request
stage. -/
structure ValueAreaRequest {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (target : Fraction.Rational) where
  /-- The original requested target is strictly positive. -/ positive : 0 < target
  /-- The retained complete walk-count and mixed-magnitude area weight. -/ weight : Fraction.Rational
  /-- The cached weight is exactly the original mixed-area scaling expression. -/ weight_eq : weight = 128 * (1 + normSq
    coefficient) * (walk.edgeCount : Fraction.Rational) ^ 4 *
    EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient
  /-- The retained positive allowance for every original paired edge. -/ perEdge : Fraction.Rational
  /-- The per-edge allowance is exactly the weighted allowance for the original target and cached weight. -/ perEdge_eq
    : perEdge = Weighted.allowance target weight
  /-- The retained per-edge allowance is strictly positive. -/ perEdge_positive : 0 < perEdge
  /-- The original mixed whole-edge request bank on the retained paired walk. -/ requests : ValueRequests
    leftDifferential rightDifferential domains coefficient perEdge paired
  /-- The cached common stage paying all retained original requests. -/ index : Nat
  /-- The cached stage is the maximum of the original retained request stages. -/ index_eq : index = max (max
    leftFixed.index rightFixed.index) requests.index

constructive_injectivity ValueAreaRequest

namespace ValueAreaRequest

variable {leftDifferential rightDifferential : Differential genus}
  {coefficient : Purelib.Data.Gaussian.Basic.Canonical}
  {leftFixed : MagnitudeBank owner domains leftDifferential}
  {rightFixed : MagnitudeBank owner domains rightDifferential}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {walk : Purelib.Polynomial.Geometry.Grid.Walks.Walk
    owner.base.bank.grid start finish}
  {paired : PairedWalk owner.mesh walk} {target
    : Rational}

/-- The complete mixed-area weight is nonnegative for the original magnitude references and walk. -/
public theorem weight_nonnegative (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (walk : Walks.Walk owner.base.bank.grid start finish) :
    0 ≤ 128 * (1 + normSq coefficient) * (walk.edgeCount : Fraction.Rational) ^ 4 *
      EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 128)
    (add_nonneg (by decide) (Data.Gaussian.Basic.Canonical.normSq_nonneg coefficient)))
    (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
    (EdgeMagnitude.mixBound_nonnegative leftFixed.nonnegative rightFixed.nonnegative coefficient)

/-- Prepare the original mixed whole-edge request bank with the weighted per-edge allowance and cache its common stage
with both magnitude references. -/
@[expose] def build (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical)
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (target : Fraction.Rational) (positive : 0 < target) :
    ValueAreaRequest (owner := owner) leftFixed rightFixed coefficient paired target :=
  let weight := 128 * (1 + normSq coefficient) * (walk.edgeCount : Fraction.Rational) ^ 4 *
    EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient
  let perEdge := Weighted.allowance target weight
  have weightNonnegative : 0 ≤ weight := weight_nonnegative leftFixed rightFixed coefficient walk
  have perEdgePositive : 0 < perEdge :=
    Weighted.allowance_positive positive weightNonnegative
  let requests := ValueRequests.build domains leftDifferential rightDifferential coefficient perEdge
    perEdgePositive paired
  ⟨positive, weight, rfl, perEdge, rfl, perEdgePositive, requests,
    max (max leftFixed.index rightFixed.index) requests.index, rfl⟩

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
  (MixedReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedEdgeRequests
  (OppositeComparison OppositePairs pair_errors)

/-- The original per-edge allowance scaled by twice one plus the coefficient squared norm. -/
@[expose, reducible] def RealizationError (request : ValueAreaRequest (owner := owner) leftFixed rightFixed coefficient
  paired target) :=
  2 * (1 + normSq coefficient) * request.perEdge

/-- Four times the original mixed magnitude bound on the two retained references. -/
@[expose, reducible] def RealizationBound (leftFixed : MagnitudeBank owner domains leftDifferential)
    (rightFixed : MagnitudeBank owner domains rightDifferential) (coefficient : Data.Gaussian.Basic.Canonical) :=
  4 * EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient

/-- The actual opposite-sheet polygon comparison on the original mixed readings and retained error and magnitude bounds.
-/
@[expose, reducible] def RealizationComparison
    (request : ValueAreaRequest (owner := owner) leftFixed rightFixed coefficient paired target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank) (rightReadings : TriangleCache owner
      rightDifferential stage domains rightBank)
    (left right : Fin 2) :=
  OppositeComparison
    (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    paired left right (RealizationError request) (RealizationBound leftFixed rightFixed coefficient)

set_option genInjectivity false in
/-- A paid area realization retaining the exact original request and mixed reading parents.

Its comparison caches both selected source observations and proves the original target pays their actual area
discrepancy. -/
structure Realization
    (request : ValueAreaRequest (owner := owner) leftFixed rightFixed coefficient paired target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank) (rightReadings : TriangleCache owner
      rightDifferential stage domains rightBank)
    (later : request.index ≤ stage) (left right : Fin 2) (different : left ≠ right) where
  /-- The retained original mixed-area request. -/ selection : ValueAreaRequest (owner := owner) leftFixed rightFixed
    coefficient paired target
  /-- The retained selection is exactly the supplied original request. -/ selection_eq : selection = request
  /-- The actual retained conjugate-linear mixed triangle readings. -/ readings : MixedReadings (owner := owner) domains
    leftDifferential rightDifferential coefficient
  /-- The retained readings are exactly the mixture of the supplied original reading banks. -/ readings_eq : readings =
    MixedReadings.ofReadings coefficient leftReadings rightReadings
  /-- The actual stage pays the original left magnitude reference. -/ leftFixedLater : leftFixed.index ≤ stage
  /-- The actual stage pays the original right magnitude reference. -/ rightFixedLater : rightFixed.index ≤ stage
  /-- The actual stage pays the retained mixed whole-edge request bank. -/ requestsLater : request.requests.index ≤
    stage
  /-- The actual cached opposite-sheet comparison on the retained mixed values. -/ comparison : RealizationComparison
    request leftReadings rightReadings left right
  /-- The original requested target pays the actual cached comparison area bound. -/ budget : comparison.areaBound ≤
    target

constructive_injectivity Realization

namespace Realization

variable {request : ValueAreaRequest (owner := owner) leftFixed rightFixed coefficient paired target}
  {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
  {rightBank : PrimitiveBank owner rightDifferential stage domains}
  {leftReadings : TriangleCache owner leftDifferential stage domains leftBank} {rightReadings : TriangleCache owner
    rightDifferential stage domains rightBank}
  {later : request.index ≤ stage} {left right : Fin 2} {different : left ≠ right}

/-- The cached source observation on the original first selected sheet. -/
@[expose] def leftSources (result : Realization request leftReadings rightReadings later left right different) :=
  result.comparison.leftSources

/-- The cached source observation on the original second selected sheet. -/
@[expose] def rightSources (result : Realization request leftReadings rightReadings later left right different) :=
  result.comparison.rightSources

/-- The cached signed area discrepancy between the two original source polygons. -/
@[expose] def residual (result : Realization request leftReadings rightReadings later left right different) :=
  result.comparison.residual

/-- The cached quantitative bound for the actual original area discrepancy. -/
@[expose] def areaBound (result : Realization request leftReadings rightReadings later left right different) :=
  result.comparison.areaBound

/-- The retained residual is the difference of the two cached original source summary areas. -/
theorem residual_eq (result : Realization request leftReadings rightReadings later left right different) :
    result.residual = result.leftSources.summary.area - result.rightSources.summary.area :=
  result.comparison.residual_eq

/-- The squared norm of the retained residual is bounded by its actual cached comparison bound. -/
theorem bounded (result : Realization request leftReadings rightReadings later left right different) :
    normSq result.residual ≤ result.areaBound :=
  result.comparison.numeric.bounded

/-- The original target bounds the squared norm of the actual retained residual. -/
theorem pay (result : Realization request leftReadings rightReadings later left right different) :
    normSq result.residual ≤ target :=
  result.bounded.trans result.budget

/-- The retained residual reads the difference of the two original source paths evaluated on the actual mixed values. -/
theorem area_readback (result : Realization request leftReadings rightReadings later left right different) :
    result.residual =
      IncrementArea.pathArea ((paired.sources left).map (fun source => source.increment
        (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient))) -
      IncrementArea.pathArea ((paired.sources right).map (fun source => source.increment
        (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient))) :=
  result.comparison.area_readback

end Realization

/-- Acquire the original source pair list and its two summaries once. Payment and both source/chart clients consume
these retained observations unchanged. -/
@[expose] def realize (request : ValueAreaRequest (owner := owner) leftFixed rightFixed coefficient paired target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank) (rightReadings : TriangleCache owner
      rightDifferential stage domains rightBank)
    (later : request.index ≤ stage) (left right : Fin 2) (different : left ≠ right) :
    Realization request leftReadings rightReadings later left right different :=
  have leftFixedLater : leftFixed.index ≤ stage :=
    (Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later))
  have rightFixedLater : rightFixed.index ≤ stage :=
    (Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later))
  have requestsLater : request.requests.index ≤ stage :=
    (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  let leftMagnitude := EdgeMagnitude.ofBank (owner := owner) leftFixed leftFixedLater leftReadings
  let rightMagnitude := EdgeMagnitude.ofBank (owner := owner) rightFixed rightFixedLater rightReadings
  let mixedMagnitude := EdgeMagnitude.mix (owner := owner) leftMagnitude rightMagnitude coefficient
  have magnitudeBound : mixedMagnitude.bound =
      EdgeMagnitude.mixBound leftFixed.bound rightFixed.bound coefficient := rfl
  have targetNonnegative : 0 ≤ RealizationError request :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by
      decide) (Data.Gaussian.Basic.Canonical.normSq_nonneg coefficient)))
      request.perEdge_positive.le
  have boundNonnegative : 0 ≤ RealizationBound leftFixed rightFixed coefficient :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (EdgeMagnitude.mixBound_nonnegative leftFixed.nonnegative rightFixed.nonnegative coefficient)
  let comparison := OppositeComparison.realize
    (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)
    paired left right (RealizationError request) (RealizationBound leftFixed rightFixed coefficient)
    targetNonnegative boundNonnegative
    (pair_errors leftReadings rightReadings paired request.requests left right different requestsLater)
    (fun source _ => by
      unfold RealizationBound
      have bounded := mixedMagnitude.source_bounded source
      rw [magnitudeBound] at bounded
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact bounded)
    (fun source _ => by
      unfold RealizationBound
      have bounded := mixedMagnitude.source_bounded source
      rw [magnitudeBound] at bounded
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact bounded)
  have weightNonnegative : 0 ≤ request.weight := request.weight_eq ▸
    weight_nonnegative leftFixed rightFixed coefficient walk
  have paid : comparison.areaBound ≤ target := by
    calc
      comparison.areaBound = 16 * (walk.edgeCount : Fraction.Rational) ^ 4 *
          RealizationError request * RealizationBound leftFixed rightFixed coefficient := comparison.areaBound_eq
      _ = request.weight * request.perEdge := by
        rw [request.weight_eq]
        unfold RealizationError RealizationBound
        ring1
      _ ≤ target := by
        rw [request.perEdge_eq]
        exact Weighted.mul_allowance_le request.positive.le weightNonnegative
  { selection := request
    selection_eq := rfl
    readings := MixedReadings.ofReadings coefficient leftReadings rightReadings
    readings_eq := rfl
    leftFixedLater := leftFixedLater
    rightFixedLater := rightFixedLater
    requestsLater := requestsLater
    comparison := comparison
    budget := paid }

/-- At a paid stage, the original mixed source paths on distinct sheets have squared area discrepancy at most the
requested target. -/
theorem accurate (request : ValueAreaRequest (owner := owner) leftFixed rightFixed coefficient paired target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank) (rightReadings : TriangleCache owner
      rightDifferential stage domains rightBank)
    (later : request.index ≤ stage) (left right : Fin 2) (different : left ≠ right) :
    normSq (IncrementArea.pathArea ((paired.sources left).map (fun source =>
        source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
          coefficient))) -
      IncrementArea.pathArea ((paired.sources right).map (fun source =>
        source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
          coefficient)))) ≤
      target := by
  let result := realize request leftReadings rightReadings later left right different
  rw [← result.area_readback]
  exact result.pay

end ValueAreaRequest

set_option genInjectivity false in
/-- A paid two-sheet word-increment request for the same conjugate-linear mixture of two differentials.

Both original differential requests use a common scaled allowance, and their maximum stage pays the mixed cancellation
bound. -/
structure ValueIncrementRequest (leftDifferential rightDifferential : Differentials.Basic.Differential genus)
    (domains : Domains owner) (coefficient : Data.Gaussian.Basic.Canonical)
    {start finish : Data.Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (sheet : Fin 2) (target : Fraction.Rational) where
  /-- The original requested target is strictly positive. -/ positive : 0 < target
  /-- The retained common allowance for the two original differential increment requests. -/ part : Fraction.Rational
  /-- The common allowance is the target divided by twice one plus the coefficient squared norm. -/ part_eq : part =
    target / (2 * (1 + normSq coefficient))
  /-- The original left differential increment request on the retained walk and sheet. -/ left :
    PairedWalk.IncrementRequest (mesh := owner.mesh) paired domains leftDifferential sheet part
  /-- The original right differential increment request on the same retained walk and sheet. -/ right :
    PairedWalk.IncrementRequest (mesh := owner.mesh) paired domains rightDifferential sheet part
  /-- The cached common stage paying all retained original requests. -/ index : Nat
  /-- The cached stage is the maximum of the original retained request stages. -/ index_eq : index = max left.index
    right.index

constructive_injectivity ValueIncrementRequest

namespace ValueIncrementRequest

variable {leftDifferential rightDifferential : Differential genus}
  {coefficient : Purelib.Data.Gaussian.Basic.Canonical}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {walk : Purelib.Polynomial.Geometry.Grid.Walks.Walk
    owner.base.bank.grid start finish}
  {paired : PairedWalk owner.mesh walk} {sheet
    : Fin 2} {target : Rational}

/-- Prepare both original differential increment requests at the common scaled allowance and retain the maximum of their
stages. -/
@[expose] def build (leftDifferential rightDifferential : Differentials.Basic.Differential genus)
    (domains : Domains owner) (coefficient : Data.Gaussian.Basic.Canonical)
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (sheet : Fin 2) (target : Fraction.Rational) (positive : 0 <
      target) :
    ValueIncrementRequest (owner := owner) leftDifferential rightDifferential domains coefficient paired sheet target :=
  let part := target / (2 * (1 + normSq coefficient))
  have partPositive : 0 < part :=
    Fraction.Order.Field.div_pos_direct positive (Data.Gaussian.Basic.Canonical.double_one_add_normSq_positive
      coefficient)
  let left := IncrementRequest.build paired domains leftDifferential sheet part partPositive
  let right := IncrementRequest.build paired domains rightDifferential sheet part partPositive
  ⟨positive, part, rfl, left, right, max left.index right.index, rfl⟩

/-- At the retained paid stage, the two opposite-sheet word increments of the original mixed readings cancel within the
requested squared-norm target. -/
theorem accurate (request : ValueIncrementRequest (owner := owner) leftDifferential rightDifferential
    domains coefficient paired sheet target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank) (rightReadings : TriangleCache owner
      rightDifferential stage domains rightBank)
    (later : request.index ≤ stage) :
    normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh
        (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient))
        (owner.edges.indexedEdges owner.vertices walk sheet) +
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh
        (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient))
        (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet))) ≤ target := by
  have leftLater : request.left.index ≤ stage :=
    (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have rightLater : request.right.index ≤ stage :=
    (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have leftBound := request.left.accurate leftReadings leftLater
  have rightBound := request.right.accurate rightReadings rightLater
  have expand (edgeList : List (OrientedEdge owner.vertices.count))
      (support : ∀ edge ∈ edgeList, edge ∈ Stokes.triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
        edge.reverse ∈ Stokes.triangleEdgeOccurrences owner.mesh.triangulation.faces) :
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh
          (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)) edgeList =
        conj (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values) edgeList) +
          coefficient * SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values)
            edgeList := by
    induction edgeList with
    | nil =>
        change (0 : Data.Gaussian.Basic.Canonical) = conj 0 + coefficient * 0
        rw [show conj (0 : Data.Gaussian.Basic.Canonical) = 0 by rfl,
          Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.add_zero]
    | cons edge rest inductionHypothesis =>
        change
          CanonicalEdgeValues.edgeValuation owner.mesh
              (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient) edge +
            SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh
              (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values coefficient)) rest =
          conj (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values edge +
            SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values) rest) +
          coefficient * (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values edge +
            SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values) rest)
        rw [EdgeMagnitude.edgeValuation_mixValues (owner := owner) (leftValues := leftReadings.values)
            (rightValues := rightReadings.values) coefficient (support edge List.mem_cons_self),
          inductionHypothesis (fun next member => support next (List.mem_cons_of_mem _ member)),
            Data.Gaussian.Basic.Canonical.conj_add]
        rw [Data.Gaussian.Basic.conj_eq_canonical]
        ring1
  have leftSupport : ∀ edge ∈ owner.edges.indexedEdges owner.vertices walk sheet,
      edge ∈ Stokes.triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
        edge.reverse ∈ Stokes.triangleEdgeOccurrences owner.mesh.triangulation.faces :=
    fun edge member => SkeletonFaceAssignments.indexedWalk_supported owner.mesh walk sheet edge member
  have rightSupport : ∀ edge ∈ owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet),
      edge ∈ Stokes.triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
        edge.reverse ∈ Stokes.triangleEdgeOccurrences owner.mesh.triangulation.faces :=
    fun edge member => SkeletonFaceAssignments.indexedWalk_supported owner.mesh walk (BranchCutLifts.otherSheet sheet)
      edge member
  rw [expand _ leftSupport, expand _ rightSupport]
  have combine :
      (conj (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values)
        (owner.edges.indexedEdges owner.vertices walk sheet)) +
          coefficient * SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values)
            (owner.edges.indexedEdges owner.vertices walk sheet)) +
        (conj (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values)
          (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet))) +
          coefficient * SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values)
            (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet))) =
      conj (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values)
        (owner.edges.indexedEdges owner.vertices walk sheet) +
          SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values)
            (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet))) +
        coefficient * (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values)
          (owner.edges.indexedEdges owner.vertices walk sheet) +
          SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values)
            (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet))) := by
    rw [Data.Gaussian.Basic.Canonical.conj_add]
    ring1
  rw [combine]
  have estimate := EdgeMagnitude.normSq_conj_add_mul
    (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values)
      (owner.edges.indexedEdges owner.vertices walk sheet) +
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values)
        (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet)))
    (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values)
      (owner.edges.indexedEdges owner.vertices walk sheet) +
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values)
        (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet)))
    coefficient
  rw [Data.Gaussian.Basic.conj_eq_canonical] at estimate
  simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  refine estimate.trans ?_
  have inner : normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values)
    (owner.edges.indexedEdges owner.vertices walk sheet) +
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh leftReadings.values)
        (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet))) +
      normSq coefficient * normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh
        rightReadings.values) (owner.edges.indexedEdges owner.vertices walk sheet) +
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.mesh rightReadings.values)
          (owner.edges.indexedEdges owner.vertices walk (BranchCutLifts.otherSheet sheet))) ≤
      request.part + normSq coefficient * request.part :=
    Fraction.Order.Arithmetic.add_le_add_direct
      (by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using leftBound)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (by simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] using rightBound)
        (Data.Gaussian.Basic.Canonical.normSq_nonneg coefficient))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inner (by
      decide : (0 : Fraction.Rational) ≤ 2)
  have equal : 2 * (request.part + normSq coefficient * request.part) = target := by
    have nonvanishing : 2 * (1 + normSq coefficient) ≠ 0 :=
      (Data.Gaussian.Basic.Canonical.double_one_add_normSq_positive coefficient).ne'
    calc
      2 * (request.part + normSq coefficient * request.part) =
          2 * (1 + normSq coefficient) * request.part := by ring1
      _ = target := by
        rw [request.part_eq, Fraction.Field.mul_comm,
          Fraction.Field.div_mul_cancel_of_ne _ _ nonvanishing]
  exact scaled.trans_eq equal

end ValueIncrementRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWalkAreaRequests
