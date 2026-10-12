module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib

public section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families (Domains MagnitudeBank PrimitiveBank
  TriangleCache Source Sources Nonloop)

/-!
# Value-parameterized paired-walk source sums

`FramedPuncturedGrid.PairedWalkRequest` bounds the source increments of one
differential. A mixed value `Purelib.Data.Gaussian.Basic.Canonical.conj left + coefficient * right` has no
differential, but its source sum is the conjugate-linear combination of the
two sides' source sums. This module combines the two requests and pays the
combined target, so every aggregate consumer can run on a mixed value.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedWalk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Order.Arithmetic (mul_nonneg_direct mul_le_mul_of_nonneg_left_direct
  add_le_add_direct add_lt_add_right_direct add_le_add_right_direct)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}
  {domains : Domains owner}

/-- The source-increment sum of a mixed value is the conjugate-linear
combination of the two sides' source-increment sums. -/
private theorem sum_increment_mix (sources : Sources owner)
    (leftValues rightValues : Fin owner.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues
      3) (coefficient : Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.map (fun source =>
      source.increment (EdgeMagnitude.mixValues (owner := owner) leftValues rightValues coefficient))) =
      Gaussian.Basic.Canonical.conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.map (fun source =>
        source.increment leftValues))) +
        coefficient * Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.map (fun source => source.increment
          rightValues)) := by
  induction sources with
  | nil =>
      change (0 : Gaussian.Basic.Canonical) = Gaussian.Basic.Canonical.conj 0 + coefficient * 0
      rw [show Gaussian.Basic.Canonical.conj (0 : Gaussian.Basic.Canonical) = 0 from rfl,
        Gaussian.Basic.mul_zero, Gaussian.Basic.add_zero]
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.map_cons, List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        EdgeMagnitude.source_increment_mixValues (owner := owner), inductionHypothesis,
          Gaussian.Basic.Canonical.conj_add]
      rw [Gaussian.Basic.conj_eq_canonical]
      ring1

/-- The strict norm bound for a conjugate-linear combination of two strictly
bounded terms. -/
private theorem normSq_conj_add_mul_lt {left right coefficient : Gaussian.Basic.Canonical} {leftBound rightBound :
  Fraction.Rational}
    (first : normSq left < leftBound) (second : normSq right < rightBound) :
    normSq (Gaussian.Basic.Canonical.conj left + coefficient * right) <
      2 * (leftBound + normSq coefficient * rightBound) := by
  have estimate : normSq (Gaussian.Basic.Canonical.conj left + coefficient * right) ≤
      2 * (normSq left + normSq coefficient * normSq right) := by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical,
      Gaussian.Basic.conj_eq_canonical] using
      EdgeMagnitude.normSq_conj_add_mul left right coefficient
  refine estimate.trans_lt ?_
  have firstStep := Fraction.Order.Arithmetic.add_lt_add_right_direct first (normSq coefficient * normSq right)
  have secondStep := Fraction.Order.Arithmetic.add_le_add_right_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct second.le (Gaussian.Basic.Canonical.normSq_nonneg
      coefficient)) leftBound
  have step : normSq left + normSq coefficient * normSq right <
      leftBound + normSq coefficient * rightBound := by
    calc
      normSq left + normSq coefficient * normSq right <
          leftBound + normSq coefficient * normSq right := firstStep
      _ = normSq coefficient * normSq right + leftBound :=
        Fraction.Field.add_comm _ _
      _ ≤ normSq coefficient * rightBound + leftBound := secondStep
      _ = leftBound + normSq coefficient * rightBound :=
        Fraction.Field.add_comm _ _
  exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) step

set_option genInjectivity false in
/-- The mixed paired-walk source request. It caches both single-differential
requests at one shared target and exposes their common source list. -/
structure ValuePairedWalkRequest (leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential
  genus)
    (domains : Domains owner)
    (coefficient : Gaussian.Basic.Canonical) {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk
      owner.base.bank.grid start finish)
    (target : Fraction.Rational) where
  /-- The requested mixed source-sum target is positive. -/ positive : 0 < target
  /-- The retained common allowance for the two original differential requests. -/ part : Fraction.Rational
  /-- The allowance is the original target divided by its conjugate-linear norm scale. -/ part_eq : part = target / (2 *
    (1 + normSq coefficient))
  /-- The actual left-differential request on the original paired walk. -/ left :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := owner.mesh) domains
    leftDifferential walk part
  /-- The actual right-differential request on the same original paired walk. -/ right :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := owner.mesh) domains
    rightDifferential walk part
  /-- Both retained requests use exactly the same original source list. -/ sources_eq : left.sources = right.sources
  /-- The cached common sufficient request stage. -/ index : Nat
  /-- The common stage is the maximum of the retained left and right indices. -/ index_eq : index = max left.index
    right.index

constructive_injectivity ValuePairedWalkRequest

namespace ValuePairedWalkRequest

variable {leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {coefficient :
  Gaussian.Basic.Canonical}
  {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk owner.base.bank.grid start finish} {target
    : Fraction.Rational}

/-- Construct one original paired walk and reuse it for both differential requests at the paid common allowance. -/
@[expose] def build (leftDifferential rightDifferential : Hyperelliptic.Differentials.Basic.Differential genus)
    (domains : Domains owner) (coefficient : Gaussian.Basic.Canonical)
    (walk : Geometry.Grid.Walks.Walk owner.base.bank.grid start finish) (target : Fraction.Rational) (positive : 0 <
      target) :
    ValuePairedWalkRequest (owner := owner) leftDifferential rightDifferential domains coefficient
      walk target :=
  let part := target / (2 * (1 + normSq coefficient))
  have partPositive : 0 < part :=
    Fraction.Order.Field.div_pos_direct positive (Data.Gaussian.Basic.Canonical.double_one_add_normSq_positive
      coefficient)
  let paired := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.build owner.mesh walk
  let left := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest.ofPaired paired domains
    leftDifferential part partPositive
  let right := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest.ofPaired paired domains
    rightDifferential part partPositive
  ⟨positive, part, rfl, left, right, rfl, max left.index right.index, rfl⟩

/-- The conjugate-linear combination of the actual original source increments meets the retained whole target at a
sufficient shared stage. -/
theorem accurate (request : ValuePairedWalkRequest (owner := owner) leftDifferential rightDifferential
    domains coefficient walk target)
    {stage : Nat} {leftBank : PrimitiveBank owner leftDifferential stage domains}
    {rightBank : PrimitiveBank owner rightDifferential stage domains}
    (leftReadings : TriangleCache owner leftDifferential stage domains leftBank) (rightReadings : TriangleCache owner
      rightDifferential stage domains rightBank)
    (later : request.index ≤ stage) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.left.sources.map (fun source =>
      source.increment (EdgeMagnitude.mixValues (owner := owner) leftReadings.values rightReadings.values
        coefficient)))) < target := by
  have leftLater : request.left.index ≤ stage :=
    (Data.Nat.Order.le_max_left _ _).trans (request.index_eq ▸ later)
  have rightLater : request.right.index ≤ stage :=
    (Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸ later)
  have leftBound : normSq (gaussianSum (request.left.sources.map
      (fun source => source.increment leftReadings.values))) < request.part := by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      request.left.accurate leftReadings leftLater
  have rightBound : normSq (gaussianSum (request.right.sources.map
      (fun source => source.increment rightReadings.values))) < request.part := by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
      request.right.accurate rightReadings rightLater
  rw [← request.sources_eq] at rightBound
  rw [sum_increment_mix]
  have estimate := normSq_conj_add_mul_lt (coefficient := coefficient) leftBound rightBound
  have equal : 2 * (request.part + normSq coefficient * request.part) = target := by
    have nonvanishing : 2 * (1 + normSq coefficient) ≠ 0 :=
      (Data.Gaussian.Basic.Canonical.double_one_add_normSq_positive coefficient).ne'
    calc
      2 * (request.part + normSq coefficient * request.part) =
          2 * (1 + normSq coefficient) * request.part := by ring1
      _ = target := by
        rw [request.part_eq, Fraction.Field.mul_comm,
          Fraction.Field.div_mul_cancel_of_ne _ _ nonvanishing]
  exact estimate.trans_eq equal

end ValuePairedWalkRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValuePairedWalk
