module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Paths.PreparedPrimitivePaths
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
public import Purelib.Riemann.Normalization.ContinuedInverseRootRequests
import Init.Data.Nat.Basic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Reciprocal root agreement across retained source parents

The source point is acquired once in its already retained primitive patch.
Both reciprocal Newton streams are compared with one reading of the actual
source root. Independent parent models and reading indices are permitted.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.ContinuedInverseRoot

open Purelib.Riemann.Normalization.ContinuedInverseRootRequests

open Purelib.Riemann.Normalization.OwnerSeededInverseRoot

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel RootPoint)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Paths
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell} {parameter :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

universe u

set_option genInjectivity false in
/-- A retained source sample, geometric location witnesses and exact error scale.

The sample and its original point, interval and containment propositions remain indexed by the caller-supplied
mathematical data. -/
structure SourceAtData (Sample : Type u) (pointEq inside contained : Prop) (scaleSpec :
  InverseRootPolynomial.Coordinate) where
  /-- The original parent parametrization reaches exactly the retained source location. -/ point_eq : pointEq
  /-- The retained original parameter lies in the rational unit interval. -/ inside : inside
  /-- The original source location lies in the retained patch neighborhood. -/ contained : contained
  /-- The retained root sample acquired once in the original source neighborhood. -/ sample : Sample
  /-- The cached scalar multiplying the geometric source-root residual. -/ scale : InverseRootPolynomial.Coordinate
  /-- The cached scale equals the specified original source and reciprocal inverse bound product. -/ scale_eq : scale =
    scaleSpec

constructive_injectivity SourceAtData

/-- The original parent patch sample at the location of a retained reciprocal root point, with its weighted
inverse-error scale. -/
abbrev SourceAt (_root : UniformReciprocalRootChannels.RootPoint model parameter) (location :
  InverseRootPolynomial.Gaussian) :=
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAtData (ContinuedNeighborhood.Point
    (patch.neighborhood count) location)
    (parent.edge.point parameter = location) (0 ≤ parameter ∧ parameter ≤ 1)
    ((patch.neighborhood count).box.Contains location)
    (6 * Data.Gaussian.Norm.Basic.normSq (ReciprocalRootNames.factor genus location * curve.polynomial.eval
      location) *
      (data.source.bound + 1 / 16) * data.inverseUpper)

namespace SourceAt

/-- Acquire the original source-neighborhood root sample at the retained reciprocal point and cache its location and
error scale. -/
@[expose] def build (root : UniformReciprocalRootChannels.RootPoint model parameter) (location :
  InverseRootPolynomial.Gaussian) (same : parent.edge.point parameter = location) :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAt root location := by
  have inside : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans root.between.1, root.between.2.trans edge.right.inside.2⟩
  have contained : (patch.neighborhood count).box.Contains location := same ▸
    PreparedPrimitivePaths.point_inside_of_endpoints parent (patch.neighborhood count).box
      (patch.start_inside count) data.finishInside inside
  let sample := ContinuedNeighborhood.Point.acquire (patch.neighborhood count) location contained
  exact ⟨same, inside, contained, sample,
    6 * Data.Gaussian.Norm.Basic.normSq (ReciprocalRootNames.factor genus location * curve.polynomial.eval
      location) *
      (data.source.bound + 1 / 16) * data.inverseUpper, rfl⟩

variable {root : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootPoint model parameter}
  {location : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

/-- The original parent root name agrees operationally with the retained source patch sample. -/
@[expose] def equivalent (source : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAt root
  location) :
    Gaussian.Equivalence.NamedEquivalent (parent.edge.rootName parameter source.inside)
      source.sample.certificate.value.name :=
  patch.point_equivalent_at count parameter source.inside source.point_eq source.contained source.sample

/-- The cached source-to-reciprocal root error scale is nonnegative. -/
theorem scale_nonnegative (source : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAt root
  location) : 0 ≤ source.scale := by
  rw [source.scale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg _))
      (add_nonneg data.source.bound_nonnegative (by decide))) data.inverseUpper_positive.le

/-- The reciprocal root and the retained source inverse share their sign through the exact seed transport, at every
later Newton stage. -/
theorem source_error (source : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAt root location)
  (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (root.channel.samples.sample index -
      (ReciprocalRootNames.factor genus location * curve.polynomial.eval location) *
        ((patch.neighborhood count).base.refine (4 + index)).value.eval location) ≤ Geometric.Basic.quarterRadius
          source.scale index := by
  let weight := ReciprocalRootNames.factor genus location * curve.polynomial.eval location
  have identity : root.channel.samples.sample index - weight * (data.source.refine (2 + index)).value.eval location =
      -(weight * ((data.source.refine (2 + index)).value.eval location -
        ReciprocalInverseModelOverlap.value curve (cell.model.refine (2 + index)) location)) := by
    rw [root.sample_eq, source.point_eq, ← ReciprocalRootNames.factor_identity curve location
      (source.point_eq ▸ PreparedExteriorReciprocal.parent_point_nonzero data.boundary source.inside)]
    dsimp only [weight, ReciprocalInverseModelOverlap.value]
    ring1
  have estimate := root.source_distance (2 + index)
  rw [source.point_eq] at estimate
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct estimate
    (Data.Gaussian.Norm.Basic.normSq_nonneg weight)
  have shifted : (data.source.refine (2 + index)).value.eval location =
      ((patch.neighborhood count).base.refine (4 + index)).value.eval location := by
    rw [data.source_refine_eq, show 2 + (2 + index) = 4 + index by omega0]
  rw [← shifted, identity, Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul]
  exact (bounded.trans_eq (by
      rw [Geometric.Basic.quarterRadius_eq_mul_pow, source.scale_eq];
      dsimp only [weight];
      ring1)).trans
    (quarterRadius_antitone source.scale_nonnegative (Nat.le_add_left index 2))

end SourceAt

variable {otherCount : Nat} {otherDifferential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve otherDifferential}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {otherEdge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {otherCell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell otherData otherEdge} {otherModel :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel otherCell} {otherParameter :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {first : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootPoint model parameter} {last
    : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootPoint otherModel otherParameter}
    {location : Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}

universe v

set_option genInjectivity false in
/-- Two retained source samples with their operational root comparison and exact common scalar weight.

The source samples retain their separate types and naming maps; the weight and its squared norm are cached with defining
equalities. -/
structure SourceJoinData (First : Type u) (Last : Type v)
    (firstName : First → Gaussian.Name.Basic.Named) (lastName : Last → Gaussian.Name.Basic.Named)
    (weightSpec : InverseRootPolynomial.Gaussian) where
  /-- The retained first source sample and its exact location witnesses. -/ first : First
  /-- The retained second source sample and its exact location witnesses. -/ last : Last
  /-- The two retained source samples name operationally equivalent roots. -/ equivalent :
    Gaussian.Equivalence.NamedEquivalent (firstName first) (lastName last)
  /-- The cached common reciprocal scaling factor times the original radicand value. -/ weight :
    InverseRootPolynomial.Gaussian
  /-- The cached scalar is exactly the supplied common source weight. -/ weight_eq : weight = weightSpec
  /-- The cached squared norm of the common source weight. -/ weightNorm : InverseRootPolynomial.Coordinate
  /-- The cached norm equals the squared norm of the retained weight. -/ weightNorm_eq : weightNorm =
    Data.Gaussian.Norm.Basic.normSq weight

constructive_injectivity SourceJoinData

/-- Two retained reciprocal root occurrences connected through their original source samples at one exact location. -/
abbrev SourceJoin (first : UniformReciprocalRootChannels.RootPoint model parameter) (last :
  UniformReciprocalRootChannels.RootPoint otherModel otherParameter) (location : InverseRootPolynomial.Gaussian) :=
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceJoinData
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAt first location)
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAt last location)
    (fun source => source.sample.certificate.value.name) (fun source => source.sample.certificate.value.name)
    (ReciprocalRootNames.factor genus location * curve.polynomial.eval location)

namespace SourceJoin

/-- Retain both original source samples and transport the supplied parent-root comparison through their exact sample
equivalences. -/
@[expose] def build (first : UniformReciprocalRootChannels.RootPoint model parameter) (last :
  UniformReciprocalRootChannels.RootPoint otherModel otherParameter)
    (location : InverseRootPolynomial.Gaussian) (firstEq : parent.edge.point parameter = location) (lastEq :
      otherParent.edge.point otherParameter = location)
    (roots : Gaussian.Equivalence.NamedEquivalent
      (parent.edge.rootName parameter ⟨edge.left.inside.1.trans first.between.1, first.between.2.trans
        edge.right.inside.2⟩)
      (otherParent.edge.rootName otherParameter ⟨otherEdge.left.inside.1.trans last.between.1, last.between.2.trans
        otherEdge.right.inside.2⟩)) :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceJoin first last location :=
  let before := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAt.build first location firstEq
  let after := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceAt.build last location lastEq
  let weight := ReciprocalRootNames.factor genus location * curve.polynomial.eval location
  ⟨before, after, before.equivalent.symm.trans (roots.trans after.equivalent), weight, rfl,
    Data.Gaussian.Norm.Basic.normSq weight, rfl⟩

/-- Two equal pairs of quarter budgets combine to the original rational budget. -/
private theorem quarter_sum (value : InverseRootPolynomial.Coordinate) : 2 * (value / 4 + value / 4) = value := by
  rw [show 2 * (value / 4 + value / 4) = value / 4 * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- Two equal pairs of quarter budgets combine to the original rational budget. -/
theorem quarter_sum_for_join (value : InverseRootPolynomial.Coordinate) : 2 * (value / 4 + value / 4) = value := by
  rw [show 2 * (value / 4 + value / 4) = value / 4 * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- All requested comparisons reuse the two source owners and their sheet equivalence. A single canonical source reading
is used on both sides. -/
@[expose] def rootEquivalent (joined : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceJoin first
  last location) :
    Gaussian.Equivalence.NamedEquivalent first.channel.certificate.value.name last.channel.certificate.value.name := by
  let left := first.channel.samples.approximation first.channel.small first.channel.inside
  let right := last.channel.samples.approximation last.channel.small last.channel.inside
  have weightNonnegative : 0 ≤ joined.weightNorm := by
    rw [joined.weightNorm_eq];
    exact Data.Gaussian.Norm.Basic.normSq_nonneg _
  let compared : Gaussian.Equivalence.Equivalent left right := {
    compare := fun leftFloor rightFloor target positive => by
      let budget := (target / 4) / 4
      have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
          decide : (0 : InverseRootPolynomial.Coordinate) < 4)
      have budgetPositive : 0 < budget := Fraction.Order.Field.div_pos_direct quarterPositive (by decide)
      let inverseTarget := budget / (joined.weightNorm + 1)
      have shiftedPositive : 0 < joined.weightNorm + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
        weightNonnegative (by decide)
      have inversePositive : 0 < inverseTarget := Fraction.Order.Field.div_pos_direct budgetPositive shiftedPositive
      let before := InverseRequest.build joined.first.sample joined.first.contained
        joined.first.sample.certificate (NamedEquivalent.refl _) inverseTarget inversePositive leftFloor
      let after := InverseRequest.build joined.last.sample joined.last.contained
        joined.first.sample.certificate joined.equivalent inverseTarget inversePositive rightFloor
      let leftIndex := Search.firstQuarterBelow joined.first.scale (max leftFloor before.index) budget
      let rightIndex := Search.firstQuarterBelow joined.last.scale (max rightFloor after.index) budget
      have leftStart := Search.firstQuarterBelow_ge joined.first.scale (max leftFloor before.index) budget
      have rightStart := Search.firstQuarterBelow_ge joined.last.scale (max rightFloor after.index) budget
      let readingIndex := max before.observation.comparison.leftIndex after.observation.comparison.leftIndex
      let reading := Data.Gaussian.Field.inv ((Sampling.approximation
        joined.first.sample.certificate.value.name).sample readingIndex)
      refine ⟨leftIndex, rightIndex, (Data.Nat.Order.le_max_left _ _).trans leftStart, (Data.Nat.Order.le_max_left _
        _).trans rightStart, ?_⟩
      intro leftStage rightStage leftLater rightLater
      have firstInverse := before.accurate (index := 4 + leftStage) (rootIndex := readingIndex)
        (((Data.Nat.Order.le_max_right _ _).trans leftStart).trans (leftLater.trans (Nat.le_add_left _ _)))
          (Data.Nat.Order.le_max_left _ _)
      have lastInverse := after.accurate (index := 4 + rightStage) (rootIndex := readingIndex)
        (((Data.Nat.Order.le_max_right _ _).trans rightStart).trans (rightLater.trans (Nat.le_add_left _ _)))
          (Data.Nat.Order.le_max_right _ _)
      let rootReading := (Sampling.approximation joined.first.sample.certificate.value.name).sample readingIndex
      have inverseEq : Data.Gaussian.Basic.Canonical.inv rootReading = Data.Gaussian.Field.inv rootReading :=
        by
        change rootReading⁻¹ = Data.Gaussian.Field.inv rootReading
        exact Data.Gaussian.Field.inv_eq rootReading
      rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical, inverseEq] at firstInverse lastInverse
      simp only [SeededNeighborhood.refine] at firstInverse lastInverse
      have weightPaid {value : InverseRootPolynomial.Gaussian} (close : Data.Gaussian.Norm.Basic.normSq value <
        inverseTarget) : Data.Gaussian.Norm.Basic.normSq (joined.weight * value) < budget := by
        rw [Data.Gaussian.Norm.Basic.normSq_mul, ← joined.weightNorm_eq]
        calc
          _ ≤ (joined.weightNorm + 1) * Data.Gaussian.Norm.Basic.normSq value :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (le_add_of_nonneg_right (by decide)) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
          _ < (joined.weightNorm + 1) * inverseTarget := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            shiftedPositive close
          _ = budget := by
            rw [Fraction.Field.mul_comm];
            exact Fraction.Field.div_mul_cancel_of_ne _ _ shiftedPositive.ne'
      have firstError : Data.Gaussian.Norm.Basic.normSq (left.sample leftStage - joined.weight * reading) <
        target / 4 := by
        have geometric := (joined.first.source_error leftStage).trans_lt
          ((quarterRadius_antitone joined.first.scale_nonnegative leftLater).trans_lt
            (Search.firstQuarterBelow_accurate _ joined.first.scale_nonnegative _ _ budgetPositive))
        rw [← joined.weight_eq] at geometric
        have inverseError := weightPaid
          (value := ((patch.neighborhood count).base.refine (4 + leftStage)).value.eval location - reading)
          (by simpa only [SeededNeighborhood.refine] using firstInverse)
        have identity : left.sample leftStage - joined.weight * reading =
            (left.sample leftStage - joined.weight * ((patch.neighborhood count).base.refine (4 + leftStage)).value.eval
              location) +
              joined.weight * (((patch.neighborhood count).base.refine (4 + leftStage)).value.eval location - reading)
                := by ring1
        rw [identity]
        exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
          ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
              decide : (0 : InverseRootPolynomial.Coordinate) < 2)
            (Fraction.Order.Arithmetic.add_lt_add_direct geometric inverseError)).trans_eq
              (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceJoin.quarter_sum_for_join (target
              / 4)))
      have lastError : Data.Gaussian.Norm.Basic.normSq (right.sample rightStage - joined.weight * reading) <
        target / 4 := by
        have geometric := (joined.last.source_error rightStage).trans_lt
          ((quarterRadius_antitone joined.last.scale_nonnegative rightLater).trans_lt
            (Search.firstQuarterBelow_accurate _ joined.last.scale_nonnegative _ _ budgetPositive))
        rw [← joined.weight_eq] at geometric
        have inverseError := weightPaid
          (value := ((otherPatch.neighborhood otherCount).base.refine (4 + rightStage)).value.eval location - reading)
          (by simpa only [SeededNeighborhood.refine] using lastInverse)
        have identity : right.sample rightStage - joined.weight * reading =
            (right.sample rightStage - joined.weight * ((otherPatch.neighborhood otherCount).base.refine (4 +
              rightStage)).value.eval location) +
              joined.weight * (((otherPatch.neighborhood otherCount).base.refine (4 + rightStage)).value.eval location -
                reading) := by ring1
        rw [identity]
        exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
          ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
              decide : (0 : InverseRootPolynomial.Coordinate) < 2)
            (Fraction.Order.Arithmetic.add_lt_add_direct geometric inverseError)).trans_eq
              (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceJoin.quarter_sum_for_join (target
              / 4)))
      rw [show left.sample leftStage - right.sample rightStage =
        (left.sample leftStage - joined.weight * reading) - (right.sample rightStage - joined.weight * reading) by
          ring1]
      have triangle := Data.Gaussian.Norm.Bounds.normSq_sub_le_two
        (left.sample leftStage - joined.weight * reading) (right.sample rightStage - joined.weight * reading)
      simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at triangle firstError lastError
      rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical]
      exact triangle.trans_lt
        ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
            decide : (0 : InverseRootPolynomial.Coordinate) < 2)
          (Fraction.Order.Arithmetic.add_lt_add_direct firstError lastError)).trans_eq
            (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins.SourceJoin.quarter_sum_for_join target)) }
  exact first.channel.samples_equivalent.symm.trans (compared.trans last.channel.samples_equivalent)

end SourceJoin
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
