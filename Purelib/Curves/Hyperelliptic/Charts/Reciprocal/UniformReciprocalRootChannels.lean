module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInverseModelOverlap
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
public import Purelib.Riemann.Normalization.InverseModelRootChannels
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Gaussian.Norm

public section

/-!
# Operational roots of the retained reciprocal cells

Two initial Newton steps supply a root channel at every point of a cell's
actual inverse arc. The small model is shared by its endpoint channels.
At a common parameter, the existing comparison with the retained source
model proves that both channels select the same sheet. The comparison pays
independent reading indices and does not identify separately prepared paths.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Approximation.Rational.Geometric.Basic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.InverseModelRootChannels

open Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseModelRootChannels (RootChannel)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Equivalence (Equivalent NamedEquivalent)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Data patch count}
  {edge : ParameterEdge}

set_option genInjectivity false in
/-- Cache the two preparation steps once for both endpoints of this cell.

The model cache is exactly refinement two of the supplied cell, with its certified one-over-256 residual ceiling. -/
structure RootModel (cell : Cell data edge) where
  /-- The cached twice-refined original reciprocal cell model. -/ model : Model
    (HyperellipticReciprocal.polynomial curve) (data.box edge.left.parameter)
  /-- The retained model is exactly refinement two of the original cell model. -/ model_eq : model = cell.model.refine 2
  /-- The cached root model has squared residual bound at most one over 256. -/ small : model.bound ≤ 1 / 256

constructive_injectivity RootModel

namespace RootModel

/-- Cache the two preparation refinements of the original cell model with their certified residual bound. -/
@[expose] def build (cell : Cell data edge) :
  RootModel cell :=
  ⟨cell.model.refine 2, rfl, by
    rw [Model.refine_bound, quarterRadius_eq_mul_pow]
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct cell.model.bound_small
      (by decide +kernel : (0 : Coordinate) ≤ (1 / 4) ^ 2)).trans_eq (by decide +kernel)⟩

/-- Refining an original inverse model by a sum equals the corresponding successive refinements. -/
private theorem refine_add {polynomial : Polynomial} {box : Rational.Box}
    (model : Model polynomial box) (first last : Nat) :
    model.refine (first + last) = (model.refine first).refine last := by
  induction last with
  | zero => rfl
  | succ last ih => rw [Nat.add_succ, Model.refine, Model.refine, ih]

/-- Every later retained root-model refinement is the original cell refinement at the index shifted by two. -/
theorem refine_eq {cell : Cell data edge} (prepared :
  RootModel cell) (index : Nat) :
    prepared.model.refine index = cell.model.refine (2 + index) := by
  rw [prepared.model_eq, ← refine_add]

end RootModel

variable {cell : Cell data edge}

set_option genInjectivity false in
/-- A retained root channel at an original parameter inside the same reciprocal cell.

The interval witness and original root channel share the supplied model, parameter and retained source edge. -/
structure RootPoint (prepared : RootModel cell)
  (parameter : Coordinate) where
  /-- The original source parameter lies between the retained cell endpoints. -/ between : edge.left.parameter ≤
    parameter ∧ parameter ≤ edge.right.parameter
  /-- The original reciprocal root channel built from the retained prepared cell model. -/ channel :
    RootChannel prepared.model (parent.edge.point parameter)⁻¹

constructive_injectivity RootPoint

namespace RootPoint

/-- Construct the retained root channel at an original contained source parameter using the same prepared reciprocal
model. -/
@[expose] def build (prepared : RootModel cell)
  (parameter : Coordinate)
    (between : edge.left.parameter ≤ parameter ∧ parameter ≤ edge.right.parameter) :
      RootPoint prepared parameter :=
  ⟨between, RootChannel.build prepared.model prepared.small _ (cell.contains parameter between)⟩

variable {prepared : RootModel cell}
  {parameter : Coordinate}

/-- Each retained root-channel reading equals the original reciprocal radicand times its shifted original inverse-model
evaluation. -/
theorem sample_eq (point : RootPoint prepared
  parameter) (index : Nat) :
    point.channel.samples.sample index = (HyperellipticReciprocal.polynomial curve).eval (parent.edge.point parameter)⁻¹
      *
      (cell.model.refine (2 + index)).value.eval (parent.edge.point parameter)⁻¹ := by
  rw [point.channel.samples.sample_eq, prepared.refine_eq]

/-- The original coefficient and shared-source bounds combined into the root-channel geometric comparison scale. -/
private def scale (data : Data patch count) (parameter : Coordinate) :
  Coordinate :=
  24 * Basic.normSq (ReciprocalRootNames.factor genus (parent.edge.point parameter) *
    curve.polynomial.eval (parent.edge.point parameter)) *
    (data.source.bound + 1 / 16) * data.inverseUpper

/-- The retained original root-channel comparison scale is nonnegative. -/
private theorem scale_nonnegative (data : Data patch count) (parameter :
  Coordinate) : 0 ≤
  scale data parameter :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide) (Basic.normSq_nonneg _))
      (add_nonneg data.source.bound_nonnegative (by decide))) data.inverseUpper_positive.le

/-- The retained source and reciprocal inverse models satisfy the explicit shared geometric discrepancy bound. -/
theorem source_distance (point : RootPoint prepared
  parameter) (index : Nat) :
    Basic.normSq ((data.source.refine index).value.eval (parent.edge.point parameter) -
      ReciprocalInverseModelOverlap.value curve (cell.model.refine index) (parent.edge.point parameter)) ≤
      6 * (data.source.bound + 1 / 16) * data.inverseUpper * ((1 / 4 : Coordinate) ^ index) := by
  have estimate := cell.distance_le index parameter point.between
  have bound : cell.model.bound = 1 / 16 := by rw [cell.model_eq]; rfl
  rw [Model.refine_bound, Model.refine_bound, bound] at estimate
  exact estimate.trans_eq (by simp only [quarterRadius_eq_mul_pow]; ring1)

variable {otherEdge : ParameterEdge} {otherCell :
  Cell data otherEdge} {otherModel :
  RootModel otherCell}

/-- Synchronized readings of the two original overlapping root channels satisfy the retained geometric comparison bound.
-/
private theorem same_index (first : RootPoint
  prepared parameter) (last : RootPoint otherModel
  parameter) (index : Nat) :
    Basic.normSq (first.channel.samples.sample index - last.channel.samples.sample index) ≤
      quarterRadius
      (scale data parameter)
      index := by
  let source := (data.source.refine (2 + index)).value.eval (parent.edge.point parameter)
  let left := ReciprocalInverseModelOverlap.value curve (cell.model.refine (2 + index)) (parent.edge.point parameter)
  let right := ReciprocalInverseModelOverlap.value curve (otherCell.model.refine (2 + index)) (parent.edge.point
    parameter)
  let weight := ReciprocalRootNames.factor genus (parent.edge.point parameter) * curve.polynomial.eval
    (parent.edge.point parameter)
  have inside : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans first.between.1, first.between.2.trans edge.right.inside.2⟩
  have identity : first.channel.samples.sample index - last.channel.samples.sample index = weight * (left - right) := by
    rw [first.sample_eq, last.sample_eq, ← ReciprocalRootNames.factor_identity curve _
      (PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside)]
    dsimp only [weight, left, right, ReciprocalInverseModelOverlap.value]
    ring1
  have estimate : Basic.normSq (left - right) ≤ 2 *
      (Basic.normSq (source - left) + Basic.normSq (source -
        right)) := by
    rw [show left - right = (source - right) - (source - left) by ring1]
    exact (Bounds.normSq_sub_le_two _ _).trans_eq (by ring1)
  have bounded := (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (estimate.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (first.source_distance (2 + index)) (last.source_distance (2 + index))) (by decide)))
    (Basic.normSq_nonneg weight))
  rw [identity, Basic.normSq_mul]
  exact (bounded.trans_eq (by
      dsimp only [weight];
      rw [quarterRadius_eq_mul_pow];
      unfold scale;
      ring1)).trans
    (quarterRadius_antitone
      (scale_nonnegative data parameter)
      (Nat.le_add_left index 2))

/-- The original coefficient and shared-source bounds combined into the root-channel geometric comparison scale. -/
@[expose] def comparisonScale (data : Data patch count) (parameter :
  Coordinate) : Coordinate :=
  24 * Basic.normSq (ReciprocalRootNames.factor genus (parent.edge.point parameter) *
    curve.polynomial.eval (parent.edge.point parameter)) *
    (data.source.bound + 1 / 16) * data.inverseUpper

/-- The retained original root-channel comparison scale is nonnegative. -/
theorem comparisonScale_nonnegative (data : Data patch count) (parameter :
  Coordinate) : 0 ≤
  comparisonScale data parameter :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide) (Basic.normSq_nonneg _))
      (add_nonneg data.source.bound_nonnegative (by decide))) data.inverseUpper_positive.le

/-- Synchronized readings of the two original overlapping root channels satisfy the retained geometric comparison bound.
-/
theorem sameIndexBound (first : RootPoint prepared
  parameter) (last : RootPoint otherModel
  parameter) (index : Nat) :
    Basic.normSq (first.channel.samples.sample index - last.channel.samples.sample index) ≤
      quarterRadius
      (comparisonScale data
      parameter) index := by
  let source := (data.source.refine (2 + index)).value.eval (parent.edge.point parameter)
  let left := ReciprocalInverseModelOverlap.value curve (cell.model.refine (2 + index)) (parent.edge.point parameter)
  let right := ReciprocalInverseModelOverlap.value curve (otherCell.model.refine (2 + index)) (parent.edge.point
    parameter)
  let weight := ReciprocalRootNames.factor genus (parent.edge.point parameter) * curve.polynomial.eval
    (parent.edge.point parameter)
  have inside : 0 ≤ parameter ∧ parameter ≤ 1 :=
    ⟨edge.left.inside.1.trans first.between.1, first.between.2.trans edge.right.inside.2⟩
  have identity : first.channel.samples.sample index - last.channel.samples.sample index = weight * (left - right) := by
    rw [first.sample_eq, last.sample_eq, ← ReciprocalRootNames.factor_identity curve _
      (PreparedExteriorReciprocal.parent_point_nonzero data.boundary inside)]
    dsimp only [weight, left, right, ReciprocalInverseModelOverlap.value]
    ring1
  have estimate : Basic.normSq (left - right) ≤ 2 *
      (Basic.normSq (source - left) + Basic.normSq (source -
        right)) := by
    rw [show left - right = (source - right) - (source - left) by ring1]
    exact (Bounds.normSq_sub_le_two _ _).trans_eq (by ring1)
  have bounded := (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (estimate.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (first.source_distance (2 + index)) (last.source_distance (2 + index))) (by decide)))
    (Basic.normSq_nonneg weight))
  rw [identity, Basic.normSq_mul]
  exact (bounded.trans_eq (by
      dsimp only [weight];
      rw [quarterRadius_eq_mul_pow];
      unfold comparisonScale;
      ring1)).trans
    (quarterRadius_antitone
      (comparisonScale_nonnegative data
      parameter) (Nat.le_add_left index 2))

/-- The actual cached root programs agree wherever two cells overlap. -/
@[expose] def equivalent (first : RootPoint
  prepared parameter) (last : RootPoint otherModel
  parameter) :
    NamedEquivalent first.channel.certificate.value.name last.channel.certificate.value.name := by
  let left := first.channel.samples.approximation first.channel.small first.channel.inside
  let right := last.channel.samples.approximation last.channel.small last.channel.inside
  let bound := comparisonScale data
    parameter
  let samples : Equivalent left right := {
    compare := fun leftStart rightStart target positive => by
      let budget := target / 4
      have budgetPositive : 0 < budget := Field.div_pos_direct positive (by decide)
      let index := firstQuarterBelow bound (max leftStart rightStart) budget
      have start := Search.firstQuarterBelow_ge bound (max leftStart rightStart) budget
      let comparison := (Equivalent.refl right).compare index index budget budgetPositive
      refine ⟨comparison.leftIndex, comparison.rightIndex,
        ((Data.Nat.Order.le_max_left _ _).trans start).trans comparison.left_ge,
        ((Data.Nat.Order.le_max_right _ _).trans start).trans comparison.right_ge, ?_⟩
      intro leftIndex rightIndex leftLater rightLater
      have same : Basic.normSq (left.sample leftIndex - right.sample leftIndex) < budget :=
        (first.sameIndexBound last leftIndex).trans_lt
          ((quarterRadius_antitone
            (comparisonScale_nonnegative
            data parameter)
            (comparison.left_ge.trans leftLater)).trans_lt
              (Search.firstQuarterBelow_accurate bound
                (comparisonScale_nonnegative
                data parameter)
                _ _ budgetPositive))
      exact (Bounds.normSq_sub_le_via (left.sample leftIndex) (right.sample leftIndex) (right.sample
        rightIndex)).trans_lt
        ((Arithmetic.mul_lt_mul_of_pos_left_direct (by
            decide : (0 : Coordinate) < 2)
          (Arithmetic.add_lt_add_direct same (comparison.close leftLater rightLater))).trans_eq (by
            rw [show 2 * (budget + budget) = budget * 4 by ring1]
            exact Fraction.Field.div_mul_cancel_of_ne target 4 (by decide))) }
  exact first.channel.samples_equivalent.symm.trans (samples.trans last.channel.samples_equivalent)

/-- The original attached winding-owner certificates of the two overlapping root channels are operationally equivalent.
-/
@[expose] def ownerEquivalent (first : RootPoint
  prepared parameter) (last : RootPoint otherModel
  parameter) :
    NamedEquivalent (first.channel.attachment.owner.certificate
      first.channel.attachment.owner.parameterNonzero).value.name
      (last.channel.attachment.owner.certificate last.channel.attachment.owner.parameterNonzero).value.name :=
  first.channel.owner_equivalent.trans ((first.equivalent last).trans last.channel.owner_equivalent.symm)

end RootPoint
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
