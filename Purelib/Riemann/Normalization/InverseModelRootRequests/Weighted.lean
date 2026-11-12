module

public import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Numerator-paid requests on the same original inverse-model root channel

The exact numerator selects a positive scale before the original inverse
request is built. Its actual model and root-name stages pay the weighted
coefficient at every independent later pair of indices.
-/

public section

namespace Purelib.Riemann.Normalization.InverseModelRootRequests.InverseRequest

open Purelib
open Purelib.Approximation.Gaussian.Name
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Riemann.Normalization.InverseModelRootChannels (RootChannel)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Polynomial Box Model)

/-- One plus the exact squared numerator norm pays multiplication, including a zero numerator. -/
def weight (numerator : Gaussian) : Rational := Norm.Basic.normSq numerator + 1

/-- The original exact numerator gives a strictly positive request scale. -/
private theorem packaged_weight_positive (numerator : Gaussian) : 0 < weight numerator :=
  Arithmetic.add_pos_of_nonneg_of_pos_direct (Norm.Basic.normSq_nonneg numerator) (by decide +kernel)

/-- The original exact numerator gives a strictly positive request scale. -/
theorem weight_positive (numerator : Gaussian) : 0 < weight numerator :=
  packaged_weight_positive numerator

/-- Request the original inverse-model accuracy divided by the exact numerator scale.

The result is the original request on the same channel and floor. Its
comparison and residual stages remain actual original selected caches.
-/
def weighted {polynomial : Polynomial} {box : Box} {model : Model polynomial box} {point : Gaussian}
    (channel : RootChannel model point) (numerator : Gaussian) (target : Rational)
    (positive : 0 < target) (floor : Nat) : InverseRequest channel (target / weight numerator) floor :=
  build channel (target / weight numerator)
    (Data.Rat.Fraction.Order.Field.div_pos_direct positive (weight_positive numerator)) floor

/-- The whole retained result is the original complete once-only factory value, including all specification fields. -/
private theorem packaged_weighted_factory {polynomial : Polynomial} {box : Box}
    {model : Model polynomial box} {point : Gaussian}
    (channel : RootChannel model point) (numerator : Gaussian) (target : Rational)
    (positive : 0 < target) (floor : Nat) :
    weighted channel numerator target positive floor =
  (
    build channel (target / weight numerator)
        (Data.Rat.Fraction.Order.Field.div_pos_direct positive (weight_positive numerator)) floor
    : InverseRequest channel (target / weight numerator) floor) := by rfl

/-- The whole retained result is the original complete once-only factory value, including all specification fields. -/
theorem weighted_factory {polynomial : Polynomial} {box : Box}
    {model : Model polynomial box} {point : Gaussian}
    (channel : RootChannel model point) (numerator : Gaussian) (target : Rational)
    (positive : 0 < target) (floor : Nat) :
    weighted channel numerator target positive floor =
  (
    build channel (target / weight numerator)
        (Data.Rat.Fraction.Order.Field.div_pos_direct positive (weight_positive numerator)) floor
    : InverseRequest channel (target / weight numerator) floor) :=
  packaged_weighted_factory channel numerator target positive floor

/-- Every independent later pair of original model/root stages pays the actual numerator-weighted coefficient.

Only scalar multiplication changes the quantity. The root channel, retained
request, original inverse model and root observations stay unchanged.
-/
private theorem packaged_weighted_accurate {polynomial : Polynomial} {box : Box} {model : Model polynomial box}
    {point numerator : Gaussian} {channel : RootChannel model point} {target : Rational} {floor : Nat}
    (request : InverseRequest channel (target / weight numerator) floor) {index rootIndex : Nat}
    (later : request.index ≤ index) (rootLater : request.comparison.rightIndex ≤ rootIndex) :
    Norm.Basic.normSq (numerator * (model.refine index).value.eval point -
      numerator * Field.inv ((Sampling.approximation channel.certificate.value.name).sample rootIndex)) < target := by
  have original := request.accurate later rootLater
  rewrite [← Norm.Basic.normSq_eq_canonical] at original
  change Norm.Basic.normSq ((model.refine index).value.eval point -
    ((Sampling.approximation channel.certificate.value.name).sample rootIndex)⁻¹) < target / weight numerator
      at original
  rewrite [Field.inv_eq] at original
  have upper : Norm.Basic.normSq numerator ≤ weight numerator := by
    have translated := Arithmetic.add_le_add_direct (Basic.le_refl (Norm.Basic.normSq numerator))
      (by decide +kernel : (0 : Rational) ≤ 1)
    exact (show Norm.Basic.normSq numerator = Norm.Basic.normSq numerator + 0 by ring1).trans_le translated
  have scalar : numerator * (model.refine index).value.eval point -
      numerator * Field.inv ((Sampling.approximation channel.certificate.value.name).sample rootIndex) =
      numerator * ((model.refine index).value.eval point -
        Field.inv ((Sampling.approximation channel.certificate.value.name).sample rootIndex)) := by ring1
  rewrite [scalar, Norm.Basic.normSq_mul]
  calc
    _ ≤ weight numerator * Norm.Basic.normSq ((model.refine index).value.eval point -
        Field.inv ((Sampling.approximation channel.certificate.value.name).sample rootIndex)) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct upper (Norm.Basic.normSq_nonneg _)
    _ < weight numerator * (target / weight numerator) :=
      Arithmetic.mul_lt_mul_of_pos_left_direct (weight_positive numerator) original
    _ = target := by
      rewrite [Data.Rat.Fraction.Field.mul_comm]
      exact Data.Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (weight_positive numerator).ne'

/-- Every independent later pair of original model/root stages pays the actual numerator-weighted coefficient.

Only scalar multiplication changes the quantity. The root channel, retained
request, original inverse model and root observations stay unchanged.
-/
theorem weighted_accurate {polynomial : Polynomial} {box : Box} {model : Model polynomial box}
    {point numerator : Gaussian} {channel : RootChannel model point} {target : Rational} {floor : Nat}
    (request : InverseRequest channel (target / weight numerator) floor) {index rootIndex : Nat}
    (later : request.index ≤ index) (rootLater : request.comparison.rightIndex ≤ rootIndex) :
    Norm.Basic.normSq (numerator * (model.refine index).value.eval point -
      numerator * Field.inv ((Sampling.approximation channel.certificate.value.name).sample rootIndex)) < target :=
  packaged_weighted_accurate (polynomial := polynomial) (box := box) (model := model)
    (point := point) (numerator := numerator) (target := target) (floor := floor)
    (index := index) (rootIndex := rootIndex) request later rootLater

end Purelib.Riemann.Normalization.InverseModelRootRequests.InverseRequest

end
