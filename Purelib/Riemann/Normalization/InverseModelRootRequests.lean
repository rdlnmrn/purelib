module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Tactic.Ring

public section

/-!
# Requested inverse errors on the model's actual root channel

The request pays the polynomial residual and the retained root comparison
together. Its cached bounds select one model stage and one root-name stage;
the estimate holds at every independent pair of later finite indices.
-/

namespace Purelib.Riemann.Normalization.InverseModelRootRequests

open Purelib.Riemann.Normalization.InverseModelRootChannels (RootChannel)
open Purelib.Riemann.RootContinuation.SquareRootChannelOwnership (parameter_nonzero)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)

variable {polynomial : Polynomial} {box : Box} {model : Model polynomial box} {point : Gaussian}

open Purelib.Riemann in
open Purelib.Data in
/-- The retained root channel has a strictly positive polynomial parameter norm. -/
theorem parameterNorm_positive (channel : RootChannel model point) : 0 < channel.samples.parameterNorm := by
  rw [channel.samples.parameterNorm_eq, channel.samples.parameter_eq]
  exact (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using (Gaussian.Norm.Basic.normSq_pos
    (RootContinuation.SquareRootChannelOwnership.parameter_nonzero channel.certificate)))

/-- The uniform inverse-value ceiling obtained by dividing the cached root bound by its parameter norm. -/
@[expose] def inverseBound (channel : RootChannel model point) : Coordinate := channel.samples.bound /
  channel.samples.parameterNorm

section
open Purelib.Data
/-- The cached inverse-value ceiling is nonnegative. -/
theorem inverseBound_nonnegative (channel : RootChannel model point) : 0 ≤ (inverseBound channel) :=
  Rat.Fraction.Order.Field.div_nonneg_direct channel.samples.bound_nonnegative (parameterNorm_positive channel).le

/-- Every refined inverse-polynomial value obeys the same retained channel ceiling.

The channel point lies in the original model box, and positivity of the parameter norm transfers the uniform root-sample
bound to the inverse value. -/
theorem inverse_value_bound (channel : RootChannel model point) (index : Nat) :
    normSq ((model.refine index).value.eval point) ≤ (inverseBound channel) := by
  apply (Rat.Fraction.Order.Field.le_div_iff_pos (parameterNorm_positive channel)).mpr
  have bound := channel.samples.sample_bounded channel.inside index
  rw [channel.samples.sample_eq, Gaussian.Basic.Canonical.normSq_mul] at bound
  rw [channel.samples.parameterNorm_eq, channel.samples.parameter_eq, Rat.Fraction.Field.mul_comm]
  exact bound

end

set_option genInjectivity false in
open Purelib.Approximation in
/-- A finite accuracy request comparing the retained inverse polynomial with its operational root inverse.

The record caches residual and root-comparison targets, the original comparison, the geometric residual stage, and a
model stage dominating both retained requirements. Its indices preserve the requested floor. -/
structure InverseRequest (channel : RootChannel model point) (target : Coordinate) (floor : Nat) where
  /-- The requested squared inverse error is strictly positive. -/ positive : 0 < target
  /-- The cached uniform inverse-value ceiling. -/ upper : Coordinate
  /-- The cached ceiling is the original channel's inverse bound. -/ upper_eq : upper = (inverseBound channel)
  /-- The retained polynomial residual tolerance. -/ residualTarget : Coordinate
  /-- The residual tolerance is one quarter of the target times the root's squared apartness lower bound. -/
    residualTarget_eq : residualTarget = target * channel.certificate.apart.certificate.lowerSq / 4
  /-- The retained tolerance for the root-sample comparison. -/ rootTarget : Coordinate
  /-- The comparison tolerance divides the residual target by the cached inverse ceiling plus one. -/ rootTarget_eq :
    rootTarget = residualTarget / (upper + 1)
  /-- The actual comparison of retained Newton samples and root-name readings at the requested floor. -/ comparison :
    Gaussian.Equivalence.Comparison
    (channel.samples.approximation channel.small channel.inside)
    (Gaussian.Name.Sampling.approximation channel.certificate.value.name) floor floor rootTarget
  /-- The selected finite model stage for the polynomial residual. -/ residualIndex : Nat
  /-- The residual stage is the original geometric search from the requested floor. -/ residualIndex_eq : residualIndex
    = Rational.Geometric.Search.firstQuarterBelow model.bound floor residualTarget
  /-- The model stage paying both the residual and sample-comparison requirements. -/ index : Nat
  /-- The retained model stage is the maximum of the residual stage and comparison's left stage. -/ index_eq : index =
    max residualIndex comparison.leftIndex

constructive_injectivity InverseRequest

namespace InverseRequest

open Purelib.Approximation in
open Purelib.Data in
/-- Construct the cached inverse-accuracy request from a positive target and stage floor.

Root apartness pays the residual target, the retained inverse ceiling pays the root comparison, and the resulting model
stage combines the geometric search with the original comparison stage. -/
@[expose] def build (channel : RootChannel model point) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    InverseRequest channel target floor :=
  let upper := (inverseBound channel)
  let residualTarget := target * channel.certificate.apart.certificate.lowerSq / 4
  let rootTarget := residualTarget / (upper + 1)
  have residualPositive : 0 < residualTarget := Rat.Fraction.Order.Field.div_pos_direct
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct positive channel.certificate.apart.certificate.positive) (by decide)
  have rootPositive : 0 < rootTarget := Rat.Fraction.Order.Field.div_pos_direct residualPositive
    (Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (inverseBound_nonnegative channel) (by decide))
  let comparison := channel.samples_equivalent.compare floor floor rootTarget rootPositive
  let residualIndex := Rational.Geometric.Search.firstQuarterBelow model.bound floor residualTarget
  ⟨positive, upper, rfl, residualTarget, rfl, rootTarget, rfl, comparison, residualIndex, rfl,
    max residualIndex comparison.leftIndex, rfl⟩

variable {channel : RootChannel model point} {target : Coordinate} {floor : Nat}

/-- The retained model stage respects the requested floor.

The retained maximum includes the original comparison stage. Its existing
floor certificate therefore applies to the selected model stage. -/
theorem floor_le (request : InverseRequest channel target floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact request.comparison.left_ge.trans (Purelib.Data.Nat.Order.le_max_right _ _)

open Purelib.Data in
/-- The retained residual target is strictly positive. -/
theorem residualTarget_positive (request : InverseRequest channel target floor) : 0 < request.residualTarget := by
  rw [request.residualTarget_eq]
  exact Rat.Fraction.Order.Field.div_pos_direct
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct request.positive channel.certificate.apart.certificate.positive) (by
      decide)

open Purelib.Approximation in
open Purelib.Data in
/-- Bound the inverse-polynomial error against every sufficiently late reading of its certified root.

Independent later model and root-name stages consume the same retained residual bound, comparison and apartness
certificate, giving squared error strictly below the original positive target. -/
theorem accurate (request : InverseRequest channel target floor) {index rootIndex : Nat}
    (later : request.index ≤ index) (rootLater : request.comparison.rightIndex ≤ rootIndex) :
    normSq ((model.refine index).value.eval point -
      inv ((Gaussian.Name.Sampling.approximation channel.certificate.value.name).sample rootIndex)) < target := by
  let inverse := (model.refine index).value.eval point
  let root := (Gaussian.Name.Sampling.approximation channel.certificate.value.name).sample rootIndex
  have indices := later
  rw [request.index_eq] at indices
  have close := request.comparison.close ((Purelib.Data.Nat.Order.le_max_right _ _).trans indices) rootLater
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at close
  change normSq (channel.samples.sample index - root) < request.rootTarget at close
  rw [channel.samples.sample_eq] at close
  have upper : normSq inverse ≤ request.upper := by
    rw [request.upper_eq]
    exact (inverse_value_bound channel) index
  have upperPositive : 0 < request.upper + 1 :=
    Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct ((Gaussian.Basic.Canonical.normSq_nonneg _).trans
      upper) (by decide)
  have rootTerm : normSq (inverse * (root - polynomial.eval point * inverse)) < request.residualTarget := by
    rw [Gaussian.Basic.Canonical.normSq_mul, show root - polynomial.eval point * inverse =
      -(polynomial.eval point * inverse - root) by ring1, Gaussian.Basic.Canonical.normSq_neg]
    calc
      _ ≤ (request.upper + 1) * normSq (polynomial.eval point * inverse - root) :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (upper.trans (le_add_of_nonneg_right (by decide))) (Gaussian.Basic.Canonical.normSq_nonneg _)
      _ < (request.upper + 1) * request.rootTarget :=
        Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct upperPositive close
      _ = request.residualTarget := by
        rw [request.rootTarget_eq, Rat.Fraction.Field.mul_comm]
        exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ upperPositive.ne'
  have residual : normSq (1 - polynomial.eval point * inverse ^ 2) < request.residualTarget := by
    apply (model.refine_residualBound index point channel.inside).trans_lt
    have residualLater := (Purelib.Data.Nat.Order.le_max_left _ _).trans indices
    rw [request.residualIndex_eq] at residualLater
    exact (quarterRadius_antitone model.bound_nonnegative residualLater).trans_lt
      (Rational.Geometric.Search.firstQuarterBelow_accurate model.bound model.bound_nonnegative floor
        request.residualTarget request.residualTarget_positive)
  have mismatch : normSq (inverse * root - 1) < target * channel.certificate.apart.certificate.lowerSq := by
    rw [show inverse * root - 1 = inverse * (root - polynomial.eval point * inverse) -
      (1 - polynomial.eval point * inverse ^ 2) by ring1]
    have subtractBound := Gaussian.Norm.Bounds.normSq_sub_le_two
      (inverse * (root - polynomial.eval point * inverse)) (1 - polynomial.eval point * inverse ^ 2)
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at subtractBound
    apply subtractBound.trans_lt
    have bound := Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Coordinate) < 2)
      (Rat.Fraction.Order.Arithmetic.add_lt_add_direct rootTerm residual)
    apply bound.trans_eq
    rw [show 2 * (request.residualTarget + request.residualTarget) = request.residualTarget * 4 by ring1,
      request.residualTarget_eq]
    exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have rootLower := Gaussian.Name.Apart.Sampling.sampled_lower channel.certificate.value channel.certificate.apart
    rootIndex
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at rootLower
  have nonzero := Gaussian.Name.Apart.Sampling.sampled_nonzero channel.certificate.value channel.certificate.apart
    rootIndex
  apply Rat.Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct (c := channel.certificate.apart.certificate.lowerSq)
    _ channel.certificate.apart.certificate.positive
  calc
    _ ≤ normSq (inverse - inv root) * normSq root :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootLower (Gaussian.Basic.Canonical.normSq_nonneg
        _)
    _ = normSq (inverse * root - 1) := by
      rw [← Gaussian.Basic.Canonical.normSq_mul]
      congr 1
      calc
        _ = inverse * root - root * inv root := by ring1
        _ = _ := by
          change inverse * root - root * root⁻¹ = inverse * root - 1
          rw [Gaussian.Basic.Canonical.mul_inv_cancel root nonzero]
    _ < _ := mismatch

end InverseRequest
end Purelib.Riemann.Normalization.InverseModelRootRequests
