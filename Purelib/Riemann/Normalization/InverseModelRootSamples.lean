module

public import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Riemann.Normalization.InverseModelRefinementSigns
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Tactic.Ring
import Purelib.Riemann.Normalization.InverseRootComparison
public import Purelib.Riemann.Normalization.InverseRootPolynomial
meta import Purelib.Elab.ConstructiveInjectivity
@[expose] public section

/-!
# Root samples from a retained inverse polynomial model

The model's polynomial sheet fixes every later Newton sample. Pointwise
refinement consumes cached evaluations of the parameter and initial inverse;
it does not regenerate the polynomial coefficients to answer a root request.
All comparisons concern displayed finite indices and rational values.
-/

namespace Purelib.Riemann.Normalization.InverseModelRootSamples

open Purelib.Riemann.Normalization.InverseRootComparison (normalized_value_bound)
open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment OverlapSample)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)

/-- Iterate the scalar inverse-root Newton correction from a retained parameter and initial value. -/
def refineValue (parameter initial : Gaussian) : Nat → Gaussian
  | 0 => initial
  | index + 1 => correction (refineValue parameter initial index)
      (1 - parameter * refineValue parameter initial index ^ 2)

open Purelib.Polynomial in
/-- Polynomial-model refinement evaluates to scalar refinement of its initial values.

The original parameter and inverse values determine the same finite Newton
recursion at every natural index, while the retained polynomial residual
supplies its exact correction equation. -/
theorem Model.refine_eval {polynomial : Polynomial} {box : Box} (model : Model polynomial box)
    (point : Gaussian) (index : Nat) :
    (model.refine index).value.eval point = refineValue (polynomial.eval point) (model.value.eval point) index := by
  induction index with
  | zero => rfl
  | succ index previous =>
      change (model.refine index).step.value.eval point =
        correction (refineValue (polynomial.eval point) (model.value.eval point) index)
          (1 - polynomial.eval point * refineValue (polynomial.eval point) (model.value.eval point) index ^ 2)
      dsimp only [Model.step, correction]
      rewrite [Dense.Basic.DensePolynomial.eval_mul, Dense.Basic.DensePolynomial.eval_add,
        Dense.Basic.DensePolynomial.eval_constant, Dense.Basic.DensePolynomial.eval_scale,
        Model.residual_eq, previous]
      exact Eq.refl _

open Purelib.Data in
/-- Bound the squared norm of parameter times approximate inverse by four plus parameter norm.

The normalized inverse-root residual is at most one sixteenth; no root extraction is needed. -/
theorem normalized_root_bound {parameter inverse : Gaussian}
    (small : normSq (1 - parameter * inverse ^ 2) ≤ 1 / 16) :
    normSq (parameter * inverse) ≤ 4 + normSq parameter := by
  rw [Gaussian.Basic.Canonical.normSq_mul]
  rcases le_total (normSq inverse) (1 : Rat.Fraction.Rational) with below | above
  · exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct below (Gaussian.Basic.Canonical.normSq_nonneg
      _)).trans
      (by rw [Rat.Fraction.Field.mul_one_direct]; exact le_add_of_nonneg_left (by decide))
  · have squared : normSq inverse ≤ normSq inverse ^ 2 := by
      calc
        _ = normSq inverse * 1 := by ring1
        _ ≤ normSq inverse * normSq inverse :=
          Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct above (Gaussian.Basic.Canonical.normSq_nonneg
            _)
        _ = _ := by ring1
    exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared
      (Gaussian.Basic.Canonical.normSq_nonneg _)).trans
      (by
        have scalar := normalized_value_bound (parameter := parameter) (value := inverse)
          (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using small)
        rw [Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar.trans (le_add_of_nonneg_right (Gaussian.Basic.Canonical.normSq_nonneg _)))

variable {polynomial : Polynomial} {box : Box}

open Purelib.Data in
set_option genInjectivity false in
/-- Cached point evaluations for one inverse-root model's finite root-sample sequence.

Retain the parameter, initial inverse value and parameter norm with exact equations so later requests refine scalar
values without rebuilding polynomial coefficients. -/
structure RootSamples (model : Model polynomial box) (point : Gaussian) where
  /-- The cached value of the parameter polynomial at the query point. -/ parameter : Gaussian
  /-- The parameter cache equals the exact polynomial evaluation. -/ parameter_eq : parameter = polynomial.eval point
  /-- The cached initial inverse-model value at the query point. -/ initial : Gaussian
  /-- The initial cache equals the retained model's polynomial evaluation. -/ initial_eq : initial = model.value.eval
    point
  /-- The cached squared norm of the parameter value. -/ parameterNorm : Rat.Fraction.Rational
  /-- The norm cache equals the exact squared norm of the parameter cache. -/ parameterNorm_eq : parameterNorm = normSq
    parameter

constructive_injectivity RootSamples

namespace RootSamples

/-- Evaluate and retain the parameter, initial inverse model and parameter norm once. -/
def build (model : Model polynomial box) (point : Gaussian) : RootSamples model point :=
  let parameter := polynomial.eval point
  ⟨parameter, rfl, model.value.eval point, rfl, normSq parameter, rfl⟩

variable {model : Model polynomial box} {point : Gaussian}

/-- Multiply the cached parameter by the scalar inverse refinement at the requested index. -/
def sample (data : RootSamples model point) (index : Nat) : Gaussian :=
  data.parameter * refineValue data.parameter data.initial index

/-- Read the scalar sample as the parameter times the refined polynomial-model value. -/
theorem sample_eq (data : RootSamples model point) (index : Nat) :
    data.sample index = polynomial.eval point * (model.refine index).value.eval point := by
  rw [sample, data.parameter_eq, data.initial_eq, Model.refine_eval]

section
open Purelib.Data
/-- Four plus the cached parameter norm, bounding every root sample. -/
def bound (data : RootSamples model point) : Rat.Fraction.Rational := 4 + data.parameterNorm
/-- The cached parameter norm times the model's initial residual bound. -/
def residualScale (data : RootSamples model point) : Rat.Fraction.Rational := data.parameterNorm * model.bound
/-- Twelve times the sample bound times the model's initial residual bound. -/
def radiusScale (data : RootSamples model point) : Rat.Fraction.Rational := 12 * data.bound * model.bound

/-- The uniform sample bound is nonnegative. -/
theorem bound_nonnegative (data : RootSamples model point) : 0 ≤ data.bound := by
  rw [bound, data.parameterNorm_eq]
  exact add_nonneg (by decide) (Gaussian.Basic.Canonical.normSq_nonneg _)

/-- The initial root-residual scale is nonnegative. -/
theorem residualScale_nonnegative (data : RootSamples model point) : 0 ≤ data.residualScale := by
  rw [residualScale, data.parameterNorm_eq]
  exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Basic.Canonical.normSq_nonneg _)
    model.bound_nonnegative

/-- The initial comparison-radius scale is nonnegative. -/
theorem radiusScale_nonnegative (data : RootSamples model point) : 0 ≤ data.radiusScale :=
  Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.bound_nonnegative) model.bound_nonnegative

end

open Purelib.Approximation in
/-- Every root sample at a point in the model box satisfies the retained uniform norm bound. -/
theorem sample_bounded (data : RootSamples model point) (inside : box.Contains point) (index : Nat) :
    normSq (data.sample index) ≤ data.bound := by
  rw [sample_eq, bound, data.parameterNorm_eq, data.parameter_eq]
  exact normalized_root_bound ((model.refine_residualBound index point inside).trans
    ((Rational.Geometric.Basic.quarterRadius_le_scale model.bound_nonnegative index).trans model.bound_small))

open Purelib.Approximation in
open Purelib.Data in
/-- The samples' squared root residual decays by the retained geometric quarter-radius. -/
theorem residual_bound (data : RootSamples model point) (inside : box.Contains point) (index : Nat) :
    normSq (data.sample index * data.sample index - data.parameter) ≤ Rational.Geometric.Basic.quarterRadius
      data.residualScale index := by
  rw [sample_eq, data.parameter_eq]
  have identity :
      (polynomial.eval point * (model.refine index).value.eval point) *
          (polynomial.eval point * (model.refine index).value.eval point) - polynomial.eval point =
        -(polynomial.eval point * (1 - polynomial.eval point * (model.refine index).value.eval point ^ 2)) := by ring1
  rw [identity, Gaussian.Basic.Canonical.normSq_neg, Gaussian.Basic.Canonical.normSq_mul]
  calc
    _ ≤ normSq (polynomial.eval point) * Rational.Geometric.Basic.quarterRadius model.bound index :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (model.refine_residualBound index point inside) (Gaussian.Basic.Canonical.normSq_nonneg _)
    _ = _ := by
      rw [residualScale, data.parameterNorm_eq, data.parameter_eq,
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

open Purelib.Riemann in
/-- All refinements of a sufficiently accurate retained inverse model select the same sheet.

The initial bound is at most one divided by 256 and the point lies in the model box. -/
private theorem same_sign (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) (first last : Nat) :
    (SignAlignment.build ((model.refine first).value.eval point) ((model.refine last).value.eval point)).flip = false :=
      by
  let common := OverlapSample.build model model point
  have refined := Normalization.InverseModelRefinementSigns.OverlapSample.refine_flip
    common inside inside small small first last
  have initial := (Normalization.InverseModelRefinementSigns.Model.refine_self_flip model) small point inside 0
  exact refined.trans initial

open Purelib.Approximation
open Purelib.Data
/-- Bound the squared distance between ordered samples by the earlier geometric comparison radius.

The initial inverse model meets the overlap-ready bound, preserving a common sheet at both finite indices. -/
theorem later_close (data : RootSamples model point) (small : model.bound ≤ 1 / 256)
    (inside : box.Contains point) {earlier later : Nat} (order : earlier ≤ later) :
    normSq (data.sample later - data.sample earlier) ≤ Rational.Geometric.Basic.quarterRadius data.radiusScale earlier
      := by
  let first := (model.refine earlier).value.eval point
  let last := (model.refine later).value.eval point
  let alignment := SignAlignment.build first last
  have selected : alignment.value = last := by
    rw [alignment.value_eq, same_sign model small point inside earlier later]
    rfl
  have distance := alignment.distance_le (model.refine_residualBound earlier point inside)
    (model.refine_residualBound later point inside)
    ((Rational.Geometric.Basic.quarterRadius_le_scale model.bound_nonnegative earlier).trans model.bound_small)
  rw [selected] at distance
  have radiusOrder := quarterRadius_antitone model.bound_nonnegative order
  have combined : 6 * (Rational.Geometric.Basic.quarterRadius model.bound earlier +
    Rational.Geometric.Basic.quarterRadius model.bound later) ≤
      12 * Rational.Geometric.Basic.quarterRadius model.bound earlier :=
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Rat.Fraction.Order.Arithmetic.add_le_add_direct le_rfl radiusOrder) (by decide)).trans_eq (by ring1)
  have total : normSq (first - last) ≤ 12 * Rational.Geometric.Basic.quarterRadius model.bound earlier * normSq first :=
    distance.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct combined
      (Gaussian.Basic.Canonical.normSq_nonneg _))
  have rootBound : normSq (polynomial.eval point) * normSq first ≤ data.bound := by
    rw [← Gaussian.Basic.Canonical.normSq_mul]
    exact (data.sample_eq earlier) ▸ data.sample_bounded inside earlier
  rw [data.sample_eq later, data.sample_eq earlier]
  have difference : polynomial.eval point * last - polynomial.eval point * first =
      -(polynomial.eval point * (first - last)) := by ring1
  rw [difference, Gaussian.Basic.Canonical.normSq_neg, Gaussian.Basic.Canonical.normSq_mul]
  calc
    _ ≤ normSq (polynomial.eval point) * (12 * Rational.Geometric.Basic.quarterRadius model.bound earlier * normSq
      first) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct total (Gaussian.Basic.Canonical.normSq_nonneg _)
    _ = (12 * Rational.Geometric.Basic.quarterRadius model.bound earlier) * (normSq (polynomial.eval point) * normSq
      first) := by
      ring1
    _ ≤ (12 * Rational.Geometric.Basic.quarterRadius model.bound earlier) * data.bound :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootBound
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
          (Rational.Geometric.Basic.quarterRadius_nonneg model.bound_nonnegative earlier))
    _ = _ := by
      rw [radiusScale, Rational.Geometric.Basic.quarterRadius_eq_mul_pow,
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

/-- Package the retained root samples with executable finite accuracy requests.

The model is overlap-ready and the point lies in its box. Geometric search selects later indices while preserving the
cached parameter, original sheet and uniform center bound. -/
def approximation (data : RootSamples model point) (small : model.bound ≤ 1 / 256)
    (inside : box.Contains point) : Gaussian.Sequence.ApproximationData where
  sample := data.sample
  radiusSq := Rational.Geometric.Basic.quarterRadius data.radiusScale
  radiusSq_nonneg := Rational.Geometric.Basic.quarterRadius_nonneg data.radiusScale_nonnegative
  later_close := fun order => by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using data.later_close small inside order
  refineIndex := fun current target _ => Rational.Geometric.Search.firstQuarterBelow data.radiusScale current target
  refineIndex_ge := fun current target _ => Rational.Geometric.Search.firstQuarterBelow_ge data.radiusScale current
    target
  refineIndex_accurate := fun current target positive =>
    Rational.Geometric.Search.firstQuarterBelow_accurate data.radiusScale data.radiusScale_nonnegative current target
      positive
  centerBound := data.bound
  centerBound_nonneg := data.bound_nonnegative
  sample_bounded := fun index => by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using data.sample_bounded inside index

end RootSamples
end Purelib.Riemann.Normalization.InverseModelRootSamples
