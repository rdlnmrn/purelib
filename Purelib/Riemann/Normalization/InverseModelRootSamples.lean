module

public import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order
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
public import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Polynomial.Dense.Gaussian.Derivative.Bounds
import Purelib.Polynomial.Clearance.Box.Region
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat.Fraction.Order
@[expose] public section

/-!
# Root samples from a retained inverse polynomial model

The model's polynomial sheet fixes every later Newton sample. Pointwise
refinement consumes cached evaluations of the parameter and initial inverse;
it does not regenerate the polynomial coefficients to answer a root request.
All comparisons concern displayed finite indices and rational values.
-/

namespace Purelib.Riemann.Normalization.InverseModelRootSamples

open Purelib.Data.Gaussian

open Purelib.Riemann.Normalization.InverseRootComparison (normalized_value_bound)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
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
      rewrite [eval_mul, eval_add,
        eval_constant, eval_scale,
        Model.residual_eq, previous]
      exact Eq.refl _

open Purelib.Data in
/-- Bound the squared norm of parameter times approximate inverse by four plus parameter norm.

The normalized inverse-root residual is at most one sixteenth; no root extraction is needed. -/
theorem normalized_root_bound {parameter inverse : Gaussian}
    (small : normSq (1 - parameter * inverse ^ 2) ≤ 1 / 16) :
    normSq (parameter * inverse) ≤ 4 + normSq parameter := by
  rw [normSq_mul]
  rcases le_total (normSq inverse) (1 : Rat.Fraction.Rational) with below | above
  · exact (Arithmetic.mul_le_mul_of_nonneg_left_direct below (normSq_nonneg
      _)).trans
      (by rw [Rat.Fraction.Field.mul_one_direct]; exact le_add_of_nonneg_left (by decide))
  · have squared : normSq inverse ≤ normSq inverse ^ 2 := by
      calc
        _ = normSq inverse * 1 := by ring1
        _ ≤ normSq inverse * normSq inverse :=
          Arithmetic.mul_le_mul_of_nonneg_left_direct above (normSq_nonneg
            _)
        _ = _ := by ring1
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct squared
      (normSq_nonneg _)).trans
      (by
        have scalar := normalized_value_bound (parameter := parameter) (value := inverse)
          (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using small)
        rw [Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar.trans (le_add_of_nonneg_right (normSq_nonneg _)))

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

/-- Two actual point caches of the same model have one spatial increment bound at every common refinement index.

The supplied original product-derivative cache has numerator equal to the
same curve polynomial. Its existing coefficient derivative estimate and
the finite box increment theorem bound the original root samples without
constructing another root channel or a refinement-dependent majorant.
-/
theorem increment_le {clearance : RegionClearance polynomial box}
    {root : InverseModelDerivativeBounds.DerivativeBounds clearance model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root polynomial)
    {start finish : Gaussian} (first : RootSamples model start) (last : RootSamples model finish)
    (startInside : box.Contains start) (finishInside : box.Contains finish) (index : Nat) :
    normSq (last.sample index - first.sample index) ≤
      2 * bounds.bound * normSq (finish - start) := by
  let coefficient := polynomial * (model.refine index).value
  have equal : ∀ point, coefficient.eval point = polynomial.eval point *
      (model.refine index).value.eval point := fun point =>
    Purelib.Polynomial.Dense.Basic.DensePolynomial.eval_mul _ _ point
  have estimate := Purelib.Polynomial.Dense.Gaussian.Derivative.Bounds.eval_sub_eval_le_of_derivative_bound
    coefficient startInside finishInside bounds.bound (fun point inside => by
      rewrite [Norm.Basic.normSq_eq_canonical]
      exact bounds.coefficient_derivative_le index coefficient equal inside)
  rewrite [first.sample_eq, last.sample_eq]
  rewrite [equal finish, equal start, Norm.Basic.normSq_eq_canonical,
    Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate

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
  exact add_nonneg (by decide) (normSq_nonneg _)

/-- The initial root-residual scale is nonnegative. -/
theorem residualScale_nonnegative (data : RootSamples model point) : 0 ≤ data.residualScale := by
  rw [residualScale, data.parameterNorm_eq]
  exact Arithmetic.mul_nonneg_direct (normSq_nonneg _)
    model.bound_nonnegative

/-- The initial comparison-radius scale is nonnegative. -/
theorem radiusScale_nonnegative (data : RootSamples model point) : 0 ≤ data.radiusScale :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide) data.bound_nonnegative) model.bound_nonnegative

end

open Purelib.Approximation in
/-- Every root sample at a point in the model box satisfies the retained uniform norm bound. -/
theorem sample_bounded (data : RootSamples model point) (inside : box.Contains point) (index : Nat) :
    normSq (data.sample index) ≤ data.bound := by
  rw [sample_eq, bound, data.parameterNorm_eq, data.parameter_eq]
  exact normalized_root_bound ((model.refine_residualBound index point inside).trans
    ((Basic.quarterRadius_le_scale model.bound_nonnegative index).trans model.bound_small))

open Purelib.Approximation in
open Purelib.Data in
/-- The samples' squared root residual decays by the retained geometric quarter-radius. -/
theorem residual_bound (data : RootSamples model point) (inside : box.Contains point) (index : Nat) :
    normSq (data.sample index * data.sample index - data.parameter) ≤ quarterRadius
      data.residualScale index := by
  rw [sample_eq, data.parameter_eq]
  have identity :
      (polynomial.eval point * (model.refine index).value.eval point) *
          (polynomial.eval point * (model.refine index).value.eval point) - polynomial.eval point =
        -(polynomial.eval point * (1 - polynomial.eval point * (model.refine index).value.eval point ^ 2)) := by ring1
  rw [identity, normSq_neg, normSq_mul]
  calc
    _ ≤ normSq (polynomial.eval point) * quarterRadius model.bound index :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (model.refine_residualBound index point inside) (normSq_nonneg _)
    _ = _ := by
      rw [residualScale, data.parameterNorm_eq, data.parameter_eq,
        Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      ring1

open Purelib.Riemann in
/-- All refinements of a sufficiently accurate retained inverse model select the same sheet.

The initial bound is at most one divided by 256 and the point lies in the model box. -/
private theorem same_sign (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) (first last : Nat) :
    (SignAlignment.build ((model.refine first).value.eval point) ((model.refine last).value.eval point)).flip = false :=
      by
  let common := OverlapSample.build model model point
  have refined := InverseModelRefinementSigns.OverlapSample.refine_flip
    common inside inside small small first last
  have initial := (InverseModelRefinementSigns.Model.refine_self_flip model) small point inside 0
  exact refined.trans initial

open Purelib.Approximation
open Purelib.Data
/-- Two ordered inverse refinements on the same retained sheet obey the original earlier-index distance bound. -/
private theorem refinement_distance_le (model : Model polynomial box) (small : model.bound ≤ 1 / 256)
    (point : Gaussian) (inside : box.Contains point) {earlier later : Nat} (order : earlier ≤ later) :
    normSq ((model.refine earlier).value.eval point - (model.refine later).value.eval point) ≤
      12 * quarterRadius model.bound earlier * normSq ((model.refine earlier).value.eval point) := by
  let first := (model.refine earlier).value.eval point
  let last := (model.refine later).value.eval point
  let alignment := SignAlignment.build first last
  have selected : alignment.value = last := by
    rw [alignment.value_eq, same_sign model small point inside earlier later]
    rfl
  have distance := alignment.distance_le (model.refine_residualBound earlier point inside)
    (model.refine_residualBound later point inside)
    ((Basic.quarterRadius_le_scale model.bound_nonnegative earlier).trans model.bound_small)
  rw [selected] at distance
  have radiusOrder := quarterRadius_antitone model.bound_nonnegative order
  have combined : 6 * (quarterRadius model.bound earlier +
    quarterRadius model.bound later) ≤
      12 * quarterRadius model.bound earlier :=
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct le_rfl radiusOrder) (by decide)).trans_eq (by ring1)
  have total : normSq (first - last) ≤ 12 * quarterRadius model.bound earlier * normSq first :=
    distance.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct combined
      (normSq_nonneg _))
  exact total

/-- Bound the squared distance between ordered samples by the earlier geometric comparison radius.

The initial inverse model meets the overlap-ready bound, preserving a common sheet at both finite indices. -/
theorem later_close (data : RootSamples model point) (small : model.bound ≤ 1 / 256)
    (inside : box.Contains point) {earlier later : Nat} (order : earlier ≤ later) :
    normSq (data.sample later - data.sample earlier) ≤ quarterRadius data.radiusScale earlier
      := by
  let first := (model.refine earlier).value.eval point
  let last := (model.refine later).value.eval point
  have total : normSq (first - last) ≤ 12 * quarterRadius model.bound earlier * normSq first :=
    refinement_distance_le model small point inside order
  have rootBound : normSq (polynomial.eval point) * normSq first ≤ data.bound := by
    rw [← normSq_mul]
    exact (data.sample_eq earlier) ▸ data.sample_bounded inside earlier
  rw [data.sample_eq later, data.sample_eq earlier]
  have difference : polynomial.eval point * last - polynomial.eval point * first =
      -(polynomial.eval point * (first - last)) := by ring1
  rw [difference, normSq_neg, normSq_mul]
  calc
    _ ≤ normSq (polynomial.eval point) * (12 * quarterRadius model.bound earlier * normSq
      first) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct total (normSq_nonneg _)
    _ = (12 * quarterRadius model.bound earlier) * (normSq (polynomial.eval point) * normSq
      first) := by
      ring1
    _ ≤ (12 * quarterRadius model.bound earlier) * data.bound :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct rootBound
        (Arithmetic.mul_nonneg_direct (by decide)
          (Basic.quarterRadius_nonneg model.bound_nonnegative earlier))
    _ = _ := by
      rw [radiusScale, Basic.quarterRadius_eq_mul_pow,
        Basic.quarterRadius_eq_mul_pow]
      ring1

/-- Every sufficiently late actual sample has small normalized mismatch with an original twice-refined inverse model.

The original model bound is at most one divided by 256. Its fixed inverse
refinement has index at least two, and the actual sample index is no earlier.
Original same-sheet distance and normalized-value bounds give the explicit
quadrance budget; no independent root or continuation owner is selected.
-/
theorem sample_polynomial_mismatch (data : RootSamples model point) (small : model.bound ≤ 1 / 256)
    (inside : box.Contains point) (index later : Nat) (order : index + 2 ≤ later) :
    normSq (1 - data.sample later * (model.refine (index + 2)).value.eval point) ≤ 1 / 32 := by
  let parameter := polynomial.eval point
  let first := (model.refine (index + 2)).value.eval point
  let last := (model.refine later).value.eval point
  let radius := quarterRadius model.bound (index + 2)
  have radiusNonnegative : 0 ≤ radius := Basic.quarterRadius_nonneg model.bound_nonnegative _
  have residual : normSq (1 - parameter * first ^ 2) ≤ radius :=
    model.refine_residualBound (index + 2) point inside
  have normalized : normSq parameter * normSq first ^ 2 ≤ 4 := by
    have smallResidual : normSq (1 - parameter * first ^ 2) ≤ 1 / 16 :=
      residual.trans ((Basic.quarterRadius_le_scale model.bound_nonnegative _).trans model.bound_small)
    have bounded := normalized_value_bound (parameter := parameter) (value := first)
      (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using smallResidual)
    rw [Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Norm.Basic.normSq_eq_canonical] at bounded
    exact bounded
  have distance : normSq (first - last) ≤ 12 * radius * normSq first :=
    refinement_distance_le model small point inside order
  have weighted : normSq (parameter * first * (first - last)) ≤ 48 * radius := by
    rw [normSq_mul, normSq_mul]
    calc
      _ ≤ (normSq parameter * normSq first) * (12 * radius * normSq first) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct distance
          (Arithmetic.mul_nonneg_direct (normSq_nonneg _) (normSq_nonneg _))
      _ = (12 * radius) * (normSq parameter * normSq first ^ 2) := by ring1
      _ ≤ (12 * radius) * 4 := Arithmetic.mul_le_mul_of_nonneg_left_direct normalized
        (Arithmetic.mul_nonneg_direct (by decide +kernel) radiusNonnegative)
      _ = 48 * radius := by ring1
  have radiusBound : radius ≤ 1 / 4096 := by
    apply (Basic.quarterRadius_antitone model.bound_nonnegative (Nat.le_add_left 2 index)).trans
    rw [Basic.quarterRadius_eq_mul_pow]
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct small
      (by decide +kernel : (0 : Coordinate) ≤ (1 / 4) ^ 2)).trans_eq
        (by decide +kernel : (1 / 256 : Coordinate) * (1 / 4) ^ 2 = 1 / 4096)
  rw [data.sample_eq]
  change normSq (1 - (parameter * last) * first) ≤ 1 / 32
  have identity : 1 - (parameter * last) * first =
      (1 - parameter * first ^ 2) + parameter * first * (first - last) := by ring1
  rw [identity]
  calc
    _ ≤ 2 * (normSq (1 - parameter * first ^ 2) + normSq (parameter * first * (first - last))) := by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
        (Gaussian.Norm.Bounds.normSq_add_le_two (1 - parameter * first ^ 2)
          (parameter * first * (first - last)))
    _ ≤ 2 * (radius + 48 * radius) := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct residual weighted) (by decide +kernel)
    _ = 98 * radius := by ring1
    _ ≤ 98 * (1 / 4096) := Arithmetic.mul_le_mul_of_nonneg_left_direct radiusBound (by decide +kernel)
    _ ≤ 1 / 32 := by decide +kernel

/-- Package the retained root samples with executable finite accuracy requests.

The model is overlap-ready and the point lies in its box. Geometric search selects later indices while preserving the
cached parameter, original sheet and uniform center bound. -/
def approximation (data : RootSamples model point) (small : model.bound ≤ 1 / 256)
    (inside : box.Contains point) : Gaussian.Sequence.ApproximationData where
  sample := data.sample
  radiusSq := quarterRadius data.radiusScale
  radiusSq_nonneg := Basic.quarterRadius_nonneg data.radiusScale_nonnegative
  later_close := fun order => by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using data.later_close small inside order
  refineIndex := fun current target _ => Search.firstQuarterBelow data.radiusScale current target
  refineIndex_ge := fun current target _ => Search.firstQuarterBelow_ge data.radiusScale current
    target
  refineIndex_accurate := fun current target positive =>
    Search.firstQuarterBelow_accurate data.radiusScale data.radiusScale_nonnegative current target
      positive
  centerBound := data.bound
  centerBound_nonneg := data.bound_nonnegative
  sample_bounded := fun index => by
    simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using data.sample_bounded inside index

section SpatialComparison

open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Data.Nat

/-- Compare the same model's two actual point caches at independently requested later stages.

A finite geometric search synchronizes the original sample tails before
using the shared product-derivative cache at one common polynomial index.
The resulting comparison retains both original approximations and starts;
its spatial allowance is explicit and its additional error is requested.
-/
def comparePoints {clearance : RegionClearance polynomial box}
    {root : InverseModelDerivativeBounds.DerivativeBounds clearance model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root polynomial)
    {start finish : Gaussian} (first : RootSamples model start) (last : RootSamples model finish)
    (small : model.bound ≤ 1 / 256) (startInside : box.Contains start) (finishInside : box.Contains finish)
    (leftStart rightStart : Nat) (accuracy : Coordinate) (positive : 0 < accuracy) :
    Comparison (last.approximation small finishInside) (first.approximation small startInside)
      leftStart rightStart (8 * bounds.bound * Basic.Canonical.normSq (finish - start) + accuracy) := by
  let left := last.approximation small finishInside
  let right := first.approximation small startInside
  let precision := accuracy / 16
  have precisionPositive : 0 < precision := Field.div_pos_direct positive (by decide)
  let leftIndex := left.refineIndex leftStart precision precisionPositive
  let rightIndex := right.refineIndex rightStart precision precisionPositive
  let index := max leftIndex rightIndex
  have leftOrder : leftIndex ≤ index := by
    dsimp only [index]
    rewrite [Order.max_eq_natMax]
    exact Order.le_max_left _ _
  have rightOrder : rightIndex ≤ index := by
    dsimp only [index]
    rewrite [Order.max_eq_natMax]
    exact Order.le_max_right _ _
  have leftRadius : left.radiusSq index ≤ precision :=
    (quarterRadius_antitone last.radiusScale_nonnegative leftOrder).trans
      (left.refineIndex_accurate leftStart precision precisionPositive).le
  have rightRadius : right.radiusSq index ≤ precision :=
    (quarterRadius_antitone first.radiusScale_nonnegative rightOrder).trans
      (right.refineIndex_accurate rightStart precision precisionPositive).le
  refine ⟨index, index, (left.refineIndex_ge leftStart precision precisionPositive).trans leftOrder,
    (right.refineIndex_ge rightStart precision precisionPositive).trans rightOrder, ?_⟩
  intro leftLater rightLater leftLaterOrder rightLaterOrder
  have leftClose := (left.later_close leftLaterOrder).trans leftRadius
  have rightClose := (right.later_close rightLaterOrder).trans rightRadius
  have same := first.increment_le bounds last startInside finishInside index
  rewrite [Norm.Basic.normSq_eq_canonical] at leftClose rightClose ⊢
  have reverse : Basic.Canonical.normSq (first.sample index - first.sample rightLater) ≤ precision := by
    have symmetric := Norm.Bounds.normSq_sub_symm
      (first.sample index) (first.sample rightLater)
    rewrite [Norm.Basic.normSq_eq_canonical,
      Norm.Basic.normSq_eq_canonical] at symmetric
    rewrite [symmetric]
    exact rightClose
  have middle : Basic.Canonical.normSq (last.sample index - first.sample rightLater) ≤
      2 * (2 * bounds.bound * Basic.Canonical.normSq (finish - start) + precision) :=
    by
      have triangle : Basic.Canonical.normSq (last.sample index - first.sample rightLater) ≤
          2 * (Basic.Canonical.normSq (last.sample index - first.sample index) +
            Basic.Canonical.normSq (first.sample index - first.sample rightLater)) := by
        simpa only [Norm.Basic.normSq_eq_canonical] using
          (Norm.Bounds.normSq_sub_le_via (last.sample index) (first.sample index)
            (first.sample rightLater))
      exact triangle.trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct same reverse) (by decide))
  change Basic.Canonical.normSq (last.sample leftLater - first.sample rightLater) <
    8 * bounds.bound * Basic.Canonical.normSq (finish - start) + accuracy
  calc
    _ ≤ 2 * (Basic.Canonical.normSq (last.sample leftLater - last.sample index) +
        Basic.Canonical.normSq (last.sample index - first.sample rightLater)) := by
      simpa only [Norm.Basic.normSq_eq_canonical] using
        (Norm.Bounds.normSq_sub_le_via (last.sample leftLater) (last.sample index)
          (first.sample rightLater))
    _ ≤ 2 * (precision + 2 * (2 * bounds.bound * Basic.Canonical.normSq (finish - start) + precision)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct leftClose middle) (by decide)
    _ = 8 * bounds.bound * Basic.Canonical.normSq (finish - start) + (6 / 16 : Coordinate) * accuracy := by
      dsimp only [precision]
      simp only [Purelib.Data.Rat.Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ < _ := by
      have ordered := Arithmetic.mul_lt_mul_of_pos_right_direct
        (by decide +kernel : (6 / 16 : Coordinate) < 1) positive
      rewrite [Purelib.Data.Rat.Fraction.Field.one_mul] at ordered
      exact Arithmetic.add_lt_add_left_direct ordered _

end SpatialComparison

end RootSamples
end Purelib.Riemann.Normalization.InverseModelRootSamples

end

namespace Purelib.Riemann.Normalization.InverseModelRootSamples

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Polynomial Box Model)

/-- Every finite scalar refinement retains an exact inverse-root fixed point.

The actual parameter and initial value satisfy the original zero-residual
identity. Each original Newton correction therefore leaves that same
initial value unchanged at every finite index.
-/
public theorem refineValue_fixed (parameter initial : Gaussian)
    (fixed : parameter * initial ^ 2 = 1) :
    ∀ index : Nat, refineValue parameter initial index = initial
  | 0 => rfl
  | index + 1 => by
      rw [refineValue, refineValue_fixed parameter initial fixed index, fixed]
      unfold InverseRootPolynomial.correction
      ring1

/-- Every retained root sample uses the same actual parameter and exact fixed inverse value.

The zero-residual identity concerns the original cached scalar evaluations.
No polynomial model, numerical owner or finite sampling index is replaced.
-/
public theorem RootSamples.sample_fixed {polynomial : Polynomial} {box : Box}
    {model : Model polynomial box} {point : Gaussian} (data : RootSamples model point)
    (fixed : data.parameter * data.initial ^ 2 = 1) (index : Nat) :
    data.sample index = data.parameter * data.initial := by
  unfold RootSamples.sample
  rewrite [refineValue_fixed data.parameter data.initial fixed index]
  rfl

end Purelib.Riemann.Normalization.InverseModelRootSamples
