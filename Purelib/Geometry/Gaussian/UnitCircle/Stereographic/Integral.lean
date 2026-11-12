module

public import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Approximation
public import Purelib.Approximation.Gaussian.Geometric.Preparation
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
public import Purelib.Polynomial.Ascending.Gaussian.RationalEmbedding.Evaluation
public import Purelib.Polynomial.Ascending.Rational.Composition
public import Purelib.Polynomial.Ascending.Rational.Geometric
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Composition
import Purelib.Polynomial.Ascending.Rational.Geometric.Cayley
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Power.Order
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Homography.Cayley.Bounds
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Finite polynomial integration of the original logarithmic circle tangent

The displayed Cayley polynomials approximate the original quarter-circle
logarithmic velocity on its actual rational parameter interval. Their
integrals retain these same finite coefficient tables.
-/

public section

namespace Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Integral

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Ascending.Rational
open Purelib.Algebra.Field
open Purelib.Approximation.Rational
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel LocalObservation)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- The retained real quadratic substitution for the logarithmic circle tangent. -/
@[expose] def substitution : Ascending.Rational.Basic.CoefficientPolynomial := ⟨[1 / 3, 0, -2 / 3]⟩

/-- The same retained substitution reads its displayed rational quadratic. -/
theorem substitution_eval (time : Fraction.Rational) :
    GaussianEvaluation.eval substitution ⟨time, 0⟩ =
      (⟨(1 - 2 * time ^ 2) / 3, 0⟩ : Canonical) := by
  apply Data.Gaussian.Basic.ext
  · change (1 / 3 : Fraction.Rational) * 1 +
      (time * (0 * 1 + (time * ((-2 / 3) * 1 + (time * 0 - 0 * 0)) -
        0 * ((-2 / 3) * 0 + (time * 0 + 0 * 0)))) -
      0 * (0 * 0 + (time * ((-2 / 3) * 0 + (time * 0 + 0 * 0)) +
        0 * ((-2 / 3) * 1 + (time * 0 - 0 * 0))))) = (1 - 2 * time ^ 2) / 3
    apply ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (3 : Fraction.Rational) ≠ 0)
    rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)]
    calc
      _ = (1 / 3 : Fraction.Rational) * 3 + ((-2 / 3) * 3) * time ^ 2 := by ring1
      _ = _ := by
        rw [show (1 / 3 : Fraction.Rational) * 3 = 1 by decide +kernel,
          show (-2 / 3 : Fraction.Rational) * 3 = -2 by decide +kernel]
        ring1
  · change (1 / 3 : Fraction.Rational) * 0 +
      (time * (0 * 0 + (time * ((-2 / 3) * 0 + (time * 0 + 0 * 0)) +
        0 * ((-2 / 3) * 1 + (time * 0 - 0 * 0)))) +
      0 * (0 * 1 + (time * ((-2 / 3) * 1 + (time * 0 - 0 * 0)) -
        0 * ((-2 / 3) * 0 + (time * 0 + 0 * 0))))) = 0
    ring1

/-- The original quadratic substitution stays inside the retained Cayley disk on the unit interval.

The displayed finite product `time² * (1 - time²)` is nonnegative on that
same interval. Clearing the fixed denominator gives its exact norm bound.
-/
theorem substitution_normSq_le (time : Fraction.Rational) (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    Norm.Basic.normSq (GaussianEvaluation.eval substitution ⟨time, 0⟩) ≤ 1 / 9 := by
  rw [substitution_eval]
  have squareUpper : time ^ 2 ≤ 1 := by
    calc
      time ^ 2 = time * time := pow_two time
      _ ≤ 1 * time := Arithmetic.mul_le_mul_of_nonneg_right_direct upper nonnegative
      _ = time := Fraction.Field.one_mul time
      _ ≤ 1 := upper
  have positive := Arithmetic.mul_nonneg_direct
    (Arithmetic.pow_nonneg_direct nonnegative 2)
    (Arithmetic.sub_nonneg_direct squareUpper)
  apply (Fraction.Order.Field.le_div_iff_pos (by decide +kernel : (0 : Fraction.Rational) < 9)).mpr
  have triple := Fraction.Field.div_mul_cancel_of_ne (1 - 2 * time ^ 2) 3
    (by decide +kernel : (3 : Fraction.Rational) ≠ 0)
  have identity : Norm.Basic.normSq (⟨(1 - 2 * time ^ 2) / 3, 0⟩ : Canonical) * 9 =
      1 - 4 * (time ^ 2 * (1 - time ^ 2)) := by
    change (((1 - 2 * time ^ 2) / 3) ^ 2 + 0 ^ 2) * 9 = _
    calc
      _ = (((1 - 2 * time ^ 2) / 3) * 3) ^ 2 := by ring1
      _ = _ := by rw [triple]; ring1
  rw [identity]
  have estimate := Arithmetic.sub_le_sub_left_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 4) positive) 1
  rw [show (1 : Fraction.Rational) - 0 = 1 by decide +kernel] at estimate
  exact estimate

/-- The same original denominator identifies the rational Cayley reading with the actual logarithmic tangent.

The bounded substitution certifies a nonzero Cayley denominator. Clearing
that same denominator recovers the original tangent's retained numerator.
-/
theorem logarithmicVelocity_eq_chart (time : Fraction.Rational)
    (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    Tangent.logarithmicVelocity time = (⟨0, 2 / 3⟩ : Canonical) *
      ((1 + GaussianEvaluation.eval substitution ⟨time, 0⟩) /
        (1 - GaussianEvaluation.eval substitution ⟨time, 0⟩) + 1) := by
  let z := GaussianEvaluation.eval substitution ⟨time, 0⟩
  have nonzero : 1 - z ≠ 0 := Projective.Homography.Cayley.Bounds.one_sub_ne_zero
    (substitution_normSq_le time nonnegative upper)
  have denominator : 1 - z = (⟨2 / 3, 0⟩ : Canonical) * unitCircleDenominator time := by
    rw [show z = (⟨(1 - 2 * time ^ 2) / 3, 0⟩ : Canonical) from substitution_eval time]
    apply Data.Gaussian.Basic.ext
    · change 1 - (1 - 2 * time ^ 2) / 3 = (2 / 3) * (time ^ 2 + 1) - 0 * 0
      apply ExplicitField.eq_of_mul_eq_mul_right (by decide +kernel : (3 : Fraction.Rational) ≠ 0)
      calc
        _ = 3 - ((1 - 2 * time ^ 2) / 3) * 3 := by ring1
        _ = 3 - (1 - 2 * time ^ 2) := by
          rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)]
        _ = ((2 / 3 : Fraction.Rational) * 3) * (time ^ 2 + 1) := by
          rw [show (2 / 3 : Fraction.Rational) * 3 = 2 by decide +kernel]
          ring1
        _ = _ := by ring1
    · change 0 - 0 = (2 / 3) * 0 + 0 * (time ^ 2 + 1)
      ring1
  apply ExplicitField.eq_of_mul_eq_mul_right nonzero
  calc
    Tangent.logarithmicVelocity time * (1 - z) =
        (⟨2 / 3, 0⟩ : Canonical) * (Tangent.logarithmicVelocity time * unitCircleDenominator time) := by
      rw [denominator]
      ring1
    _ = (⟨0, 2 / 3⟩ : Canonical) * 2 := by
      rw [Tangent.logarithmicVelocity_mul_denominator]
      decide +kernel
    _ = ((⟨0, 2 / 3⟩ : Canonical) * ((1 + z) / (1 - z) + 1)) * (1 - z) := by
      have cleared := ExplicitField.div_mul_cancel (1 + z) nonzero
      calc
        _ = (⟨0, 2 / 3⟩ : Canonical) * ((1 + z) + (1 - z)) := by ring1
        _ = (⟨0, 2 / 3⟩ : Canonical) * (((1 + z) / (1 - z)) * (1 - z) + (1 - z)) := by
          rw [cleared]
        _ = _ := by ring1

/-- A finite original Cayley prefix, substituted once into the retained real quadratic. -/
@[expose] def polynomial (degree : Nat) : Ascending.Gaussian.CoefficientPolynomial :=
  Ascending.Gaussian.Arithmetic.scale (⟨0, 2 / 3⟩ : Canonical)
    (Ascending.Gaussian.RationalEmbedding.Basic.ofRational
      (Ascending.Rational.Basic.add
        (Ascending.Rational.Composition.compose (Ascending.Rational.Geometric.geometricPrefix degree) substitution)
        (Ascending.Rational.Basic.constant 1)))

/-- The finite tangent polynomial reads the same original geometric prefix at the cached substitution. -/
theorem polynomial_eval (degree : Nat) (time : Fraction.Rational) :
    Evaluation.eval (polynomial degree) ⟨time, 0⟩ =
      (⟨0, 2 / 3⟩ : Canonical) *
        (GaussianEvaluation.eval (Ascending.Rational.Geometric.geometricPrefix degree)
          (GaussianEvaluation.eval substitution ⟨time, 0⟩) + 1) := by
  rw [polynomial, Evaluation.eval_scale,
    Ascending.Gaussian.RationalEmbedding.Evaluation.eval_ofRational,
    GaussianEvaluation.eval_add,
    GaussianEvaluation.Composition.eval_compose]
  have constant : GaussianEvaluation.eval (Ascending.Rational.Basic.constant 1)
      (⟨time, 0⟩ : Canonical) = 1 := by
    change Scale.scale 1 1 + (⟨time, 0⟩ : Canonical) * 0 = 1
    rw [Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.add_zero]
    decide +kernel
  rw [constant]

/-- The actual logarithmic tangent and its retained finite polynomial have an explicit geometric squared-error bound.

The original finite Cayley-prefix remainder is scaled by the same Gaussian
factor as the retained polynomial. Both readings use the same substitution.
-/
theorem polynomial_error_le (degree : Nat) (time : Fraction.Rational)
    (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    Norm.Basic.normSq
      (Evaluation.eval (polynomial degree) ⟨time, 0⟩ - Tangent.logarithmicVelocity time) ≤
        4 * (1 / 9 : Fraction.Rational) ^ (degree + 1) := by
  rw [polynomial_eval, logarithmicVelocity_eq_chart time nonnegative upper]
  have difference (left right : Canonical) :
      (⟨0, 2 / 3⟩ : Canonical) * (left + 1) - (⟨0, 2 / 3⟩ : Canonical) * (right + 1) =
        (⟨0, 2 / 3⟩ : Canonical) * (left - right) := by ring1
  rw [difference, Norm.Basic.normSq_mul, show Norm.Basic.normSq (⟨0, 2 / 3⟩ : Canonical) = 4 / 9 by decide +kernel]
  have estimate := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Ascending.Rational.Geometric.Cayley.geometricPrefix_chart_error
      (substitution_normSq_le time nonnegative upper) degree) (by decide +kernel : (0 : Fraction.Rational) ≤ 4 / 9)
  calc
    _ ≤ (4 / 9 : Fraction.Rational) * (9 * (1 / 9 : Fraction.Rational) ^ (degree + 1)) := estimate
    _ = ((4 / 9 : Fraction.Rational) * 9) * (1 / 9 : Fraction.Rational) ^ (degree + 1) := by ring1
    _ = _ := by rw [show (4 / 9 : Fraction.Rational) * 9 = 4 by decide +kernel]

/-- The finite squared-error allowance of the original logarithmic-tangent polynomial stage. -/
@[expose] def allowance (index : Nat) : Fraction.Rational :=
  Geometric.Basic.quarterRadius (1 / 256) index

/-- Every retained stage allowance is nonnegative. -/
theorem allowance_nonnegative (index : Nat) : 0 ≤ allowance index :=
  Geometric.Basic.quarterRadius_nonneg (by decide +kernel) index

/-- The displayed stage shift gives the original tangent polynomial its retained quarter-radius allowance.

The degree offset four pays the fixed scale `1/256`; the original finite
Cayley remainder decreases at least as fast as the same quarter schedule.
-/
theorem stage_error_le (index : Nat) (time : Fraction.Rational)
    (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    Norm.Basic.normSq
      (Evaluation.eval (polynomial (index + 4)) ⟨time, 0⟩ - Tangent.logarithmicVelocity time) ≤
        allowance index := by
  have powerBound := Arithmetic.pow_le_pow_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1 / 9)
    (by decide +kernel : (1 / 9 : Fraction.Rational) ≤ 1 / 4) (index + 4 + 1)
  calc
    _ ≤ 4 * (1 / 9 : Fraction.Rational) ^ (index + 4 + 1) :=
      polynomial_error_le (index + 4) time nonnegative upper
    _ ≤ 4 * (1 / 4 : Fraction.Rational) ^ (index + 4 + 1) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct powerBound (by decide +kernel)
    _ = (4 * (1 / 4 : Fraction.Rational) ^ 5) * (1 / 4 : Fraction.Rational) ^ index := by
      rw [show index + 4 + 1 = index + 5 from rfl, pow_add]
      ring1
    _ = allowance index := by
      rw [show (4 * (1 / 4 : Fraction.Rational) ^ 5) = 1 / 256 by decide +kernel,
        allowance, Geometric.Basic.quarterRadius_eq_mul_pow]

/-- One retained tangent polynomial and its actual original endpoint observations form the stage's integration cell.

The coefficient table is computed once and shared by the cell and its two
actual supplied-integrand residual observations. The supplied pointwise
identity derives the same global logarithmic-tangent error bound. The
original logarithmic velocity is retained as the literal default.
-/
@[expose] def cell (index : Nat)
    (integrand : Fraction.Rational → Canonical := Tangent.logarithmicVelocity)
    (integrand_eq : ∀ time, integrand time = Tangent.logarithmicVelocity time := by intro; rfl) : CellModel :=
  let retained := polynomial (index + 4)
  let ceiling := allowance index
  let observe (time : Fraction.Rational) (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
      LocalObservation retained ceiling :=
    let reading := integrand time
    { parameter := time
      integrandReading := reading
      error := reading - Evaluation.eval retained ⟨time, 0⟩
      decomposition := rfl
      error_le := by
        rw [← Norm.Basic.normSq_eq_canonical, Norm.Bounds.normSq_sub_symm]
        have reading_eq : reading = Tangent.logarithmicVelocity time := integrand_eq time
        rw [reading_eq]
        exact stage_error_le index time nonnegative upper }
  { start := 0
    finish := 1
    polynomial := retained
    localAllowance := ceiling
    localAllowance_nonneg := allowance_nonnegative index
    observations := [observe 0 (by decide +kernel) (by decide +kernel),
      observe 1 (by decide +kernel) (by decide +kernel)] }

/-- The retained stage cell integrates precisely its original finite tangent polynomial. -/
theorem cell_integralSample (index : Nat)
    (integrand : Fraction.Rational → Canonical := Tangent.logarithmicVelocity)
    (integrand_eq : ∀ time, integrand time = Tangent.logarithmicVelocity time := by intro; rfl) :
    (cell index integrand integrand_eq).integralSample =
      Ascending.Gaussian.Integral.definiteIntegral (polynomial (index + 4)) 0 1 := by
  change ((1 : Canonical) - 0) * _ = _
  rw [Data.Gaussian.Basic.sub_zero, Data.Gaussian.Basic.one_mul]
  rfl

/-- The original ordered stage path retains its actual single integration cell. -/
@[expose] def model (index : Nat)
    (integrand : Fraction.Rational → Canonical := Tangent.logarithmicVelocity)
    (integrand_eq : ∀ time, integrand time = Tangent.logarithmicVelocity time := by intro; rfl) : PathModel :=
  ⟨[cell index integrand integrand_eq]⟩

/-- The original path's integral sample is the integral of its retained tangent polynomial. -/
theorem model_integralSample (index : Nat)
    (integrand : Fraction.Rational → Canonical := Tangent.logarithmicVelocity)
    (integrand_eq : ∀ time, integrand time = Tangent.logarithmicVelocity time := by intro; rfl) :
    (model index integrand integrand_eq).integralSample =
      Ascending.Gaussian.Integral.definiteIntegral (polynomial (index + 4)) 0 1 := by
  rw [model, PathModel.singleton_integralSample, cell_integralSample index integrand integrand_eq]

/-- The stage path retains precisely the uniform tangent-error allowance. -/
theorem model_aggregateAllowance (index : Nat)
    (integrand : Fraction.Rational → Canonical := Tangent.logarithmicVelocity)
    (integrand_eq : ∀ time, integrand time = Tangent.logarithmicVelocity time := by intro; rfl) :
    (model index integrand integrand_eq).aggregateAllowance = allowance index := by
  change (1 : Fraction.Rational) *
    (Data.Gaussian.Basic.Canonical.normSq ((1 : Canonical) - 0) * allowance index + 0) = _
  rw [Data.Gaussian.Basic.sub_zero, show Data.Gaussian.Basic.Canonical.normSq (1 : Canonical) = 1 by decide +kernel]
  ring1

/-- Every later retained polynomial differs pointwise from the earlier one by their paid original tangent errors. -/
theorem polynomial_later_close {earlier later : Nat} (order : earlier ≤ later)
    (time : Fraction.Rational) (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    Norm.Basic.normSq
      (Evaluation.eval (polynomial (later + 4)) ⟨time, 0⟩ -
        Evaluation.eval (polynomial (earlier + 4)) ⟨time, 0⟩) ≤ 4 * allowance earlier := by
  have laterBound := (stage_error_le later time nonnegative upper).trans
    (Geometric.Basic.quarterRadius_antitone (by decide +kernel) order)
  have earlierBound := stage_error_le earlier time nonnegative upper
  have estimate := Norm.Bounds.normSq_sub_le_via
    (Evaluation.eval (polynomial (later + 4)) ⟨time, 0⟩) (Tangent.logarithmicVelocity time)
    (Evaluation.eval (polynomial (earlier + 4)) ⟨time, 0⟩)
  rw [Norm.Bounds.normSq_sub_symm (Tangent.logarithmicVelocity time)] at estimate
  calc
    _ ≤ _ := estimate
    _ ≤ 2 * (allowance earlier + allowance earlier) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct laterBound earlierBound) (by decide +kernel)
    _ = _ := by ring1

/-- Later actual polynomial integrals obey the original finite quarter-radius movement contract.

The actual difference polynomial is integrated through the original cell's
zero-primitive comparison. Its uniform bound uses both original tangent
errors and the retained order between their finite stages.
-/
theorem sample_later_close {earlier later : Nat} (order : earlier ≤ later) :
    Norm.Basic.normSq ((model later).integralSample - (model earlier).integralSample) ≤
      Geometric.Basic.quarterRadius (1 / 16) earlier := by
  let difference := Ascending.Gaussian.Arithmetic.add (polynomial (later + 4))
    (Ascending.Gaussian.Arithmetic.scale (-1) (polynomial (earlier + 4)))
  let differenceCell := CellModel.exact 0 1 difference
  have readback : differenceCell.integralSample = (model later).integralSample - (model earlier).integralSample := by
    dsimp only [differenceCell]
    rw [CellModel.exact_integralSample, model_integralSample, model_integralSample,
      Data.Gaussian.Basic.sub_zero, Data.Gaussian.Basic.one_mul]
    dsimp only [difference]
    rw [Ascending.Gaussian.Integral.definiteIntegral_add,
      Ascending.Gaussian.Integral.definiteIntegral_scale]
    ring1
  have estimate := Integration.Polynomial.Gaussian.Cell.Primitive.integral_normSq_le differenceCell
    (4 * allowance earlier) (by
      intro time inside
      change Norm.Basic.normSq (((1 : Canonical) - 0) *
        Evaluation.eval difference ⟨time, 0⟩) ≤ _
      rw [Data.Gaussian.Basic.sub_zero, Data.Gaussian.Basic.one_mul]
      dsimp only [difference]
      rw [Evaluation.eval_add,
        Evaluation.eval_scale]
      have reading :
          Evaluation.eval (polynomial (later + 4)) ⟨time, 0⟩ +
              (-1 : Canonical) * Evaluation.eval (polynomial (earlier + 4)) ⟨time, 0⟩ =
            Evaluation.eval (polynomial (later + 4)) ⟨time, 0⟩ -
              Evaluation.eval (polynomial (earlier + 4)) ⟨time, 0⟩ := by ring1
      rw [reading]
      exact polynomial_later_close order time inside.1 inside.2)
  rw [readback] at estimate
  calc
    _ ≤ 2 * (4 * allowance earlier) := estimate
    _ = Geometric.Basic.quarterRadius (1 / 32) earlier := by
      rw [allowance, Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      calc
        _ = (8 * (1 / 256 : Fraction.Rational)) * (1 / 4 : Fraction.Rational) ^ earlier := by ring1
        _ = _ := by rw [show (8 * (1 / 256 : Fraction.Rational)) = 1 / 32 by decide +kernel]
    _ ≤ _ := Geometric.Basic.quarterRadius_scale_mono (by decide +kernel) earlier

/-- The retained finite tangent polynomials have a common pointwise quadrance ceiling.

The same original tangent has quadrance at most four. Its actual retained
polynomial residual pays the remaining finite margin on the unit interval.
-/
theorem polynomial_normSq_le (index : Nat) (time : Fraction.Rational)
    (nonnegative : 0 ≤ time) (upper : time ≤ 1) :
    Norm.Basic.normSq (Evaluation.eval (polynomial (index + 4)) ⟨time, 0⟩) ≤ 9 := by
  have errorBound := (stage_error_le index time nonnegative upper).trans
    (Geometric.Basic.quarterRadius_le_scale (by decide +kernel) index)
  have decomposition : Evaluation.eval (polynomial (index + 4)) ⟨time, 0⟩ =
      (Evaluation.eval (polynomial (index + 4)) ⟨time, 0⟩ - Tangent.logarithmicVelocity time) +
        Tangent.logarithmicVelocity time := by ring1
  calc
    _ = _ := congrArg Norm.Basic.normSq decomposition
    _ ≤ _ := Norm.Bounds.normSq_add_le_two _ _
    _ ≤ 2 * ((1 / 256 : Fraction.Rational) + 4) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct errorBound (Tangent.logarithmicVelocity_normSq_le time))
        (by decide +kernel)
    _ ≤ 9 := by decide +kernel

/-- Every actual retained polynomial integral has the same finite quadrance ceiling.

The original cell's finite primitive comparison integrates its actual
pointwise polynomial bound. No analytic integration assertion is supplied.
-/
theorem sample_normSq_le (index : Nat) : Norm.Basic.normSq (model index).integralSample ≤ 18 := by
  have estimate := Integration.Polynomial.Gaussian.Cell.Primitive.integral_normSq_le (cell index) 9 (by
    intro time inside
    change Norm.Basic.normSq (((1 : Canonical) - 0) *
      Evaluation.eval (polynomial (index + 4)) ⟨time, 0⟩) ≤ 9
    rw [Data.Gaussian.Basic.sub_zero, Data.Gaussian.Basic.one_mul]
    exact polynomial_normSq_le index time inside.1 inside.2)
  change Norm.Basic.normSq (cell index).integralSample ≤ (18 : Fraction.Rational) at estimate
  rw [model, PathModel.singleton_integralSample]
  exact estimate

/-- The actual logarithmic quarter-circle integral as an original certified finite refinement program.

Each stage integrates its retained Cayley polynomial, with original endpoint
observations, a uniform error bound against the actual tangent and the same
finite movement and center certificates.
-/
@[expose] def program : RefinementProgram where
  model := model
  errorScale := 1 / 16
  errorScale_nonneg := by decide +kernel
  modelAllowance_le := by
    intro index
    rw [model_aggregateAllowance]
    exact Geometric.Basic.quarterRadius_scale_mono (by decide +kernel) index
  later_close := by
    intro earlier later order
    rw [← Norm.Basic.normSq_eq_canonical]
    exact sample_later_close order
  centerBound := 18
  centerBound_nonneg := by decide +kernel
  sample_bounded := by
    intro index
    rw [← Norm.Basic.normSq_eq_canonical]
    exact sample_normSq_le index

/-- The original initial tangent stage has its displayed finite coefficient table.

The complete original Horner construction retains eleven entries, including
its two trailing zeros. Kernel decision verifies this literal table.
-/
private theorem initial_polynomial : polynomial 4 =
    ⟨[⟨0, 484 / 243⟩, 0, ⟨0, -464 / 243⟩, 0, ⟨0, 128 / 81⟩, 0, ⟨0, -224 / 243⟩, 0, ⟨0, 64 / 243⟩, 0, 0]⟩ := by
  decide +kernel

/-- The original initial sample's displayed scalar reads the same two direct denominator-one integer records. -/
private theorem initial_scalar : (17156 / 10935 : Fraction.Rational) =
    Fraction.Cast.fromInt 17156 / Fraction.Cast.fromInt 10935 := by
  have numerator : (17156 : Fraction.Rational) = Fraction.Cast.fromInt 17156 := by
    simpa only [Nat.cast_ofNat] using Fraction.Cast.natCast_eq_fromInt 17156
  have denominator : (10935 : Fraction.Rational) = Fraction.Cast.fromInt 10935 := by
    simpa only [Nat.cast_ofNat] using Fraction.Cast.natCast_eq_fromInt 10935
  rw [numerator, denominator]

/-- The initial retained tangent polynomial integral has its exact nonzero imaginary reading. -/
theorem initial_sample : (program.model 0).integralSample = (⟨0, 17156 / 10935⟩ : Canonical) := by
  change (model 0).integralSample = _
  rw [model_integralSample, show 0 + 4 = 4 from rfl, initial_polynomial, initial_scalar]
  decide +kernel

/-- The actual coherent CCL channel of the original retained quarter-integral samples. -/
@[expose] def channel : CoherentNamed := Preparation.sampledChannel program.geometric

/-- The actual initial quarter-integral observation certifies whole-ball separation from zero. -/
theorem initial_separated :
    let state := Refinement.State.initial channel
    2 * (channel.name.process.ball state.source).radiusSq <
      Norm.Basic.normSq (channel.name.process.ball state.source).center := by
  change 2 * Geometric.Basic.quarterRadius (1 / 16) 0 < Norm.Basic.normSq (program.model 0).integralSample
  rw [initial_sample, initial_scalar]
  decide +kernel

/-- Prepare the actual quarter-integral channel by consuming its original initial cached observation.

The denominator certificate comes from the same program's actual first
sample and its paid geometric ball. No separate winding value, fresh
integral channel or assumed nonzero comparison replaces that observation.
-/
@[expose] def prepared : Prepared channel :=
  let source := program.geometric
  let state := Refinement.State.initial channel
  let ball := channel.name.process.ball state.source
  Preparation.fromBall source channel (NamedEquivalent.refl channel.name) state ball rfl initial_separated

end Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Integral
