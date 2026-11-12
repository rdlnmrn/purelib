module

public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Finite polynomial refinement of an inverse square root

Newton--Schulz refinement uses polynomial multiplication only.  A cached
residual `e = 1 - P q²` is updated alongside `q`; it is not recomputed from
scratch.  A small residual contracts by an explicit rational factor at every
finite step.  No infinite series or completed square root is used.

The semantic cache interface also accepts generated polynomial data checked
by the same exact equations and bounds.  Residual control alone does not
identify a sheet; that identification must retain the initial root owner.
-/

namespace Purelib.Riemann.Normalization.InverseRootPolynomial

section
open Purelib.Data
/-- The rational scalar type for inverse-root coordinates and bounds. -/
abbrev Coordinate := Rat.Fraction.Rational
/-- The executable Gaussian rational type for inverse-root evaluations. -/
abbrev Gaussian := Gaussian.Basic.Canonical
end

open Purelib.Polynomial in
/-- The dense Gaussian polynomial type used by the inverse-root cache. -/
abbrev Polynomial := Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Geometry in
/-- The rational coordinate box on which the inverse-root cache is certified. -/
abbrev Box := Rational.Box

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial

section
open Purelib.Data
/-- The Gaussian rational scalar one half. -/
@[expose] def half : Gaussian.Basic.Canonical := ⟨1 / 2, 0⟩

/-- Apply the Newton–Schulz value update using the retained square residual. -/
@[expose] def correction (value residual : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical := value * (1 + half *
  residual)

/-- Compute the polynomial residual update e squared times (3 plus e), divided by four. -/
@[expose] def residualStep (residual : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical := residual ^ 2 * (3 +
  residual) * half ^ 2

end

section
open Purelib.Riemann
open Purelib.Data
/-- The Newton–Schulz value correction has the displayed exact polynomial residual update.

The retained input residual equals one minus the parameter times the value squared. -/
theorem correction_residual (parameter value residual : Gaussian.Basic.Canonical)
    (residual_eq : residual = 1 - parameter * value ^ 2) :
    1 - parameter * correction value residual ^ 2 =
      residualStep residual := by
  have twice : (2 : Gaussian.Basic.Canonical) * half = 1 := by decide
  have squared : (4 : Gaussian.Basic.Canonical) * half ^ 2 = 1 := by decide
  calc
    _ = residualStep residual + residual * (1 - 2 * half) +
        residual ^ 2 * (2 * half - 4 * half ^ 2) := by
      rw [residual_eq]
      unfold correction residualStep
      ring1
    _ = residualStep residual := by rw [twice, squared]; ring1

/-- A square residual of quadrance at most one sixteenth contracts by a factor of at least four.

The estimate applies to the exact finite polynomial residual update. -/
theorem residualStep_contracts {residual : Gaussian.Basic.Canonical}
    (small : normSq residual <= 1 / 16) :
    normSq (residualStep residual) <=
      normSq residual / 4 := by
  have residualNonnegative := normSq_nonneg residual
  have residualLeOne : normSq residual <= 1 := small.trans (by decide)
  have factorBound : normSq ((3 : Gaussian.Basic.Canonical) + residual) <= 20 := by
    calc
      _ <= 2 * (normSq (3 : Gaussian.Basic.Canonical) + normSq
        residual) := by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
          Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ <= 2 * (9 + 1) := Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (le_of_eq (by decide)) residualLeOne) (by decide)
      _ = 20 := by decide
  have scaledSmall : normSq residual * 16 <= 1 :=
    (Field.le_div_iff_pos (by decide : (0 : Rat.Fraction.Rational) < 16)).1 small
  have numeratorBound : normSq residual ^ 2 * 20 <= normSq residual *
    4 := by
    calc
      _ <= normSq residual ^ 2 * 64 :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
        (show (20 : Rat.Fraction.Rational) <= 64 by decide +kernel) (Arithmetic.sq_nonneg_direct _)
      _ = (normSq residual * 16) * (normSq residual * 4) := by ring1
      _ <= 1 * (normSq residual * 4) :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct
        scaledSmall (Arithmetic.mul_nonneg_direct residualNonnegative (by decide))
      _ = normSq residual * 4 := Rat.Fraction.Field.one_mul _
  calc
    normSq (residualStep residual) =
      normSq residual ^ 2 * normSq (3 + residual) * (1 / 16) := by
      unfold residualStep
      rw [pow_two residual, pow_two half,
        normSq_mul, normSq_mul,
        normSq_mul, normSq_mul]
      have halfNorm : normSq half = (1 / 4 : Rat.Fraction.Rational) := by decide
      rw [halfNorm]
      rw [show (1 / 4 : Rat.Fraction.Rational) * (1 / 4) = 1 / 16 by decide]
      ring1
    _ <= normSq residual ^ 2 * 20 * (1 / 16) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.mul_le_mul_of_nonneg_left_direct factorBound
          (Arithmetic.sq_nonneg_direct _)) (by decide)
    _ <= (normSq residual * 4) * (1 / 16) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct numeratorBound (by decide)
    _ = normSq residual * (4 * (1 / 16)) := by ring1
    _ = normSq residual * (1 / 4) := by rw [show (4 : Rat.Fraction.Rational) * (1 / 16) = 1 / 4
      by decide]
    _ = normSq residual / 4 := by
      rewrite [Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.one_mul]
      exact Eq.refl _

end

open Purelib.Data in
set_option genInjectivity false in
/-- Cached polynomial value and residual with a uniform small quadrance bound on a rational box.

The residual equation is pointwise, allowing any coefficient representation satisfying the exact identity. The
nonnegative bound is at most one sixteenth. -/
structure Model (polynomial : Polynomial) (box : Box) where
  /-- The retained polynomial approximation to the inverse square root. -/ value : Polynomial
  /-- The retained polynomial residual, updated alongside the value. -/ residual : Polynomial
  /-- At every point the residual is one minus the source value times the cached value squared. -/ residual_eq : forall
    point, residual.eval point = 1 - polynomial.eval point * (value.eval point) ^ 2
  /-- The uniform rational bound for residual quadrance on the box. -/ bound : Rat.Fraction.Rational
  /-- The retained quadrance bound is nonnegative. -/ bound_nonnegative : 0 <= bound
  /-- The retained bound is at most one sixteenth. -/ bound_small : bound <= 1 / 16
  /-- Every point in the box satisfies the retained residual quadrance bound. -/ residualBound : forall point,
    box.Contains point -> normSq (residual.eval point) <= bound

constructive_injectivity Model

namespace Model

variable {polynomial : Polynomial} {box : Box}

open Purelib.Data in
open Purelib.Polynomial in
/-- Construct the initial polynomial cache from a constant inverse-root seed.

The supplied pointwise proof bounds the seed's residual quadrance by one sixteenth throughout the same box. -/
@[expose] def ofSeed (polynomial : Polynomial) (box : Box) (seed : Gaussian.Basic.Canonical)
    (small : forall point, box.Contains point -> normSq (1 - polynomial.eval point * seed ^ 2)
      <= 1 / 16) :
    Model polynomial box where
  value := constant seed
  residual := constant 1 - polynomial * constant (seed ^ 2)
  residual_eq := fun point => by
    rw [eval_sub, eval_mul,
      eval_constant, eval_constant,
      eval_constant]
  bound := 1 / 16
  bound_nonnegative := by decide
  bound_small := le_rfl
  residualBound := fun point inside => by
    simpa only [eval_sub, eval_mul,
      eval_constant] using small point inside

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- Refine the polynomial value and residual together by one Newton–Schulz step.

Consume the retained residual directly in both updates, preserve its exact equation, and divide the uniform bound by
four. -/
@[expose] def step (model : Model polynomial box) : Model polynomial box :=
  { value := model.value * (constant 1 + model.residual.scale half)
    residual := (model.residual * model.residual * (constant 3 + model.residual)).scale
      (half ^ 2)
    residual_eq := fun point => by
      simp only [eval_mul, eval_add,
        eval_constant, eval_scale]
      have identity := correction_residual (polynomial.eval point) (model.value.eval
        point)
        (model.residual.eval point) (model.residual_eq point)
      unfold correction residualStep at identity
      exact (by ring1 : half ^ 2 *
          (model.residual.eval point * model.residual.eval point * (3 + model.residual.eval point)) =
        model.residual.eval point ^ 2 * (3 + model.residual.eval point) * half ^ 2).trans identity.symm
    bound := model.bound / 4
    bound_nonnegative := Field.div_nonneg_direct model.bound_nonnegative (by decide)
    bound_small := by
      have divided := Arithmetic.mul_le_mul_of_nonneg_right_direct model.bound_small
        (by decide : (0 : Rat.Fraction.Rational) <= (4 : Rat.Fraction.Rational)⁻¹)
      have small : model.bound / 4 <= (1 / 16 : Rat.Fraction.Rational) / 4 := by
        simpa only [Rat.Fraction.Field.div_eq_mul_inv_direct] using divided
      exact small.trans (by decide)
    residualBound := fun point inside => by
      have initial := model.residualBound point inside
      have contracted := residualStep_contracts (initial.trans model.bound_small)
      have divided := Arithmetic.mul_le_mul_of_nonneg_right_direct initial
        (by decide : (0 : Rat.Fraction.Rational) <= (4 : Rat.Fraction.Rational)⁻¹)
      have comparison : normSq (model.residual.eval point) / 4 <= model.bound / 4 := by
        simpa only [Rat.Fraction.Field.div_eq_mul_inv_direct] using divided
      have evaluation :
          ((model.residual * model.residual * (constant 3 + model.residual)).scale (half ^
            2)).eval point =
            residualStep (model.residual.eval point) := by
        simp only [eval_scale, eval_mul,
          eval_add, eval_constant,
          residualStep]
        ring1
      rw [evaluation]
      exact contracted.trans comparison }

/-- A single polynomial refinement divides the retained bound by four. -/
@[simp] theorem step_bound (model : Model polynomial box) : model.step.bound = model.bound / 4 := rfl

/-- Perform the requested finite number of cached polynomial refinement steps. -/
@[expose] def refine (model : Model polynomial box) : Nat -> Model polynomial box
  | 0 => model
  | index + 1 => (refine model index).step

/-- Two finite refinements read the same original model at the sum of their actual indices. -/
theorem refine_add (model : Model polynomial box) (first last : Nat) :
    (model.refine first).refine last = model.refine (first + last) := by
  induction last with
  | zero => rfl
  | succ last ih =>
      change ((model.refine first).refine last).step = (model.refine (first + last)).step
      exact congrArg Model.step ih

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- The bound after finite refinement is the initial bound times the corresponding power of one quarter. -/
theorem refine_bound (model : Model polynomial box) (index : Nat) :
    (model.refine index).bound = Rational.Geometric.Basic.quarterRadius model.bound index := by
  induction index with
  | zero =>
      rw [refine,
        Rational.Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero,
        Rat.Fraction.Field.mul_one_direct]
  | succ index inductionHypothesis =>
      rw [refine, step_bound,
        inductionHypothesis]
      simp only [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ,
        Rat.Fraction.Field.div_eq_mul_inv_direct, Rat.Fraction.Field.one_mul]
      ring1

open Purelib.Approximation in
open Purelib.Data in
/-- Every finite refinement satisfies its explicit geometric residual bound on the original box.

The evaluated error uses the same retained source polynomial and refined value cache. -/
theorem refine_residualBound (model : Model polynomial box) (index : Nat)
    (point : Gaussian.Basic.Canonical) (inside : box.Contains point) :
    normSq (1 - polynomial.eval point * ((model.refine index).value.eval point) ^ 2) <=
      Rational.Geometric.Basic.quarterRadius model.bound index := by
  rw [<- (model.refine index).residual_eq, <- model.refine_bound]
  exact (model.refine index).residualBound point inside

open Purelib.Polynomial.Dense.Basic in
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense in
/-- Equal inverse-model values at a point remain equal after synchronized Newton refinement.

The two models may use different boxes; their initial scalar equality is
retained at the same point through every common refinement index. -/
theorem refine_eval_eq {polynomial : Polynomial} {leftBox rightBox : Box}
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) (point : Gaussian)
    (equal : left.value.eval point = right.value.eval point) (index : Nat) :
    (left.refine index).value.eval point = (right.refine index).value.eval point := by
  induction index with
  | zero => exact equal
  | succ index ih =>
      simp only [refine, step, eval_mul,
        eval_add, eval_constant,
        eval_scale, Model.residual_eq, ih, -eq_self]
      rfl

end Model

end Purelib.Riemann.Normalization.InverseRootPolynomial
