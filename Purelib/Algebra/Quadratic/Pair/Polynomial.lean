module

public import Purelib.Algebra.Quadratic.Pair.Norm
public import Purelib.Polynomial.Dense.Gaussian.Multiplication
import Purelib.Polynomial.Dense.Gaussian.Extensionality
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Bool.Decide
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Quadratic pairs with retained polynomial denominators

The numerator uses the original quadratic pair owner, with parameter minus
the radicand. A common displayed denominator gives exact finite expressions
without quotient carriers or root selection. Coefficient equality clears the
original denominators; numerical readback separately requires their guards.
-/

public section

namespace Purelib.Algebra.Quadratic.Pair.Polynomial

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Algebra.Field (ExplicitField)

/-- The finite descending Gaussian coefficient tables used by quadratic expressions. -/
abbrev Coefficients := DensePolynomial Canonical

set_option genInjectivity false in
/-- A displayed quadratic polynomial pair divided by one retained polynomial.

The original pair parameter is minus the indexed radicand, so its generator
squares to that radicand. Definedness retains the displayed denominator even
when its polynomial factors could be cancelled. -/
structure Expression (radicand : Coefficients) where
  /-- The original quadratic pair of polynomial numerators. -/
  numerator : Pair Coefficients (-radicand)
  /-- The original displayed common polynomial denominator. -/
  denominator : Coefficients

constructive_injectivity Expression

namespace Expression

variable {radicand : Coefficients}

/-- Embed a polynomial coefficient with a displayed unit denominator. -/
@[expose] def scalar (value : Coefficients) : Expression radicand :=
  ⟨Pair.scalar value, DensePolynomial.constant 1⟩

/-- The zero expression retains a displayed unit denominator. -/
@[expose] def zero : Expression radicand := scalar 0

/-- The unit expression retains a displayed unit numerator and denominator. -/
@[expose] def one : Expression radicand := scalar (DensePolynomial.constant 1)

/-- The original formal generator has coordinates zero and one. -/
@[expose] def generator : Expression radicand :=
  ⟨⟨0, DensePolynomial.constant 1⟩, DensePolynomial.constant 1⟩

/-- Add expressions by retaining the product of both original denominators. -/
@[expose] def add (left right : Expression radicand) : Expression radicand :=
  ⟨Pair.scale right.denominator left.numerator + Pair.scale left.denominator right.numerator,
    left.denominator * right.denominator⟩

/-- Multiply expressions in the original nominal quadratic pair algebra. -/
@[expose] def mul (left right : Expression radicand) : Expression radicand :=
  ⟨left.numerator * right.numerator, left.denominator * right.denominator⟩

/-- Negate both numerator coordinates while preserving the original denominator. -/
@[expose] def neg (value : Expression radicand) : Expression radicand :=
  ⟨-value.numerator, value.denominator⟩

/-- Subtract expressions through the same denominator-preserving addition. -/
@[expose] def sub (left right : Expression radicand) : Expression radicand :=
  left.add right.neg

/-- Multiply both numerator coordinates by one retained polynomial coefficient. -/
@[expose] def scale (factor : Coefficients) (value : Expression radicand) : Expression radicand :=
  ⟨Pair.scale factor value.numerator, value.denominator⟩

/-- The original displayed denominator is nonzero at the retained coordinate. -/
@[expose] def Defined (value : Expression radicand) (point : Canonical) : Prop :=
  value.denominator.eval point ≠ 0

/-- An admitted original quotient cannot have the identically zero denominator.

The retained coordinate guard contradicts zero evaluation of a coefficient-zero
denominator. This does not admit a cancelled extension at another coordinate.
-/
theorem Defined.denominator_nonzero {value : Expression radicand} {point : Canonical}
    (defined : value.Defined point) : value.denominator.isZero = false := by
  by_cases zero : value.denominator.isZero = true
  · exact (defined (DensePolynomial.eval_eq_zero_of_isZero zero point)).elim
  · exact Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true _ zero

/-- The original displayed denominator guard has an exact executable decision. -/
instance (value : Expression radicand) (point : Canonical) : Decidable (value.Defined point) :=
  inferInstanceAs (Decidable (value.denominator.eval point ≠ 0))

/-- Read both divided coefficients into the original scalar pair at the same radicand evaluation.

This is a total scalar calculation; interpretation as the original quotient
requires the separate `Defined` certificate. -/
@[expose] def evaluate (value : Expression radicand) (point : Canonical) : Pair Canonical (-radicand.eval point) :=
  let denominator := value.denominator.eval point
  ⟨value.numerator.re.eval point / denominator, value.numerator.im.eval point / denominator⟩

/-- Read the scalar coordinate of the original displayed quotient. -/
theorem evaluate_re (value : Expression radicand) (point : Canonical) :
    (value.evaluate point).re = value.numerator.re.eval point / value.denominator.eval point := rfl

/-- Read the generator coefficient of the original displayed quotient. -/
theorem evaluate_im (value : Expression radicand) (point : Canonical) :
    (value.evaluate point).im = value.numerator.im.eval point / value.denominator.eval point := rfl

/-- Cache-free scalar readback of the real cleared cross-denominator difference. -/
@[expose] def realDifference (left right : Expression radicand) : Coefficients :=
  left.numerator.re * right.denominator - right.numerator.re * left.denominator

/-- Cache-free scalar readback of the imaginary cleared cross-denominator difference. -/
@[expose] def imaginaryDifference (left right : Expression radicand) : Coefficients :=
  left.numerator.im * right.denominator - right.numerator.im * left.denominator

/-- Exact coefficient equality after clearing both original displayed denominators.

The relation checks both finite polynomial tables. It makes no assertion of
definedness, numerical inequality when the check fails, or injectivity at one
selected coordinate and sheet. -/
@[expose] def Equal (left right : Expression radicand) : Prop :=
  (left.realDifference right).isZero = true ∧ (left.imaginaryDifference right).isZero = true

/-- The finite coefficient equality predicate has an executable decision. -/
instance (left right : Expression radicand) : Decidable (left.Equal right) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- All-input cleared scalar laws certify the two finite coefficient equality checks.

Only the coefficient-sized retained Gaussian probe lists are needed to turn
the scalar laws into exact zero certificates. -/
theorem equal_of_cross_eval (left right : Expression radicand)
    (real : ∀ point : Canonical,
      left.numerator.re.eval point * right.denominator.eval point =
        right.numerator.re.eval point * left.denominator.eval point)
    (imaginary : ∀ point : Canonical,
      left.numerator.im.eval point * right.denominator.eval point =
        right.numerator.im.eval point * left.denominator.eval point) : left.Equal right := by
  constructor
  · apply Extensionality.isZero_of_eval_eq_zero
    intro point
    change (left.numerator.re * right.denominator - right.numerator.re * left.denominator).eval point = 0
    rewrite [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_mul, real point]
    exact sub_self _
  · apply Extensionality.isZero_of_eval_eq_zero
    intro point
    change (left.numerator.im * right.denominator - right.numerator.im * left.denominator).eval point = 0
    rewrite [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_mul, imaginary point]
    exact sub_self _

/-- Recover the real cleared scalar law from the exact coefficient certificate. -/
theorem Equal.real_cross {left right : Expression radicand} (equal : left.Equal right) (point : Canonical) :
    left.numerator.re.eval point * right.denominator.eval point =
      right.numerator.re.eval point * left.denominator.eval point := by
  have zero := DensePolynomial.eval_eq_zero_of_isZero equal.1 point
  change (left.numerator.re * right.denominator - right.numerator.re * left.denominator).eval point = 0 at zero
  rewrite [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_mul] at zero
  calc
    _ = (left.numerator.re.eval point * right.denominator.eval point -
        right.numerator.re.eval point * left.denominator.eval point) +
        right.numerator.re.eval point * left.denominator.eval point := by ring1
    _ = _ := by rewrite [zero, zero_add]; rfl

/-- Recover the imaginary cleared scalar law from the exact coefficient certificate. -/
theorem Equal.imaginary_cross {left right : Expression radicand} (equal : left.Equal right) (point : Canonical) :
    left.numerator.im.eval point * right.denominator.eval point =
      right.numerator.im.eval point * left.denominator.eval point := by
  have zero := DensePolynomial.eval_eq_zero_of_isZero equal.2 point
  change (left.numerator.im * right.denominator - right.numerator.im * left.denominator).eval point = 0 at zero
  rewrite [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_mul] at zero
  calc
    _ = (left.numerator.im.eval point * right.denominator.eval point -
        right.numerator.im.eval point * left.denominator.eval point) +
        right.numerator.im.eval point * left.denominator.eval point := by ring1
    _ = _ := by rewrite [zero, zero_add]; rfl

/-- Reverse a finite cleared coefficient identity while preserving both original denominators. -/
theorem Equal.symm {left right : Expression radicand} (equal : left.Equal right) : right.Equal left :=
  equal_of_cross_eval right left (fun point => (equal.real_cross point).symm)
    (fun point => (equal.imaginary_cross point).symm)

/-- Cancel two original nonzero scalar denominators in a cleared coordinate identity. -/
private theorem quotient_eq_of_cross (a b c d : Canonical) (bNonzero : b ≠ 0) (dNonzero : d ≠ 0)
    (cross : a * d = c * b) : a / b = c / d := by
  apply ExplicitField.eq_of_mul_eq_mul_right (ExplicitField.mul_ne_zero bNonzero dNonzero)
  calc
    a / b * (b * d) = a * d := by
      rewrite [← mul_assoc, ExplicitField.div_mul_cancel a bNonzero]
      rfl
    _ = c * b := cross
    _ = c / d * (b * d) := by
      rewrite [mul_comm b d, ← mul_assoc, ExplicitField.div_mul_cancel c dNonzero]
      rfl

/-- Exact coefficient equality realizes as pair equality on the original shared domain. -/
theorem Equal.evaluate_eq {left right : Expression radicand} (equal : left.Equal right) (point : Canonical)
    (leftDefined : left.Defined point) (rightDefined : right.Defined point) :
    left.evaluate point = right.evaluate point := by
  apply Pair.ext
  · exact quotient_eq_of_cross _ _ _ _ leftDefined rightDefined (equal.real_cross point)
  · exact quotient_eq_of_cross _ _ _ _ leftDefined rightDefined (equal.imaginary_cross point)

/-- A scalar polynomial expression is defined at every coordinate. -/
theorem defined_scalar (value : Coefficients) (point : Canonical) :
    (scalar (radicand := radicand) value).Defined point := by
  change (DensePolynomial.constant (1 : Canonical)).eval point ≠ 0
  rewrite [DensePolynomial.eval_constant]
  exact BoundaryCanonical.one_ne_zero

/-- The original generator expression is defined at every coordinate. -/
theorem defined_generator (point : Canonical) : (generator (radicand := radicand)).Defined point :=
  defined_scalar (radicand := radicand) 0 point

/-- Both original denominator guards supply the guard of their retained product. -/
theorem defined_add (left right : Expression radicand) (point : Canonical)
    (leftDefined : left.Defined point) (rightDefined : right.Defined point) :
    (left.add right).Defined point := by
  change (left.denominator * right.denominator).eval point ≠ 0
  rewrite [DensePolynomial.eval_mul]
  exact ExplicitField.mul_ne_zero leftDefined rightDefined

/-- Both original denominator guards supply the guard of the quadratic product. -/
theorem defined_mul (left right : Expression radicand) (point : Canonical)
    (leftDefined : left.Defined point) (rightDefined : right.Defined point) :
    (left.mul right).Defined point := defined_add left right point leftDefined rightDefined

/-- Scaling a numerator preserves the original denominator guard. -/
theorem defined_scale (factor : Coefficients) (value : Expression radicand) (point : Canonical)
    (defined : value.Defined point) : (scale factor value).Defined point := defined

/-- The zero scalar expression reads back as the original zero pair. -/
theorem evaluate_zero (point : Canonical) : (zero (radicand := radicand)).evaluate point = 0 := by
  apply Pair.ext
  · change (0 : Coefficients).eval point / (DensePolynomial.constant 1).eval point = 0
    rewrite [DensePolynomial.eval_zero, ExplicitField.zero_div]
    rfl
  · change (0 : Coefficients).eval point / (DensePolynomial.constant 1).eval point = 0
    rewrite [DensePolynomial.eval_zero, ExplicitField.zero_div]
    rfl

/-- Divide by a displayed scalar unit through the original explicit field laws. -/
private theorem div_one (value : Canonical) : value / 1 = value := by
  have cancelled := ExplicitField.div_mul_cancel value BoundaryCanonical.one_ne_zero
  rewrite [mul_one] at cancelled
  exact cancelled

/-- A polynomial scalar expression reads back as its original exact scalar pair. -/
theorem evaluate_scalar (value : Coefficients) (point : Canonical) :
    (scalar (radicand := radicand) value).evaluate point = Pair.scalar (value.eval point) := by
  apply Pair.ext
  · change value.eval point / (DensePolynomial.constant 1).eval point = value.eval point
    rewrite [DensePolynomial.eval_constant]
    exact div_one _
  · change (0 : Coefficients).eval point / (DensePolynomial.constant 1).eval point = 0
    rewrite [DensePolynomial.eval_zero, ExplicitField.zero_div]
    rfl

/-- The formal generator reads back as the original scalar quadratic generator. -/
theorem evaluate_generator (point : Canonical) :
    (generator (radicand := radicand)).evaluate point = Pair.generator := by
  apply Pair.ext
  · change (0 : Coefficients).eval point / (DensePolynomial.constant 1).eval point = 0
    rewrite [DensePolynomial.eval_zero, ExplicitField.zero_div]
    rfl
  · change (DensePolynomial.constant 1).eval point / (DensePolynomial.constant 1).eval point = 1
    rewrite [DensePolynomial.eval_constant]
    exact div_one _

/-- Cross-denominator addition agrees with the two original scalar quotients. -/
private theorem quotient_add (a b c d : Canonical) (bNonzero : b ≠ 0) (dNonzero : d ≠ 0) :
    (d * a + b * c) / (b * d) = a / b + c / d := by
  apply ExplicitField.eq_of_mul_eq_mul_right (ExplicitField.mul_ne_zero bNonzero dNonzero)
  rewrite [ExplicitField.div_mul_cancel _ (ExplicitField.mul_ne_zero bNonzero dNonzero)]
  calc
    d * a + b * c = (a / b * b) * d + (c / d * d) * b := by
      rewrite [ExplicitField.div_mul_cancel a bNonzero, ExplicitField.div_mul_cancel c dNonzero]
      ring1
    _ = (a / b + c / d) * (b * d) := by ring1

/-- Readback of addition uses the original scalar pair sum on the shared domain. -/
theorem evaluate_add (left right : Expression radicand) (point : Canonical)
    (leftDefined : left.Defined point) (rightDefined : right.Defined point) :
    (left.add right).evaluate point = left.evaluate point + right.evaluate point := by
  apply Pair.ext
  · change (right.denominator * left.numerator.re + left.denominator * right.numerator.re).eval point /
      (left.denominator * right.denominator).eval point = _
    rewrite [DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_mul, DensePolynomial.eval_mul]
    exact quotient_add _ _ _ _ leftDefined rightDefined
  · change (right.denominator * left.numerator.im + left.denominator * right.numerator.im).eval point /
      (left.denominator * right.denominator).eval point = _
    rewrite [DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_mul, DensePolynomial.eval_mul]
    exact quotient_add _ _ _ _ leftDefined rightDefined

/-- Readback of multiplication uses the original quadratic product on the shared domain. -/
theorem evaluate_mul (left right : Expression radicand) (point : Canonical)
    (leftDefined : left.Defined point) (rightDefined : right.Defined point) :
    (left.mul right).evaluate point = left.evaluate point * right.evaluate point := by
  apply Pair.ext
  · change (left.numerator.re * right.numerator.re - (-radicand) * left.numerator.im * right.numerator.im).eval point /
      (left.denominator * right.denominator).eval point = _
    rewrite [DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_mul,
      DensePolynomial.eval_mul, DensePolynomial.eval_mul, DensePolynomial.eval_neg]
    apply ExplicitField.eq_of_mul_eq_mul_right (ExplicitField.mul_ne_zero leftDefined rightDefined)
    rewrite [ExplicitField.div_mul_cancel _ (ExplicitField.mul_ne_zero leftDefined rightDefined)]
    change _ = ((left.numerator.re.eval point / left.denominator.eval point) *
      (right.numerator.re.eval point / right.denominator.eval point) -
      (-radicand.eval point) * (left.numerator.im.eval point / left.denominator.eval point) *
      (right.numerator.im.eval point / right.denominator.eval point)) *
      (left.denominator.eval point * right.denominator.eval point)
    have realLeft := ExplicitField.div_mul_cancel (left.numerator.re.eval point) leftDefined
    have realRight := ExplicitField.div_mul_cancel (right.numerator.re.eval point) rightDefined
    have imaginaryLeft := ExplicitField.div_mul_cancel (left.numerator.im.eval point) leftDefined
    have imaginaryRight := ExplicitField.div_mul_cancel (right.numerator.im.eval point) rightDefined
    calc
      _ = (left.numerator.re.eval point / left.denominator.eval point * left.denominator.eval point) *
          (right.numerator.re.eval point / right.denominator.eval point * right.denominator.eval point) -
          (-radicand.eval point) *
          (left.numerator.im.eval point / left.denominator.eval point * left.denominator.eval point) *
          (right.numerator.im.eval point / right.denominator.eval point * right.denominator.eval point) := by
        rewrite [realLeft, realRight, imaginaryLeft, imaginaryRight]
        rfl
      _ = _ := by ring1
  · change (left.numerator.re * right.numerator.im + left.numerator.im * right.numerator.re).eval point /
      (left.denominator * right.denominator).eval point = _
    rewrite [DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_mul, DensePolynomial.eval_mul]
    apply ExplicitField.eq_of_mul_eq_mul_right (ExplicitField.mul_ne_zero leftDefined rightDefined)
    rewrite [ExplicitField.div_mul_cancel _ (ExplicitField.mul_ne_zero leftDefined rightDefined)]
    change _ = ((left.numerator.re.eval point / left.denominator.eval point) *
      (right.numerator.im.eval point / right.denominator.eval point) +
      (left.numerator.im.eval point / left.denominator.eval point) *
      (right.numerator.re.eval point / right.denominator.eval point)) *
      (left.denominator.eval point * right.denominator.eval point)
    have realLeft := ExplicitField.div_mul_cancel (left.numerator.re.eval point) leftDefined
    have realRight := ExplicitField.div_mul_cancel (right.numerator.re.eval point) rightDefined
    have imaginaryLeft := ExplicitField.div_mul_cancel (left.numerator.im.eval point) leftDefined
    have imaginaryRight := ExplicitField.div_mul_cancel (right.numerator.im.eval point) rightDefined
    calc
      _ = (left.numerator.re.eval point / left.denominator.eval point * left.denominator.eval point) *
          (right.numerator.im.eval point / right.denominator.eval point * right.denominator.eval point) +
          (left.numerator.im.eval point / left.denominator.eval point * left.denominator.eval point) *
          (right.numerator.re.eval point / right.denominator.eval point * right.denominator.eval point) := by
        rewrite [realLeft, realRight, imaginaryLeft, imaginaryRight]
        rfl
      _ = _ := by ring1

/-- Numerator scaling reads back as scaling of the original evaluated pair. -/
theorem evaluate_scale (factor : Coefficients) (value : Expression radicand) (point : Canonical) :
    (scale factor value).evaluate point = Pair.scale (factor.eval point) (value.evaluate point) := by
  apply Pair.ext
  · change (factor * value.numerator.re).eval point / value.denominator.eval point =
      factor.eval point * (value.numerator.re.eval point / value.denominator.eval point)
    rewrite [DensePolynomial.eval_mul, ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
    exact mul_assoc _ _ _
  · change (factor * value.numerator.im).eval point / value.denominator.eval point =
      factor.eval point * (value.numerator.im.eval point / value.denominator.eval point)
    rewrite [DensePolynomial.eval_mul, ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
    exact mul_assoc _ _ _

/-- Negation reads back as negation of the same original scalar pair. -/
theorem evaluate_neg (value : Expression radicand) (point : Canonical) :
    value.neg.evaluate point = -(value.evaluate point) := by
  apply Pair.ext
  · change (-value.numerator.re).eval point / value.denominator.eval point =
      -(value.numerator.re.eval point / value.denominator.eval point)
    rewrite [DensePolynomial.eval_neg, ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
    ring1
  · change (-value.numerator.im).eval point / value.denominator.eval point =
      -(value.numerator.im.eval point / value.denominator.eval point)
    rewrite [DensePolynomial.eval_neg, ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
    ring1

/-- The original generator square is exactly the indexed polynomial radicand. -/
theorem generator_square :
    ((generator (radicand := radicand)).mul generator).Equal (scalar radicand) := by
  apply equal_of_cross_eval
  · intro point
    simp only [mul, generator, scalar, Pair.mul_re, Pair.scalar_re,
      DensePolynomial.eval_sub, DensePolynomial.eval_mul, DensePolynomial.eval_neg,
      DensePolynomial.eval_constant, DensePolynomial.eval_zero]
    ring1
  · intro point
    simp only [mul, generator, scalar, Pair.mul_im, Pair.scalar_im,
      DensePolynomial.eval_add, DensePolynomial.eval_mul, DensePolynomial.eval_constant,
      DensePolynomial.eval_zero]
    ring1

set_option genInjectivity false in
/-- The cached cleared coefficient differences of two original expressions.

Both input expressions remain indexed. The differences are computed once and
retained independently of any selected coordinate or sheet. -/
structure Comparison (left right : Expression radicand) where
  /-- The actual first input expression retained as executable data. -/
  leftSource : Expression radicand
  /-- The first retained source is the original first input. -/
  leftSource_eq : leftSource = left
  /-- The actual second input expression retained as executable data. -/
  rightSource : Expression radicand
  /-- The second retained source is the original second input. -/
  rightSource_eq : rightSource = right
  /-- The retained real-coordinate cleared difference. -/
  real : Coefficients
  /-- The real difference belongs to these original inputs. -/
  real_eq : real = left.realDifference right
  /-- The retained imaginary-coordinate cleared difference. -/
  imaginary : Coefficients
  /-- The imaginary difference belongs to these original inputs. -/
  imaginary_eq : imaginary = left.imaginaryDifference right

constructive_injectivity Comparison

/-- Compute and retain both cleared coefficient differences exactly once. -/
@[expose] def compare (left right : Expression radicand) : Comparison left right :=
  ⟨left, rfl, right, rfl, left.realDifference right, rfl, left.imaginaryDifference right, rfl⟩

set_option genInjectivity false in
/-- Exact coefficient equality or the identified obstruction to its finite check.

An obstruction states which cached polynomial difference is nonzero. It does
not assert numerical inequality at a selected coordinate or root sheet. -/
inductive Comparison.Outcome {left right : Expression radicand} (attempt : Comparison left right) where
  /-- Both cached coefficient differences vanish exactly. -/
  | equal (certificate : left.Equal right)
  /-- The real-coordinate coefficient difference is nonzero. -/
  | realObstructed (nonzero : attempt.real.isZero = false)
  /-- The real difference vanishes and the imaginary difference is nonzero. -/
  | imaginaryObstructed (realZero : attempt.real.isZero = true)
      (nonzero : attempt.imaginary.isZero = false)

constructive_injectivity Comparison.Outcome

/-- Check the cached coefficient differences without repeating their polynomial arithmetic. -/
@[expose] def Comparison.check {left right : Expression radicand} (attempt : Comparison left right) :
    attempt.Outcome :=
  if realZero : attempt.real.isZero = true then
    if imaginaryZero : attempt.imaginary.isZero = true then .equal (by
      constructor
      · rewrite [← attempt.real_eq]
        exact realZero
      · rewrite [← attempt.imaginary_eq]
        exact imaginaryZero)
    else .imaginaryObstructed realZero
      (Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true _ imaginaryZero)
  else .realObstructed (Purelib.Data.Bool.Decide.bool_eq_false_of_not_eq_true _ realZero)

/-- A retained real-coordinate obstruction proves failure of this exact coefficient check. -/
theorem Comparison.not_equal_of_real {left right : Expression radicand} (attempt : Comparison left right)
    (nonzero : attempt.real.isZero = false) : ¬left.Equal right := by
  intro equal
  have zero := equal.1
  rewrite [← attempt.real_eq, nonzero] at zero
  exact Bool.noConfusion zero

/-- A retained imaginary-coordinate obstruction proves failure of this exact coefficient check. -/
theorem Comparison.not_equal_of_imaginary {left right : Expression radicand} (attempt : Comparison left right)
    (nonzero : attempt.imaginary.isZero = false) : ¬left.Equal right := by
  intro equal
  have zero := equal.2
  rewrite [← attempt.imaginary_eq, nonzero] at zero
  exact Bool.noConfusion zero

/-- The formal norm numerator of the original retained quadratic polynomial pair. -/
@[expose] def normNumerator (value : Expression radicand) : Coefficients := value.numerator.norm

/-- Conjugate inversion retains the source denominator as a factor of the target denominator.

The displayed expression is `C²(A-BY)/(C N)`, with `N=A²-PB²`.
Keeping the original `C` factor preserves the original undefined points; the
norm route additionally requires nonzero `N` at the selected coordinate. -/
@[expose] def inverse (value : Expression radicand) : Expression radicand :=
  let norm := value.normNumerator
  let denominatorSquare := value.denominator * value.denominator
  ⟨Pair.scale denominatorSquare value.numerator.conjugate, value.denominator * norm⟩

/-- The norm-route inverse is defined when both original denominator and norm numerator are nonzero. -/
theorem defined_inverse (value : Expression radicand) (point : Canonical) (defined : value.Defined point)
    (normNonzero : value.normNumerator.eval point ≠ 0) : value.inverse.Defined point := by
  change (value.denominator * value.normNumerator).eval point ≠ 0
  rewrite [DensePolynomial.eval_mul]
  exact ExplicitField.mul_ne_zero defined normNonzero

/-- Conjugate inversion multiplies to one as an exact cleared coefficient identity.

This identity supplies a value law only on the original source and inverse
domains. A zero norm test never certifies zero on a selected sheet. -/
theorem mul_inverse (value : Expression radicand) : (value.mul value.inverse).Equal one := by
  apply equal_of_cross_eval
  · intro point
    change (value.numerator.re * ((value.denominator * value.denominator) * value.numerator.re) -
      (-radicand) * value.numerator.im * ((value.denominator * value.denominator) * -value.numerator.im)).eval point *
      (DensePolynomial.constant 1).eval point =
      (DensePolynomial.constant 1).eval point *
      (value.denominator * (value.denominator *
        (value.numerator.re * value.numerator.re + (-radicand) * value.numerator.im * value.numerator.im))).eval point
    simp only [DensePolynomial.eval_mul, DensePolynomial.eval_add, DensePolynomial.eval_sub,
      DensePolynomial.eval_neg, DensePolynomial.eval_constant]
    ring1
  · intro point
    change (value.numerator.re * ((value.denominator * value.denominator) * -value.numerator.im) +
      value.numerator.im * ((value.denominator * value.denominator) * value.numerator.re)).eval point *
      (DensePolynomial.constant 1).eval point =
      (0 : Coefficients).eval point * (value.denominator *
        (value.denominator * value.normNumerator)).eval point
    simp only [DensePolynomial.eval_mul, DensePolynomial.eval_add, DensePolynomial.eval_neg,
      DensePolynomial.eval_constant, DensePolynomial.eval_zero]
    ring1

set_option genInjectivity false in
/-- Retained conjugate-inversion data for one original common-denominator expression. -/
structure Inverse (original : Expression radicand) where
  /-- The actual source expression, retained as executable data. -/
  source : Expression radicand
  /-- The source is the original expression. -/
  source_eq : source = original
  /-- The computed and cached norm numerator. -/
  norm : Coefficients
  /-- The cached norm is the original canonical norm calculation. -/
  norm_eq : norm = original.normNumerator
  /-- The computed and cached inverse expression, retaining the source guard. -/
  expression : Expression radicand
  /-- The inverse uses the canonical original conjugate construction. -/
  expression_eq : expression = original.inverse
  /-- The original product has exact unit coefficients after denominator clearing. -/
  product_eq : (original.mul expression).Equal one

constructive_injectivity Inverse

/-- Compute and retain the norm and conjugate inverse once for one original expression. -/
@[expose] def prepareInverse (original : Expression radicand) : Inverse original :=
  let norm := original.normNumerator
  let denominatorSquare := original.denominator * original.denominator
  let expression : Expression radicand :=
    ⟨Pair.scale denominatorSquare original.numerator.conjugate, original.denominator * norm⟩
  ⟨original, rfl, norm, rfl, expression, rfl, mul_inverse original⟩

/-- The displayed unit expression reads back as the original scalar unit pair. -/
theorem evaluate_one (point : Canonical) : (one (radicand := radicand)).evaluate point = 1 := by
  have equal := evaluate_scalar (radicand := radicand) (DensePolynomial.constant 1) point
  rewrite [DensePolynomial.eval_constant] at equal
  exact equal

/-- An admitted conjugate-norm inverse multiplies to the original scalar unit pair. -/
theorem inverse_product (original : Expression radicand) (point : Canonical)
    (defined : original.Defined point) (normNonzero : original.normNumerator.eval point ≠ 0) :
    original.evaluate point * original.inverse.evaluate point = 1 := by
  have inverseDefined := defined_inverse original point defined normNonzero
  have productDefined := defined_mul original original.inverse point defined inverseDefined
  have unitDefined := defined_scalar (radicand := radicand) (DensePolynomial.constant 1) point
  have equal := (mul_inverse original).evaluate_eq point productDefined unitDefined
  rewrite [evaluate_mul original original.inverse point defined inverseDefined, evaluate_one] at equal
  exact equal

/-- The exact source denominator and cached norm route admit inversion at this coordinate. -/
@[expose] def Inverse.Admitted {original : Expression radicand} (attempt : Inverse original)
    (point : Canonical) : Prop := original.Defined point ∧ attempt.norm.eval point ≠ 0

/-- Every admitted retained norm-route attempt has the original inverse denominator guard. -/
theorem Inverse.defined {original : Expression radicand} (attempt : Inverse original) (point : Canonical)
    (admitted : attempt.Admitted point) : attempt.expression.Defined point := by
  rewrite [attempt.expression_eq]
  apply defined_inverse original point admitted.1
  rewrite [← attempt.norm_eq]
  exact admitted.2

set_option genInjectivity false in
/-- A certified pointwise outcome of the retained conjugate-norm inversion route.

A zero source denominator proves the source quotient is undefined. A zero
norm proves only obstruction to this particular inversion route, including
split radicands with nonzero selected-sheet values. -/
inductive Inverse.Outcome {original : Expression radicand} (attempt : Inverse original) (point : Canonical) where
  /-- The original denominator and cached norm both pass their exact nonzero guards. -/
  | admitted (evidence : attempt.Admitted point)
  /-- The original displayed quotient denominator vanishes. -/
  | undefined (denominatorZero : original.denominator.eval point = 0)
  /-- The source quotient is defined but its cached norm numerator vanishes. -/
  | normObstructed (defined : original.Defined point) (normZero : attempt.norm.eval point = 0)

constructive_injectivity Inverse.Outcome

/-- Decide the source-domain and norm guards using the cached inversion attempt. -/
@[expose] def Inverse.check {original : Expression radicand} (attempt : Inverse original) (point : Canonical) :
    attempt.Outcome point :=
  if denominatorZero : original.denominator.eval point = 0 then .undefined denominatorZero
  else if normZero : attempt.norm.eval point = 0 then .normObstructed denominatorZero normZero
  else .admitted ⟨denominatorZero, normZero⟩

end Expression

end Purelib.Algebra.Quadratic.Pair.Polynomial

end
