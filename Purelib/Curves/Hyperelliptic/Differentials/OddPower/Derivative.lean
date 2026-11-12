module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Approximation.Gaussian.Name.Coherent.Power.Square
public import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Power
import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Data.Gaussian.Cast
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.NatCast
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Spatial derivative specifications of the original odd-power functions

For the retained primitive function scale·P(x)/y^(2k+1), the two finite
polynomial derivatives compute the independent cleared numerator
2P′f−(2k+1)Pf′. The resulting odd-power specification agrees operationally
with its actual two Leibniz evaluator terms on the identical original sheet.

This is an algebraic coefficient bridge. No geometric integral, primitive
edge increment comparison or closed-boundary cancellation is supplied here.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative

open Purelib
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Polynomial
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

/-- The exact Gaussian coefficient of the odd exponent determined by a denominator pair count. -/
@[expose] def oddCoefficient (pairs : Nat) : Canonical :=
  ⟨Fraction.Cast.fromInt (Int.ofNat (2 * pairs + 1)), 0⟩

/-- The retained finite odd coefficient agrees with its original natural-number cast. -/
theorem oddCoefficient_eq (pairs : Nat) : oddCoefficient pairs = ((2 * pairs + 1 : Nat) : Canonical) := by
  apply Data.Gaussian.Basic.ext
  · change Fraction.Cast.fromInt (Int.ofNat (2 * pairs + 1)) = ((2 * pairs + 1 : Nat) : Canonical).re
    rewrite [Cast.natCast_re, Fraction.Cast.natCast_eq_fromInt]
    rfl
  · change (0 : Fraction.Rational) = ((2 * pairs + 1 : Nat) : Canonical).im
    rewrite [Cast.natCast_im]
    rfl

/-- Every finite odd exponent has a nonzero exact Gaussian coefficient. -/
theorem oddCoefficient_ne_zero (pairs : Nat) : oddCoefficient pairs ≠ 0 := by
  intro zero
  have numeratorZero := congrArg (fun value : Canonical => value.re.num) zero
  change Int.ofNat (2 * pairs + 1) = Int.ofNat 0 at numeratorZero
  exact Nat.noConfusion (Int.ofNat.inj numeratorZero)

/-- The original odd exponent embedded directly as an exact real Gaussian coefficient. -/
@[expose] def exponentCoefficient {polynomial : CoefficientPolynomial} (primitive : OddPowerDifferential polynomial) :
    Canonical :=
  oddCoefficient primitive.denominatorPairs

/-- The original exponent coefficient is the exact scalar used by the shared odd-power derivative law. -/
theorem exponentCoefficient_eq {polynomial : CoefficientPolynomial} (primitive : OddPowerDifferential polynomial) :
    exponentCoefficient primitive = 2 * (primitive.denominatorPairs : Canonical) + 1 := by
  unfold exponentCoefficient
  rewrite [oddCoefficient_eq, Algebra.NatCast.add, Algebra.NatCast.mul]
  rfl

/-- Every retained odd exponent has a nonzero exact Gaussian coefficient. -/
theorem exponentCoefficient_ne_zero {polynomial : CoefficientPolynomial}
    (primitive : OddPowerDifferential polynomial) : exponentCoefficient primitive ≠ 0 :=
  oddCoefficient_ne_zero primitive.denominatorPairs

variable {radicand : Pair.Polynomial.Coefficients}

/-- The original explicit odd coefficient is the same retained Gaussian integer cast. -/
theorem exponentCoefficient_eq_intCast (primitive : OddPowerDifferential radicand) :
    exponentCoefficient primitive = (Int.ofNat primitive.denominatorExponent : Canonical) := by
  apply Data.Gaussian.Basic.ext
  · change Fraction.Cast.fromInt (Int.ofNat primitive.denominatorExponent) =
      (Int.ofNat primitive.denominatorExponent : Canonical).re
    rewrite [Cast.gaussian_int_re, Fraction.Cast.intCast_eq_fromInt]
    rfl
  · change (0 : Fraction.Rational) = (Int.ofNat primitive.denominatorExponent : Canonical).im
    rewrite [Cast.intCast_im]
    rfl

set_option genInjectivity false in
/-- Cached spatial derivative data for one original odd-power function and its exact defining curve polynomial.

The original primitive, scale, numerator and exponent remain indices.
The original polynomial derivative algorithms construct both derivative
caches, the cleared numerator and all three differential specifications.
-/
structure Specification (polynomial : CoefficientPolynomial) (primitive : OddPowerDifferential polynomial) where
  /-- The original numerator derivative, computed once. -/
  numeratorDerivative : CoefficientPolynomial
  /-- The cache is the complete original Gaussian dense derivative construction. -/
  numeratorDerivative_eq : numeratorDerivative = GCD.derivative primitive.numerator
  /-- The original curve polynomial derivative, computed once. -/
  polynomialDerivative : CoefficientPolynomial
  /-- The curve derivative cache retains its complete original construction. -/
  polynomialDerivative_eq : polynomialDerivative = GCD.derivative polynomial
  /-- The actual cleared numerator combining both original retained derivative caches. -/
  numerator : CoefficientPolynomial
  /-- The numerator uses those same retained caches and the original odd exponent coefficient. -/
  numerator_eq : numerator = (numeratorDerivative * polynomial).scale 2 -
    (primitive.numerator * polynomialDerivative).scale (exponentCoefficient primitive)
  /-- The independent spatial-derivative odd-power differential specification. -/
  differential : OddPowerDifferential polynomial
  /-- The derivative specification retains the original scale divided by two and one additional denominator pair. -/
  differential_eq : differential =
    OddPowerDifferential.ofCoefficients polynomial numerator (primitive.denominatorPairs + 1) (primitive.scale / 2)
  /-- The first original Leibniz term, with numerator derivative and the unchanged primitive exponent and scale. -/
  first : OddPowerDifferential polynomial
  /-- The first term consumes the identical cached numerator derivative. -/
  first_eq : first =
    OddPowerDifferential.ofCoefficients polynomial numeratorDerivative primitive.denominatorPairs primitive.scale
  /-- The second original Leibniz term, subtracted from the first. -/
  last : OddPowerDifferential polynomial
  /-- The second term retains the original primitive numerator, curve derivative cache and exponent coefficient. -/
  last_eq : last =
    OddPowerDifferential.ofCoefficients polynomial (primitive.numerator * polynomialDerivative)
      (primitive.denominatorPairs + 1) (primitive.scale * exponentCoefficient primitive / 2)

constructive_injectivity Specification

namespace Specification

variable {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}

/-- Compute both original polynomial derivatives once and retain their complete cleared and Leibniz specifications. -/
@[expose] def build (polynomial : CoefficientPolynomial) (primitive : OddPowerDifferential polynomial)
    (polynomialDerivative : CoefficientPolynomial := GCD.derivative polynomial)
    (polynomialDerivative_eq : polynomialDerivative = GCD.derivative polynomial := by rfl) :
    Specification polynomial primitive :=
  let numeratorDerivative := GCD.derivative primitive.numerator
  let numerator := (numeratorDerivative * polynomial).scale 2 -
    (primitive.numerator * polynomialDerivative).scale (exponentCoefficient primitive)
  let differential : OddPowerDifferential polynomial :=
    OddPowerDifferential.ofCoefficients polynomial numerator (primitive.denominatorPairs + 1) (primitive.scale / 2)
  let first : OddPowerDifferential polynomial :=
    OddPowerDifferential.ofCoefficients polynomial numeratorDerivative primitive.denominatorPairs primitive.scale
  let last : OddPowerDifferential polynomial :=
    OddPowerDifferential.ofCoefficients polynomial (primitive.numerator * polynomialDerivative)
      (primitive.denominatorPairs + 1) (primitive.scale * exponentCoefficient primitive / 2)
  { numeratorDerivative := numeratorDerivative
    numeratorDerivative_eq := rfl
    polynomialDerivative := polynomialDerivative
    polynomialDerivative_eq := polynomialDerivative_eq
    numerator := numerator
    numerator_eq := rfl
    differential := differential
    differential_eq := rfl
    first := first
    first_eq := rfl
    last := last
    last_eq := rfl }

/-- A supplied original derivative cache yields the complete default derivative specification.

Equality transports the full original record, including every retained
coefficient cache and construction certificate. Default two-argument calls
continue to compute the original curve derivative once.
-/
theorem build_eq_default (polynomialDerivative : CoefficientPolynomial)
    (polynomialDerivative_eq : polynomialDerivative = GCD.derivative polynomial) :
    build polynomial primitive polynomialDerivative polynomialDerivative_eq = build polynomial primitive := by
  cases polynomialDerivative_eq
  rfl

/-- The spatial derivative adds exactly two to the original odd reciprocal exponent. -/
theorem differential_exponent (specification : Specification polynomial primitive) :
    specification.differential.denominatorExponent = primitive.denominatorExponent + 2 := by
  rewrite [specification.differential_eq]
  change 2 * (primitive.denominatorPairs + 1) + 1 = (2 * primitive.denominatorPairs + 1) + 2
  rewrite [Nat.mul_add, Nat.mul_one]
  exact Nat.add_right_comm _ _ _

/-- The first Leibniz term preserves the original primitive reciprocal exponent. -/
theorem first_exponent (specification : Specification polynomial primitive) :
    specification.first.denominatorExponent = primitive.denominatorExponent := by
  rewrite [specification.first_eq]
  rfl

/-- The second Leibniz term uses the same independent spatial-derivative reciprocal exponent. -/
theorem last_exponent (specification : Specification polynomial primitive) :
    specification.last.denominatorExponent = primitive.denominatorExponent + 2 := by
  rewrite [specification.last_eq]
  change 2 * (primitive.denominatorPairs + 1) + 1 = (2 * primitive.denominatorPairs + 1) + 2
  rewrite [Nat.mul_add, Nat.mul_one]
  exact Nat.add_right_comm _ _ _

/-- The derivative's exact coefficient is the first Leibniz coefficient times the curve value minus the second. -/
theorem coefficient_eq (specification : Specification polynomial primitive) (point : Canonical) :
    specification.differential.scale * specification.differential.numerator.eval point =
      (specification.first.scale * specification.first.numerator.eval point) * polynomial.eval point -
        specification.last.scale * specification.last.numerator.eval point := by
  rewrite [specification.differential_eq, specification.first_eq, specification.last_eq]
  change (primitive.scale / 2) * specification.numerator.eval point =
    (primitive.scale * specification.numeratorDerivative.eval point) * polynomial.eval point -
      (primitive.scale * exponentCoefficient primitive / 2) *
        (primitive.numerator * specification.polynomialDerivative).eval point
  rewrite [specification.numerator_eq, eval_sub, eval_scale, eval_mul, eval_scale, eval_mul]
  rewrite [Algebra.Field.ExplicitField.div_eq_mul_inv, Algebra.Field.ExplicitField.div_eq_mul_inv]
  have half : (2 : Canonical) * (2 : Canonical)⁻¹ = 1 := by decide +kernel
  calc
    _ = (primitive.scale * specification.numeratorDerivative.eval point * polynomial.eval point) *
          (2 * (2 : Canonical)⁻¹) -
        (primitive.scale * exponentCoefficient primitive * (2 : Canonical)⁻¹) *
          (primitive.numerator.eval point * specification.polynomialDerivative.eval point) := by ring1
    _ = _ := by rewrite [half, Basic.mul_one]; rfl

/-- The original derivative cache realizes the shared formal derivative of its original coefficient expression.

The shared odd-reciprocal derivative theorem supplies both original cleared
coordinate identities. The supplied derivative caches identify the resulting
numerator with twice this specification's coefficient numerator; scalar two
is cancelled without dividing by the radicand or changing its domain.
-/
theorem coefficient_derivative_equal (specification : Specification polynomial primitive) :
    primitive.coefficient.derivative.Equal specification.differential.coefficient := by
  let source := (Expression.oddReciprocal polynomial primitive.denominatorPairs
    (primitive.numerator.scale primitive.scale)).derivative
  let middle := Expression.oddPrimitiveDerivative polynomial primitive.denominatorPairs
    (primitive.numerator.scale primitive.scale)
  have original := Expression.derivative_oddReciprocal polynomial
    (primitive.numerator.scale primitive.scale) primitive.denominatorPairs
  change source.Equal middle at original
  have denominator (point : Canonical) :
      middle.denominator.eval point = 2 * specification.differential.coefficient.denominator.eval point := by
    dsimp only [middle, Expression.oddPrimitiveDerivative]
    rewrite [specification.differential.coefficient_eq, specification.differential_eq]
    change ((Dense.Power.power polynomial (primitive.denominatorPairs + 2)).scale 2).eval point =
      2 * (Dense.Power.power polynomial ((primitive.denominatorPairs + 1) + 1)).eval point
    rewrite [eval_scale]
    rfl
  have real (point : Canonical) :
      middle.numerator.re.eval point = 2 * specification.differential.coefficient.numerator.re.eval point := by
    dsimp only [middle, Expression.oddPrimitiveDerivative]
    rewrite [specification.differential.coefficient_eq]
    change (0 : CoefficientPolynomial).eval point = 2 * (0 : CoefficientPolynomial).eval point
    rewrite [eval_zero, Data.Gaussian.Basic.mul_zero]
    rfl
  have imaginary (point : Canonical) :
      middle.numerator.im.eval point = 2 * specification.differential.coefficient.numerator.im.eval point := by
    dsimp only [middle, Expression.oddPrimitiveDerivative]
    rewrite [specification.differential.coefficient_eq, specification.differential_eq]
    change (Expression.oddPrimitiveNumerator polynomial (primitive.numerator.scale primitive.scale)
      primitive.denominatorPairs).eval point = 2 * (specification.numerator.scale (primitive.scale / 2)).eval point
    rewrite [Expression.oddPrimitiveNumerator, specification.numerator_eq,
      specification.numeratorDerivative_eq, specification.polynomialDerivative_eq]
    simp only [GCD.derivative, eval_sub, eval_scale, eval_mul, Dense.Derivative.eval_derivative_scale]
    rewrite [exponentCoefficient_eq, Algebra.Field.ExplicitField.div_eq_mul_inv]
    have half : (2 : Canonical) * (2 : Canonical)⁻¹ = 1 := by decide +kernel
    calc
      _ = primitive.scale *
          (2 * (Dense.Derivative.derivative primitive.numerator).eval point * polynomial.eval point -
            (2 * (primitive.denominatorPairs : Canonical) + 1) * primitive.numerator.eval point *
              (Dense.Derivative.derivative polynomial).eval point) := by ring1
      _ = primitive.scale *
          (2 * (Dense.Derivative.derivative primitive.numerator).eval point * polynomial.eval point -
            (2 * (primitive.denominatorPairs : Canonical) + 1) * primitive.numerator.eval point *
              (Dense.Derivative.derivative polynomial).eval point) * (2 * (2 : Canonical)⁻¹) := by
        rewrite [half, Data.Gaussian.Basic.mul_one]
        rfl
      _ = _ := by ring1
  have cancelDouble (a b c d : Canonical) (equal : a * (2 * b) = (2 * c) * d) : a * b = c * d := by
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_left (by decide +kernel : (2 : Canonical) ≠ 0)
    calc
      2 * (a * b) = a * (2 * b) := by ring1
      _ = (2 * c) * d := equal
      _ = 2 * (c * d) := by ring1
  rewrite [primitive.coefficient_eq]
  change source.Equal specification.differential.coefficient
  apply Expression.equal_of_cross_eval
  · intro point
    have comparison := original.real_cross point
    change source.numerator.re.eval point * middle.denominator.eval point =
      middle.numerator.re.eval point * source.denominator.eval point at comparison
    rewrite [denominator point, real point] at comparison
    exact cancelDouble _ _ _ _ comparison
  · intro point
    have comparison := original.imaginary_cross point
    change source.numerator.im.eval point * middle.denominator.eval point =
      middle.numerator.im.eval point * source.denominator.eval point at comparison
    rewrite [denominator point, imaginary point] at comparison
    exact cancelDouble _ _ _ _ comparison

/-- The independently constructed spatial-derivative evaluator agrees with the retained two Leibniz terms.

The original point and complete sheet channel, apartness certificate and
square comparison are retained. The existing source reciprocal and finite
power comparisons derive this operational agreement from the internally
computed coefficient identity.
-/
def agrees (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name) :
    NamedEquivalent (specification.differential.value point sheet apart).name
      (CoherentNamed.add (specification.first.value point sheet apart)
        (CoherentNamed.neg (specification.last.value point sheet apart))).name := by
  let reciprocal := (Coherence.exact 1).div sheet apart
  have result := Power.reciprocalPower_coefficient_difference sheet reciprocal apart rfl (polynomial.eval point)
    (specification.first.scale * specification.first.numerator.eval point)
    (specification.last.scale * specification.last.numerator.eval point) square primitive.denominatorExponent
  unfold OddPowerDifferential.value
  rewrite [specification.differential_exponent, specification.first_exponent, specification.last_exponent,
    specification.coefficient_eq point]
  exact result

set_option genInjectivity false in
/-- Materialized primitive, spatial derivative and Leibniz channels on the exact same original prepared sheet.

The specification, original point, complete sheet and apartness remain
indices. Every cache is the complete original evaluator construction;
the retained comparison relates the two actual differential process trees.
-/
structure Values (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name) where
  /-- The actual original primitive-function evaluator, retained once. -/
  primitiveValue : CoherentNamed
  /-- The primitive cache is its complete original numerator, scale, exponent and sheet evaluator. -/
  primitiveValue_eq : primitiveValue = primitive.value point sheet apart
  /-- The actual independent spatial-derivative evaluator. -/
  derivative : CoherentNamed
  /-- The derivative cache is the exact evaluator of the independently computed derivative specification. -/
  derivative_eq : derivative = specification.differential.value point sheet apart
  /-- The actual first original Leibniz evaluator on that identical sheet. -/
  first : CoherentNamed
  /-- The first cache is its complete original evaluator construction. -/
  first_eq : first = specification.first.value point sheet apart
  /-- The actual second original Leibniz evaluator, to be subtracted. -/
  last : CoherentNamed
  /-- The second cache preserves its complete original evaluator construction. -/
  last_eq : last = specification.last.value point sheet apart
  /-- The actual signed difference of those identical cached Leibniz terms. -/
  difference : CoherentNamed
  /-- The difference uses both retained actual term caches. -/
  difference_eq : difference = CoherentNamed.add first (CoherentNamed.neg last)
  /-- The retained operational comparison of the actual independent derivative with the actual Leibniz difference. -/
  agreement : NamedEquivalent derivative.name difference.name

constructive_injectivity Values

namespace Values

/-- Construct the original primitive, derivative and Leibniz channels from the same original square law.

A supplied primitive evaluator and its exact original factory equality are
retained literally. Without them the original primitive value is computed
once; the derivative, both Leibniz terms, signed difference and operational
agreement always use the same shared original construction.
-/
@[expose] def build (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name)
    (primitiveValue : CoherentNamed := primitive.value point sheet apart)
    (primitiveValue_eq : primitiveValue = primitive.value point sheet apart := by rfl) :
    Values specification point sheet apart :=
  let derivative := specification.differential.value point sheet apart
  let first := specification.first.value point sheet apart
  let last := specification.last.value point sheet apart
  let difference := CoherentNamed.add first (CoherentNamed.neg last)
  { primitiveValue := primitiveValue
    primitiveValue_eq := primitiveValue_eq
    derivative := derivative
    derivative_eq := rfl
    first := first
    first_eq := rfl
    last := last
    last_eq := rfl
    difference := difference
    difference_eq := rfl
    agreement := specification.agrees point sheet apart square }

/-- A supplied original evaluator cache preserves the complete default derivative-values record.

Equality elimination retains every evaluator, its factory certificate and
the actual derivative-to-Leibniz comparison, beyond their scalar readings.
-/
theorem build_eq_default (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name)
    (primitiveValue : CoherentNamed) (primitiveValue_eq : primitiveValue = primitive.value point sheet apart) :
    build specification point sheet apart square primitiveValue primitiveValue_eq =
      build specification point sheet apart square := by
  cases primitiveValue_eq
  rfl

/-- The complete supplied original primitive evaluator is the identical stored primitive cache. -/
theorem build_primitiveValue (specification : Specification polynomial primitive) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name)
    (primitiveValue : CoherentNamed) (primitiveValue_eq : primitiveValue = primitive.value point sheet apart) :
    (build specification point sheet apart square primitiveValue primitiveValue_eq).primitiveValue = primitiveValue :=
  (rfl)

end Values

end Specification

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
