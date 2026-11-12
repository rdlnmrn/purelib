module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Power
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-! # Squarefree reduction of odd sheet denominators

A squarefree certificate for the original curve polynomial retains a finite
Bézout result. One preparation consumes that identical result, retaining its
normalized coefficients and the original curve derivative. Each reduction step uses those
identical caches to lower the denominator by two, while retaining the original
spatial-derivative specification of its computed primitive.

The complete recursion ends at a differential with denominator `y`, and
retains every exact primitive in order. This is denominator reduction only;
it does not supply degree reduction, de Rham independence, residue conditions,
primitive boundary cancellation or geometric period transport.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Curves.Hyperelliptic.Differentials.OddPower
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

/-- Exact readbacks of one curve-derivative cache and the original certificate's two normalized coefficients. -/
@[expose] def PreparationIdentity (polynomial : CoefficientPolynomial)
    (certificate : SquarefreeCertificate polynomial) (polynomialDerivative : CoefficientPolynomial)
    (coefficients : CoefficientPolynomial × CoefficientPolynomial) : Prop :=
  polynomialDerivative = GCD.derivative polynomial ∧
    coefficients.1 = certificate.left ∧ coefficients.2 = certificate.right

/-- A reduction preparation indexed by the original squarefree certificate and its retained Euclidean result.

The original certificate already retains the complete Euclidean result and
its construction equality. This preparation stores the curve derivative
once, and evaluates each original coefficient-normalization function once
for reuse throughout every denominator-lowering step. It does not copy the
Euclidean record or invoke the Euclidean algorithm again.
-/
@[expose] def Preparation (polynomial : CoefficientPolynomial)
    (certificate : SquarefreeCertificate polynomial) : Type :=
  (polynomialDerivative : CoefficientPolynomial) ×
    {coefficients : CoefficientPolynomial × CoefficientPolynomial //
      PreparationIdentity polynomial certificate polynomialDerivative coefficients}

namespace Preparation

variable {polynomial : CoefficientPolynomial} {certificate : SquarefreeCertificate polynomial}

/-- The retained complete derivative of the original curve polynomial. -/
@[expose] def polynomialDerivative (preparation : Preparation polynomial certificate) : CoefficientPolynomial :=
  preparation.1

/-- The retained original normalized coefficient of the curve polynomial. -/
@[expose] def left (preparation : Preparation polynomial certificate) : CoefficientPolynomial :=
  preparation.2.val.1

/-- The retained original normalized coefficient of the curve derivative. -/
@[expose] def right (preparation : Preparation polynomial certificate) : CoefficientPolynomial :=
  preparation.2.val.2

/-- The derivative cache preserves the complete original construction. -/
theorem polynomialDerivative_eq (preparation : Preparation polynomial certificate) :
    preparation.polynomialDerivative = GCD.derivative polynomial :=
  preparation.2.property.1

/-- The left cache is the original certificate's complete selected normalization. -/
theorem left_eq (preparation : Preparation polynomial certificate) :
    preparation.left = certificate.left :=
  preparation.2.property.2.1

/-- The right cache is the original certificate's complete selected normalization. -/
theorem right_eq (preparation : Preparation polynomial certificate) :
    preparation.right = certificate.right :=
  preparation.2.property.2.2

/-- The normalized left cache consumes the original certificate's actual retained Euclidean result. -/
theorem left_cache_eq (preparation : Preparation polynomial certificate) :
    preparation.left = certificate.result.left.scale certificate.unit⁻¹ :=
  preparation.left_eq.trans certificate.left_eq

/-- The normalized right cache consumes that identical original Euclidean result. -/
theorem right_cache_eq (preparation : Preparation polynomial certificate) :
    preparation.right = certificate.result.right.scale certificate.unit⁻¹ :=
  preparation.right_eq.trans certificate.right_eq

/-- The two retained normalized coefficients satisfy the original certificate's Bézout identity. -/
theorem identity (preparation : Preparation polynomial certificate) (point : Canonical) :
    1 = preparation.left.eval point * polynomial.eval point +
      preparation.right.eval point * preparation.polynomialDerivative.eval point := by
  have original := certificate.identity point
  rewrite [← preparation.left_eq, ← preparation.right_eq, ← preparation.polynomialDerivative_eq] at original
  exact original

/-- Retain an existing curve derivative and normalize the original certificate's cached Euclidean coefficients once. -/
@[expose] def ofPolynomialDerivative (polynomial : CoefficientPolynomial)
    (certificate : SquarefreeCertificate polynomial) (polynomialDerivative : CoefficientPolynomial)
    (polynomialDerivative_eq : polynomialDerivative = GCD.derivative polynomial) :
    Preparation polynomial certificate :=
  let coefficients := (certificate.left, certificate.right)
  ⟨polynomialDerivative, ⟨coefficients, polynomialDerivative_eq, rfl, rfl⟩⟩

/-- Compute the derivative and two normalizations, reusing the original certificate's completed Euclidean cache. -/
@[expose] def build (polynomial : CoefficientPolynomial) (certificate : SquarefreeCertificate polynomial) :
    Preparation polynomial certificate :=
  ofPolynomialDerivative polynomial certificate (GCD.derivative polynomial) rfl

end Preparation

/-- The precise denominator counts, original scale and cleared numerator identity of one lowering step. -/
@[expose] def StepIdentity (polynomial : CoefficientPolynomial) (input : OddPowerDifferential polynomial) (pairs : Nat)
    (primitive : OddPowerDifferential polynomial) (specification : Derivative.Specification polynomial primitive)
    (remainder : OddPowerDifferential polynomial) : Prop :=
  input.denominatorPairs = pairs + 1 ∧
    primitive.denominatorPairs = pairs ∧ primitive.scale = input.scale ∧
    remainder.denominatorPairs = pairs ∧ remainder.scale = input.scale ∧
    ∀ point : Canonical,
      input.numerator.eval point =
        remainder.numerator.eval point * polynomial.eval point +
          specification.numeratorDerivative.eval point * polynomial.eval point -
            (Derivative.exponentCoefficient primitive / 2) * primitive.numerator.eval point *
              specification.polynomialDerivative.eval point

/-- A lowering step retaining its original input, exact primitive, original derivative certificate and remainder.

The primitive and remainder both use one fewer denominator pair than the
original input, at the identical original scalar. The exact numerator identity
is certified using the derivative caches of the original specification.
-/
@[expose] def Step (polynomial : CoefficientPolynomial) (input : OddPowerDifferential polynomial)
    (pairs : Nat) : Type :=
  (primitive : OddPowerDifferential polynomial) ×
    (specification : Derivative.Specification polynomial primitive) ×
      {remainder : OddPowerDifferential polynomial //
        StepIdentity polynomial input pairs primitive specification remainder}

namespace Step

variable {polynomial : CoefficientPolynomial} {input : OddPowerDifferential polynomial} {pairs : Nat}

/-- The retained primitive with one fewer denominator pair than the original input. -/
@[expose] def primitive (step : Step polynomial input pairs) : OddPowerDifferential polynomial := step.1

/-- The complete original spatial-derivative certificate of the retained primitive. -/
@[expose] def specification (step : Step polynomial input pairs) :
    Derivative.Specification polynomial step.primitive := step.2.1

/-- The retained lower-denominator differential. -/
@[expose] def remainder (step : Step polynomial input pairs) : OddPowerDifferential polynomial := step.2.2.val

/-- The original input has exactly the successor denominator-pair count. -/
theorem input_pairs (step : Step polynomial input pairs) : input.denominatorPairs = pairs + 1 :=
  step.2.2.property.1

/-- The original primitive has the predecessor denominator-pair count. -/
theorem primitive_pairs (step : Step polynomial input pairs) : step.primitive.denominatorPairs = pairs :=
  step.2.2.property.2.1

/-- The original primitive retains the original input scalar. -/
theorem primitive_scale (step : Step polynomial input pairs) : step.primitive.scale = input.scale :=
  step.2.2.property.2.2.1

/-- The remainder has the predecessor denominator-pair count. -/
theorem remainder_pairs (step : Step polynomial input pairs) : step.remainder.denominatorPairs = pairs :=
  step.2.2.property.2.2.2.1

/-- The remainder retains the original input scalar. -/
theorem remainder_scale (step : Step polynomial input pairs) : step.remainder.scale = input.scale :=
  step.2.2.property.2.2.2.2.1

/-- The exact identity is `A = RF + B′F − ((2k−1)/2)BF′`, with the original derivative caches. -/
theorem numerator_eq (step : Step polynomial input pairs) (point : Canonical) :
    input.numerator.eval point =
      step.remainder.numerator.eval point * polynomial.eval point +
        step.specification.numeratorDerivative.eval point * polynomial.eval point -
          (Derivative.exponentCoefficient step.primitive / 2) * step.primitive.numerator.eval point *
            step.specification.polynomialDerivative.eval point :=
  step.2.2.property.2.2.2.2.2 point

/-- The complete original derivative coefficient is the exact part of the original input coefficient. -/
theorem coefficient_eq (step : Step polynomial input pairs) (point : Canonical) :
    input.scale * input.numerator.eval point =
      (step.remainder.scale * step.remainder.numerator.eval point) * polynomial.eval point +
        step.specification.differential.scale * step.specification.differential.numerator.eval point := by
  have derivative := step.specification.coefficient_eq point
  rewrite [step.specification.first_eq, step.specification.last_eq, step.primitive_scale] at derivative
  have numerator := congrArg (fun value : Canonical => input.scale * value) (step.numerator_eq point)
  rewrite [step.remainder_scale, derivative]
  calc
    _ = input.scale *
        (step.remainder.numerator.eval point * polynomial.eval point +
          step.specification.numeratorDerivative.eval point * polynomial.eval point -
            (Derivative.exponentCoefficient step.primitive / 2) * step.primitive.numerator.eval point *
              step.specification.polynomialDerivative.eval point) := numerator
    _ = _ := by
      dsimp only [OddPowerDifferential.ofCoefficients]
      rewrite [eval_mul, ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
      ring1

/-- Both lower channels use the primitive's original odd reciprocal exponent. -/
theorem remainder_exponent (step : Step polynomial input pairs) :
    step.remainder.denominatorExponent = step.primitive.denominatorExponent := by
  change 2 * step.remainder.denominatorPairs + 1 = 2 * step.primitive.denominatorPairs + 1
  rewrite [step.remainder_pairs, step.primitive_pairs]
  rfl

/-- The original input exponent equals the retained derivative's exponent. -/
theorem input_exponent (step : Step polynomial input pairs) :
    input.denominatorExponent = step.primitive.denominatorExponent + 2 := by
  change 2 * input.denominatorPairs + 1 = (2 * step.primitive.denominatorPairs + 1) + 2
  rewrite [step.input_pairs, step.primitive_pairs, Nat.mul_add, Nat.mul_one]
  exact Nat.add_right_comm _ _ _

/-- Build one squarefree lowering step from the identical retained Bézout and curve-derivative caches.

Multiplying the normalized Bézout identity by the input numerator gives
`A = UF + VF′`. The primitive numerator is `B = −2V/(2k−1)`.
Its original derivative cache supplies the remainder numerator `R = U−B′`.
The odd coefficient is always nonzero, so this construction is total.
-/
@[expose] def build {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (input : OddPowerDifferential polynomial) (pairs : Nat)
    (inputPairs : input.denominatorPairs = pairs + 1) : Step polynomial input pairs := by
  let coefficient := Derivative.oddCoefficient pairs
  let left := preparation.left * input.numerator
  let right := preparation.right * input.numerator
  let primitive : OddPowerDifferential polynomial :=
    OddPowerDifferential.ofCoefficients polynomial (right.scale (-2 / coefficient)) pairs input.scale
  let specification := Derivative.Specification.build polynomial primitive
    preparation.polynomialDerivative preparation.polynomialDerivative_eq
  let remainder : OddPowerDifferential polynomial :=
    OddPowerDifferential.ofCoefficients polynomial (left - specification.numeratorDerivative) pairs input.scale
  refine ⟨primitive, specification, ⟨remainder, inputPairs, rfl, rfl, rfl, rfl, ?_⟩⟩
  intro point
  have decomposed : input.numerator.eval point =
      left.eval point * polynomial.eval point + right.eval point * preparation.polynomialDerivative.eval point := by
    change input.numerator.eval point =
      (preparation.left * input.numerator).eval point * polynomial.eval point +
        (preparation.right * input.numerator).eval point * preparation.polynomialDerivative.eval point
    rewrite [eval_mul, eval_mul]
    calc
      _ = input.numerator.eval point * 1 := (_root_.mul_one _).symm
      _ = input.numerator.eval point *
          (preparation.left.eval point * polynomial.eval point +
            preparation.right.eval point * preparation.polynomialDerivative.eval point) :=
        congrArg (fun value : Canonical => input.numerator.eval point * value) (preparation.identity point)
      _ = _ := by ring1
  have coefficientNonzero : coefficient ≠ 0 := Derivative.oddCoefficient_ne_zero pairs
  have inverse := ExplicitField.mul_inv_cancel coefficient coefficientNonzero
  have half : (2 : Canonical) * (2 : Canonical)⁻¹ = 1 := by decide +kernel
  have cancellation : (coefficient / 2) * (-2 / coefficient) = (-1 : Canonical) := by
    rewrite [ExplicitField.div_eq_mul_inv, ExplicitField.div_eq_mul_inv]
    calc
      _ = -((coefficient * coefficient⁻¹) * (2 * (2 : Canonical)⁻¹)) := by ring1
      _ = -1 := by rewrite [inverse, half, _root_.mul_one]; rfl
  change input.numerator.eval point =
    (left - specification.numeratorDerivative).eval point * polynomial.eval point +
      specification.numeratorDerivative.eval point * polynomial.eval point -
        (coefficient / 2) * (right.scale (-2 / coefficient)).eval point *
          preparation.polynomialDerivative.eval point
  rewrite [eval_sub, eval_scale]
  calc
    _ = left.eval point * polynomial.eval point + right.eval point * preparation.polynomialDerivative.eval point :=
      decomposed
    _ = (left.eval point - specification.numeratorDerivative.eval point) * polynomial.eval point +
        specification.numeratorDerivative.eval point * polynomial.eval point -
          ((coefficient / 2) * (-2 / coefficient)) * right.eval point *
            preparation.polynomialDerivative.eval point := by
      rewrite [cancellation]
      ring1
    _ = _ := by ring1

/-- The step's original derivative certificate consumes the identical prepared curve-derivative cache. -/
theorem build_polynomialDerivative {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (input : OddPowerDifferential polynomial) (pairs : Nat)
    (inputPairs : input.denominatorPairs = pairs + 1) :
    (build preparation input pairs inputPairs).specification.polynomialDerivative = preparation.polynomialDerivative :=
  rfl

/-- The primitive numerator is the exact retained normalized right coefficient times the original input numerator. -/
theorem build_primitiveNumerator {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (input : OddPowerDifferential polynomial) (pairs : Nat)
    (inputPairs : input.denominatorPairs = pairs + 1) :
    (build preparation input pairs inputPairs).primitive.numerator =
      (preparation.right * input.numerator).scale
        (-2 / Derivative.oddCoefficient pairs) :=
  rfl

/-- The remainder consumes the identical retained derivative cache of the step's original primitive. -/
theorem build_remainderNumerator {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (input : OddPowerDifferential polynomial) (pairs : Nat)
    (inputPairs : input.denominatorPairs = pairs + 1) :
    (build preparation input pairs inputPairs).remainder.numerator =
      preparation.left * input.numerator -
        (build preparation input pairs inputPairs).specification.numeratorDerivative :=
  rfl

/-- The original coefficient expression is the lower differential plus the retained derivative expression.

The exact numerator identity is transported through the three original
coefficient caches and their actual denominator pair counts. No pointwise
root evaluation or denominator cancellation is used in the coefficient check.
-/
theorem coefficient_equal (step : Step polynomial input pairs) :
    input.coefficient.Equal (step.remainder.coefficient.add step.specification.differential.coefficient) := by
  have differentialPairs : step.specification.differential.denominatorPairs = pairs + 1 := by
    rewrite [step.specification.differential_eq]
    change step.primitive.denominatorPairs + 1 = pairs + 1
    exact congrArg (fun count => count + 1) step.primitive_pairs
  rewrite [input.coefficient_eq, step.remainder.coefficient_eq, step.specification.differential.coefficient_eq]
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [Basic.coefficientSpec, Expression.oddReciprocal, Expression.add,
      Pair.scale, Pair.add_re, eval_mul, eval_add, eval_zero]
    ring1
  · intro point
    simp only [Basic.coefficientSpec, Expression.oddReciprocal, Expression.add,
      Pair.scale, Pair.add_im, eval_mul, eval_add, eval_scale, Dense.Power.eval_power]
    rewrite [step.input_pairs, step.remainder_pairs, differentialPairs, step.coefficient_eq point]
    simp only [pow_succ]
    ring1

/-- The actual original input evaluator agrees with the lower channel plus the retained exact derivative.

All three coefficient interpretations retain the same original square
provenance and apart sheet. The original finite coefficient check and
Denotation realization laws compare those same actual numerical channels.
-/
def agrees (step : Step polynomial input pairs) (point : Canonical)
    (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name) :
    NamedEquivalent (input.value point sheet apart).name
      (CoherentNamed.add (step.remainder.value point sheet apart)
        (step.specification.differential.value point sheet apart)).name :=
  OddPowerDifferential.agrees_add input step.remainder step.specification.differential
    step.coefficient_equal point sheet apart square

end Step

/-- A structural sequence of original lowering steps ending with the unchanged zero-pair owner. -/
@[expose] def Chain (polynomial : CoefficientPolynomial) (input : OddPowerDifferential polynomial) : Nat → Type
  | 0 => {remainder : OddPowerDifferential polynomial // remainder = input ∧ input.denominatorPairs = 0}
  | pairs + 1 => (step : Step polynomial input pairs) × Chain polynomial step.remainder pairs

namespace Chain

variable {polynomial : CoefficientPolynomial}

/-- The final retained differential with denominator `y`. -/
@[expose] def remainder :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} →
      Chain polynomial input pairs → OddPowerDifferential polynomial
  | _, 0, chain => chain.val
  | _, _ + 1, chain => remainder chain.2

/-- Every complete chain ends with exactly zero additional denominator pairs. -/
theorem remainder_pairs :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} → (chain : Chain polynomial input pairs) →
    chain.remainder.denominatorPairs = 0
  | _, 0, chain => by
      change chain.val.denominatorPairs = 0
      rewrite [chain.property.1]
      exact chain.property.2
  | _, _ + 1, chain => remainder_pairs chain.2

/-- A complete chain preserves the original scale in its final retained differential. -/
theorem remainder_scale :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} → (chain : Chain polynomial input pairs) →
    chain.remainder.scale = input.scale
  | _, 0, chain => congrArg OddPowerDifferential.scale chain.property.1
  | _, _ + 1, chain => (remainder_scale chain.2).trans chain.1.remainder_scale

/-- The original primitive parents and derivative certificates, ordered from the highest denominator downward. -/
@[expose] def specifications :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} → Chain polynomial input pairs →
    List ((primitive : OddPowerDifferential polynomial) × Derivative.Specification polynomial primitive)
  | _, 0, _ => []
  | _, _ + 1, chain => ⟨chain.1.primitive, chain.1.specification⟩ :: specifications chain.2

/-- A complete chain retains exactly one original primitive derivative for every removed denominator pair. -/
theorem specifications_length :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} → (chain : Chain polynomial input pairs) →
    chain.specifications.length = pairs
  | _, 0, _ => rfl
  | _, _ + 1, chain => congrArg Nat.succ (specifications_length chain.2)

/-- The exact primitive coefficients transported to the original input's cleared denominator. -/
@[expose] def exactCoefficient (point : Canonical) :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} → Chain polynomial input pairs → Canonical
  | _, 0, _ => 0
  | _, _ + 1, chain =>
      chain.1.specification.differential.scale * chain.1.specification.differential.numerator.eval point +
        polynomial.eval point * exactCoefficient point chain.2

/-- All retained exact primitives and the final numerator give the complete original cleared coefficient. -/
theorem coefficient_eq (point : Canonical) :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} → (chain : Chain polynomial input pairs) →
    input.scale * input.numerator.eval point =
      (chain.remainder.scale * chain.remainder.numerator.eval point) * polynomial.eval point ^ pairs +
        chain.exactCoefficient point
  | _, 0, chain => by
      change _ = (chain.val.scale * chain.val.numerator.eval point) * polynomial.eval point ^ 0 + 0
      rewrite [chain.property.1, pow_zero, _root_.mul_one, _root_.add_zero]
      rfl
  | _, pairs + 1, chain => by
      have current := chain.1.coefficient_eq point
      have remaining := coefficient_eq point chain.2
      change _ = (chain.2.remainder.scale * chain.2.remainder.numerator.eval point) *
        polynomial.eval point ^ (pairs + 1) +
          (chain.1.specification.differential.scale * chain.1.specification.differential.numerator.eval point +
            polynomial.eval point * chain.2.exactCoefficient point)
      rewrite [pow_succ]
      calc
        _ = (chain.1.remainder.scale * chain.1.remainder.numerator.eval point) * polynomial.eval point +
            chain.1.specification.differential.scale * chain.1.specification.differential.numerator.eval point :=
          current
        _ = ((chain.2.remainder.scale * chain.2.remainder.numerator.eval point) * polynomial.eval point ^ pairs +
            chain.2.exactCoefficient point) * polynomial.eval point +
              chain.1.specification.differential.scale * chain.1.specification.differential.numerator.eval point :=
          congrArg (fun value : Canonical => value * polynomial.eval point +
            chain.1.specification.differential.scale * chain.1.specification.differential.numerator.eval point)
            remaining
        _ = _ := by ring1

/-- The actual final differential evaluator with every retained exact derivative added in structural order. -/
@[expose] def value (point : Canonical) (sheet : CoherentNamed) (apart : Named.Apart sheet.name) :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} → Chain polynomial input pairs → CoherentNamed
  | _, 0, chain => chain.val.value point sheet apart
  | _, _ + 1, chain => CoherentNamed.add (value point sheet apart chain.2)
      (chain.1.specification.differential.value point sheet apart)

/-- The original input evaluator agrees with the full retained denominator reduction on the identical original sheet. -/
def agrees (point : Canonical) (sheet : CoherentNamed) (apart : Named.Apart sheet.name)
    (square : NamedEquivalent (sheet.mul sheet).name (Coherence.exact (polynomial.eval point)).name) :
    {input : OddPowerDifferential polynomial} → {pairs : Nat} → (chain : Chain polynomial input pairs) →
      NamedEquivalent (input.value point sheet apart).name (chain.value point sheet apart).name
  | input, 0, chain => by
      change NamedEquivalent (input.value point sheet apart).name (chain.val.value point sheet apart).name
      rewrite [chain.property.1]
      exact NamedEquivalent.refl _
  | _, _ + 1, chain =>
      (chain.1.agrees point sheet apart square).trans
        (Sum.Congruence.coherentAdd_respects (chain.1.remainder.value point sheet apart)
          (chain.2.value point sheet apart) (chain.1.specification.differential.value point sheet apart)
          (chain.1.specification.differential.value point sheet apart)
          (agrees point sheet apart square chain.2) (NamedEquivalent.refl _))

/-- Lower the original pair count structurally, reusing the identical preparation at every recursive call. -/
@[expose] def build {certificate : SquarefreeCertificate polynomial}
    (preparation : Preparation polynomial certificate) (pairs : Nat) (input : OddPowerDifferential polynomial)
    (inputPairs : input.denominatorPairs = pairs) : Chain polynomial input pairs :=
  match pairs with
  | 0 => ⟨input, rfl, inputPairs⟩
  | pairs + 1 =>
      let step := Step.build preparation input pairs inputPairs
      ⟨step, build preparation pairs step.remainder step.remainder_pairs⟩

end Chain

/-- A complete denominator reduction retaining the one shared squarefree preparation and its original lowering chain. -/
@[expose] def Reduced (polynomial : CoefficientPolynomial) (certificate : SquarefreeCertificate polynomial)
    (input : OddPowerDifferential polynomial) : Type :=
  Preparation polynomial certificate × Chain polynomial input input.denominatorPairs

/-- Reduce all odd-denominator pairs using the original certificate's Euclidean result and one derivative cache. -/
@[expose] def reduce (polynomial : CoefficientPolynomial) (certificate : SquarefreeCertificate polynomial)
    (input : OddPowerDifferential polynomial) : Reduced polynomial certificate input :=
  let preparation := Preparation.build polynomial certificate
  ⟨preparation, Chain.build preparation input.denominatorPairs input rfl⟩

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Reduction
