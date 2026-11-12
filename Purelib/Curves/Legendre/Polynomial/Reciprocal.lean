module

public import Purelib.Curves.Legendre.Polynomial
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
public import Purelib.Polynomial.Dense.Gaussian.Reciprocal
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Power
import Purelib.Polynomial.Dense.Power
import Purelib.Polynomial.Dense.Derivative
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-! # Exact ramified reduction of the weighted Legendre differential

The regular factor is Q(t)=(1-t²)(1-λt²). In the original formal quadratic
pair, the coefficient of x dx/y is -2/(t²r), where r²=Q(t). The finite
quotient derivative gives 2d(r/t)-2λt²/r. All displayed denominators remain
part of the expressions. These are finite coefficient certificates, not an
identification of rational readings with exact operational root channels.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal

open Purelib.Polynomial.Dense.Gaussian

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The exact regular reversed-cubic factor at the reciprocal coordinate w. -/
def regularAt (parameter : Canonical) : Coefficients := ⟨[parameter, -(1 + parameter), 1]⟩

/-- The exact regular factor after the ramified substitution w=t². -/
def ramifiedAt (parameter : Canonical) : Coefficients := ⟨[parameter, 0, -(1 + parameter), 0, 1]⟩

/-- The original finite coordinate polynomial used by the displayed quotient denominator. -/
def coordinate : Coefficients := ⟨[1, 0]⟩

/-- The retained finite coordinate table reads its original argument. -/
theorem coordinate_eval (point : Canonical) : coordinate.eval point = point := by
  unfold coordinate eval evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The same retained coordinate table has finite automatic derivative one. -/
theorem coordinate_derivative_eval (point : Canonical) :
    (Derivative.derivative coordinate).eval point = 1 := by
  rewrite [Derivative.eval_derivative]
  unfold coordinate Derivative.evalDerivativeCoeffs
  simp only [List.foldl_cons, List.foldl_nil, Derivative.evalDerivativeStep]
  ring1

/-- The original reversed-cubic factor has its exact quadratic scalar readback. -/
private theorem packaged_regularAt_eval (parameter point : Canonical) :
    (regularAt parameter).eval point = (1 - point) * (1 - parameter * point) := by
  unfold regularAt eval evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The original reversed-cubic factor has its exact quadratic scalar readback. -/
theorem regularAt_eval (parameter point : Canonical) :
    (regularAt parameter).eval point = (1 - point) * (1 - parameter * point) :=
  packaged_regularAt_eval parameter point

/-- The original quadratic regular factor has its finite automatic derivative at the same reciprocal coordinate. -/
private theorem packaged_regularAt_derivative_eval (parameter point : Canonical) :
    (Derivative.derivative (regularAt parameter)).eval point = 2 * parameter * point - (1 + parameter) := by
  rewrite [Derivative.eval_derivative]
  unfold regularAt Derivative.evalDerivativeCoeffs
  simp only [-eq_self, -iff_self, List.foldl_cons, List.foldl_nil, Derivative.evalDerivativeStep]
  ring1

/-- The original quadratic regular factor has its finite automatic derivative at the same reciprocal coordinate. -/
theorem regularAt_derivative_eval (parameter point : Canonical) :
    (Derivative.derivative (regularAt parameter)).eval point = 2 * parameter * point - (1 + parameter) :=
  packaged_regularAt_derivative_eval parameter point

/-- The same five finite coefficients give the actual ramified regular factor. -/
private theorem packaged_ramifiedAt_eval (parameter point : Canonical) :
    (ramifiedAt parameter).eval point = (1 - point ^ 2) * (1 - parameter * point ^ 2) := by
  unfold ramifiedAt eval evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The same five finite coefficients give the actual ramified regular factor. -/
theorem ramifiedAt_eval (parameter point : Canonical) :
    (ramifiedAt parameter).eval point = (1 - point ^ 2) * (1 - parameter * point ^ 2) :=
  packaged_ramifiedAt_eval parameter point

/-- The automatic derivative reads the original finite quartic factor without analytic differentiation. -/
private theorem ramifiedAt_derivative_eval (parameter point : Canonical) :
    (Derivative.derivative (ramifiedAt parameter)).eval point =
      -2 * (1 + parameter) * point + 4 * parameter * point ^ 3 := by
  rewrite [Derivative.eval_derivative]
  unfold ramifiedAt Derivative.evalDerivativeCoeffs
  simp only [List.foldl_cons, List.foldl_nil, Derivative.evalDerivativeStep]
  ring1

/-- The ramified factor is the original finite square substitution of its actual reciprocal regular factor. -/
private theorem packaged_substitution_eval (parameter point : Canonical) :
    (Substitution.Power.substitute (regularAt parameter) 2).eval point =
      (ramifiedAt parameter).eval point := by
  rewrite [Substitution.Power.eval_substitute, regularAt_eval, ramifiedAt_eval]
  rfl

/-- The ramified factor is the original finite square substitution of its actual reciprocal regular factor. -/
theorem substitution_eval (parameter point : Canonical) :
    (Substitution.Power.substitute (regularAt parameter) 2).eval point =
      (ramifiedAt parameter).eval point := packaged_substitution_eval parameter point

/-- The independently displayed reciprocal factor reads the original reversed Legendre coefficients exactly. -/
private theorem packaged_original_regular_eval (parameter point : Canonical) :
    (Gaussian.Reciprocal.reversed (Paths.polynomial parameter)).eval point =
      (regularAt parameter).eval point := by
  rewrite [Gaussian.Reciprocal.reversed_eval, regularAt_eval]
  change (Gaussian.Reciprocal.lowJet point [1, -(1 + parameter), parameter, 0]).1 =
    (1 - point) * (1 - parameter * point)
  unfold Gaussian.Reciprocal.lowJet
  simp only [List.foldr_cons, List.foldr_nil]
  ring1

/-- The independently displayed reciprocal factor reads the original reversed Legendre coefficients exactly. -/
theorem original_regular_eval (parameter point : Canonical) :
    (Gaussian.Reciprocal.reversed (Paths.polynomial parameter)).eval point =
      (regularAt parameter).eval point := packaged_original_regular_eval parameter point

/-- The actual square substitution of the original reversed cubic has the same ramified factor readback. -/
private theorem packaged_original_substitution_eval (parameter point : Canonical) :
    (Substitution.Power.substitute
      (Gaussian.Reciprocal.reversed (Paths.polynomial parameter)) 2).eval point =
      (ramifiedAt parameter).eval point := by
  rewrite [Substitution.Power.eval_substitute, original_regular_eval,
    regularAt_eval, ramifiedAt_eval]
  rfl

/-- The actual square substitution of the original reversed cubic has the same ramified factor readback. -/
theorem original_substitution_eval (parameter point : Canonical) :
    (Substitution.Power.substitute
      (Gaussian.Reciprocal.reversed (Paths.polynomial parameter)) 2).eval point =
      (ramifiedAt parameter).eval point := packaged_original_substitution_eval parameter point

/-- The original formal exact-term value r/t retains the nonzero coordinate denominator. -/
def potential (parameter : Canonical) : Expression (ramifiedAt parameter) :=
  ⟨⟨0, constant 1⟩, coordinate⟩

/-- The original finite quotient slope is (-1+λt⁴)/(t²r), with both original denominator factors retained. -/
def potentialSlope (parameter : Canonical) : Expression (ramifiedAt parameter) :=
  ⟨⟨0, ⟨[parameter, 0, 0, 0, -1]⟩⟩, Power.power coordinate 2 * ramifiedAt parameter⟩

/-- The actual quotient derivative of r/t is the retained finite second-kind slope. -/
private theorem packaged_potential_derivative (parameter : Canonical) :
    (potential parameter).derivative.Equal (potentialSlope parameter) := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, potential, potentialSlope,
      Expression.derivative, Expression.directionalDerivative,
      eval_mul, eval_sub, eval_scale, eval_zero,
      Power.eval_power, Power.eval_derivative_zero]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, potential, potentialSlope,
      Expression.derivative, Expression.directionalDerivative,
      eval_mul, eval_add, eval_sub, eval_scale, eval_constant,
      Power.eval_power, Power.eval_derivative_constant, coordinate_eval, coordinate_derivative_eval,
      ramifiedAt_eval, ramifiedAt_derivative_eval]
    simp only [-eq_self, -iff_self, eval, evalCoeffs, List.foldl_cons, List.foldl_nil]
    ring1

/-- The actual quotient derivative of r/t is the retained finite second-kind slope. -/
theorem potential_derivative (parameter : Canonical) :
    (potential parameter).derivative.Equal (potentialSlope parameter) := packaged_potential_derivative parameter

/-- The weighted ramified coefficient -2/(t²r) retains both original pole and regular-root guards. -/
def weighted (parameter : Canonical) : Expression (ramifiedAt parameter) :=
  ⟨⟨0, constant (-2)⟩, Power.power coordinate 2 * ramifiedAt parameter⟩

/-- The ordinary polynomial-numerator remainder is -2λt²/r at the same original formal root. -/
def remainder (parameter : Canonical) : Expression (ramifiedAt parameter) :=
  Expression.oddReciprocal (ramifiedAt parameter) 0 ⟨[-2 * parameter, 0, 0]⟩

/-- The complete coefficient after the exact-term reduction retains its displayed quotient derivative. -/
def reduced (parameter : Canonical) : Expression (ramifiedAt parameter) :=
  (Expression.scale (constant 2) (potential parameter).derivative).add (remainder parameter)

/-- The original finite quadratic quotient rule certifies the weighted second-kind reduction.

Both denominator-cleared coefficient checks are derived from the same
quartic and its actual finite automatic derivative. No selected root,
primitive estimate, completed integral or final period equality is an input.
-/
private theorem packaged_reduction (parameter : Canonical) :
    (weighted parameter).Equal (reduced parameter) := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, weighted, reduced, potential, remainder,
      Expression.derivative, Expression.directionalDerivative, Expression.scale, Expression.add,
      Expression.oddReciprocal, Algebra.Quadratic.Pair.scale, Algebra.Quadratic.Pair.add_re,
      eval_mul, eval_add, eval_sub, eval_scale, eval_zero, eval_constant, Power.eval_power,
      Power.eval_derivative_zero]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, weighted, reduced, potential, remainder,
      Expression.derivative, Expression.directionalDerivative, Expression.scale, Expression.add,
      Expression.oddReciprocal, Algebra.Quadratic.Pair.scale, Algebra.Quadratic.Pair.add_im,
      eval_mul, eval_add, eval_sub, eval_scale, eval_constant, Power.eval_power,
      Power.eval_derivative_constant, coordinate_eval, coordinate_derivative_eval,
      ramifiedAt_eval, ramifiedAt_derivative_eval]
    simp only [-eq_self, -iff_self, eval, evalCoeffs, List.foldl_cons, List.foldl_nil]
    ring1

/-- The original finite quadratic quotient rule certifies the weighted second-kind reduction.

Both denominator-cleared coefficient checks are derived from the same
quartic and its actual finite automatic derivative. No selected root,
primitive estimate, completed integral or final period equality is an input.
-/
theorem reduction (parameter : Canonical) :
    (weighted parameter).Equal (reduced parameter) :=
  packaged_reduction parameter

/-- The same original weighted denominator supplies the coordinate and regular-root guards separately. -/
private theorem packaged_weighted_guards {parameter point : Canonical}
    (defined : (weighted parameter).Defined point) : point ≠ 0 ∧ (ramifiedAt parameter).eval point ≠ 0 := by
  have denominator : point ^ 2 * (ramifiedAt parameter).eval point ≠ 0 := by
    change (Power.power coordinate 2 * ramifiedAt parameter).eval point ≠ 0 at defined
    rewrite [eval_mul, Power.eval_power, coordinate_eval] at defined
    exact defined
  constructor
  · intro zero
    apply denominator
    rewrite [zero]
    ring1
  · intro zero
    apply denominator
    rewrite [zero]
    ring1

/-- The same original weighted denominator supplies the coordinate and regular-root guards separately. -/
theorem weighted_guards {parameter point : Canonical}
    (defined : (weighted parameter).Defined point) : point ≠ 0 ∧ (ramifiedAt parameter).eval point ≠ 0 :=
  packaged_weighted_guards defined

/-- The exact reduced expression retains the guards derived from its original weighted domain. -/
private theorem packaged_reduced_defined {parameter point : Canonical}
    (defined : (weighted parameter).Defined point) : (reduced parameter).Defined point := by
  have guards := weighted_guards defined
  have potentialDefined : (potential parameter).Defined point := by
    change coordinate.eval point ≠ 0
    intro zero
    exact guards.1 ((coordinate_eval point).symm.trans zero)
  have derivativeDefined := Expression.defined_derivative (potential parameter) point potentialDefined guards.2
  have remainderDefined : (remainder parameter).Defined point := by
    change (Power.power (ramifiedAt parameter) (0 + 1)).eval point ≠ 0
    rewrite [Power.eval_power, pow_one]
    exact guards.2
  exact Expression.defined_add _ _ point
    (Expression.defined_scale (constant 2) _ point derivativeDefined) remainderDefined

/-- The exact reduced expression retains the guards derived from its original weighted domain. -/
theorem reduced_defined {parameter point : Canonical}
    (defined : (weighted parameter).Defined point) : (reduced parameter).Defined point :=
  packaged_reduced_defined defined

/-- Reinterpret the same cached weighted coefficients and channel by the internally proved exact reduction.

The original coordinate, root channel, square identity, divided pair and
channel are retained unchanged. This is a readback operation at a supplied
rational coordinate; it does not replace the cap's operational quotient
coordinate by a rational approximation or execute another observation.
-/
def reduce {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    Expression.Denotation (reduced parameter) point generator :=
  source.reinterpret (reduced parameter)
    (by rewrite [source.source_eq]; exact (reduction parameter).symm) (reduced_defined source.defined)

/-- Exact reduction retains the complete original divided-coefficient pair. -/
private theorem packaged_reduce_value {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    (reduce source).value = source.value := by rfl

/-- Exact reduction retains the complete original divided-coefficient pair. -/
theorem reduce_value {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    (reduce source).value = source.value := packaged_reduce_value source

/-- Exact reduction retains the same operational coefficient channel, with no observation replay. -/
private theorem packaged_reduce_channel {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    (reduce source).channel = source.channel := by rfl

/-- Exact reduction retains the same operational coefficient channel, with no observation replay. -/
theorem reduce_channel {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    (reduce source).channel = source.channel := packaged_reduce_channel source

end Purelib.Curves.Legendre.Polynomial.Reciprocal

end
