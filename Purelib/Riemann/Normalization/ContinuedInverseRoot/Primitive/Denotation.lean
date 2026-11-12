module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Bounds
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Readback
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Polynomial.Dense.Power
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained primitive denotations at the actual shared root witnesses

Exact divided coefficients come from the original denotation. The spatial
primitive polynomial and its actual evaluation remain separate source data;
comparison uses the same retained inverse-model power and root witness.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

open Purelib
open Purelib.Algebra.Field
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Approximation.Rational

variable {polynomial : Coefficients} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {point : Canonical}

/-- Select the original inverse, cube or fifth-power polynomial from the same retained model power cache. -/
@[expose] def primitivePolynomial {model : Model polynomial patch.base.box} (powers : OddPowers model.value)
    (pairs : Fin 3) : Coefficients :=
  if pairs.val = 0 then model.value else if pairs.val = 1 then powers.cube else powers.fifth

/-- Select the corresponding retained original geometric scale without recomputing its scalar factors. -/
@[expose] def PrimitiveBounds.scale {sample : Point patch point} (bounds : PrimitiveBounds sample)
    (pairs : Fin 3) : Fraction.Rational :=
  if pairs.val = 0 then bounds.inverseScale else if pairs.val = 1 then bounds.cubeScale else bounds.fifthScale

/-- Every selected original primitive power has a nonnegative retained geometric scale. -/
theorem PrimitiveBounds.scale_nonnegative {sample : Point patch point} (bounds : PrimitiveBounds sample)
    (pairs : Fin 3) : 0 ≤ bounds.scale pairs := by
  unfold scale
  split
  · exact bounds.inverseScale_nonnegative
  · split
    · exact bounds.cubeScale_nonnegative
    · exact bounds.fifthScale_nonnegative

/-- The original quadratic primitive denotation on its actual continued point's selected root channel. -/
abbrev PrimitiveDenotation (sample : Point patch point) (pairs : Fin 3) (numerator : Coefficients) :=
  Expression.Denotation (Expression.oddReciprocal polynomial pairs.val numerator) point sample.certificate.value

/-- Retain an original odd-power primitive denotation using its already cached numerator and parameter factors.

The original continued point supplies the selected generator equation and
nonzero parameter guard. Its retained scalar factors produce the original
quadratic pair without repeating polynomial evaluations. -/
@[noinline, nospecialize] def retainPrimitiveDenotation (sample : Point patch point)
    (bounds : PrimitiveBounds sample) (pairs : Fin 3) (numerator : Coefficients)
    (factor : {scalar : Canonical // scalar = numerator.eval point})
    (multiplier : {scalar : Canonical // scalar = bounds.parameterInverse ^ (pairs.val + 1)} :=
      ⟨bounds.parameterInverse ^ (pairs.val + 1), rfl⟩) : PrimitiveDenotation sample pairs numerator := by
  let expression := Expression.oddReciprocal polynomial pairs.val numerator
  have defined : expression.Defined point := by
    change (Polynomial.Dense.Power.power polynomial (pairs.val + 1)).eval point ≠ 0
    rewrite [Polynomial.Dense.Power.eval_power]
    exact ExplicitField.pow_ne_zero_of_ne_zero sample.owner.parameterNonzero _
  let value : Algebra.Quadratic.Pair Canonical (-polynomial.eval point) := ⟨0, factor.val * multiplier.val⟩
  have readback : value = expression.evaluate point := by
    apply Algebra.Quadratic.Pair.ext
    · rewrite [Expression.evaluate_re]
      change (0 : Canonical) = 0 / _
      rewrite [ExplicitField.div_eq_mul_inv, Basic.zero_mul]
      rfl
    · rewrite [Expression.evaluate_im]
      change factor.val * multiplier.val = numerator.eval point /
        (Polynomial.Dense.Power.power polynomial (pairs.val + 1)).eval point
      rewrite [factor.property, multiplier.property, bounds.parameterInverse_eq,
        Polynomial.Dense.Power.eval_power, ExplicitField.div_eq_mul_inv,
        ExplicitField.inverse_pow_nonzero sample.owner.parameterNonzero]
      rfl
  exact Expression.retainValue expression point sample.certificate.value defined
    (Approximation.Gaussian.Provenance.Power.PowerIdentity.ofSquare sample.certificate.square) value readback

namespace PrimitiveReading

variable {sample : Point patch point} {depth : Nat} {model : Model polynomial patch.base.box}
    {powers : OddPowers model.value}

/-- Read the same retained scalar inverse, cube or fifth-power cache at its actual original source stage. -/
@[expose] def oddValue (reading : PrimitiveReading sample depth model powers) (pairs : Fin 3) : Canonical :=
  if pairs.val = 0 then reading.inverse else if pairs.val = 1 then reading.cube else reading.fifth

/-- The selected scalar primitive power reads the actual selected original polynomial cache. -/
theorem oddValue_readback (reading : PrimitiveReading sample depth model powers) (pairs : Fin 3) :
    reading.oddValue pairs = (primitivePolynomial powers pairs).eval point := by
  unfold oddValue primitivePolynomial
  split
  · exact reading.inverse_eq
  · split
    · exact reading.cube_eq
    · exact reading.fifth_eq

/-- The selected scalar power has its actual original same-root geometric error ceiling. -/
theorem oddValue_error_le (reading : PrimitiveReading sample depth model powers)
    (bounds : PrimitiveBounds sample) (inside : patch.box.Contains point) (pairs : Fin 3) :
    Norm.Basic.normSq (reading.oddValue pairs - reading.root * bounds.parameterInverse ^ (pairs.val + 1)) ≤
      Geometric.Basic.quarterRadius (bounds.scale pairs) depth := by
  cases pairs with
  | mk pairs below =>
    cases pairs with
    | zero =>
      change Norm.Basic.normSq (reading.inverse - reading.root * bounds.parameterInverse ^ 1) ≤ _
      rewrite [pow_one]
      exact reading.generator_error_le_scale bounds inside
    | succ pairs =>
      cases pairs with
      | zero => exact reading.cube_error_le_scale bounds inside
      | succ pairs =>
        cases pairs with
        | zero => exact reading.fifth_error_le_scale bounds inside
        | succ pairs =>
          exact False.elim (Nat.not_lt_zero _
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ below))))

end PrimitiveReading

/-- The original primitive denotation's real divided coefficient is zero. -/
theorem PrimitiveDenotation.real_zero {sample : Point patch point} {pairs : Fin 3} {numerator : Coefficients}
    (denotation : PrimitiveDenotation sample pairs numerator) : denotation.value.re = 0 := by
  rewrite [denotation.value_eq, Expression.evaluate_re]
  change (0 : Canonical) / _ = 0
  rewrite [ExplicitField.div_eq_mul_inv, Basic.zero_mul]
  rfl

/-- The original primitive's generator coefficient retains its actual guarded denominator power. -/
theorem PrimitiveDenotation.imaginary_readback {sample : Point patch point} {pairs : Fin 3} {numerator : Coefficients}
    (denotation : PrimitiveDenotation sample pairs numerator) (bounds : PrimitiveBounds sample) :
    denotation.value.im = numerator.eval point * bounds.parameterInverse ^ (pairs.val + 1) := by
  rewrite [denotation.value_eq, Expression.evaluate_im]
  change numerator.eval point / (Polynomial.Dense.Power.power polynomial (pairs.val + 1)).eval point = _
  rewrite [Polynomial.Dense.Power.eval_power, ExplicitField.div_eq_mul_inv,
    ExplicitField.inverse_pow_nonzero sample.owner.parameterNonzero, bounds.parameterInverse_eq]
  rfl

/-- The original generator-coefficient quadrance reads the numerator norm and cached parameter-inverse norm. -/
theorem PrimitiveDenotation.imaginary_norm {sample : Point patch point} {pairs : Fin 3} {numerator : Coefficients}
    (denotation : PrimitiveDenotation sample pairs numerator) (bounds : PrimitiveBounds sample) :
    Norm.Basic.normSq denotation.value.im =
      Norm.Basic.normSq (numerator.eval point) * bounds.inverseNorm ^ (pairs.val + 1) := by
  rewrite [denotation.imaginary_readback bounds, Norm.Basic.normSq_mul, Power.normSq_pow, ← bounds.inverseNorm_eq]
  rfl

set_option genInjectivity false in
/-- One actual spatial primitive reading compared with its original cached quadratic denotation.

The original primitive polynomial retains its exact compilation equation in
the same inverse-model cache. Its numerical readback and the denotation's
linear reading consume the same point and externally shared root witness. -/
structure PrimitiveValue {sample : Point patch point} {depth : Nat} {model : Model polynomial patch.base.box}
    {powers : OddPowers model.value} (reading : PrimitiveReading sample depth model powers)
    (pairs : Fin 3) (numerator : Coefficients) (original : PrimitiveDenotation sample pairs numerator)
    (source : Coefficients) where
  /-- The actual original primitive denotation retained with its original denominator guard. -/
  denotation : PrimitiveDenotation sample pairs numerator
  /-- The retained denotation is the original endpoint owner. -/
  denotation_eq : denotation = original
  /-- The actual original spatial primitive polynomial at this source model stage. -/
  polynomial : Coefficients
  /-- The retained polynomial is the original compiled spatial primitive. -/
  polynomial_eq : polynomial = source
  /-- The actual source table reads the original numerator times the same retained model power at this point. -/
  compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point
  /-- The cached original numerator factor at the same actual source point. -/
  factor : Canonical
  /-- The retained factor belongs to the original numerator and source coordinate. -/
  factor_eq : factor = numerator.eval point
  /-- The cached actual source primitive polynomial evaluation at the original point. -/
  value : Canonical
  /-- The scalar value reads that exact retained spatial polynomial. -/
  value_eq : value = polynomial.eval point
  /-- The cached scalar reading of the original divided coefficients at the shared original root witness. -/
  linear : Canonical
  /-- The original divided coefficient cache and shared witness produce this exact linear reading. -/
  linear_eq : linear = denotation.value.re + denotation.value.im * reading.root
  /-- The cached actual difference between the original source primitive and its shared-root linear reading. -/
  residual : Canonical
  /-- The retained residual belongs to these exact two cached readings. -/
  residual_eq : residual = value - linear

constructive_injectivity PrimitiveValue

/-- Cache an original primitive reading using the same retained numerator factor and scalar power observation.

The scalar product consumes the already retained odd-power reading. Its
readback to the original spatial polynomial is proved from the compilation
certificate, so the potentially large source polynomial is not reevaluated. -/
@[expose] def retainPrimitiveValue {sample : Point patch point} {depth : Nat}
    {model : Model polynomial patch.base.box} {powers : OddPowers model.value}
    (reading : PrimitiveReading sample depth model powers) (pairs : Fin 3) (numerator : Coefficients)
    (original : PrimitiveDenotation sample pairs numerator) (source : Coefficients)
    (compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point)
    (factor : {scalar : Canonical // scalar = numerator.eval point} := ⟨numerator.eval point, rfl⟩) :
    PrimitiveValue reading pairs numerator original source :=
  let value := factor.val * reading.oddValue pairs
  have value_eq : value = source.eval point := by
    have sourceReading := compiled
    rewrite [← reading.oddValue_readback] at sourceReading
    have factorReading := congrArg (fun scalar : Canonical => scalar * reading.oddValue pairs) factor.property
    exact factorReading.trans sourceReading.symm
  let linear := original.value.re + original.value.im * reading.root
  let residual := value - linear
  ⟨original, rfl, source, rfl, compiled, factor.val, factor.property, value, value_eq, linear, rfl, residual, rfl⟩

/-- The cached linear reading consumes the original primitive denotation and the same retained root witness. -/
theorem PrimitiveValue.linear_readback {sample : Point patch point} {depth : Nat}
    {model : Model polynomial patch.base.box} {powers : OddPowers model.value}
    {reading : PrimitiveReading sample depth model powers} {pairs : Fin 3} {numerator : Coefficients}
    {original : PrimitiveDenotation sample pairs numerator} {source : Coefficients}
    (value : PrimitiveValue reading pairs numerator original source) :
    value.linear = original.value.re + original.value.im * reading.root := by
  have real := congrArg (fun denotation => denotation.value.re) value.denotation_eq
  have imaginary := congrArg (fun denotation => denotation.value.im) value.denotation_eq
  rewrite [value.linear_eq, real, imaginary]
  rfl

/-- The actual retained primitive residual is bounded by the source numerator norm and same original power scale. -/
theorem PrimitiveValue.residual_le {sample : Point patch point} {depth : Nat}
    {model : Model polynomial patch.base.box} {powers : OddPowers model.value}
    {reading : PrimitiveReading sample depth model powers} {pairs : Fin 3} {numerator : Coefficients}
    {original : PrimitiveDenotation sample pairs numerator} {source : Coefficients}
    (value : PrimitiveValue reading pairs numerator original source) (bounds : PrimitiveBounds sample)
    (inside : patch.box.Contains point) :
    Norm.Basic.normSq value.residual ≤
      Geometric.Basic.quarterRadius (Norm.Basic.normSq (numerator.eval point) * bounds.scale pairs) depth := by
  have identity : value.residual = numerator.eval point *
      (reading.oddValue pairs - reading.root * bounds.parameterInverse ^ (pairs.val + 1)) := by
    have polynomialReading := congrArg (fun polynomial : Coefficients => polynomial.eval point) value.polynomial_eq
    have sourceValue := value.value_eq.trans (polynomialReading.trans value.compiled)
    rewrite [← reading.oddValue_readback] at sourceValue
    have linearValue : value.linear = numerator.eval point *
        (reading.root * bounds.parameterInverse ^ (pairs.val + 1)) := by
      rewrite [value.linear_eq, value.denotation.real_zero, value.denotation.imaginary_readback bounds]
      ring1
    rewrite [value.residual_eq, sourceValue, linearValue]
    ring1
  rewrite [identity, Norm.Basic.normSq_mul]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (reading.oddValue_error_le bounds inside pairs) (Norm.Basic.normSq_nonneg _)).trans_eq (by
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1)

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

end
