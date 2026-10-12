module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Power
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Data.Gaussian

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Dense.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box

open Purelib.Polynomial.Dense.Gaussian.Primitive

open Purelib.Polynomial.Dense.Gaussian.Substitution

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# Finite regular primitives for both reciprocal degree parities

The even chart uses w = t and the odd chart uses w = t². In the latter,
v = t times the regular reversed-polynomial root. The pulled differential
has the polynomial numerator -2 t^(2(g-1-k)); no inverse coordinate or
singular coefficient is introduced at the cap origin. The root residual,
differential transport and finite antiderivative are certified separately.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (Coordinate Gaussian Polynomial Box)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian.Reciprocal (reversed)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat}

/-- The cap coordinate degree is one at a regular reciprocal origin and two at a ramified origin. -/
def degree (curve : Hyperelliptic.Basic.HyperellipticCurve genus) : Nat := HyperellipticReciprocal.originOrder curve + 1

/-- Test whether the original reciprocal radicand has origin order one. -/
def ramified (curve : Hyperelliptic.Basic.HyperellipticCurve genus) : Bool :=
  decide (HyperellipticReciprocal.originOrder curve = 1)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
/-- The primitive parity construction uses exactly the original cap coordinate degree.

The original odd or even degree shape selects the same origin order and its
Boolean ramification test. Their literal parity exponents equal the retained cap degree. -/
theorem parity_degree (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    Parity.degree (ramified curve) = degree curve := by
  cases shape : curve.degreeShape with
  | odd =>
      conv_rhs => simp only [degree]
      change Parity.degree (decide (HyperellipticReciprocal.originOrder curve = 1)) =
        HyperellipticReciprocal.originOrder curve + 1
      rw [HyperellipticReciprocal.originOrder, shape]
      rfl
  | even =>
      conv_rhs => simp only [degree]
      change Parity.degree (decide (HyperellipticReciprocal.originOrder curve = 1)) =
        HyperellipticReciprocal.originOrder curve + 1
      rw [HyperellipticReciprocal.originOrder, shape]
      rfl

/-- Raise the original cap parameter to its retained regular or ramified coordinate degree. -/
def point (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (parameter : ReciprocalInnerInverse.Gaussian) :
  Gaussian := parameter ^ degree curve

end

/-- Multiply the retained regular root by the cap parameter to the original reciprocal origin order. -/
def rootCoordinate (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (parameter regularRoot :
  ReciprocalInnerInverse.Gaussian) : Gaussian :=
  parameter ^ HyperellipticReciprocal.originOrder curve * regularRoot

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
/-- The exact derivative of the cap coordinate power map. -/
def tangent (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (parameter : ReciprocalInnerInverse.Gaussian) :
  Gaussian :=
  (degree curve : ReciprocalInnerInverse.Gaussian) * parameter ^ HyperellipticReciprocal.originOrder curve

/-- The cap coordinate factor scales the residual of the original regular root candidate.

The retained origin order is zero or one. Each degree shape supplies the same
coordinate power and its square, including the branch origin and inexact roots. -/
theorem root_residual (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (parameter regularRoot :
  ReciprocalInnerInverse.Gaussian) :
    rootCoordinate curve parameter regularRoot ^ 2 -
      (HyperellipticReciprocal.polynomial curve).eval (point curve
      parameter) =
      parameter ^ (2 * HyperellipticReciprocal.originOrder curve) *
        (regularRoot ^ 2 - (Reciprocal.reversed curve.polynomial).eval
          (point curve parameter)) := by
  rw [HyperellipticReciprocal.polynomial_eval]
  dsimp only [rootCoordinate,
    point, degree]
  rcases (HyperellipticReciprocal.origin_factor curve).2 with regular | branch
  · rw [regular]
    change (parameter ^ 0 * regularRoot) ^ 2 - (Reciprocal.reversed curve.polynomial).eval (parameter ^ 1) * (parameter
      ^ 1) ^ 0 =
      parameter ^ 0 * (regularRoot ^ 2 - (Reciprocal.reversed curve.polynomial).eval (parameter ^ 1))
    ring1
  · rw [branch]
    change (parameter ^ 1 * regularRoot) ^ 2 - (Reciprocal.reversed curve.polynomial).eval (parameter ^ 2) * (parameter
      ^ 2) ^ 1 =
      parameter ^ 2 * (regularRoot ^ 2 - (Reciprocal.reversed curve.polynomial).eval (parameter ^ 2))
    rw [pow_one]
    ring1

/-- The regular pulled differential coefficient retains the reciprocal minus sign, coordinate degree and reversed basis
exponent. -/
def coefficient (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus)
    (parameter inverseRoot : ReciprocalInnerInverse.Gaussian) : Gaussian :=
  -(degree curve : ReciprocalInnerInverse.Gaussian) * parameter ^ (degree curve *
    (HyperellipticReciprocal.reversedDifferential differential).exponent) * inverseRoot

/-- Cancel the same nonzero coordinate factor between the reciprocal differential denominator and coordinate derivative.
-/
private theorem cancel_factor (numerator rate factor root : ReciprocalInnerInverse.Gaussian) (factorNonzero : factor ≠
  0) (rootNonzero : root ≠ 0) :
    -(numerator / (factor * root)) * (rate * factor) = -(rate * numerator) / root := by
  have productNonzero := Data.Gaussian.Field.mul_ne_zero_direct factorNonzero rootNonzero
  apply Data.Gaussian.Field.mul_right_cancel_of_ne productNonzero
  calc
    _ = -(rate * factor) * ((numerator / (factor * root)) * (factor * root)) := by ring1
    _ = -(rate * factor) * numerator := by rw [Algebra.Field.ExplicitField.div_mul_cancel _ productNonzero]
    _ = (-(rate * numerator)) * factor := by ring1
    _ = ((-(rate * numerator) / root) * root) * factor := by
      rw [Algebra.Field.ExplicitField.div_mul_cancel _ rootNonzero]
    _ = _ := by ring1

/-- Exact substitution on the overlap, with the ramification derivative and the reciprocal minus sign both retained. The
right side is regular at t=0. -/
theorem coefficient_transport (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential :
  Differentials.Basic.Differential genus)
    (parameter regularRoot : ReciprocalInnerInverse.Gaussian) (parameterNonzero : parameter ≠ 0) (rootNonzero :
      regularRoot ≠ 0) :
    -Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.coefficient
      (HyperellipticReciprocal.reversedDifferential differential)
      (point curve parameter)
        (rootCoordinate curve parameter regularRoot) *
        tangent curve parameter =
        coefficient curve differential parameter (Data.Gaussian.Field.inv regularRoot) := by
  unfold HyperellipticReciprocal.coefficient rootCoordinate
    Cap.Primitives.tangent
  rw [cancel_factor _ _ _ _ (Power.pow_ne_zero_direct _
    parameterNonzero _) rootNonzero]
  unfold point coefficient
  rw [← pow_mul, Algebra.Field.ExplicitField.div_eq_mul_inv, Data.Gaussian.Field.inv_eq]
  ring1

/-- The finite polynomial numerator of the regular pulled differential, with its exact degree factor and reversed
exponent. -/
def numerator (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential
  genus) : Polynomial :=
  DensePolynomial.shift (degree curve * (HyperellipticReciprocal.reversedDifferential differential).exponent)
    (DensePolynomial.constant (-(degree curve : ReciprocalInnerInverse.Gaussian)))

/-- The retained finite numerator evaluates to its exact cap-coordinate power expression. -/
theorem numerator_eval (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential :
  Differentials.Basic.Differential genus) (parameter : ReciprocalInnerInverse.Gaussian) :
    (numerator curve differential).eval parameter =
      -(degree curve : ReciprocalInnerInverse.Gaussian) * parameter ^ (degree curve *
        (HyperellipticReciprocal.reversedDifferential differential).exponent) := by
  rw [numerator, DensePolynomial.eval_shift, DensePolynomial.eval_constant]

end

variable {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives in
set_option genInjectivity false in
/-- Cached finite polynomial differential and primitive data at one retained cap-model refinement.

The original inverse-root model, power substitution, primitive factor and derivative identities remain attached to the
same curve and differential. -/
structure Sample (data : ReciprocalInnerInverse.Data curve collar) (differential : Differentials.Basic.Differential
  genus)
    (index : Nat) (box : ReciprocalInnerInverse.Box) where
  /-- The cached refinement of the original regular inverse-root model. -/ inverse : InverseRootPolynomial.Model
    data.polynomial collar.box
  /-- The cached inverse model is exactly the original model refined at the retained index. -/ inverse_eq : inverse =
    data.model.refine index
  /-- The cached inverse polynomial after the original cap power substitution. -/ pulledInverse :
    ReciprocalInnerInverse.Polynomial
  /-- The cached pulled polynomial evaluates to the retained inverse model at the original cap coordinate. -/
    pulledInverse_eq : ∀ parameter, pulledInverse.eval parameter = inverse.value.eval
    (point curve parameter)
  /-- The cached finite polynomial coefficient of the pulled differential. -/ coefficient :
    ReciprocalInnerInverse.Polynomial
  /-- The cached coefficient evaluates to the original pulled differential expression. -/ coefficient_eq : ∀ parameter,
    coefficient.eval parameter =
    Primitives.coefficient curve differential parameter (pulledInverse.eval
      parameter)
  /-- The retained finite polynomial primitive of the cached coefficient with its original box remainder certificate. -/
    primitive : Certificate.DensePrimitive coefficient box
  /-- The cached regular-coordinate factor of the retained cap primitive. -/ factor : ReciprocalInnerInverse.Polynomial
  /-- The retained primitive is the original cap parameter times its cached regular-coordinate factor. -/
    primitive_factor : ∀ parameter, primitive.value.eval parameter =
    parameter * factor.eval (point curve parameter)
  /-- The retained primitive coefficient list is exactly the parity expansion of its cached factor. -/ primitive_coeffs
    : primitive.value.coeffs = Parity.valueCoefficients factor
    (decide (HyperellipticReciprocal.originOrder curve = 1))
  /-- The cached factor satisfies the exact derivative identity for the retained regular inverse polynomial. -/
    factor_derivative : ∀ coordinate, factor.eval coordinate + (degree curve : ReciprocalInnerInverse.Gaussian) *
    coordinate *
    (GCD.derivative factor).eval coordinate =
      -(degree curve : ReciprocalInnerInverse.Gaussian) * coordinate ^
        (HyperellipticReciprocal.reversedDifferential differential).exponent * inverse.value.eval coordinate

constructive_injectivity Sample

namespace Sample

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample in
/-- Refine the retained inverse-root model once and cache its pulled coefficient and exact finite primitive.

The parity construction retains the primitive factor, coefficient identity and box Taylor remainder certificate. -/
def build (data : ReciprocalInnerInverse.Data curve collar) (differential : Differentials.Basic.Differential genus)
    (index : Nat) (box : ReciprocalInnerInverse.Box) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample data
      differential index box := by
  let inverse := data.model.refine index
  let pulled := Power.substitute inverse.value (degree curve)
  let coefficient := numerator curve differential * pulled
  let regular := (DensePolynomial.shift (HyperellipticReciprocal.reversedDifferential differential).exponent
    inverse.value).scale
    (-(degree curve : ReciprocalInnerInverse.Gaussian))
  let integrated := Parity.Data.build regular (Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.ramified curve)
  have derivative_eq (parameter : ReciprocalInnerInverse.Gaussian) :
      (GCD.derivative integrated.value).eval parameter = coefficient.eval parameter := by
    rw [GCD.derivative, integrated.derivative_eq, Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.parity_degree]
    change regular.eval (parameter ^ degree curve) =
      (numerator curve differential * pulled).eval parameter
    rw [DensePolynomial.eval_mul, Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.numerator_eval,
      Power.eval_substitute]
    change ((DensePolynomial.shift (HyperellipticReciprocal.reversedDifferential differential).exponent
      inverse.value).scale
      (-(degree curve : ReciprocalInnerInverse.Gaussian))).eval (parameter ^ degree curve) = _
    rw [DensePolynomial.eval_scale, DensePolynomial.eval_shift, ← pow_mul]
    ring1
  let primitive : Certificate.DensePrimitive coefficient box :=
    { value := integrated.value
      derivative_eq := derivative_eq
      remainderBound := Taylor.denseTaylorRemainderBound integrated.value box
      remainderBound_nonnegative := (Taylor.denseTaylorRemainderBound_pos _ _).le
      increment_bound := fun startInside finishInside => by
        have bound := Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
          integrated.value finishInside startInside
        rw [derivative_eq] at bound
        exact bound }
  refine ⟨inverse, rfl, pulled, Power.eval_substitute inverse.value (degree curve), coefficient,
    (fun parameter => by
        rw [DensePolynomial.eval_mul, Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.numerator_eval];
        rfl), primitive, integrated.factor, ?_,
      integrated.value_coeffs, ?_⟩
  · intro parameter
    change integrated.value.eval parameter = parameter * integrated.factor.eval
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.point curve parameter)
    rw [integrated.value_eq, Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.parity_degree]
    rfl
  · intro coordinate
    have identity := integrated.factor_derivative coordinate
    rw [Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.parity_degree] at identity
    exact identity.trans (by
      change ((DensePolynomial.shift (HyperellipticReciprocal.reversedDifferential differential).exponent
        inverse.value).scale
        (-(degree curve : ReciprocalInnerInverse.Gaussian))).eval coordinate = _
      rw [DensePolynomial.eval_scale, DensePolynomial.eval_shift]
      ring1)

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential
  : Differential genus} {index : Nat} {box :
  Box}

/-- The primitive is an actual finite polynomial at the cap origin for both parities, with no coordinate denominator in
its derivative. -/
theorem derivative_eq (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample data differential index
  box) (parameter : ReciprocalInnerInverse.Gaussian) :
    (GCD.derivative sample.primitive.value).eval parameter =
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.coefficient curve differential parameter
        (sample.inverse.value.eval (Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.point curve parameter)) := by
  rw [sample.primitive.derivative_eq, sample.coefficient_eq, sample.pulledInverse_eq]

/-- The same primitive used for Taylor increments has its constant fixed at the cap origin. Its cached factor supplies
endpoint values in w. -/
theorem primitive_zero (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample data differential index
  box) : sample.primitive.value.eval 0 = 0 := by
  rw [sample.primitive_factor, Data.Gaussian.Basic.zero_mul]

/-- Residual control uses the entire original inner box, including its origin. The pulled domain is stated explicitly;
no mesh coverage is inferred. -/
theorem residual_bound (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample data differential index
  box) {parameter : ReciprocalInnerInverse.Gaussian}
    (inside : collar.box.Contains (Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.point curve parameter)) :
    Data.Gaussian.Norm.Basic.normSq (1 - (Reciprocal.reversed curve.polynomial).eval
      (Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.point curve parameter) * (sample.pulledInverse.eval
      parameter) ^ 2) ≤
      Geometric.Basic.quarterRadius data.model.bound index := by
  rw [sample.pulledInverse_eq, sample.inverse_eq, ← data.polynomial_eq]
  have scalar := data.model.refine_residualBound index _ inside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

end Sample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
