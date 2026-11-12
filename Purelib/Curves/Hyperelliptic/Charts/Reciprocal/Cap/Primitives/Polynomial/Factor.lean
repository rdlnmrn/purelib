module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Polynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FactorBounds
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Polynomial.Dense.Gaussian.Radial.Bounds
import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Purelib.Data.Gaussian.Cast
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
public import Purelib.Riemann.Normalization.InverseModelDifferentialResidual
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-! # The retained ramified primitive factor as a physical w numerator

The same finite parity cache has F(t)=t*S(t²). Its numerator U(w)=w*S(w)
therefore gives U/t at the actual operational t, and its cleared w-root
derivative has coefficient w*N*B/2 using the SAME regular inverse B.
The finite B*r-1 residual remains explicit; B is never made an exact root.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.PolynomialSample

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (Gaussian Polynomial Box)
open Purelib.Riemann.Normalization.InverseRootPolynomial (half)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (differentialResidual)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Division
open Purelib.Data.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box}

/-- Multiply the SAME retained parity factor by its original physical reciprocal coordinate. -/
def shiftedFactor (sample : PolynomialSample cap numerator index box) : Polynomial :=
  shift 1 sample.integrated.factor

/-- The shifted factor evaluates to the original coordinate times the same retained finite factor. -/
private theorem packaged_shiftedFactor_eval (sample : PolynomialSample cap numerator index box) (point : Gaussian) :
    sample.shiftedFactor.eval point = point * sample.integrated.factor.eval point := by
  unfold shiftedFactor
  rewrite [eval_shift, pow_one]
  exact Basic.mul_comm _ _

/-- The shifted factor evaluates to the original coordinate times the same retained finite factor. -/
theorem shiftedFactor_eval (sample : PolynomialSample cap numerator index box) (point : Gaussian) :
    sample.shiftedFactor.eval point = point * sample.integrated.factor.eval point :=
  packaged_shiftedFactor_eval sample point

/-- Its finite derivative is the SAME retained factor plus coordinate times that factor's derivative. -/
private theorem packaged_shiftedFactor_derivative
    (sample : PolynomialSample cap numerator index box) (point : Gaussian) :
    (Derivative.derivative sample.shiftedFactor).eval point =
      sample.integrated.factor.eval point + point * (Derivative.derivative sample.integrated.factor).eval point := by
  unfold shiftedFactor
  rewrite [Derivative.eval_derivative_shift_one]
  ring1

/-- Its finite derivative is the SAME retained factor plus coordinate times that factor's derivative. -/
theorem shiftedFactor_derivative (sample : PolynomialSample cap numerator index box) (point : Gaussian) :
    (Derivative.derivative sample.shiftedFactor).eval point =
      sample.integrated.factor.eval point + point * (Derivative.derivative sample.integrated.factor).eval point :=
  packaged_shiftedFactor_derivative sample point

/-- The actual physical w-root coefficient retains the original full numerator and SAME finite regular inverse.

This is the denominator-cleared derivative of U/t with t²=w. It is an exact
finite coefficient identity, not an analytic derivative of rational t readings.
-/
theorem shiftedFactor_coefficient (sample : PolynomialSample cap numerator index box) (point : Gaussian) :
    point * (Derivative.derivative sample.shiftedFactor).eval point - half * sample.shiftedFactor.eval point =
      half * point * (numerator.eval point * sample.1.val.value.eval point) := by
  have parity := sample.integrated.factor_derivative point
  have regular := congrArg (fun polynomial : Polynomial => polynomial.eval point) sample.2.1.property
  rewrite [eval_mul] at regular
  have original : sample.integrated.factor.eval point +
      2 * point * (Derivative.derivative sample.integrated.factor).eval point =
        numerator.eval point * sample.1.val.value.eval point := by
    exact parity.trans regular
  have twiceHalf : (2 : Gaussian) * half = 1 := by decide +kernel
  rewrite [sample.shiftedFactor_derivative, sample.shiftedFactor_eval]
  calc
    _ = half * point * (sample.integrated.factor.eval point +
        2 * point * (Derivative.derivative sample.integrated.factor).eval point) +
        (1 - 2 * half) * point *
          (sample.integrated.factor.eval point + point * (Derivative.derivative sample.integrated.factor).eval point) :=
      by ring1
    _ = _ := by rewrite [twiceHalf, original]; ring1

/-- The physical numerator retains the same parity factor and original regular inverse model.

The polynomial C=U*P*B is formed from the actual supplied sample, with
U=w*S. It supplies a finite primitive on the original reciprocal q root;
no rational substitute for the operational coordinate t is introduced.
-/
def physicalCoefficient (sample : PolynomialSample cap numerator index box) : Polynomial :=
  sample.shiftedFactor * cap.polynomial * sample.1.val.value

/-- The physical coefficient is exactly the displayed product of the three original retained polynomials. -/
private theorem packaged_physicalCoefficient_factory (sample : PolynomialSample cap numerator index box) :
    sample.physicalCoefficient = sample.shiftedFactor * cap.polynomial * sample.1.val.value := by rfl

/-- The physical coefficient is exactly the displayed product of the three original retained polynomials. -/
theorem physicalCoefficient_factory (sample : PolynomialSample cap numerator index box) :
    sample.physicalCoefficient = sample.shiftedFactor * cap.polynomial * sample.1.val.value :=
  packaged_physicalCoefficient_factory sample

/-- Its scalar value is the original U*P*B product at the supplied physical point. -/
theorem physicalCoefficient_eval (sample : PolynomialSample cap numerator index box) (point : Gaussian) :
    sample.physicalCoefficient.eval point =
      sample.shiftedFactor.eval point * cap.polynomial.eval point * sample.1.val.value.eval point := by
  rewrite [sample.physicalCoefficient_factory, eval_mul, eval_mul]
  rfl

/-- Its derivative retains the original three finite product-rule terms. -/
theorem physicalCoefficient_derivative (sample : PolynomialSample cap numerator index box) (point : Gaussian) :
    (Derivative.derivative sample.physicalCoefficient).eval point =
      ((Derivative.derivative sample.shiftedFactor).eval point * cap.polynomial.eval point +
        sample.shiftedFactor.eval point * (Derivative.derivative cap.polynomial).eval point) *
          sample.1.val.value.eval point +
      sample.shiftedFactor.eval point * cap.polynomial.eval point *
        (Derivative.derivative sample.1.val.value).eval point := by
  rewrite [sample.physicalCoefficient_factory, Derivative.eval_derivative_mul,
    Derivative.eval_derivative_mul, eval_mul]
  rfl

/-- The physical coefficient differs from w*N*P/2 by the two actual finite regular-model residuals.

The original inverse-root differential residual is 2*P*B'+P'*B, and its
square residual is 1-P*B². Both remain in the identity; no finite inverse
model is promoted to an exact root or an exact primitive derivative.
-/
theorem physicalCoefficient_residual (sample : PolynomialSample cap numerator index box) (point : Gaussian) :
    point * cap.polynomial.eval point * (Derivative.derivative sample.physicalCoefficient).eval point -
        half * (cap.polynomial.eval point + point * (Derivative.derivative cap.polynomial).eval point) *
          sample.physicalCoefficient.eval point - half * point * numerator.eval point * cap.polynomial.eval point =
      half * point * cap.polynomial.eval point *
        (sample.shiftedFactor.eval point * differentialResidual cap.polynomial sample.1.val.value point -
          numerator.eval point * sample.1.val.residual.eval point) := by
  have coefficient := sample.shiftedFactor_coefficient point
  have twiceHalf : (2 : Gaussian) * half = 1 := by decide +kernel
  rewrite [sample.physicalCoefficient_derivative, sample.physicalCoefficient_eval,
    sample.1.val.residual_eq]
  unfold differentialResidual
  calc
    _ = cap.polynomial.eval point ^ 2 * sample.1.val.value.eval point *
          (point * (Derivative.derivative sample.shiftedFactor).eval point -
            half * sample.shiftedFactor.eval point) +
        half * point * sample.shiftedFactor.eval point * cap.polynomial.eval point *
          (2 * cap.polynomial.eval point * (Derivative.derivative sample.1.val.value).eval point +
            (Derivative.derivative cap.polynomial).eval point * sample.1.val.value.eval point) -
        half * point * numerator.eval point * cap.polynomial.eval point +
        (1 - 2 * half) * point * sample.shiftedFactor.eval point * cap.polynomial.eval point *
          (cap.polynomial.eval point * (Derivative.derivative sample.1.val.value).eval point +
            (Derivative.derivative cap.polynomial).eval point * sample.1.val.value.eval point) := by ring1
    _ = _ := by rewrite [coefficient, twiceHalf]; ring1

/-- The finite inverse error is exactly the original numerator times the actual B*r-1 residual. -/
theorem product_residual (sample : PolynomialSample cap numerator index box) (point rootReading : Gaussian) :
    (numerator.eval point * sample.1.val.value.eval point) * rootReading - numerator.eval point =
      numerator.eval point * (sample.1.val.value.eval point * rootReading - 1) := by ring1

/-- Its exact quadrance retains both the full numerator and nonzero finite regular-model residual. -/
theorem product_residual_norm (sample : PolynomialSample cap numerator index box) (point rootReading : Gaussian) :
    Norm.Basic.normSq ((numerator.eval point * sample.1.val.value.eval point) * rootReading - numerator.eval point) =
      Norm.Basic.normSq (numerator.eval point) *
        Norm.Basic.normSq (sample.1.val.value.eval point * rootReading - 1) :=
  (congrArg Norm.Basic.normSq (sample.product_residual point rootReading)).trans (Norm.Basic.normSq_mul _ _)

/-- The SAME original finite parity primitive agrees with U divided by its actual retained operational t channel.

The original square certificate and ordinary quotient cancellation derive
the relation internally. No displayed t sample is identified with a rational
square root, and no independently continued w owner is identified here.
-/
def quotientAgreement {point : Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) (branch : HyperellipticReciprocal.originOrder curve = 1)
    (sample : PolynomialSample cap numerator index box) :
    NamedEquivalent
      (Horner.polynomialEval sample.primitive.value
        overlap.coordinate.prepared.denominator).name
      (div (Coherence.exact (sample.shiftedFactor.eval point)) overlap.coordinate.prepared.denominator
        overlap.coordinate.prepared.apart).name := by
  let t := overlap.coordinate.prepared.denominator
  let factor := Coherence.exact (sample.integrated.factor.eval point)
  let value := Coherence.exact (sample.shiftedFactor.eval point)
  let quotient := div value t overlap.coordinate.prepared.apart
  have parameter : point ^ HyperellipticReciprocal.originOrder curve = point := by
    rewrite [branch, pow_one]
    rfl
  have square := NamedEquivalent.transport rfl
    (congrArg (fun scalar : Gaussian => (Coherence.exact scalar).name) parameter) overlap.coordinate.square
  have multiplied : NamedEquivalent (mul t (mul t factor)).name value.name :=
    (Laws.coherentMul_assoc t t factor).symm.trans
      ((Congruence.coherentMul_respects (mul t t) (Coherence.exact point) factor factor square
        (NamedEquivalent.refl _)).trans
        ((Exact.Arithmetic.exact_mul point (sample.integrated.factor.eval point)).trans
          (NamedEquivalent.transport rfl
            (congrArg (fun scalar : Gaussian => (Coherence.exact scalar).name)
              (sample.shiftedFactor_eval point).symm) (NamedEquivalent.refl _))))
  have divided : NamedEquivalent (mul t quotient).name value.name :=
    (Laws.coherentMul_comm t quotient).trans
      (Cancellation.coherentDiv_mul_cancel value t overlap.coordinate.prepared.apart)
  have cancel := Cancellation.coherentMul_cancel_left t (mul t factor) quotient
    overlap.coordinate.prepared.apart (multiplied.trans divided.symm)
  exact (sample.endpointAgreement overlap branch).trans cancel

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Data.Rat.Fraction.Order
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)

/-- The original shifted parity factor has a uniform ceiling independent of its model refinement stage.

The radial polynomial w*s*S(w*s²) uses the same retained parity factor and
inverse model. Every radial argument stays in the regular P box; the
numerator Horner ceiling and original inverse ceiling are fixed before the
stage is chosen. No radial path is taken in the singular w*P box.
-/
theorem shiftedFactor_le {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box}
    (sample : PolynomialSample cap numerator index box)
    (bounds : PrimitiveOverlapBounds cap.clearance numerator)
    {point : Gaussian} (inside : collar.box.Contains point) :
    Norm.Basic.normSq (sample.shiftedFactor.eval point) ≤
      2 * collar.box.normSqBound * bounds.numeratorUpper * bounds.inverseUpper := by
  have estimate := Radial.Bounds.scaled_factor_bound point sample.integrated.factor point true
    (collar.box.normSqBound * (bounds.numeratorUpper * bounds.inverseUpper)) (by
      intro parameter unit
      let coordinate := point * (Cast.Path.ofCoordinate parameter) ^ Primitive.Parity.degree true
      have contained : collar.box.Contains coordinate :=
        Cap.FactorBounds.radial_inside (genus := genus) (curve := curve) (collar := collar)
          inside unit (Primitive.Parity.degree true)
      have parity := sample.integrated.factor_derivative coordinate
      have regular := congrArg (fun polynomial : Polynomial => polynomial.eval coordinate) sample.2.1.property
      rewrite [eval_mul] at regular
      have coefficient := parity.trans regular
      change Norm.Basic.normSq (point *
        (sample.integrated.factor.eval coordinate + (Primitive.Parity.degree true : Gaussian) * coordinate *
          (Derivative.derivative sample.integrated.factor).eval coordinate)) ≤ _
      rewrite [coefficient, Norm.Basic.normSq_mul]
      have productBound : Norm.Basic.normSq (numerator.eval coordinate * sample.1.val.value.eval coordinate) ≤
          bounds.numeratorUpper * bounds.inverseUpper :=
        (Norm.Basic.normSq_eq_canonical _).trans_le (bounds.numerator_inverse_le sample.1.val contained)
      exact Arithmetic.mul_le_mul_direct (collar.box.normSq_le_normSqBound inside) productBound
        (Norm.Basic.normSq_nonneg _) collar.box.normSqBound_nonneg)
  have value := congrArg Norm.Basic.normSq (sample.shiftedFactor_eval point)
  exact (value.trans_le estimate).trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.PolynomialSample

end
