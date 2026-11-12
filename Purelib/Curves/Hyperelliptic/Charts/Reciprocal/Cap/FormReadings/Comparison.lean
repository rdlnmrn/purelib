module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.DifferentialTransport
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-! # Spatial comparisons of the actual retained cap-form coefficients

Both original whole coefficient channels are compared through their actual
stored root scalings and the same retained polynomial model's point
comparison. The finite error retains the exact scalar numerator separation,
original denominator floors and independently paid observation indices.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Coefficient

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseModelRootChannels
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational.Budget
open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Gaussian

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {parameter : Canonical} {inside : collar.box.Contains (Primitives.point curve parameter)}
  {differential : OddPowerDifferential curve.polynomial} {factor : Canonical}
  {prepared : Preparation cap parameter inside factor}

/-- The exact numerator of the supplied whole form after moving its two actual root scales into one quotient.

The original numerator reading is consumed from its retained cache. The
actual cap tangent, inverse-coordinate Jacobian and both original root
scale factors determine this finite scalar calculation.
-/
def numerator (cached : Coefficient differential prepared) : Canonical :=
  (Primitives.tangent curve parameter * (-(((Primitives.point curve parameter)⁻¹) ^ 2) * cached.1.val)) /
    ((((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) *
      factor)

/-- The exact retained scalar calculation reads the actual numerator cache and original coordinate factors. -/
theorem numerator_eq (cached : Coefficient differential prepared) :
    cached.numerator =
      (Primitives.tangent curve parameter * (-(((Primitives.point curve parameter)⁻¹) ^ 2) * cached.1.val)) /
        ((((Primitives.point curve parameter)⁻¹) ^ (genus + 1)) *
          factor) := by
  unfold numerator
  rfl

/-- The original nonzero coordinate guard clears both scale factors in the actual scalar quotient. -/
theorem numerator_cleared (cached : Coefficient differential prepared) (nonzero : parameter ≠ 0) :
    ((Primitives.point curve parameter)⁻¹) ^ (genus + 1) *
      (factor * cached.numerator) =
      Primitives.tangent curve parameter * (-(((Primitives.point curve parameter)⁻¹) ^ 2) * cached.1.val) := by
  let first := ((Primitives.point curve parameter)⁻¹) ^ (genus + 1)
  let second := factor
  have pointNonzero : Primitives.point curve parameter ≠ 0 :=
    ExplicitField.pow_ne_zero_of_ne_zero nonzero _
  have firstNonzero : first ≠ 0 :=
    ExplicitField.pow_ne_zero_of_ne_zero (ExplicitField.inv_ne_zero pointNonzero) _
  have secondNonzero : second ≠ 0 := prepared.2.1.factor_nonzero
  have productNonzero := ExplicitField.mul_ne_zero firstNonzero secondNonzero
  rewrite [numerator_eq]
  change first * (second * (_ / (first * second))) = _
  rewrite [show first * (second *
    ((Primitives.tangent curve parameter * (-(((Primitives.point curve parameter)⁻¹) ^ 2) * cached.1.val)) /
      (first * second))) =
    ((Primitives.tangent curve parameter * (-(((Primitives.point curve parameter)⁻¹) ^ 2) * cached.1.val)) /
      (first * second)) * (first * second) by ring1]
  exact ExplicitField.div_mul_cancel _ productNonzero

/-- The exact numerator of the actual retained cap form is its original padded polynomial divided by the chart power.

The original bounded-degree numerator and supplied padded cache are kept
at the original differential owner. The nonzero parameter cancels the
actual cap root scale; the existing inverse-coordinate numerator identity
then supplies the same finite polynomial in both degree parities.
-/
theorem numerator_padded {prepared : Preparation cap parameter inside}
    (cached : Coefficient differential prepared) (nonzero : parameter ≠ 0)
    (bound : differential.numerator.natDegree ≤ 2 * genus)
    (polynomial : { value : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial //
      value = Reciprocal.padded differential.numerator (2 * genus) }) :
    cached.numerator =
      ((Primitives.degree curve : Canonical) * (-differential.scale *
        polynomial.val.eval (Primitives.point curve parameter))) /
          (Primitives.point curve parameter) ^ (genus + 1) := by
  let point := Primitives.point curve parameter
  let power := point ^ (genus + 1)
  let inversePower := (point⁻¹) ^ (genus + 1)
  let factor := parameter ^ HyperellipticReciprocal.originOrder curve
  let degree : Canonical := Primitives.degree curve
  let reading := -((point⁻¹) ^ 2) * cached.1.val
  have pointNonzero : point ≠ 0 := ExplicitField.pow_ne_zero_of_ne_zero nonzero _
  have factorNonzero : factor ≠ 0 := ExplicitField.pow_ne_zero_of_ne_zero nonzero _
  have powerNonzero : power ≠ 0 := ExplicitField.pow_ne_zero_of_ne_zero pointNonzero _
  have cleared := cached.numerator_cleared nonzero
  change inversePower * (factor * cached.numerator) = (degree * factor) * reading at cleared
  have reordered : (inversePower * cached.numerator) * factor = (degree * reading) * factor := by
    calc
      _ = inversePower * (factor * cached.numerator) := by ring1
      _ = (degree * factor) * reading := cleared
      _ = _ := by ring1
  have simplified := ExplicitField.eq_of_mul_eq_mul_right factorNonzero reordered
  have cancel : power * inversePower = (1 : Canonical) := by
    change point ^ (genus + 1) * (point⁻¹) ^ (genus + 1) = 1
    rewrite [← Algebra.Semiring.Normalization.product_pow, Canonical.mul_inv_cancel point pointNonzero, one_pow]
    rfl
  have numeratorEq : cached.numerator = degree * (power * reading) := by
    calc
      _ = (1 : Canonical) * cached.numerator := (Gaussian.Basic.one_mul _).symm
      _ = (power * inversePower) * cached.numerator := by rewrite [cancel]; rfl
      _ = power * (inversePower * cached.numerator) := by ring1
      _ = power * (degree * reading) := by rewrite [simplified]; rfl
      _ = _ := by ring1
  have padded := RootCoordinates.Overlap.padded_numerator differential pointNonzero bound polynomial cached.1
    (⟨polynomial.val.eval point, rfl⟩ : { value : Canonical // value = polynomial.val.eval point })
  have multiplied : cached.numerator * power = degree * (-differential.scale * polynomial.val.eval point) := by
    calc
      _ = (degree * (power * reading)) * power := congrArg (fun value : Canonical => value * power) numeratorEq
      _ = degree * ((power * reading) * power) := by ring1
      _ = _ := congrArg (fun value : Canonical => degree * value) padded
  apply ExplicitField.eq_of_mul_eq_mul_right powerNonzero
  rewrite [ExplicitField.div_mul_cancel _ powerNonzero]
  exact multiplied

/-- The finite squared-separation budget of two actual whole cap-form coefficient caches.

The exact numerator difference, same-model point increment, both retained
denominator floors and actual sampler ceilings determine this quantity.
The additional accuracy remains separate from both spatial increments.
-/
@[expose] def separationBound
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {start finish : Canonical}
    {firstInside : collar.box.Contains (Primitives.point curve start)}
    {lastInside : collar.box.Contains (Primitives.point curve finish)}
    {firstFactor lastFactor : Canonical}
    {firstPrepared : Preparation cap start firstInside firstFactor}
    {lastPrepared : Preparation cap finish lastInside lastFactor}
    (first : Coefficient differential firstPrepared) (last : Coefficient differential lastPrepared)
    (accuracy : Fraction.Rational) : Fraction.Rational :=
  16 * Quotient.quotientBound 1
    (Name.Sampling.approximation (Coherence.exact first.numerator).name).centerBound
    (Name.Sampling.approximation firstPrepared.1.certificate.value.name).centerBound
    (Name.Coherent.Division.SampleEquivalence.commonLower
      lastPrepared.1.certificate.apart firstPrepared.1.certificate.apart)
    (Norm.Basic.normSq (last.numerator - first.numerator) + accuracy)
    (32 * bounds.bound * Canonical.normSq (Primitives.point curve finish - Primitives.point curve start) + accuracy) +
      accuracy

/-- Compare the actual two full cap-form channels by their exact numerator separation and same-model root variation.

The supplied whole coefficient caches retain both original numerical root
preparations. Their actual coordinate guards derive the scalar quotient
identities internally. Both denominator guards and their original center
ceilings remain in the finite quotient bound; no sheet-persistence or
successful integration comparison is assumed.
-/
def comparePoints
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {start finish : Canonical}
    {firstInside : collar.box.Contains (Primitives.point curve start)}
    {lastInside : collar.box.Contains (Primitives.point curve finish)}
    {firstFactor lastFactor : Canonical}
    {firstPrepared : Preparation cap start firstInside firstFactor}
    {lastPrepared : Preparation cap finish lastInside lastFactor}
    (first : Coefficient differential firstPrepared) (last : Coefficient differential lastPrepared)
    (pairs : differential.denominatorPairs = 0) (startNonzero : start ≠ 0) (finishNonzero : finish ≠ 0)
    (leftStart rightStart : Nat) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Equivalence.Comparison (Name.Sampling.approximation last.channel.name)
      (Name.Sampling.approximation first.channel.name) leftStart rightStart
      (separationBound bounds first last accuracy) := by
  let precision := accuracy / 16
  have precisionPositive : 0 < precision := Fraction.Order.Field.div_pos_direct positive (by decide)
  let firstNumerator := first.numerator
  let lastNumerator := last.numerator
  let firstEquivalent := first.quotient_equivalent pairs firstNumerator (first.numerator_cleared startNonzero)
  let lastEquivalent := last.quotient_equivalent pairs lastNumerator (last.numerator_cleared finishNonzero)
  let left := lastEquivalent.compare leftStart 0 precision precisionPositive
  let right := firstEquivalent.symm.compare 0 rightStart precision precisionPositive
  let numerators := Equivalence.Comparison.of_constant_samples
    (Name.Sampling.approximation (Coherence.exact lastNumerator).name)
    (Name.Sampling.approximation (Coherence.exact firstNumerator).name) lastNumerator firstNumerator
    (Sequence.Name.Exact.exactNamedSample lastNumerator) (Sequence.Name.Exact.exactNamedSample firstNumerator)
    0 0 accuracy positive
  let roots := RootChannel.Preparation.comparePoints bounds firstPrepared.1 lastPrepared.1 0 0 accuracy positive
  let quotient := Name.Coherent.Division.Equivalence.coherentDiv_comparison
    (Coherence.exact lastNumerator) (Coherence.exact firstNumerator)
    lastPrepared.1.certificate.value firstPrepared.1.certificate.value
    lastPrepared.1.certificate.apart firstPrepared.1.certificate.apart
    numerators roots 0 0 precision precisionPositive
  let bound := Quotient.quotientBound 1
    (Name.Sampling.approximation (Coherence.exact firstNumerator).name).centerBound
    (Name.Sampling.approximation firstPrepared.1.certificate.value.name).centerBound
    (Name.Coherent.Division.SampleEquivalence.commonLower
      lastPrepared.1.certificate.apart firstPrepared.1.certificate.apart)
    (Norm.Basic.normSq (lastNumerator - firstNumerator) + accuracy)
    (32 * bounds.bound * Canonical.normSq (Primitives.point curve finish - Primitives.point curve start) + accuracy)
  let combined := left.trans (quotient.trans right)
  have ordered : 2 * (precision + 2 * (4 * bound + precision + precision)) ≤ 16 * bound + accuracy := by
    have grouped : 2 * (precision + 2 * (4 * bound + precision + precision)) =
        16 * bound + (10 / 16 : Fraction.Rational) * accuracy := by
      dsimp only [precision]
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    rewrite [grouped]
    have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
      (by decide +kernel : (10 / 16 : Fraction.Rational) < 1) positive
    rewrite [Fraction.Field.one_mul] at paid
    exact (Fraction.Order.Arithmetic.add_lt_add_left_direct paid (16 * bound)).le
  exact combined.weaken _ ordered

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Coefficient

end
