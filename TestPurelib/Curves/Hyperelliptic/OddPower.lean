module
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.DifferentialTransport
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction

import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic

/-!
# Odd-power readbacks at the original isolated sheets

Both actual sheets of the radicand two supply one retained root owner and one
prepared equivalent denominator. Powers one, three and five use that same
original generator, square certificate and apartness witness. The nonconstant
radicand one plus the spatial square is interpreted at the point one.
-/

namespace TestPurelib.Curves.Hyperelliptic.OddPower

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Riemann.RootContinuation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

/-- The constant radicand two with its original finite coefficient table. -/
private def two : Coefficients := DensePolynomial.constant 2

/-- The nonconstant radicand one plus the spatial square. -/
private def quadratic : Coefficients := ⟨[1, 0, 1]⟩

/-- The spatial numerator one plus the original variable. -/
private def numerator : Coefficients := ⟨[1, 1]⟩

/-- Compute one apart presentation without selecting a different root or sheet. -/
private def prepareTwo (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter : sidecar.parameter = 2) : Prepared generator :=
  SquareRootProvenance.prepared_of_square sidecar.square (by rewrite [parameter]; decide +kernel)

/-- The original isolated owner supplies the exact odd-power comparison at its retained apart presentation. -/
private def comparePrepared (radicand : Coefficients) (point : Canonical) (evaluation : radicand.eval point = 2)
    (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator) (parameter : sidecar.parameter = 2)
    (pairs : Nat) :
    let prepared := prepareTwo generator sidecar parameter
    let differential := OddPowerDifferential.ofCoefficients radicand numerator pairs 3
    let retained := sidecar.transport prepared.equivalent.symm
    let identity := PowerIdentity.ofSquare retained.square
    let square : PowerIdentity prepared.denominator 2 (radicand.eval point) :=
      evaluation.symm ▸ (show retained.parameter = 2 from parameter) ▸ identity
    NamedEquivalent
      (CoherentNamed.mul (Coherence.exact (differential.scale * differential.numerator.eval point))
        (Power.namedPower
          (CoherentNamed.div (Coherence.exact 1) prepared.denominator prepared.apart)
          differential.denominatorExponent)).name
      (differential.interpret point prepared.denominator square prepared.apart).channel.name := by
  let prepared := prepareTwo generator sidecar parameter
  let differential := OddPowerDifferential.ofCoefficients radicand numerator pairs 3
  let retained := sidecar.transport prepared.equivalent.symm
  have identity := PowerIdentity.ofSquare retained.square
  have retainedParameter : retained.parameter = 2 := parameter
  rewrite [retainedParameter, ← evaluation] at identity
  exact differential.reciprocal_power_equivalent point prepared.denominator identity prepared.apart

/-- The three original odd powers agree on both isolated sheets of the constant radicand. -/
private def constant_sheets (sheet : Fin 2) (pairs : Fin 3) :
    let original := SquareRootSidecar.isolated (2 : Canonical) sheet
    let parameter := SquareRootSidecar.isolated_parameter (2 : Canonical) sheet
    let prepared := prepareTwo original.1 original.2 parameter
    let differential := OddPowerDifferential.ofCoefficients two numerator pairs.val 3
    let retained := original.2.transport prepared.equivalent.symm
    let identity := PowerIdentity.ofSquare retained.square
    let square : PowerIdentity prepared.denominator 2 (two.eval 0) :=
      (DensePolynomial.eval_constant (2 : Canonical) (0 : Canonical)).symm ▸
        (show retained.parameter = 2 from parameter) ▸ identity
    NamedEquivalent
      (CoherentNamed.mul (Coherence.exact (differential.scale * differential.numerator.eval 0))
        (Power.namedPower
          (CoherentNamed.div (Coherence.exact 1) prepared.denominator prepared.apart)
          differential.denominatorExponent)).name
      (differential.interpret 0 prepared.denominator square prepared.apart).channel.name :=
  let original := SquareRootSidecar.isolated (2 : Canonical) sheet
  comparePrepared two 0 (DensePolynomial.eval_constant (2 : Canonical) (0 : Canonical)) original.1 original.2
    (SquareRootSidecar.isolated_parameter (2 : Canonical) sheet) pairs.val

/-- The same three original odd powers agree at one for the nonconstant radicand on both sheets. -/
private def quadratic_sheets (sheet : Fin 2) (pairs : Fin 3) :
    let original := SquareRootSidecar.isolated (2 : Canonical) sheet
    let parameter := SquareRootSidecar.isolated_parameter (2 : Canonical) sheet
    let prepared := prepareTwo original.1 original.2 parameter
    let differential := OddPowerDifferential.ofCoefficients quadratic numerator pairs.val 3
    let retained := original.2.transport prepared.equivalent.symm
    let identity := PowerIdentity.ofSquare retained.square
    let square : PowerIdentity prepared.denominator 2 (quadratic.eval 1) :=
      (show quadratic.eval 1 = 2 by decide +kernel).symm ▸
        (show retained.parameter = 2 from parameter) ▸ identity
    NamedEquivalent
      (CoherentNamed.mul (Coherence.exact (differential.scale * differential.numerator.eval 1))
        (Power.namedPower
          (CoherentNamed.div (Coherence.exact 1) prepared.denominator prepared.apart)
          differential.denominatorExponent)).name
      (differential.interpret 1 prepared.denominator square prepared.apart).channel.name :=
  let original := SquareRootSidecar.isolated (2 : Canonical) sheet
  comparePrepared quadratic 1 (by decide +kernel) original.1 original.2
    (SquareRootSidecar.isolated_parameter (2 : Canonical) sheet) pairs.val

/-- The original first-power coefficients read back three halves at the constant radicand. -/
private theorem constant_first_power :
    (OddPowerDifferential.ofCoefficients two numerator 0 3).coefficient.evaluate 0 = ⟨0, 3 / 2⟩ := by
  decide +kernel

/-- The original third-power coefficients read back three quarters at the constant radicand. -/
private theorem constant_third_power :
    (OddPowerDifferential.ofCoefficients two numerator 1 3).coefficient.evaluate 0 = ⟨0, 3 / 4⟩ := by
  decide +kernel

/-- The original fifth-power coefficients read back three eighths at the constant radicand. -/
private theorem constant_fifth_power :
    (OddPowerDifferential.ofCoefficients two numerator 2 3).coefficient.evaluate 0 = ⟨0, 3 / 8⟩ := by
  decide +kernel

/-- The original first-power coefficients read back three at one for the nonconstant radicand. -/
private theorem quadratic_first_power :
    (OddPowerDifferential.ofCoefficients quadratic numerator 0 3).coefficient.evaluate 1 = ⟨0, 3⟩ := by
  decide +kernel

/-- The original third-power coefficients read back three halves at one for the nonconstant radicand. -/
private theorem quadratic_third_power :
    (OddPowerDifferential.ofCoefficients quadratic numerator 1 3).coefficient.evaluate 1 = ⟨0, 3 / 2⟩ := by
  decide +kernel

/-- The original fifth-power coefficients read back three quarters at one for the nonconstant radicand. -/
private theorem quadratic_fifth_power :
    (OddPowerDifferential.ofCoefficients quadratic numerator 2 3).coefficient.evaluate 1 = ⟨0, 3 / 4⟩ := by
  decide +kernel

section CapErrorBounds

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (Overlap prepareJetErrorBound)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name
open Purelib.Geometry.Rational
open Purelib.Riemann.Topology
open Purelib.Data.Rat

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {point : Canonical} {owner : SquareRootContinuationChain.Owner
    ((HyperellipticReciprocal.polynomial curve).eval point)}

/-- The original even sheet consumes its actual returned error in the internally prepared neighborhood bound. -/
example (overlap : Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0)
    (bound : differential.numerator.degreeCount ≤ 2 * genus + 1)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Canonical // value = Evaluation.eval jet.val point })
    (residualCache : { value : Canonical // value = Evaluation.eval remainder.val point })
    (factor : Prepared (origin.certificate.value.add
      (overlap.regularRoot.value.mul (Coherence.exact coefficientCache.val))))
    (inside : (Box.symmetric (prepareJetErrorBound origin jet remainder).1.val
      (prepareJetErrorBound origin jet remainder).1.property.le).Contains point)
    (leftStart rightStart : Nat) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Equivalence.Comparison
      (Sampling.approximation (overlap.evenJetPullback nonzero differential pairs regularChart bound
        origin jet remainder coefficientCache residualCache factor).1.error.name)
      (Sampling.approximation (Coherence.exact 0).name) leftStart rightStart
      ((prepareJetErrorBound origin jet remainder).2.1.val + accuracy) := by
  let request := prepareJetErrorBound origin jet remainder
  let pulled := overlap.evenJetPullback nonzero differential pairs regularChart bound
    origin jet remainder coefficientCache residualCache factor
  exact request.2.2 point overlap.regular ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    coefficientCache residualCache factor
    pulled.1 inside leftStart rightStart accuracy positive

/-- The original ramified tangent consumes its actual returned error in the internally prepared neighborhood bound. -/
example (overlap : Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (bound : differential.numerator.degreeCount ≤ 2 * genus)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Canonical // value = Evaluation.eval jet.val point })
    (residualCache : { value : Canonical // value = Evaluation.eval remainder.val point })
    (factor : Prepared (origin.certificate.value.add
      (overlap.regularRoot.value.mul (Coherence.exact coefficientCache.val))))
    (inside : (Box.symmetric (prepareJetErrorBound origin jet remainder).1.val
      (prepareJetErrorBound origin jet remainder).1.property.le).Contains point)
    (leftStart rightStart : Nat) (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Equivalence.Comparison
      (Sampling.approximation (overlap.oddJetPullback nonzero differential pairs branch bound
        origin jet remainder coefficientCache residualCache factor).1.error.name)
      (Sampling.approximation (Coherence.exact 0).name) leftStart rightStart
      ((prepareJetErrorBound origin jet remainder).2.1.val + accuracy) := by
  let request := prepareJetErrorBound origin jet remainder
  let pulled := overlap.oddJetPullback nonzero differential pairs branch bound
    origin jet remainder coefficientCache residualCache factor
  exact request.2.2 point overlap.regular ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    coefficientCache residualCache factor
    pulled.1 inside leftStart rightStart accuracy positive

/-- The actual even pullback error receives the internally paid coordinate-power decay estimate. -/
example (overlap : Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (regularChart : HyperellipticReciprocal.originOrder curve = 0)
    (bound : differential.numerator.degreeCount ≤ 2 * genus + 1)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Canonical // value = Evaluation.eval jet.val point })
    (residualCache : { value : Canonical // value = Evaluation.eval remainder.val point })
    (factor : Prepared (origin.certificate.value.add
      (overlap.regularRoot.value.mul (Coherence.exact coefficientCache.val))))
    (target : Fraction.Rational) (positive : 0 < target)
    (inside : (Box.symmetric (RootCoordinates.prepareJetDecay origin jet remainder target positive).1.val
      (RootCoordinates.prepareJetDecay origin jet remainder target positive).1.property.le).Contains point)
    (leftStart rightStart : Nat) :
    Equivalence.Comparison
      (Sampling.approximation ((Coherence.exact (point ^ (genus + 1))).mul
        (overlap.evenJetPullback nonzero differential pairs regularChart bound
          origin jet remainder coefficientCache residualCache factor).1.error).name)
      (Sampling.approximation (Coherence.exact 0).name) leftStart rightStart
      target := by
  let request := RootCoordinates.prepareJetDecay origin jet remainder target positive
  let pulled := overlap.evenJetPullback nonzero differential pairs regularChart bound
    origin jet remainder coefficientCache residualCache factor
  let compared := request.2 point overlap.regular ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    coefficientCache residualCache factor
    pulled.1 inside leftStart rightStart (target / 2)
      (Fraction.Order.Field.div_pos_direct positive (by decide))
  have paid : target / 2 + target / 2 = target := by
    calc
      _ = (target / 2) * 2 := by ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)
  exact compared.weaken target paid.le

/-- The actual odd pullback error receives the same internally paid coordinate-power decay estimate. -/
example (overlap : Overlap cap point owner) (nonzero : point ≠ 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (bound : differential.numerator.degreeCount ≤ 2 * genus)
    (origin : Owners.Point cap 0) (jet : InfinityCoefficients.Jet curve)
    (remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val)
    (coefficientCache : { value : Canonical // value = Evaluation.eval jet.val point })
    (residualCache : { value : Canonical // value = Evaluation.eval remainder.val point })
    (factor : Prepared (origin.certificate.value.add
      (overlap.regularRoot.value.mul (Coherence.exact coefficientCache.val))))
    (target : Fraction.Rational) (positive : 0 < target)
    (inside : (Box.symmetric (RootCoordinates.prepareJetDecay origin jet remainder target positive).1.val
      (RootCoordinates.prepareJetDecay origin jet remainder target positive).1.property.le).Contains point)
    (leftStart rightStart : Nat) :
    Equivalence.Comparison
      (Sampling.approximation ((Coherence.exact (point ^ (genus + 1))).mul
        (overlap.oddJetPullback nonzero differential pairs branch bound
          origin jet remainder coefficientCache residualCache factor).1.error).name)
      (Sampling.approximation (Coherence.exact 0).name) leftStart rightStart
      target := by
  let request := RootCoordinates.prepareJetDecay origin jet remainder target positive
  let pulled := overlap.oddJetPullback nonzero differential pairs branch bound
    origin jet remainder coefficientCache residualCache factor
  let compared := request.2 point overlap.regular ⟨overlap.regularRoot, overlap.regularRoot_eq⟩
    coefficientCache residualCache factor
    pulled.1 inside leftStart rightStart (target / 2)
      (Fraction.Order.Field.div_pos_direct positive (by decide))
  have paid : target / 2 + target / 2 = target := by
    calc
      _ = (target / 2) * 2 := by ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)
  exact compared.weaken target paid.le

/-- The positive even coordinate belongs to the actual scaled cap root and agrees operationally with one. -/
private def even_fixed_coordinate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical} (regular : Owners.Point cap point)
    (parity : HyperellipticReciprocal.originOrder curve = 0) :
    let retained := Overlap.Scaled.even regular parity
    NamedEquivalent retained.2.2.val.coordinate.prepared.denominator.name (Coherence.exact 1).name :=
  Overlap.Scaled.factor_agrees (Overlap.Scaled.even regular parity)

/-- The other even coordinate retains the negative of that same actual regular-root occurrence. -/
private def even_negative_fixed_coordinate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical} (regular : Owners.Point cap point)
    (parity : HyperellipticReciprocal.originOrder curve = 0) :
    let retained := Overlap.Scaled.evenNegative regular parity
    NamedEquivalent retained.2.2.val.coordinate.prepared.denominator.name (Coherence.exact (-1)).name :=
  Overlap.Scaled.factor_agrees (Overlap.Scaled.evenNegative regular parity)

/-- The original ramified coordinate agrees with the same supplied uniformizer at its actual squared point. -/
private def odd_fixed_coordinate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    (uniformizer : Canonical) (nonzero : uniformizer ≠ 0) (regular : Owners.Point cap (uniformizer ^ 2))
    (parity : HyperellipticReciprocal.originOrder curve = 1) :
    let retained := Overlap.Scaled.odd uniformizer nonzero regular parity
    NamedEquivalent retained.2.2.val.coordinate.prepared.denominator.name (Coherence.exact uniformizer).name :=
  Overlap.Scaled.factor_agrees (Overlap.Scaled.odd uniformizer nonzero regular parity)

/-- Both even sheets retain the complete same supplied original regular-model point. -/
private theorem even_retained_point {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical} (regular : Owners.Point cap point)
    (parity : HyperellipticReciprocal.originOrder curve = 0) :
    (Overlap.Scaled.even regular parity).2.2.val.regular = regular ∧
      (Overlap.Scaled.evenNegative regular parity).2.2.val.regular = regular := ⟨rfl, rfl⟩

/-- The ramified construction retains the complete original regular-model point at the actual squared uniformizer. -/
private theorem odd_retained_point {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    (uniformizer : Canonical) (nonzero : uniformizer ≠ 0) (regular : Owners.Point cap (uniformizer ^ 2))
    (parity : HyperellipticReciprocal.originOrder curve = 1) :
    (Overlap.Scaled.odd uniformizer nonzero regular parity).2.2.val.regular = regular := rfl

/-- The positive even source passes its actual chart tangent and supplied affine caches through the form comparison. -/
private def even_fixed_pullback {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {point : Canonical} (regular : Owners.Point cap point) (nonzero : point ≠ 0)
    (parity : HyperellipticReciprocal.originOrder curve = 0)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (affine : ReciprocalRootNames.ScaledRoot (Overlap.Scaled.even regular parity).overlap.reciprocal
      ((point⁻¹) ^ (genus + 1)) curve.polynomial point⁻¹)
    (reading : { value : Canonical // value = differential.scale * differential.numerator.eval point⁻¹ }) :
    NamedEquivalent
      ((Coherence.exact (Primitives.tangent curve point)).mul
        ((Coherence.exact (-((point⁻¹) ^ 2))).mul
          (differential.value point⁻¹ affine.certificate.value affine.certificate.apart))).name
      ((Coherence.exact 1).mul
        (CoherentNamed.div (Coherence.exact (point ^ (genus + 1) * (-((point⁻¹) ^ 2) * reading.val)))
          (Overlap.Scaled.even regular parity).overlap.regularRoot.value
          (Overlap.Scaled.even regular parity).overlap.regularRoot.apart)).name :=
  (Overlap.Scaled.even regular parity).even_pullback nonzero parity differential pairs affine reading

/-- The ramified source uses the actual squared chart point and its original twice-uniformizer tangent. -/
private def odd_fixed_pullback {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    (uniformizer : Canonical) (nonzero : uniformizer ≠ 0) (regular : Owners.Point cap (uniformizer ^ 2))
    (parity : HyperellipticReciprocal.originOrder curve = 1)
    (differential : OddPowerDifferential curve.polynomial) (pairs : differential.denominatorPairs = 0)
    (affine : ReciprocalRootNames.ScaledRoot
      (Overlap.Scaled.odd uniformizer nonzero regular parity).overlap.reciprocal
      (((uniformizer ^ 2)⁻¹) ^ (genus + 1)) curve.polynomial (uniformizer ^ 2)⁻¹)
    (reading : { value : Canonical //
      value = differential.scale * differential.numerator.eval (uniformizer ^ 2)⁻¹ }) :
    NamedEquivalent
      ((Coherence.exact (Primitives.tangent curve uniformizer)).mul
        ((Coherence.exact (-(((uniformizer ^ 2)⁻¹) ^ 2))).mul
          (differential.value (uniformizer ^ 2)⁻¹ affine.certificate.value affine.certificate.apart))).name
      ((Coherence.exact 2).mul
        (CoherentNamed.div
          (Coherence.exact ((uniformizer ^ 2) ^ (genus + 1) * (-(((uniformizer ^ 2)⁻¹) ^ 2) * reading.val)))
          (Overlap.Scaled.odd uniformizer nonzero regular parity).overlap.regularRoot.value
          (Overlap.Scaled.odd uniformizer nonzero regular parity).overlap.regularRoot.apart)).name :=
  (Overlap.Scaled.odd uniformizer nonzero regular parity).odd_pullback
    uniformizer nonzero parity differential pairs affine reading

end CapErrorBounds

section WholeFormObservation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Data.Rat.Fraction (Rational)

/-- The original numerical model and whole affine differential supply an actual finite cap-form request. -/
private def wholeFormReading {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (differential : OddPowerDifferential curve.polynomial) (cap : ReciprocalInnerInverse.Data curve collar)
    (parameter : Canonical) (nonzero : parameter ≠ 0)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (target : Rational) (positive : 0 < target) : FormReadings.Reading differential cap parameter inside target :=
  FormReadings.read differential cap parameter nonzero inside target positive

/-- The request consumes the same cached complete coefficient and pays its actual observed process radius. -/
private theorem wholeFormReading_paid {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (differential : OddPowerDifferential curve.polynomial) (cap : ReciprocalInnerInverse.Data curve collar)
    (parameter : Canonical) (nonzero : parameter ≠ 0)
    (inside : collar.box.Contains (Primitives.point curve parameter))
    (target : Rational) (positive : 0 < target) :
    (wholeFormReading differential cap parameter nonzero inside target positive).request.reading.radius < target :=
  FormReadings.Reading.radius_lt _

end WholeFormObservation

end TestPurelib.Curves.Hyperelliptic.OddPower
