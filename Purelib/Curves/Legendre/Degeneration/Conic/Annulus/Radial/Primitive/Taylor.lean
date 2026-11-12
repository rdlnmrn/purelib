module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent.Expansion
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Taylor
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Factorization
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Admission
import Purelib.Calculus.Jet.Quadratic.Composition.Bounds
import Purelib.Calculus.Jet.Quadratic.Product.Bounds
import Purelib.Calculus.Jet.Quadratic.SquareRoot.Radicand.Bounds
import Purelib.Calculus.Jet.Quadratic.Polynomial.Bounds
import Purelib.Geometry.Rational.Box.Square.Centered.Norm
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Quadratic.Split
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Calculus.Jet.Quadratic.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Primitive endpoint Taylor certificates on the original radial chart

The same original source and target Readings retain their cofactor root
observations at fourth-power chart accuracy. The prescribed original base
and ordinate expansions construct polynomial, inverse and finite odd-power
certificates. Their product gives the independently prescribed primitive
endpoints and an actual quantified quadratic chart remainder.

The scalar slope is the constructed chain and product rule on these exact
readings. Agreement with an independently observed cleared derivative,
uniform fixed-box ceilings and primitive integral comparisons are separate.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor

open Purelib.Curves.Hyperelliptic.Differentials.OddPower
open Purelib.Polynomial.Dense
open Purelib.Calculus.Jet.Quadratic.SquareRoot

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time delta : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside time} {lastInside : FixedRootBoxPath.Inside (time + delta)}

/-- One unchanged original cofactor observation pays the actual chart increment's fourth-power residual scale. -/
private theorem paid_residual {cofactor : Canonical} {accuracy : AccuracyRequest}
    {root : CertifiedSquareRoot.Certificate cofactor}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy)
    (accuracy_eq : accuracy.tolerance = delta ^ 4) :
    Norm.Basic.normSq (sample.reading * sample.reading - cofactor) ≤
      1 * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
  rewrite [Fraction.Field.one_mul, Stereographic.Tangent.increment_fourth]
  exact sample.reading_residual_lt.le.trans_eq accuracy_eq

public section

set_option genInjectivity false in
/-- Actual prescribed primitive endpoints and their finite scalar chart Taylor certificate on two original observations.

The original primitive, quarter, source/target Readings and complete selected
cofactor observations remain indices. The certificate's own computed factor
pays its actual chain-rule remainder; no derivative or integral relation is
required as a field or supplied by a caller.
-/
structure Expansion (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy) where
  /-- Both actual original root observations pay the same fourth-power chart request. -/
  accuracy_eq : accuracy.tolerance = delta ^ 4
  /-- The original scalar chart certificate retains its computed actual slope, remainder and finite factor. -/
  certificate : Quadratic.Basic.Certificate (Stereographic.Tangent.increment delta)
  /-- The base is the independently prescribed original primitive at the same selected source cofactor reading. -/
  base_eq : certificate.base = Primitive.reading (site := site) primitive quarter time sourceSample.reading
  /-- The output is the prescribed primitive at the distinct actual selected target cofactor reading. -/
  output_eq : certificate.output =
    Primitive.reading (site := site) primitive quarter (time + delta) targetSample.reading

constructive_injectivity Expansion

/-- Construct the original primitive's actual finite chart expansion from both retained fourth-power observations.

The original tangent constructors prescribe both base and ordinate endpoint
certificates. Actual root admission and original signed-box containment derive
cofactor floors and their sum floor. Intrinsic regularity derives both exact
ordinate floors. Existing stable inverse, polynomial, composition and product
constructors then compute every remainder internally without division by the
chart increment or substitution of arithmetic witnesses.
-/
def build (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (accuracy_eq : accuracy.tolerance = delta ^ 4) :
    Expansion primitive source target accuracy sourceSample targetSample := by
  let base := Tangent.baseExpansion site parameter 2 quarter positive actual.data.lower actual.data.upper time delta
  let ordinate := Tangent.ordinateExpansion site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have unit := Stereographic.Tangent.increment_unit firstInside lastInside
  have canonicalUnit : Canonical.normSq (Stereographic.Tangent.increment delta) ≤ 1 := by
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact unit
  have baseFirst := Tangent.baseExpansion_base site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have baseLast := Tangent.baseExpansion_output site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have ordinateFirst := Tangent.ordinateExpansion_base site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have ordinateLast := Tangent.ordinateExpansion_output site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have sourcePointInside : (spatialBox site).Contains base.base := by
    rewrite [baseFirst]
    exact point_inside site parameter 2 (Waist.direction quarter time) positive
      actual.data.lower actual.data.upper actual.data.bound
  have targetPointInside : (spatialBox site).Contains base.output := by
    rewrite [baseLast]
    exact point_inside site parameter 2 (Waist.direction quarter (time + delta)) positive
      actual.data.lower actual.data.upper actual.data.bound
  let numeratorOuter := Quadratic.Polynomial.certificateInBox primitive.numerator (spatialBox site)
    base.base base.output sourcePointInside targetPointInside
  let numerator := base.compose numeratorOuter canonicalUnit
  let cofactorOuter := Quadratic.Polynomial.certificateInBox (unitPolynomial site) (spatialBox site)
    base.base base.output sourcePointInside targetPointInside
  let cofactor := base.compose cofactorOuter canonicalUnit
  have cofactorFirst : cofactor.base = (unitPolynomial site).eval
      (point site parameter 2 (Waist.direction quarter time) positive).base :=
    congrArg (unitPolynomial site).eval baseFirst
  have cofactorLast : cofactor.output = (unitPolynomial site).eval
      (point site parameter 2 (Waist.direction quarter (time + delta)) positive).base :=
    congrArg (unitPolynomial site).eval baseLast
  have sourceSigned := source.signed.contains
    (sourceSample.reading_in_initial_box source.lift.unitOwner source.lift.unitRoot_eq)
  have targetSigned := target.signed.contains
    (targetSample.reading_in_initial_box target.lift.unitOwner target.lift.unitRoot_eq)
  have sourceLower : (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq sourceSample.reading :=
    UnitRoot.root_normSq_lower site (by
      rewrite [baseFirst] at sourcePointInside
      exact sourcePointInside)
      (sourceSample.reading_residual_lt_target source.lift.unitOwner source.lift.unitRoot_eq).le
  have targetLower : (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq targetSample.reading :=
    UnitRoot.root_normSq_lower site (by
      rewrite [baseLast] at targetPointInside
      exact targetPointInside)
      (targetSample.reading_residual_lt_target target.lift.unitOwner target.lift.unitRoot_eq).le
  have sourceResidual : Norm.Basic.normSq (sourceSample.reading * sourceSample.reading - cofactor.base) ≤
      1 * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    rewrite [cofactorFirst]
    exact paid_residual sourceSample accuracy_eq
  have targetResidual : Norm.Basic.normSq (targetSample.reading * targetSample.reading - cofactor.output) ≤
      1 * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    rewrite [cofactorLast]
    exact paid_residual targetSample accuracy_eq
  let cofactorInverse := Radicand.inverseCertificate cofactor
    sourceSample.reading targetSample.reading 1 1 (Norm.Basic.normSq cofactor.slope) (1 / 16) 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) sourceLower targetLower
    (by decide +kernel) (UnitRoot.box_sum_lower site sourceSigned targetSigned)
    (Fraction.Order.Basic.le_refl _) unit sourceResidual targetResidual
  let floor := (9 / 16) * Norm.Basic.normSq (halfGap site parameter)
  have floorPositive : 0 < floor := Arithmetic.mul_pos_direct (by decide +kernel)
    (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm))
  have ordinateSourceLower : floor ≤ Norm.Basic.normSq ordinate.base := by
    rewrite [ordinateFirst]
    exact parallel_ordinate_lower site parameter (Waist.direction quarter time)
  have ordinateTargetLower : floor ≤ Norm.Basic.normSq ordinate.output := by
    rewrite [ordinateLast]
    exact parallel_ordinate_lower site parameter (Waist.direction quarter (time + delta))
  let ordinateReciprocal := Radicand.reciprocalCertificate ordinate.base ordinate.output floor
    floorPositive ordinateSourceLower ordinateTargetLower
  let ordinateInverse := ordinate.compose ordinateReciprocal canonicalUnit
  let powerPolynomial := Derivative.Taylor.powerPolynomial primitive
  let cofactorPowerOuter := Quadratic.Polynomial.certificate powerPolynomial cofactorInverse.base cofactorInverse.output
  let cofactorPower := cofactorInverse.compose cofactorPowerOuter canonicalUnit
  let ordinatePowerOuter := Quadratic.Polynomial.certificate powerPolynomial ordinateInverse.base ordinateInverse.output
  let ordinatePower := ordinateInverse.compose ordinatePowerOuter canonicalUnit
  let numeratorOrdinate := Quadratic.Product.certificate numerator ordinatePower unit
  let product := Quadratic.Product.certificate numeratorOrdinate cofactorPower unit
  let certificate := product.scale primitive.scale
  have numeratorFirst : numerator.base = primitive.numerator.eval
      (point site parameter 2 (Waist.direction quarter time) positive).base :=
    congrArg primitive.numerator.eval baseFirst
  have numeratorLast : numerator.output = primitive.numerator.eval
      (point site parameter 2 (Waist.direction quarter (time + delta)) positive).base :=
    congrArg primitive.numerator.eval baseLast
  have cofactorInverseFirst : cofactorInverse.base = sourceSample.reading⁻¹ := rfl
  have cofactorInverseLast : cofactorInverse.output = targetSample.reading⁻¹ := rfl
  have ordinateInverseFirst : ordinateInverse.base =
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ :=
    congrArg (fun value : Canonical => value⁻¹) ordinateFirst
  have ordinateInverseLast : ordinateInverse.output =
      (point site parameter 2 (Waist.direction quarter (time + delta)) positive).ordinate⁻¹ :=
    congrArg (fun value : Canonical => value⁻¹) ordinateLast
  have cofactorPowerFirst : cofactorPower.base = sourceSample.reading⁻¹ ^ primitive.denominatorExponent := by
    change powerPolynomial.eval cofactorInverse.base = _
    rewrite [Derivative.Taylor.powerPolynomial_eval, cofactorInverseFirst]
    rfl
  have cofactorPowerLast : cofactorPower.output = targetSample.reading⁻¹ ^ primitive.denominatorExponent := by
    change powerPolynomial.eval cofactorInverse.output = _
    rewrite [Derivative.Taylor.powerPolynomial_eval, cofactorInverseLast]
    rfl
  have ordinatePowerFirst : ordinatePower.base =
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^ primitive.denominatorExponent := by
    change powerPolynomial.eval ordinateInverse.base = _
    rewrite [Derivative.Taylor.powerPolynomial_eval, ordinateInverseFirst]
    rfl
  have ordinatePowerLast : ordinatePower.output =
      (point site parameter 2 (Waist.direction quarter (time + delta)) positive).ordinate⁻¹ ^
        primitive.denominatorExponent := by
    change powerPolynomial.eval ordinateInverse.output = _
    rewrite [Derivative.Taylor.powerPolynomial_eval, ordinateInverseLast]
    rfl
  exact
    { accuracy_eq := accuracy_eq
      certificate := certificate
      base_eq := by
        change primitive.scale * (numerator.base * ordinatePower.base * cofactorPower.base) = _
        rewrite [numeratorFirst, ordinatePowerFirst, cofactorPowerFirst]
        unfold Primitive.reading
        ring1
      output_eq := by
        change primitive.scale * (numerator.output * ordinatePower.output * cofactorPower.output) = _
        rewrite [numeratorLast, ordinatePowerLast, cofactorPowerLast]
        unfold Primitive.reading
        ring1 }

/-- The actual chart builder's slope is its prescribed product and chain rule on the same source cofactor reading.

Both tangent constructors and every original polynomial, reciprocal and
power constructor supply their actual computed slopes. The retained
specification merely reads the original numerator derivative cache; no
spatial derivative agreement is assumed.
-/
theorem build_slope_eq (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (accuracy_eq : accuracy.tolerance = delta ^ 4)
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive) :
    (build primitive source target regular accuracy sourceSample targetSample accuracy_eq).certificate.slope =
      OddPower.Derivative.Factorization.chainReading specification
        (point site parameter 2 (Waist.direction quarter time) positive).base
        (point site parameter 2 (Waist.direction quarter time) positive).ordinate sourceSample.reading
        (Tangent.baseVelocity site parameter 2 quarter time)
        (Tangent.ordinateVelocity site parameter 2 quarter time) 1 := by
  let base := Tangent.baseExpansion site parameter 2 quarter positive actual.data.lower actual.data.upper time delta
  let ordinate := Tangent.ordinateExpansion site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  let power := Derivative.Taylor.powerPolynomial primitive
  unfold build
  change primitive.scale *
      (((base.slope * (GCD.derivative primitive.numerator).eval base.base) * power.eval ordinate.base⁻¹ +
          primitive.numerator.eval base.base *
            ((ordinate.slope * (-(ordinate.base⁻¹ * ordinate.base⁻¹))) *
              (GCD.derivative power).eval ordinate.base⁻¹)) * power.eval sourceSample.reading⁻¹ +
        (primitive.numerator.eval base.base * power.eval ordinate.base⁻¹) *
          (((Quadratic.SquareRoot.half *
              (base.slope * (GCD.derivative (unitPolynomial site)).eval base.base) * sourceSample.reading⁻¹) *
              (-(sourceSample.reading⁻¹ * sourceSample.reading⁻¹))) *
            (GCD.derivative power).eval sourceSample.reading⁻¹)) = _
  dsimp only [base, ordinate, power]
  rewrite [Tangent.baseExpansion_slope, Tangent.baseExpansion_base, Tangent.ordinateExpansion_slope,
    Tangent.ordinateExpansion_base, Derivative.Taylor.powerPolynomial_eval,
    Derivative.Taylor.powerPolynomial_eval, Derivative.Taylor.powerPolynomial_derivative_eval,
    Derivative.Taylor.powerPolynomial_derivative_eval]
  unfold unitPolynomial
  rewrite [Gaussian.Linear.Translated.derivative_eval]
  have ordinatePower :
      ((point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ *
        (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹) *
          (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^
            (2 * primitive.denominatorPairs) =
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^
        (primitive.denominatorExponent + 1) := by
    rewrite [← pow_two, ← pow_add]
    exact congrArg (fun exponent : Nat =>
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^ exponent)
      (by unfold OddPowerDifferential.denominatorExponent; omega0)
  have cofactorPower :
      (sourceSample.reading⁻¹ * sourceSample.reading⁻¹ * sourceSample.reading⁻¹) *
        sourceSample.reading⁻¹ ^ (2 * primitive.denominatorPairs) =
      sourceSample.reading⁻¹ ^ (primitive.denominatorExponent + 2) := by
    calc
      _ = sourceSample.reading⁻¹ ^ 3 * sourceSample.reading⁻¹ ^ (2 * primitive.denominatorPairs) := by
        rewrite [pow_succ, pow_two]; ring1
      _ = _ := by
        rewrite [← pow_add]
        exact congrArg (fun exponent : Nat => sourceSample.reading⁻¹ ^ exponent)
          (by unfold OddPowerDifferential.denominatorExponent; omega0)
  have half : Quadratic.SquareRoot.half = (2 : Canonical)⁻¹ := by decide +kernel
  unfold OddPower.Derivative.Factorization.chainReading
  rewrite [specification.numeratorDerivative_eq, Algebra.Field.ExplicitField.div_eq_mul_inv, half]
  have regroup (scale numerator derivative baseVelocity ordinateVelocity exponent half
      ordinateInverse cofactorInverse ordinateTail cofactorTail ordinatePower cofactorPower : Canonical) :
      scale *
        (((baseVelocity * derivative) * ordinatePower +
          numerator * ((ordinateVelocity * (-(ordinateInverse * ordinateInverse))) *
            (exponent * ordinateTail))) * cofactorPower +
          (numerator * ordinatePower) *
            (((half * baseVelocity * cofactorInverse) * (-(cofactorInverse * cofactorInverse))) *
              (exponent * cofactorTail))) =
        scale * (derivative * baseVelocity * ordinatePower * cofactorPower -
          exponent * numerator * ordinateVelocity * (ordinateInverse * ordinateInverse * ordinateTail) *
            cofactorPower -
          (exponent * half) * numerator * baseVelocity * ordinatePower *
            (cofactorInverse * cofactorInverse * cofactorInverse * cofactorTail)) := by ring1
  calc
    _ = primitive.scale *
      ((GCD.derivative primitive.numerator).eval
          (point site parameter 2 (Waist.direction quarter time) positive).base *
          Tangent.baseVelocity site parameter 2 quarter time *
          (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^
            primitive.denominatorExponent * sourceSample.reading⁻¹ ^ primitive.denominatorExponent -
        OddPower.Derivative.exponentCoefficient primitive * primitive.numerator.eval
          (point site parameter 2 (Waist.direction quarter time) positive).base *
          Tangent.ordinateVelocity site parameter 2 quarter time *
          (((point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ *
              (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹) *
            (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^
              (2 * primitive.denominatorPairs)) * sourceSample.reading⁻¹ ^ primitive.denominatorExponent -
        (OddPower.Derivative.exponentCoefficient primitive * (2 : Canonical)⁻¹) * primitive.numerator.eval
          (point site parameter 2 (Waist.direction quarter time) positive).base *
          Tangent.baseVelocity site parameter 2 quarter time *
          (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^
            primitive.denominatorExponent *
          ((sourceSample.reading⁻¹ * sourceSample.reading⁻¹ * sourceSample.reading⁻¹) *
            sourceSample.reading⁻¹ ^ (2 * primitive.denominatorPairs))) := by
      rewrite [Gaussian.Basic.mul_one]
      exact regroup primitive.scale
        (primitive.numerator.eval (point site parameter 2 (Waist.direction quarter time) positive).base)
        ((GCD.derivative primitive.numerator).eval
          (point site parameter 2 (Waist.direction quarter time) positive).base)
        (Tangent.baseVelocity site parameter 2 quarter time)
        (Tangent.ordinateVelocity site parameter 2 quarter time)
        (OddPower.Derivative.exponentCoefficient primitive) (2 : Canonical)⁻¹
        (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ sourceSample.reading⁻¹
        ((point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^
          (2 * primitive.denominatorPairs))
        (sourceSample.reading⁻¹ ^ (2 * primitive.denominatorPairs))
        ((point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^ primitive.denominatorExponent)
        (sourceSample.reading⁻¹ ^ primitive.denominatorExponent)
    _ = _ := by
      rewrite [ordinatePower, cofactorPower]
      rewrite [Gaussian.Basic.mul_one]
      rfl

namespace Expansion

/-- The actual prescribed source and target primitive readings pay the constructed scalar chart Taylor remainder.

The original selected cofactor observations and chart increment remain
unchanged. The constructed certificate's own finite factor bounds the exact
endpoint difference from its retained chain/product-rule slope.
-/
theorem remainder_le {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {source : Transport.Reading actual time firstInside} {target : Transport.Reading actual (time + delta) lastInside}
    {accuracy : AccuracyRequest}
    {sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy}
    {targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy}
    (expansion : Expansion primitive source target accuracy sourceSample targetSample) :
    Norm.Basic.normSq
      (Primitive.reading (site := site) primitive quarter (time + delta) targetSample.reading -
        Primitive.reading (site := site) primitive quarter time sourceSample.reading -
          Stereographic.Tangent.increment delta * expansion.certificate.slope) ≤
      expansion.certificate.factor * delta ^ 4 := by
  rewrite [← expansion.base_eq, ← expansion.output_eq, expansion.certificate.expansion]
  have paid : Norm.Basic.normSq expansion.certificate.remainder ≤
      expansion.certificate.factor * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    simpa only [Norm.Basic.normSq_eq_canonical] using expansion.certificate.remainder_le
  exact paid.trans_eq (congrArg (fun value : Fraction.Rational => expansion.certificate.factor * value)
    (Stereographic.Tangent.increment_fourth delta))

end Expansion

end

public section

/-- The original chart, fixed inverse boxes and coefficient programs compute the primitive's uniform remainder ceiling.

Intrinsic regularity pays the fixed ordinate inverse box; the same original
cofactor floor pays its fixed inverse box. Original finite Horner scans and
composition/product factors compute this ceiling independently of times,
chart increments, cofactor sample indices or arithmetic witnesses.
-/
def ceiling (site : Fin 2) (parameter : Canonical)
    (primitive : OddPowerDifferential (Paths.polynomial parameter)) (regular : parameter ≠ criticalValue site) :
    Fraction.Rational :=
  let gap := Norm.Basic.normSq (halfGap site parameter)
  let chart := (25 / 4) * gap
  let chartSensitivity := 2 * (chart + chart)
  let floor := (9 / 16) * gap
  let ordinateBox := Box.Square.Centered.normBox floor⁻¹
    (Fraction.Order.Field.inv_pos_direct (parallel_ordinate_floor_positive site parameter regular)).le
  let cofactorBox := Box.Square.Centered.normBox 16 (by decide +kernel)
  let numeratorValue := Gaussian.Bounds.Box.denseEvalNormBound primitive.numerator (spatialBox site)
  let numeratorDerivative := Derivative.Taylor.slopeCeiling primitive.numerator (spatialBox site)
  let numeratorTaylor := Derivative.Taylor.remainderCeiling primitive.numerator (spatialBox site)
  let numeratorSlope := chart * numeratorDerivative
  let numeratorFactor := 2 * (numeratorDerivative * chart + numeratorTaylor * chartSensitivity ^ 2)
  let cofactorDerivative := Derivative.Taylor.slopeCeiling (unitPolynomial site) (spatialBox site)
  let cofactorTaylor := Derivative.Taylor.remainderCeiling (unitPolynomial site) (spatialBox site)
  let cofactorSlope := chart * cofactorDerivative
  let cofactorFactor := 2 * (cofactorDerivative * chart + cofactorTaylor * chartSensitivity ^ 2)
  let cofactorInverseSlope := cofactorSlope * (1 / 16)⁻¹ ^ 3
  let cofactorInverseFactor := Radicand.inverseCeiling cofactorFactor cofactorSlope (1 / 16) 1 1 1
  let ordinateInverseSlope := chart * floor⁻¹ ^ 2
  let ordinateInverseFactor := 2 * (floor⁻¹ ^ 2 * chart + floor⁻¹ ^ 3 * chartSensitivity ^ 2)
  let power := Derivative.Taylor.powerPolynomial primitive
  let cofactorPowerDerivative := Derivative.Taylor.slopeCeiling power cofactorBox
  let cofactorPowerTaylor := Derivative.Taylor.remainderCeiling power cofactorBox
  let cofactorPowerSlope := cofactorInverseSlope * cofactorPowerDerivative
  let cofactorPowerFactor := 2 * (cofactorPowerDerivative * cofactorInverseFactor +
    cofactorPowerTaylor * (2 * (cofactorInverseSlope + cofactorInverseFactor)) ^ 2)
  let ordinatePowerDerivative := Derivative.Taylor.slopeCeiling power ordinateBox
  let ordinatePowerTaylor := Derivative.Taylor.remainderCeiling power ordinateBox
  let ordinatePowerSlope := ordinateInverseSlope * ordinatePowerDerivative
  let ordinatePowerFactor := 2 * (ordinatePowerDerivative * ordinateInverseFactor +
    ordinatePowerTaylor * (2 * (ordinateInverseSlope + ordinateInverseFactor)) ^ 2)
  let ordinatePowerValue := floor⁻¹ ^ primitive.denominatorExponent
  let cofactorPowerValue : Fraction.Rational := (1 / 16)⁻¹ ^ primitive.denominatorExponent
  let numeratorOrdinateValue := numeratorValue * ordinatePowerValue
  let numeratorOrdinateSlope := 2 * (numeratorSlope * ordinatePowerValue + numeratorValue * ordinatePowerSlope)
  let numeratorOrdinateFactor := 4 * (ordinatePowerValue * numeratorFactor + numeratorValue * ordinatePowerFactor +
    (2 * (numeratorSlope + numeratorFactor)) * (2 * (ordinatePowerSlope + ordinatePowerFactor)))
  Norm.Basic.normSq primitive.scale *
    (4 * (cofactorPowerValue * numeratorOrdinateFactor + numeratorOrdinateValue * cofactorPowerFactor +
      (2 * (numeratorOrdinateSlope + numeratorOrdinateFactor)) * (2 * (cofactorPowerSlope + cofactorPowerFactor))))

/-- Intrinsic regularity makes the computed fixed primitive chart ceiling nonnegative.

The original finite coefficient bounds and positive ordinate/cofactor floors
pay every composition and product budget. This proof concerns the computed
ceiling itself and requires no chart time, sample or expansion certificate.
-/
theorem ceiling_nonnegative (site : Fin 2) (parameter : Canonical)
    (primitive : OddPowerDifferential (Paths.polynomial parameter)) (regular : parameter ≠ criticalValue site) :
    0 ≤ ceiling site parameter primitive regular := by
  let gap := Norm.Basic.normSq (halfGap site parameter)
  let chart := (25 / 4) * gap
  let chartSensitivity := 2 * (chart + chart)
  let floor := (9 / 16) * gap
  let ordinateBox := Box.Square.Centered.normBox floor⁻¹
    (Fraction.Order.Field.inv_pos_direct (parallel_ordinate_floor_positive site parameter regular)).le
  let cofactorBox := Box.Square.Centered.normBox 16 (by decide +kernel)
  let numeratorValue := Gaussian.Bounds.Box.denseEvalNormBound primitive.numerator (spatialBox site)
  let numeratorDerivative := Derivative.Taylor.slopeCeiling primitive.numerator (spatialBox site)
  let numeratorTaylor := Derivative.Taylor.remainderCeiling primitive.numerator (spatialBox site)
  let numeratorSlope := chart * numeratorDerivative
  let numeratorFactor := 2 * (numeratorDerivative * chart + numeratorTaylor * chartSensitivity ^ 2)
  let cofactorDerivative := Derivative.Taylor.slopeCeiling (unitPolynomial site) (spatialBox site)
  let cofactorTaylor := Derivative.Taylor.remainderCeiling (unitPolynomial site) (spatialBox site)
  let cofactorSlope := chart * cofactorDerivative
  let cofactorFactor := 2 * (cofactorDerivative * chart + cofactorTaylor * chartSensitivity ^ 2)
  let cofactorInverseSlope := cofactorSlope * (1 / 16)⁻¹ ^ 3
  let cofactorInverseFactor := Radicand.inverseCeiling cofactorFactor cofactorSlope (1 / 16) 1 1 1
  let ordinateInverseSlope := chart * floor⁻¹ ^ 2
  let ordinateInverseFactor := 2 * (floor⁻¹ ^ 2 * chart + floor⁻¹ ^ 3 * chartSensitivity ^ 2)
  let power := Derivative.Taylor.powerPolynomial primitive
  let cofactorPowerDerivative := Derivative.Taylor.slopeCeiling power cofactorBox
  let cofactorPowerTaylor := Derivative.Taylor.remainderCeiling power cofactorBox
  let cofactorPowerSlope := cofactorInverseSlope * cofactorPowerDerivative
  let cofactorPowerFactor := 2 * (cofactorPowerDerivative * cofactorInverseFactor +
    cofactorPowerTaylor * (2 * (cofactorInverseSlope + cofactorInverseFactor)) ^ 2)
  let ordinatePowerDerivative := Derivative.Taylor.slopeCeiling power ordinateBox
  let ordinatePowerTaylor := Derivative.Taylor.remainderCeiling power ordinateBox
  let ordinatePowerSlope := ordinateInverseSlope * ordinatePowerDerivative
  let ordinatePowerFactor := 2 * (ordinatePowerDerivative * ordinateInverseFactor +
    ordinatePowerTaylor * (2 * (ordinateInverseSlope + ordinateInverseFactor)) ^ 2)
  let ordinatePowerValue := floor⁻¹ ^ primitive.denominatorExponent
  let cofactorPowerValue : Fraction.Rational := (1 / 16)⁻¹ ^ primitive.denominatorExponent
  let numeratorOrdinateValue := numeratorValue * ordinatePowerValue
  let numeratorOrdinateSlope := 2 * (numeratorSlope * ordinatePowerValue + numeratorValue * ordinatePowerSlope)
  let numeratorOrdinateFactor := 4 * (ordinatePowerValue * numeratorFactor + numeratorValue * ordinatePowerFactor +
    (2 * (numeratorSlope + numeratorFactor)) * (2 * (ordinatePowerSlope + ordinatePowerFactor)))
  have composition (innerSlope innerFactor outerSlope outerFactor : Fraction.Rational)
      (factorNonnegative : 0 ≤ innerFactor) (slopeNonnegative : 0 ≤ outerSlope)
      (outerNonnegative : 0 ≤ outerFactor) :
      0 ≤ 2 * (outerSlope * innerFactor + outerFactor * (2 * (innerSlope + innerFactor)) ^ 2) :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct slopeNonnegative factorNonnegative)
        (Arithmetic.mul_nonneg_direct outerNonnegative
          (Arithmetic.sq_nonneg_direct (2 * (innerSlope + innerFactor)))))
  have productSlope (leftValue rightValue leftSlope rightSlope : Fraction.Rational)
      (leftValueNonnegative : 0 ≤ leftValue) (rightValueNonnegative : 0 ≤ rightValue)
      (leftSlopeNonnegative : 0 ≤ leftSlope) (rightSlopeNonnegative : 0 ≤ rightSlope) :
      0 ≤ 2 * (leftSlope * rightValue + leftValue * rightSlope) :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct leftSlopeNonnegative rightValueNonnegative)
        (Arithmetic.mul_nonneg_direct leftValueNonnegative rightSlopeNonnegative))
  have product (leftValue rightValue leftSlope rightSlope leftFactor rightFactor : Fraction.Rational)
      (leftValueNonnegative : 0 ≤ leftValue) (rightValueNonnegative : 0 ≤ rightValue)
      (leftSlopeNonnegative : 0 ≤ leftSlope) (rightSlopeNonnegative : 0 ≤ rightSlope)
      (leftFactorNonnegative : 0 ≤ leftFactor) (rightFactorNonnegative : 0 ≤ rightFactor) :
      0 ≤ 4 * (rightValue * leftFactor + leftValue * rightFactor +
        (2 * (leftSlope + leftFactor)) * (2 * (rightSlope + rightFactor))) :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Arithmetic.add_le_add_direct
          (Arithmetic.mul_nonneg_direct rightValueNonnegative leftFactorNonnegative)
          (Arithmetic.mul_nonneg_direct leftValueNonnegative rightFactorNonnegative))
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.mul_nonneg_direct (by decide +kernel)
            (Arithmetic.add_le_add_direct leftSlopeNonnegative leftFactorNonnegative))
          (Arithmetic.mul_nonneg_direct (by decide +kernel)
            (Arithmetic.add_le_add_direct rightSlopeNonnegative rightFactorNonnegative))))
  have chartNonnegative : 0 ≤ chart :=
    Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)
  have floorInverse : 0 ≤ floor⁻¹ :=
    (Fraction.Order.Field.inv_pos_direct (parallel_ordinate_floor_positive site parameter regular)).le
  have cofactorInverse : (0 : Fraction.Rational) ≤ (1 / 16)⁻¹ := by decide +kernel
  have numeratorValueNonnegative : 0 ≤ numeratorValue :=
    (Bounds.Box.denseHornerNormBounds_nonneg primitive.numerator (spatialBox site)).1
  have numeratorDerivativeNonnegative : 0 ≤ numeratorDerivative :=
    (Bounds.Box.denseHornerNormBounds_nonneg (GCD.derivative primitive.numerator) (spatialBox site)).1
  have numeratorTaylorNonnegative : 0 ≤ numeratorTaylor :=
    (Bounds.Box.Taylor.denseHornerTaylorNormBounds_nonneg primitive.numerator (spatialBox site)).2.2
  have numeratorSlopeNonnegative : 0 ≤ numeratorSlope :=
    Arithmetic.mul_nonneg_direct chartNonnegative numeratorDerivativeNonnegative
  have numeratorFactorNonnegative : 0 ≤ numeratorFactor :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct numeratorDerivativeNonnegative chartNonnegative)
        (Arithmetic.mul_nonneg_direct numeratorTaylorNonnegative
          (Arithmetic.sq_nonneg_direct chartSensitivity)))
  have cofactorDerivativeNonnegative : 0 ≤ cofactorDerivative :=
    (Bounds.Box.denseHornerNormBounds_nonneg (GCD.derivative (unitPolynomial site)) (spatialBox site)).1
  have cofactorTaylorNonnegative : 0 ≤ cofactorTaylor :=
    (Bounds.Box.Taylor.denseHornerTaylorNormBounds_nonneg (unitPolynomial site) (spatialBox site)).2.2
  have cofactorFactorNonnegative : 0 ≤ cofactorFactor :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct cofactorDerivativeNonnegative chartNonnegative)
        (Arithmetic.mul_nonneg_direct cofactorTaylorNonnegative
          (Arithmetic.sq_nonneg_direct chartSensitivity)))
  have cofactorInverseSlopeNonnegative : 0 ≤ cofactorInverseSlope :=
    Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct chartNonnegative cofactorDerivativeNonnegative)
      (Arithmetic.pow_nonneg_direct cofactorInverse 3)
  have cofactorInverseFactorNonnegative : 0 ≤ cofactorInverseFactor :=
    Radicand.inverseCeiling_nonnegative cofactorFactorNonnegative
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ordinateInverseSlopeNonnegative : 0 ≤ ordinateInverseSlope :=
    Arithmetic.mul_nonneg_direct chartNonnegative
      (Arithmetic.pow_nonneg_direct floorInverse 2)
  have ordinateInverseFactorNonnegative : 0 ≤ ordinateInverseFactor :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.pow_nonneg_direct floorInverse 2) chartNonnegative)
        (Arithmetic.mul_nonneg_direct
          (Arithmetic.pow_nonneg_direct floorInverse 3)
          (Arithmetic.sq_nonneg_direct chartSensitivity)))
  have cofactorPowerDerivativeNonnegative : 0 ≤ cofactorPowerDerivative :=
    (Bounds.Box.denseHornerNormBounds_nonneg (GCD.derivative power) cofactorBox).1
  have cofactorPowerTaylorNonnegative : 0 ≤ cofactorPowerTaylor :=
    (Bounds.Box.Taylor.denseHornerTaylorNormBounds_nonneg power cofactorBox).2.2
  have cofactorPowerSlopeNonnegative : 0 ≤ cofactorPowerSlope :=
    Arithmetic.mul_nonneg_direct cofactorInverseSlopeNonnegative cofactorPowerDerivativeNonnegative
  have cofactorPowerFactorNonnegative : 0 ≤ cofactorPowerFactor :=
    composition cofactorInverseSlope cofactorInverseFactor cofactorPowerDerivative cofactorPowerTaylor
      cofactorInverseFactorNonnegative cofactorPowerDerivativeNonnegative cofactorPowerTaylorNonnegative
  have ordinatePowerDerivativeNonnegative : 0 ≤ ordinatePowerDerivative :=
    (Bounds.Box.denseHornerNormBounds_nonneg (GCD.derivative power) ordinateBox).1
  have ordinatePowerTaylorNonnegative : 0 ≤ ordinatePowerTaylor :=
    (Bounds.Box.Taylor.denseHornerTaylorNormBounds_nonneg power ordinateBox).2.2
  have ordinatePowerSlopeNonnegative : 0 ≤ ordinatePowerSlope :=
    Arithmetic.mul_nonneg_direct ordinateInverseSlopeNonnegative ordinatePowerDerivativeNonnegative
  have ordinatePowerFactorNonnegative : 0 ≤ ordinatePowerFactor :=
    composition ordinateInverseSlope ordinateInverseFactor ordinatePowerDerivative ordinatePowerTaylor
      ordinateInverseFactorNonnegative ordinatePowerDerivativeNonnegative ordinatePowerTaylorNonnegative
  have ordinatePowerValueNonnegative : 0 ≤ ordinatePowerValue :=
    Arithmetic.pow_nonneg_direct floorInverse primitive.denominatorExponent
  have cofactorPowerValueNonnegative : 0 ≤ cofactorPowerValue :=
    Arithmetic.pow_nonneg_direct cofactorInverse primitive.denominatorExponent
  have numeratorOrdinateValueNonnegative : 0 ≤ numeratorOrdinateValue :=
    Arithmetic.mul_nonneg_direct numeratorValueNonnegative ordinatePowerValueNonnegative
  have numeratorOrdinateSlopeNonnegative : 0 ≤ numeratorOrdinateSlope :=
    productSlope numeratorValue ordinatePowerValue numeratorSlope ordinatePowerSlope
      numeratorValueNonnegative ordinatePowerValueNonnegative numeratorSlopeNonnegative ordinatePowerSlopeNonnegative
  have numeratorOrdinateFactorNonnegative : 0 ≤ numeratorOrdinateFactor :=
    product numeratorValue ordinatePowerValue numeratorSlope ordinatePowerSlope numeratorFactor ordinatePowerFactor
      numeratorValueNonnegative ordinatePowerValueNonnegative numeratorSlopeNonnegative ordinatePowerSlopeNonnegative
      numeratorFactorNonnegative ordinatePowerFactorNonnegative
  have finalNonnegative := product numeratorOrdinateValue cofactorPowerValue numeratorOrdinateSlope
    cofactorPowerSlope numeratorOrdinateFactor cofactorPowerFactor numeratorOrdinateValueNonnegative
    cofactorPowerValueNonnegative numeratorOrdinateSlopeNonnegative cofactorPowerSlopeNonnegative
    numeratorOrdinateFactorNonnegative cofactorPowerFactorNonnegative
  exact Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg primitive.scale) finalNonnegative

/-- The actual chart builder's factor is bounded by its fixed original coefficient and geometry ceiling.

Every bound consumes the exact input certificate of the existing builder.
The original two-point power hulls refine into internally computed fixed
inverse boxes. No caller supplies a remainder conclusion, inverse enclosure
or replacement certificate, and the actual build operation is unchanged.
-/
theorem build_factor_le (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (accuracy_eq : accuracy.tolerance = delta ^ 4) :
    (build primitive source target regular accuracy sourceSample targetSample accuracy_eq).certificate.factor ≤
      ceiling site parameter primitive regular := by
  let base := Tangent.baseExpansion site parameter 2 quarter positive actual.data.lower actual.data.upper time delta
  let ordinate := Tangent.ordinateExpansion site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have unit := Stereographic.Tangent.increment_unit firstInside lastInside
  have canonicalUnit : Canonical.normSq (Stereographic.Tangent.increment delta) ≤ 1 := by
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact unit
  have baseFirst := Tangent.baseExpansion_base site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have baseLast := Tangent.baseExpansion_output site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have ordinateFirst := Tangent.ordinateExpansion_base site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have ordinateLast := Tangent.ordinateExpansion_output site parameter 2 quarter positive
    actual.data.lower actual.data.upper time delta
  have sourcePointInside : (spatialBox site).Contains base.base := by
    rewrite [baseFirst]
    exact point_inside site parameter 2 (Waist.direction quarter time) positive
      actual.data.lower actual.data.upper actual.data.bound
  have targetPointInside : (spatialBox site).Contains base.output := by
    rewrite [baseLast]
    exact point_inside site parameter 2 (Waist.direction quarter (time + delta)) positive
      actual.data.lower actual.data.upper actual.data.bound
  let numeratorOuter := Quadratic.Polynomial.certificateInBox primitive.numerator (spatialBox site)
    base.base base.output sourcePointInside targetPointInside
  let numerator := base.compose numeratorOuter canonicalUnit
  let cofactorOuter := Quadratic.Polynomial.certificateInBox (unitPolynomial site) (spatialBox site)
    base.base base.output sourcePointInside targetPointInside
  let cofactor := base.compose cofactorOuter canonicalUnit
  have cofactorFirst : cofactor.base = (unitPolynomial site).eval
      (point site parameter 2 (Waist.direction quarter time) positive).base :=
    congrArg (unitPolynomial site).eval baseFirst
  have cofactorLast : cofactor.output = (unitPolynomial site).eval
      (point site parameter 2 (Waist.direction quarter (time + delta)) positive).base :=
    congrArg (unitPolynomial site).eval baseLast
  have sourceSigned := source.signed.contains
    (sourceSample.reading_in_initial_box source.lift.unitOwner source.lift.unitRoot_eq)
  have targetSigned := target.signed.contains
    (targetSample.reading_in_initial_box target.lift.unitOwner target.lift.unitRoot_eq)
  have sourceLower : (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq sourceSample.reading :=
    UnitRoot.root_normSq_lower site (by
      rewrite [baseFirst] at sourcePointInside
      exact sourcePointInside)
      (sourceSample.reading_residual_lt_target source.lift.unitOwner source.lift.unitRoot_eq).le
  have targetLower : (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq targetSample.reading :=
    UnitRoot.root_normSq_lower site (by
      rewrite [baseLast] at targetPointInside
      exact targetPointInside)
      (targetSample.reading_residual_lt_target target.lift.unitOwner target.lift.unitRoot_eq).le
  have sourceResidual : Norm.Basic.normSq (sourceSample.reading * sourceSample.reading - cofactor.base) ≤
      1 * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    rewrite [cofactorFirst]
    exact paid_residual sourceSample accuracy_eq
  have targetResidual : Norm.Basic.normSq (targetSample.reading * targetSample.reading - cofactor.output) ≤
      1 * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    rewrite [cofactorLast]
    exact paid_residual targetSample accuracy_eq
  let cofactorInverse := Radicand.inverseCertificate cofactor
    sourceSample.reading targetSample.reading 1 1 (Norm.Basic.normSq cofactor.slope) (1 / 16) 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) sourceLower targetLower
    (by decide +kernel) (UnitRoot.box_sum_lower site sourceSigned targetSigned)
    (Fraction.Order.Basic.le_refl _) unit sourceResidual targetResidual
  let floor := (9 / 16) * Norm.Basic.normSq (halfGap site parameter)
  have floorPositive : 0 < floor := Arithmetic.mul_pos_direct (by decide +kernel)
    (Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero (by decide +kernel) regular.symm))
  have ordinateSourceLower : floor ≤ Norm.Basic.normSq ordinate.base := by
    rewrite [ordinateFirst]
    exact parallel_ordinate_lower site parameter (Waist.direction quarter time)
  have ordinateTargetLower : floor ≤ Norm.Basic.normSq ordinate.output := by
    rewrite [ordinateLast]
    exact parallel_ordinate_lower site parameter (Waist.direction quarter (time + delta))
  let ordinateReciprocal := Radicand.reciprocalCertificate ordinate.base ordinate.output floor
    floorPositive ordinateSourceLower ordinateTargetLower
  let ordinateInverse := ordinate.compose ordinateReciprocal canonicalUnit
  let powerPolynomial := Derivative.Taylor.powerPolynomial primitive
  let cofactorPowerOuter := Quadratic.Polynomial.certificate powerPolynomial cofactorInverse.base cofactorInverse.output
  let cofactorPower := cofactorInverse.compose cofactorPowerOuter canonicalUnit
  let ordinatePowerOuter := Quadratic.Polynomial.certificate powerPolynomial ordinateInverse.base ordinateInverse.output
  let ordinatePower := ordinateInverse.compose ordinatePowerOuter canonicalUnit
  let numeratorOrdinate := Quadratic.Product.certificate numerator ordinatePower unit
  let product := Quadratic.Product.certificate numeratorOrdinate cofactorPower unit
  let certificate := product.scale primitive.scale
  let gap := Norm.Basic.normSq (halfGap site parameter)
  let chart := (25 / 4) * gap
  let chartSensitivity := 2 * (chart + chart)
  let ordinateBox := Box.Square.Centered.normBox floor⁻¹ (Fraction.Order.Field.inv_pos_direct floorPositive).le
  let cofactorBox := Box.Square.Centered.normBox 16 (by decide +kernel)
  let numeratorValue := Gaussian.Bounds.Box.denseEvalNormBound primitive.numerator (spatialBox site)
  let numeratorDerivative := Derivative.Taylor.slopeCeiling primitive.numerator (spatialBox site)
  let numeratorTaylor := Derivative.Taylor.remainderCeiling primitive.numerator (spatialBox site)
  let numeratorSlope := chart * numeratorDerivative
  let numeratorFactor := 2 * (numeratorDerivative * chart + numeratorTaylor * chartSensitivity ^ 2)
  let cofactorDerivative := Derivative.Taylor.slopeCeiling (unitPolynomial site) (spatialBox site)
  let cofactorTaylor := Derivative.Taylor.remainderCeiling (unitPolynomial site) (spatialBox site)
  let cofactorSlope := chart * cofactorDerivative
  let cofactorFactor := 2 * (cofactorDerivative * chart + cofactorTaylor * chartSensitivity ^ 2)
  let cofactorInverseSlope := cofactorSlope * (1 / 16)⁻¹ ^ 3
  let cofactorInverseFactor := Radicand.inverseCeiling cofactorFactor cofactorSlope (1 / 16) 1 1 1
  let ordinateInverseSlope := chart * floor⁻¹ ^ 2
  let ordinateInverseFactor := 2 * (floor⁻¹ ^ 2 * chart + floor⁻¹ ^ 3 * chartSensitivity ^ 2)
  let cofactorPowerDerivative := Derivative.Taylor.slopeCeiling powerPolynomial cofactorBox
  let cofactorPowerTaylor := Derivative.Taylor.remainderCeiling powerPolynomial cofactorBox
  let cofactorPowerSlope := cofactorInverseSlope * cofactorPowerDerivative
  let cofactorPowerFactor := 2 * (cofactorPowerDerivative * cofactorInverseFactor +
    cofactorPowerTaylor * (2 * (cofactorInverseSlope + cofactorInverseFactor)) ^ 2)
  let ordinatePowerDerivative := Derivative.Taylor.slopeCeiling powerPolynomial ordinateBox
  let ordinatePowerTaylor := Derivative.Taylor.remainderCeiling powerPolynomial ordinateBox
  let ordinatePowerSlope := ordinateInverseSlope * ordinatePowerDerivative
  let ordinatePowerFactor := 2 * (ordinatePowerDerivative * ordinateInverseFactor +
    ordinatePowerTaylor * (2 * (ordinateInverseSlope + ordinateInverseFactor)) ^ 2)
  let ordinatePowerValue := floor⁻¹ ^ primitive.denominatorExponent
  let cofactorPowerValue : Fraction.Rational := (1 / 16)⁻¹ ^ primitive.denominatorExponent
  let numeratorOrdinateValue := numeratorValue * ordinatePowerValue
  let numeratorOrdinateSlope := 2 * (numeratorSlope * ordinatePowerValue + numeratorValue * ordinatePowerSlope)
  let numeratorOrdinateFactor := 4 * (ordinatePowerValue * numeratorFactor + numeratorValue * ordinatePowerFactor +
    (2 * (numeratorSlope + numeratorFactor)) * (2 * (ordinatePowerSlope + ordinatePowerFactor)))
  have baseSlopeBound : Norm.Basic.normSq base.slope ≤ chart := by
    rewrite [Tangent.baseExpansion_slope]
    exact Tangent.baseVelocity_normSq_le site parameter 2 quarter positive actual.data.lower actual.data.upper time
  have baseFactorBound : base.factor ≤ chart := by
    rewrite [Tangent.baseExpansion_factor]
    exact Fraction.Order.Basic.le_refl _
  have ordinateSlopeBound : Norm.Basic.normSq ordinate.slope ≤ chart := by
    rewrite [Tangent.ordinateExpansion_slope]
    exact Tangent.ordinateVelocity_normSq_le site parameter 2 quarter positive actual.data.lower actual.data.upper time
  have ordinateFactorBound : ordinate.factor ≤ chart := by
    rewrite [Tangent.ordinateExpansion_factor]
    exact Fraction.Order.Basic.le_refl _
  have numeratorOuterSlope : Norm.Basic.normSq numeratorOuter.slope ≤ numeratorDerivative :=
    Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound
      (Gaussian.GCD.derivative primitive.numerator) sourcePointInside
  have numeratorSlopeBound : Norm.Basic.normSq numerator.slope ≤ numeratorSlope :=
    base.compose_slope_le numeratorOuter canonicalUnit baseSlopeBound numeratorOuterSlope
  have numeratorFactorBound : numerator.factor ≤ numeratorFactor :=
    base.compose_factor_le numeratorOuter canonicalUnit baseSlopeBound baseFactorBound numeratorOuterSlope
      (Fraction.Order.Basic.le_refl numeratorOuter.factor)
  have numeratorBase : Norm.Basic.normSq numerator.base ≤ numeratorValue :=
    Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound primitive.numerator sourcePointInside
  have cofactorOuterSlope : Norm.Basic.normSq cofactorOuter.slope ≤ cofactorDerivative :=
    Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound
      (Gaussian.GCD.derivative (unitPolynomial site)) sourcePointInside
  have cofactorSlopeBound : Norm.Basic.normSq cofactor.slope ≤ cofactorSlope :=
    base.compose_slope_le cofactorOuter canonicalUnit baseSlopeBound cofactorOuterSlope
  have cofactorFactorBound : cofactor.factor ≤ cofactorFactor :=
    base.compose_factor_le cofactorOuter canonicalUnit baseSlopeBound baseFactorBound cofactorOuterSlope
      (Fraction.Order.Basic.le_refl cofactorOuter.factor)
  have cofactorInverseFactorBound : cofactorInverse.factor ≤ cofactorInverseFactor :=
    Radicand.inverseFactor_le_ceiling cofactor
      (firstFactor := 1) (lastFactor := 1) (slopeUpper := Norm.Basic.normSq cofactor.slope)
      (factorCeiling := cofactorFactor) (slopeCeiling := cofactorSlope) (floor := 1 / 16) (sumFloor := 1)
      (by decide +kernel) (by decide +kernel)
      (Norm.Basic.normSq_nonneg cofactor.slope) (by decide +kernel) (by decide +kernel)
      cofactorFactorBound cofactorSlopeBound
  have cofactorInverseSlopeBound : Norm.Basic.normSq cofactorInverse.slope ≤ cofactorInverseSlope := by
    change Norm.Basic.normSq
      ((Quadratic.SquareRoot.half * cofactor.slope * sourceSample.reading⁻¹) *
        (-(sourceSample.reading⁻¹ * sourceSample.reading⁻¹))) ≤ _
    have identity : (Quadratic.SquareRoot.half * cofactor.slope * sourceSample.reading⁻¹) *
        (-(sourceSample.reading⁻¹ * sourceSample.reading⁻¹)) =
      -(Quadratic.SquareRoot.half * cofactor.slope * sourceSample.reading⁻¹ ^ 3) := by ring1
    rewrite [identity, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    have coefficient := Arithmetic.mul_le_mul_direct
      (show Norm.Basic.normSq Quadratic.SquareRoot.half ≤ 1 from by decide +kernel) cofactorSlopeBound
      (Norm.Basic.normSq_nonneg _) (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
    rewrite [Fraction.Field.one_mul] at coefficient
    exact Arithmetic.mul_le_mul_direct coefficient
      (Norm.Reciprocal.power_normSq_le (by decide +kernel) sourceLower 3) (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg cofactor.slope).trans cofactorSlopeBound)
  have ordinateReciprocalSlope : Norm.Basic.normSq ordinateReciprocal.slope ≤ floor⁻¹ ^ 2 := by
    change Norm.Basic.normSq (-(ordinate.base⁻¹ * ordinate.base⁻¹)) ≤ _
    have identity : -(ordinate.base⁻¹ * ordinate.base⁻¹) = -(ordinate.base⁻¹ ^ 2) := by rewrite [pow_two]; rfl
    rewrite [identity, Norm.Basic.normSq_neg]
    exact Norm.Reciprocal.power_normSq_le floorPositive ordinateSourceLower 2
  have ordinateInverseSlopeBound : Norm.Basic.normSq ordinateInverse.slope ≤ ordinateInverseSlope :=
    ordinate.compose_slope_le ordinateReciprocal canonicalUnit ordinateSlopeBound ordinateReciprocalSlope
  have ordinateInverseFactorBound : ordinateInverse.factor ≤ ordinateInverseFactor :=
    ordinate.compose_factor_le ordinateReciprocal canonicalUnit ordinateSlopeBound ordinateFactorBound
      ordinateReciprocalSlope (Fraction.Order.Basic.le_refl ordinateReciprocal.factor)
  have sourceInverseInside : cofactorBox.Contains cofactorInverse.base := by
    apply Box.Square.Centered.normBox_contains (by decide +kernel : (0 : Fraction.Rational) ≤ 16)
    have bounded := Norm.Reciprocal.normSq_le (by decide +kernel) sourceLower
    rewrite [show ((1 / 16 : Fraction.Rational)⁻¹) = 16 by decide +kernel] at bounded
    exact bounded
  have targetInverseInside : cofactorBox.Contains cofactorInverse.output := by
    apply Box.Square.Centered.normBox_contains (by decide +kernel : (0 : Fraction.Rational) ≤ 16)
    have bounded := Norm.Reciprocal.normSq_le (by decide +kernel) targetLower
    rewrite [show ((1 / 16 : Fraction.Rational)⁻¹) = 16 by decide +kernel] at bounded
    exact bounded
  have sourceOrdinateInverseInside : ordinateBox.Contains ordinateInverse.base :=
    Box.Square.Centered.normBox_contains (Fraction.Order.Field.inv_pos_direct floorPositive).le
      (Norm.Reciprocal.normSq_le floorPositive ordinateSourceLower)
  have targetOrdinateInverseInside : ordinateBox.Contains ordinateInverse.output :=
    Box.Square.Centered.normBox_contains (Fraction.Order.Field.inv_pos_direct floorPositive).le
      (Norm.Reciprocal.normSq_le floorPositive ordinateTargetLower)
  have cofactorPowerOuterSlope : Norm.Basic.normSq cofactorPowerOuter.slope ≤ cofactorPowerDerivative :=
    Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound
      (Gaussian.GCD.derivative powerPolynomial) sourceInverseInside
  have cofactorPowerOuterFactor : cofactorPowerOuter.factor ≤ cofactorPowerTaylor :=
    Quadratic.Polynomial.certificate_factor_le_box powerPolynomial sourceInverseInside targetInverseInside
  have cofactorPowerSlopeBound : Norm.Basic.normSq cofactorPower.slope ≤ cofactorPowerSlope :=
    cofactorInverse.compose_slope_le cofactorPowerOuter canonicalUnit
      cofactorInverseSlopeBound cofactorPowerOuterSlope
  have cofactorPowerFactorBound : cofactorPower.factor ≤ cofactorPowerFactor :=
    cofactorInverse.compose_factor_le cofactorPowerOuter canonicalUnit
      cofactorInverseSlopeBound cofactorInverseFactorBound cofactorPowerOuterSlope cofactorPowerOuterFactor
  have cofactorPowerBase : Norm.Basic.normSq cofactorPower.base ≤ cofactorPowerValue := by
    change Norm.Basic.normSq (powerPolynomial.eval sourceSample.reading⁻¹) ≤ _
    rewrite [Derivative.Taylor.powerPolynomial_eval]
    exact Norm.Reciprocal.power_normSq_le (by decide +kernel) sourceLower primitive.denominatorExponent
  have ordinatePowerOuterSlope : Norm.Basic.normSq ordinatePowerOuter.slope ≤ ordinatePowerDerivative :=
    Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound
      (Gaussian.GCD.derivative powerPolynomial) sourceOrdinateInverseInside
  have ordinatePowerOuterFactor : ordinatePowerOuter.factor ≤ ordinatePowerTaylor :=
    Quadratic.Polynomial.certificate_factor_le_box powerPolynomial
      sourceOrdinateInverseInside targetOrdinateInverseInside
  have ordinatePowerSlopeBound : Norm.Basic.normSq ordinatePower.slope ≤ ordinatePowerSlope :=
    ordinateInverse.compose_slope_le ordinatePowerOuter canonicalUnit
      ordinateInverseSlopeBound ordinatePowerOuterSlope
  have ordinatePowerFactorBound : ordinatePower.factor ≤ ordinatePowerFactor :=
    ordinateInverse.compose_factor_le ordinatePowerOuter canonicalUnit
      ordinateInverseSlopeBound ordinateInverseFactorBound ordinatePowerOuterSlope ordinatePowerOuterFactor
  have ordinatePowerBase : Norm.Basic.normSq ordinatePower.base ≤ ordinatePowerValue := by
    change Norm.Basic.normSq (powerPolynomial.eval ordinate.base⁻¹) ≤ _
    rewrite [Derivative.Taylor.powerPolynomial_eval]
    exact Norm.Reciprocal.power_normSq_le floorPositive ordinateSourceLower primitive.denominatorExponent
  have numeratorOrdinateBase : Norm.Basic.normSq numeratorOrdinate.base ≤ numeratorOrdinateValue := by
    change Norm.Basic.normSq (numerator.base * ordinatePower.base) ≤ _
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct numeratorBase ordinatePowerBase (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg numerator.base).trans numeratorBase)
  have numeratorOrdinateSlopeBound : Norm.Basic.normSq numeratorOrdinate.slope ≤ numeratorOrdinateSlope :=
    Quadratic.Product.slope_le numerator ordinatePower unit numeratorBase ordinatePowerBase
      numeratorSlopeBound ordinatePowerSlopeBound
  have numeratorOrdinateFactorBound : numeratorOrdinate.factor ≤ numeratorOrdinateFactor :=
    Quadratic.Product.factor_le numerator ordinatePower unit numeratorBase ordinatePowerBase
      numeratorSlopeBound ordinatePowerSlopeBound numeratorFactorBound ordinatePowerFactorBound
  have productFactorBound : product.factor ≤
      4 * (cofactorPowerValue * numeratorOrdinateFactor + numeratorOrdinateValue * cofactorPowerFactor +
        (2 * (numeratorOrdinateSlope + numeratorOrdinateFactor)) *
          (2 * (cofactorPowerSlope + cofactorPowerFactor))) :=
    Quadratic.Product.factor_le numeratorOrdinate cofactorPower unit numeratorOrdinateBase cofactorPowerBase
      numeratorOrdinateSlopeBound cofactorPowerSlopeBound numeratorOrdinateFactorBound cofactorPowerFactorBound
  unfold build
  change Canonical.normSq primitive.scale * product.factor ≤ _
  rewrite [← Norm.Basic.normSq_eq_canonical]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct productFactorBound
    (Norm.Basic.normSq_nonneg primitive.scale)).trans_eq (by unfold ceiling; rfl)

/-- The actual prescribed primitive endpoints pay the fixed chart remainder ceiling at the same fourth-power request. -/
theorem build_remainder_le (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (accuracy_eq : accuracy.tolerance = delta ^ 4) :
    Norm.Basic.normSq
      (Primitive.reading (site := site) primitive quarter (time + delta) targetSample.reading -
        Primitive.reading (site := site) primitive quarter time sourceSample.reading -
          Stereographic.Tangent.increment delta *
            (build primitive source target regular accuracy sourceSample targetSample accuracy_eq).certificate.slope) ≤
      ceiling site parameter primitive regular * delta ^ 4 := by
  have fourthNonnegative : (0 : Fraction.Rational) ≤ delta ^ 4 :=
    (Arithmetic.sq_nonneg_direct (delta * delta)).trans_eq (by ring1)
  exact (Expansion.remainder_le
    (build primitive source target regular accuracy sourceSample targetSample accuracy_eq)).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (build_factor_le primitive source target regular accuracy sourceSample targetSample accuracy_eq)
      fourthNonnegative)

end

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor
