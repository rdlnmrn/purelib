module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Slope
public import Purelib.Calculus.Jet.Quadratic.Perturbation
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Primitive chart Taylor certificates on independent original arithmetic observations

Both original primitive endpoints and the independently constructed spatial
derivative times original base velocity keep their actual evaluator caches.
The same two retained cofactor observations pay their spread and square
residual requests. Three original arithmetic comparisons select independent
states and witnesses; the computed source residual pays the derivative's
difference from the actual chart chain-rule slope before perturbation.

The resulting finite remainder concerns those actual arithmetic witnesses.
It does not assert a geometric primitive edge integral or endpoint law.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Observation

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation

open Purelib
open Purelib.Data
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Calculus.Jet
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time delta : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside time} {lastInside : FixedRootBoxPath.Inside (time + delta)}

/-- One original endpoint's arithmetic observation keeps its original numerical and factored primitive caches. -/
abbrev PrimitiveReading {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
    {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
    {accuracy : AccuracyRequest} (endpoint : Endpoint primitive reading regular)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :=
  Factorization.Reading primitive
    (point site parameter 2 (Waist.direction quarter time) positive).base
    reading.lift.unitRoot.value reading.lift.unitRoot.apart sample.state sample.observation
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹
    endpoint.values.value endpoint.values.factored accuracy (1 / 16)

/-- The independent spatial derivative observation keeps the true base-velocity product and original factored cache. -/
abbrev DerivativeReading {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {source : Transport.Reading actual time firstInside} {regular : parameter ≠ criticalValue site}
    {accuracy : AccuracyRequest} (endpoint : Endpoint primitive source regular)
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (values : Primitive.Observation.DerivativeValues specification endpoint)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy) :=
  Factorization.Reading specification.differential
    (point site parameter 2 (Waist.direction quarter time) positive).base
    source.lift.unitRoot.value source.lift.unitRoot.apart sample.state sample.observation
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (Stereographic.Tangent.logarithmicVelocity time) values.pullback values.factored accuracy (1 / 16)

/-- One original endpoint's same-root arithmetic allowance is scaled by its exact uncancelled ordinate coefficient. -/
@[expose] def primitiveFactor (primitive : OddPowerDifferential (Paths.polynomial parameter))
    {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
    (reading : Transport.Reading actual time inside) : Fraction.Rational :=
  Factorization.allowanceFactor primitive
    (point site parameter 2 (Waist.direction quarter time) positive).base
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ reading.lift.unitRoot (1 / 16)

/-- The independent spatial derivative allowance retains its logarithmic velocity and actual cofactor owner. -/
@[expose] def derivativeFactor {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (source : Transport.Reading actual time firstInside) : Fraction.Rational :=
  Factorization.allowanceFactor specification.differential
    (point site parameter 2 (Waist.direction quarter time) positive).base
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (Stereographic.Tangent.logarithmicVelocity time) source.lift.unitRoot (1 / 16)

set_option genInjectivity false in
/-- A chart expansion retaining three independent original arithmetic comparisons and their computed finite remainder.

Both complete original endpoint caches and the independent derivative cache
remain indices. The scalar chart builder is retained once, and the actual
observations store their independent states, witnesses and payments. Their
internally derived discrepancy bounds feed the existing perturbation factory.
-/
structure Expansion (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (sourceEndpoint : Endpoint primitive source regular) (targetEndpoint : Endpoint primitive target regular)
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (sourceValues : Primitive.Observation.DerivativeValues specification sourceEndpoint) where
  /-- The actual prescribed primitive chart certificate constructed on these identical cofactor observations. -/
  scalar : Taylor.Expansion primitive source target accuracy sourceSample targetSample
  /-- The scalar cache is exactly the original chart builder with its same retained residual payment. -/
  scalar_eq : scalar =
    Taylor.build primitive source target regular accuracy sourceSample targetSample scalar.accuracy_eq
  /-- The actual independently chosen arithmetic source primitive observation. -/
  sourceValue : PrimitiveReading sourceEndpoint sourceSample
  /-- The actual independently chosen arithmetic target primitive observation. -/
  targetValue : PrimitiveReading targetEndpoint targetSample
  /-- The actual independently chosen spatial derivative times original base velocity observation. -/
  derivative : DerivativeReading sourceEndpoint specification sourceValues sourceSample
  /-- The derivative observation pays both its own arithmetic error and original source square residual. -/
  derivative_le : Norm.Basic.normSq (derivative.reading - scalar.certificate.slope) ≤
    2 * (derivativeFactor specification source + slopeResidualFactor site parameter primitive) * delta ^ 4
  /-- The quadratic certificate on the three actual original arithmetic witnesses. -/
  certificate : Quadratic.Basic.Certificate (Stereographic.Tangent.increment delta)
  /-- The actual source arithmetic witness is retained as the certificate base. -/
  base_eq : certificate.base = sourceValue.reading
  /-- The distinct actual target arithmetic witness is retained as the certificate output. -/
  output_eq : certificate.output = targetValue.reading
  /-- The independently observed derivative product witness is retained as the certificate slope. -/
  slope_eq : certificate.slope = derivative.reading
  /-- The actual original scalar and three paid observation factors determine the exact constructed remainder factor. -/
  factor_eq : certificate.factor = 4 * (scalar.certificate.factor + primitiveFactor primitive source +
    primitiveFactor primitive target + 2 * (derivativeFactor specification source +
      slopeResidualFactor site parameter primitive))

constructive_injectivity Expansion

/-- A factored evaluator observation pays its same-root allowance at the original fourth-power chart request. -/
private theorem reading_le {radicand : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {rootParameter : Canonical} (differential : OddPowerDifferential radicand) (point factor velocity : Canonical)
    (root : CertifiedSquareRoot.Certificate rootParameter) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy)
    {original factored : CoherentNamed}
    (retained : Factorization.Reading differential point root.value root.apart
      sample.state sample.observation factor velocity original factored accuracy (1 / 16))
    (accuracy_eq : accuracy.tolerance = delta ^ 4) :
    Norm.Basic.normSq (retained.reading -
      Factorization.scalarReading differential point factor velocity sample.observation) ≤
      Factorization.allowanceFactor differential point factor velocity root (1 / 16) *
        Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
  rewrite [Stereographic.Tangent.increment_fourth]
  exact retained.reading_close.le.trans
    ((Factorization.errorBound_le_factor differential point factor velocity root sample
      retained.positive).trans_eq (congrArg
        (fun tolerance : Fraction.Rational =>
          Factorization.allowanceFactor differential point factor velocity root (1 / 16) *
            tolerance)
        accuracy_eq))

/-- Assemble retained original arithmetic observations into their paid primitive chart expansion.

The exact scalar factory cache and the three independently selected original
Reading caches are consumed unchanged. Their existing comparison payments
and the actual source square residual derive all perturbation bounds; no
arithmetic observation is requested and no derivative equality is assumed.
-/
def ofReadings (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (sourceEndpoint : Endpoint primitive source regular) (targetEndpoint : Endpoint primitive target regular)
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (sourceValues : Primitive.Observation.DerivativeValues specification sourceEndpoint)
    (scalar : Taylor.Expansion primitive source target accuracy sourceSample targetSample)
    (scalar_eq : scalar = Taylor.build primitive source target regular accuracy sourceSample targetSample
      scalar.accuracy_eq)
    (sourceValue : PrimitiveReading sourceEndpoint sourceSample)
    (targetValue : PrimitiveReading targetEndpoint targetSample)
    (derivative : DerivativeReading sourceEndpoint specification sourceValues sourceSample) :
    Expansion primitive source target regular accuracy sourceSample targetSample
      sourceEndpoint targetEndpoint specification sourceValues := by
  let baseFactor := primitiveFactor primitive source
  let outputFactor := primitiveFactor primitive target
  let slopeFactor := 2 * (derivativeFactor specification source + slopeResidualFactor site parameter primitive)
  have unit := Stereographic.Tangent.increment_unit firstInside lastInside
  have baseBound : Norm.Basic.normSq (sourceValue.reading - scalar.certificate.base) ≤
      baseFactor * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    rewrite [scalar.base_eq]
    have paid := reading_le primitive
      (point site parameter 2 (Waist.direction quarter time) positive).base
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ source.lift.unitRoot
      sourceSample sourceValue scalar.accuracy_eq
    rewrite [Primitive.Observation.primitive_scalar_eq] at paid
    exact paid
  have outputBound : Norm.Basic.normSq (targetValue.reading - scalar.certificate.output) ≤
      outputFactor * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    rewrite [scalar.output_eq]
    have paid := reading_le primitive
      (point site parameter 2 (Waist.direction quarter (time + delta)) positive).base
      (point site parameter 2 (Waist.direction quarter (time + delta)) positive).ordinate
      (point site parameter 2 (Waist.direction quarter (time + delta)) positive).ordinate⁻¹ target.lift.unitRoot
      targetSample targetValue scalar.accuracy_eq
    rewrite [Primitive.Observation.primitive_scalar_eq] at paid
    exact paid
  have derivativeBound := reading_le specification.differential
    (point site parameter 2 (Waist.direction quarter time) positive).base
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (Stereographic.Tangent.logarithmicVelocity time) source.lift.unitRoot sourceSample derivative scalar.accuracy_eq
  rewrite [Primitive.Observation.derivative_scalar_eq] at derivativeBound
  have residualBound := scalar_slope_le primitive source target regular accuracy sourceSample targetSample
    scalar.accuracy_eq specification
  rewrite [← scalar_eq, ← Stereographic.Tangent.increment_fourth] at residualBound
  have slopeBound : Norm.Basic.normSq (derivative.reading - scalar.certificate.slope) ≤
      slopeFactor * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    calc
      _ ≤ 2 * (Norm.Basic.normSq (derivative.reading -
          Differential.reading site parameter quarter time specification.differential sourceSample.reading) +
        Norm.Basic.normSq
          (Differential.reading site parameter quarter time specification.differential sourceSample.reading -
            scalar.certificate.slope)) := Norm.Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 * (derivativeFactor specification source *
          Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 +
        slopeResidualFactor site parameter primitive * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct derivativeBound residualBound) (by decide +kernel)
      _ = _ := by dsimp only [slopeFactor]; ring1
  have baseNonnegative := Factorization.allowanceFactor_nonnegative primitive
    (point site parameter 2 (Waist.direction quarter time) positive).base
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ source.lift.unitRoot
    (floor := 1 / 16) (by decide +kernel)
  have outputNonnegative := Factorization.allowanceFactor_nonnegative primitive
    (point site parameter 2 (Waist.direction quarter (time + delta)) positive).base
    (point site parameter 2 (Waist.direction quarter (time + delta)) positive).ordinate
    (point site parameter 2 (Waist.direction quarter (time + delta)) positive).ordinate⁻¹
    target.lift.unitRoot (floor := 1 / 16) (by decide +kernel)
  have derivativeNonnegative := Factorization.allowanceFactor_nonnegative
    specification.differential
    (point site parameter 2 (Waist.direction quarter time) positive).base
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (Stereographic.Tangent.logarithmicVelocity time) source.lift.unitRoot (floor := 1 / 16) (by decide +kernel)
  have slopeNonnegative : 0 ≤ slopeFactor := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.add_le_add_direct derivativeNonnegative
      (slopeResidualFactor_nonnegative site parameter primitive regular))
  let certificate := scalar.certificate.perturb sourceValue.reading targetValue.reading derivative.reading
    baseFactor outputFactor slopeFactor baseNonnegative outputNonnegative slopeNonnegative unit
    baseBound outputBound slopeBound
  exact
    { scalar := scalar
      scalar_eq := scalar_eq
      sourceValue := sourceValue
      targetValue := targetValue
      derivative := derivative
      derivative_le := by rewrite [← Stereographic.Tangent.increment_fourth]; exact slopeBound
      certificate := certificate
      base_eq := rfl
      output_eq := rfl
      slope_eq := rfl
      factor_eq := rfl }

section RetainedReadings

variable (primitive : OddPowerDifferential (Paths.polynomial parameter))
variable (source : Transport.Reading actual time firstInside)
variable (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
variable (accuracy : AccuracyRequest)
variable (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
variable (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
variable (sourceEndpoint : Endpoint primitive source regular) (targetEndpoint : Endpoint primitive target regular)
variable (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
variable (sourceValues : Primitive.Observation.DerivativeValues specification sourceEndpoint)
variable (scalar : Taylor.Expansion primitive source target accuracy sourceSample targetSample)
variable (scalar_eq : scalar = Taylor.build primitive source target regular accuracy sourceSample targetSample
  scalar.accuracy_eq)
variable (sourceValue : PrimitiveReading sourceEndpoint sourceSample)
variable (targetValue : PrimitiveReading targetEndpoint targetSample)
variable (derivative : DerivativeReading sourceEndpoint specification sourceValues sourceSample)

/-- Retained-reading assembly preserves the complete original scalar chart factory cache. -/
theorem ofReadings_scalar :
    (ofReadings primitive source target regular accuracy sourceSample targetSample
      sourceEndpoint targetEndpoint specification sourceValues scalar scalar_eq
      sourceValue targetValue derivative).scalar = scalar := by
  rfl

/-- Retained-reading assembly preserves the whole source Reading and both selected process indices. -/
theorem ofReadings_sourceValue :
    (ofReadings primitive source target regular accuracy sourceSample targetSample
      sourceEndpoint targetEndpoint specification sourceValues scalar scalar_eq
      sourceValue targetValue derivative).sourceValue = sourceValue := by
  rfl

/-- Retained-reading assembly preserves the whole target Reading and both original observations. -/
theorem ofReadings_targetValue :
    (ofReadings primitive source target regular accuracy sourceSample targetSample
      sourceEndpoint targetEndpoint specification sourceValues scalar scalar_eq
      sourceValue targetValue derivative).targetValue = targetValue := by
  rfl

/-- Retained-reading assembly preserves the complete independently selected spatial-derivative Reading. -/
theorem ofReadings_derivative :
    (ofReadings primitive source target regular accuracy sourceSample targetSample
      sourceEndpoint targetEndpoint specification sourceValues scalar scalar_eq
      sourceValue targetValue derivative).derivative = derivative := by
  rfl

end RetainedReadings

/-- Request three actual original arithmetic observations and assemble their primitive chart expansion.

The scalar and each original arithmetic request are constructed once. The
retained-reading constructor then derives all payments on those exact caches.
-/
def build (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (source : Transport.Reading actual time firstInside)
    (target : Transport.Reading actual (time + delta) lastInside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy)
    (targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy)
    (accuracy_eq : accuracy.tolerance = delta ^ 4)
    (sourceEndpoint : Endpoint primitive source regular) (targetEndpoint : Endpoint primitive target regular)
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (sourceValues : Primitive.Observation.DerivativeValues specification sourceEndpoint) :
    Expansion primitive source target regular accuracy sourceSample targetSample
      sourceEndpoint targetEndpoint specification sourceValues := by
  let scalar := Taylor.build primitive source target regular accuracy sourceSample targetSample accuracy_eq
  let sourceValue := Primitive.Observation.primitiveRequest
    primitive source regular sourceEndpoint sourceSample accuracy
  let targetValue := Primitive.Observation.primitiveRequest
    primitive target regular targetEndpoint targetSample accuracy
  let derivative := Primitive.Observation.derivativeRequest
    specification sourceEndpoint sourceValues sourceSample accuracy
  exact ofReadings primitive source target regular accuracy sourceSample targetSample
    sourceEndpoint targetEndpoint specification sourceValues scalar rfl sourceValue targetValue derivative

namespace Expansion

/-- The three retained independent arithmetic witnesses pay their internally constructed finite chart remainder. -/
theorem remainder_le {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {source : Transport.Reading actual time firstInside}
    {target : Transport.Reading actual (time + delta) lastInside} {regular : parameter ≠ criticalValue site}
    {accuracy : AccuracyRequest}
    {sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy}
    {targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy}
    {sourceEndpoint : Endpoint primitive source regular} {targetEndpoint : Endpoint primitive target regular}
    {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive}
    {sourceValues : Primitive.Observation.DerivativeValues specification sourceEndpoint}
    (expansion : Expansion primitive source target regular accuracy sourceSample targetSample
      sourceEndpoint targetEndpoint specification sourceValues) :
    Norm.Basic.normSq (expansion.targetValue.reading - expansion.sourceValue.reading -
      Stereographic.Tangent.increment delta * expansion.derivative.reading) ≤
      expansion.certificate.factor * delta ^ 4 := by
  rewrite [← expansion.base_eq, ← expansion.output_eq, ← expansion.slope_eq, expansion.certificate.expansion]
  have paid : Norm.Basic.normSq expansion.certificate.remainder ≤
      expansion.certificate.factor * Norm.Basic.normSq (Stereographic.Tangent.increment delta) ^ 2 := by
    simpa only [Norm.Basic.normSq_eq_canonical] using expansion.certificate.remainder_le
  exact paid.trans_eq (congrArg (fun fourth : Fraction.Rational => expansion.certificate.factor * fourth)
    (Stereographic.Tangent.increment_fourth delta))

end Expansion

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Observation

end
