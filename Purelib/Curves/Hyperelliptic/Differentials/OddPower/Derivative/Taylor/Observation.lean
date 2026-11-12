module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Taylor
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Residual
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache
public import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate.Derivative
public import Purelib.Calculus.Jet.Quadratic.Perturbation
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Paid original primitive and independent derivative observations

The original spatial Taylor expansion retains both actual sheet readings.
The source square residual pays its scalar slope's discrepancy from the
independently constructed cleared derivative. Actual primitive endpoint and
derivative arithmetic observations keep their evaluator caches, independent
states and witnesses. The existing quadratic perturbation construction pays
these three independent readings before any primitive edge integral claim.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Taylor.Observation

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Algebra.Quadratic (Pair)
open Purelib.Riemann.RootContinuation

variable {radicand : Pair.Polynomial.Coefficients}

/-- The retained scalar primitive slope is exactly the original two Leibniz specification readings. -/
theorem slope_eq_leibniz {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
    {box inverseBox window : Box} {side : Box.OutsideSide window 0} {first last : Canonical}
    {source : CertifiedSquareRoot.Certificate (polynomial.eval first)}
    {target : CertifiedSquareRoot.Certificate (polynomial.eval last)} {accuracy : AccuracyRequest}
    {sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy}
    {targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target accuracy}
    (expansion : Taylor.Expansion polynomial primitive box inverseBox window side first last source target accuracy
      sourceSample targetSample) (specification : Specification polynomial primitive) :
    expansion.certificate.slope = Residual.leibnizReading specification first sourceSample.reading := by
  rewrite [expansion.slope_eq]
  unfold Residual.leibnizReading
  rewrite [specification.first_eq, specification.last_eq, specification.numeratorDerivative_eq,
    specification.polynomialDerivative_eq]
  change primitive.scale *
      ((GCD.derivative primitive.numerator).eval first * sourceSample.reading⁻¹ ^ primitive.denominatorExponent +
        primitive.numerator.eval first *
          (-(Quadratic.SquareRoot.half * (GCD.derivative polynomial).eval first * sourceSample.reading⁻¹ ^ 3) *
            (GCD.derivative (powerPolynomial primitive)).eval sourceSample.reading⁻¹)) =
    (primitive.scale * (GCD.derivative primitive.numerator).eval first) *
        sourceSample.reading⁻¹ ^ primitive.denominatorExponent -
      (primitive.scale * exponentCoefficient primitive / 2) *
        (primitive.numerator * GCD.derivative polynomial).eval first *
          sourceSample.reading⁻¹ ^ (primitive.denominatorExponent + 2)
  unfold powerPolynomial
  rewrite [Power.Coordinate.derivative_eval, exponentCoefficient_eq_intCast,
    Purelib.Polynomial.Dense.Basic.DensePolynomial.eval_mul, Algebra.Field.ExplicitField.div_eq_mul_inv]
  rewrite [show 2 * primitive.denominatorPairs + 1 = primitive.denominatorExponent from rfl]
  have half : (2 : Canonical)⁻¹ = Quadratic.SquareRoot.half := by decide +kernel
  rewrite [half]
  have exponent : 3 + 2 * primitive.denominatorPairs = primitive.denominatorExponent + 2 := by
    unfold OddPowerDifferential.denominatorExponent
    omega0
  have powers : sourceSample.reading⁻¹ ^ 3 * sourceSample.reading⁻¹ ^ (2 * primitive.denominatorPairs) =
      sourceSample.reading⁻¹ ^ (primitive.denominatorExponent + 2) := by
    rewrite [← pow_add, exponent]
    rfl
  calc
    _ = (primitive.scale * (GCD.derivative primitive.numerator).eval first) *
        sourceSample.reading⁻¹ ^ primitive.denominatorExponent -
      (primitive.scale * (Int.ofNat primitive.denominatorExponent : Canonical) * Quadratic.SquareRoot.half) *
        (primitive.numerator.eval first * (GCD.derivative polynomial).eval first) *
          (sourceSample.reading⁻¹ ^ 3 * sourceSample.reading⁻¹ ^ (2 * primitive.denominatorPairs)) := by ring1
    _ = _ := by rewrite [powers]; rfl

/-- The independent derivative's scalar anchor differs from the Taylor slope by the paid original square residual. -/
theorem scalar_slope_le {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
    {box inverseBox window : Box} {side : Box.OutsideSide window 0} {first last : Canonical}
    {source : CertifiedSquareRoot.Certificate (polynomial.eval first)}
    {target : CertifiedSquareRoot.Certificate (polynomial.eval last)} {accuracy : AccuracyRequest}
    {sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy}
    {targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target accuracy}
    (expansion : Taylor.Expansion polynomial primitive box inverseBox window side first last source target accuracy
      sourceSample targetSample) (specification : Specification polynomial primitive)
    (firstInside : box.Contains first) {floor : Fraction.Rational} (positive : 0 < floor)
    (lower : floor ≤ Norm.Basic.normSq sourceSample.reading) :
    Norm.Basic.normSq (OddPower.Observation.scalarReading specification.differential first sourceSample.observation -
      expansion.certificate.slope) ≤ Residual.factor primitive box floor * Norm.Basic.normSq (last - first) ^ 2 := by
  rewrite [slope_eq_leibniz expansion specification]
  exact Residual.difference_normSq_le specification first sourceSample.observation sourceSample.reading_nonzero
    firstInside positive lower (sourceSample.reading_residual_lt.le.trans_eq expansion.accuracy_eq)

variable {polynomial : CoefficientPolynomial} {primitive : OddPowerDifferential polynomial}
  {box inverseBox window : Box} {side : Box.OutsideSide window 0} {first last : Canonical}
  {source : CertifiedSquareRoot.Certificate (polynomial.eval first)}
  {target : CertifiedSquareRoot.Certificate (polynomial.eval last)} {accuracy : AccuracyRequest}
  {sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source accuracy}
  {targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target accuracy}

/-- The exact type of one actual original primitive source arithmetic observation with its supplied retained cache. -/
abbrev SourceReading (coefficient : CoherentNamed) (floor : Fraction.Rational) :=
  Cache.Reading primitive first source.value source.apart sourceSample.state
    sourceSample.observation accuracy coefficient floor

/-- The exact type of the independently selected target primitive arithmetic observation. -/
abbrev TargetReading (coefficient : CoherentNamed) (floor : Fraction.Rational) :=
  Cache.Reading primitive last target.value target.apart targetSample.state
    targetSample.observation accuracy coefficient floor

/-- The exact independent cleared derivative arithmetic observation type preserves the same original source sheet. -/
abbrev DerivativeReading (specification : Specification polynomial primitive) (coefficient : CoherentNamed)
    (floor : Fraction.Rational) :=
  Cache.Reading specification.differential first source.value source.apart sourceSample.state
    sourceSample.observation accuracy coefficient floor

set_option genInjectivity false in
/-- Three actual original arithmetic readings and a spatial Taylor certificate on those independent witnesses.

The original scalar expansion, derivative specification, source evaluator
caches and target primitive cache remain indices. Each arithmetic observation
retains its original nominal process and comparison; the constructed quadratic
certificate uses their actual selected witnesses without replacing them.
-/
structure Expansion
    (scalar : Taylor.Expansion polynomial primitive box inverseBox window side first last source target accuracy
      sourceSample targetSample)
    (specification : Specification polynomial primitive)
    (sourceValues : specification.Values first source.value source.apart)
    (targetValue : CoherentNamed) (sourceFloor targetFloor : Fraction.Rational) where
  /-- The original source primitive arithmetic observation uses the identical retained evaluator cache. -/
  sourceValue : SourceReading (polynomial := polynomial) (primitive := primitive) (first := first)
    (source := source) (accuracy := accuracy) (sourceSample := sourceSample) sourceValues.primitiveValue sourceFloor
  /-- The actual target primitive observation keeps its distinct retained evaluator cache. -/
  targetReading : TargetReading (polynomial := polynomial) (primitive := primitive) (last := last)
    (target := target) (accuracy := accuracy) (targetSample := targetSample) targetValue targetFloor
  /-- The derivative slope comes from its actual original independent cleared evaluator cache. -/
  derivative : DerivativeReading (first := first) (source := source) (accuracy := accuracy)
    (sourceSample := sourceSample) specification sourceValues.derivative sourceFloor
  /-- The actual arithmetic derivative witness pays both its original spread and source square residual. -/
  derivative_le : Norm.Basic.normSq (derivative.reading - scalar.certificate.slope) ≤
    2 * (Cache.allowanceFactor specification.differential first source sourceFloor +
      Residual.factor primitive box sourceFloor) * Norm.Basic.normSq (last - first) ^ 2
  /-- The actual three-reading quadratic certificate retains these exact independently selected witnesses. -/
  certificate : Quadratic.Basic.Certificate (last - first)
  /-- The original source arithmetic witness is the certificate base. -/
  base_eq : certificate.base = sourceValue.reading
  /-- The independently selected target primitive arithmetic witness is the certificate output. -/
  output_eq : certificate.output = targetReading.reading
  /-- The independently selected cleared derivative arithmetic witness is the certificate slope. -/
  slope_eq : certificate.slope = derivative.reading
  /-- The original scalar and three observation allowances pay the exact constructed factor. -/
  factor_eq : certificate.factor = 4 * (scalar.certificate.factor +
    Cache.allowanceFactor primitive first source sourceFloor + Cache.allowanceFactor primitive last target targetFloor +
      2 * (Cache.allowanceFactor specification.differential first source sourceFloor +
        Residual.factor primitive box sourceFloor))

constructive_injectivity Expansion

/-- The original source arithmetic witness pays its computed allowance against the unchanged selected sheet reading. -/
private theorem reading_le {parameter point : Canonical} {root : CertifiedSquareRoot.Certificate parameter}
    {sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy}
    (differential : OddPowerDifferential radicand) {coefficient : CoherentNamed} {floor : Fraction.Rational}
    (retained : Cache.Reading differential point root.value root.apart sample.state
      sample.observation accuracy coefficient floor)
    (accuracy_eq : accuracy.tolerance = Norm.Basic.normSq (last - first) ^ 2) :
    Norm.Basic.normSq (retained.reading - OddPower.Observation.scalarReading differential point sample.observation) ≤
      Cache.allowanceFactor differential point root floor * Norm.Basic.normSq (last - first) ^ 2 :=
  retained.reading_close.le.trans
    ((Cache.errorBound_le_factor differential point root sample retained.positive).trans_eq
    (congrArg (fun tolerance : Fraction.Rational => Cache.allowanceFactor differential point root floor * tolerance)
      accuracy_eq))

/-- The original fixed-box residual factor is nonnegative under its actual positive observation floor. -/
private theorem residual_factor_nonnegative (primitive : OddPowerDifferential radicand) (box : Box)
    {floor : Fraction.Rational} (positive : 0 < floor) : 0 ≤ Residual.factor primitive box floor :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg primitive.scale)
      (Bounds.Box.denseHornerNormBounds_nonneg (GCD.derivative primitive.numerator) box).1)
    (Arithmetic.pow_nonneg_direct (Fraction.Order.Field.inv_pos_direct positive).le _)

/-- Construct the three original arithmetic observations and pay their actual finite primitive expansion.

The source primitive and derivative use the supplied original evaluator
caches; the target uses its distinct retained cache. Actual root-candidate
floors pay the unchanged arithmetic processes. The independently observed
derivative pays both its arithmetic spread and the original source square
residual before the existing perturbation constructor combines the readings.
-/
def build
    (scalar : Taylor.Expansion polynomial primitive box inverseBox window side first last source target accuracy
      sourceSample targetSample)
    (specification : Specification polynomial primitive)
    (sourceValues : specification.Values first source.value source.apart)
    (targetValue : CoherentNamed)
    (targetValue_eq : targetValue = primitive.value last target.value target.apart)
    (firstInside : box.Contains first) (sourceFloor targetFloor : Fraction.Rational)
    (sourcePositive : 0 < sourceFloor) (targetPositive : 0 < targetFloor)
    (sourceLower : ∀ {candidate : Canonical}, sourceSample.observation.Possible candidate →
      sourceFloor ≤ Norm.Basic.normSq candidate)
    (targetLower : ∀ {candidate : Canonical}, targetSample.observation.Possible candidate →
      targetFloor ≤ Norm.Basic.normSq candidate)
    (unit : Norm.Basic.normSq (last - first) ≤ 1) :
    Expansion scalar specification sourceValues targetValue sourceFloor targetFloor := by
  let sourceValue := Cache.request primitive first source.value source.apart sourceSample.state
    sourceSample.observation sourceSample.observation_eq accuracy sourceValues.primitiveValue
    sourceValues.primitiveValue_eq sourceFloor sourcePositive sourceLower
  let targetReading := Cache.request primitive last target.value target.apart targetSample.state
    targetSample.observation targetSample.observation_eq accuracy targetValue targetValue_eq
    targetFloor targetPositive targetLower
  let derivative := Cache.request specification.differential first source.value source.apart
    sourceSample.state sourceSample.observation sourceSample.observation_eq accuracy sourceValues.derivative
    sourceValues.derivative_eq sourceFloor sourcePositive sourceLower
  let baseFactor := Cache.allowanceFactor primitive first source sourceFloor
  let outputFactor := Cache.allowanceFactor primitive last target targetFloor
  let slopeFactor := 2 * (Cache.allowanceFactor specification.differential first source sourceFloor +
    Residual.factor primitive box sourceFloor)
  have baseBound : Norm.Basic.normSq (sourceValue.reading - scalar.certificate.base) ≤
      baseFactor * Norm.Basic.normSq (last - first) ^ 2 := by
    rewrite [scalar.base_eq]
    exact reading_le primitive sourceValue scalar.accuracy_eq
  have outputBound : Norm.Basic.normSq (targetReading.reading - scalar.certificate.output) ≤
      outputFactor * Norm.Basic.normSq (last - first) ^ 2 := by
    rewrite [scalar.output_eq]
    exact reading_le primitive targetReading scalar.accuracy_eq
  have derivativeBound := reading_le specification.differential derivative scalar.accuracy_eq
  have residualBound := scalar_slope_le scalar specification firstInside sourcePositive
    (sourceLower sourceSample.observation.witness_possible)
  have slopeBound : Norm.Basic.normSq (derivative.reading - scalar.certificate.slope) ≤
      slopeFactor * Norm.Basic.normSq (last - first) ^ 2 := by
    calc
      _ ≤ 2 * (Norm.Basic.normSq (derivative.reading -
          OddPower.Observation.scalarReading specification.differential first sourceSample.observation) +
        Norm.Basic.normSq
          (OddPower.Observation.scalarReading specification.differential first sourceSample.observation -
            scalar.certificate.slope)) := Norm.Bounds.normSq_sub_le_via _ _ _
      _ ≤ 2 * (Cache.allowanceFactor specification.differential first source sourceFloor *
          Norm.Basic.normSq (last - first) ^ 2 + Residual.factor primitive box sourceFloor *
            Norm.Basic.normSq (last - first) ^ 2) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct derivativeBound residualBound) (by decide +kernel)
      _ = _ := by dsimp only [slopeFactor]; ring1
  have baseNonnegative := Cache.allowanceFactor_nonnegative primitive first source sourcePositive
  have outputNonnegative := Cache.allowanceFactor_nonnegative primitive last target targetPositive
  have slopeNonnegative : 0 ≤ slopeFactor :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.add_le_add_direct
        (Cache.allowanceFactor_nonnegative specification.differential first source sourcePositive)
        (residual_factor_nonnegative primitive box sourcePositive))
  let certificate := scalar.certificate.perturb sourceValue.reading targetReading.reading derivative.reading
    baseFactor outputFactor slopeFactor baseNonnegative outputNonnegative slopeNonnegative unit
    baseBound outputBound slopeBound
  exact
    { sourceValue := sourceValue
      targetReading := targetReading
      derivative := derivative
      derivative_le := slopeBound
      certificate := certificate
      base_eq := rfl
      output_eq := rfl
      slope_eq := rfl
      factor_eq := rfl }

namespace Expansion

/-- The three actual independent arithmetic witnesses satisfy their internally paid finite remainder inequality. -/
theorem remainder_le
    {scalar : Taylor.Expansion polynomial primitive box inverseBox window side first last source target accuracy
      sourceSample targetSample}
    {specification : Specification polynomial primitive}
    {sourceValues : specification.Values first source.value source.apart}
    {targetValue : CoherentNamed} {sourceFloor targetFloor : Fraction.Rational}
    (expansion : Expansion scalar specification sourceValues targetValue sourceFloor targetFloor) :
    Canonical.normSq (expansion.targetReading.reading - expansion.sourceValue.reading -
      (last - first) * expansion.derivative.reading) ≤
        expansion.certificate.factor * Canonical.normSq (last - first) ^ 2 := by
  rewrite [← expansion.base_eq, ← expansion.output_eq, ← expansion.slope_eq, expansion.certificate.expansion]
  exact expansion.certificate.remainder_le

end Expansion

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative.Taylor.Observation
