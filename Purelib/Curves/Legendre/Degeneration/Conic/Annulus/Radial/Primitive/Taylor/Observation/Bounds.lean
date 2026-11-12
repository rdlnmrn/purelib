module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Observation
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-!
# Uniform ceilings for the retained primitive arithmetic chart expansion

The original parallel ordinate floor pays the primitive's odd reciprocal
weight and the spatial derivative's even reciprocal weight. The original
logarithmic velocity bounds the latter uniformly. Those computed weights
and the original spatial box pay the existing arithmetic allowances on the
identical retained cofactor certificates, with no new observation or query.

The actual scalar cache equality and exact constructed factor readback then
bound the observed expansion. Every original arithmetic comparison, chosen
state, reading and remainder payment remains unchanged. The conclusion is a
finite chart bound; it asserts no primitive integral endpoint law.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Observation

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation

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
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time delta : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside time} {lastInside : FixedRootBoxPath.Inside (time + delta)}

/-- The uncancelled primitive weight is exactly the original ordinate's odd reciprocal power. -/
private theorem primitive_weight_eq (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (ordinate : Canonical) :
    Factorization.weight primitive ordinate ordinate⁻¹ =
      ordinate⁻¹ ^ primitive.denominatorExponent := by
  unfold Factorization.weight OddPowerDifferential.denominatorExponent
  rewrite [pow_succ]
  exact Gaussian.Basic.mul_comm _ _

public section

/-- The original spatial box and intrinsic ordinate floor compute the primitive observation's fixed allowance. -/
def primitiveCeiling (site : Fin 2) (parameter : Canonical)
    (primitive : OddPowerDifferential (Paths.polynomial parameter)) : Fraction.Rational :=
  Factorization.allowanceCeiling primitive (spatialBox site) (1 / 16)
    (((9 / 16) * Norm.Basic.normSq (halfGap site parameter))⁻¹ ^ primitive.denominatorExponent)

/-- The original logarithmic velocity and even ordinate reciprocal weight compute the derivative's fixed allowance. -/
def derivativeCeiling (site : Fin 2) (parameter : Canonical)
    {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive) : Fraction.Rational :=
  Factorization.allowanceCeiling specification.differential (spatialBox site) (1 / 16)
    (4 * ((9 / 16) * Norm.Basic.normSq (halfGap site parameter))⁻¹ ^
      (2 * specification.differential.denominatorPairs))

/-- Intrinsic regularity makes the computed original primitive allowance nonnegative. -/
theorem primitiveCeiling_nonnegative (site : Fin 2) (parameter : Canonical)
    (primitive : OddPowerDifferential (Paths.polynomial parameter)) (regular : parameter ≠ criticalValue site) :
    0 ≤ primitiveCeiling site parameter primitive :=
  Factorization.allowanceCeiling_nonnegative primitive (spatialBox site)
    (by decide +kernel)
    (Arithmetic.pow_nonneg_direct
      (Fraction.Order.Field.inv_pos_direct (parallel_ordinate_floor_positive site parameter regular)).le
      primitive.denominatorExponent)

/-- Intrinsic regularity makes the computed independent spatial derivative allowance nonnegative. -/
theorem derivativeCeiling_nonnegative (site : Fin 2) (parameter : Canonical)
    {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (regular : parameter ≠ criticalValue site) : 0 ≤ derivativeCeiling site parameter specification :=
  Factorization.allowanceCeiling_nonnegative specification.differential (spatialBox site)
    (by decide +kernel)
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.pow_nonneg_direct
        (Fraction.Order.Field.inv_pos_direct (parallel_ordinate_floor_positive site parameter regular)).le
        (2 * specification.differential.denominatorPairs)))

/-- The original point enclosure and ordinate floor bound an endpoint's exact retained primitive allowance.

The original unit-root certificate remains the arithmetic allowance owner.
The prescribed ordinate reciprocal weight receives its bound internally from
the original parallel geometry, independently of time and sample indices.
-/
theorem primitiveFactor_le_ceiling (primitive : OddPowerDifferential (Paths.polynomial parameter))
    {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
    (reading : Transport.Reading actual time inside) (regular : parameter ≠ criticalValue site) :
    primitiveFactor primitive reading ≤ primitiveCeiling site parameter primitive := by
  have weightBound : Norm.Basic.normSq
      (Factorization.weight primitive
        (point site parameter 2 (Waist.direction quarter time) positive).ordinate
        (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹) ≤
      ((9 / 16) * Norm.Basic.normSq (halfGap site parameter))⁻¹ ^ primitive.denominatorExponent := by
    rewrite [primitive_weight_eq]
    exact Norm.Reciprocal.power_normSq_le (parallel_ordinate_floor_positive site parameter regular)
      (parallel_ordinate_lower site parameter (Waist.direction quarter time)) primitive.denominatorExponent
  exact Factorization.allowanceFactor_le_ceiling primitive
    (point site parameter 2 (Waist.direction quarter time) positive).base
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ reading.lift.unitRoot
    (point_inside site parameter 2 (Waist.direction quarter time) positive
      actual.data.lower actual.data.upper actual.data.bound) (by decide +kernel) weightBound

/-- The original point enclosure, ordinate floor and logarithmic velocity bound the actual derivative allowance.

The spatial derivative and its original cofactor certificate remain the
same inputs of the arithmetic allowance. The velocity and even reciprocal
power budgets are derived from those original chart owners.
-/
theorem derivativeFactor_le_ceiling {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (source : Transport.Reading actual time firstInside) (regular : parameter ≠ criticalValue site) :
    derivativeFactor specification source ≤ derivativeCeiling site parameter specification := by
  have powerBound := Norm.Reciprocal.power_normSq_le (parallel_ordinate_floor_positive site parameter regular)
    (parallel_ordinate_lower site parameter (Waist.direction quarter time))
    (2 * specification.differential.denominatorPairs)
  have weightBound : Norm.Basic.normSq
      (Factorization.weight specification.differential
        (point site parameter 2 (Waist.direction quarter time) positive).ordinate
        (Stereographic.Tangent.logarithmicVelocity time)) ≤
      4 * ((9 / 16) * Norm.Basic.normSq (halfGap site parameter))⁻¹ ^
        (2 * specification.differential.denominatorPairs) := by
    unfold Factorization.weight
    rewrite [Norm.Basic.normSq_mul]
    exact Arithmetic.mul_le_mul_direct
      (Stereographic.Tangent.logarithmicVelocity_normSq_le time) powerBound
      (Norm.Basic.normSq_nonneg _) (by decide +kernel)
  exact Factorization.allowanceFactor_le_ceiling specification.differential
    (point site parameter 2 (Waist.direction quarter time) positive).base
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (Stereographic.Tangent.logarithmicVelocity time) source.lift.unitRoot
    (point_inside site parameter 2 (Waist.direction quarter time) positive
      actual.data.lower actual.data.upper actual.data.bound) (by decide +kernel) weightBound

/-- Original scalar, endpoint and spatial-derivative budgets compute the observed primitive's fixed chart ceiling.

The ceiling depends only on the original primitive, derivative specification,
site, parameter and intrinsic regularity. It contains no chart times, sample
indices, supplied inverse enclosure or requested remainder conclusion.
-/
def ceiling (site : Fin 2) (parameter : Canonical)
    (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (regular : parameter ≠ criticalValue site) : Fraction.Rational :=
  4 * (Taylor.ceiling site parameter primitive regular + 2 * primitiveCeiling site parameter primitive +
    2 * (derivativeCeiling site parameter specification + Taylor.slopeResidualFactor site parameter primitive))

/-- Intrinsic regularity makes the observed primitive's computed fixed chart ceiling nonnegative. -/
theorem ceiling_nonnegative (site : Fin 2) (parameter : Canonical)
    (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (regular : parameter ≠ criticalValue site) : 0 ≤ ceiling site parameter primitive specification regular :=
  Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.add_le_add_direct
      (Arithmetic.add_le_add_direct (Taylor.ceiling_nonnegative site parameter primitive regular)
        (Arithmetic.mul_nonneg_direct (by decide +kernel)
          (primitiveCeiling_nonnegative site parameter primitive regular)))
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Arithmetic.add_le_add_direct
          (derivativeCeiling_nonnegative site parameter specification regular)
          (Taylor.slopeResidualFactor_nonnegative site parameter primitive regular))))

namespace Expansion

variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {source : Transport.Reading actual time firstInside}
variable {target : Transport.Reading actual (time + delta) lastInside} {regular : parameter ≠ criticalValue site}
variable {accuracy : AccuracyRequest}
variable {sourceSample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy}
variable {targetSample : CertifiedSquareRoot.Sampling.ResidualObservation target.lift.unitRoot accuracy}
variable {sourceEndpoint : Endpoint primitive source regular} {targetEndpoint : Endpoint primitive target regular}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive}
variable {sourceValues : Primitive.Observation.DerivativeValues specification sourceEndpoint}

/-- The exact retained scalar builder and observed factor readback pay the fixed chart ceiling.

The original scalar cache is compared through its factory equality. The
actual source, target and independent derivative allowance factors retain
the same original cofactor owners. Only scalar bounds are composed; every
selected arithmetic comparison, state, reading and certificate stays intact.
-/
theorem factor_le (expansion : Expansion primitive source target regular accuracy sourceSample targetSample
    sourceEndpoint targetEndpoint specification sourceValues) :
    expansion.certificate.factor ≤ ceiling site parameter primitive specification regular := by
  have scalarFactor_eq : expansion.scalar.certificate.factor =
      (Taylor.build primitive source target regular accuracy sourceSample targetSample
        expansion.scalar.accuracy_eq).certificate.factor :=
    congrArg (fun cached : Taylor.Expansion primitive source target accuracy sourceSample targetSample =>
      cached.certificate.factor) expansion.scalar_eq
  have scalarBound := scalarFactor_eq.trans_le
    (Taylor.build_factor_le primitive source target regular accuracy sourceSample targetSample
      expansion.scalar.accuracy_eq)
  have sourceBound := primitiveFactor_le_ceiling primitive source regular
  have targetBound := primitiveFactor_le_ceiling primitive target regular
  have derivativeBound := derivativeFactor_le_ceiling specification source regular
  have derivativePaid :
      2 * (derivativeFactor specification source + Taylor.slopeResidualFactor site parameter primitive) ≤
        2 * (derivativeCeiling site parameter specification + Taylor.slopeResidualFactor site parameter primitive) :=
    Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct derivativeBound
        (Fraction.Order.Basic.le_refl (Taylor.slopeResidualFactor site parameter primitive))) (by decide +kernel)
  have paid : expansion.scalar.certificate.factor + primitiveFactor primitive source +
      primitiveFactor primitive target +
        2 * (derivativeFactor specification source + Taylor.slopeResidualFactor site parameter primitive) ≤
      Taylor.ceiling site parameter primitive regular + primitiveCeiling site parameter primitive +
        primitiveCeiling site parameter primitive +
          2 * (derivativeCeiling site parameter specification + Taylor.slopeResidualFactor site parameter primitive) :=
    Arithmetic.add_le_add_direct
      (Arithmetic.add_le_add_direct
        (Arithmetic.add_le_add_direct scalarBound sourceBound) targetBound) derivativePaid
  rewrite [expansion.factor_eq]
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct (c := (4 : Fraction.Rational)) paid
    (by decide +kernel)).trans_eq (by unfold ceiling; ring1)

/-- The same three actual arithmetic readings obey the fixed primitive chart remainder ceiling. -/
theorem uniform_remainder_le (expansion : Expansion primitive source target regular accuracy sourceSample targetSample
    sourceEndpoint targetEndpoint specification sourceValues) :
    Norm.Basic.normSq (expansion.targetValue.reading - expansion.sourceValue.reading -
      Stereographic.Tangent.increment delta * expansion.derivative.reading) ≤
      ceiling site parameter primitive specification regular * delta ^ 4 := by
  have fourthNonnegative : (0 : Fraction.Rational) ≤ delta ^ 4 :=
    (Arithmetic.sq_nonneg_direct (delta * delta)).trans_eq (by ring1)
  exact expansion.remainder_le.trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct expansion.factor_le fourthNonnegative)

end Expansion

end

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Observation
