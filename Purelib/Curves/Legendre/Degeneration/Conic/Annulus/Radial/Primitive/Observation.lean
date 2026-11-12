module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Derivative
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Factorization
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Admission
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
import Purelib.Tactic.Ring

/-!
# Independent primitive and spatial-derivative observations on the original chart

The prescribed primitive endpoint and independently computed spatial
derivative use the original polynomial and prepared full-sheet evaluator.
The derivative cache consumes the already retained primitive cache, then its
actual arithmetic product with the original base velocity is compared to the
original cofactor pullback. Both observation requests retain that identical
cofactor observation while selecting their own actual arithmetic witnesses.

These are spatial derivatives along the original chart. They do not realize
parameter derivatives or establish a primitive integral endpoint law.
-/

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}

/-- Every candidate of the same original cofactor observation pays the fixed geometric cofactor floor. -/
private theorem unitLower (reading : Transport.Reading actual time inside) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy)
    {candidate : Canonical} (possible : sample.observation.Possible candidate) :
    (1 / 16 : Fraction.Rational) ≤ Norm.Basic.normSq candidate :=
  UnitRoot.root_normSq_lower site
    (point_inside site parameter 2 (Waist.direction quarter time) positive
      actual.data.lower actual.data.upper actual.data.bound)
    (sample.candidate_residual_lt_target reading.lift.unitOwner reading.lift.unitRoot_eq possible).le

public section

/-- The retained original prepared finite-power identity gives the product-square input of the spatial derivative. -/
def square {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
    (endpoint : Endpoint primitive reading regular) :
    NamedEquivalent (endpoint.prepared.denominator.mul endpoint.prepared.denominator).name
      (Coherence.exact ((Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter time) positive).base)).name :=
  (Power.namedPower_two endpoint.prepared.denominator).symm.trans endpoint.values.identity

/-- Cache the independently constructed spatial derivative and its actual original chart pullback.

The primitive Endpoint is retained as an index. The derivative values reuse
its actual numerical primitive evaluator and prepared denominator, then one
arithmetic product and one original factored pullback are materialized.
-/
@[expose] def DerivativeValues {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (endpoint : Endpoint primitive reading regular) :=
  Σ values : { retained : specification.Values
        (point site parameter 2 (Waist.direction quarter time) positive).base
        endpoint.prepared.denominator endpoint.prepared.apart //
      retained = OddPower.Derivative.Specification.Values.build specification
        (point site parameter 2 (Waist.direction quarter time) positive).base
        endpoint.prepared.denominator endpoint.prepared.apart (square endpoint)
        endpoint.values.value endpoint.values.value_eq },
    { pullback : CoherentNamed // pullback = values.val.derivative.mul
        (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time)) } ×
      { factored : CoherentNamed // factored = Differential.value specification.differential reading.lift }

namespace DerivativeValues

/-- Cache the independent derivative, its base-velocity product and its original cofactor factorization once. -/
def build {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (endpoint : Endpoint primitive reading regular) : DerivativeValues specification endpoint :=
  let values := OddPower.Derivative.Specification.Values.build specification
    (point site parameter 2 (Waist.direction quarter time) positive).base
    endpoint.prepared.denominator endpoint.prepared.apart (square endpoint)
    endpoint.values.value endpoint.values.value_eq
  let pullback := values.derivative.mul (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time))
  let factored := Differential.value specification.differential reading.lift
  ⟨⟨values, rfl⟩, ⟨⟨pullback, rfl⟩, ⟨factored, rfl⟩⟩⟩

variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive}
variable {endpoint : Endpoint primitive reading regular}

/-- Read the independent original derivative and its retained Leibniz evaluator caches. -/
@[expose] def values (retained : DerivativeValues specification endpoint) := retained.1.val

/-- Read the actual arithmetic product of the independently constructed derivative and original chart base velocity. -/
@[expose] def pullback (retained : DerivativeValues specification endpoint) : CoherentNamed := retained.2.1.val

/-- Read the cached original cofactor pullback of that identical independent spatial derivative specification. -/
@[expose] def factored (retained : DerivativeValues specification endpoint) : CoherentNamed := retained.2.2.val

/-- The primitive component of the independent derivative cache is the unchanged original Endpoint evaluator. -/
theorem primitive_eq (retained : DerivativeValues specification endpoint) :
    retained.values.primitiveValue = endpoint.values.value := by
  rewrite [show retained.values = OddPower.Derivative.Specification.Values.build specification
    (point site parameter 2 (Waist.direction quarter time) positive).base
    endpoint.prepared.denominator endpoint.prepared.apart (square endpoint)
    endpoint.values.value endpoint.values.value_eq from retained.1.property]
  exact OddPower.Derivative.Specification.Values.build_primitiveValue _ _ _ _ _ _ _

/-- The actual derivative pullback cache is its complete product factory on the same original chart. -/
theorem pullback_eq (retained : DerivativeValues specification endpoint) : retained.pullback =
    retained.values.derivative.mul (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time)) :=
  retained.2.1.property

/-- The factored derivative cache is the original pullback factory of its independently computed specification. -/
theorem factored_eq (retained : DerivativeValues specification endpoint) : retained.factored =
    Differential.value specification.differential reading.lift := retained.2.2.property

/-- The actual independent derivative product agrees operationally with its identical retained factored evaluator. -/
def agrees (retained : DerivativeValues specification endpoint) :
    NamedEquivalent retained.pullback.name retained.factored.name := by
  have left_eq : retained.pullback = (specification.differential.value
      (point site parameter 2 (Waist.direction quarter time) positive).base
      endpoint.prepared.denominator endpoint.prepared.apart).mul
        (Coherence.exact (Tangent.baseVelocity site parameter 2 quarter time)) := by
    rewrite [retained.pullback_eq, retained.values.derivative_eq]
    rfl
  exact NamedEquivalent.transport (congrArg (fun value : CoherentNamed => value.name) left_eq.symm)
    (congrArg (fun value : CoherentNamed => value.name) retained.factored_eq.symm)
    (Differential.value_agrees specification.differential regular reading.lift endpoint.prepared)

end DerivativeValues

/-- The paid factored primitive anchor is the independently prescribed original primitive endpoint formula. -/
theorem primitive_scalar_eq (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (sample : OddPower.Observation.RootObservation) :
    Factorization.scalarReading primitive
      (point site parameter 2 (Waist.direction quarter time) positive).base
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ sample =
      Primitive.reading (site := site) primitive quarter time sample.witness := by
  unfold Factorization.scalarReading Factorization.weight
    OddPower.Observation.scalarReading Primitive.reading
  calc
    _ = (primitive.scale * primitive.numerator.eval
        (point site parameter 2 (Waist.direction quarter time) positive).base *
        (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ *
          (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹ ^
            (2 * primitive.denominatorPairs)) * sample.witness⁻¹ ^ primitive.denominatorExponent := by ring1
    _ = _ := by rewrite [primitive.factorized_inverse_coefficient]; rfl

/-- The paid factored derivative anchor is the independent spatial derivative's prescribed original chart scalar. -/
theorem derivative_scalar_eq (differential : OddPowerDifferential (Paths.polynomial parameter))
    (sample : OddPower.Observation.RootObservation) :
    Factorization.scalarReading differential
      (point site parameter 2 (Waist.direction quarter time) positive).base
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate
      (Stereographic.Tangent.logarithmicVelocity time) sample =
      Differential.reading site parameter quarter time differential sample.witness := by
  unfold Factorization.scalarReading Factorization.weight
    OddPower.Observation.scalarReading Differential.reading
  ring1

/-- Observe the retained primitive evaluator at its prescribed endpoint using the same original cofactor sample. -/
def primitiveRequest (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (regular : parameter ≠ criticalValue site)
    (endpoint : Endpoint primitive reading regular) {rootAccuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy)
    (accuracy : AccuracyRequest) :
    Factorization.Reading primitive
      (point site parameter 2 (Waist.direction quarter time) positive).base
      reading.lift.unitRoot.value reading.lift.unitRoot.apart sample.state sample.observation
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹
      endpoint.values.value endpoint.values.factored accuracy (1 / 16) :=
  Factorization.request primitive
    (point site parameter 2 (Waist.direction quarter time) positive).base
    reading.lift.unitRoot.value reading.lift.unitRoot.apart sample.state sample.observation sample.observation_eq
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹
    endpoint.values.value endpoint.values.factored endpoint.values.factored_eq
    (endpoint.values.agrees_factored regular) accuracy (1 / 16) (by decide +kernel) (unitLower reading sample)

/-- Observe the independent spatial derivative times original base velocity using the unchanged cofactor sample. -/
def derivativeRequest {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
    (specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive)
    (endpoint : Endpoint primitive reading regular) (retained : DerivativeValues specification endpoint)
    {rootAccuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy)
    (accuracy : AccuracyRequest) :
    Factorization.Reading specification.differential
      (point site parameter 2 (Waist.direction quarter time) positive).base
      reading.lift.unitRoot.value reading.lift.unitRoot.apart sample.state sample.observation
      (point site parameter 2 (Waist.direction quarter time) positive).ordinate
      (Stereographic.Tangent.logarithmicVelocity time)
      retained.pullback retained.factored accuracy (1 / 16) :=
  Factorization.request specification.differential
    (point site parameter 2 (Waist.direction quarter time) positive).base
    reading.lift.unitRoot.value reading.lift.unitRoot.apart sample.state sample.observation sample.observation_eq
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (Stereographic.Tangent.logarithmicVelocity time) retained.pullback retained.factored retained.factored_eq
    retained.agrees accuracy (1 / 16) (by decide +kernel) (unitLower reading sample)

end

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation
