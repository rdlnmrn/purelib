module

public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Request
public import Purelib.Algebra.Monogenic.Coordinates.Reading.Observation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Composed observations on the original root tower

Every stage retains one actual original cyclic observation and pays its own
backward residual request. The tail consumes that same cached child reading.
The endpoint therefore reads the original final coefficient algebra, with
the fixed gain and the error requested before any observations were made.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading renaming
  Observation → CyclicObservation, Request → CyclicRequest
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

universe u

/-- The original final scalar-reading type, retaining its same cached weight and scalar embedding. -/
@[expose] def Endpoint {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius : Rational} (parameters : Parameters tower parent gain radius)
    (embed : Canonical → K) : Type u :=
  GaussianReading parameters.finalWeight (fun coefficient => tower.embed (embed coefficient))

set_option genInjectivity false in
/-- The actual paid original observations and cached readings of one complete budget.

The same original tower, parameter chain, budget and initial Gaussian reading
remain indices. Each tail is indexed by its preceding retained child, so no
final model or independent final error certificate is supplied by a caller.
-/
inductive Trace : {K : Type u} → [ring : CommRing K] → [equality : DecidableEq K] →
    {polynomial : DensePolynomial K} → {tower : Tower K ring equality polynomial} →
    {parent : Weight K} → {gain radius target tolerance : Rational} →
    {parameters : Parameters tower parent gain radius} → Budget parameters target tolerance →
    {embed : Canonical → K} → (reading : GaussianReading parent embed) → reading.gain = gain →
    Endpoint parameters embed → Type (u + 1)
  /-- The original constant endpoint retains the same initial reading without an observation. -/
  | constant {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
      {parent : Weight K} {gain radius target : Rational} {degreeZero : polynomial.natDegree = 0}
      {gainNonnegative : 0 ≤ gain} {radiusNonnegative : 0 ≤ radius} {targetPositive : 0 < target}
      {embed : Canonical → K} {reading : GaussianReading parent embed} {gain_eq : reading.gain = gain} :
      Trace (.constant targetPositive : Budget
        (.constant degreeZero gainNonnegative radiusNonnegative :
          Parameters (.constant polynomial degreeZero) parent gain radius) target target) reading gain_eq reading
  /-- One paid observation constructs the same child consumed by the remaining original stages. -/
  | step {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
      {adjunction : Companion.Adjunction polynomial}
      {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
      {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}
      {parent : Weight K} {gain radius target tolerance : Rational}
      {current : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius}
      {next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius}
      {embed : Canonical → K} {reading : GaussianReading parent embed} {gain_eq : reading.gain = gain}
      {endpoint : Endpoint next (fun coefficient => Cyclic.Element.scalar adjunction.table (embed coefficient))}
      (tail : Budget next target tolerance) (request : CyclicRequest current tolerance)
      (observation : CyclicObservation current reading gain_eq) (paid : observation.residual ≤ request.tolerance)
      (rest : Trace tail observation.child observation.gain_eq endpoint) :
      Trace (.step tail request : Budget
        (.step current next : Parameters (.step adjunction decreases remaining) parent gain radius)
          target request.tolerance) reading gain_eq endpoint

constructive_injectivity Trace

set_option genInjectivity false in
/-- A cached final reading with every actual paid original stage and its endpoint certificate.

The endpoint is retained directly rather than recovered by executable
elimination of the large dependent trace. The trace keeps all original
observations and certifies that this is the same final child they construct.
-/
structure Realization {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
    {parent : Weight K} {gain radius target tolerance : Rational} {parameters : Parameters tower parent gain radius}
    (budget : Budget parameters target tolerance) {embed : Canonical → K}
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain) where
  /-- The same cached endpoint reading of the original final coefficient algebra. -/
  finalReading : Endpoint parameters embed
  /-- Every original observation and payment produces this exact retained endpoint. -/
  trace : Trace budget reading gain_eq finalReading

constructive_injectivity Realization

namespace Realization

/-- Retain the same initial reading as the endpoint of an original constant budget. -/
@[expose] def constant {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {parent : Weight K} {gain radius target : Rational}
    {degreeZero : polynomial.natDegree = 0} {gainNonnegative : 0 ≤ gain} {radiusNonnegative : 0 ≤ radius}
    {embed : Canonical → K} (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain)
    (targetPositive : 0 < target) : Realization (.constant targetPositive : Budget
      (.constant degreeZero gainNonnegative radiusNonnegative :
        Parameters (.constant polynomial degreeZero) parent gain radius) target target) reading gain_eq :=
  { finalReading := reading, trace := .constant }

/-- Retain one paid original observation and the exact cached endpoint of its same original tail. -/
@[expose] def step {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
    {polynomial : DensePolynomial K} {adjunction : Companion.Adjunction polynomial}
    {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
    {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}
    {parent : Weight K} {gain radius target tolerance : Rational}
    {current : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius}
    {next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius}
    {embed : Canonical → K} {reading : GaussianReading parent embed} {gain_eq : reading.gain = gain}
    (tail : Budget next target tolerance) (request : CyclicRequest current tolerance)
    (observation : CyclicObservation current reading gain_eq) (paid : observation.residual ≤ request.tolerance)
    (rest : Realization tail observation.child observation.gain_eq) :
    Realization (.step tail request : Budget
      (.step current next : Parameters (.step adjunction decreases remaining) parent gain radius)
        target request.tolerance) reading gain_eq :=
  { finalReading := rest.finalReading, trace := .step tail request observation paid rest.trace }

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {tower : Tower K ring equality polynomial} {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius} {budget : Budget parameters target tolerance}
variable {embed : Canonical → K} {reading : GaussianReading parent embed} {gain_eq : reading.gain = gain}

/-- The same cached endpoint has the final gain fixed before all original observations. -/
theorem final_gain (realization : Realization budget reading gain_eq) :
    realization.finalReading.gain = parameters.finalGain := by
  cases realization with
  | mk _ trace =>
      induction trace with
      | constant => assumption
      | step _ _ _ _ _ previous => exact previous

/-- Every paid original observation composes to the requested endpoint error from the paid initial reading. -/
theorem error_le (realization : Realization budget reading gain_eq) :
    reading.error ≤ tolerance → realization.finalReading.error ≤ target := by
  cases realization with
  | mk _ trace =>
      induction trace with
      | constant => intro bounded; exact bounded
      | step _ request observation paid _ previous =>
          intro bounded
          exact previous (observation.error_lt request bounded paid).le

/-- A strict paid initial error gives a strict requested error at the same cached endpoint. -/
theorem error_lt (realization : Realization budget reading gain_eq) :
    reading.error < tolerance → realization.finalReading.error < target := by
  cases realization with
  | mk _ trace =>
      induction trace with
      | constant => intro bounded; exact bounded
      | step _ request observation paid _ previous =>
          intro bounded
          exact previous (observation.error_lt request bounded.le paid)

/-- The final model reads each original embedded coefficient exactly as the same initial model.

Scalar readback at each original cyclic adjunction is exact even when its
multiplication is only approximately preserved. Later stages therefore keep
all earlier coefficient readings rather than perturbing them again.
-/
theorem final_read_embed (realization : Realization budget reading gain_eq) :
    ∀ value : K, realization.finalReading.read (tower.embed value) = reading.read value := by
  cases realization with
  | mk _ trace =>
      induction trace with
      | constant => intro value; rfl
      | step _ _ observation _ _ previous =>
          intro value
          exact (previous (Cyclic.Element.scalar _ value)).trans
            (observation.read_scalar value)

end Realization

end Purelib.Polynomial.Dense.Roots.Tower.Reading

end
