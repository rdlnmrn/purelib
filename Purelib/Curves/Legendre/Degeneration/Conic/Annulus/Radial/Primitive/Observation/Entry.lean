module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Reading.Time
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Stages

/-!
# Retained primitive endpoint observations

One endpoint keeps its complete original full-sheet preparation and
primitive evaluator caches. Its existing cofactor observation retains its
own square-residual request, selected state and index; an independent
arithmetic request selects the actual original/factored comparison once.

Exact time-index transport moves this entire cache without another query,
root request, preparation or arithmetic comparison. Both original arithmetic
observations and their complete comparison remain the retained originals.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation

open Purelib
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}

/-- The original paid primitive arithmetic Reading retains distinct root-residual and arithmetic requests. -/
abbrev EndpointReading {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
    (endpoint : Endpoint primitive reading regular) {rootAccuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy)
    (accuracy : AccuracyRequest) :=
  OddPower.Observation.Factorization.Reading primitive
    (point site parameter 2 (Waist.direction quarter time) positive).base
    reading.lift.unitRoot.value reading.lift.unitRoot.apart sample.state sample.observation
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate
    (point site parameter 2 (Waist.direction quarter time) positive).ordinate⁻¹
    endpoint.values.value endpoint.values.factored accuracy (1 / 16)

/-- One actual endpoint cache retains its original primitive evaluators and one selected arithmetic comparison.

The original Reading, selected cofactor observation and both requests remain
indices. The selected arithmetic Reading is its exact original factory on
these retained caches; its scalar witness is not substituted for a name.
-/
@[expose] def Entry (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (regular : parameter ≠ criticalValue site)
    {rootAccuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy)
    (accuracy : AccuracyRequest) :=
  Σ endpoint : Endpoint primitive reading regular,
    { selected : EndpointReading endpoint sample accuracy //
      selected = primitiveRequest primitive reading regular endpoint sample accuracy }

namespace Entry

/-- Observe a supplied original endpoint once, preserving its complete prepared sheet and evaluator caches. -/
def ofEndpoint {primitive : OddPowerDifferential (Paths.polynomial parameter)}
    {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
    (endpoint : Endpoint primitive reading regular) {rootAccuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy)
    (accuracy : AccuracyRequest) : Entry primitive reading regular sample accuracy :=
  let selected := primitiveRequest primitive reading regular endpoint sample accuracy
  ⟨endpoint, ⟨selected, rfl⟩⟩

/-- Construct one original primitive endpoint and its selected arithmetic observation on the supplied root sample. -/
def build (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (regular : parameter ≠ criticalValue site)
    {rootAccuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy)
    (accuracy : AccuracyRequest) : Entry primitive reading regular sample accuracy :=
  let endpoint := Endpoint.build primitive reading regular
  ofEndpoint endpoint sample accuracy

section Retained

variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
variable {rootAccuracy accuracy : AccuracyRequest}
variable {sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy}

/-- Read the complete original endpoint preparation and three actual primitive evaluator caches. -/
@[expose] def endpoint (entry : Entry primitive reading regular sample accuracy) :
    Endpoint primitive reading regular := entry.1

/-- Read the unchanged selected arithmetic comparison, states and original/factored observations. -/
@[expose] def selected (entry : Entry primitive reading regular sample accuracy) :
    EndpointReading entry.endpoint sample accuracy := entry.2.val

/-- The retained arithmetic observation is the original request factory on this same endpoint and root sample. -/
theorem selected_eq (entry : Entry primitive reading regular sample accuracy) :
    entry.selected = primitiveRequest primitive reading regular entry.endpoint sample accuracy := entry.2.property

/-- Read the original evaluator's actual selected witness without repeating either observation request. -/
@[expose] def value (entry : Entry primitive reading regular sample accuracy) : Canonical := entry.selected.reading

variable {other : Fraction.Rational} {otherInside : FixedRootBoxPath.Inside other}

/-- Transport the whole original endpoint observation along an exact time equality without recomputing any cache. -/
@[expose] def castTime (equal : time = other) (entry : Entry primitive reading regular sample accuracy) :
    Entry primitive (reading.castTime (lastInside := otherInside) equal) regular
      (reading.castTimeSample (lastInside := otherInside) equal sample) accuracy := by
  cases equal
  exact entry

/-- Exact time transport preserves the original selected primitive witness. -/
theorem castTime_value (equal : time = other) (entry : Entry primitive reading regular sample accuracy) :
    (entry.castTime (otherInside := otherInside) equal).value = entry.value := by
  cases equal
  rfl

/-- Exact time transport preserves the selected original/factored arithmetic comparison and both its starts. -/
theorem castTime_comparison (equal : time = other) (entry : Entry primitive reading regular sample accuracy) :
    HEq (entry.castTime (otherInside := otherInside) equal).selected.comparison entry.selected.comparison := by
  cases equal
  rfl

/-- Exact time transport preserves both complete original arithmetic observation records. -/
theorem castTime_observations (equal : time = other) (entry : Entry primitive reading regular sample accuracy) :
    (entry.castTime (otherInside := otherInside) equal).selected.originalObservation =
      entry.selected.originalObservation ∧
    (entry.castTime (otherInside := otherInside) equal).selected.paidObservation = entry.selected.paidObservation := by
  cases equal
  exact ⟨rfl, rfl⟩

end Retained

/-- One original endpoint keeps its root selection after a stated stage and its independent primitive observation.

The returned original residual observation includes its selected state,
comparison and attained stage floor. The primitive Entry consumes that same
observation without repeating the square-root request.
-/
@[expose] def Sampled (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (regular : parameter ≠ criticalValue site)
    (rootAccuracy accuracy : AccuracyRequest) (stage : Nat) :=
  Σ sample : { retained : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy //
      stage ≤ retained.comparison.leftIndex },
    Entry primitive reading regular sample.val accuracy

namespace Sampled

/-- Request the same original cofactor certificate after its own retained stage and cache one primitive observation. -/
def build (primitive : OddPowerDifferential (Paths.polynomial parameter))
    (reading : Transport.Reading actual time inside) (regular : parameter ≠ criticalValue site)
    (rootAccuracy accuracy : AccuracyRequest) (stage : Nat) :
    Sampled primitive reading regular rootAccuracy accuracy stage :=
  let sample := CertifiedSquareRoot.Sampling.requestAfter reading.lift.unitRoot rootAccuracy stage
  let entry := Entry.build primitive reading regular sample.val accuracy
  ⟨sample, entry⟩

variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {reading : Transport.Reading actual time inside} {regular : parameter ≠ criticalValue site}
variable {rootAccuracy accuracy : AccuracyRequest} {stage : Nat}

/-- Read the exact original cofactor residual observation selected by the retained stage-aware root request. -/
@[expose] def sample (retained : Sampled primitive reading regular rootAccuracy accuracy stage) :
    CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot rootAccuracy := retained.1.val

/-- Read the primitive endpoint cache and arithmetic comparison on that identical selected cofactor observation. -/
@[expose] def entry (retained : Sampled primitive reading regular rootAccuracy accuracy stage) :
    Entry primitive reading regular retained.sample accuracy := retained.2

/-- The same selected square comparison index pays the original supplied stage on this exact endpoint certificate. -/
theorem index_ge (retained : Sampled primitive reading regular rootAccuracy accuracy stage) :
    stage ≤ retained.sample.comparison.leftIndex := retained.1.property

end Sampled

end Entry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation

end
