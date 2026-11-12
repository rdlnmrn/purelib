module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Movement
public import Purelib.Approximation.Gaussian.Division.Prepared.Observation
import Purelib.Approximation.Gaussian.Name.Coherent.Transport

/-! # A full-cubic preparation from the identical retained paired factor state

The existing full product and two original factor observations remain the
inputs. Their actual signed windows give a candidate floor on that exact
paired state. The prepared full-cubic certificate retains the existing
arithmetic presentation and preserves all candidates into that old state.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {reading : Reading completed time inside}
variable {unitAccuracy normalAccuracy : Approximation.AccuracyRequest}

namespace Samples

/-- The actual normalized seed radius computes a strictly positive full-product squared-norm floor. -/
theorem productFloor_positive : 0 < anchor.seed.separation.radius ^ 2 / 4 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.pow_pos_direct anchor.seed.separation.positive 2)
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 4)

/-- One prepared presentation and one full-cubic certificate on the same old paired observation state. -/
@[expose] def Root (samples : Samples reading unitAccuracy normalAccuracy) : Type 1 :=
  Σ prepared : { retained : Division.Prepared reading.values.value //
      retained = Division.Prepared.ofObservation samples.product productFloor_positive
        samples.candidate_normSq_lower },
    { root : CertifiedSquareRoot.Certificate ((Paths.polynomial parameter).eval (segment.pointAt time)) //
      root = CertifiedSquareRoot.Certificate.ofPrepared reading.values.value reading.values.square prepared.val }

namespace Root

variable (samples : Samples reading unitAccuracy normalAccuracy)

/-- Prepare the old full product at its actual retained state and certify that identical prepared full cubic once. -/
def build : Root samples :=
  let prepared := Division.Prepared.ofObservation samples.product productFloor_positive samples.candidate_normSq_lower
  let root := CertifiedSquareRoot.Certificate.ofPrepared reading.values.value reading.values.square prepared
  ⟨⟨prepared, rfl⟩, ⟨root, rfl⟩⟩

variable {samples}

/-- Read the same complete productive presentation retained for the old full-product observation. -/
@[expose] def prepared (retained : Root samples) : Division.Prepared reading.values.value := retained.1.val

/-- Read the same complete full-cubic certificate, rather than either normalized-only factor certificate. -/
@[expose] def certificate (retained : Root samples) := retained.2.val

/-- The productive presentation is the existing original-state preparation on these exact factor observations. -/
theorem prepared_eq (retained : Root samples) : retained.prepared =
    Division.Prepared.ofObservation samples.product productFloor_positive samples.candidate_normSq_lower :=
  retained.1.property

/-- The full cubic is certified on that identical retained prepared presentation. -/
theorem certificate_eq (retained : Root samples) : retained.certificate =
    CertifiedSquareRoot.Certificate.ofPrepared reading.values.value reading.values.square retained.prepared :=
  retained.2.property

/-- The original product and its same-state prepared full cubic have the existing operational agreement. -/
def equivalent (retained : Root samples) :
    NamedEquivalent reading.values.value.name retained.certificate.value.name :=
  NamedEquivalent.transport rfl
    (congrArg (fun root : CertifiedSquareRoot.Certificate
      ((Paths.polynomial parameter).eval (segment.pointAt time)) => root.value.name) retained.certificate_eq).symm
    (CertifiedSquareRoot.Certificate.ofPrepared_agrees reading.values.value reading.values.square retained.prepared)

/-- The actual root name is the identical supplied prepared denominator. -/
theorem value_eq (retained : Root samples) : retained.certificate.value = retained.prepared.denominator :=
  (congrArg CertifiedSquareRoot.Certificate.value retained.certificate_eq).trans
    (CertifiedSquareRoot.Certificate.ofPrepared_value reading.values.value reading.values.square retained.prepared)

/-- An arbitrary complete preparation-factory equality preserves candidate provenance to the unchanged old reading. -/
private theorem prepared_candidate
    (prepared : Division.Prepared reading.values.value)
    (same : prepared = Division.Prepared.ofObservation samples.product productFloor_positive
      samples.candidate_normSq_lower)
    {state : prepared.denominator.name.process.State} {candidate : Canonical}
    (possible : prepared.denominator.name.process.Possible state candidate) :
    reading.values.value.name.process.Possible samples.product.state candidate := by
  cases same
  exact Division.Prepared.ofObservation_candidate samples.product productFloor_positive
    samples.candidate_normSq_lower possible

/-- Every prepared full-root candidate belongs to the SAME old paired factor state.

The original whole certificate equality transports the actual candidate
state once. The existing based and apartified provenance then returns to
the unchanged paired state; no original factor or observation is rerun.
-/
theorem candidate_at_product (retained : Root samples)
    {state : retained.certificate.value.name.process.State} {candidate : Canonical}
    (possible : retained.certificate.value.name.process.Possible state candidate) :
    reading.values.value.name.process.Possible samples.product.state candidate :=
  prepared_candidate retained.prepared retained.prepared_eq
    (possible_castState retained.value_eq state possible)

/-- Every actual prepared root candidate keeps the positive full-product floor from both original factor windows. -/
theorem candidate_lower (retained : Root samples)
    {state : retained.certificate.value.name.process.State} {candidate : Canonical}
    (possible : retained.certificate.value.name.process.Possible state candidate) :
    anchor.seed.separation.radius ^ 2 / 4 ≤ Norm.Basic.normSq candidate :=
  samples.candidate_normSq_lower (retained.candidate_at_product possible)

end Root

end Samples

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading

end
