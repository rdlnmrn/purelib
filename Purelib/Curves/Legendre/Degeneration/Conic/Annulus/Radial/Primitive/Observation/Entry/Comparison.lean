module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Factorization.Comparison
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Interpretation
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-!
# Finite comparisons of retained primitive endpoint observations

Both endpoint Entries keep their original full cubic lift, prepared
denominator, coefficient denotation, evaluator and selected arithmetic
observation. A supplied operational comparison of the original full cubic
lifts transports the cached coefficient denotations at an identical base.
The existing generic observation comparison then pays the two old selected
arithmetic values using their actual state radii and its new tail request.

No original root or arithmetic observation is requested again. In
particular, the old arithmetic values remain independent witnesses.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

namespace Entry

variable {site : Fin 2} {parameter : Canonical}
variable {firstQuarter lastQuarter : UnitCircuitQuarter}
variable {firstPositive lastPositive : (0 : Fraction.Rational) < 2}
variable {firstActual : Transport.Quarter site parameter 2 firstQuarter firstPositive}
variable {lastActual : Transport.Quarter site parameter 2 lastQuarter lastPositive}
variable {firstTime lastTime : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside firstTime} {lastInside : FixedRootBoxPath.Inside lastTime}
variable {firstReading : Transport.Reading firstActual firstTime firstInside}
variable {lastReading : Transport.Reading lastActual lastTime lastInside}
variable {firstRegular lastRegular : parameter ≠ criticalValue site}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {firstRootAccuracy lastRootAccuracy firstAccuracy lastAccuracy : AccuracyRequest}
variable {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
variable {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}

/-- Compare the two retained prepared denominators through their original full cubic lift owners. -/
def preparedEquivalent
    (first : Entry primitive firstReading firstRegular firstSample firstAccuracy)
    (last : Entry primitive lastReading lastRegular lastSample lastAccuracy)
    (fullSheet : NamedEquivalent firstReading.lift.value.name lastReading.lift.value.name) :
    NamedEquivalent first.endpoint.prepared.denominator.name last.endpoint.prepared.denominator.name :=
  first.endpoint.prepared.equivalent.symm.trans (fullSheet.trans last.endpoint.prepared.equivalent)

/-- The two original primitive evaluator names agree at the same base and operationally compared full sheet.

The coefficient comparison transports the last endpoint's retained exact
quadratic pair to the first prepared denominator. Exact base equality only
identifies coefficient evaluation; the supplied full cubic comparison pays
the selected generator. Both original numerical evaluators are connected
through their own existing cached interpretation comparisons.
-/
def equivalent
    (first : Entry primitive firstReading firstRegular firstSample firstAccuracy)
    (last : Entry primitive lastReading lastRegular lastSample lastAccuracy)
    (point_eq : (point site parameter 2 (Waist.direction firstQuarter firstTime) firstPositive).base =
      (point site parameter 2 (Waist.direction lastQuarter lastTime) lastPositive).base)
    (fullSheet : NamedEquivalent firstReading.lift.value.name lastReading.lift.value.name) :
    NamedEquivalent first.endpoint.values.value.name last.endpoint.values.value.name := by
  let sheets := first.preparedEquivalent last fullSheet
  let moved := last.endpoint.values.interpretation.transport first.endpoint.prepared.denominator sheets
  have channel_eq : moved.channel = first.endpoint.values.interpretation.channel :=
    moved.channel_readback.trans
      ((congrArg (fun coordinate : Canonical =>
          primitive.coefficient.denote coordinate first.endpoint.prepared.denominator) point_eq.symm).trans
        first.endpoint.values.interpretation.channel_readback.symm)
  have transported := last.endpoint.values.interpretation.transport_equivalent
    first.endpoint.prepared.denominator sheets
  have interpreted : NamedEquivalent first.endpoint.values.interpretation.channel.name
      last.endpoint.values.interpretation.channel.name :=
    NamedEquivalent.transport (congrArg CoherentNamed.name channel_eq) rfl transported
  exact first.endpoint.values.agrees_interpretation.trans
    (interpreted.trans last.endpoint.values.agrees_interpretation.symm)

/-- Compare the unchanged actual primitive arithmetic observations with one finite operational tail request.

The two observation views are formed once from the old selected states and
witnesses. The returned original Comparison stores both views, their actual
ball radii, based processes, selected tail samples and quantitative payment.
No old observation is replaced by either of those later tail samples.
-/
def compare
    (first : Entry primitive firstReading firstRegular firstSample firstAccuracy)
    (last : Entry primitive lastReading lastRegular lastSample lastAccuracy)
    (point_eq : (point site parameter 2 (Waist.direction firstQuarter firstTime) firstPositive).base =
      (point site parameter 2 (Waist.direction lastQuarter lastTime) lastPositive).base)
    (fullSheet : NamedEquivalent firstReading.lift.value.name lastReading.lift.value.name)
    (request : AccuracyRequest) :
    Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation request.tolerance :=
  let firstObservation := first.selected.asObservation
  let lastObservation := last.selected.asObservation
  let agreement := first.equivalent last point_eq fullSheet
  Equivalence.Observation.Comparison.build firstObservation lastObservation agreement request.tolerance request.positive

/-- The two original arithmetic requests and the actual comparison target bound the old primitive values. -/
theorem comparison_error_lt
    (first : Entry primitive firstReading firstRegular firstSample firstAccuracy)
    (last : Entry primitive lastReading lastRegular lastSample lastAccuracy)
    {request : AccuracyRequest}
    (comparison : Equivalence.Observation.Comparison
      first.selected.asObservation last.selected.asObservation request.tolerance) :
    Norm.Basic.normSq (first.value - last.value) <
      16 * ((OddPower.Observation.radiusRequest firstAccuracy).tolerance +
        (OddPower.Observation.radiusRequest lastAccuracy).tolerance) + 4 * request.tolerance := by
  have bound := comparison.residual_le
  rewrite [comparison.residual_eq] at bound
  change Norm.Basic.normSq (first.value - last.value) ≤ comparison.bound at bound
  calc
    _ ≤ comparison.bound := bound
    _ = 16 * (first.selected.asObservation.radius + last.selected.asObservation.radius) +
        4 * request.tolerance := comparison.bound_eq
    _ < _ :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (of_decide_eq_true rfl : (0 : Fraction.Rational) < 16)
          (Fraction.Order.Arithmetic.add_lt_add_direct first.selected.asObservation_radius_lt
            last.selected.asObservation_radius_lt)) _

/-- A shared original arithmetic accuracy pays both old seam values with the finite factor five halves. -/
theorem comparison_error_shared_lt {accuracy : AccuracyRequest}
    (first : Entry primitive firstReading firstRegular firstSample accuracy)
    (last : Entry primitive lastReading lastRegular lastSample accuracy)
    (comparison : Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation
      (OddPower.Observation.comparisonRequest accuracy).tolerance) :
    Norm.Basic.normSq (first.value - last.value) < (5 / 2 : Fraction.Rational) * accuracy.tolerance :=
  (first.comparison_error_lt last (request := OddPower.Observation.comparisonRequest accuracy) comparison).trans_eq
    (OddPower.Observation.Reading.interpretation_budget accuracy)

end Entry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation

end
