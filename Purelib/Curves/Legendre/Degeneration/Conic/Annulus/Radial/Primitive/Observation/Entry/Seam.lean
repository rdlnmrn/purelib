module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry.Comparison
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Fin
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Comparison
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Paid oriented primitive observation seams of the original circuit

The two supplied endpoint Readings need not be the Circuit's own endpoint
queries. Each retains its original complete cubic and cofactor owners.
Same-quarter comparisons connect those two old queries to the Circuit's
stored full cubic seams. The exact oriented physical join
then transports the retained primitive coefficient denotations and pays the
two independent original arithmetic observations.

This finite seam comparison asserts no equality of their selected values,
primitive integral endpoint law or canonical cycle attachment.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

section Payment

variable {site : Fin 2} {parameter : Canonical} {firstQuarter lastQuarter : UnitCircuitQuarter}
variable {firstPositive lastPositive : (0 : Fraction.Rational) < 2}
variable {firstActual : Transport.Quarter site parameter 2 firstQuarter firstPositive}
variable {lastActual : Transport.Quarter site parameter 2 lastQuarter lastPositive}
variable {firstTime lastTime : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside firstTime} {lastInside : FixedRootBoxPath.Inside lastTime}
variable {firstReading : Transport.Reading firstActual firstTime firstInside}
variable {lastReading : Transport.Reading lastActual lastTime lastInside}
variable {firstRegular lastRegular : parameter ≠ criticalValue site}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {firstRootAccuracy lastRootAccuracy accuracy : AccuracyRequest}
variable {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
variable {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}

/-- One original observation Comparison retains its exact completed factory and the internally paid old-value bound. -/
abbrev Payment (first : Entry primitive firstReading firstRegular firstSample accuracy)
    (last : Entry primitive lastReading lastRegular lastSample accuracy)
    (factory : Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation
      (OddPower.Observation.comparisonRequest accuracy).tolerance) :=
  { comparison : Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation
      (OddPower.Observation.comparisonRequest accuracy).tolerance //
    comparison = factory ∧
      Norm.Basic.normSq (first.value - last.value) < (5 / 2 : Fraction.Rational) * accuracy.tolerance }

namespace Payment

variable {first : Entry primitive firstReading firstRegular firstSample accuracy}
variable {last : Entry primitive lastReading lastRegular lastSample accuracy}
variable {factory : Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation
  (OddPower.Observation.comparisonRequest accuracy).tolerance}

/-- The actual stored comparison residual obeys the payment on the same two old selected values. -/
theorem residual_lt (paid : Payment first last factory) :
    Norm.Basic.normSq paid.val.residual < (5 / 2 : Fraction.Rational) * accuracy.tolerance := by
  rewrite [paid.val.residual_eq]
  exact paid.property.2

end Payment

end Payment

namespace LegSeam

variable {site : Fin 2} {parameter : Canonical} {previousQuarter nextQuarter : UnitCircuitQuarter}
variable {firstInside : FixedRootBoxPath.Inside 1} {lastInside : FixedRootBoxPath.Inside 0}

/-- An exact oriented direction join preserves the actual scale-two physical base. -/
theorem point_eq (site : Fin 2) (parameter : Canonical)
    (directions : Waist.direction previousQuarter 1 = Waist.direction nextQuarter 0) :
    (point site parameter 2 (Waist.direction previousQuarter 1) (of_decide_eq_true rfl)).base =
      (point site parameter 2 (Waist.direction nextQuarter 0) (of_decide_eq_true rfl)).base :=
  congrArg (fun direction => (point site parameter 2 direction (of_decide_eq_true rfl)).base) directions

/-- Compare old endpoint queries through an existing full-cubic seam of their original retained Legs.

Both local comparisons retain the supplied query and the Leg's distinct
stored query. The middle witness is the supplied original signed cubic
Seam, so this construction does not infer full-sheet closure from a
normalized root trace or from the equality of physical coordinates.
-/
def fullSheet (previous : Transport.Leg site parameter previousQuarter)
    (next : Transport.Leg site parameter nextQuarter) (seam : Transport.Seam previous next)
    (firstReading : Transport.Reading previous.actual 1 firstInside)
    (lastReading : Transport.Reading next.actual 0 lastInside) :
    NamedEquivalent firstReading.lift.value.name lastReading.lift.value.name := by
  have firstLocal := firstReading.agrees_of_base_eq previous.target previous.regular rfl
  have lastLocal := next.source.agrees_of_base_eq lastReading next.regular rfl
  unfold Transport.Seam at seam
  exact firstLocal.trans (seam.trans lastLocal)

variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {firstRootAccuracy lastRootAccuracy firstAccuracy lastAccuracy : AccuracyRequest}

/-- Pay arbitrary old primitive endpoint observations using the actual retained-Leg seam and direction join. -/
def compare (previous : Transport.Leg site parameter previousQuarter)
    (next : Transport.Leg site parameter nextQuarter)
    (directions : Waist.direction previousQuarter 1 = Waist.direction nextQuarter 0)
    (seam : Transport.Seam previous next)
    {firstReading : Transport.Reading previous.actual 1 firstInside}
    {lastReading : Transport.Reading next.actual 0 lastInside}
    {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
    {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}
    (first : Entry primitive firstReading previous.regular firstSample firstAccuracy)
    (last : Entry primitive lastReading next.regular lastSample lastAccuracy)
    (request : AccuracyRequest) :
    Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation request.tolerance :=
  Entry.compare first last (point_eq site parameter directions) (fullSheet previous next seam firstReading lastReading)
    request

end LegSeam

namespace FirstSecond

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter}
variable {firstInside : FixedRootBoxPath.Inside 1} {lastInside : FixedRootBoxPath.Inside 0}

/-- The original oriented first and second radial quarters have the same physical base at their actual seam. -/
theorem point_eq (site : Fin 2) (parameter : Canonical) :
    (point site parameter 2 (Waist.direction .first 1) (of_decide_eq_true rfl)).base =
      (point site parameter 2 (Waist.direction .second 0) (of_decide_eq_true rfl)).base :=
  congrArg (fun direction => (point site parameter 2 direction (of_decide_eq_true rfl)).base)
    Waist.directions_join.1

/-- Compare two original endpoint query owners through the Circuit's actual retained full cubic seam.

Each same-quarter comparison consumes the supplied original query and the
Circuit's separate stored query, including their actual cofactor Owners.
The middle witness is the existing signed full cubic seam; normalized trace
closure alone is not used to infer a full cubic sheet comparison.
-/
def fullSheet (circuit : Transport.Circuit site parameter)
    (firstReading : Transport.Reading circuit.first.actual 1 firstInside)
    (lastReading : Transport.Reading circuit.second.actual 0 lastInside) :
    NamedEquivalent firstReading.lift.value.name lastReading.lift.value.name := by
  exact LegSeam.fullSheet circuit.first circuit.second circuit.first_second firstReading lastReading

variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {firstReading : Transport.Reading circuit.first.actual 1 firstInside}
variable {lastReading : Transport.Reading circuit.second.actual 0 lastInside}
variable {firstRootAccuracy lastRootAccuracy firstAccuracy lastAccuracy : AccuracyRequest}
variable {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
variable {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}

/-- Pay the two original first-to-second primitive observations without querying either endpoint again.

The exact endpoint cache, root observation, independent arithmetic request
and selected arithmetic state remain those supplied by each Entry. The
returned original Comparison retains both old observation radii and its
actual finite tail comparison on the derived original evaluator agreement.
-/
def compare (circuit : Transport.Circuit site parameter)
    {firstReading : Transport.Reading circuit.first.actual 1 firstInside}
    {lastReading : Transport.Reading circuit.second.actual 0 lastInside}
    {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
    {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}
    (first : Entry primitive firstReading circuit.first.regular firstSample firstAccuracy)
    (last : Entry primitive lastReading circuit.second.regular lastSample lastAccuracy)
    (request : AccuracyRequest) :
    Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation request.tolerance :=
  Entry.compare first last (point_eq site parameter) (fullSheet circuit firstReading lastReading) request

/-- Cache one actual seam comparison and its internally derived five-halves payment on the two old values.

The common original arithmetic request computes the tail request. Both
old selected observations remain inputs of the returned original Comparison;
its actual residual payment and the two original radius laws prove the
displayed bound without a caller-supplied sample inequality.
-/
@[expose] def shared {accuracy : AccuracyRequest}
    (first : Entry primitive firstReading circuit.first.regular firstSample accuracy)
    (last : Entry primitive lastReading circuit.second.regular lastSample accuracy) :
    { comparison : Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation
        (OddPower.Observation.comparisonRequest accuracy).tolerance //
      comparison = compare circuit first last (OddPower.Observation.comparisonRequest accuracy) ∧
        Norm.Basic.normSq (first.value - last.value) < (5 / 2 : Fraction.Rational) * accuracy.tolerance } :=
  let comparison := compare circuit first last (OddPower.Observation.comparisonRequest accuracy)
  ⟨comparison, rfl, first.comparison_error_shared_lt last comparison⟩

end FirstSecond

namespace SecondThird

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstInside : FixedRootBoxPath.Inside 1} {lastInside : FixedRootBoxPath.Inside 0}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {firstRootAccuracy lastRootAccuracy firstAccuracy lastAccuracy : AccuracyRequest}

/-- Pay the original second-to-third endpoint observations through their actual oriented full-cubic seam. -/
def compare (circuit : Transport.Circuit site parameter)
    {firstReading : Transport.Reading circuit.second.actual 1 firstInside}
    {lastReading : Transport.Reading circuit.third.actual 0 lastInside}
    {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
    {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}
    (first : Entry primitive firstReading circuit.second.regular firstSample firstAccuracy)
    (last : Entry primitive lastReading circuit.third.regular lastSample lastAccuracy)
    (request : AccuracyRequest) :
    Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation request.tolerance :=
  LegSeam.compare circuit.second circuit.third Waist.directions_join.2.1 circuit.second_third
    first last request

variable {firstReading : Transport.Reading circuit.second.actual 1 firstInside}
variable {lastReading : Transport.Reading circuit.third.actual 0 lastInside}
variable {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
variable {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}

/-- Retain one actual second-to-third comparison and derive its five-halves old-value bound internally. -/
@[expose] def shared {accuracy : AccuracyRequest}
    (first : Entry primitive firstReading circuit.second.regular firstSample accuracy)
    (last : Entry primitive lastReading circuit.third.regular lastSample accuracy) :
    { comparison : Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation
        (OddPower.Observation.comparisonRequest accuracy).tolerance //
      comparison = compare circuit first last (OddPower.Observation.comparisonRequest accuracy) ∧
        Norm.Basic.normSq (first.value - last.value) < (5 / 2 : Fraction.Rational) * accuracy.tolerance } :=
  let comparison := compare circuit first last (OddPower.Observation.comparisonRequest accuracy)
  ⟨comparison, rfl, first.comparison_error_shared_lt last comparison⟩

end SecondThird

namespace ThirdFourth

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstInside : FixedRootBoxPath.Inside 1} {lastInside : FixedRootBoxPath.Inside 0}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {firstRootAccuracy lastRootAccuracy firstAccuracy lastAccuracy : AccuracyRequest}

/-- Pay the original third-to-fourth endpoint observations through their actual oriented full-cubic seam. -/
def compare (circuit : Transport.Circuit site parameter)
    {firstReading : Transport.Reading circuit.third.actual 1 firstInside}
    {lastReading : Transport.Reading circuit.fourth.actual 0 lastInside}
    {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
    {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}
    (first : Entry primitive firstReading circuit.third.regular firstSample firstAccuracy)
    (last : Entry primitive lastReading circuit.fourth.regular lastSample lastAccuracy)
    (request : AccuracyRequest) :
    Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation request.tolerance :=
  LegSeam.compare circuit.third circuit.fourth Waist.directions_join.2.2.1 circuit.third_fourth
    first last request

variable {firstReading : Transport.Reading circuit.third.actual 1 firstInside}
variable {lastReading : Transport.Reading circuit.fourth.actual 0 lastInside}
variable {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
variable {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}

/-- Retain one actual third-to-fourth comparison and derive its five-halves old-value bound internally. -/
@[expose] def shared {accuracy : AccuracyRequest}
    (first : Entry primitive firstReading circuit.third.regular firstSample accuracy)
    (last : Entry primitive lastReading circuit.fourth.regular lastSample accuracy) :
    { comparison : Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation
        (OddPower.Observation.comparisonRequest accuracy).tolerance //
      comparison = compare circuit first last (OddPower.Observation.comparisonRequest accuracy) ∧
        Norm.Basic.normSq (first.value - last.value) < (5 / 2 : Fraction.Rational) * accuracy.tolerance } :=
  let comparison := compare circuit first last (OddPower.Observation.comparisonRequest accuracy)
  ⟨comparison, rfl, first.comparison_error_shared_lt last comparison⟩

end ThirdFourth

namespace FourthFirst

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstInside : FixedRootBoxPath.Inside 1} {lastInside : FixedRootBoxPath.Inside 0}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {firstRootAccuracy lastRootAccuracy firstAccuracy lastAccuracy : AccuracyRequest}

/-- Pay the original fourth-to-first endpoint observations through their actual oriented full-cubic seam. -/
def compare (circuit : Transport.Circuit site parameter)
    {firstReading : Transport.Reading circuit.fourth.actual 1 firstInside}
    {lastReading : Transport.Reading circuit.first.actual 0 lastInside}
    {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
    {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}
    (first : Entry primitive firstReading circuit.fourth.regular firstSample firstAccuracy)
    (last : Entry primitive lastReading circuit.first.regular lastSample lastAccuracy)
    (request : AccuracyRequest) :
    Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation request.tolerance :=
  LegSeam.compare circuit.fourth circuit.first Waist.directions_join.2.2.2 circuit.fourth_first
    first last request

variable {firstReading : Transport.Reading circuit.fourth.actual 1 firstInside}
variable {lastReading : Transport.Reading circuit.first.actual 0 lastInside}
variable {firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot firstRootAccuracy}
variable {lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot lastRootAccuracy}

/-- Retain one actual fourth-to-first comparison and derive its five-halves old-value bound internally. -/
@[expose] def shared {accuracy : AccuracyRequest}
    (first : Entry primitive firstReading circuit.fourth.regular firstSample accuracy)
    (last : Entry primitive lastReading circuit.first.regular lastSample accuracy) :
    { comparison : Equivalence.Observation.Comparison first.selected.asObservation last.selected.asObservation
        (OddPower.Observation.comparisonRequest accuracy).tolerance //
      comparison = compare circuit first last (OddPower.Observation.comparisonRequest accuracy) ∧
        Norm.Basic.normSq (first.value - last.value) < (5 / 2 : Fraction.Rational) * accuracy.tolerance } :=
  let comparison := compare circuit first last (OddPower.Observation.comparisonRequest accuracy)
  ⟨comparison, rfl, first.comparison_error_shared_lt last comparison⟩

end FourthFirst

namespace Circuit

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {zeroInside : FixedRootBoxPath.Inside 0} {oneInside : FixedRootBoxPath.Inside 1}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)} {accuracy : AccuracyRequest}
variable {firstStartReading : Transport.Reading circuit.first.actual 0 zeroInside}
variable {firstStartRootAccuracy : AccuracyRequest}
variable {firstStartSample : CertifiedSquareRoot.Sampling.ResidualObservation
  firstStartReading.lift.unitRoot firstStartRootAccuracy}
variable {firstFinishReading : Transport.Reading circuit.first.actual 1 oneInside}
variable {firstFinishRootAccuracy : AccuracyRequest}
variable {firstFinishSample : CertifiedSquareRoot.Sampling.ResidualObservation
  firstFinishReading.lift.unitRoot firstFinishRootAccuracy}
variable {secondStartReading : Transport.Reading circuit.second.actual 0 zeroInside}
variable {secondStartRootAccuracy : AccuracyRequest}
variable {secondStartSample : CertifiedSquareRoot.Sampling.ResidualObservation
  secondStartReading.lift.unitRoot secondStartRootAccuracy}
variable {secondFinishReading : Transport.Reading circuit.second.actual 1 oneInside}
variable {secondFinishRootAccuracy : AccuracyRequest}
variable {secondFinishSample : CertifiedSquareRoot.Sampling.ResidualObservation
  secondFinishReading.lift.unitRoot secondFinishRootAccuracy}
variable {thirdStartReading : Transport.Reading circuit.third.actual 0 zeroInside}
variable {thirdStartRootAccuracy : AccuracyRequest}
variable {thirdStartSample : CertifiedSquareRoot.Sampling.ResidualObservation
  thirdStartReading.lift.unitRoot thirdStartRootAccuracy}
variable {thirdFinishReading : Transport.Reading circuit.third.actual 1 oneInside}
variable {thirdFinishRootAccuracy : AccuracyRequest}
variable {thirdFinishSample : CertifiedSquareRoot.Sampling.ResidualObservation
  thirdFinishReading.lift.unitRoot thirdFinishRootAccuracy}
variable {fourthStartReading : Transport.Reading circuit.fourth.actual 0 zeroInside}
variable {fourthStartRootAccuracy : AccuracyRequest}
variable {fourthStartSample : CertifiedSquareRoot.Sampling.ResidualObservation
  fourthStartReading.lift.unitRoot fourthStartRootAccuracy}
variable {fourthFinishReading : Transport.Reading circuit.fourth.actual 1 oneInside}
variable {fourthFinishRootAccuracy : AccuracyRequest}
variable {fourthFinishSample : CertifiedSquareRoot.Sampling.ResidualObservation
  fourthFinishReading.lift.unitRoot fourthFinishRootAccuracy}

/-- Four actual seam Comparison caches retain their original observations and exact concrete oriented factories.

Every supplied Entry remains an index, including each independent original
root observation and the common original arithmetic accuracy request. This
product stores original Comparison owners, not copies of their fields.
-/
abbrev Comparison
    (firstStart : Entry primitive firstStartReading circuit.first.regular firstStartSample accuracy)
    (firstFinish : Entry primitive firstFinishReading circuit.first.regular firstFinishSample accuracy)
    (secondStart : Entry primitive secondStartReading circuit.second.regular secondStartSample accuracy)
    (secondFinish : Entry primitive secondFinishReading circuit.second.regular secondFinishSample accuracy)
    (thirdStart : Entry primitive thirdStartReading circuit.third.regular thirdStartSample accuracy)
    (thirdFinish : Entry primitive thirdFinishReading circuit.third.regular thirdFinishSample accuracy)
    (fourthStart : Entry primitive fourthStartReading circuit.fourth.regular fourthStartSample accuracy)
    (fourthFinish : Entry primitive fourthFinishReading circuit.fourth.regular fourthFinishSample accuracy) :=
  Payment firstFinish secondStart
    (FirstSecond.compare circuit firstFinish secondStart (OddPower.Observation.comparisonRequest accuracy)) ×
  Payment secondFinish thirdStart
    (SecondThird.compare circuit secondFinish thirdStart (OddPower.Observation.comparisonRequest accuracy)) ×
  Payment thirdFinish fourthStart
    (ThirdFourth.compare circuit thirdFinish fourthStart (OddPower.Observation.comparisonRequest accuracy)) ×
  Payment fourthFinish firstStart
    (FourthFirst.compare circuit fourthFinish firstStart (OddPower.Observation.comparisonRequest accuracy))

/-- Construct all four actual old-observation seam comparisons once from the original signed circuit evidence. -/
def build
    (firstStart : Entry primitive firstStartReading circuit.first.regular firstStartSample accuracy)
    (firstFinish : Entry primitive firstFinishReading circuit.first.regular firstFinishSample accuracy)
    (secondStart : Entry primitive secondStartReading circuit.second.regular secondStartSample accuracy)
    (secondFinish : Entry primitive secondFinishReading circuit.second.regular secondFinishSample accuracy)
    (thirdStart : Entry primitive thirdStartReading circuit.third.regular thirdStartSample accuracy)
    (thirdFinish : Entry primitive thirdFinishReading circuit.third.regular thirdFinishSample accuracy)
    (fourthStart : Entry primitive fourthStartReading circuit.fourth.regular fourthStartSample accuracy)
    (fourthFinish : Entry primitive fourthFinishReading circuit.fourth.regular fourthFinishSample accuracy) :
    Comparison firstStart firstFinish secondStart secondFinish thirdStart thirdFinish fourthStart fourthFinish :=
  ⟨FirstSecond.shared (circuit := circuit) firstFinish secondStart,
    ⟨SecondThird.shared (circuit := circuit) secondFinish thirdStart,
      ⟨ThirdFourth.shared (circuit := circuit) thirdFinish fourthStart,
        FourthFirst.shared (circuit := circuit) fourthFinish firstStart⟩⟩⟩

namespace Comparison

variable {firstStart : Entry primitive firstStartReading circuit.first.regular firstStartSample accuracy}
variable {firstFinish : Entry primitive firstFinishReading circuit.first.regular firstFinishSample accuracy}
variable {secondStart : Entry primitive secondStartReading circuit.second.regular secondStartSample accuracy}
variable {secondFinish : Entry primitive secondFinishReading circuit.second.regular secondFinishSample accuracy}
variable {thirdStart : Entry primitive thirdStartReading circuit.third.regular thirdStartSample accuracy}
variable {thirdFinish : Entry primitive thirdFinishReading circuit.third.regular thirdFinishSample accuracy}
variable {fourthStart : Entry primitive fourthStartReading circuit.fourth.regular fourthStartSample accuracy}
variable {fourthFinish : Entry primitive fourthFinishReading circuit.fourth.regular fourthFinishSample accuracy}

/-- Read the complete original first-to-second comparison and its factory/payment witness. -/
@[expose] def first_second (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish) :
    Payment firstFinish secondStart
      (FirstSecond.compare circuit firstFinish secondStart (OddPower.Observation.comparisonRequest accuracy)) :=
  compared.1

/-- Read the complete original second-to-third comparison and its factory/payment witness. -/
@[expose] def second_third (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish) :
    Payment secondFinish thirdStart
      (SecondThird.compare circuit secondFinish thirdStart (OddPower.Observation.comparisonRequest accuracy)) :=
  compared.2.1

/-- Read the complete original third-to-fourth comparison and its factory/payment witness. -/
@[expose] def third_fourth (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish) :
    Payment thirdFinish fourthStart
      (ThirdFourth.compare circuit thirdFinish fourthStart (OddPower.Observation.comparisonRequest accuracy)) :=
  compared.2.2.1

/-- Read the complete original fourth-to-first comparison and its factory/payment witness. -/
@[expose] def fourth_first (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish) :
    Payment fourthFinish firstStart
      (FourthFirst.compare circuit fourthFinish firstStart (OddPower.Observation.comparisonRequest accuracy)) :=
  compared.2.2.2

/-- The four actual stored old-value residuals retain the original cyclic seam order. -/
@[expose] def residuals (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish) :
    Fin 4 → Canonical :=
  Data.Fin.cases compared.first_second.val.residual
    (Data.Fin.cases compared.second_third.val.residual
      (Data.Fin.cases compared.third_fourth.val.residual
        (fun _ : Fin 1 => compared.fourth_first.val.residual)))

/-- Each actual stored comparison residual has its internally derived common five-halves old-value payment. -/
theorem residual_lt (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish)
    (index : Fin 4) :
    Norm.Basic.normSq (compared.residuals index) < (5 / 2 : Fraction.Rational) * accuracy.tolerance := by
  refine Data.Fin.cases_induction ?_ (fun remaining => ?_) index
  · exact Payment.residual_lt compared.first_second
  · refine Data.Fin.cases_induction ?_ (fun remaining => ?_) remaining
    · exact Payment.residual_lt compared.second_third
    · refine Data.Fin.cases_induction ?_ (fun _remaining => ?_) remaining
      · exact Payment.residual_lt compared.third_fourth
      · exact Payment.residual_lt compared.fourth_first

/-- Sum the four original stored seam residuals in their actual oriented cyclic order. -/
@[expose] def sum (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish) :
    Canonical := FiniteSum.Fin.sumFin compared.residuals

/-- The four retained seam residuals sum to the same four forward quarter boundary differences.

This is a finite scalar identity of the eight OLD input values. It does not
identify observations across a seam or assert an integral endpoint theorem.
-/
theorem sum_eq_boundary (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish) :
    compared.sum =
      (firstFinish.value - firstStart.value) + (secondFinish.value - secondStart.value) +
        (thirdFinish.value - thirdStart.value) + (fourthFinish.value - fourthStart.value) := by
  unfold sum
  rewrite [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
  change compared.first_second.val.residual + (compared.second_third.val.residual +
    (compared.third_fourth.val.residual + (compared.fourth_first.val.residual + 0))) = _
  rewrite [compared.first_second.val.residual_eq, compared.second_third.val.residual_eq,
    compared.third_fourth.val.residual_eq, compared.fourth_first.val.residual_eq]
  change (firstFinish.value - secondStart.value) + ((secondFinish.value - thirdStart.value) +
    ((thirdFinish.value - fourthStart.value) + ((fourthFinish.value - firstStart.value) + 0))) = _
  ring1

/-- The four actual stored seam comparisons pay their aggregate squared error by forty common tolerances.

The original indexed finite-sum norm bound consumes the four individually
derived comparison payments. Neither the aggregate inequality nor any
individual sample inequality is supplied as a constructor input.
-/
theorem error_le (compared : Comparison firstStart firstFinish secondStart secondFinish
    thirdStart thirdFinish fourthStart fourthFinish) :
    Norm.Basic.normSq compared.sum ≤ 40 * accuracy.tolerance := by
  have bound := Norm.Sum.Indexed.normSq_sumFin_le compared.residuals
    ((5 / 2 : Fraction.Rational) * accuracy.tolerance) (fun index => (compared.residual_lt index).le)
  change Norm.Basic.normSq compared.sum ≤
    (4 : Fraction.Rational) ^ 2 * ((5 / 2 : Fraction.Rational) * accuracy.tolerance) at bound
  have scalar : (4 : Fraction.Rational) ^ 2 * (5 / 2 : Fraction.Rational) = 40 := by
    decide +kernel
  calc
    _ ≤ (4 : Fraction.Rational) ^ 2 * ((5 / 2 : Fraction.Rational) * accuracy.tolerance) := bound
    _ = ((4 : Fraction.Rational) ^ 2 * (5 / 2 : Fraction.Rational)) * accuracy.tolerance := by ring1
    _ = _ := congrArg (fun coefficient : Fraction.Rational => coefficient * accuracy.tolerance) scalar

end Comparison

end Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry

end
