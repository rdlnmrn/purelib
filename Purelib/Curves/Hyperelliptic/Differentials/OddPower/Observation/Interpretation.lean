module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
public import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Algebraic interpretation of retained odd-power arithmetic observations

The original numerical reading, state and observation remain unchanged.
The exact square certificate of that same sheet derives agreement with
its retained algebraic denotation. The existing observation comparison
pays the old reading's visible radius, the independently requested
algebraic reading's radius and the actual new comparison target.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Reading

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

variable {radicand : Coefficients} {differential : OddPowerDifferential radicand}
variable {point : Canonical} {sheet : CoherentNamed} {apart : Named.Apart sheet.name}
variable {state : sheet.name.process.State} {rootObservation : RootObservation} {accuracy : AccuracyRequest}

/-- Retain the original arithmetic witness and state in the existing generic observation interface. -/
@[expose] def asObservation (retained : Reading differential point sheet apart state rootObservation accuracy) :
    Equivalence.Observation.Reading retained.coefficient :=
  Equivalence.Observation.Reading.retain retained.coefficient retained.originalState retained.reading
    retained.reading_possible

/-- The unchanged original arithmetic state has its already paid visible radius. -/
theorem asObservation_radius_lt (retained : Reading differential point sheet apart state rootObservation accuracy) :
    retained.asObservation.radius < (radiusRequest accuracy).tolerance := by
  change (retained.coefficient.name.process.ball retained.originalState).radiusSq < _
  rewrite [retained.originalState_eq]
  exact radius_lt retained.coefficient accuracy retained.comparison.left_ge

/-- The original numerical coefficient agrees with a retained denotation on its identical original sheet.

The denotation's original operational square certificate derives the
coefficient-domain guard and the reciprocal-power comparison. Complete
coefficient-cache equality preserves the original arithmetic name.
-/
def equivalent_denotation (retained : Reading differential point sheet apart state rootObservation accuracy)
    (denotation : Expression.Denotation differential.coefficient point sheet) :
    NamedEquivalent retained.coefficient.name denotation.channel.name := by
  have comparison := differential.reciprocal_power_equivalent point sheet denotation.identity apart
  have first : (differential.value point sheet apart).name = retained.coefficient.name :=
    congrArg CoherentNamed.name retained.coefficient_eq.symm
  have last : (differential.interpret point sheet denotation.identity apart).channel.name =
      denotation.channel.name :=
    congrArg CoherentNamed.name
      (((differential.interpret point sheet denotation.identity apart).channel_readback).trans
        denotation.channel_readback.symm)
  exact NamedEquivalent.transport first last comparison

/-- Compare the old arithmetic witness with an independently retained algebraic reading.

The existing comparison retains both observations, both original names,
their actual based views and newly selected tail indices and samples.
Its radius payment concerns the old witness itself, not a substituted
later canonical sample of the original arithmetic process.
-/
def compareDenotation (retained : Reading differential point sheet apart state rootObservation accuracy)
    (denotation : Expression.Denotation differential.coefficient point sheet)
    (observed : Equivalence.Observation.Reading denotation.channel) (request : AccuracyRequest) :
    Equivalence.Observation.Comparison retained.asObservation observed request.tolerance :=
  Equivalence.Observation.Comparison.build retained.asObservation observed
    (retained.equivalent_denotation denotation) request.tolerance request.positive

/-- The original sixteenth-radius and eighth-comparison payments have their exact combined factor. -/
theorem interpretation_budget (request : AccuracyRequest) :
    16 * ((radiusRequest request).tolerance + (radiusRequest request).tolerance) +
        4 * (comparisonRequest request).tolerance = (5 / 2 : Fraction.Rational) * request.tolerance := by
  change 16 * (request.tolerance / 16 + request.tolerance / 16) +
    4 * (request.tolerance / 8) = _
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct]
  calc
    _ = request.tolerance * (16 * ((16 : Fraction.Rational)⁻¹ + 16⁻¹) + 4 * 8⁻¹) := by ring1
    _ = request.tolerance * (5 / 2 : Fraction.Rational) :=
      congrArg (fun scalar : Fraction.Rational => request.tolerance * scalar) (by decide +kernel)
    _ = _ := Fraction.Field.mul_comm _ _

/-- One cached denotation, its independent paid reading and the original observation comparison.

The denotation retains the complete original interpretation factory on
the supplied square certificate. Both new selected comparison samples and
the old actual arithmetic observation remain in existing owned records.
-/
abbrev Interpretation (retained : Reading differential point sheet apart state rootObservation accuracy)
    (identity : PowerIdentity sheet 2 (radicand.eval point)) : Type 1 :=
  (denotation : { original : Expression.Denotation differential.coefficient point sheet //
    original = differential.interpret point sheet identity apart }) ×
  (requested : Equivalence.Observation.Request denotation.val.channel (radiusRequest accuracy).tolerance) ×
  Equivalence.Observation.Comparison retained.asObservation requested.reading (comparisonRequest accuracy).tolerance

/-- Interpret the original sheet and request its algebraic observation without another numerical observation. -/
def requestInterpretation (retained : Reading differential point sheet apart state rootObservation accuracy)
    (identity : PowerIdentity sheet 2 (radicand.eval point)) : Interpretation retained identity :=
  let denotation := differential.interpret point sheet identity apart
  let requested := Equivalence.Observation.Request.build denotation.channel
    (radiusRequest accuracy).tolerance (radiusRequest accuracy).positive
  let comparison := retained.compareDenotation denotation requested.reading (comparisonRequest accuracy)
  ⟨⟨denotation, rfl⟩, requested, comparison⟩

namespace Interpretation

variable {retained : Reading differential point sheet apart state rootObservation accuracy}
variable {identity : PowerIdentity sheet 2 (radicand.eval point)}

/-- Read the one retained original algebraic denotation without reconstructing it. -/
@[expose] def denotation (interpreted : Interpretation retained identity) :
    Expression.Denotation differential.coefficient point sheet := interpreted.1.val

/-- The cached denotation is the complete original interpretation on the supplied square certificate. -/
theorem denotation_eq (interpreted : Interpretation retained identity) :
    interpreted.denotation = differential.interpret point sheet identity apart := interpreted.1.property

/-- Read the independently selected algebraic observation and its original paid request. -/
@[expose] def requested (interpreted : Interpretation retained identity) :
    Equivalence.Observation.Request interpreted.denotation.channel (radiusRequest accuracy).tolerance :=
  interpreted.2.1

/-- Read the existing comparison retaining the old witness and the actual new tail selection. -/
@[expose] def comparison (interpreted : Interpretation retained identity) :
    Equivalence.Observation.Comparison retained.asObservation interpreted.requested.reading
      (comparisonRequest accuracy).tolerance := interpreted.2.2

/-- The old arithmetic witness and actual algebraic reading pay their computed shared finite accuracy.

Both old and new visible radii meet the retained sixteenth request. The
existing observation comparison pays those two radii and its own eighth
target; the resulting factor is derived internally from these actual caches.
-/
theorem error_lt (interpreted : Interpretation retained identity) :
    Norm.Basic.normSq (retained.reading - interpreted.requested.reading.value) <
      (5 / 2 : Fraction.Rational) * accuracy.tolerance := by
  have bound := interpreted.comparison.residual_le
  rewrite [interpreted.comparison.residual_eq] at bound
  change Norm.Basic.normSq (retained.reading - interpreted.requested.reading.value) ≤
    interpreted.comparison.bound at bound
  calc
    _ ≤ interpreted.comparison.bound := bound
    _ = 16 * (retained.asObservation.radius + interpreted.requested.reading.radius) +
        4 * (comparisonRequest accuracy).tolerance := interpreted.comparison.bound_eq
    _ < 16 * ((radiusRequest accuracy).tolerance + (radiusRequest accuracy).tolerance) +
        4 * (comparisonRequest accuracy).tolerance :=
      Fraction.Order.Arithmetic.add_lt_add_right_direct
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide +kernel : (0 : Fraction.Rational) < 16)
          (Fraction.Order.Arithmetic.add_lt_add_direct retained.asObservation_radius_lt
            interpreted.requested.radius_lt)) _
    _ = _ := interpretation_budget accuracy

end Interpretation

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Reading

end
