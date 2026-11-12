module

public import TestPurelib.Curves.Legendre.PeriodVariation.Sampling
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache
import Purelib.Approximation.Gaussian.Process.Sampling

/-! # Actual arithmetic Legendre variation on the retained nonsquare fixture

The existing source and target owners, certificates and paid observations are
reused unchanged. Original arithmetic evaluators retain their own observed
states and witnesses for the two value rows, two first derivative rows and
source second derivative slopes. Their independently paid errors lift both
scalar Taylor banks to actual arithmetic readings.
-/

namespace TestPurelib.Curves.Legendre.PeriodVariation.Arithmetic

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian

/-- Construct the actual arithmetic banks on the exact existing original-root observation fixture. -/
public def observations : Variation.Arithmetic.Observations Sampling.jet :=
  Variation.Arithmetic.request Sampling.jet

-- Assertions consume the retained original observations and their readback
-- laws without executing root or arithmetic sampling inside proof reduction.
attribute [local irreducible] observations

/-- The source value bank is the original evaluator on the same cached source certificate. -/
theorem source_value_owner (coordinate : Fin 2) :
    (observations.sourceValue coordinate).original.coefficient =
      (Specification.valueSpecification Sampling.parameter coordinate).value
        2 Sampling.source.value Sampling.source.apart :=
  (observations.sourceValue coordinate).original.coefficient_eq

/-- The distinct target value bank preserves the original target evaluator and certificate cache. -/
theorem target_value_owner (coordinate : Fin 2) :
    (observations.targetValue coordinate).original.coefficient =
      (Specification.valueSpecification (Sampling.parameter + Sampling.increment) coordinate).value
        2 Sampling.target.value Sampling.target.apart :=
  (observations.targetValue coordinate).original.coefficient_eq

/-- The complete target observation retains the changed family radicand, not merely an equal raw value channel. -/
example (coordinate : Fin 2) :
    let original : OddPower.Observation.Reading
      (Specification.valueSpecification (Sampling.parameter + Sampling.increment) coordinate)
      2 Sampling.target.value Sampling.target.apart Sampling.jet.targetSample.state
      Sampling.jet.targetSample.observation Sampling.jet.accuracy :=
        (observations.targetValue coordinate).original
    original = (observations.targetValue coordinate).original := rfl

/-- The complete source observation retains its distinct original family radicand and original cached states. -/
example (coordinate : Fin 2) :
    let original : OddPower.Observation.Reading
      (Specification.valueSpecification Sampling.parameter coordinate)
      2 Sampling.source.value Sampling.source.apart Sampling.jet.sourceSample.state
      Sampling.jet.sourceSample.observation Sampling.jet.accuracy :=
        (observations.sourceValue coordinate).original
    original = (observations.sourceValue coordinate).original := rfl

/-- Every actual source arithmetic witness is possible at its own retained original evaluator state. -/
theorem source_value_possible (coordinate : Fin 2) :
    (observations.sourceValue coordinate).original.coefficient.name.process.Possible
      (observations.sourceValue coordinate).original.originalState (observations.sourceValue coordinate).reading :=
  (observations.sourceValue coordinate).original.reading_possible

/-- The target arithmetic witness retains its independently selected original process state. -/
theorem target_value_possible (coordinate : Fin 2) :
    (observations.targetValue coordinate).original.coefficient.name.process.Possible
      (observations.targetValue coordinate).original.originalState (observations.targetValue coordinate).reading :=
  (observations.targetValue coordinate).original.reading_possible

/-- The actual first derivative bank retains the original cubic reciprocal arithmetic evaluator. -/
theorem source_first_owner (coordinate : Fin 2) :
    (observations.sourceFirst coordinate).original.coefficient =
      (Specification.firstDerivativeSpecification Sampling.parameter coordinate).value
        2 Sampling.source.value Sampling.source.apart :=
  (observations.sourceFirst coordinate).original.coefficient_eq

/-- The actual slope of the first variation comes from the original fifth-power arithmetic evaluator. -/
theorem source_second_owner (coordinate : Fin 2) :
    (observations.sourceSecond coordinate).original.coefficient =
      (Specification.secondDerivativeSpecification Sampling.parameter coordinate).value
        2 Sampling.source.value Sampling.source.apart :=
  (observations.sourceSecond coordinate).original.coefficient_eq

/-- The original-start state belongs to the arithmetic comparison's actual selected index. -/
theorem selected_original_state (coordinate : Fin 2) :
    (observations.sourceFirst coordinate).original.originalState = Process.Sampling.stateAt
      (observations.sourceFirst coordinate).original.coefficient.name.process
      (observations.sourceFirst coordinate).original.coefficient.name.state
      (observations.sourceFirst coordinate).original.comparison.leftIndex :=
  (observations.sourceFirst coordinate).original.originalState_eq

/-- The paid-start arithmetic state keeps its own selected index and original starting-state cache. -/
theorem selected_paid_state (coordinate : Fin 2) :
    (observations.sourceFirst coordinate).original.paidState = Process.Sampling.stateAt
      (observations.sourceFirst coordinate).original.coefficient.name.process
      (observations.sourceFirst coordinate).original.paidStart
      (observations.sourceFirst coordinate).original.comparison.rightIndex :=
  (observations.sourceFirst coordinate).original.paidState_eq

/-- The actual source value discrepancy is paid at the original fourth-order increment scale. -/
theorem source_value_paid (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceValue coordinate).reading -
      Variation.valueReading coordinate 2 Sampling.jet.sourceSample.reading) ≤
      OddPower.Observation.Cache.allowanceFactor
        (Specification.valueSpecification Sampling.parameter coordinate) 2 Sampling.source
        Sampling.jet.clearance.sourceFloor *
        Norm.Basic.normSq Sampling.increment ^ 2 :=
  observations.sourceValue_le coordinate

/-- The actual independent cubic-factor first reading pays that same original increment scale. -/
theorem source_first_paid (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceFirst coordinate).reading -
      Variation.firstReading coordinate 2 Sampling.jet.sourceSample.reading) ≤
      OddPower.Observation.Cache.allowanceFactor
        (Specification.firstDerivativeSpecification Sampling.parameter coordinate) 2 Sampling.source
        Sampling.jet.clearance.sourceFloor *
        Norm.Basic.normSq Sampling.increment ^ 2 :=
  observations.sourceFirst_le coordinate

/-- The actual source second derivative pays its independent fifth-power factor budget. -/
theorem source_second_paid (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceSecond coordinate).reading -
      Variation.secondReading coordinate 2 Sampling.jet.sourceSample.reading) ≤
      OddPower.Observation.Cache.allowanceFactor
        (Specification.secondDerivativeSpecification Sampling.parameter coordinate) 2 Sampling.source
        Sampling.jet.clearance.sourceFloor *
        Norm.Basic.normSq Sampling.increment ^ 2 :=
  observations.sourceSecond_le coordinate

/-- The value certificate retains the actual source arithmetic base. -/
theorem value_base (coordinate : Fin 2) :
    (observations.valueCertificate coordinate).base = (observations.sourceValue coordinate).reading :=
  observations.valueCertificate_base coordinate

/-- The value certificate retains the actual target arithmetic output. -/
theorem value_output (coordinate : Fin 2) :
    (observations.valueCertificate coordinate).output = (observations.targetValue coordinate).reading :=
  observations.valueCertificate_output coordinate

/-- The value variation uses the actual original source first derivative as its slope. -/
theorem value_slope (coordinate : Fin 2) :
    (observations.valueCertificate coordinate).slope = (observations.sourceFirst coordinate).reading :=
  observations.valueCertificate_slope coordinate

/-- The first variation uses the independently observed original source second derivative as its slope. -/
theorem first_slope (coordinate : Fin 2) :
    (observations.firstCertificate coordinate).slope = (observations.sourceSecond coordinate).reading :=
  observations.firstCertificate_slope coordinate

/-- Both actual value rows satisfy their internally constructed finite Taylor remainder inequalities. -/
theorem value_remainder (coordinate : Fin 2) :
    Gaussian.Basic.Canonical.normSq ((observations.targetValue coordinate).reading -
      (observations.sourceValue coordinate).reading - Sampling.increment *
        (observations.sourceFirst coordinate).reading) ≤
      (observations.valueCertificate coordinate).factor * Gaussian.Basic.Canonical.normSq Sampling.increment ^ 2 := by
  have bound := (observations.valueCertificate coordinate).remainder_le
  rewrite [← (observations.valueCertificate coordinate).expansion,
    observations.valueCertificate_base coordinate, observations.valueCertificate_output coordinate,
    observations.valueCertificate_slope coordinate] at bound
  exact bound

/-- Both first derivative rows satisfy finite bounds with their actual second derivative arithmetic slopes. -/
theorem first_remainder (coordinate : Fin 2) :
    Gaussian.Basic.Canonical.normSq ((observations.targetFirst coordinate).reading -
      (observations.sourceFirst coordinate).reading - Sampling.increment *
        (observations.sourceSecond coordinate).reading) ≤
      (observations.firstCertificate coordinate).factor * Gaussian.Basic.Canonical.normSq Sampling.increment ^ 2 := by
  have bound := (observations.firstCertificate coordinate).remainder_le
  rewrite [← (observations.firstCertificate coordinate).expansion,
    observations.firstCertificate_base coordinate, observations.firstCertificate_output coordinate,
    observations.firstCertificate_slope coordinate] at bound
  exact bound

end TestPurelib.Curves.Legendre.PeriodVariation.Arithmetic
