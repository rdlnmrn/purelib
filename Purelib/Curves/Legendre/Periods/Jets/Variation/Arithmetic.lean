module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Bounds
public import Purelib.Calculus.Jet.Quadratic.Perturbation
public import Purelib.Data.Fin
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Actual arithmetic observations of the two retained Legendre coefficient banks

Every observation uses the original value or first derivative specification,
the original cached sheet channel, and the actual selected root-process
observation. The original arithmetic evaluator refines its own occurrences
independently. Existing rebase comparisons and finite spread bounds pay their
differences from the scalar Taylor witnesses.

The request constructor computes all ten arithmetic observations once and
stores their two-entry banks, including the source second derivative slopes.
It does not repeat root sampling or replace an
arithmetic reading by its scalar anchor. Spatial coordinates remain fixed
across the parameter increment; lifted-cycle integration is a separate step.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic

open Purelib.Calculus.Jet.Quadratic.Basic (Certificate)

open Purelib
open Purelib.Approximation
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation

/-- The two original value-differential observations retain their evaluator caches and actual observation floor. -/
abbrev ValueReadings {radicand : Canonical} {accuracy : AccuracyRequest} (parameter : Canonical)
    (root : CertifiedSquareRoot.Certificate radicand)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy) (point : Canonical)
    (floor : Fraction.Rational) : Type 1 :=
  (coordinate : Fin 2) → Cache.Reading (Specification.valueSpecification parameter coordinate)
    point root.value root.apart sample.state sample.observation accuracy
    ((Specification.valueSpecification parameter coordinate).value point root.value root.apart) floor

/-- The two original first derivative observations retain their evaluator caches and actual observation floor. -/
abbrev FirstReadings {radicand : Canonical} {accuracy : AccuracyRequest} (parameter : Canonical)
    (root : CertifiedSquareRoot.Certificate radicand)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy) (point : Canonical)
    (floor : Fraction.Rational) : Type 1 :=
  (coordinate : Fin 2) → Cache.Reading (Specification.firstDerivativeSpecification parameter coordinate)
    point root.value root.apart sample.state sample.observation accuracy
    ((Specification.firstDerivativeSpecification parameter coordinate).value point root.value root.apart) floor

/-- The two original second derivative observations retain their evaluator caches and actual observation floor. -/
abbrev SecondReadings {radicand : Canonical} {accuracy : AccuracyRequest} (parameter : Canonical)
    (root : CertifiedSquareRoot.Certificate radicand)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation root accuracy) (point : Canonical)
    (floor : Fraction.Rational) : Type 1 :=
  (coordinate : Fin 2) → Cache.Reading (Specification.secondDerivativeSpecification parameter coordinate)
    point root.value root.apart sample.state sample.observation accuracy
    ((Specification.secondDerivativeSpecification parameter coordinate).value point root.value root.apart) floor

/-- The generic scalar anchor of an original value observation is the original Legendre value coefficient. -/
theorem value_scalar_eq (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (observation : OddPower.Observation.RootObservation) :
    OddPower.Observation.scalarReading (Specification.valueSpecification parameter coordinate) point observation =
      Variation.valueReading coordinate point observation.witness := by
  unfold OddPower.Observation.scalarReading
    OddPower.Basic.OddPowerDifferential.denominatorExponent
  rewrite [Specification.valueSpecification_denominatorPairs parameter coordinate]
  rewrite [pow_one]
  exact (Variation.valueReading_specification parameter coordinate point observation.witness).symm

/-- The generic scalar anchor of an original first observation is the original Legendre first derivative coefficient. -/
theorem first_scalar_eq (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (observation : OddPower.Observation.RootObservation) :
    OddPower.Observation.scalarReading (Specification.firstDerivativeSpecification parameter coordinate)
      point observation =
      Variation.firstReading coordinate point observation.witness := by
  have pairs : (Specification.firstDerivativeSpecification parameter coordinate).denominatorPairs = 1 := rfl
  unfold OddPower.Observation.scalarReading
    OddPower.Basic.OddPowerDifferential.denominatorExponent
  rewrite [pairs]
  exact (Variation.firstReading_specification parameter coordinate point observation.witness).symm

/-- The scalar anchor of the original second observation is the original Legendre second derivative coefficient. -/
theorem second_scalar_eq (parameter : Canonical) (coordinate : Fin 2) (point : Canonical)
    (observation : OddPower.Observation.RootObservation) :
    OddPower.Observation.scalarReading (Specification.secondDerivativeSpecification parameter coordinate)
      point observation =
      Variation.secondReading coordinate point observation.witness := by
  have pairs : (Specification.secondDerivativeSpecification parameter coordinate).denominatorPairs = 2 := rfl
  unfold OddPower.Observation.scalarReading
    OddPower.Basic.OddPowerDifferential.denominatorExponent
  rewrite [pairs]
  exact (Variation.secondReading_specification parameter coordinate point observation.witness).symm

set_option genInjectivity false in
/-- Both actual original coefficient banks on the two original paid root observations.

The source and target certificates remain indexed by the same displayed
spatial point. Each original arithmetic observation retains its actual process,
independent selected states, witnesses and comparison payment.
-/
structure Observations {parameter increment point : Canonical}
    {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
    {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
    {unit : Norm.Basic.normSq increment ≤ 1}
    (jet : Sampling.SampledJet parameter increment point source target unit) where
  /-- The retained source value-differential observations. -/
  sourceValue : ValueReadings parameter source jet.sourceSample point
    jet.clearance.sourceFloor
  /-- The retained target value-differential observations. -/
  targetValue : ValueReadings (parameter + increment) target jet.targetSample point
    jet.clearance.targetFloor
  /-- The retained source first derivative observations. -/
  sourceFirst : FirstReadings parameter source jet.sourceSample point
    jet.clearance.sourceFloor
  /-- The retained target first derivative observations. -/
  targetFirst : FirstReadings (parameter + increment) target jet.targetSample point
    jet.clearance.targetFloor
  /-- The original source second derivative observations used by the actual first variation slopes. -/ sourceSecond :
    SecondReadings parameter source jet.sourceSample point jet.clearance.sourceFloor

constructive_injectivity Observations

/-- Request all ten original arithmetic observations once and store their exact two-entry banks.

Each entry uses its actual cached source or target root observation and that
observation's complete process equality. All entries pay the same original
fourth-order residual accuracy as a free arithmetic comparison budget.
-/
@[expose] def request {parameter increment point : Canonical}
    {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
    {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
    {unit : Norm.Basic.normSq increment ≤ 1}
    (jet : Sampling.SampledJet parameter increment point source target unit) : Observations jet := by
  let sourceValueZeroForm := Specification.valueSpecification parameter 0
  let sourceValueZeroEvaluator := sourceValueZeroForm.value point source.value source.apart
  let sourceValueZero := Cache.request sourceValueZeroForm point source.value source.apart
    jet.sourceSample.state jet.sourceSample.observation jet.sourceSample.observation_eq jet.accuracy
    sourceValueZeroEvaluator rfl jet.clearance.sourceFloor jet.clearance.sourcePositive jet.clearance.sourceLower
  let sourceValueOneForm := Specification.valueSpecification parameter 1
  let sourceValueOneEvaluator := sourceValueOneForm.value point source.value source.apart
  let sourceValueOne := Cache.request sourceValueOneForm point source.value source.apart
    jet.sourceSample.state jet.sourceSample.observation jet.sourceSample.observation_eq jet.accuracy
    sourceValueOneEvaluator rfl jet.clearance.sourceFloor jet.clearance.sourcePositive jet.clearance.sourceLower
  let targetValueZeroForm := sourceValueZeroForm.atRadicand (Paths.polynomial (parameter + increment))
  let targetValueZeroEvaluator := targetValueZeroForm.value point
    target.value target.apart
  let targetValueZero := Cache.request targetValueZeroForm point
    target.value target.apart
    jet.targetSample.state jet.targetSample.observation jet.targetSample.observation_eq jet.accuracy
    targetValueZeroEvaluator rfl jet.clearance.targetFloor jet.clearance.targetPositive jet.clearance.targetLower
  let targetValueOneForm := sourceValueOneForm.atRadicand (Paths.polynomial (parameter + increment))
  let targetValueOneEvaluator := targetValueOneForm.value point
    target.value target.apart
  let targetValueOne := Cache.request targetValueOneForm point
    target.value target.apart
    jet.targetSample.state jet.targetSample.observation jet.targetSample.observation_eq jet.accuracy
    targetValueOneEvaluator rfl jet.clearance.targetFloor jet.clearance.targetPositive jet.clearance.targetLower
  let sourceFirstZeroForm := Specification.firstDerivativeSpecification parameter 0
  let sourceFirstZeroEvaluator := sourceFirstZeroForm.value point
    source.value source.apart
  let sourceFirstZero := Cache.request sourceFirstZeroForm point
    source.value source.apart
    jet.sourceSample.state jet.sourceSample.observation jet.sourceSample.observation_eq jet.accuracy
    sourceFirstZeroEvaluator rfl jet.clearance.sourceFloor jet.clearance.sourcePositive jet.clearance.sourceLower
  let sourceFirstOneForm := Specification.firstDerivativeSpecification parameter 1
  let sourceFirstOneEvaluator := sourceFirstOneForm.value point
    source.value source.apart
  let sourceFirstOne := Cache.request sourceFirstOneForm point
    source.value source.apart
    jet.sourceSample.state jet.sourceSample.observation jet.sourceSample.observation_eq jet.accuracy
    sourceFirstOneEvaluator rfl jet.clearance.sourceFloor jet.clearance.sourcePositive jet.clearance.sourceLower
  let targetFirstZeroForm := sourceFirstZeroForm.atRadicand (Paths.polynomial (parameter + increment))
  let targetFirstZeroEvaluator := targetFirstZeroForm.value point
    target.value target.apart
  let targetFirstZero := Cache.request targetFirstZeroForm point
    target.value target.apart
    jet.targetSample.state jet.targetSample.observation jet.targetSample.observation_eq jet.accuracy
    targetFirstZeroEvaluator rfl jet.clearance.targetFloor jet.clearance.targetPositive jet.clearance.targetLower
  let targetFirstOneForm := sourceFirstOneForm.atRadicand (Paths.polynomial (parameter + increment))
  let targetFirstOneEvaluator := targetFirstOneForm.value point
    target.value target.apart
  let targetFirstOne := Cache.request targetFirstOneForm point
    target.value target.apart
    jet.targetSample.state jet.targetSample.observation jet.targetSample.observation_eq jet.accuracy
    targetFirstOneEvaluator rfl jet.clearance.targetFloor jet.clearance.targetPositive jet.clearance.targetLower
  let sourceSecondZeroForm := Specification.secondDerivativeSpecification parameter 0
  let sourceSecondZeroEvaluator := sourceSecondZeroForm.value point
    source.value source.apart
  let sourceSecondZero := Cache.request sourceSecondZeroForm point
    source.value source.apart
    jet.sourceSample.state jet.sourceSample.observation jet.sourceSample.observation_eq jet.accuracy
    sourceSecondZeroEvaluator rfl jet.clearance.sourceFloor jet.clearance.sourcePositive jet.clearance.sourceLower
  let sourceSecondOneForm := Specification.secondDerivativeSpecification parameter 1
  let sourceSecondOneEvaluator := sourceSecondOneForm.value point
    source.value source.apart
  let sourceSecondOne := Cache.request sourceSecondOneForm point
    source.value source.apart
    jet.sourceSample.state jet.sourceSample.observation jet.sourceSample.observation_eq jet.accuracy
    sourceSecondOneEvaluator rfl jet.clearance.sourceFloor jet.clearance.sourcePositive jet.clearance.sourceLower
  exact
    { sourceValue := Data.Fin.casesDependent sourceValueZero
        (Data.Fin.casesDependent sourceValueOne (fun index => Fin.elim0 index))
      targetValue := Data.Fin.casesDependent targetValueZero
        (Data.Fin.casesDependent targetValueOne (fun index => Fin.elim0 index))
      sourceFirst := Data.Fin.casesDependent sourceFirstZero
        (Data.Fin.casesDependent sourceFirstOne (fun index => Fin.elim0 index))
      targetFirst := Data.Fin.casesDependent targetFirstZero
        (Data.Fin.casesDependent targetFirstOne (fun index => Fin.elim0 index))
      sourceSecond := Data.Fin.casesDependent sourceSecondZero
        (Data.Fin.casesDependent sourceSecondOne (fun index => Fin.elim0 index)) }

namespace Observations

variable {parameter increment point : Canonical}
  {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
  {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
  {unit : Norm.Basic.normSq increment ≤ 1}
  {jet : Sampling.SampledJet parameter increment point source target unit}

/-- The actual source value arithmetic reading is close to its unchanged selected scalar root anchor. -/
theorem sourceValue_close (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceValue coordinate).reading -
      Variation.valueReading coordinate point jet.sourceSample.reading) <
      Cache.errorBound (Specification.valueSpecification parameter coordinate) point jet.clearance.sourceFloor
        jet.sourceSample.observation jet.accuracy := by
  have close := (observations.sourceValue coordinate).reading_close
  rewrite [value_scalar_eq] at close
  exact close

/-- The distinct actual target value reading pays the comparison bound on its own original process. -/
theorem targetValue_close (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.targetValue coordinate).reading -
      Variation.valueReading coordinate point jet.targetSample.reading) <
      Cache.errorBound (Specification.valueSpecification (parameter + increment) coordinate) point
        jet.clearance.targetFloor
        jet.targetSample.observation jet.accuracy := by
  have close := (observations.targetValue coordinate).reading_close
  rewrite [value_scalar_eq] at close
  exact close

/-- The actual source first derivative reading pays its independent-factor comparison against the same scalar root. -/
theorem sourceFirst_close (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceFirst coordinate).reading -
      Variation.firstReading coordinate point jet.sourceSample.reading) <
      Cache.errorBound (Specification.firstDerivativeSpecification parameter coordinate) point
        jet.clearance.sourceFloor jet.sourceSample.observation jet.accuracy := by
  have close := (observations.sourceFirst coordinate).reading_close
  rewrite [first_scalar_eq] at close
  exact close

/-- The actual target first derivative reading retains its own original root process and comparison payment. -/
theorem targetFirst_close (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.targetFirst coordinate).reading -
      Variation.firstReading coordinate point jet.targetSample.reading) <
      Cache.errorBound (Specification.firstDerivativeSpecification (parameter + increment) coordinate) point
        jet.clearance.targetFloor jet.targetSample.observation jet.accuracy := by
  have close := (observations.targetFirst coordinate).reading_close
  rewrite [first_scalar_eq] at close
  exact close

/-- The actual source second derivative reading pays the original fifth-power independent-factor comparison bound. -/
theorem sourceSecond_close (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceSecond coordinate).reading -
      Variation.secondReading coordinate point jet.sourceSample.reading) <
      Cache.errorBound (Specification.secondDerivativeSpecification parameter coordinate) point
        jet.clearance.sourceFloor jet.sourceSample.observation jet.accuracy := by
  have close := (observations.sourceSecond coordinate).reading_close
  rewrite [second_scalar_eq] at close
  exact close

/-- The actual source value reading pays a computed fourth-order coefficient factor. -/
theorem sourceValue_le (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceValue coordinate).reading -
      Variation.valueReading coordinate point jet.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.valueSpecification parameter coordinate) point source
        jet.clearance.sourceFloor * Norm.Basic.normSq increment ^ 2 :=
  ((observations.sourceValue_close coordinate).le.trans
    (Cache.errorBound_le_factor (Specification.valueSpecification parameter coordinate) point source
      jet.sourceSample jet.clearance.sourcePositive)).trans_eq
      (congrArg (fun tolerance =>
        Cache.allowanceFactor (Specification.valueSpecification parameter coordinate) point source
        jet.clearance.sourceFloor *
        tolerance) jet.accuracy_eq)

/-- The actual target value reading pays its distinct original root process's fourth-order factor. -/
theorem targetValue_le (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.targetValue coordinate).reading -
      Variation.valueReading coordinate point jet.targetSample.reading) ≤
      Cache.allowanceFactor (Specification.valueSpecification (parameter + increment) coordinate) point target
        jet.clearance.targetFloor * Norm.Basic.normSq increment ^ 2 :=
  ((observations.targetValue_close coordinate).le.trans
    (Cache.errorBound_le_factor (Specification.valueSpecification (parameter + increment) coordinate) point target
      jet.targetSample jet.clearance.targetPositive)).trans_eq
      (congrArg (fun tolerance =>
        Cache.allowanceFactor (Specification.valueSpecification (parameter + increment) coordinate) point target
        jet.clearance.targetFloor *
        tolerance) jet.accuracy_eq)

/-- The actual source first derivative reading pays its computed independent cubic-factor error. -/
theorem sourceFirst_le (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceFirst coordinate).reading -
      Variation.firstReading coordinate point jet.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor *
        Norm.Basic.normSq increment ^ 2 :=
  ((observations.sourceFirst_close coordinate).le.trans
    (Cache.errorBound_le_factor (Specification.firstDerivativeSpecification parameter coordinate) point source
      jet.sourceSample jet.clearance.sourcePositive)).trans_eq
      (congrArg (fun tolerance =>
        Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor *
        tolerance) jet.accuracy_eq)

/-- The actual target first derivative reading pays the computed factor on its own original process. -/
theorem targetFirst_le (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.targetFirst coordinate).reading -
      Variation.firstReading coordinate point jet.targetSample.reading) ≤
      Cache.allowanceFactor (Specification.firstDerivativeSpecification (parameter + increment) coordinate) point target
        jet.clearance.targetFloor *
        Norm.Basic.normSq increment ^ 2 :=
  ((observations.targetFirst_close coordinate).le.trans
    (Cache.errorBound_le_factor (Specification.firstDerivativeSpecification (parameter + increment) coordinate)
      point target
      jet.targetSample jet.clearance.targetPositive)).trans_eq
      (congrArg (fun tolerance =>
        Cache.allowanceFactor (Specification.firstDerivativeSpecification (parameter + increment) coordinate)
      point target
        jet.clearance.targetFloor *
        tolerance) jet.accuracy_eq)

/-- The actual source second derivative reading pays the computed independent fifth-power slope error. -/
theorem sourceSecond_le (observations : Observations jet) (coordinate : Fin 2) :
    Norm.Basic.normSq ((observations.sourceSecond coordinate).reading -
      Variation.secondReading coordinate point jet.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.secondDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor *
        Norm.Basic.normSq increment ^ 2 :=
  ((observations.sourceSecond_close coordinate).le.trans
    (Cache.errorBound_le_factor (Specification.secondDerivativeSpecification parameter coordinate) point source
      jet.sourceSample jet.clearance.sourcePositive)).trans_eq
      (congrArg (fun tolerance =>
        Cache.allowanceFactor (Specification.secondDerivativeSpecification parameter coordinate) point source
          jet.clearance.sourceFloor * tolerance)
        jet.accuracy_eq)

/-- Construct finite value variation on actual arithmetic base, output and first-derivative readings.

The scalar certificate remains the source of the Taylor residual. Both value
readings and the actual source first derivative independently pay their
original arithmetic observation factors before the generic perturbation
construction computes the new remainder bound.
-/
@[expose] def valueCertificate (observations : Observations jet) (coordinate : Fin 2) :
    Certificate increment := by
  let certificate := jet.value coordinate
  have base_eq : certificate.base = Variation.valueReading coordinate point jet.sourceSample.reading := by
    change (jet.value coordinate).base = Variation.valueReading coordinate point jet.sourceSample.reading
    rewrite [jet.value_agrees coordinate, Variation.valueCertificate_base]
    rfl
  have output_eq : certificate.output = Variation.valueReading coordinate point jet.targetSample.reading := by
    change (jet.value coordinate).output = Variation.valueReading coordinate point jet.targetSample.reading
    rewrite [jet.value_agrees coordinate, Variation.valueCertificate_output]
    rfl
  have slope_eq : certificate.slope = Variation.firstReading coordinate point jet.sourceSample.reading := by
    change (jet.value coordinate).slope = Variation.firstReading coordinate point jet.sourceSample.reading
    rewrite [jet.value_agrees coordinate, Variation.valueCertificate_slope]
    rfl
  exact certificate.perturb (observations.sourceValue coordinate).reading (observations.targetValue coordinate).reading
    (observations.sourceFirst coordinate).reading
    (Cache.allowanceFactor (Specification.valueSpecification parameter coordinate) point source
      jet.clearance.sourceFloor)
    (Cache.allowanceFactor (Specification.valueSpecification (parameter + increment) coordinate) point target
      jet.clearance.targetFloor)
    (Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
      jet.clearance.sourceFloor)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.sourcePositive)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.targetPositive)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.sourcePositive) unit
    (by rewrite [base_eq]; exact observations.sourceValue_le coordinate)
    (by rewrite [output_eq]; exact observations.targetValue_le coordinate)
    (by rewrite [slope_eq]; exact observations.sourceFirst_le coordinate)

/-- Construct the finite first-derivative variation certificate using its actual original second-derivative slope.

The original scalar first variation supplies the Taylor remainder. Both first
readings and the actual source second derivative pay their independently
constructed arithmetic bounds, so every retained reading belongs to its
original coefficient evaluator on the same two root processes.
-/
@[expose] def firstCertificate (observations : Observations jet) (coordinate : Fin 2) :
    Certificate increment := by
  let certificate := jet.first coordinate
  have base_eq : certificate.base = Variation.firstReading coordinate point jet.sourceSample.reading := by
    change (jet.first coordinate).base = Variation.firstReading coordinate point jet.sourceSample.reading
    rewrite [jet.first_agrees coordinate, Variation.firstCertificate_base]
    rfl
  have output_eq : certificate.output = Variation.firstReading coordinate point jet.targetSample.reading := by
    change (jet.first coordinate).output = Variation.firstReading coordinate point jet.targetSample.reading
    rewrite [jet.first_agrees coordinate, Variation.firstCertificate_output]
    rfl
  have slope_eq : certificate.slope = Variation.secondReading coordinate point jet.sourceSample.reading := by
    change (jet.first coordinate).slope = Variation.secondReading coordinate point jet.sourceSample.reading
    rewrite [jet.first_agrees coordinate, Variation.firstCertificate_slope]
    rfl
  exact certificate.perturb (observations.sourceFirst coordinate).reading (observations.targetFirst coordinate).reading
    (observations.sourceSecond coordinate).reading
    (Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
      jet.clearance.sourceFloor)
    (Cache.allowanceFactor (Specification.firstDerivativeSpecification (parameter + increment) coordinate) point target
      jet.clearance.targetFloor)
    (Cache.allowanceFactor (Specification.secondDerivativeSpecification parameter coordinate) point source
      jet.clearance.sourceFloor)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.sourcePositive)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.targetPositive)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.sourcePositive) unit
    (by rewrite [base_eq]; exact observations.sourceFirst_le coordinate)
    (by rewrite [output_eq]; exact observations.targetFirst_le coordinate)
    (by rewrite [slope_eq]; exact observations.sourceSecond_le coordinate)

/-- The actual value-variation certificate retains its original source arithmetic reading. -/
theorem valueCertificate_base (observations : Observations jet) (coordinate : Fin 2) :
    (observations.valueCertificate coordinate).base = (observations.sourceValue coordinate).reading := by
  unfold valueCertificate
  rewrite [Certificate.perturb_base]
  rfl

/-- The actual value-variation output is the distinct original target arithmetic reading. -/
theorem valueCertificate_output (observations : Observations jet) (coordinate : Fin 2) :
    (observations.valueCertificate coordinate).output = (observations.targetValue coordinate).reading := by
  unfold valueCertificate
  rewrite [Certificate.perturb_output]
  rfl

/-- The actual value-variation slope is the original source first derivative arithmetic reading. -/
theorem valueCertificate_slope (observations : Observations jet) (coordinate : Fin 2) :
    (observations.valueCertificate coordinate).slope = (observations.sourceFirst coordinate).reading := by
  unfold valueCertificate
  rewrite [Certificate.perturb_slope]
  rfl

/-- The actual first-variation certificate retains its original source first derivative reading. -/
theorem firstCertificate_base (observations : Observations jet) (coordinate : Fin 2) :
    (observations.firstCertificate coordinate).base = (observations.sourceFirst coordinate).reading := by
  unfold firstCertificate
  rewrite [Certificate.perturb_base]
  rfl

/-- The actual first-variation output is the original target first derivative arithmetic reading. -/
theorem firstCertificate_output (observations : Observations jet) (coordinate : Fin 2) :
    (observations.firstCertificate coordinate).output = (observations.targetFirst coordinate).reading := by
  unfold firstCertificate
  rewrite [Certificate.perturb_output]
  rfl

/-- The actual first-variation slope is the independently observed original source second derivative reading. -/
theorem firstCertificate_slope (observations : Observations jet) (coordinate : Fin 2) :
    (observations.firstCertificate coordinate).slope = (observations.sourceSecond coordinate).reading := by
  unfold firstCertificate
  rewrite [Certificate.perturb_slope]
  rfl

end Observations

end Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic
