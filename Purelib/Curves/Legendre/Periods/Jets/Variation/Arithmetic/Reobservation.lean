module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache.Reobservation
public import Purelib.Data.Vector.Dependent
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # New spatially paid arithmetic banks on the same retained scalar roots

All ten new observations request the minimum of their independent spatial
accuracy and the original parameter-fourth accuracy. Their original evaluator
caches, old observations and actual old/new operational comparisons remain
retained. Direct scalar-root bounds give BOTH spatial error contraction and
the original parameter Taylor factors on these same new readings.
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

variable {parameter increment point : Canonical}
    {source : CertifiedSquareRoot.Certificate (Polynomials.curveValue parameter point)}
    {target : CertifiedSquareRoot.Certificate (Polynomials.curveValue (parameter + increment) point)}
    {unit : Norm.Basic.normSq increment ≤ 1}
    {jet : Sampling.SampledJet parameter increment point source target unit}

/-- Five materialized two-entry banks with new independent payments on each original evaluator cache.

Every entry retains its complete old arithmetic reading, the genuinely new
reading and their actual generic observation comparison. The same original
scalar jet and root observations remain indices throughout all five banks.
-/
@[expose] def Reobservations (observations : Observations jet) (spatial : AccuracyRequest) :=
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Cache.Reading.Reobservation (observations.sourceValue coordinate) (spatial.minimum jet.accuracy)) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Cache.Reading.Reobservation (observations.targetValue coordinate) (spatial.minimum jet.accuracy)) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Cache.Reading.Reobservation (observations.sourceFirst coordinate) (spatial.minimum jet.accuracy)) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Cache.Reading.Reobservation (observations.targetFirst coordinate) (spatial.minimum jet.accuracy)) ×
  Vector.DependentVector (fun coordinate : Fin 2 =>
    Cache.Reading.Reobservation (observations.sourceSecond coordinate) (spatial.minimum jet.accuracy))

namespace Reobservations

variable {observations : Observations jet} {spatial : AccuracyRequest}

/-- Select every new arithmetic entry once using its actual old evaluator and common independently paid accuracy. -/
def build (observations : Observations jet) (spatial : AccuracyRequest) : Reobservations observations spatial :=
  let sourceValue := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.sourceValue coordinate).reobserve (spatial.minimum jet.accuracy))
  let targetValue := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.targetValue coordinate).reobserve (spatial.minimum jet.accuracy))
  let sourceFirst := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.sourceFirst coordinate).reobserve (spatial.minimum jet.accuracy))
  let targetFirst := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.targetFirst coordinate).reobserve (spatial.minimum jet.accuracy))
  let sourceSecond := Vector.DependentVector.ofFn (fun coordinate : Fin 2 =>
    (observations.sourceSecond coordinate).reobserve (spatial.minimum jet.accuracy))
  ⟨sourceValue, targetValue, sourceFirst, targetFirst, sourceSecond⟩

/-- Read the stored sourceValue bank with its complete old/new coefficient and comparison caches. -/
@[expose] def sourceValue (paid : Reobservations observations spatial) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Cache.Reading.Reobservation (observations.sourceValue coordinate) (spatial.minimum jet.accuracy)) := paid.1

/-- Read the stored targetValue bank with its complete old/new coefficient and comparison caches. -/
@[expose] def targetValue (paid : Reobservations observations spatial) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Cache.Reading.Reobservation (observations.targetValue coordinate) (spatial.minimum jet.accuracy)) := paid.2.1

/-- Read the stored sourceFirst bank with its complete old/new coefficient and comparison caches. -/
@[expose] def sourceFirst (paid : Reobservations observations spatial) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Cache.Reading.Reobservation (observations.sourceFirst coordinate) (spatial.minimum jet.accuracy)) := paid.2.2.1

/-- Read the stored targetFirst bank with its complete old/new coefficient and comparison caches. -/
@[expose] def targetFirst (paid : Reobservations observations spatial) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Cache.Reading.Reobservation (observations.targetFirst coordinate) (spatial.minimum jet.accuracy)) := paid.2.2.2.1

/-- Read the stored sourceSecond bank with its complete old/new coefficient and comparison caches. -/
@[expose] def sourceSecond (paid : Reobservations observations spatial) :
    Vector.DependentVector (fun coordinate : Fin 2 =>
      Cache.Reading.Reobservation (observations.sourceSecond coordinate) (spatial.minimum jet.accuracy)) := paid.2.2.2.2

/-- The new sourceValue witness keeps the original parameter-fourth allowance on its identical scalar root. -/
theorem sourceValue_le (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point jet.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.valueSpecification parameter coordinate) point source
        jet.clearance.sourceFloor * Norm.Basic.normSq increment ^ 2 := by
  have close := (paid.sourceValue.get coordinate).reading_close
  rewrite [value_scalar_eq] at close
  exact (close.le.trans
    (Cache.errorBound_le_factor_of_tolerance_le (Specification.valueSpecification parameter coordinate)
      point source jet.sourceSample (spatial.minimum_le_right jet.accuracy) jet.clearance.sourcePositive)).trans_eq
    (congrArg (fun tolerance =>
      Cache.allowanceFactor (Specification.valueSpecification parameter coordinate) point source
        jet.clearance.sourceFloor * tolerance) jet.accuracy_eq)

/-- The same new sourceValue witness also pays its independent spatial accuracy and original root spread.

The bound contains no old arithmetic observation radius or comparison tail.
Its two spatial contributions concern the actual newly requested evaluator
and the independently paid unchanged primary root observation.
-/
theorem sourceValue_spatial_le (paid : Reobservations observations spatial) (coordinate : Fin 2)
    {spread : Fraction.Rational} (rootPaid : jet.sourceSample.observation.spread ≤ spread) :
    Norm.Basic.normSq ((paid.sourceValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point jet.sourceSample.reading) ≤
      spatial.tolerance + 4 * Cache.sensitivity (Specification.valueSpecification parameter coordinate)
        point jet.clearance.sourceFloor * spread := by
  have close := (paid.sourceValue.get coordinate).reading_error_le rootPaid
  rewrite [value_scalar_eq] at close
  exact close.trans (Fraction.Order.Arithmetic.add_le_add_direct
    (spatial.minimum_le_left jet.accuracy) (Fraction.Order.Basic.le_refl _))

/-- The new targetValue witness keeps the original parameter-fourth allowance on its identical scalar root. -/
theorem targetValue_le (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.targetValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point jet.targetSample.reading) ≤
      Cache.allowanceFactor (Specification.valueSpecification (parameter + increment) coordinate) point target
        jet.clearance.targetFloor * Norm.Basic.normSq increment ^ 2 := by
  have close := (paid.targetValue.get coordinate).reading_close
  rewrite [value_scalar_eq] at close
  exact (close.le.trans
    (Cache.errorBound_le_factor_of_tolerance_le (Specification.valueSpecification (parameter + increment) coordinate)
      point target jet.targetSample (spatial.minimum_le_right jet.accuracy) jet.clearance.targetPositive)).trans_eq
    (congrArg (fun tolerance =>
      Cache.allowanceFactor (Specification.valueSpecification (parameter + increment) coordinate) point target
        jet.clearance.targetFloor * tolerance) jet.accuracy_eq)

/-- The same new targetValue witness also pays its independent spatial accuracy and original root spread.

The bound contains no old arithmetic observation radius or comparison tail.
Its two spatial contributions concern the actual newly requested evaluator
and the independently paid unchanged primary root observation.
-/
theorem targetValue_spatial_le (paid : Reobservations observations spatial) (coordinate : Fin 2)
    {spread : Fraction.Rational} (rootPaid : jet.targetSample.observation.spread ≤ spread) :
    Norm.Basic.normSq ((paid.targetValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point jet.targetSample.reading) ≤
      spatial.tolerance + 4 * Cache.sensitivity (Specification.valueSpecification (parameter + increment) coordinate)
        point jet.clearance.targetFloor * spread := by
  have close := (paid.targetValue.get coordinate).reading_error_le rootPaid
  rewrite [value_scalar_eq] at close
  exact close.trans (Fraction.Order.Arithmetic.add_le_add_direct
    (spatial.minimum_le_left jet.accuracy) (Fraction.Order.Basic.le_refl _))

/-- The new sourceFirst witness keeps the original parameter-fourth allowance on its identical scalar root. -/
theorem sourceFirst_le (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point jet.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor * Norm.Basic.normSq increment ^ 2 := by
  have close := (paid.sourceFirst.get coordinate).reading_close
  rewrite [first_scalar_eq] at close
  exact (close.le.trans
    (Cache.errorBound_le_factor_of_tolerance_le (Specification.firstDerivativeSpecification parameter coordinate)
      point source jet.sourceSample (spatial.minimum_le_right jet.accuracy) jet.clearance.sourcePositive)).trans_eq
    (congrArg (fun tolerance =>
      Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor * tolerance) jet.accuracy_eq)

/-- The same new sourceFirst witness also pays its independent spatial accuracy and original root spread.

The bound contains no old arithmetic observation radius or comparison tail.
Its two spatial contributions concern the actual newly requested evaluator
and the independently paid unchanged primary root observation.
-/
theorem sourceFirst_spatial_le (paid : Reobservations observations spatial) (coordinate : Fin 2)
    {spread : Fraction.Rational} (rootPaid : jet.sourceSample.observation.spread ≤ spread) :
    Norm.Basic.normSq ((paid.sourceFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point jet.sourceSample.reading) ≤
      spatial.tolerance + 4 * Cache.sensitivity (Specification.firstDerivativeSpecification parameter coordinate)
        point jet.clearance.sourceFloor * spread := by
  have close := (paid.sourceFirst.get coordinate).reading_error_le rootPaid
  rewrite [first_scalar_eq] at close
  exact close.trans (Fraction.Order.Arithmetic.add_le_add_direct
    (spatial.minimum_le_left jet.accuracy) (Fraction.Order.Basic.le_refl _))

/-- The new targetFirst witness keeps the original parameter-fourth allowance on its identical scalar root. -/
theorem targetFirst_le (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.targetFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point jet.targetSample.reading) ≤
      Cache.allowanceFactor (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate) point target
        jet.clearance.targetFloor * Norm.Basic.normSq increment ^ 2 := by
  have close := (paid.targetFirst.get coordinate).reading_close
  rewrite [first_scalar_eq] at close
  exact (close.le.trans
    (Cache.errorBound_le_factor_of_tolerance_le (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate)
      point target jet.targetSample (spatial.minimum_le_right jet.accuracy) jet.clearance.targetPositive)).trans_eq
    (congrArg (fun tolerance =>
      Cache.allowanceFactor (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate) point target
        jet.clearance.targetFloor * tolerance) jet.accuracy_eq)

/-- The same new targetFirst witness also pays its independent spatial accuracy and original root spread.

The bound contains no old arithmetic observation radius or comparison tail.
Its two spatial contributions concern the actual newly requested evaluator
and the independently paid unchanged primary root observation.
-/
theorem targetFirst_spatial_le (paid : Reobservations observations spatial) (coordinate : Fin 2)
    {spread : Fraction.Rational} (rootPaid : jet.targetSample.observation.spread ≤ spread) :
    Norm.Basic.normSq ((paid.targetFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point jet.targetSample.reading) ≤
      spatial.tolerance + 4 * Cache.sensitivity (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate)
        point jet.clearance.targetFloor * spread := by
  have close := (paid.targetFirst.get coordinate).reading_error_le rootPaid
  rewrite [first_scalar_eq] at close
  exact close.trans (Fraction.Order.Arithmetic.add_le_add_direct
    (spatial.minimum_le_left jet.accuracy) (Fraction.Order.Basic.le_refl _))

/-- The new sourceSecond witness keeps the original parameter-fourth allowance on its identical scalar root. -/
theorem sourceSecond_le (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceSecond.get coordinate).requested.reading -
      Variation.secondReading coordinate point jet.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.secondDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor * Norm.Basic.normSq increment ^ 2 := by
  have close := (paid.sourceSecond.get coordinate).reading_close
  rewrite [second_scalar_eq] at close
  exact (close.le.trans
    (Cache.errorBound_le_factor_of_tolerance_le (Specification.secondDerivativeSpecification parameter coordinate)
      point source jet.sourceSample (spatial.minimum_le_right jet.accuracy) jet.clearance.sourcePositive)).trans_eq
    (congrArg (fun tolerance =>
      Cache.allowanceFactor (Specification.secondDerivativeSpecification parameter coordinate) point source
        jet.clearance.sourceFloor * tolerance) jet.accuracy_eq)

/-- The same new sourceSecond witness also pays its independent spatial accuracy and original root spread.

The bound contains no old arithmetic observation radius or comparison tail.
Its two spatial contributions concern the actual newly requested evaluator
and the independently paid unchanged primary root observation.
-/
theorem sourceSecond_spatial_le (paid : Reobservations observations spatial) (coordinate : Fin 2)
    {spread : Fraction.Rational} (rootPaid : jet.sourceSample.observation.spread ≤ spread) :
    Norm.Basic.normSq ((paid.sourceSecond.get coordinate).requested.reading -
      Variation.secondReading coordinate point jet.sourceSample.reading) ≤
      spatial.tolerance + 4 * Cache.sensitivity (Specification.secondDerivativeSpecification parameter coordinate)
        point jet.clearance.sourceFloor * spread := by
  have close := (paid.sourceSecond.get coordinate).reading_error_le rootPaid
  rewrite [second_scalar_eq] at close
  exact close.trans (Fraction.Order.Arithmetic.add_le_add_direct
    (spatial.minimum_le_left jet.accuracy) (Fraction.Order.Basic.le_refl _))

/-- Construct the value Taylor certificate from the retained scalar roots and the new spatially paid readings.

The source, target and independent slope bounds are proved on the new bank
itself. The old displayed arithmetic witnesses and their radius costs are
absent from this parameter Taylor construction.
-/
@[expose] def valueCertificate (paid : Reobservations observations spatial) (coordinate : Fin 2) :
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
  exact certificate.perturb (paid.sourceValue.get coordinate).requested.reading
    (paid.targetValue.get coordinate).requested.reading
    (paid.sourceFirst.get coordinate).requested.reading
    (Cache.allowanceFactor (Specification.valueSpecification parameter coordinate) point source
      jet.clearance.sourceFloor)
    (Cache.allowanceFactor (Specification.valueSpecification (parameter + increment) coordinate) point
      target jet.clearance.targetFloor)
    (Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
      jet.clearance.sourceFloor)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.sourcePositive)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.targetPositive)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.sourcePositive) unit
    (by rewrite [base_eq]; exact paid.sourceValue_le coordinate)
    (by rewrite [output_eq]; exact paid.targetValue_le coordinate)
    (by rewrite [slope_eq]; exact paid.sourceFirst_le coordinate)

/-- The new value certificate retains its actual independently paid base reading. -/
theorem valueCertificate_base (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    (paid.valueCertificate coordinate).base = (paid.sourceValue.get coordinate).requested.reading := by
  unfold valueCertificate
  rewrite [Certificate.perturb_base]
  rfl

/-- The new value certificate retains its actual independently paid output reading. -/
theorem valueCertificate_output (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    (paid.valueCertificate coordinate).output = (paid.targetValue.get coordinate).requested.reading := by
  unfold valueCertificate
  rewrite [Certificate.perturb_output]
  rfl

/-- The new value certificate retains its actual independently paid slope reading. -/
theorem valueCertificate_slope (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    (paid.valueCertificate coordinate).slope = (paid.sourceFirst.get coordinate).requested.reading := by
  unfold valueCertificate
  rewrite [Certificate.perturb_slope]
  rfl

/-- The new value bank has the original numerical Taylor factor on the same scalar cache and sheet floors.

Only the factor agrees. The independently selected new arithmetic readings
remain distinct from their old counterparts, with their own actual requests.
-/
theorem valueCertificate_factor_eq (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    (paid.valueCertificate coordinate).factor = (observations.valueCertificate coordinate).factor := by
  unfold valueCertificate Observations.valueCertificate
  rewrite [Certificate.perturb_factor, Certificate.perturb_factor]
  rfl

/-- The actual new value readings satisfy their directly constructed parameter Taylor remainder bound. -/
theorem value_remainder_le (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    Canonical.normSq
      ((paid.targetValue.get coordinate).requested.reading -
        (paid.sourceValue.get coordinate).requested.reading -
        increment * (paid.sourceFirst.get coordinate).requested.reading) ≤
      (paid.valueCertificate coordinate).factor * Canonical.normSq increment ^ 2 := by
  have bound := (paid.valueCertificate coordinate).remainder_le
  rewrite [← (paid.valueCertificate coordinate).expansion, paid.valueCertificate_base coordinate,
    paid.valueCertificate_output coordinate, paid.valueCertificate_slope coordinate] at bound
  exact bound

/-- Construct the first-derivative Taylor certificate from the same scalar roots and new spatially paid readings.

The source, target and independent slope bounds are proved on the new bank
itself. The old displayed arithmetic witnesses and their radius costs are
absent from this parameter Taylor construction.
-/
@[expose] def firstCertificate (paid : Reobservations observations spatial) (coordinate : Fin 2) :
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
  exact certificate.perturb (paid.sourceFirst.get coordinate).requested.reading
    (paid.targetFirst.get coordinate).requested.reading
    (paid.sourceSecond.get coordinate).requested.reading
    (Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point source
      jet.clearance.sourceFloor)
    (Cache.allowanceFactor (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate) point target
      jet.clearance.targetFloor)
    (Cache.allowanceFactor (Specification.secondDerivativeSpecification parameter coordinate) point source
      jet.clearance.sourceFloor)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.sourcePositive)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.targetPositive)
    (Cache.allowanceFactor_nonnegative _ _ _ jet.clearance.sourcePositive) unit
    (by rewrite [base_eq]; exact paid.sourceFirst_le coordinate)
    (by rewrite [output_eq]; exact paid.targetFirst_le coordinate)
    (by rewrite [slope_eq]; exact paid.sourceSecond_le coordinate)

/-- The new first-derivative certificate retains its actual independently paid base reading. -/
theorem firstCertificate_base (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    (paid.firstCertificate coordinate).base = (paid.sourceFirst.get coordinate).requested.reading := by
  unfold firstCertificate
  rewrite [Certificate.perturb_base]
  rfl

/-- The new first-derivative certificate retains its actual independently paid output reading. -/
theorem firstCertificate_output (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    (paid.firstCertificate coordinate).output = (paid.targetFirst.get coordinate).requested.reading := by
  unfold firstCertificate
  rewrite [Certificate.perturb_output]
  rfl

/-- The new first-derivative certificate retains its actual independently paid slope reading. -/
theorem firstCertificate_slope (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    (paid.firstCertificate coordinate).slope = (paid.sourceSecond.get coordinate).requested.reading := by
  unfold firstCertificate
  rewrite [Certificate.perturb_slope]
  rfl

/-- The new first-derivative bank has the original numerical Taylor factor on the same scalar cache and sheet floors.

Only the factor agrees. The independently selected new arithmetic readings
remain distinct from their old counterparts, with their own actual requests.
-/
theorem firstCertificate_factor_eq (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    (paid.firstCertificate coordinate).factor = (observations.firstCertificate coordinate).factor := by
  unfold firstCertificate Observations.firstCertificate
  rewrite [Certificate.perturb_factor, Certificate.perturb_factor]
  rfl

/-- The actual new first-derivative readings satisfy their directly constructed parameter Taylor remainder bound. -/
theorem first_remainder_le (paid : Reobservations observations spatial) (coordinate : Fin 2) :
    Canonical.normSq
      ((paid.targetFirst.get coordinate).requested.reading -
        (paid.sourceFirst.get coordinate).requested.reading -
        increment * (paid.sourceSecond.get coordinate).requested.reading) ≤
      (paid.firstCertificate coordinate).factor * Canonical.normSq increment ^ 2 := by
  have bound := (paid.firstCertificate coordinate).remainder_le
  rewrite [← (paid.firstCertificate coordinate).expansion, paid.firstCertificate_base coordinate,
    paid.firstCertificate_output coordinate, paid.firstCertificate_slope coordinate] at bound
  exact bound

end Reobservations

end Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic

end
