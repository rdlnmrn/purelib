module
public import Purelib.Integration.Cell.Source.Continuous.Producer
public import Purelib.Integration.Partition.Affine
public import Purelib.Integration.Partition.Length
public import Purelib.Approximation.Rational.Uniform.Reverse
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-!
# Rational endpoint transport for continuous source integration

The retained oriented endpoint pair maps the unit parameter by the original
affine partition operation. The existing rational bound process is scaled by
the signed endpoint displacement; coincident endpoints return exact zero.
-/

public section

namespace Purelib.Integration.SourceFrontier.Continuous.Affine

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Read the original rational source at the retained affine unit parameter. -/
@[expose] def pullback (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval)
    (parameter : Fraction.Rational) : Fraction.Rational := source (Partition.Affine.sourceParameter interval parameter)

/-- The affine pullback reads the original source at the retained start when the parameter is zero. -/
theorem pullback_zero (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval) :
    pullback source interval 0 = source interval.start := by
  have endpoint : Partition.Affine.sourceParameter interval 0 = interval.start := by
    unfold Partition.Affine.sourceParameter
    ring1
  exact congrArg source endpoint

/-- The affine pullback reads the original source at the retained finish when the parameter is one. -/
theorem pullback_one (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval) :
    pullback source interval 1 = source interval.finish := by
  have endpoint : Partition.Affine.sourceParameter interval 1 = interval.finish := by
    unfold Partition.Affine.sourceParameter
    ring1
  exact congrArg source endpoint

/-- Read the source on reversed endpoints at exactly the reflected original parameter. -/
theorem pullback_reversed (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval)
    (parameter : Fraction.Rational) :
    pullback source ⟨interval.finish, interval.start⟩ parameter =
      Rational.Uniform.reversed (pullback source interval) parameter := by
  have endpoint : Partition.Affine.sourceParameter ⟨interval.finish, interval.start⟩ parameter =
      Partition.Affine.sourceParameter interval (1 - parameter) := by
    unfold Partition.Affine.sourceParameter
    ring1
  exact congrArg source endpoint

/-- Reverse an affine pullback using the original effective modulus and the same radius. -/
@[expose] def reversedModulus (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval)
    (modulus : Rational.Uniform.Modulus (pullback source interval)) :
    Rational.Uniform.Modulus (pullback source ⟨interval.finish, interval.start⟩) :=
  modulus.reversed.transport (fun point _ _ => pullback_reversed source interval point)

/-- Construct an oriented rational bound process from the original endpoint pair and affine source modulus.

Positive displacement scales the original unit-parameter process directly;
negative displacement scales by its positive magnitude and negates the
result. Coincident endpoints return the original exact-zero process without
making an integration request. -/
@[expose] def boundProcess (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval)
    (modulus : Rational.Uniform.Modulus (pullback source interval)) : BoundProcess :=
  if positive : 0 < interval.signedLength then
    (Continuous.producer modulus).boundProcess.scalePositive interval.signedLength positive
  else if negative : interval.signedLength < 0 then
    ((Continuous.producer modulus).boundProcess.scalePositive (-interval.signedLength) (by
      have opposite := Fraction.Order.Arithmetic.neg_lt_neg_direct negative
      rw [neg_zero] at opposite
      exact opposite)).neg
  else BoundProcess.exact 0

/-- Coincident rational endpoints yield the exact zero process. -/
theorem boundProcess_zero (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval)
    (modulus : Rational.Uniform.Modulus (pullback source interval)) (zero : interval.signedLength = 0) :
    boundProcess source interval modulus = BoundProcess.exact 0 := by
  have notPositive : ¬ 0 < interval.signedLength := by rw [zero]; decide
  have notNegative : ¬ interval.signedLength < 0 := by rw [zero]; decide
  unfold boundProcess
  rw [dif_neg notPositive, dif_neg notNegative]

/-- A positively oriented interval uses its exact positive displacement. -/
theorem boundProcess_positive (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval)
    (modulus : Rational.Uniform.Modulus (pullback source interval)) (positive : 0 < interval.signedLength) :
    boundProcess source interval modulus =
      (Continuous.producer modulus).boundProcess.scalePositive interval.signedLength positive := by
  unfold boundProcess
  rw [dif_pos positive]

/-- A negatively oriented interval uses the negation of its positive displacement magnitude. -/
theorem boundProcess_negative (source : Fraction.Rational → Fraction.Rational) (interval : Partition.Interval)
    (modulus : Rational.Uniform.Modulus (pullback source interval)) (negative : interval.signedLength < 0)
    (positive : 0 < -interval.signedLength) :
    boundProcess source interval modulus =
      ((Continuous.producer modulus).boundProcess.scalePositive (-interval.signedLength) positive).neg := by
  unfold boundProcess
  rw [dif_neg (not_lt_of_ge negative.le), dif_pos negative]

end Purelib.Integration.SourceFrontier.Continuous.Affine

end
