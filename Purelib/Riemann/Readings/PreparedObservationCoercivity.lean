module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Polynomial.Geometry.EvaluationLower

public import Purelib.Riemann.Readings.PreparedObservationInterpolation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Readings.PreparedObservationPoints
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Uniform quantitative coercivity of the fixed observation bank

The inverse of the finite observation matrix supplies a positive rational
constant, depending only on the curve, which bounds the squared coefficient
norm by the sum of squared numerator evaluations.  This is a finite
interpolation estimate, not a compactness or minimum-eigenvalue argument.

This module does not identify observation values with surface integrals.
That remaining geometric step must convert the pointwise estimate to boxes
and to the actual period-program boundary comparison.
-/

namespace Purelib.Riemann.Readings.PreparedObservationCoercivity

open Purelib.LinearAlgebra
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationPoints (ObservationBank GaussianPolynomial)
open Purelib.Riemann.Readings.PreparedObservationInterpolation (ObservationInterpolation)

open Purelib.Data.Rat in
/-- The exact rational coordinate field of the observation bounds. -/
abbrev Coordinate := Fraction.Rational

section
open Purelib.Algebra
/-- A finite sum of pointwise nonnegative rational values is nonnegative. -/
private theorem sum_nonnegative {count : Nat} (values : Fin count -> Coordinate)
    (nonnegative : forall index, 0 <= values index) : 0 <= FiniteSum.Fin.sumFin values := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono
    (fun _ : Fin count => (0 : Coordinate)) values nonnegative
  simpa only [FiniteSum.Fin.sumFin_zero] using bound

/-- Every entry of a nonnegative finite rational family is bounded by its sum. -/
private theorem entry_le_sum {count : Nat} (values : Fin count -> Coordinate)
    (nonnegative : forall index, 0 <= values index) (index : Fin count) :
    values index <= FiniteSum.Fin.sumFin values := by
  rw [<- FiniteSum.Fin.sumFin_ite_eq index values]
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro entry
  by_cases equal : entry = index
  · rw [if_pos equal]
  · rw [if_neg equal]
    exact nonnegative entry

/-- A constant finite rational sum equals the index count times its value. -/
private theorem sum_constant (count : Nat) (value : Coordinate) :
    FiniteSum.Fin.sumFin (fun _ : Fin count => value) = (count : Coordinate) * value := by
  induction count with
  | zero => change 0 = 0 * value; ring1
  | succ count inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ, inductionHypothesis, Nat.cast_succ]
      ring1

end

open Purelib.Algebra in
open Purelib.LinearAlgebra.Gaussian in
/-- The sum of squared Gaussian norms of the original coefficient vector. -/
def coefficientNormSq {count : Nat}
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) : Coordinate :=
  FiniteSum.Fin.sumFin (fun row => normSq (coefficients row))

open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
/-- A retained nonzero coefficient witness makes the coefficient squared-norm sum strictly positive. -/
theorem coefficientNormSq_positive {count : Nat}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count}
    (nonzero : Energy.NonzeroGaussianVector coefficients) :
    0 < coefficientNormSq coefficients := by
  have positive := Norm.Basic.normSq_pos nonzero.coefficient_nonzero
  rw [Norm.Basic.normSq_eq_canonical] at positive
  have nonnegative (row : Fin count) : 0 ≤ normSq (coefficients row) := by
    have scalar := Norm.Basic.normSq_nonneg (coefficients row)
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar
  exact positive.trans_le (entry_le_sum _ nonnegative nonzero.index)

open Purelib.Algebra in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- The sum of squared polynomial-evaluation norms at the original observation bank points.

The polynomial is formed from the supplied coefficient vector, and the observation indices and points remain those of
the retained bank. -/
def observationNormSq {polynomial : GaussianPolynomial} {count : Nat}
    (bank : ObservationBank polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) : Coordinate :=
  FiniteSum.Fin.sumFin (fun column => normSq
    ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
      (bank.pointAt column)))

open Purelib.Algebra in
set_option genInjectivity false in
/-- Cached positive-coercivity data from an original scaled interpolation inverse.

The record retains the interpolation, sum of inverse-entry squared norms, scalar squared norm, comparison scale and
their exact defining equalities. The lower factor is the scalar norm divided by the comparison scale. -/
structure ObservationCoercivity (polynomial : GaussianPolynomial) (count : Nat) where
  /-- The original observation bank and its retained scaled inverse interpolation certificate. -/ interpolation :
    ObservationInterpolation polynomial count
  /-- The cached sum of squared norms of every entry in the original inverse matrix. -/ inverseNorm : Coordinate
  /-- The cached inverse norm equals the exact double finite sum of original entry norms. -/ inverseNorm_eq :
    inverseNorm = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
    normSq (interpolation.inverse.inverse column row)))
  /-- The cached squared norm of the original nonzero inverse scalar. -/ scalarNorm : Coordinate
  /-- The cached scalar norm equals the original inverse scalar's squared norm. -/ scalarNorm_eq : scalarNorm = normSq
    interpolation.inverse.scalar
  /-- The cached coefficient comparison scale, including its positive unit offset. -/ comparisonScale : Coordinate
  /-- The comparison scale equals count squared times the retained inverse norm plus one. -/ comparisonScale_eq :
    comparisonScale = (count : Coordinate) ^ 2 * inverseNorm + 1
  /-- The cached rational coercivity lower factor. -/ lower : Coordinate
  /-- The lower factor equals the retained scalar norm divided by the comparison scale. -/ lower_eq : lower = scalarNorm
    / comparisonScale

constructive_injectivity ObservationCoercivity

namespace ObservationCoercivity

variable {polynomial : GaussianPolynomial} {count : Nat}

open Purelib.Algebra in
/-- Compute and retain coercivity scalars from the original observation interpolation.

The comparison scale is the square of the observation count times the inverse-entry norm sum plus one; the lower factor
uses the original inverse scalar norm. -/
def ofInterpolation (interpolation : ObservationInterpolation polynomial count) :
    ObservationCoercivity polynomial count :=
  let inverseNorm := FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun row =>
    normSq (interpolation.inverse.inverse column row)))
  let scalarNorm := normSq interpolation.inverse.scalar
  let comparisonScale := (count : Coordinate) ^ 2 * inverseNorm + 1
  { interpolation := interpolation
    inverseNorm := inverseNorm
    inverseNorm_eq := rfl
    scalarNorm := scalarNorm
    scalarNorm_eq := rfl
    comparisonScale := comparisonScale
    comparisonScale_eq := rfl
    lower := scalarNorm / comparisonScale
    lower_eq := rfl }

open Purelib.Data.Gaussian in
/-- The retained sum of squared inverse-entry norms is nonnegative. -/
theorem inverseNorm_nonnegative (certificate : ObservationCoercivity polynomial count) :
    0 <= certificate.inverseNorm := by
  rw [certificate.inverseNorm_eq]
  exact sum_nonnegative _ (fun column => sum_nonnegative _ (fun row => by
    have scalar := Norm.Basic.normSq_nonneg (certificate.interpolation.inverse.inverse column row)
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar))

open Purelib.Data.Rat in
/-- The retained count-scaled inverse norm plus one is strictly positive. -/
theorem comparisonScale_positive (certificate : ObservationCoercivity polynomial count) :
    0 < certificate.comparisonScale := by
  rw [certificate.comparisonScale_eq]
  exact lt_of_lt_of_le (show (0 : Coordinate) < 1 by decide)
    (le_add_of_nonneg_left (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) certificate.inverseNorm_nonnegative))

open Purelib.Data.Gaussian in
/-- The original interpolation inverse's nonzero scalar has strictly positive squared norm. -/
theorem scalarNorm_positive (certificate : ObservationCoercivity polynomial count) :
    0 < certificate.scalarNorm := by
  rw [certificate.scalarNorm_eq]
  have scalar := Norm.Basic.normSq_pos certificate.interpolation.scalar_nonzero
  rw [Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

open Purelib.Data.Rat in
/-- The retained coercivity lower factor is strictly positive. -/
theorem lower_positive (certificate : ObservationCoercivity polynomial count) :
    0 < certificate.lower := by
  rw [certificate.lower_eq]
  exact Fraction.Order.Field.div_pos_direct certificate.scalarNorm_positive
    certificate.comparisonScale_positive

open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- Every original inverse entry's squared norm is bounded by the retained full inverse norm sum. -/
private theorem inverseEntry_le (certificate : ObservationCoercivity polynomial count)
    (column row : Fin count) :
    normSq (certificate.interpolation.inverse.inverse column row) <= certificate.inverseNorm := by
  rw [certificate.inverseNorm_eq]
  have entryBound := entry_le_sum
    (fun entry : Fin count => normSq (certificate.interpolation.inverse.inverse column entry))
    (fun entry => by
      have scalar := Norm.Basic.normSq_nonneg (certificate.interpolation.inverse.inverse column entry)
      rw [Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar) row
  have columnBound := entry_le_sum
    (fun entry : Fin count => FiniteSum.Fin.sumFin (fun row : Fin count =>
      normSq (certificate.interpolation.inverse.inverse entry row)))
    (fun entry => sum_nonnegative _ (fun row => by
      have scalar := Norm.Basic.normSq_nonneg (certificate.interpolation.inverse.inverse entry row)
      rw [Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar)) column
  exact entryBound.trans columnBound

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- Bound one coefficient's scalar-weighted squared norm by the observation norm sum and retained inverse norm.

The original interpolation reconstruction and finite Gaussian sum estimate supply the observation-count factor without
replacing the coefficient vector or bank. -/
theorem coefficient_mul_scalarNorm_le
    (certificate : ObservationCoercivity polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) (row : Fin count) :
    normSq (coefficients row) * certificate.scalarNorm <=
      (count : Coordinate) * observationNormSq certificate.interpolation.bank coefficients *
        certificate.inverseNorm := by
  rw [certificate.scalarNorm_eq, ← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical,
    <- Norm.Basic.normSq_mul,
    <- certificate.interpolation.reconstruct coefficients row]
  have localBounds : forall column : Fin count,
      Data.Gaussian.Norm.Basic.normSq
        ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
            (certificate.interpolation.bank.pointAt column) *
          certificate.interpolation.inverse.inverse column row) <=
      Data.Gaussian.Norm.Basic.normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
        (certificate.interpolation.bank.pointAt column)) * certificate.inverseNorm := by
    intro column
    rw [Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by
        have scalar := certificate.inverseEntry_le column row
        simpa only [Norm.Basic.normSq_eq_canonical] using scalar)
      (Norm.Basic.normSq_nonneg _)
  have bound := Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    _ _ localBounds
  rw [FiniteSum.Fin.sumFin_mul_right] at bound
  have observationEq : FiniteSum.Fin.sumFin
      (fun column => Data.Gaussian.Norm.Basic.normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
        (certificate.interpolation.bank.pointAt column))) =
      observationNormSq certificate.interpolation.bank coefficients := by
    apply FiniteSum.Fin.sumFin_congr
    intro column
    exact Norm.Basic.normSq_eq_canonical _
  rw [observationEq] at bound
  exact bound.trans_eq (by ring1)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- The scalar-weighted coefficient norm sum is bounded by comparison scale times the observation norm sum. -/
theorem coefficientNorm_mul_scalarNorm_le
    (certificate : ObservationCoercivity polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) :
    coefficientNormSq coefficients * certificate.scalarNorm <=
      certificate.comparisonScale * observationNormSq certificate.interpolation.bank coefficients := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _
    (fun row => certificate.coefficient_mul_scalarNorm_le coefficients row)
  rw [FiniteSum.Fin.sumFin_mul_right, sum_constant] at bound
  have observationNonnegative : 0 <= observationNormSq certificate.interpolation.bank coefficients :=
    sum_nonnegative _ (fun column => by
      have scalar := Norm.Basic.normSq_nonneg
        ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
          (certificate.interpolation.bank.pointAt column))
      rw [Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar)
  calc
    coefficientNormSq coefficients * certificate.scalarNorm <=
        (count : Coordinate) * ((count : Coordinate) *
          observationNormSq certificate.interpolation.bank coefficients * certificate.inverseNorm) := bound
    _ <= (count : Coordinate) * ((count : Coordinate) *
          observationNormSq certificate.interpolation.bank coefficients * certificate.inverseNorm) +
        observationNormSq certificate.interpolation.bank coefficients :=
      le_add_of_nonneg_right observationNonnegative
    _ = certificate.comparisonScale *
        observationNormSq certificate.interpolation.bank coefficients := by
      rw [certificate.comparisonScale_eq]
      ring1

open Purelib.Data.Rat
open Purelib.LinearAlgebra.Gaussian
/-- The positive retained lower factor times the coefficient norm sum is bounded by the original observation norm sum.
-/
theorem lower_mul_coefficientNorm_le
    (certificate : ObservationCoercivity polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) :
    certificate.lower * coefficientNormSq coefficients <=
      observationNormSq certificate.interpolation.bank coefficients := by
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
    (c := certificate.comparisonScale) _ certificate.comparisonScale_positive
  have lowerCancel : certificate.lower * certificate.comparisonScale = certificate.scalarNorm := by
    rw [certificate.lower_eq]
    exact Fraction.Field.div_mul_cancel_of_ne _ _
      certificate.comparisonScale_positive.ne'
  calc
    (certificate.lower * coefficientNormSq coefficients) * certificate.comparisonScale =
        coefficientNormSq coefficients *
          (certificate.lower * certificate.comparisonScale) := by ring1
    _ = coefficientNormSq coefficients * certificate.scalarNorm := by rw [lowerCancel]
    _ <= certificate.comparisonScale *
        observationNormSq certificate.interpolation.bank coefficients :=
      certificate.coefficientNorm_mul_scalarNorm_le coefficients
    _ = _ := by ring1

/-- A nonzero original coefficient vector has strictly positive observation norm under the retained interpolation
certificate. -/
theorem observationNormSq_positive
    (certificate : ObservationCoercivity polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count)
    (nonzero : Energy.NonzeroGaussianVector coefficients) :
    0 < observationNormSq certificate.interpolation.bank coefficients :=
  (Fraction.Order.Arithmetic.mul_pos_direct certificate.lower_positive
    (coefficientNormSq_positive nonzero)).trans_le
      (certificate.lower_mul_coefficientNorm_le coefficients)

end ObservationCoercivity

open Purelib in
open Purelib.Riemann.Readings in
/-- Construct observation coercivity from the curve's canonical retained observation interpolation. -/
def curveObservationCoercivity {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus) :
    ObservationCoercivity curve.polynomial genus :=
  ObservationCoercivity.ofInterpolation (PreparedObservationInterpolation.curveObservationInterpolation curve)

end Purelib.Riemann.Readings.PreparedObservationCoercivity
