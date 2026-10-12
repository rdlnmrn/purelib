module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Readings.PreparedObservationInterpolation
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.EvaluationLower

public import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Coefficient-uniform variation on finite rational boxes

Apply the audited finite Horner bounds to the fixed monomial basis, then
combine them by finite Cauchy--Schwarz.  The cached bound depends only on the
box and the coefficient count.  In particular it remains homogeneous when
the requested coefficient vector is arbitrarily small.
-/

namespace Purelib.Riemann.Integration.PreparedNumeratorVariation

open Purelib.LinearAlgebra
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Readings.PreparedObservationInterpolation (eval_reverse_ofFn)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

/-- The original rational box carrier with retained coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box

open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The coefficient polynomial of the unit vector at the retained basis index. -/
def basisNumerator {count : Nat} (row : Fin count) : Geometry.EvaluationLower.GaussianPolynomial :=
  Geometry.EvaluationLower.coefficientPolynomial
    (Vector.Basic.vectorOfFn (fun entry => if entry = row then (1 : Basic.Canonical) else 0))

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The unit-coefficient basis numerator evaluates to the point raised to the original index value. -/
theorem basisNumerator_eval {count : Nat} (row : Fin count) (point : Basic.Canonical) :
    (basisNumerator row).eval point = point ^ row.val := by
  change Dense.Basic.DensePolynomial.evalCoeffs point
    (List.ofFn (fun entry =>
      Vector.Basic.vectorOfFn (fun entry : Fin count => if entry = row then (1 : Basic.Canonical) else 0)
        entry)).reverse = _
  rw [eval_reverse_ofFn]
  calc
    _ = FiniteSum.Fin.sumFin (fun entry : Fin count => if entry = row then point ^ entry.val else 0) :=
      FiniteSum.Fin.sumFin_congr (fun entry => by
        rw [Vector.Basic.vectorOfFn_apply]
        by_cases equal : entry = row
        · rw [if_pos equal, if_pos equal, Basic.one_mul]
        · rw [if_neg equal, if_neg equal, Basic.zero_mul])
    _ = _ := FiniteSum.Fin.sumFin_ite_eq row _

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- A finite rational sum of pointwise nonnegative values is nonnegative. -/
private theorem sum_nonnegative {count : Nat} (values : Fin count -> Fraction.Rational)
    (nonnegative : forall row, 0 <= values row) : 0 <= FiniteSum.Fin.sumFin values := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono
    (fun _ : Fin count => (0 : Fraction.Rational)) values nonnegative
  simpa only [FiniteSum.Fin.sumFin_zero] using bound

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- Cached monomial variation bounds on one original ambient box.

The record retains each basis polynomial's exact squared-norm Lipschitz bound, their sum and the
coefficient-count-scaled total used for arbitrary numerator vectors. -/
structure NumeratorVariation (count : Nat) (ambient : Box) where
  /-- The cached variation bound for each original basis numerator on the ambient box. -/ basisSlope :
    Data.Vector Fraction.Rational count
  /-- Each cached basis value equals its exact polynomial box Lipschitz bound. -/ basisSlope_eq : forall row, basisSlope
    row =
    Bounds.Box.denseLipschitzBound (basisNumerator row) ambient
  /-- The cached sum of the original basis variation bounds. -/ totalSlope : Fraction.Rational
  /-- The total slope equals the exact finite sum of the retained basis vector. -/ totalSlope_eq : totalSlope =
    FiniteSum.Fin.sumFin (fun row => basisSlope row)
  /-- The cached coefficient-count-scaled total slope. -/ scale : Fraction.Rational
  /-- The scale equals the original coefficient count times the retained total slope. -/ scale_eq : scale = (count :
    Fraction.Rational) * totalSlope

constructive_injectivity NumeratorVariation

namespace NumeratorVariation

variable {count : Nat} {ambient : Box}

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- Compute and retain the basis variation vector and its two aggregate bounds on the original ambient box.

The exact vector readback equations tie every retained basis bound to its original unit-coefficient polynomial. -/
def build (count : Nat) (ambient : Box) : NumeratorVariation count ambient :=
  let slopes := Vector.Basic.vectorOfFn fun row : Fin count =>
    Bounds.Box.denseLipschitzBound (basisNumerator row) ambient
  let total := FiniteSum.Fin.sumFin (fun row => slopes row)
  { basisSlope := slopes
    basisSlope_eq := fun row => Vector.Basic.vectorOfFn_apply _ row
    totalSlope := total
    totalSlope_eq := rfl
    scale := (count : Fraction.Rational) * total
    scale_eq := rfl }

open Purelib.Polynomial.Dense.Gaussian in
/-- Every retained basis variation bound is strictly positive. -/
theorem basisSlope_positive (variation : NumeratorVariation count ambient)
    (row : Fin count) : 0 < variation.basisSlope row := by
  rw [variation.basisSlope_eq]
  exact Bounds.Box.denseLipschitzBound_pos _ _

/-- The retained sum of basis variation bounds is nonnegative. -/
theorem totalSlope_nonnegative (variation : NumeratorVariation count ambient) :
    0 <= variation.totalSlope := by
  rw [variation.totalSlope_eq]
  exact sum_nonnegative _ (fun row => (variation.basisSlope_positive row).le)

open Purelib.Data.Rat in
/-- The count-scaled retained total variation bound is nonnegative. -/
theorem scale_nonnegative (variation : NumeratorVariation count ambient) :
    0 <= variation.scale := by
  rw [variation.scale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count))
    variation.totalSlope_nonnegative

open Purelib.Algebra in
/-- Each retained basis variation bound is at most their nonnegative sum. -/
theorem basisSlope_le_total (variation : NumeratorVariation count ambient)
    (row : Fin count) : variation.basisSlope row <= variation.totalSlope := by
  rw [variation.totalSlope_eq, <- FiniteSum.Fin.sumFin_ite_eq row (fun entry => variation.basisSlope entry)]
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro entry
  by_cases equal : entry = row
  · rw [if_pos equal]
  · rw [if_neg equal]
    exact (variation.basisSlope_positive entry).le

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
/-- Within the original ambient box, the squared difference of a retained basis power is bounded by total slope times
squared point distance. -/
theorem power_sub_bound (variation : NumeratorVariation count ambient)
    (row : Fin count) {left right : Basic.Canonical}
    (leftInside : ambient.Contains left) (rightInside : ambient.Contains right) :
    normSq (left ^ row.val - right ^ row.val) <=
      variation.totalSlope * normSq (left - right) := by
  have bound := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
    (basisNumerator row) leftInside rightInside
  rw [basisNumerator_eval, basisNumerator_eval, <- variation.basisSlope_eq] at bound
  simp only [Norm.Basic.normSq_eq_canonical] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (variation.basisSlope_le_total row) (by
        simpa only [Norm.Basic.normSq_eq_canonical]
          using (Norm.Basic.normSq_nonneg _)))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- Bound the squared variation of the original coefficient polynomial inside its ambient box.

The bound is the retained count-scaled basis slope times the original coefficient norm sum and squared distance between
the supplied points. -/
theorem numerator_sub_bound (variation : NumeratorVariation count ambient)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count)
    {left right : Basic.Canonical}
    (leftInside : ambient.Contains left) (rightInside : ambient.Contains right) :
    normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval left -
      (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval right) <=
      variation.scale * coefficientNormSq coefficients * normSq (left - right) := by
  change normSq
    (Dense.Basic.DensePolynomial.evalCoeffs left (List.ofFn coefficients).reverse -
      Dense.Basic.DensePolynomial.evalCoeffs right (List.ofFn coefficients).reverse) <= _
  rw [eval_reverse_ofFn, eval_reverse_ofFn]
  have localBounds : forall row : Fin count,
      normSq (coefficients row * left ^ row.val - coefficients row * right ^ row.val) <=
        normSq (coefficients row) * (variation.totalSlope * normSq (left - right)) := by
    intro row
    rw [<- mul_sub, ← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_mul]
    simp only [Norm.Basic.normSq_eq_canonical]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (variation.power_sub_bound row leftInside rightInside) (by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using (Norm.Basic.normSq_nonneg _))
  have bound := Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
    _ _ _ (fun row => by simpa only [Norm.Basic.normSq_eq_canonical] using localBounds row)
  simp only [Norm.Basic.normSq_eq_canonical] at bound
  rw [FiniteSum.Fin.sumFin_mul_right] at bound
  exact bound.trans_eq (by rw [variation.scale_eq]; unfold coefficientNormSq; ring1)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- Transport a numerator squared-norm lower estimate from a retained sample to another point in the same refining cell.

Half the sample value minus the original variation scale times coefficient norm and cell diagonal squared is a lower
bound at every supplied point of that cell. -/
theorem sampled_lower_le (variation : NumeratorVariation count ambient)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count)
    {sample point : Basic.Canonical} {cell : Box}
    (sampleInside : cell.Contains sample) (pointInside : cell.Contains point)
    (refines : cell.Refines ambient) :
    normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample) / 2 -
        variation.scale * coefficientNormSq coefficients * cell.diagonalSq <=
      normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) := by
  have bound := variation.numerator_sub_bound coefficients
    (refines.contains sampleInside) (refines.contains pointInside)
  have coefficientNonnegative : 0 <= coefficientNormSq coefficients :=
    sum_nonnegative _ (fun row => by
        simpa only [Norm.Basic.normSq_eq_canonical]
          using (Norm.Basic.normSq_nonneg (coefficients row)))
  have distanceBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show normSq (sample - point) ≤ cell.diagonalSq from by
      simpa only [Norm.Basic.normSq_eq_canonical] using
        (Box.normSq_sub_le_diagonalSq sampleInside pointInside))
    (Fraction.Order.Arithmetic.mul_nonneg_direct variation.scale_nonnegative coefficientNonnegative)
  have triangle := Norm.Bounds.half_normSq_sub_le_normSq_sub
    ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample)
    ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point)
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  have rearranged : normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample) / 2 -
      normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample -
        (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) <=
      normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) := by
    calc
      _ = (normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample) / 2 -
          normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point)) +
          (normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) -
            normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample -
              (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point)) := by ring1
      _ <= normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample -
          (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) +
          (normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) -
            normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample -
              (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point)) :=
        Fraction.Order.Arithmetic.add_le_add_direct triangle le_rfl
      _ = normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) := by ring1
  exact (Fraction.Order.Arithmetic.sub_le_sub_left_direct
    (bound.trans distanceBound)
    (normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval sample) / 2)).trans rearranged

end NumeratorVariation

end Purelib.Riemann.Integration.PreparedNumeratorVariation
