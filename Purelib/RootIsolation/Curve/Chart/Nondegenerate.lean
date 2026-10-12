module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Projective.Hermitian.Chart.Nondegenerate
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.OfFn.Nodup
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Interval.Unit
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.Rational.Nonzero.Search.Central
import Purelib.Polynomial.Dense.RootBound
import Purelib.RationalFunctions.Curve.Coordinates
import Purelib.RationalFunctions.Curve.Nondegenerate
import Purelib.RationalFunctions.Curve.Substitution
public import Purelib.RationalFunctions.Curve.Substitution.GCD

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RationalFunctions

section
public section

/-!
# Nondegeneracy of the finite CCL boundary charts

Every active curve source is a genuine rational line or a nonzero-radius
circle transported by an invertible finite homography.  Consequently its
homogeneous denominator is a represented nonzero coordinate polynomial, and
its affine values are injective at non-pole parameters.

The final theorem uses only finitely many parameters: one denominator-safe
point in each of `natDegree + 1` disjoint unit intervals.  If both cleared
coordinates vanished identically, these points would give too many distinct
displayed roots of the original Gaussian-rational polynomial.
-/

namespace Purelib.RootIsolation.Curve.Chart

/-- Choose a denominator-safe rational parameter in the indexed open unit interval.

The finite central search uses the chart's nonzero denominator-norm polynomial and its displayed degree. -/
private def safeParameter
    {form : HermitianForm} (chart : BoundedChart form)
    (nondegenerate : chart.Nondegenerate) (index : Nat) : Fraction.Rational :=
  Dense.Rational.Nonzero.Search.Central.centralSearchValue
    (Curve.Coordinates.denominatorNormSq
      chart.parameterization.curve)
    (Curve.Coordinates.denominatorNormSq
      chart.parameterization.curve).natDegree
    (a := (index : Fraction.Rational)) (b := (index : Fraction.Rational) + 1)
    (Data.Rat.Interval.Unit.unitIntervalProper index) nondegenerate.denominatorNormNonzero (by rfl)

open Purelib.RootIsolation
/-- The selected parameter has nonzero curve denominator and lies strictly between its index and successor. -/
private theorem safeParameter_spec
    {form : HermitianForm} (chart : BoundedChart form)
    (nondegenerate : chart.Nondegenerate) (index : Nat) :
    chart.parameterization.curve.denominatorAt
        (safeParameter chart nondegenerate index) ≠ 0 ∧
      (index : Fraction.Rational) < safeParameter chart nondegenerate index ∧
      safeParameter chart nondegenerate index < (index : Fraction.Rational) + 1 := by
  change Curve.RationalCurve.Nondegenerate chart.parameterization.curve at nondegenerate
  have specification := Dense.Rational.Nonzero.Search.Central.centralSearchValue_spec
    (Curve.Coordinates.denominatorNormSq
      chart.parameterization.curve)
    (Curve.Coordinates.denominatorNormSq
      chart.parameterization.curve).natDegree
    (a := (index : Fraction.Rational)) (b := (index : Fraction.Rational) + 1)
    (Data.Rat.Interval.Unit.unitIntervalProper index) nondegenerate.denominatorNormNonzero (by rfl)
  refine ⟨?_, specification.2.1, specification.2.2⟩
  change chart.parameterization.curve.denominatorAt
      (Dense.Rational.Nonzero.Search.Central.centralSearchValue
        (Curve.Coordinates.denominatorNormSq
          chart.parameterization.curve)
        (Curve.Coordinates.denominatorNormSq
          chart.parameterization.curve).natDegree
        (Data.Rat.Interval.Unit.unitIntervalProper index) nondegenerate.denominatorNormNonzero
          (by rfl)) ≠ 0
  intro denominatorZero
  apply specification.1
  rw [Curve.Coordinates.eval_denominatorNormSq]
  exact congrArg Gaussian.Norm.Basic.normSq denominatorZero |>.trans Gaussian.Norm.Basic.normSq_zero

/-- Different natural indices select different denominator-safe parameters. -/
private theorem safeParameter_injective
    {form : HermitianForm} (chart : BoundedChart form)
    (nondegenerate : chart.Nondegenerate) :
    Function.Injective (safeParameter chart nondegenerate) := by
  have strict (left right : Nat) (less : left < right) :
      safeParameter chart nondegenerate left <
        safeParameter chart nondegenerate right := by
    have leftBounds := safeParameter_spec chart nondegenerate left
    have rightBounds := safeParameter_spec chart nondegenerate right
    have separated :
        ((left + 1 : Nat) : Fraction.Rational) ≤ (right : Fraction.Rational) :=
      Fraction.Cast.Order.natCast_le_direct (Nat.succ_le_of_lt less)
    exact (leftBounds.2.2.trans_le separated).trans rightBounds.2.1
  intro left right equal
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro reversed
    have impossible := strict right left reversed
    rewrite [equal] at impossible
    exact lt_irrefl _ impossible
  · apply Nat.le_of_not_lt
    intro forward
    have impossible := strict left right forward
    rewrite [equal] at impossible
    exact lt_irrefl _ impossible

/-- Both denominator-cleared coordinates cannot vanish identically on an
active nondegenerate chart of a positive-degree displayed polynomial. -/
theorem not_identicallyZero
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {form : HermitianForm} (chart : BoundedChart form)
    (nondegenerate : chart.Nondegenerate) :
    ¬ ((Curve.Substitution.realPolynomial p
          chart.parameterization.curve).isZero = true ∧
       (Curve.Substitution.imaginaryPolynomial p
          chart.parameterization.curve).isZero = true) := by
  rintro ⟨realZero, imaginaryZero⟩
  have polynomialNonzero : p.isZero = false :=
    Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive
  let parameter : Fin (p.natDegree + 1) → Fraction.Rational := fun index =>
    safeParameter chart nondegenerate index.val
  let point : Fin (p.natDegree + 1) → Gaussian.Basic.Canonical := fun index =>
    chart.parameterization.curve.point (parameter index)
  have denominatorAt (index : Fin (p.natDegree + 1)) :
      chart.parameterization.curve.denominatorAt (parameter index) ≠ 0 :=
    (safeParameter_spec chart nondegenerate index.val).1
  have pointInjective : Function.Injective point := by
    intro left right equal
    apply Fin.ext
    apply safeParameter_injective chart nondegenerate
    exact nondegenerate.pointInjective (denominatorAt left)
      (denominatorAt right) equal
  let points := List.ofFn point
  have pointsNodup : points.Nodup :=
    Data.List.OfFn.Nodup.nodup_ofFn_of_injective (function := point) pointInjective
  have roots : ∀ value ∈ points, p.eval value = 0 := by
    intro value member
    change value ∈ List.ofFn point at member
    have member := Data.List.OfFn.Basic.mem_ofFn.mp member
    rcases member with ⟨index, rfl⟩
    apply (Curve.cleared_pair_zero_iff p
      chart.parameterization.curve (parameter index)
      (denominatorAt index)).1
    exact ⟨DensePolynomial.eval_eq_zero_of_isZero realZero (parameter index),
      DensePolynomial.eval_eq_zero_of_isZero imaginaryZero (parameter index)⟩
  have tooMany := Dense.RootBound.Roots.nodup_zeros_length_lt_degreeCount
    p polynomialNonzero points pointsNodup roots
  rw [Data.List.OfFn.Basic.length_ofFn,
    DensePolynomial.natDegree_add_one_eq_degreeCount polynomialNonzero] at tooMany
  exact Nat.lt_irrefl p.degreeCount tooMany

end Purelib.RootIsolation.Curve.Chart

end
