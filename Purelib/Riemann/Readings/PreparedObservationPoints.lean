module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.DropWhile.Basic
-- The exposed bank extension retains the original membership certificates.
public import Purelib.Data.List.Membership
import Purelib.Data.List.Reverse
import Purelib.Data.List.OfFn.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Polynomial.Dense.RootBound
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplication
import Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Geometry.EvaluationLower
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Automatic finite observation points for raw differential coercivity

The observation bank depends only on the curve and its requested finite size,
not on a differential coefficient vector.  Each new point is found by the
existing bounded nonzero-evaluation algorithm applied to a cached avoidance
polynomial.  Multiplying by one linear factor excludes the new point from all
subsequent choices.  Thus all observations are distinct and clear of the curve
denominator, without a successful-search premise or a carrier-wide root set.

The finite root-count theorem then proves that this fixed bank detects every
nonzero standard differential combination.  Quantitative interpolation and
the conversion of the observations to surface boxes are subsequent steps.
-/

namespace Purelib.Riemann.Readings.PreparedObservationPoints

open Purelib.Data.List

open Purelib.Data in
/-- The executable Gaussian rational scalar type. -/
abbrev Gaussian := Gaussian.Basic.Canonical
open Purelib.Polynomial in
/-- The dense Gaussian polynomial type used for observation constraints. -/
abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

open Purelib.Polynomial.Dense.Basic.DensePolynomial

set_option genInjectivity false in
/-- Distinct finite observations away from a polynomial's zeros, with a cached exclusion polynomial.

The retained avoidance polynomial vanishes at every existing observation. A point where it is nonzero is both fresh and
clear of the original denominator. -/
structure ObservationBank (polynomial : GaussianPolynomial) (count : Nat) where
  /-- The ordered list of retained Gaussian observation points. -/ points : List Gaussian
  /-- The retained point list has the indexed observation count. -/ length_eq : points.length = count
  /-- The retained observations contain no repeated point. -/ distinct : points.Nodup
  /-- The original denominator is nonzero at every retained observation. -/ denominator_nonzero : forall point, point ∈
    points -> polynomial.eval point ≠ 0
  /-- The cached polynomial used to select a fresh admissible observation. -/ avoidance : GaussianPolynomial
  /-- The cached avoidance polynomial is nonzero. -/ avoidance_nonzero : avoidance.isZero = false
  /-- Every retained observation is a zero of the cached avoidance polynomial. -/ avoidance_zero : forall point, point ∈
    points -> avoidance.eval point = 0
  /-- Nonvanishing of the avoidance polynomial implies nonvanishing of the original denominator. -/ avoidance_clear :
    forall point, avoidance.eval point ≠ 0 -> polynomial.eval point ≠ 0

constructive_injectivity ObservationBank

/-- The monic linear polynomial whose unique zero is the supplied observation. -/
def exclusionFactor (point : Gaussian) : GaussianPolynomial := ⟨[1, -point]⟩

open Purelib.Polynomial in
/-- The linear exclusion factor is a nonzero dense polynomial.

Its original coefficient list starts with one. The retained Boolean
normalization scan therefore keeps that nonzero head and the complete list. -/
theorem exclusionFactor_nonzero (point : Gaussian) :
    (exclusionFactor point).isZero = false := by
  change ([1, -point].dropWhile (fun value : Gaussian => decide (value = 0))).isEmpty = false
  exact congrArg (fun values : List Gaussian => values.isEmpty)
    (DropWhile.cons_of_false (fun value : Gaussian => decide (value = 0)) 1 [-point] (by decide))

/-- Evaluating the exclusion factor subtracts its retained root from the argument. -/
theorem exclusionFactor_eval (point value : Gaussian) :
    (exclusionFactor point).eval value = value - point := by
  change (0 * value + 1) * value + -point = value - point
  ring1

namespace ObservationBank

variable {polynomial : GaussianPolynomial} {count : Nat}

/-- Read an observation using the bank's retained length equality and finite index bound. -/
def pointAt (bank : ObservationBank polynomial count) (index : Fin count) : Gaussian :=
  bank.points[index.val]'(by rw [bank.length_eq]; exact index.isLt)

/-- Every indexed observation belongs to the retained point list. -/
theorem pointAt_mem (bank : ObservationBank polynomial count) (index : Fin count) :
    bank.pointAt index ∈ bank.points := List.getElem_mem _

/-- Every point in the retained list has a finite observation index. -/
theorem exists_pointAt_of_mem (bank : ObservationBank polynomial count)
    {point : Gaussian} (member : point ∈ bank.points) :
    exists index : Fin count, bank.pointAt index = point := by
  rcases List.mem_iff_getElem.mp member with ⟨index, bound, equal⟩
  exact ⟨⟨index, by rw [← bank.length_eq]; exact bound⟩, equal⟩

/-- Construct the empty observation bank with the original nonzero polynomial as its avoidance cache. -/
def empty (polynomial : GaussianPolynomial) (nonzero : polynomial.isZero = false) :
    ObservationBank polynomial 0 where
  points := []
  length_eq := rfl
  distinct := List.nodup_nil
  denominator_nonzero := by intro point member; exact (List.not_mem_nil member).elim
  avoidance := polynomial
  avoidance_nonzero := nonzero
  avoidance_zero := by intro point member; exact (List.not_mem_nil member).elim
  avoidance_clear := fun _ clear => clear

open Purelib.Polynomial in
/-- Prepend one fresh observation chosen by finite nonzero polynomial evaluation.

Multiply the previous avoidance cache by the new point's linear exclusion factor, retaining distinctness, denominator
clearance and the exact avoidance implications. -/
def extend (bank : ObservationBank polynomial count) :
    ObservationBank polynomial (count + 1) := by
  let evaluation := Dense.Gaussian.NonzeroEvaluation.findNonzeroEvaluation
    bank.avoidance bank.avoidance_nonzero
  have fresh : evaluation.point ∉ bank.points := by
    intro member
    exact evaluation.valueNonzero (bank.avoidance_zero evaluation.point member)
  let nextAvoidance := exclusionFactor evaluation.point * bank.avoidance
  refine
    { points := evaluation.point :: bank.points
      length_eq := congrArg Nat.succ bank.length_eq
      distinct := List.Pairwise.cons
        (fun point member equal => fresh (equal.symm ▸ member)) bank.distinct
      denominator_nonzero := ?_
      avoidance := nextAvoidance
      avoidance_nonzero := Dense.Gaussian.Multiplication.product_isZero_false
        (exclusionFactor_nonzero evaluation.point) bank.avoidance_nonzero
      avoidance_zero := ?_
      avoidance_clear := ?_ }
  · intro point member
    rcases Membership.mem_cons.mp member with rfl | oldMember
    · exact bank.avoidance_clear evaluation.point evaluation.valueNonzero
    · exact bank.denominator_nonzero point oldMember
  · intro point member
    rw [show nextAvoidance.eval point =
      (exclusionFactor evaluation.point).eval point * bank.avoidance.eval point from
      Dense.Basic.DensePolynomial.eval_mul _ _ _]
    rcases Membership.mem_cons.mp member with rfl | oldMember
    · rw [exclusionFactor_eval, sub_self, zero_mul]
    · rw [bank.avoidance_zero point oldMember, mul_zero]
  · intro point clear
    apply bank.avoidance_clear point
    intro oldZero
    apply clear
    change (exclusionFactor evaluation.point * bank.avoidance).eval point = 0
    rw [Dense.Basic.DensePolynomial.eval_mul, oldZero, mul_zero]

/-- Construct the requested finite number of distinct admissible observations.

Repeated extension consumes the retained avoidance polynomial and certificates. Selection depends only on the
denominator and count, independently of any coefficient vector. -/
def build (polynomial : GaussianPolynomial) (nonzero : polynomial.isZero = false) :
    (count : Nat) -> ObservationBank polynomial count
  | 0 => empty polynomial nonzero
  | count + 1 => (build polynomial nonzero count).extend

open Purelib.Polynomial in
/-- A polynomial vanishing at sufficiently many retained observations is zero.

The observation count is at least its coefficient count; distinctness and the finite root bound force the conclusion. -/
theorem polynomial_zero_of_evaluations_zero
    (bank : ObservationBank polynomial count) (numerator : GaussianPolynomial)
    (degreeBound : numerator.degreeCount <= count)
    (zeros : forall point, point ∈ bank.points -> numerator.eval point = 0) :
    numerator.isZero = true := by
  cases nonzero : numerator.isZero with
  | true => rfl
  | false =>
      have tooMany := Dense.RootBound.Roots.nodup_zeros_length_lt_degreeCount
        numerator nonzero bank.points bank.distinct zeros
      rw [bank.length_eq] at tooMany
      exact (not_lt_of_ge degreeBound tooMany).elim

end ObservationBank

open Purelib.Curves in
/-- Construct a genus-sized observation bank away from the curve's defining polynomial zeros.

This fixed bank depends on the admissible curve and is shared by all vectors of standard differential coefficients. -/
def curveObservations {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    ObservationBank curve.polynomial genus :=
  ObservationBank.build curve.polynomial curve.nonzero genus

section
open Purelib.Polynomial
open Purelib.LinearAlgebra
/-- The coefficient polynomial of a genus-sized vector has at most genus coefficient slots.

The original List.ofFn table has exactly genus entries and reversal preserves
its length. Removing its initial zero prefix can only decrease that same count. -/
theorem coefficientPolynomial_degreeCount_le {genus : Nat}
    (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    (Geometry.EvaluationLower.coefficientPolynomial coefficients).degreeCount <= genus := by
  change ((List.ofFn coefficients).reverse.dropWhile (· = 0)).length <= genus
  exact (DropWhile.length_le (fun value : Gaussian => decide (value = 0))
    (List.ofFn coefficients).reverse).trans_eq (by
      rw [Reverse.length_reverse, OfFn.Basic.length_ofFn])

/-- Vanishing at every retained observation forces every differential coefficient to vanish.

The genus-sized bank separates coefficient polynomials through its distinct points and their retained finite root bound.
-/
theorem ObservationBank.coefficients_zero_of_evaluations_zero {genus : Nat}
    {polynomial : GaussianPolynomial} (bank : ObservationBank polynomial genus)
    (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (zeros : forall point, point ∈ bank.points ->
      (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point = 0) :
    forall row, coefficients row = 0 := by
  have polynomialZero := bank.polynomial_zero_of_evaluations_zero
    (Geometry.EvaluationLower.coefficientPolynomial coefficients)
    (coefficientPolynomial_degreeCount_le coefficients) zeros
  intro row
  by_cases zero : coefficients row = 0
  · exact zero
  · have polynomialNonzero := Geometry.EvaluationLower.coefficientPolynomial_nonzero
      (coefficients := coefficients) ⟨row, zero⟩
    rw [polynomialZero] at polynomialNonzero
    exact Bool.noConfusion polynomialNonzero

end

open Purelib.Curves in
open Purelib.Polynomial in
open Purelib.LinearAlgebra in
/-- The automatic curve observation bank separates every standard differential coefficient vector. -/
theorem coefficients_zero_of_observations_zero {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (coefficients : Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (zeros : forall point, point ∈ (curveObservations curve).points ->
      (Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point = 0) :
    forall row, coefficients row = 0 :=
  (curveObservations curve).coefficients_zero_of_evaluations_zero coefficients zeros

end Purelib.Riemann.Readings.PreparedObservationPoints
