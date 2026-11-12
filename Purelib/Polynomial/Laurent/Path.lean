module

public import Purelib.Polynomial.Laurent.Polynomialization
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
public import Purelib.Data.Gaussian.Cast
public import Purelib.Data.List.DependentProduct
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Power
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite Laurent coefficient paths

Original signed exponents retain their order and occurrences. Each coefficient
is an original finite Gaussian polynomial in a rational parameter. Cached
original Horner folds provide a uniform finite squared-variation budget;
vanishing coefficients do not change the displayed source-domain guards.
-/

namespace Purelib.Polynomial.Laurent

open Purelib.Data
open Purelib.Polynomial.Laurent.Basic (LaurentTerm LaurentPolynomial)
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Gaussian.Basic (Canonical)
open Rat.Fraction (Rational)
open Rat.Fraction.Order
open Purelib.Algebra.FiniteSum.Rational

namespace Path

set_option genInjectivity false in
/-- One original signed exponent with a finite Gaussian-polynomial coefficient path. -/
public structure Term where
  /-- The original finite coefficient polynomial in the rational parameter. -/
  coefficient : CoefficientPolynomial
  /-- The original signed exponent, retained even when its coefficient vanishes. -/
  exponent : Data.Int.Exponent

constructive_injectivity Term

/-- A rational parameter lies between the two retained unit-cell endpoints. -/
@[expose] public def Parameter (value : Rational) : Prop := 0 ≤ value ∧ value ≤ 1

namespace Term

/-- Specialize the coefficient once into the original Laurent term owner. -/
@[expose] public def specialize (term : Term) (parameter : Rational) : LaurentTerm :=
  ⟨term.coefficient.eval (Gaussian.Cast.Path.ofCoordinate parameter), term.exponent⟩

/-- The original radius-one paired Horner fold for this same coefficient polynomial. -/
@[expose] public def horner (term : Term) : Polynomial.Bounds.Horner :=
  term.coefficient.coeffs.foldl (Dense.Gaussian.Bounds.Horner.step 1) ⟨0, 0⟩

set_option genInjectivity false in
/-- A cached original coefficient-path Horner fold with its exact constructor equation. -/
public structure Prepared (term : Term) where
  /-- The once-computed original value/slope pair. -/
  bounds : Polynomial.Bounds.Horner
  /-- The cache is the complete original coefficient fold. -/
  bounds_eq : bounds = term.horner

constructive_injectivity Prepared

/-- Compute the original coefficient-path bound pair once. -/
@[expose] public def prepare (term : Term) : Prepared term := ⟨term.horner, rfl⟩

/-- A unit-cell parameter has real-axis Gaussian quadrance at most one. -/
private theorem parameter_norm_le {parameter : Rational} (inside : Parameter parameter) :
    Gaussian.Norm.Basic.normSq (Gaussian.Cast.Path.ofCoordinate parameter) ≤ 1 := by
  have square := Arithmetic.mul_le_mul_direct inside.2 inside.2 inside.1 (by decide : (0 : Rational) ≤ 1)
  change parameter ^ 2 + 0 ^ 2 ≤ 1
  rewrite [show parameter ^ 2 + 0 ^ 2 = parameter * parameter by ring1]
  exact square.trans_eq (by decide)

/-- The actual original coefficient fold has nonnegative value and slope components. -/
public theorem Prepared.nonnegative {term : Term} (prepared : Prepared term) :
    0 ≤ prepared.bounds.value ∧ 0 ≤ prepared.bounds.slope := by
  have specification := Dense.Gaussian.Bounds.Horner.evalNormBoundsCoeffs_spec term.coefficient.coeffs
    (radiusSq := 1) (x := 0) (y := 0) (by decide) (by decide) (by decide) 0 0 ⟨0, 0⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rewrite [prepared.bounds_eq]
  exact ⟨specification.1, specification.2.1⟩

/-- The cached original slope bounds squared coefficient variation throughout the unit parameter cell. -/
public theorem Prepared.variation {term : Term} (prepared : Prepared term)
    {left right : Rational} (leftInside : Parameter left) (rightInside : Parameter right) :
    Gaussian.Norm.Basic.normSq ((term.specialize left).coefficient - (term.specialize right).coefficient) ≤
      prepared.bounds.slope * (left - right) ^ 2 := by
  have specification := Dense.Gaussian.Bounds.Horner.evalNormBoundsCoeffs_spec term.coefficient.coeffs
    (radiusSq := 1) (x := Gaussian.Cast.Path.ofCoordinate left) (y := Gaussian.Cast.Path.ofCoordinate right)
    (by decide) (parameter_norm_le leftInside) (parameter_norm_le rightInside) 0 0 ⟨0, 0⟩
    (by decide) (by decide) (by decide) (by decide) (by
      rewrite [Gaussian.Basic.sub_self, Gaussian.Norm.Basic.normSq_zero, Rat.Fraction.Field.zero_mul_direct]
      exact Rat.Fraction.Order.Basic.le_refl _)
  have variation := specification.2.2.2.2
  change Gaussian.Norm.Basic.normSq
    ((term.specialize left).coefficient - (term.specialize right).coefficient) ≤
      term.horner.slope * Gaussian.Norm.Basic.normSq
        (Gaussian.Cast.Path.ofCoordinate left - Gaussian.Cast.Path.ofCoordinate right) at variation
  have distance : Gaussian.Norm.Basic.normSq
      (Gaussian.Cast.Path.ofCoordinate left - Gaussian.Cast.Path.ofCoordinate right) = (left - right) ^ 2 := by
    change (left - right) ^ 2 + (0 - 0) ^ 2 = (left - right) ^ 2
    ring1
  rewrite [← prepared.bounds_eq, distance] at variation
  exact variation

end Term
end Path

set_option genInjectivity false in
/-- An ordered finite Laurent coefficient path on one rational parameter cell.

Repeated signed exponents and zero coefficient occurrences remain in the same
original term list. The actual normalized support may vary with the parameter.
-/
public structure Path where
  /-- The finite original coefficient-polynomial/exponent occurrences. -/
  terms : List Purelib.Polynomial.Laurent.Path.Term

constructive_injectivity Path

namespace Path

/-- Construct the original Laurent expression at the displayed rational parameter. -/
@[expose] public def symbol (path : Path) (parameter : Rational) : LaurentPolynomial :=
  ⟨path.terms.map (fun term => term.specialize parameter)⟩

/-- Retain the same original exponent syntax with zero coefficients to compute its common raw shift. -/
@[expose] public def shape (path : Path) : LaurentPolynomial :=
  ⟨path.terms.map (fun term => ⟨0, term.exponent⟩)⟩

/-- Specialization preserves the exact original displayed negative-exponent bound. -/
public theorem rawShift_symbol (path : Path) (parameter : Rational) :
    (path.symbol parameter).rawShift = path.shape.rawShift := by
  cases path with
  | mk terms =>
      induction terms with
      | nil => rfl
      | cons head tail inductionHypothesis =>
          change Nat.max head.exponent.negativeMagnitude
              (LaurentPolynomial.rawShiftTerms (tail.map (fun term => term.specialize parameter))) =
            Nat.max head.exponent.negativeMagnitude
              (LaurentPolynomial.rawShiftTerms (tail.map (fun term => ⟨0, term.exponent⟩)))
          exact congrArg (Nat.max head.exponent.negativeMagnitude) inductionHypothesis

/-- Original cached Horner bounds at every bounded coefficient-path occurrence. -/
public abbrev BoundsBank (terms : List Term) :=
  List.DependentProduct terms (fun index => Term.Prepared (terms.get index))

/-- Read each same retained original slope in its original occurrence order. -/
@[expose] public def slopes (terms : List Term) (entries : BoundsBank terms) : List Rational :=
  List.ofFn (fun index => (List.DependentProduct.get terms entries index).bounds.slope)

set_option genInjectivity false in
/-- A prepared coefficient path retaining the original folds and a common finite variation coefficient. -/
public structure Prepared (path : Path) where
  /-- The same displayed exponent syntax determines the common polynomializing shift. -/
  shift : Nat
  /-- The common shift uses the original raw-shift constructor. -/
  shift_eq : shift = path.shape.rawShift
  /-- Every coefficient occurrence retains its once-computed original Horner fold. -/
  entries : BoundsBank path.terms
  /-- The bank is the original materialization of the coefficient-bound constructor. -/
  entries_eq : entries = List.DependentProduct.ofFn path.terms (fun index => (path.terms.get index).prepare)
  /-- The once-materialized ordered slope table from the same stored bank. -/
  slopeTable : List Rational
  /-- The slope table only reads the retained original bound entries. -/
  slopeTable_eq : slopeTable = slopes path.terms entries
  /-- The original finite scalar sum of those retained slopes. -/
  slopeSum : Rational
  /-- The sum consumes the same retained ordered table. -/
  slopeSum_eq : slopeSum = Squares.coordinateSum slopeTable
  /-- The cached coefficient multiplying squared parameter differences. -/
  coefficient : Rational
  /-- Finite Cauchy--Schwarz pays the original term count times the slope sum. -/
  coefficient_eq : coefficient = (path.terms.length : Rational) * slopeSum

constructive_injectivity Prepared

/-- Prepare every original coefficient-path bound once and retain its common variation payment. -/
@[expose] public def prepare (path : Path) : Prepared path :=
  let entries := List.DependentProduct.ofFn path.terms (fun index => (path.terms.get index).prepare)
  let slopeTable := slopes path.terms entries
  let slopeSum := Squares.coordinateSum slopeTable
  { shift := path.shape.rawShift, shift_eq := rfl, entries, entries_eq := rfl
    slopeTable, slopeTable_eq := rfl, slopeSum, slopeSum_eq := rfl
    coefficient := (path.terms.length : Rational) * slopeSum, coefficient_eq := rfl }

/-- Reading a nonempty retained slope table exposes its same cached head and tail. -/
private theorem slopes_cons (head : Term) (tail : List Term) (entries : BoundsBank (head :: tail)) :
    slopes (head :: tail) entries = entries.1.bounds.slope :: slopes tail entries.2 := by
  unfold slopes
  rewrite [List.OfFn.Basic.ofFn_succ]
  rfl

/-- The scalar sum of the same cached original coefficient slopes is nonnegative. -/
private theorem slopes_nonnegative : (terms : List Term) → (entries : BoundsBank terms) →
    0 ≤ Squares.coordinateSum (slopes terms entries)
  | [], _ => Rat.Fraction.Order.Basic.le_refl _
  | head :: tail, entries => by
      rewrite [slopes_cons]
      exact add_nonneg entries.1.nonnegative.2 (slopes_nonnegative tail entries.2)

/-- The retained finite variation coefficient is nonnegative, including an empty path. -/
public theorem Prepared.nonnegative {path : Path} (prepared : Prepared path) :
    0 ≤ prepared.coefficient := by
  rewrite [prepared.coefficient_eq, prepared.slopeSum_eq, prepared.slopeTable_eq]
  exact Arithmetic.mul_nonneg_direct (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _))
    (slopes_nonnegative path.terms prepared.entries)

/-- The original polynomialized term recursion evaluates to the same ordered Gaussian sum. -/
private theorem polynomialize_eval (terms : List Term) (parameter : Rational) (shift : Nat)
    (point : Canonical) :
    (LaurentPolynomial.polynomializeTerms shift (terms.map (fun term => term.specialize parameter))).eval point =
      Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term =>
        (term.specialize parameter).coefficient * point ^ term.exponent.shifted shift)) := by
  induction terms with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change (Dense.Basic.DensePolynomial.shift (head.exponent.shifted shift)
          (Dense.Basic.DensePolynomial.constant (head.specialize parameter).coefficient) +
        LaurentPolynomial.polynomializeTerms shift (tail.map (fun term => term.specialize parameter))).eval point = _
      rewrite [Dense.Basic.DensePolynomial.eval_add, Dense.Basic.DensePolynomial.eval_shift,
        Dense.Basic.DensePolynomial.eval_constant, inductionHypothesis]
      rfl

/-- The retained common polynomialization reads exactly the original coefficient-path values. -/
public theorem polynomialized_eval (path : Path) (parameter : Rational) (shift : Nat)
    (point : Canonical) :
    ((path.symbol parameter).polynomialize shift).eval point =
      Gaussian.Norm.Sum.Basic.gaussianSum (path.terms.map (fun term =>
        (term.specialize parameter).coefficient * point ^ term.exponent.shifted shift)) :=
  polynomialize_eval path.terms parameter shift point

/-- A unit-circle power preserves the original coefficient difference's squared norm. -/
private theorem weighted_variation (term : Term) (prepared : Term.Prepared term)
    {left right : Rational} (leftInside : Parameter left) (rightInside : Parameter right)
    (point : Canonical) (unit : Gaussian.Norm.Basic.normSq point = 1) (shift : Nat) :
    Gaussian.Norm.Basic.normSq
        ((term.specialize left).coefficient * point ^ term.exponent.shifted shift -
          (term.specialize right).coefficient * point ^ term.exponent.shifted shift) ≤
      prepared.bounds.slope * (left - right) ^ 2 := by
  rewrite [show (term.specialize left).coefficient * point ^ term.exponent.shifted shift -
      (term.specialize right).coefficient * point ^ term.exponent.shifted shift =
      ((term.specialize left).coefficient - (term.specialize right).coefficient) *
        point ^ term.exponent.shifted shift by ring1,
    Gaussian.Norm.Basic.normSq_mul, Gaussian.Power.normSq_pow, unit,
    one_pow, Rat.Fraction.Field.mul_one_direct]
  exact prepared.variation leftInside rightInside

/-- The same retained coefficient folds bound the sum of all weighted squared differences. -/
private theorem weighted_sum_le (terms : List Term) (entries : BoundsBank terms)
    {left right : Rational} (leftInside : Parameter left) (rightInside : Parameter right)
    (point : Canonical) (unit : Gaussian.Norm.Basic.normSq point = 1) (shift : Nat) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (terms.map (fun term =>
        (term.specialize left).coefficient * point ^ term.exponent.shifted shift -
          (term.specialize right).coefficient * point ^ term.exponent.shifted shift)) ≤
      Squares.coordinateSum (slopes terms entries) * (left - right) ^ 2 := by
  induction terms with
  | nil =>
      change (0 : Rational) ≤ 0 * (left - right) ^ 2
      rewrite [Rat.Fraction.Field.zero_mul_direct]
      exact Rat.Fraction.Order.Basic.le_refl _
  | cons head tail inductionHypothesis =>
      rewrite [slopes_cons, List.map_cons, Gaussian.Norm.Sum.Basic.gaussianNormSqSum,
        ← Gaussian.Norm.Basic.normSq_eq_canonical, Squares.coordinateSum]
      have combined := Arithmetic.add_le_add_direct
        (weighted_variation head entries.1 leftInside rightInside point unit shift)
        (inductionHypothesis entries.2)
      exact combined.trans_eq (by ring1)

/-- The cached finite coefficient bounds variation of every common numerator on the whole rational unit circle.

The same original ordered coefficient occurrences supply both evaluations.
Unit powers preserve their squared differences, and finite Gaussian
Cauchy--Schwarz combines their cached original Horner bounds.
-/
public theorem Prepared.variation {path : Path} (prepared : Prepared path)
    {left right : Rational} (leftInside : Parameter left) (rightInside : Parameter right)
    (point : Canonical) (unit : Gaussian.Norm.Basic.normSq point = 1) (shift : Nat) :
    Gaussian.Norm.Basic.normSq
        (((path.symbol left).polynomialize shift).eval point -
          ((path.symbol right).polynomialize shift).eval point) ≤
      prepared.coefficient * (left - right) ^ 2 := by
  rewrite [path.polynomialized_eval, path.polynomialized_eval,
    ← Gaussian.Norm.Sum.Basic.gaussianSum_map_sub]
  have sumBound := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le (path.terms.map (fun term =>
    (term.specialize left).coefficient * point ^ term.exponent.shifted shift -
      (term.specialize right).coefficient * point ^ term.exponent.shifted shift))
  rewrite [List.Map.length_map, ← Gaussian.Norm.Basic.normSq_eq_canonical] at sumBound
  have bounded := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (weighted_sum_le path.terms prepared.entries leftInside rightInside point unit shift)
    (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le path.terms.length))
  apply sumBound.trans
  apply bounded.trans_eq
  rewrite [prepared.coefficient_eq, prepared.slopeSum_eq, prepared.slopeTable_eq]
  ring1

end Path
end Purelib.Polynomial.Laurent
