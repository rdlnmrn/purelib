module

public import Purelib.Polynomial.Laurent.Normalization
public import Purelib.RootIsolation.Multiplicity.Circle.Comparison
public import Purelib.RationalFunctions.Winding.Circle
import Purelib.Polynomial.Clearance.Circle.LinearFactor
import Purelib.Polynomial.Winding.Circle.Operations
import Purelib.Data.Gaussian.Power
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Independent rational-circle winding of original Laurent symbols

The original normalized polynomial and actual minimal pole-clearing power
supply a retained quotient direction on both complete rational circle charts.
The chart-event procedure computes its winding independently. The original
polynomial argument comparison then gives inside multiplicity minus pole
order, with every original negative-power input guard preserved.
-/

namespace Purelib.Polynomial.Laurent.Circle

open Purelib.Data
open Purelib.Algebra.Field
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.RationalFunctions.Winding.Circle
open Basic (LaurentPolynomial)
open Normalization (Normalized)
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Dense.Gaussian
open Gaussian.Basic (Canonical)
open Rat.Fraction (Rational)
open Purelib.Polynomial.Clearance.Circle (Certificate)
open Purelib.RootIsolation.Multiplicity.Circle renaming Comparison → PolynomialComparison

set_option genInjectivity false in
/-- Retained original quotient paths for one normalized original Laurent expression.

The numerator is its same cached polynomialization. The denominator is the
original finite coordinate power at its actual minimal pole order, with an
automatic exact unit margin. Both cleared denominator charts and all quotient
coordinate products are materialized once from the retained parents.
-/
public structure Substitutions {source : LaurentPolynomial} (normalized : Normalized source)
    (numeratorPaths : Boundary.Substitutions normalized.polynomial) where
  /-- The once-computed actual pole-clearing coordinate power. -/
  denominator : CoefficientPolynomial
  /-- The denominator is the original polynomial power at the same cached pole order. -/
  denominator_eq : denominator = Power.polynomialPower (LinearFactor.linearFactor 0) normalized.poleOrder
  /-- The once-computed original denominator chart substitutions. -/
  denominatorPaths : Boundary.Substitutions denominator
  /-- The denominator paths are the original constructor's complete result. -/
  denominatorPaths_eq : denominatorPaths = Boundary.Substitutions.prepare denominator
  /-- The exact unit denominator margin on the complete rational circle. -/
  denominatorMargin : Certificate denominator
  /-- The margin is the original coordinate-power margin under the retained denominator identity. -/
  denominatorMargin_eq : denominatorMargin = denominator_eq.symm ▸ Certificate.coordinatePower normalized.poleOrder
  /-- The transferred complete denominator chart clearances. -/
  denominatorClearance : Boundary.Clearance denominatorPaths
  /-- The clearances consume the same stored paths and margin. -/
  denominatorClearance_eq : denominatorClearance = denominatorMargin.onBoundary denominatorPaths
  /-- The once-computed original conjugate-denominator quotient coordinates. -/
  quotient : Paths numeratorPaths denominatorPaths
  /-- The quotient consumes the same original numerator and stored denominator paths. -/
  quotient_eq : quotient = Paths.prepare numeratorPaths denominatorPaths

constructive_injectivity Substitutions

namespace Substitutions

/-- Construct actual original quotient coordinates and denominator payments without caller search fuel. -/
@[expose] public def prepare {source : LaurentPolynomial} (normalized : Normalized source)
    (numeratorPaths : Boundary.Substitutions normalized.polynomial) : Substitutions normalized numeratorPaths :=
  let denominator := Power.polynomialPower (LinearFactor.linearFactor 0) normalized.poleOrder
  let denominatorPaths := Boundary.Substitutions.prepare denominator
  let denominatorMargin := Certificate.coordinatePower normalized.poleOrder
  let denominatorClearance := denominatorMargin.onBoundary denominatorPaths
  let quotient := Paths.prepare numeratorPaths denominatorPaths
  { denominator, denominator_eq := rfl, denominatorPaths, denominatorPaths_eq := rfl
    denominatorMargin, denominatorMargin_eq := rfl, denominatorClearance, denominatorClearance_eq := rfl
    quotient, quotient_eq := rfl }

/-- The retained original denominator evaluates to the same actual minimal coordinate power. -/
public theorem denominator_eval {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} (paths : Substitutions normalized numeratorPaths)
    (point : Canonical) : paths.denominator.eval point = point ^ normalized.poleOrder := by
  rw [paths.denominator_eq, Power.eval_polynomialPower, LinearFactor.linearFactor_eval, Gaussian.Basic.sub_zero]

/-- Rational unit-circle points are explicitly apart from zero. -/
public theorem unit_ne_zero {point : Canonical} (unit : point.normSq = 1) : point ≠ 0 := by
  intro zero
  rw [zero, Canonical.normSq_zero] at unit
  exact (by decide : (0 : Rational) ≠ 1) unit

/-- The original Laurent expression keeps its original evaluation guards at every rational unit point. -/
public theorem definedAt {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} (_paths : Substitutions normalized numeratorPaths)
    {point : Canonical} (unit : point.normSq = 1) : source.DefinedAt point :=
  source.definedAt_of_nonzero (unit_ne_zero unit)

/-- The original guarded Laurent value is the actual retained polynomialization divided by its pole-clearing power. -/
public theorem quotient_value {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} (paths : Substitutions normalized numeratorPaths)
    (point : Canonical) (nonzero : point ≠ 0) :
    normalized.polynomial.eval point / paths.denominator.eval point = source.eval point := by
  rw [normalized.polynomial_eval point (source.definedAt_of_nonzero nonzero), paths.denominator_eval]
  rw [Gaussian.Basic.mul_comm (point ^ normalized.poleOrder) (source.eval point)]
  exact ExplicitField.mul_div_cancel_right _ _ (ExplicitField.pow_ne_zero_of_ne_zero nonzero _)

/-- At every explicitly nonzero input, original Laurent zeros are exactly the retained polynomialization zeros. -/
public theorem source_zero_iff {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} (paths : Substitutions normalized numeratorPaths)
    (point : Canonical) (nonzero : point ≠ 0) :
    normalized.polynomial.eval point = 0 ↔ source.eval point = 0 := by
  constructor
  · intro zero
    have value := paths.quotient_value point nonzero
    rw [zero, ExplicitField.div_eq_mul_inv, Gaussian.Basic.zero_mul] at value
    exact value.symm
  · intro zero
    have value := normalized.polynomial_eval point (source.definedAt_of_nonzero nonzero)
    rw [zero, Gaussian.Basic.mul_zero] at value
    exact value

/-- The original primary quotient coordinates have the same exact positive direction as the original guarded symbol. -/
public theorem primary_direction {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} (paths : Substitutions normalized numeratorPaths)
    (parameter : Rational) :
    (⟨paths.quotient.primaryReal.eval parameter, paths.quotient.primaryImaginary.eval parameter⟩ : Canonical) =
      (⟨(parameter ^ 2 + 1) ^ normalized.polynomial.coeffs.length *
        (parameter ^ 2 + 1) ^ paths.denominator.coeffs.length *
        (paths.denominator.eval ((circle 1).point parameter)).normSq, 0⟩ : Canonical) *
        source.eval ((circle 1).point parameter) := by
  rw [paths.quotient.primary_direction paths.denominatorClearance, paths.quotient_value]
  exact unit_ne_zero ((normSq_circle_point 1 parameter).trans Canonical.normSq_one)

/-- The reciprocal quotient coordinates retain the exact direction of the original guarded symbol. -/
public theorem reciprocal_direction {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} (paths : Substitutions normalized numeratorPaths)
    (parameter : Rational) :
    (⟨paths.quotient.reciprocalReal.eval parameter, paths.quotient.reciprocalImaginary.eval parameter⟩ : Canonical) =
      (⟨(parameter ^ 2 + 1) ^ normalized.polynomial.coeffs.length *
        (parameter ^ 2 + 1) ^ paths.denominator.coeffs.length *
        (paths.denominator.eval ((reciprocalCircle 1).point parameter)).normSq, 0⟩ : Canonical) *
        source.eval ((reciprocalCircle 1).point parameter) := by
  rw [paths.quotient.reciprocal_direction paths.denominatorClearance, paths.quotient_value]
  exact unit_ne_zero ((normSq_reciprocalCircle_point 1 parameter).trans Canonical.normSq_one)

/-- The same original denominator chart reading is exactly four times the actual pole order. -/
public theorem denominator_raw {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} (paths : Substitutions normalized numeratorPaths) :
    Winding.Circle.raw paths.denominatorPaths = 4 * (normalized.poleOrder : Int) := by
  let coordinatePaths := Boundary.Substitutions.prepare (LinearFactor.linearFactor 0)
  let powerPaths : Boundary.Substitutions
      (Power.polynomialPower (LinearFactor.linearFactor 0) normalized.poleOrder) :=
    paths.denominator_eq ▸ paths.denominatorPaths
  have power := Winding.Circle.raw_power (Certificate.linearInside 0 (by decide)) coordinatePaths
    normalized.poleOrder powerPaths
  rw [Winding.Circle.raw_coordinate] at power
  calc
    Winding.Circle.raw paths.denominatorPaths = Winding.Circle.raw powerPaths :=
      (Winding.Circle.raw_transport paths.denominator_eq paths.denominatorPaths).symm
    _ = (normalized.poleOrder : Int) * 4 := power
    _ = 4 * (normalized.poleOrder : Int) := by ring1

end Substitutions

set_option genInjectivity false in
/-- An independent original Laurent winding compared with the complete original polynomial root inventory.

The same polynomial boundary paths remain indexed throughout. Its original
argument comparison and the Laurent quotient paths are built once. The
quotient phase procedure independently computes the original symbol winding;
only afterward is it proved equal to inside multiplicity minus pole order.
-/
public structure Comparison {source : LaurentPolynomial} (normalized : Normalized source)
    (numeratorPaths : Boundary.Substitutions normalized.polynomial)
    (clearance : Boundary.Clearance numeratorPaths) where
  /-- The once-computed original polynomial argument-principle comparison. -/
  polynomial : PolynomialComparison numeratorPaths clearance
  /-- The polynomial comparison is the same automatic constructor on the cached polynomialization. -/
  polynomial_eq : polynomial = PolynomialComparison.prepare numeratorPaths clearance
    normalized.polynomial_normalized
  /-- The once-computed actual quotient paths and denominator payments. -/
  paths : Substitutions normalized numeratorPaths
  /-- The paths are the same original automatic quotient construction. -/
  paths_eq : paths = Substitutions.prepare normalized numeratorPaths
  /-- The independent original quotient chart-event phase reading. -/
  reading : Reading paths.quotient clearance paths.denominatorClearance
  /-- The reading is the original independent phase constructor on those same cached products. -/
  reading_eq : reading = Reading.prepare paths.quotient clearance paths.denominatorClearance
  /-- The independent Laurent winding is the original inside multiplicity minus its actual minimal pole order. -/
  winding_eq : reading.winding = (polynomial.inventory.insideCount : Int) - (normalized.poleOrder : Int)

constructive_injectivity Comparison

namespace Comparison

/-- Retain complete original polynomial comparison, quotient paths and independent Laurent reading caches. -/
@[expose] public def ofCaches {source : LaurentPolynomial} (normalized : Normalized source)
    (numeratorPaths : Boundary.Substitutions normalized.polynomial)
    (clearance : Boundary.Clearance numeratorPaths)
    (polynomial : PolynomialComparison numeratorPaths clearance)
    (polynomialEq : polynomial = PolynomialComparison.prepare numeratorPaths clearance
      normalized.polynomial_normalized)
    (paths : Substitutions normalized numeratorPaths)
    (pathsEq : paths = Substitutions.prepare normalized numeratorPaths)
    (reading : Reading paths.quotient clearance paths.denominatorClearance)
    (readingEq : reading = Reading.prepare paths.quotient clearance paths.denominatorClearance) :
    Comparison normalized numeratorPaths clearance :=
  { polynomial, polynomial_eq := polynomialEq, paths, paths_eq := pathsEq, reading, reading_eq := readingEq
    winding_eq := by
      have equal := (reading.raw_eq.symm.trans
        (raw_eq_sub paths.quotient clearance paths.denominatorClearance)).trans
        (congrArg₂ (fun numerator denominator : Int => numerator - denominator)
          polynomial.raw_eq paths.denominator_raw)
      exact Purelib.Data.Int.Arithmetic.eq_of_mul_eq_mul_left (by decide : (4 : Int) ≠ 0)
        (equal.trans (by ring1)) }

/-- Extend one retained complete original polynomial comparison with the actual Laurent quotient reading.

Only the original denominator and quotient chart caches are prepared. The
retained polynomial inventory, isolation, locations and arguments are reused.
-/
@[expose] public def ofPolynomial {source : LaurentPolynomial} (normalized : Normalized source)
    (numeratorPaths : Boundary.Substitutions normalized.polynomial)
    (clearance : Boundary.Clearance numeratorPaths)
    (polynomial : PolynomialComparison numeratorPaths clearance)
    (polynomialEq : polynomial = PolynomialComparison.prepare numeratorPaths clearance
      normalized.polynomial_normalized) : Comparison normalized numeratorPaths clearance :=
  let paths := Substitutions.prepare normalized numeratorPaths
  let reading := Reading.prepare paths.quotient clearance paths.denominatorClearance
  ofCaches normalized numeratorPaths clearance polynomial polynomialEq paths rfl reading rfl

/-- Construct the original independent Laurent winding and complete polynomial-root comparison internally. -/
@[expose] public def prepare {source : LaurentPolynomial} (normalized : Normalized source)
    (numeratorPaths : Boundary.Substitutions normalized.polynomial)
    (clearance : Boundary.Clearance numeratorPaths) : Comparison normalized numeratorPaths clearance :=
  let polynomial := PolynomialComparison.prepare numeratorPaths clearance
    normalized.polynomial_normalized
  ofPolynomial normalized numeratorPaths clearance polynomial rfl

/-- A checked complete polynomial comparison recovers the same original automatic Laurent construction. -/
public theorem ofPolynomial_eq_prepare {source : LaurentPolynomial} (normalized : Normalized source)
    (numeratorPaths : Boundary.Substitutions normalized.polynomial)
    (clearance : Boundary.Clearance numeratorPaths)
    (polynomial : PolynomialComparison numeratorPaths clearance)
    (polynomialEq : polynomial = PolynomialComparison.prepare numeratorPaths clearance
      normalized.polynomial_normalized) :
    ofPolynomial normalized numeratorPaths clearance polynomial polynomialEq =
      prepare normalized numeratorPaths clearance := by
  cases polynomialEq
  rfl

/-- Checked complete quotient caches restore the original automatic Laurent comparison. -/
public theorem ofCaches_eq_prepare {source : LaurentPolynomial} (normalized : Normalized source)
    (numeratorPaths : Boundary.Substitutions normalized.polynomial)
    (clearance : Boundary.Clearance numeratorPaths)
    (polynomial : PolynomialComparison numeratorPaths clearance)
    (polynomialEq : polynomial = PolynomialComparison.prepare numeratorPaths clearance
      normalized.polynomial_normalized)
    (paths : Substitutions normalized numeratorPaths)
    (pathsEq : paths = Substitutions.prepare normalized numeratorPaths)
    (reading : Reading paths.quotient clearance paths.denominatorClearance)
    (readingEq : reading = Reading.prepare paths.quotient clearance paths.denominatorClearance) :
    ofCaches normalized numeratorPaths clearance polynomial polynomialEq paths pathsEq reading readingEq =
      prepare normalized numeratorPaths clearance := by
  cases polynomialEq
  cases pathsEq
  cases readingEq
  rfl

/-- Restore the complete original Laurent circle comparison from its same polynomial and quotient caches. -/
public theorem restore {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance numeratorPaths}
    (comparison : Comparison normalized numeratorPaths clearance) :
    comparison = prepare normalized numeratorPaths clearance := by
  cases comparison with
  | mk polynomial polynomialEq paths pathsEq reading readingEq windingEq =>
      cases polynomialEq
      cases pathsEq
      cases readingEq
      rfl

/-- The retained whole-boundary certificate proves nonvanishing of the same original Laurent expression. -/
public theorem source_nonzero {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance numeratorPaths}
    (comparison : Comparison normalized numeratorPaths clearance) {point : Canonical} (unit : point.normSq = 1) :
    source.eval point ≠ 0 := by
  intro zero
  exact comparison.polynomial.margin.toCertificate.eval_ne unit
    ((comparison.paths.source_zero_iff point (Substitutions.unit_ne_zero unit)).mpr zero)

/-- The signed pole-minus-inside boundary index is the negative of the independently computed symbol winding. -/
public theorem index_eq_neg_winding {source : LaurentPolynomial} {normalized : Normalized source}
    {numeratorPaths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance numeratorPaths}
    (comparison : Comparison normalized numeratorPaths clearance) :
    (normalized.poleOrder : Int) - (comparison.polynomial.inventory.insideCount : Int) =
      -comparison.reading.winding := by
  rw [comparison.winding_eq]
  ring1

end Comparison
end Purelib.Polynomial.Laurent.Circle
