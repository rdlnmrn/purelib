module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.EvaluationLower

public import Purelib.Riemann.Readings.PreparedObservationSeparation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Riemann.Readings.PreparedObservationInterpolation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.PreparedObservationPoints
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedNumeratorVariation
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Uniform coercivity on automatically separated observation boxes

The fixed observation bank is thickened using one common positive radius.
Denominator clearance, pairwise separation, and the total numerator variation
are all paid before a coefficient vector is requested.  Clamping signed local
lower bounds to zero then retains a uniform positive fraction of the finite
interpolation bound.
-/

namespace Purelib.Riemann.Readings.PreparedObservationBoxes

open Purelib.Data.Rat.Fraction

open Purelib.Riemann.Readings.PreparedObservationCoercivity (Coordinate ObservationCoercivity coefficientNormSq
  curveObservationCoercivity)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Readings.PreparedObservationCoercivity (observationNormSq)
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood variationRadius
  variationRadius_positive variationRadius_le_one variation_error_le_quarter centeredBox_proper half_sub_quarter)
open Purelib.Riemann.Readings.PreparedObservationSeparation (minimumRadius minimumRadius_positive minimumRadius_le)
open Purelib.Geometry.Rational (Box)

open Purelib.LinearAlgebra
open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Algebra
/-- A finite rational sum of nonnegative entries is nonnegative. -/
private theorem sum_nonnegative {count : Nat} (values : Fin count -> Coordinate)
    (nonnegative : forall row, 0 <= values row) : 0 <= FiniteSum.Fin.sumFin values := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono
    (fun _ : Fin count => (0 : Coordinate)) values nonnegative
  simpa only [FiniteSum.Fin.sumFin_zero] using bound

/-- Every nonnegative entry is bounded by the original finite sum. -/
private theorem entry_le_sum {count : Nat} (values : Fin count -> Coordinate)
    (nonnegative : forall row, 0 <= values row) (row : Fin count) :
    values row <= FiniteSum.Fin.sumFin values := by
  rw [<- FiniteSum.Fin.sumFin_ite_eq row values]
  apply FiniteSum.Rational.Order.Positivity.sumFin_mono
  intro entry
  by_cases equal : entry = row
  · rw [if_pos equal]
  · rw [if_neg equal]
    exact nonnegative entry

end

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Readings in
set_option genInjectivity false in
/-- Separated observation boxes with common coercivity, variation and denominator bounds.

The record retains the exact interpolation points and their neighborhoods, caches the common minimum
clearance/separation/variation radius, and specifies its denominator scale and positive density coefficient. -/
structure ObservationBoxes (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (count : Nat) where
  /-- The retained interpolation coercivity certificate for the original polynomial and coefficient count. -/ coercivity
    : ObservationCoercivity polynomial count
  /-- The indexed retained neighborhoods of the original observation sites. -/ sites : Data.Vector
    (ObservationNeighborhood polynomial count) count
  /-- Each neighborhood center is the exact original interpolation-bank point at that index. -/ sites_center : forall
    index, (sites index).center = coercivity.interpolation.bank.pointAt index
  /-- The cached sum of the original neighborhoods' variation scales. -/ totalVariation : Coordinate
  /-- The cached total variation equals the sum over those exact retained sites. -/ totalVariation_eq : totalVariation =
    FiniteSum.Fin.sumFin (fun index => (sites index).variation.scale)
  /-- The common radius allowed by all original site neighborhoods. -/ clearanceRadius : Coordinate
  /-- The clearance radius equals the original finite minimum of site radii. -/ clearanceRadius_eq : clearanceRadius =
    minimumRadius count (fun index => (sites index).radius)
  /-- The common separation radius from the original interpolation bank. -/ separationRadius : Coordinate
  /-- The separation radius is exactly the retained bank's separation radius. -/ separationRadius_eq : separationRadius
    = PreparedObservationSeparation.ObservationBank.separationRadius coercivity.interpolation.bank
  /-- The retained common radius for clearance, separation and variation control. -/ radius : Coordinate
  /-- The radius is the exact minimum of the three original restrictions. -/ radius_eq : radius = min clearanceRadius
    (min separationRadius (variationRadius coercivity.lower totalVariation))
  /-- The cached common majorant for all original denominator evaluations. -/ denominatorScale : Coordinate
  /-- The scale is one plus the finite sum of the retained site majorants. -/ denominatorScale_eq : denominatorScale = 1
    + FiniteSum.Fin.sumFin (fun index => (sites index).denominatorMajorant)
  /-- The cached positive density coefficient for the retained observation boxes. -/ densityConstant : Coordinate
  /-- The density coefficient is exactly the retained coercivity lower bound divided by four and the denominator
scale. -/
  densityConstant_eq : densityConstant = coercivity.lower / 4 / denominatorScale

constructive_injectivity ObservationBoxes

namespace ObservationBoxes

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {count : Nat}

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Riemann.Readings in
/-- Construct the retained observation neighborhoods and common box constants from exact interpolation coercivity.

Each neighborhood uses its original bank point and nonzero denominator certificate. All aggregate bounds are cached with
equations to those same neighborhoods. -/
def ofCoercivity (coercivity : ObservationCoercivity polynomial count) :
    ObservationBoxes polynomial count :=
  let bank := coercivity.interpolation.bank
  let sites := Vector.Basic.vectorOfFn fun index : Fin count =>
    ObservationNeighborhood.ofPoint polynomial count (bank.pointAt index)
      (bank.denominator_nonzero _ (bank.pointAt_mem index))
  let totalVariation := FiniteSum.Fin.sumFin (fun index => (sites index).variation.scale)
  let clearanceRadius := minimumRadius count (fun index => (sites index).radius)
  let separationRadius := PreparedObservationSeparation.ObservationBank.separationRadius bank
  let denominatorScale := 1 + FiniteSum.Fin.sumFin (fun index => (sites index).denominatorMajorant)
  { coercivity := coercivity
    sites := sites
    sites_center := fun index => by rw [Vector.Basic.vectorOfFn_apply]; rfl
    totalVariation := totalVariation
    totalVariation_eq := rfl
    clearanceRadius := clearanceRadius
    clearanceRadius_eq := rfl
    separationRadius := separationRadius
    separationRadius_eq := rfl
    radius := min clearanceRadius (min separationRadius (variationRadius coercivity.lower totalVariation))
    radius_eq := rfl
    denominatorScale := denominatorScale
    denominatorScale_eq := rfl
    densityConstant := coercivity.lower / 4 / denominatorScale
    densityConstant_eq := rfl }

/-- The sum of the retained neighborhoods' variation scales is nonnegative. -/
theorem totalVariation_nonnegative (boxes : ObservationBoxes polynomial count) :
    0 <= boxes.totalVariation := by
  rw [boxes.totalVariation_eq]
  exact sum_nonnegative _ (fun index => (boxes.sites index).variation.scale_nonnegative)

open Purelib.Riemann.Readings in
/-- The common clearance, separation and variation radius is positive.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem radius_positive (boxes : ObservationBoxes polynomial count) : 0 < boxes.radius := by
  rw [boxes.radius_eq, boxes.clearanceRadius_eq, boxes.separationRadius_eq]
  exact Order.Basic.lt_min (minimumRadius_positive _ (fun index => (boxes.sites index).radius_positive))
    (Order.Basic.lt_min (PreparedObservationSeparation.ObservationBank.separationRadius_positive
      boxes.coercivity.interpolation.bank)
      (variationRadius_positive boxes.coercivity.lower_positive boxes.totalVariation_nonnegative))

/-- The common radius lies within the exact retained site's certified neighborhood radius.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem radius_le_site (boxes : ObservationBoxes polynomial count) (index : Fin count) :
    boxes.radius <= (boxes.sites index).radius := by
  rw [boxes.radius_eq]
  exact (Order.Basic.min_le_left _ _).trans (by rw [boxes.clearanceRadius_eq]; exact minimumRadius_le _ index)

/-- The common radius satisfies the original coercivity-to-variation restriction.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem radius_le_variation (boxes : ObservationBoxes polynomial count) :
    boxes.radius <= variationRadius boxes.coercivity.lower boxes.totalVariation := by
  rw [boxes.radius_eq]
  exact (Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_right _ _)

open Purelib.Geometry.Rational in
/-- The centered rational square at the exact retained observation site with the common certified radius. -/
def box (boxes : ObservationBoxes polynomial count) (index : Fin count) : Box :=
  Box.Square.Centered.BoxTransport.centeredBox (boxes.sites index).center boxes.radius boxes.radius_positive.le

/-- Each retained centered observation square has strictly ordered sides. -/
theorem box_proper (boxes : ObservationBoxes polynomial count) (index : Fin count) :
    (boxes.box index).Proper := centeredBox_proper _ boxes.radius_positive

open Purelib.Riemann.Readings in
/-- Distinct original observation indices give separated retained centered squares.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem box_separated (boxes : ObservationBoxes polynomial count) {left right : Fin count}
    (different : left ≠ right) : (boxes.box left).Separated (boxes.box right) := by
  unfold box
  rw [boxes.sites_center, boxes.sites_center]
  apply PreparedObservationSeparation.ObservationBank.separated_of_radius_le boxes.coercivity.interpolation.bank
    boxes.radius boxes.radius_positive
    ?_ different
  rw [boxes.radius_eq, <- boxes.separationRadius_eq]
  exact (Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _)

open Purelib.Polynomial.Dense.Gaussian in
/-- The original site's polynomial denominator majorant is positive. -/
private theorem majorant_positive (boxes : ObservationBoxes polynomial count) (index : Fin count) :
    0 < (boxes.sites index).denominatorMajorant := by
  rw [(boxes.sites index).denominatorMajorant_eq]
  exact Bounds.Box.denseEvalNormMajorant_pos _ _

/-- The cached denominator scale is at least one. -/
theorem one_le_denominatorScale (boxes : ObservationBoxes polynomial count) :
    1 <= boxes.denominatorScale := by
  rw [boxes.denominatorScale_eq]
  exact le_add_of_nonneg_right (sum_nonnegative _ (fun index => (boxes.majorant_positive index).le))

/-- The cached common denominator scale is positive. -/
theorem denominatorScale_positive (boxes : ObservationBoxes polynomial count) :
    0 < boxes.denominatorScale := (by decide : (0 : Coordinate) < 1).trans_le boxes.one_le_denominatorScale

/-- Each original site's denominator majorant is bounded by the common cached scale. -/
theorem majorant_le_denominatorScale (boxes : ObservationBoxes polynomial count) (index : Fin count) :
    (boxes.sites index).denominatorMajorant <= boxes.denominatorScale := by
  rw [boxes.denominatorScale_eq]
  exact (entry_le_sum _ (fun entry => (boxes.majorant_positive entry).le) index).trans
    (le_add_of_nonneg_left (by decide))

open Purelib.Data.Rat in
/-- The retained coercivity divided by four and the common denominator scale is positive. -/
theorem densityConstant_positive (boxes : ObservationBoxes polynomial count) : 0 < boxes.densityConstant := by
  rw [boxes.densityConstant_eq]
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct boxes.coercivity.lower_positive (by decide))
    boxes.denominatorScale_positive

open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- The nonnegative numerator bound from the original center value and variation error.

The maximum with zero uses the exact coefficient norm, retained site variation scale and common radius; the error factor
is eight times the radius squared. -/
def numeratorLower (boxes : ObservationBoxes polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) (index : Fin count) : Coordinate :=
  max 0 (normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
      (boxes.sites index).center) / 2 -
    (boxes.sites index).variation.scale * coefficientNormSq coefficients * (8 * boxes.radius ^ 2))

open Purelib.LinearAlgebra.Gaussian in
/-- The retained local numerator lower bound is nonnegative.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem numeratorLower_nonnegative (boxes : ObservationBoxes polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) (index : Fin count) :
    0 <= boxes.numeratorLower coefficients index := Order.Basic.le_max_left _ _

open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- The retained numerator lower bound holds throughout its original observation box.

The bound compares the original retained rational quantities. Direct order
certificates preserve the same minimum or maximum branch and its supplied
positive or weak bounds without changing any cached value. -/
theorem numeratorLower_le (boxes : ObservationBoxes polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) (index : Fin count)
    {point : Basic.Canonical} (inside : (boxes.box index).Contains point) :
    boxes.numeratorLower coefficients index <=
      normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) :=
  Order.Basic.max_le (Basic.Canonical.normSq_nonneg _) ((boxes.sites index).numerator_lower coefficients
    boxes.radius_positive.le (boxes.radius_le_site index) inside)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- The sum of retained local numerator bounds preserves one quarter of the original coercivity.

The common radius pays the total variation error for the same coefficient vector and interpolation sites, retaining the
exact coefficient squared norm. -/
theorem quarter_coercivity_le_numeratorSum (boxes : ObservationBoxes polynomial count)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector count) :
    boxes.coercivity.lower / 4 * coefficientNormSq coefficients <=
      FiniteSum.Fin.sumFin (boxes.numeratorLower coefficients) := by
  have signedBound := FiniteSum.Rational.Order.Positivity.sumFin_mono
    (fun index : Fin count =>
      normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval
        (boxes.sites index).center) / 2 -
      (boxes.sites index).variation.scale * coefficientNormSq coefficients * (8 * boxes.radius ^ 2))
    (boxes.numeratorLower coefficients) (fun _ => Order.Basic.le_max_right _ _)
  have centerSum := FiniteSum.Fin.sumFin_congr (fun index : Fin count =>
    congrArg (fun point => normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point))
      (boxes.sites_center index))
  simp only [FiniteSum.Fin.sumFin_sub, Fraction.Field.div_eq_mul_inv_direct,
    FiniteSum.Fin.sumFin_mul_right] at signedBound
  rw [centerSum, <- boxes.totalVariation_eq] at signedBound
  have coefficientNonnegative : 0 <= coefficientNormSq coefficients :=
    sum_nonnegative _ (fun _ => Basic.Canonical.normSq_nonneg _)
  have observationBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (boxes.coercivity.lower_mul_coefficientNorm_le coefficients)
    (show (0 : Coordinate) <= (2 : Coordinate)⁻¹ by decide)
  have errorBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (variation_error_le_quarter boxes.totalVariation_nonnegative boxes.radius_positive.le
      boxes.radius_le_variation) coefficientNonnegative
  calc
    boxes.coercivity.lower / 4 * coefficientNormSq coefficients =
        (boxes.coercivity.lower / 2 - boxes.coercivity.lower / 4) * coefficientNormSq coefficients := by
      rw [half_sub_quarter]
    _ = (boxes.coercivity.lower * coefficientNormSq coefficients) * (2 : Coordinate)⁻¹ -
        (boxes.coercivity.lower / 4) * coefficientNormSq coefficients := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ <= observationNormSq boxes.coercivity.interpolation.bank coefficients * (2 : Coordinate)⁻¹ -
        (boxes.totalVariation * (8 * boxes.radius ^ 2)) * coefficientNormSq coefficients :=
      Fraction.Order.Arithmetic.sub_le_sub_direct observationBound errorBound
    _ = observationNormSq boxes.coercivity.interpolation.bank coefficients * (2 : Coordinate)⁻¹ -
        boxes.totalVariation * coefficientNormSq coefficients * (8 * boxes.radius ^ 2) := by ring1
    _ <= _ := signedBound

end ObservationBoxes

open Purelib.Curves.Hyperelliptic in
/-- Construct the separated observation boxes from the original hyperelliptic curve's interpolation coercivity. -/
def curveObservationBoxes {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) :
    ObservationBoxes curve.polynomial genus :=
  ObservationBoxes.ofCoercivity (curveObservationCoercivity curve)

end Purelib.Riemann.Readings.PreparedObservationBoxes
