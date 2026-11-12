module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.EvaluationLower

public import Purelib.Riemann.Integration.PreparedNumeratorVariation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Data.Rat.Fraction.Order

@[expose] public section

/-!
# Automatic clear neighborhoods of fixed observations

All radii and Horner bounds are computed before receiving a numerator
coefficient vector.  Refining a neighborhood preserves a positive denominator
margin and the homogeneous numerator variation estimate.  No interval
successful-check hypothesis is required from the caller.
-/

namespace Purelib.Riemann.Readings.PreparedObservationNeighborhoods

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.LinearAlgebra.Gaussian.Energy (GaussianVector)
open Purelib.Riemann.Integration.PreparedNumeratorVariation (NumeratorVariation)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

section
open Purelib.Data.Rat
/-- The minimum of one and the target divided by thirty-two times the scale plus one.

For a positive target and nonnegative scale, this positive radius controls the squared-diagonal variation error by one
quarter of the target. -/
def variationRadius (target scale : Rational) : Rational :=
  min 1 (target / (8 * (scale + 1)) / 4)

/-- A positive target and nonnegative scale give a strictly positive variation radius.

Adding one to the retained scale makes its original denominator positive.
The two positive divisions and the original minimum preserve strict positivity. -/
theorem variationRadius_positive {target scale : Rational}
    (targetPositive : 0 < target) (scaleNonnegative : 0 <= scale) :
    0 < variationRadius target scale := by
  apply Basic.lt_min (by decide)
  exact Field.div_pos_direct
    (Field.div_pos_direct targetPositive
      (Arithmetic.mul_pos_direct (by decide)
        (Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative (by decide)))) (by decide)

/-- The retained variation radius is at most one.

The original minimum keeps the unit cap together with its target-dependent
term. Its left projection bounds the same selected rational radius. -/
theorem variationRadius_le_one (target scale : Rational) :
    variationRadius target scale <= 1 := Basic.min_le_left _ _

/-- A nonnegative radius below the variation radius bounds scaled squared-diagonal error by a quarter target.

The original unit cap bounds the square by the radius. The retained scale is
bounded by its incremented denominator, and exact positive-denominator
cancellation pays the displayed target quarter. -/
theorem variation_error_le_quarter {target scale radius : Rational}
    (scaleNonnegative : 0 <= scale) (radiusNonnegative : 0 <= radius)
    (radiusBound : radius <= variationRadius target scale) :
    scale * (8 * radius ^ 2) <= target / 4 := by
  have scalePositive : 0 < scale + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative (by decide)
  have eightScalePositive : 0 < 8 * (scale + 1) :=
    Arithmetic.mul_pos_direct (by decide) scalePositive
  have squareBound : radius ^ 2 <= radius := by
    rw [pow_two]
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (radiusBound.trans (variationRadius_le_one target scale)) radiusNonnegative).trans_eq
        (Fraction.Field.mul_one_direct radius)
  have enlarged : scale <= scale + 1 := by
    calc
      scale = scale + 0 := by ring1
      _ <= scale + 1 := Arithmetic.add_le_add_direct le_rfl (by decide)
  calc
    scale * (8 * radius ^ 2) <= (scale + 1) * (8 * radius ^ 2) :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct
        enlarged
        (Arithmetic.mul_nonneg_direct (by decide)
          (Arithmetic.sq_nonneg_direct _))
    _ = (8 * (scale + 1)) * radius ^ 2 := by ring1
    _ <= (8 * (scale + 1)) * radius :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct squareBound eightScalePositive.le
    _ <= (8 * (scale + 1)) * (target / (8 * (scale + 1)) / 4) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (radiusBound.trans (Basic.min_le_right _ _)) eightScalePositive.le
    _ = (target / (8 * (scale + 1)) * (8 * (scale + 1))) / 4 := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ = target / 4 := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ eightScalePositive.ne']

/-- Subtracting a quarter of a rational value from its half leaves its quarter. -/
theorem half_sub_quarter (value : Rational) : value / 2 - value / 4 = value / 4 := by
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  have halves : (2 : Rational)⁻¹ = 2 * (4 : Rational)⁻¹ := by decide
  rw [halves]
  ring1

/-- The chosen radius leaves at least a quarter of the target after subtracting variation error from its half. -/
theorem quarter_le_half_sub_error {target scale radius : Rational}
    (scaleNonnegative : 0 <= scale) (radiusNonnegative : 0 <= radius)
    (radiusBound : radius <= variationRadius target scale) :
    target / 4 <= target / 2 - scale * (8 * radius ^ 2) := by
  rw [<- half_sub_quarter target]
  exact Arithmetic.sub_le_sub_left_direct
    (variation_error_le_quarter scaleNonnegative radiusNonnegative radiusBound) _

end

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
/-- A centered box of nonnegative radius contains its original center.

The same nonnegative radius bounds zero in both coordinate intervals.
Direct scalar addition and subtraction translations retain their original endpoints. -/
theorem centeredBox_center (center : Basic.Canonical) {radius : Rational}
    (nonnegative : 0 <= radius) :
    (BoxTransport.centeredBox center radius nonnegative).Contains center := by
  have lower (coordinate : Rational) : coordinate - radius <= coordinate := by
    calc
      coordinate - radius <= coordinate - 0 :=
        Arithmetic.sub_le_sub_left_direct nonnegative coordinate
      _ = coordinate := by ring1
  have upper (coordinate : Rational) : coordinate <= coordinate + radius := by
    calc
      coordinate = coordinate + 0 := by ring1
      _ <= coordinate + radius := Arithmetic.add_le_add_direct le_rfl nonnegative
  exact ⟨lower center.re, upper center.re, lower center.im, upper center.im⟩

/-- A centered box of positive radius has strictly increasing coordinate intervals.

Subtracting the retained positive radius puts each lower endpoint below its
center; adding that same radius puts its original upper endpoint above the center. -/
theorem centeredBox_proper (center : Basic.Canonical) {radius : Rational}
    (positive : 0 < radius) :
    (BoxTransport.centeredBox center radius positive.le).Proper := by
  have increasing (coordinate : Rational) : coordinate - radius < coordinate + radius := by
    calc
      coordinate - radius < coordinate - 0 :=
        Arithmetic.sub_lt_sub_left_direct positive coordinate
      _ = coordinate + 0 := by ring1
      _ < coordinate + radius := Arithmetic.add_lt_add_left_direct positive coordinate
  exact ⟨increasing center.re, increasing center.im⟩

/-- Centered boxes with the same center refine according to their nonnegative radii. -/
theorem centeredBox_refines (center : Basic.Canonical) {small large : Rational}
    (smallNonnegative : 0 <= small) (largeNonnegative : 0 <= large)
    (bound : small <= large) :
    (BoxTransport.centeredBox center small smallNonnegative).Refines
      (BoxTransport.centeredBox center large largeNonnegative) :=
  ⟨Arithmetic.sub_le_sub_left_direct bound _,
    add_le_add_right bound _,
    Arithmetic.sub_le_sub_left_direct bound _,
    add_le_add_right bound _⟩

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
set_option genInjectivity false in
/-- A nonzero polynomial observation with retained denominator and numerator variation data on its unit box.

The record caches the center value squared norm, denominator slope and majorant, and a radius tied to those exact
values. The numerator variation retains the same ambient box and coefficient count. -/
structure ObservationNeighborhood (polynomial :
  Basic.CanonicalCoefficients.CoefficientPolynomial) (count : Nat) where
  /-- The original Gaussian observation point. -/ center : Basic.Canonical
  /-- The retained ambient box for all numerator and denominator bounds. -/ ambient : Box
  /-- The ambient box is exactly the unit square centered at the original observation point. -/ ambient_eq : ambient =
    BoxTransport.centeredBox center 1 (by decide)
  /-- Cached numerator variation bounds on this exact ambient box and coefficient count. -/ variation :
    NumeratorVariation count ambient
  /-- The cached squared norm of the polynomial at the original center. -/ denominatorValue : Rational
  /-- The cached denominator value equals the original center evaluation's squared norm. -/ denominatorValue_eq :
    denominatorValue = normSq (polynomial.eval center)
  /-- The original center evaluation has strictly positive squared norm. -/ denominatorValue_positive : 0 <
    denominatorValue
  /-- The cached denominator variation bound on the retained ambient box. -/ denominatorSlope : Rational
  /-- The cached slope equals the original polynomial's exact box Lipschitz bound. -/ denominatorSlope_eq :
    denominatorSlope = Bounds.Box.denseLipschitzBound polynomial ambient
  /-- The cached upper bound for denominator squared norms on the retained ambient box. -/ denominatorMajorant :
    Rational
  /-- The cached majorant equals the original polynomial's box evaluation bound. -/ denominatorMajorant_eq :
    denominatorMajorant =
    Bounds.Box.denseEvalNormMajorant polynomial ambient
  /-- The retained positive observation-neighborhood radius. -/ radius : Rational
  /-- The radius is exactly the variation radius computed from the retained denominator value and slope. -/ radius_eq :
    radius = variationRadius denominatorValue denominatorSlope

constructive_injectivity ObservationNeighborhood

namespace ObservationNeighborhood

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {count : Nat}

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Construct an observation neighborhood from an original point where the polynomial is nonzero.

The unit centered box, numerator bounds, denominator value and variation bounds are computed once and retained with
their defining equalities. -/
def ofPoint (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (count : Nat)
  (point : Basic.Canonical)
    (clear : polynomial.eval point ≠ 0) : ObservationNeighborhood polynomial count :=
  let ambient := BoxTransport.centeredBox point 1 (by decide)
  let value := normSq (polynomial.eval point)
  let slope := Bounds.Box.denseLipschitzBound polynomial ambient
  { center := point
    ambient := ambient
    ambient_eq := rfl
    variation := NumeratorVariation.build count ambient
    denominatorValue := value
    denominatorValue_eq := rfl
    denominatorValue_positive := by
      have scalar := Norm.Basic.normSq_pos clear
      rw [Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar
    denominatorSlope := slope
    denominatorSlope_eq := rfl
    denominatorMajorant := Bounds.Box.denseEvalNormMajorant polynomial ambient
    denominatorMajorant_eq := rfl
    radius := variationRadius value slope
    radius_eq := rfl }

open Purelib.Polynomial.Dense.Gaussian in
/-- The cached denominator variation slope is strictly positive. -/
theorem denominatorSlope_positive (site : ObservationNeighborhood polynomial count) :
    0 < site.denominatorSlope := by
  rw [site.denominatorSlope_eq]
  exact Bounds.Box.denseLipschitzBound_pos _ _

/-- The retained observation radius is strictly positive. -/
theorem radius_positive (site : ObservationNeighborhood polynomial count) : 0 < site.radius := by
  rw [site.radius_eq]
  exact variationRadius_positive site.denominatorValue_positive site.denominatorSlope_positive.le

/-- The retained observation radius is at most the unit ambient radius. -/
theorem radius_le_one (site : ObservationNeighborhood polynomial count) : site.radius <= 1 := by
  rw [site.radius_eq]
  exact variationRadius_le_one _ _

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- Every nonnegative centered radius below the retained observation radius refines the original ambient box. -/
theorem box_refines (site : ObservationNeighborhood polynomial count)
    {radius : Rational} (nonnegative : 0 <= radius) (bound : radius <= site.radius) :
    (BoxTransport.centeredBox site.center radius nonnegative).Refines site.ambient := by
  rw [site.ambient_eq]
  exact centeredBox_refines _ nonnegative (by decide) (bound.trans site.radius_le_one)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- The original denominator slope and squared radius bound movement throughout the same centered observation box.

Both points remain in the original ambient box. Its retained polynomial
Lipschitz bound and the original squared diagonal give this weak finite
ceiling before a continuation allowance is chosen.
-/
theorem denominator_movement_le (site : ObservationNeighborhood polynomial count)
    {radius : Rational} (nonnegative : 0 ≤ radius) (bound : radius ≤ site.radius)
    {point : Basic.Canonical}
    (inside : (BoxTransport.centeredBox site.center radius nonnegative).Contains point) :
    normSq (polynomial.eval site.center - polynomial.eval point) ≤
      site.denominatorSlope * (8 * radius ^ 2) := by
  have centerInside := centeredBox_center site.center nonnegative
  have refines := site.box_refines nonnegative bound
  have variation := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial
    (refines.contains centerInside) (refines.contains inside)
  rewrite [← site.denominatorSlope_eq] at variation
  have distance := Box.normSq_sub_le_diagonalSq centerInside inside
  rewrite [BoxTransport.centeredBox_diagonalSq] at distance
  have movement := variation.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    distance site.denominatorSlope_positive.le)
  rewrite [Norm.Basic.normSq_eq_canonical] at movement
  exact movement

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Inside a retained-radius centered box, the polynomial squared norm is at least one quarter of its original center
value.

The exact denominator slope and radius equation pay the squared-diagonal error on the same ambient box. -/
theorem denominator_lower (site : ObservationNeighborhood polynomial count)
    {radius : Rational} (nonnegative : 0 <= radius) (bound : radius <= site.radius)
    {point : Basic.Canonical}
    (inside : (BoxTransport.centeredBox site.center radius nonnegative).Contains point) :
    site.denominatorValue / 4 <= normSq (polynomial.eval point) := by
  have radiusBound := bound.trans_eq site.radius_eq
  have lower := quarter_le_half_sub_error site.denominatorSlope_positive.le nonnegative radiusBound
  have comparison := Geometry.EvaluationLower.sampledNormLower_le polynomial site.center
    (centeredBox_center site.center nonnegative) (site.box_refines nonnegative bound) inside
  unfold Geometry.EvaluationLower.sampledNormLower at comparison
  simp only [Norm.Basic.normSq_eq_canonical] at comparison
  rw [BoxTransport.centeredBox_diagonalSq,
    <- site.denominatorValue_eq, <- site.denominatorSlope_eq] at comparison
  exact lower.trans comparison

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Inside a retained-radius centered box, the polynomial squared norm is bounded by the cached ambient majorant. -/
theorem denominator_upper (site : ObservationNeighborhood polynomial count)
    {radius : Rational} (nonnegative : 0 <= radius) (bound : radius <= site.radius)
    {point : Basic.Canonical}
    (inside : (BoxTransport.centeredBox site.center radius nonnegative).Contains point) :
    normSq (polynomial.eval point) <= site.denominatorMajorant := by
  rw [site.denominatorMajorant_eq]
  have scalar := Bounds.Box.normSq_eval_le_denseEvalNormMajorant polynomial
    ((site.box_refines nonnegative bound).contains inside)
  simpa only [Norm.Basic.normSq_eq_canonical] using scalar

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Polynomial in
/-- Bound the coefficient polynomial's squared norm throughout a retained-radius centered box from its original center
reading.

The loss uses the exact retained numerator variation scale, original coefficient norm sum and the centered box's squared
diagonal. -/
theorem numerator_lower (site : ObservationNeighborhood polynomial count)
    (coefficients : GaussianVector count)
    {radius : Rational} (nonnegative : 0 <= radius) (bound : radius <= site.radius)
    {point : Basic.Canonical}
    (inside : (BoxTransport.centeredBox site.center radius nonnegative).Contains point) :
    normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval site.center) / 2 -
        site.variation.scale * coefficientNormSq coefficients * (8 * radius ^ 2) <=
      normSq ((Geometry.EvaluationLower.coefficientPolynomial coefficients).eval point) := by
  have comparison := site.variation.sampled_lower_le coefficients
    (centeredBox_center site.center nonnegative) inside (site.box_refines nonnegative bound)
  rw [BoxTransport.centeredBox_diagonalSq] at comparison
  exact comparison

end ObservationNeighborhood

end Purelib.Riemann.Readings.PreparedObservationNeighborhoods
