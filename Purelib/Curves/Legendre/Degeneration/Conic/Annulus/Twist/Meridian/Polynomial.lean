module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian
public import Purelib.Geometry.Gaussian.UnitCircle.Polynomial.Winding
import Purelib.Polynomial.Dense.Gaussian.Constants
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Multiplication.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine
import Purelib.Data.Fin.Two
import Purelib.Tactic.Ring

/-! # A joined polynomial witness on the actual labelled meridian rays

Four actual cubic edges use the original site centre and labelled parameter
displacement. They join literally at the same cardinal positions as the
original phase. Reading the original phaseChart gives positive radial
incidence with Meridian.parameterAt at every admitted rational position,
with the original small radius bound and both singular exclusions retained.

The finite winding is that of these actual joined displacement edges. Their
positive incidence does not identify prepared root transport or monodromy:
a full-cubic/cofactor lift, collar/complement gluing, canonical cycle
attachment and comparison with the retained parallel transport remain
separate geometric certificates.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Rational.Pair.Path.Basic (PolynomialEdge)

/-- The actual site-centred polynomial quarter retains the original labelled displacement and quarter multiplier. -/
@[expose] def quarterPolynomial (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter) :
    CoefficientPolynomial :=
  Constants.gaussianConstant (criticalValue site) +
    UnitCircle.Polynomial.scaledPolynomial (parameter - criticalValue site) quarter

/-- Read one actual labelled polynomial quarter at its original unit-interval parameter. -/
@[expose] def quarterAt (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : Canonical :=
  (quarterPolynomial site parameter quarter).eval (Affine.line 0 1 time)

/-- The same site-centred polynomial quarter evaluates to the original centre plus its displaced cubic point. -/
theorem quarterAt_eq (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : quarterAt site parameter quarter time =
      criticalValue site + (parameter - criticalValue site) * UnitCircle.Polynomial.point quarter time := by
  unfold quarterAt quarterPolynomial
  rewrite [DensePolynomial.eval_add, Constants.gaussianConstant_eval,
    UnitCircle.Polynomial.scaledPolynomial_eval]
  rfl

/-- Each actual labelled polynomial quarter lies on its original rational quarter's exact positive radial ray. -/
theorem quarterAt_displacement (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : quarterAt site parameter quarter time - criticalValue site =
      Scale.scale (UnitCircle.Polynomial.gain time)
        ((Waist.direction quarter time).value * (parameter - criticalValue site)) := by
  rewrite [quarterAt_eq]
  have cancelled : criticalValue site + (parameter - criticalValue site) *
      UnitCircle.Polynomial.point quarter time - criticalValue site =
      (parameter - criticalValue site) * UnitCircle.Polynomial.point quarter time := by ring1
  rewrite [cancelled, UnitCircle.Polynomial.point_incidence]
  calc
    _ = Scale.scale (UnitCircle.Polynomial.gain time)
        ((parameter - criticalValue site) *
          (UnitCircle.Quarter.unitCircuitMultiplier quarter * UnitCircle.Stereographic.unitQuarterPoint time)) :=
      (Scale.scale_mul_right _ _ _).symm
    _ = _ := congrArg (Scale.scale (UnitCircle.Polynomial.gain time)) (by
      rewrite [Waist.direction_value]
      ring1)

/-- The actual four labelled polynomial quarters join in order and retain the literal closing occurrence. -/
theorem quarterAt_join (site : Fin 2) (parameter : Canonical) :
    quarterAt site parameter .first 1 = quarterAt site parameter .second 0 ∧
      quarterAt site parameter .second 1 = quarterAt site parameter .third 0 ∧
      quarterAt site parameter .third 1 = quarterAt site parameter .fourth 0 ∧
      quarterAt site parameter .fourth 1 = quarterAt site parameter .first 0 := by
  constructor
  · exact (quarterAt_eq site parameter .first 1).trans
      ((congrArg (fun point : Canonical => criticalValue site + (parameter - criticalValue site) * point)
        UnitCircle.Polynomial.points_join.1).trans (quarterAt_eq site parameter .second 0).symm)
  constructor
  · exact (quarterAt_eq site parameter .second 1).trans
      ((congrArg (fun point : Canonical => criticalValue site + (parameter - criticalValue site) * point)
        UnitCircle.Polynomial.points_join.2.1).trans (quarterAt_eq site parameter .third 0).symm)
  constructor
  · exact (quarterAt_eq site parameter .third 1).trans
      ((congrArg (fun point : Canonical => criticalValue site + (parameter - criticalValue site) * point)
        UnitCircle.Polynomial.points_join.2.2.1).trans (quarterAt_eq site parameter .fourth 0).symm)
  · exact (quarterAt_eq site parameter .fourth 1).trans
      ((congrArg (fun point : Canonical => criticalValue site + (parameter - criticalValue site) * point)
        UnitCircle.Polynomial.points_join.2.2.2).trans (quarterAt_eq site parameter .first 0).symm)

/-- The actual labelled polynomial loop uses the SAME original phase selector and its retained affine quarter time. -/
@[expose] def polynomialAt (site : Fin 2) (parameter : Canonical) (position : Fraction.Rational) : Canonical :=
  let chart := Twist.phaseChart position
  quarterAt site parameter chart.1 chart.2

/-- The actual polynomial witness is positively radially incident to the SAME original labelled meridian.

The exact factor is read from the original selected quarter time. The
original phase and both endpoint owners are retained; this equation states
coordinate incidence and does not identify root or frame owners.
-/
theorem polynomialAt_incidence (site : Fin 2) (parameter : Canonical) (position : Fraction.Rational) :
    polynomialAt site parameter position - criticalValue site =
      Scale.scale (UnitCircle.Polynomial.gain (Twist.phaseChart position).2)
        (parameterAt site parameter position - criticalValue site) := by
  unfold polynomialAt
  rewrite [quarterAt_displacement, displacement, Twist.phase_chart]
  rfl

/-- On the actual admitted original phase interval the SAME incidence factor is between one half and one. -/
theorem polynomialAt_gain {position : Fraction.Rational} (inside : 0 ≤ position ∧ position ≤ 1) :
    (1 / 2 : Fraction.Rational) ≤ UnitCircle.Polynomial.gain (Twist.phaseChart position).2 ∧
      UnitCircle.Polynomial.gain (Twist.phaseChart position).2 ≤ 1 :=
  UnitCircle.Polynomial.gain_bounds (Twist.phaseChart_inside position inside)

/-- The witness retains the same five original phase positions, with the earlier-quarter endpoint at each seam. -/
theorem polynomialAt_cardinals (site : Fin 2) (parameter : Canonical) :
    polynomialAt site parameter 0 = quarterAt site parameter .first 0 ∧
      polynomialAt site parameter (1 / 4) = quarterAt site parameter .first 1 ∧
      polynomialAt site parameter (1 / 2) = quarterAt site parameter .second 1 ∧
      polynomialAt site parameter (3 / 4) = quarterAt site parameter .third 1 ∧
      polynomialAt site parameter 1 = quarterAt site parameter .fourth 1 := by
  unfold polynomialAt
  rewrite [Twist.phaseChart_cardinals.1, Twist.phaseChart_cardinals.2.1,
    Twist.phaseChart_cardinals.2.2.1, Twist.phaseChart_cardinals.2.2.2.1,
    Twist.phaseChart_cardinals.2.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The polynomial witness starts at the SAME original parameter and returns after its four actual joined edges. -/
theorem polynomialAt_endpoints (site : Fin 2) (parameter : Canonical) :
    polynomialAt site parameter 0 = parameter ∧ polynomialAt site parameter 1 = parameter := by
  have first : quarterAt site parameter .first 0 = parameter := by
    rewrite [quarterAt_eq, (UnitCircle.Polynomial.point_endpoints .first).1]
    change criticalValue site + (parameter - criticalValue site) * (1 : Canonical) = parameter
    ring1
  exact ⟨(polynomialAt_cardinals site parameter).1.trans first,
    (polynomialAt_cardinals site parameter).2.2.2.2.trans ((quarterAt_join site parameter).2.2.2.trans first)⟩

/-- The original labelled polynomial quarter has the exact original displacement radius scaled by the SAME factor. -/
theorem quarterAt_normSq (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : Norm.Basic.normSq (quarterAt site parameter quarter time - criticalValue site) =
      UnitCircle.Polynomial.gain time ^ 2 * Norm.Basic.normSq (parameter - criticalValue site) := by
  rewrite [quarterAt_displacement, Scale.normSq_scale, Norm.Basic.normSq_mul, (Waist.direction quarter time).unit]
  ring1

/-- The actual labelled polynomial witness stays inside the original displacement radius on each original quarter. -/
theorem quarterAt_radius (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1) :
    Norm.Basic.normSq (quarterAt site parameter quarter time - criticalValue site) ≤
      Norm.Basic.normSq (parameter - criticalValue site) := by
  have upper := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (UnitCircle.Polynomial.point_upper quarter inside) (Norm.Basic.normSq_nonneg (parameter - criticalValue site))
  rewrite [UnitCircle.Polynomial.point_normSq] at upper
  exact (quarterAt_normSq site parameter quarter time).trans_le (upper.trans_eq (Fraction.Field.one_mul _))

/-- The original selected critical value is excluded on every admitted actual labelled polynomial quarter. -/
theorem quarterAt_regular {site : Fin 2} {parameter : Canonical} (regular : parameter ≠ criticalValue site)
    (quarter : UnitCircuitQuarter) {time : Fraction.Rational} (inside : 0 ≤ time ∧ time ≤ 1) :
    quarterAt site parameter quarter time ≠ criticalValue site := by
  have different : parameter - criticalValue site ≠ 0 := by
    intro zero
    apply regular
    calc
      parameter = criticalValue site + (parameter - criticalValue site) := by ring1
      _ = criticalValue site := by rewrite [zero]; ring1
  have nonzero := Field.mul_ne_zero_direct different (UnitCircle.Polynomial.point_ne_zero quarter inside)
  intro same
  apply nonzero
  calc
    _ = quarterAt site parameter quarter time - criticalValue site := by rewrite [quarterAt_eq]; ring1
    _ = 0 := by rewrite [same]; ring1

/-- Both original singular parameters remain excluded throughout the actual labelled polynomial witness. -/
theorem polynomialAt_regular {site : Fin 2} {parameter : Canonical} (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    {position : Fraction.Rational} (inside : 0 ≤ position ∧ position ≤ 1) :
    polynomialAt site parameter position ≠ 0 ∧ polynomialAt site parameter position ≠ 1 := by
  have timeInside := Twist.phaseChart_inside position inside
  have selected := quarterAt_regular regular (Twist.phaseChart position).1 timeInside
  have radius := (quarterAt_radius site parameter (Twist.phaseChart position).1 timeInside).trans bound
  have patch := Waist.parameter_inside site (quarterAt site parameter (Twist.phaseChart position).1
    (Twist.phaseChart position).2) (radius.trans (by decide +kernel))
  have other := Degeneration.parameter_ne_remaining site patch
  rcases Purelib.Data.Fin.Two.finTwo_cases site with zero | one
  · subst site
    exact ⟨selected, other⟩
  · subst site
    exact ⟨other, selected⟩

/-- One original oriented polynomial edge of the actual labelled parameter loop. -/
@[expose] def quarterEdge (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter) : PolynomialEdge :=
  PolynomialEdge.ofLine (quarterPolynomial site parameter quarter) 0 1 0 1

/-- The labelled polynomial edge retains the exact real coordinate of its SAME quarter point. -/
theorem quarterEdge_real (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : (quarterEdge site parameter quarter).realPart.eval time =
      (quarterAt site parameter quarter time).re := PolynomialEdge.ofLine_real_eval _ _ _ _ _ _

/-- The labelled polynomial edge retains the exact imaginary coordinate of its SAME quarter point. -/
theorem quarterEdge_imag (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : (quarterEdge site parameter quarter).imagPart.eval time =
      (quarterAt site parameter quarter time).im := PolynomialEdge.ofLine_imag_eval _ _ _ _ _ _

/-- The four actual labelled polynomial edges retain their original order and all outer endpoint occurrences. -/
@[expose] def polynomialEdges (site : Fin 2) (parameter : Canonical) : List PolynomialEdge :=
  [quarterEdge site parameter .first, quarterEdge site parameter .second,
    quarterEdge site parameter .third, quarterEdge site parameter .fourth]

/-- Subtracting the original labelled centre gives the SAME actual displaced polynomial edge used for winding. -/
@[expose] def displacementEdge (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter) :
    PolynomialEdge := UnitCircle.Polynomial.scaledEdge (parameter - criticalValue site) quarter

/-- The numerical winding edge retains the actual labelled polynomial quarter's real displacement coordinate. -/
theorem displacementEdge_real (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : (displacementEdge site parameter quarter).realPart.eval time =
      (quarterAt site parameter quarter time - criticalValue site).re := by
  unfold displacementEdge UnitCircle.Polynomial.scaledEdge
  rewrite [PolynomialEdge.ofLine_real_eval, UnitCircle.Polynomial.scaledPolynomial_eval, quarterAt_eq]
  exact congrArg Data.Gaussian.Basic.re (by ring1)

/-- The numerical winding edge retains the actual labelled polynomial quarter's imaginary displacement coordinate. -/
theorem displacementEdge_imag (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter)
    (time : Fraction.Rational) : (displacementEdge site parameter quarter).imagPart.eval time =
      (quarterAt site parameter quarter time - criticalValue site).im := by
  unfold displacementEdge UnitCircle.Polynomial.scaledEdge
  rewrite [PolynomialEdge.ofLine_imag_eval, UnitCircle.Polynomial.scaledPolynomial_eval, quarterAt_eq]
  exact congrArg Data.Gaussian.Basic.im (by ring1)

/-- The four actual joined labelled displacement edges compute winding one, with raw Cauchy-index sum four. -/
theorem displacement_winding {site : Fin 2} {parameter : Canonical} (regular : parameter ≠ criticalValue site) :
    (displacementEdge site parameter .first).doubledWinding +
      (displacementEdge site parameter .second).doubledWinding +
      (displacementEdge site parameter .third).doubledWinding +
      (displacementEdge site parameter .fourth).doubledWinding = 4 := by
  apply UnitCircle.Polynomial.scaled_winding
  intro zero
  apply regular
  calc
    parameter = criticalValue site + (parameter - criticalValue site) := by ring1
    _ = criticalValue site := by rewrite [zero]; ring1

/-- Dividing the SAME actual labelled displacement index sum by four gives ordinary winding one. -/
theorem displacement_winding_one {site : Fin 2} {parameter : Canonical}
    (regular : parameter ≠ criticalValue site) :
    ((displacementEdge site parameter .first).doubledWinding +
      (displacementEdge site parameter .second).doubledWinding +
      (displacementEdge site parameter .third).doubledWinding +
      (displacementEdge site parameter .fourth).doubledWinding) / 4 = 1 :=
  (congrArg (fun value : Int => value / 4) (displacement_winding regular)).trans
    (by decide +kernel : (4 : Int) / 4 = 1)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Twist.Meridian

end
