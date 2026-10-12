module
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Bounds.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.List.Minimum
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
public import Purelib.RootIsolation.Newton.Restart.Uniform.Budget
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-!
# Comparison of uniform and anchored Newton budgets

A protected boundary strip bounds the four gaps at a displayed contained
point satisfying the clearance-quarter test. Both budgets retain that same box.
-/

namespace Purelib.RootIsolation.Newton.Restart.Uniform.Anchored

open Purelib.Data.Rat.Bounds

open Purelib.Data.Rat.List

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib

/-- The uniform radius is below the point-specific anchored radius for every
contained rational point meeting the clearance-quarter residual test.

The clearance-quarter residual test supplies four uniform side margins.
Their scaled bounds and the common Newton caps bound every anchored-radius entry. -/
public theorem uniformAnchoredRadius_le_anchoredRadius
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (contains : current.box.Contains point)
    (cap : Fraction.Rational)
    (residualSmall : Data.Gaussian.Norm.Basic.normSq (p.eval point) < current.clearance.bound / 4) :
    Newton.Restart.Uniform.Budget.uniformAnchoredRadius squarefree current cap ≤
      Newton.Restart.Anchored.Budget.anchoredRadius squarefree current point cap := by
  let uniform := Newton.Restart.Uniform.Budget.uniformAnchoredRadius squarefree current cap
  let interior := current.clearance.residualInteriorRadius
  have bounds := Newton.Restart.Uniform.Budget.uniformAnchoredRadius_bounds squarefree current cap
  have margins := current.clearance.residualInteriorMargins contains
    residualSmall
  have leftGap : interior ≤ point.re - current.box.xLower := by
    calc
      interior = (current.box.xLower + interior) - current.box.xLower := by
        ring1
      _ ≤ point.re - current.box.xLower :=
        Order.Arithmetic.sub_le_sub_right_direct margins.1.le current.box.xLower
  have rightGap : interior ≤ current.box.xUpper - point.re := by
    calc
      interior = (point.re + interior) - point.re := by ring1
      _ ≤ current.box.xUpper - point.re :=
        Order.Arithmetic.sub_le_sub_right_direct margins.2.1.le point.re
  have bottomGap : interior ≤ point.im - current.box.yLower := by
    calc
      interior = (current.box.yLower + interior) - current.box.yLower := by
        ring1
      _ ≤ point.im - current.box.yLower :=
        Order.Arithmetic.sub_le_sub_right_direct margins.2.2.1.le current.box.yLower
  have topGap : interior ≤ current.box.yUpper - point.im := by
    calc
      interior = (point.im + interior) - point.im := by ring1
      _ ≤ current.box.yUpper - point.im :=
        Order.Arithmetic.sub_le_sub_right_direct margins.2.2.2.le point.im
  apply Minimum.le_positiveMinimum (Newton.Restart.Anchored.Budget.anchoredRadiusValues squarefree current point cap)
    bounds.1
  intro value member
  cases member with
  | head =>
      exact bounds.1
  | tail _ member =>
    cases member with
    | head =>
        exact bounds.2.1.trans (Scale.div_six_mono leftGap)
    | tail _ member =>
      cases member with
      | head =>
          exact bounds.2.1.trans (Scale.div_six_mono rightGap)
      | tail _ member =>
        cases member with
        | head =>
            exact bounds.2.1.trans (Scale.div_six_mono bottomGap)
        | tail _ member =>
          cases member with
          | head =>
              exact bounds.2.1.trans (Scale.div_six_mono topGap)
          | tail _ member =>
            cases member with
            | head =>
                exact bounds.2.2.1
            | tail _ member =>
              cases member with
              | head =>
                  exact bounds.2.2.2.1
              | tail _ member =>
                cases member with
                | head =>
                    exact bounds.2.2.2.2
                | tail _ member =>
                  cases member

/-- A cap below the point-independent reference radius is also the exact
point-specific radius at every contained sample satisfying the uniform
clearance-quarter test.

The uniform reference radius bounds the corresponding point-specific
reference radius from below. The supplied cap therefore remains its selected minimum. -/
public theorem anchoredRadius_eq_cap_of_le_uniformReference
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (contains : current.box.Contains point)
    {cap : Fraction.Rational}
    (capLeReference :
      cap ≤ Newton.Restart.Uniform.Budget.uniformAnchoredRadius squarefree current 1)
    (residualSmall :
      Data.Gaussian.Norm.Basic.normSq (p.eval point) < current.clearance.bound / 4) :
    Newton.Restart.Anchored.Budget.anchoredRadius squarefree current point cap = cap := by
  apply Newton.Restart.Anchored.Budget.anchoredRadius_eq_cap_of_le_reference
  exact capLeReference.trans
    (uniformAnchoredRadius_le_anchoredRadius squarefree current point contains
      1 residualSmall)

/-- The uniform residual budget gives strict containment and the anchored residual bound at the supplied point.

The retained clearance-quarter budget gives strict containment. Monotonicity
of the two squared-radius budgets then gives the corresponding anchored residual bound. -/
public theorem uniform_residual_strict_and_anchored
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (contains : current.box.Contains point)
    {cap : Fraction.Rational} (capPositive : 0 < cap)
    (residual : Data.Gaussian.Norm.Basic.normSq (p.eval point) <
      Newton.Restart.Uniform.Budget.uniformAnchoredResidualTarget squarefree current cap) :
    current.box.StrictContains point ∧
      Data.Gaussian.Norm.Basic.normSq (p.eval point) <
        Newton.Restart.Anchored.Budget.anchoredResidualTarget squarefree current point cap := open Purelib.Algebra.Field
          in by
  let uniform := Newton.Restart.Uniform.Budget.uniformAnchoredRadius squarefree current cap
  let anchored := Newton.Restart.Anchored.Budget.anchoredRadius squarefree current point cap
  have residualQuarter : Data.Gaussian.Norm.Basic.normSq (p.eval point) <
      current.clearance.bound / 4 :=
    residual.trans_le (Order.Basic.min_le_left _ _)
  have quarterLtBound : current.clearance.bound / 4 <
      current.clearance.bound := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      current.clearance.bound * (4 : Fraction.Rational)⁻¹ <
          current.clearance.bound * 1 :=
        Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          current.clearance.positive (by decide)
      _ = current.clearance.bound := by ring1
  have strict := current.clearance.strictContains_of_residual_lt contains
    (residualQuarter.trans quarterLtBound)
  have radiusOrder : uniform ≤ anchored := by
    simpa only [uniform, anchored] using
      uniformAnchoredRadius_le_anchoredRadius squarefree current point contains
        cap residualQuarter
  have radiusSquareOrder : uniform ^ 2 ≤ anchored ^ 2 :=
    Order.Arithmetic.pow_le_pow_direct
      (Newton.Restart.Uniform.Budget.uniformAnchoredRadius_pos squarefree current capPositive).le radiusOrder 2
  have sourceOrder :
      Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * uniform ^ 2) ≤
        Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * anchored ^ 2) := by
    have doubled :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        radiusSquareOrder (show (0 : Fraction.Rational) ≤ 2 by decide)
    exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct doubled
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p current.box).le
  have displacementOrder :
      Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box * uniform ^ 2 ≤
        Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box * anchored ^ 2 :=
    Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      radiusSquareOrder (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin_pos squarefree current.box).le
  have residualUniform : Data.Gaussian.Norm.Basic.normSq (p.eval point) <
      min
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * uniform ^ 2))
        (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box * uniform ^ 2) := by
    exact residual.trans_le (Order.Basic.min_le_right _ _)
  have uniformLeAnchored :
      min
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * uniform ^ 2))
          (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box * uniform ^ 2) ≤
        min
          (Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * anchored ^ 2))
          (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box * anchored ^ 2) :=
    le_min
      (Data.Rat.Fraction.Order.Basic.le_trans _ _ _
        (Order.Basic.min_le_left _ _) sourceOrder)
      (Data.Rat.Fraction.Order.Basic.le_trans _ _ _
        (Order.Basic.min_le_right _ _) displacementOrder)
  exact ⟨strict, by
    simpa only [Newton.Restart.Anchored.Budget.anchoredResidualTarget, uniform, anchored] using
      residualUniform.trans_le uniformLeAnchored⟩

end Purelib.RootIsolation.Newton.Restart.Uniform.Anchored
