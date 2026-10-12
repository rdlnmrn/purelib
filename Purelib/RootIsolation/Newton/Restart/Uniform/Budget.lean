module
import Purelib.Polynomial.Clearance.Box.Region.Basic
public import Purelib.Polynomial.Clearance.Box.Interior
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.List.Minimum
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
public import Purelib.RootIsolation.Newton.Restart.Anchored.Budget
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor

/-!
# Uniform Newton radius and residual budgets

The boundary-clearance strip supplies point-independent caps on a finite
minimum fold. The same selected radius determines source and displacement budgets.
-/

namespace Purelib.RootIsolation.Newton.Restart.Uniform.Budget

open Purelib.Data.Rat.List

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib

/-- Finite radius caps independent of the eventual displayed sample.  The
boundary-clearance strip supplies all four geometric margins at once.

The five entries retain the unit cap, protected boundary strip, external
cap and two Newton coefficient ratios for the supplied polynomial and box. -/
private def uniformAnchoredRadiusValues
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (cap : Fraction.Rational) : List Fraction.Rational :=
  [1,
    current.clearance.residualInteriorRadius / 6,
    cap,
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box /
      (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box),
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box /
      Newton.Restart.Anchored.Budget.anchoredTaylorCoefficient p current.box]

/-- One positive radius valid for every sufficiently small-residual rational
point contained in the winding box.

The right minimum fold starts at one and retains the five radius caps.
The protected strip replaces individual point-dependent boundary gaps. -/
@[expose] public def uniformAnchoredRadius
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (cap : Fraction.Rational) : Fraction.Rational :=
  ([1,
    current.clearance.residualInteriorRadius / 6,
    cap,
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box /
      (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box),
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box /
      (2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
        Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box))] : List Fraction.Rational).foldr min
          1

/-- A positive external cap gives a strictly positive uniform anchored radius.

The clearance strip and both Newton ratios are strictly positive.
Together with the positive external cap and unit entry they bound the folded minimum. -/
public theorem uniformAnchoredRadius_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    {cap : Fraction.Rational} (capPositive : 0 < cap) :
    0 < uniformAnchoredRadius squarefree current cap := by
  change 0 < Minimum.positiveMinimum (uniformAnchoredRadiusValues squarefree current cap)
  apply Minimum.positiveMinimum_pos
  intro value member
  cases member with
  | head =>
      exact (by decide)
  | tail _ member =>
    cases member with
    | head =>
        exact Order.Field.div_pos_direct
              current.clearance.residualInteriorRadius_pos (by decide)
    | tail _ member =>
      cases member with
      | head =>
          exact capPositive
      | tail _ member =>
        cases member with
        | head =>
            exact Order.Field.div_pos_direct
                  (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold_pos squarefree current.box)
                  (Order.Arithmetic.mul_pos_direct (by decide)
                    (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p current.box))
        | tail _ member =>
          cases member with
          | head =>
              exact Order.Field.div_pos_direct
                    (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin_pos squarefree current.box)
                    (Newton.Restart.Anchored.Budget.anchoredTaylorCoefficient_pos p current.box)
          | tail _ member =>
            cases member

/-- The uniform radius satisfies the unit, protected-strip, external-cap, residual and Taylor caps simultaneously.

Each cap appears in the original five-entry list. Its membership bound
concerns the same folded radius and retains the conjunction order of those entries. -/
public theorem uniformAnchoredRadius_bounds
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (cap : Fraction.Rational) :
    let radius := uniformAnchoredRadius squarefree current cap
    radius ≤ 1 ∧
      radius ≤ current.clearance.residualInteriorRadius / 6 ∧
      radius ≤ cap ∧
      radius ≤ Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box /
        (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box) ∧
      radius ≤ Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box /
        (2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
          Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box)) := by
  let values := uniformAnchoredRadiusValues squarefree current cap
  have below (value : Fraction.Rational) (member : value ∈ values) :
      Minimum.positiveMinimum values ≤ value := Minimum.positiveMinimum_le_of_mem member
  exact
    ⟨below 1 (List.Mem.head _),
      below (current.clearance.residualInteriorRadius / 6)
        (List.Mem.tail _ (List.Mem.head _)),
      below cap (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      below (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box /
          (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box))
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
      below (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box /
          Newton.Restart.Anchored.Budget.anchoredTaylorCoefficient p current.box)
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))⟩

/-- A cap below the point-independent unit-cap reference radius is the exact uniform anchored radius.

The reference radius uses cap one and bounds the remaining four entries.
The supplied cap then bounds the full list from below while remaining an entry. -/
public theorem uniformAnchoredRadius_eq_cap_of_le_reference
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient) {cap : Fraction.Rational}
    (capLeReference :
      cap ≤ uniformAnchoredRadius squarefree current 1) :
    uniformAnchoredRadius squarefree current cap = cap := by
  apply le_antisymm
  · exact (uniformAnchoredRadius_bounds squarefree current cap).2.2.1
  · have bounds := uniformAnchoredRadius_bounds squarefree current 1
    change cap ≤ Minimum.positiveMinimum
      (uniformAnchoredRadiusValues squarefree current cap)
    apply Minimum.le_positiveMinimum
    · exact capLeReference.trans bounds.1
    · intro value member
      cases member with
      | head =>
          exact capLeReference.trans bounds.1
      | tail _ member =>
        cases member with
        | head =>
            exact capLeReference.trans bounds.2.1
        | tail _ member =>
          cases member with
          | head =>
              exact le_rfl
          | tail _ member =>
            cases member with
            | head =>
                exact capLeReference.trans bounds.2.2.2.1
            | tail _ member =>
              cases member with
              | head =>
                  exact capLeReference.trans bounds.2.2.2.2
              | tail _ member =>
                cases member

/-- Point-independent residual target: one quarter of the boundary clearance
ensures a uniform interior strip, while the other two terms are the ordinary
source-variation and Newton-displacement budgets at the uniform radius.

The minimum retains the clearance quarter and the source and displacement
budgets computed from the selected uniform radius squared. -/
@[expose] public def uniformAnchoredResidualTarget
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (cap : Fraction.Rational) : Fraction.Rational :=
  let radius := uniformAnchoredRadius squarefree current cap
  min (current.clearance.bound / 4)
    (min
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * radius ^ 2))
      (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box * radius ^ 2))

/-- A positive external cap gives a strictly positive point-independent residual target.

The external cap gives a positive uniform radius. The clearance and
polynomial coefficients are positive, making all three retained minimum entries positive. -/
public theorem uniformAnchoredResidualTarget_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    {cap : Fraction.Rational} (capPositive : 0 < cap) :
    0 < uniformAnchoredResidualTarget squarefree current cap := by
  let radius := uniformAnchoredRadius squarefree current cap
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      uniformAnchoredRadius_pos squarefree current capPositive
  exact Order.Basic.lt_min
    (Order.Field.div_pos_direct current.clearance.positive
      (by decide))
    (Order.Basic.lt_min
      (Order.Arithmetic.mul_pos_direct
        (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p current.box)
        (Order.Arithmetic.mul_pos_direct (by decide)
          (Order.Arithmetic.pow_pos_direct radiusPositive 2)))
      (Order.Arithmetic.mul_pos_direct
        (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin_pos squarefree current.box)
        (Order.Arithmetic.pow_pos_direct radiusPositive 2)))

end Purelib.RootIsolation.Newton.Restart.Uniform.Budget
