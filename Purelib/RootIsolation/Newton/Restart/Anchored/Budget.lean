module
public import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.List.Minimum
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Squarefree
public import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Band.Parameters
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Anchored Newton radius and residual budgets

A displayed strict interior point supplies four signed box margins. Together
with an external cap and polynomial bounds they determine its folded radius.
-/

namespace Purelib.RootIsolation.Newton.Restart.Anchored.Budget

open Purelib.Data.Rat.List

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib

/-- Compute twice the extraction-band Taylor coefficient times the box remainder bound.

Twice the extraction-band coefficient scales the box remainder ceiling.
Both factors use the supplied polynomial and the same retained box. -/
@[expose] public def anchoredTaylorCoefficient
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box) : Fraction.Rational :=
  2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
    Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p box)

/-- The anchored Taylor coefficient is strictly positive.

The extraction coefficient is the displayed positive product of fixed
rational constants, and the box remainder ceiling is strictly positive. -/
public theorem anchoredTaylorCoefficient_pos
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Box) :
    0 < anchoredTaylorCoefficient p box := by
  have twoPositive : (0 : Fraction.Rational) < 2 := by decide
  have fourPositive : (0 : Fraction.Rational) < 4 := by decide
  have ninePositive : (0 : Fraction.Rational) < 9 := by decide
  have extractionPositive :
      0 < Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient := by
    unfold Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient
    exact Order.Arithmetic.mul_pos_direct
      (Order.Arithmetic.mul_pos_direct fourPositive ninePositive)
      ninePositive
  exact Order.Arithmetic.mul_pos_direct twoPositive
    (Order.Arithmetic.mul_pos_direct extractionPositive
      (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p box))

/-- Finite list of every positive scalar cap used for a rational point
strictly inside a winding box.

The list retains the four signed interior gaps, the external cap and both
Newton coefficient ratios in their displayed order, preceded by the unit cap. -/
@[expose] public def anchoredRadiusValues
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (cap : Fraction.Rational) : List Fraction.Rational :=
  [1,
    (point.re - current.box.xLower) / 6,
    (current.box.xUpper - point.re) / 6,
    (point.im - current.box.yLower) / 6,
    (current.box.yUpper - point.im) / 6,
    cap,
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box /
      (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box),
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box /
      anchoredTaylorCoefficient p current.box]

/-- One positive rational radius below every geometric, Newton, Taylor, and
external cap for the displayed strict interior point.

The right minimum fold starts at one and scans all eight caps.
The four geometric gaps and two Newton ratios use the same supplied point and box. -/
@[expose] public def anchoredRadius
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (cap : Fraction.Rational) : Fraction.Rational :=
  ([1,
    (point.re - current.box.xLower) / 6,
    (current.box.xUpper - point.re) / 6,
    (point.im - current.box.yLower) / 6,
    (current.box.yUpper - point.im) / 6,
    cap,
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box /
      (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box),
    Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box /
      (2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
        Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box))] : List Fraction.Rational).foldr min
          1

/-- A strict interior sample and positive external cap give a strictly positive anchored radius.

Strict containment makes each signed boundary gap positive. The external
cap and the positive Newton coefficient ratios complete positivity of all entries. -/
public theorem anchoredRadius_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (strict : current.box.StrictContains point)
    {cap : Fraction.Rational} (capPositive : 0 < cap) :
    0 < anchoredRadius squarefree current point cap := by
  change 0 < Minimum.positiveMinimum (anchoredRadiusValues squarefree current point cap)
  apply Minimum.positiveMinimum_pos
  intro value member
  cases member with
  | head =>
      exact (by decide)
  | tail _ member =>
    cases member with
    | head =>
        exact Order.Field.div_pos_direct
              (Order.Arithmetic.sub_pos_direct strict.1) (by decide)
    | tail _ member =>
      cases member with
      | head =>
          exact Order.Field.div_pos_direct
                (Order.Arithmetic.sub_pos_direct strict.2.1) (by decide)
      | tail _ member =>
        cases member with
        | head =>
            exact Order.Field.div_pos_direct
                  (Order.Arithmetic.sub_pos_direct strict.2.2.1) (by decide)
        | tail _ member =>
          cases member with
          | head =>
              exact Order.Field.div_pos_direct
                    (Order.Arithmetic.sub_pos_direct strict.2.2.2) (by decide)
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
                          (anchoredTaylorCoefficient_pos p current.box)
                | tail _ member =>
                  cases member

/-- The anchored radius satisfies its eight retained scalar caps.

Each listed cap bounds the same folded radius. The nested conjunction
records the unit, four geometric, external, residual and Taylor bounds in list order. -/
public theorem anchoredRadius_bounds
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (cap : Fraction.Rational) :
    let radius := anchoredRadius squarefree current point cap
    radius ≤ 1 ∧
      radius ≤ (point.re - current.box.xLower) / 6 ∧
      radius ≤ (current.box.xUpper - point.re) / 6 ∧
      radius ≤ (point.im - current.box.yLower) / 6 ∧
      radius ≤ (current.box.yUpper - point.im) / 6 ∧
      radius ≤ cap ∧
      radius ≤ Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box /
        (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box) ∧
      radius ≤ Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box /
        (2 * (Dense.Gaussian.Newton.Box.Band.Parameters.extractionBandTaylorCoefficient *
          Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p current.box)) := by
  let values := anchoredRadiusValues squarefree current point cap
  have below (value : Fraction.Rational) (member : value ∈ values) :
      Minimum.positiveMinimum values ≤ value :=
    Minimum.positiveMinimum_le_of_mem member
  exact
    ⟨below 1 (List.Mem.head _),
      below ((point.re - current.box.xLower) / 6)
        (List.Mem.tail _ (List.Mem.head _)),
      below ((current.box.xUpper - point.re) / 6)
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      below ((point.im - current.box.yLower) / 6)
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
      below ((current.box.yUpper - point.im) / 6)
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))),
      below cap (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head
        _)))))),
      below (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeThreshold squarefree current.box /
          (4 * Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box))
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.head _))))))),
      below (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box /
          anchoredTaylorCoefficient p current.box)
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.head _))))))))⟩

/-- Positive residual target simultaneously small enough for the anchored
source variation and the derivative-normalized Newton displacement.

The target selects the smaller source-variation and derivative-displacement
budgets, both computed from the same selected anchored radius squared. -/
@[expose] public def anchoredResidualTarget
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (cap : Fraction.Rational) : Fraction.Rational :=
  let radius := anchoredRadius squarefree current point cap
  min
    (Dense.Gaussian.Bounds.Box.denseLipschitzBound p current.box * (2 * radius ^ 2))
    (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin squarefree current.box * radius ^ 2)

/-- The anchored residual target is positive for a strict interior sample and positive external cap.

Strict containment and the positive external cap give a positive radius.
The source and derivative coefficients are positive, as are both resulting budgets. -/
public theorem anchoredResidualTarget_pos
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (strict : current.box.StrictContains point)
    {cap : Fraction.Rational} (capPositive : 0 < cap) :
    0 < anchoredResidualTarget squarefree current point cap := by
  let radius := anchoredRadius squarefree current point cap
  have radiusPositive : 0 < radius :=
    anchoredRadius_pos squarefree current point strict capPositive
  exact Order.Basic.lt_min
    (Order.Arithmetic.mul_pos_direct
      (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p current.box)
      (Order.Arithmetic.mul_pos_direct (by decide)
        (Order.Arithmetic.pow_pos_direct radiusPositive 2)))
    (Order.Arithmetic.mul_pos_direct
      (Dense.Gaussian.Derivative.Separation.Squarefree.derivativeMargin_pos squarefree current.box)
      (Order.Arithmetic.pow_pos_direct radiusPositive 2))

/-- The computed anchored radius does not exceed the supplied external cap.

The external cap is retained as the sixth entry of the radius list.
Its membership bound applies to the original selected folded radius. -/
public theorem anchoredRadius_le_cap
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) (cap : Fraction.Rational) :
    anchoredRadius squarefree current point cap ≤ cap :=
  (anchoredRadius_bounds squarefree current point cap).2.2.2.2.2.1

/-- A cap below the unit-cap reference radius is the exact anchored radius.

The reference radius uses cap one and bounds every other retained entry.
A cap below that reference is both a list entry and a common lower bound. -/
public theorem anchoredRadius_eq_cap_of_le_reference
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (current : Clearance.Box.Region.ProtectedAmbient p ambient)
    (point : Gaussian.Basic.Canonical) {cap : Fraction.Rational}
    (capLeReference :
      cap ≤ anchoredRadius squarefree current point 1) :
    anchoredRadius squarefree current point cap = cap := by
  apply le_antisymm
  · exact anchoredRadius_le_cap squarefree current point cap
  · have bounds := anchoredRadius_bounds squarefree current point 1
    change cap ≤ Minimum.positiveMinimum
      (anchoredRadiusValues squarefree current point cap)
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
              exact capLeReference.trans bounds.2.2.1
          | tail _ member =>
            cases member with
            | head =>
                exact capLeReference.trans bounds.2.2.2.1
            | tail _ member =>
              cases member with
              | head =>
                  exact capLeReference.trans bounds.2.2.2.2.1
              | tail _ member =>
                cases member with
                | head =>
                    exact le_rfl
                | tail _ member =>
                  cases member with
                  | head =>
                      exact capLeReference.trans bounds.2.2.2.2.2.2.1
                  | tail _ member =>
                    cases member with
                    | head =>
                        exact capLeReference.trans bounds.2.2.2.2.2.2.2
                    | tail _ member =>
                      cases member

end Purelib.RootIsolation.Newton.Restart.Anchored.Budget
