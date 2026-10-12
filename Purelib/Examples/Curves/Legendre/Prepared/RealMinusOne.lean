module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Riemann.Paths.PreparedClearPathModels.Execution
import Purelib.Data.Fin
import Purelib.Data.Fin.Cases
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
import Purelib.Polynomial.Squarefree.Bezout.Evaluation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
public import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Translated
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.SquareRootDegree
public import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Tactic.Ring

section
public section

/-!
# Explicit finite branch data for a rational Legendre curve

This module constructs the real genus-one curve
`y² = x (x - 1) (x + 1)` from an explicit squarefree certificate, isolates
its three finite branch points in rational boxes, and supplies exact local
quadratic owners for both sheets.  The final declarations expose bounded
prepared-bank attempts for the canonical A and B paths and promote successful
executions to a certified period schedule, while retaining the constructive
total preparation as a fallback.
-/

namespace Purelib.Examples.Curves.Legendre.Prepared.RealMinusOne

open Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
open Purelib.Polynomial.Winding
open Purelib.Data.Fin
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath
open Purelib.Polynomial.Clearance.Box.Line.Basic (VerticalLineClearance)
open Purelib.Polynomial.Clearance.Box.Line.Basic (HorizontalLineClearance)

open Purelib.Examples

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.Geometry.Rational.Box.Square

open Purelib.Polynomial.Dense.Gaussian.Basic.ExplicitLegendrePreparedData (GaussianPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Linear
open Purelib.Data.Rat.Fraction renaming Rational -> Coordinate
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)

/-- The displayed cubic factorization (x+1)x(x-1). -/
@[expose] def factors : GaussianPolynomial :=
  (Translated.translatedCoordinate (Gaussian.Components.Basic.point (-1) 0) *
    Translated.translatedCoordinate (Gaussian.Components.Basic.point 0 0)) *
      Translated.translatedCoordinate (Gaussian.Components.Basic.point 1 0)

/-- The Gaussian polynomial with descending coefficients [1,0,-1,0]. -/
@[expose] def polynomial : GaussianPolynomial :=
  ⟨[1, 0, -1, 0]⟩

/-- The displayed coefficient polynomial equals (x+1)x(x-1). -/
theorem polynomial_eq_factors : polynomial = factors := by decide

/-- The displayed cubic is not the zero polynomial. -/
theorem polynomial_nonzero : polynomial.isZero = false := by decide

/-- The displayed polynomial has degree three. -/
theorem polynomial_degree : polynomial.natDegree = 3 := by decide

/-- The displayed cubic evaluates to z cubed minus z. -/
@[simp] theorem polynomial_eval (z : Gaussian.Basic.Canonical) :
    polynomial.eval z = z ^ 3 - z := by
  unfold polynomial Dense.Basic.DensePolynomial.eval
    Dense.Basic.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The linear Bézout coefficient -9z/2 for the cubic. -/
@[expose] def bezoutLeft : GaussianPolynomial := ⟨[Gaussian.Basic.ExplicitLegendrePreparedData.point (-9 / 2) 0, 0]⟩

/-- The quadratic Bézout coefficient 3z²/2-1 for the derivative. -/
@[expose] def bezoutRight : GaussianPolynomial := ⟨[Gaussian.Basic.ExplicitLegendrePreparedData.point (3 / 2) 0, 0, -1]⟩

/-- The left Bézout coefficient evaluates to -9z/2. -/
@[simp] theorem bezoutLeft_eval (z : Gaussian.Basic.Canonical) :
    bezoutLeft.eval z = Gaussian.Basic.ExplicitLegendrePreparedData.point (-9 / 2) 0 * z := by
  unfold bezoutLeft Dense.Basic.DensePolynomial.eval
    Dense.Basic.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The right Bézout coefficient evaluates to 3z²/2-1. -/
@[simp] theorem bezoutRight_eval (z : Gaussian.Basic.Canonical) :
    bezoutRight.eval z = Gaussian.Basic.ExplicitLegendrePreparedData.point (3 / 2) 0 * z ^ 2 - 1 := by
  unfold bezoutRight Dense.Basic.DensePolynomial.eval
    Dense.Basic.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- The derivative of the displayed cubic evaluates to 3z²-1. -/
@[simp] theorem derivative_eval (z : Gaussian.Basic.Canonical) :
    (Dense.Gaussian.GCD.derivative polynomial).eval z = 3 * z ^ 2 - 1 := by
  unfold polynomial Dense.Gaussian.GCD.derivative
  rw [Dense.Derivative.eval_derivative]
  unfold Dense.Derivative.evalDerivativeCoeffs
    Dense.Derivative.evalDerivativeStep
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

/-- Certify squarefreeness of the displayed cubic by the retained explicit Bézout identity.

The coefficients -9z/2 and 3z²/2-1 combine the cubic and its derivative to give one. -/
@[expose] def polynomial_squarefree :
    Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate polynomial :=
  Squarefree.Bezout.Evaluation.squarefreeOfEvalBezout polynomial polynomial_nonzero
    bezoutLeft bezoutRight (by
      intro z
      rw [bezoutLeft_eval, polynomial_eval, bezoutRight_eval, derivative_eval]
      apply Gaussian.Field.mul_right_cancel_of_ne
        (factor := 2) (by decide)
      have leftScaled : Gaussian.Basic.ExplicitLegendrePreparedData.point (-9 / 2) 0 * 2 = -9 := by decide
      have rightScaled : Gaussian.Basic.ExplicitLegendrePreparedData.point (3 / 2) 0 * 2 = 3 := by decide
      calc
        (Gaussian.Basic.ExplicitLegendrePreparedData.point (-9 / 2) 0 * z * (z ^ 3 - z) +
              (Gaussian.Basic.ExplicitLegendrePreparedData.point (3 / 2) 0 * z ^ 2 - 1) * (3 * z ^ 2 - 1)) * 2 =
            (Gaussian.Basic.ExplicitLegendrePreparedData.point (-9 / 2) 0 * 2) * z * (z ^ 3 - z) +
              ((Gaussian.Basic.ExplicitLegendrePreparedData.point (3 / 2) 0 * 2) * z ^ 2 - 2) *
                (3 * z ^ 2 - 1) := by ring1
        _ = (-9) * z * (z ^ 3 - z) +
              (3 * z ^ 2 - 2) * (3 * z ^ 2 - 1) := by
          rw [leftScaled, rightScaled]
        _ = 1 * 2 := by ring1)

/-- The rational Legendre member `y² = x (x - 1) (x + 1)`. -/
@[expose] def curve : Hyperelliptic.Basic.HyperellipticCurve 1 where
  polynomial := polynomial
  nonzero := polynomial_nonzero
  squarefree := polynomial_squarefree
  degreeShape := .odd (by
    change polynomial.natDegree = 3
    exact polynomial_degree)

/-- The rational root rectangle centered at a real coordinate with horizontal radius 1/4 and vertical radius 1/2. -/
@[expose] def boxAt (x : Fraction.Rational) : Box :=
  { xLower := x - 1 / 4
    xUpper := x + 1 / 4
    yLower := -1 / 2
    yUpper := 1 / 2
    x_valid := by
      apply le_of_lt
      calc
        x - 1 / 4 < x := by
          exact (Fraction.Order.Arithmetic.sub_lt_sub_left_direct
            (by decide : (0 : Fraction.Rational) < 1 / 4) x).trans_eq (by ring1)
        _ < x + 1 / 4 := by
          exact (show x = x + 0 by ring1).trans_lt
            (Fraction.Order.Arithmetic.add_lt_add_left_direct
              (by decide : (0 : Fraction.Rational) < 1 / 4) x)
    y_valid := by decide }

/-- Every displayed real-root rectangle has strictly positive coordinate widths. -/
theorem boxAt_proper (x : Fraction.Rational) : (boxAt x).Proper := by
  constructor
  · change x - 1 / 4 < x + 1 / 4
    calc
      x - 1 / 4 < x := by
        exact (Fraction.Order.Arithmetic.sub_lt_sub_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 4) x).trans_eq (by ring1)
      _ < x + 1 / 4 := by
        exact (show x = x + 0 by ring1).trans_lt
          (Fraction.Order.Arithmetic.add_lt_add_left_direct
            (by decide : (0 : Fraction.Rational) < 1 / 4) x)
  · change (-1 / 2 : Fraction.Rational) < 1 / 2
    decide

/-- Certify the centered linear factor on the boundary of its displayed root rectangle. -/
@[expose] def selfClearance (x : Fraction.Rational) :
    BoundaryClearance
      (Translated.translatedCoordinate (Gaussian.Components.Basic.point x 0)) (boxAt x) :=
  Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearanceBox
    (Gaussian.Basic.ExplicitLegendrePreparedData.point x 0) (by
      unfold boxAt Gaussian.Basic.ExplicitLegendrePreparedData.point
      exact (Fraction.Order.Arithmetic.sub_lt_sub_left_direct
        (by decide : (0 : Fraction.Rational) < 1 / 4) x).trans_eq (by ring1))
    (by
      unfold boxAt Gaussian.Basic.ExplicitLegendrePreparedData.point
      exact (show x = x + 0 by ring1).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct
          (by decide : (0 : Fraction.Rational) < 1 / 4) x))
    (by change (-1 / 2 : Fraction.Rational) < 0; decide)
    (by change (0 : Fraction.Rational) < 1 / 2; decide)

/-- Certify a linear factor whose root lies strictly left of the displayed root rectangle. -/
@[expose] def leftClearance (rootX boxX : Fraction.Rational)
    (separated : rootX < boxX - 1 / 4) :
    BoundaryClearance
      (Translated.translatedCoordinate (Gaussian.Components.Basic.point rootX 0)) (boxAt boxX) :=
  Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_left
    (Gaussian.Basic.ExplicitLegendrePreparedData.point rootX 0) (by
      unfold boxAt Gaussian.Basic.ExplicitLegendrePreparedData.point
      exact separated)

/-- Certify a linear factor whose root lies strictly right of the displayed root rectangle. -/
@[expose] def rightClearance (rootX boxX : Fraction.Rational)
    (separated : boxX + 1 / 4 < rootX) :
    BoundaryClearance
      (Translated.translatedCoordinate (Gaussian.Components.Basic.point rootX 0)) (boxAt boxX) :=
  Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_right
    (Gaussian.Basic.ExplicitLegendrePreparedData.point rootX 0) (by
      unfold boxAt Gaussian.Basic.ExplicitLegendrePreparedData.point
      exact separated)

/-- The displayed cubic has certified nonzero boundary values on the rectangle around minus one. -/
@[expose] def clearanceMinusOne :
    BoundaryClearance polynomial (boxAt (-1)) := by
  rw [polynomial_eq_factors]
  exact BoundaryClearance.mul
    (BoundaryClearance.mul
      (selfClearance (-1)) (rightClearance 0 (-1) (by decide)))
    (rightClearance 1 (-1) (by decide))

/-- The displayed cubic has certified nonzero boundary values on the rectangle around zero. -/
@[expose] def clearanceZero :
    BoundaryClearance polynomial (boxAt 0) := by
  rw [polynomial_eq_factors]
  exact BoundaryClearance.mul
    (BoundaryClearance.mul
      (leftClearance (-1) 0 (by decide)) (selfClearance 0))
    (rightClearance 1 0 (by decide))

/-- The displayed cubic has certified nonzero boundary values on the rectangle around one. -/
@[expose] def clearanceOne :
    BoundaryClearance polynomial (boxAt 1) := by
  rw [polynomial_eq_factors]
  exact BoundaryClearance.mul
    (BoundaryClearance.mul
      (leftClearance (-1) 1 (by decide))
      (leftClearance 0 1 (by decide)))
    (selfClearance 1)

/-- Certify the cubic on a vertical ambient line whose real coordinate avoids -1, zero and one. -/
@[expose] def verticalClearance (x : Fraction.Rational)
    (apartMinusOne : x ≠ -1) (apartZero : x ≠ 0)
    (apartOne : x ≠ 1) :
    VerticalLineClearance polynomial
      (Box.largeSquareBox polynomial) x := by
  rw [polynomial_eq_factors]
  exact VerticalLineClearance.mul
    (VerticalLineClearance.mul
      (Clearance.Box.Line.Translated.translatedCoordinate_verticalLineClearance
        (Gaussian.Basic.ExplicitLegendrePreparedData.point (-1) 0) _ x apartMinusOne)
      (Clearance.Box.Line.Translated.translatedCoordinate_verticalLineClearance
        (Gaussian.Basic.ExplicitLegendrePreparedData.point 0 0) _ x apartZero))
    (Clearance.Box.Line.Translated.translatedCoordinate_verticalLineClearance
      (Gaussian.Basic.ExplicitLegendrePreparedData.point 1 0) _ x apartOne)

/-- Certify the cubic on a horizontal ambient line with nonzero imaginary coordinate. -/
@[expose] def horizontalClearance (y : Fraction.Rational) (apartZero : y ≠ 0) :
    HorizontalLineClearance polynomial
      (Box.largeSquareBox polynomial) y := by
  rw [polynomial_eq_factors]
  exact HorizontalLineClearance.mul
    (HorizontalLineClearance.mul
      (Clearance.Box.Line.Translated.translatedCoordinate_horizontalLineClearance
        (Gaussian.Basic.ExplicitLegendrePreparedData.point (-1) 0) _ y apartZero)
      (Clearance.Box.Line.Translated.translatedCoordinate_horizontalLineClearance
        (Gaussian.Basic.ExplicitLegendrePreparedData.point 0 0) _ y apartZero))
    (Clearance.Box.Line.Translated.translatedCoordinate_horizontalLineClearance
      (Gaussian.Basic.ExplicitLegendrePreparedData.point 1 0) _ y apartZero)

/-- A displayed root rectangle refines the original large ambient square when its two horizontal bounds fit. -/
theorem refinesAmbient (x : Fraction.Rational)
    (lowerX : -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ≤
      (boxAt x).xLower)
    (upperX : (boxAt x).xUpper ≤
      Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial) :
    (boxAt x).Refines (Box.largeSquareBox polynomial) := by
  unfold Rational.Box.Refines Box.largeSquareBox
    Rational.Box.symmetric
  exact ⟨lowerX, upperX,
    (by
        change -Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial ≤ (-1 / 2 : Fraction.Rational);
        decide),
    (by
        change (1 / 2 : Fraction.Rational) ≤ Dense.Gaussian.Bounds.RootRadius.denseLargeSquareRadius polynomial;
        decide)⟩

/-- The displayed cubic has quadrupled winding four on the rectangle around minus one. -/
theorem windingMinusOne :
    Box.Basic.quadrupledBoxWinding polynomial (boxAt (-1)) = 4 := by
  decide

/-- The displayed cubic has quadrupled winding four on the rectangle around zero. -/
theorem windingZero :
    Box.Basic.quadrupledBoxWinding polynomial (boxAt 0) = 4 := by
  decide

/-- The displayed cubic has quadrupled winding four on the rectangle around one. -/
theorem windingOne :
    Box.Basic.quadrupledBoxWinding polynomial (boxAt 1) = 4 := by
  decide

/-- The original root rectangle around minus one, ambient refinement, boundary clearance and nonzero winding
certificate. -/
@[expose] def rawMinusOne : State.Raw.RawWindingState polynomial
    (Box.largeSquareBox polynomial) where
  box := boxAt (-1)
  refinesAmbient := refinesAmbient (-1) (by decide) (by decide)
  proper := boxAt_proper (-1)
  clearance := clearanceMinusOne
  rawWinding_ne := by rw [windingMinusOne]; decide

/-- The original root rectangle around zero, ambient refinement, boundary clearance and nonzero winding certificate. -/
@[expose] def rawZero : State.Raw.RawWindingState polynomial
    (Box.largeSquareBox polynomial) where
  box := boxAt 0
  refinesAmbient := refinesAmbient 0 (by decide) (by decide)
  proper := boxAt_proper 0
  clearance := clearanceZero
  rawWinding_ne := by rw [windingZero]; decide

/-- The original root rectangle around one, ambient refinement, boundary clearance and nonzero winding certificate. -/
@[expose] def rawOne : State.Raw.RawWindingState polynomial
    (Box.largeSquareBox polynomial) where
  box := boxAt 1
  refinesAmbient := refinesAmbient 1 (by decide) (by decide)
  proper := boxAt_proper 1
  clearance := clearanceOne
  rawWinding_ne := by rw [windingOne]; decide

/-- Upgrade an exact raw winding state to winding one using winding four and all four ambient line clearances. -/
@[expose] def stateOfRaw
    (raw : State.Raw.RawWindingState polynomial
      (Box.largeSquareBox polynomial))
    (windingFour : Box.Basic.quadrupledBoxWinding polynomial raw.box = 4)
    (left : VerticalLineClearance polynomial
      (Box.largeSquareBox polynomial) raw.box.xLower)
    (right : VerticalLineClearance polynomial
      (Box.largeSquareBox polynomial) raw.box.xUpper)
    (bottom : HorizontalLineClearance polynomial
      (Box.largeSquareBox polynomial) raw.box.yLower)
    (top : HorizontalLineClearance polynomial
      (Box.largeSquareBox polynomial) raw.box.yUpper) :
    WindingOneState polynomial
      (Box.largeSquareBox polynomial) where
  box := raw.box
  refinesAmbient := raw.refinesAmbient
  proper := raw.proper
  clearance := raw.clearance
  rawWindingFour := windingFour
  ambientLeftClearance := left
  ambientRightClearance := right
  ambientBottomClearance := bottom
  ambientTopClearance := top

/-- The winding-one state around minus one retaining all four ambient line clearances. -/
@[expose] def stateMinusOne := stateOfRaw rawMinusOne windingMinusOne
  (verticalClearance (boxAt (-1)).xLower (by decide) (by decide) (by decide))
  (verticalClearance (boxAt (-1)).xUpper (by decide) (by decide) (by decide))
  (horizontalClearance (boxAt (-1)).yLower (by decide))
  (horizontalClearance (boxAt (-1)).yUpper (by decide))

/-- The winding-one state around zero retaining all four ambient line clearances. -/
@[expose] def stateZero := stateOfRaw rawZero windingZero
  (verticalClearance (boxAt 0).xLower (by decide) (by decide) (by decide))
  (verticalClearance (boxAt 0).xUpper (by decide) (by decide) (by decide))
  (horizontalClearance (boxAt 0).yLower (by decide))
  (horizontalClearance (boxAt 0).yUpper (by decide))

/-- The winding-one state around one retaining all four ambient line clearances. -/
@[expose] def stateOne := stateOfRaw rawOne windingOne
  (verticalClearance (boxAt 1).xLower (by decide) (by decide) (by decide))
  (verticalClearance (boxAt 1).xUpper (by decide) (by decide) (by decide))
  (horizontalClearance (boxAt 1).yLower (by decide))
  (horizontalClearance (boxAt 1).yUpper (by decide))

/-- The three explicit winding-one states in root order -1, zero, one. -/
@[expose] def stateAt : Fin 3 → WindingOneState polynomial
    (Box.largeSquareBox polynomial) :=
  Data.Fin.casesDependent (size := 2) (motive := fun _ => WindingOneState polynomial
    (Box.largeSquareBox polynomial)) stateMinusOne (fun following =>
    Data.Fin.casesDependent (size := 1) (motive := fun _ => WindingOneState polynomial
      (Box.largeSquareBox polynomial)) stateZero (fun last =>
      Data.Fin.casesDependent (size := 0) (motive := fun _ => WindingOneState polynomial
        (Box.largeSquareBox polynomial)) stateOne
        (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) last) following)

/-- Distinct displayed root indices have separated winding-one boxes. -/
theorem stateAt_pairwise : ∀ left right : Fin 3, left ≠ right →
    (stateAt left).box.Separated (stateAt right).box := by
  intro left right different
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

/-- Reindex the displayed winding-one states by the curve polynomial degree. -/
@[expose] def curveStateAt (index : Fin curve.polynomial.natDegree) :
    WindingOneState curve.polynomial
      (Box.largeSquareBox curve.polynomial) :=
  stateAt (Fin.cast polynomial_degree index)

/-- Distinct degree-indexed curve states retain separated root boxes. -/
theorem curveStateAt_pairwise
    (left right : Fin curve.polynomial.natDegree) (different : left ≠ right) :
    (curveStateAt left).box.Separated (curveStateAt right).box := by
  apply stateAt_pairwise
  intro equal
  apply different
  apply Fin.ext
  exact congrArg Fin.val equal

/-- The curve polynomial has degree greater than one. -/
theorem degreeGtOne : 1 < curve.polynomial.natDegree := by
  change 1 < polynomial.natDegree
  rw [polynomial_degree]
  decide

/-- The degree-complete finite branch isolation data constructed from the three displayed winding-one states. -/
@[expose] def branchData : Hyperelliptic.Branches.BranchIsolation.Data curve :=
  Hyperelliptic.Branches.BranchIsolation.Data.ofStates curve degreeGtOne
    curveStateAt curveStateAt_pairwise

/-- The retained branch data has exactly three sites. -/
theorem branchData_siteCount : branchData.siteCount = 3 := rfl

/-! ## Exact quadratic owners at the three finite branch anchors -/

/-- Convert a displayed root index to the corresponding retained branch-data index. -/
@[expose] def branchIndex (index : Fin 3) :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branchData :=
  Fin.cast branchData_siteCount.symm index

/-- The exact lower-left anchors of the three displayed branch boxes. -/
@[expose] def squareRootEndpointPoint : Fin 3 → Gaussian.Basic.Canonical :=
  Data.Fin.casesDependent (size := 2) (motive := fun _ => Gaussian.Basic.Canonical)
    (Gaussian.Basic.ExplicitLegendrePreparedData.point (-5 / 4) (-1 / 2)) (fun second =>
      Data.Fin.casesDependent (size := 1) (motive := fun _ => Gaussian.Basic.Canonical)
        (Gaussian.Basic.ExplicitLegendrePreparedData.point (-1 / 4) (-1 / 2)) (fun third =>
          Data.Fin.casesDependent (size := 0) (motive := fun _ => Gaussian.Basic.Canonical)
            (Gaussian.Basic.ExplicitLegendrePreparedData.point (3 / 4) (-1 / 2))
            (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) third) second)

/-- At refinement depth zero, each retained branch-track anchor is its displayed lower-left endpoint. -/
theorem refinedTrackAnchor_eq_squareRootEndpointPoint : ∀ index : Fin 3,
    Hyperelliptic.Branches.Cuts.refinedTrackAnchor branchData degreeGtOne
        (branchIndex index) 0 = squareRootEndpointPoint index := by
  intro index
  rcases Cases.three index with indexZero | indexOne | indexTwo <;>
    subst index <;> rfl

/-- Evaluate the exact cubic at the selected branch-box anchor. -/
@[expose] def squareRootParameter (index : Fin 3) : Gaussian :=
  polynomial.eval (squareRootEndpointPoint index)

/-- The displayed Gaussian centers 1-i, 3/4+i/3 and -i for the three positive-sheet owners. -/
@[expose] def positiveSquareRootCenter : Fin 3 → Gaussian.Basic.Canonical :=
  Data.Fin.casesDependent (size := 2) (motive := fun _ => Gaussian.Basic.Canonical)
    (Gaussian.Basic.ExplicitLegendrePreparedData.point 1 (-1)) (fun second =>
      Data.Fin.casesDependent (size := 1) (motive := fun _ => Gaussian.Basic.Canonical)
        (Gaussian.Basic.ExplicitLegendrePreparedData.point (3 / 4) (1 / 3)) (fun third =>
          Data.Fin.casesDependent (size := 0) (motive := fun _ => Gaussian.Basic.Canonical)
            (Gaussian.Basic.ExplicitLegendrePreparedData.point 0 (-1))
            (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) third) second)

/-- Select the displayed square-root center or its negative according to the retained sheet index. -/
@[expose] def squareRootCenter (index : Fin 3) : Fin 2 → Gaussian.Basic.Canonical :=
  Data.Fin.casesDependent (size := 1) (motive := fun _ => Gaussian.Basic.Canonical) (positiveSquareRootCenter index)
    (fun last =>
    Data.Fin.casesDependent (size := 0) (motive := fun _ => Gaussian.Basic.Canonical) (-positiveSquareRootCenter index)
      (fun impossible => False.elim (Nat.not_lt_zero impossible.val impossible.isLt)) last)

/-- The square of radius one half centered at the selected sheet-owner center. -/
@[expose] def squareRootOwnerBox (index : Fin 3) (sheet : Fin 2) : Box :=
  Centered.Affine.centeredSquare (squareRootCenter index sheet)
    (1 / 2) (by decide)

/-- The exact quadratic whose roots are the two square roots of the selected cubic endpoint value. -/
@[expose] def squareRootPolynomial (index : Fin 3) : GaussianPolynomial :=
  Purelib.Polynomial.Power.Gaussian.rootPolynomial (squareRootParameter index)
    RootContinuation.SquareRootDegree.degreeTwo

/-- The three displayed cubic endpoint values are all nonzero. -/
theorem squareRootParameter_nonzero :
    ∀ index : Fin 3, squareRootParameter index ≠ 0 := by
  decide +revert

/-- The quadratic vertical determinant is nonzero on the left boundary of every displayed sheet-owner square. -/
theorem squareRootOwner_leftNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).xLower ≠
        0 := by
  decide +revert

/-- The quadratic vertical determinant is nonzero on the right boundary of every displayed sheet-owner square. -/
theorem squareRootOwner_rightNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).xUpper ≠
        0 := by
  decide +revert

/-- The quadratic horizontal determinant is nonzero on the bottom boundary of every displayed sheet-owner square. -/
theorem squareRootOwner_bottomNonzero :
    ∀ index : Fin 3, ∀ sheet : Fin 2,
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).yLower ≠
        0 := by
  decide +revert

/-- The quadratic horizontal determinant is nonzero on the top boundary of every displayed sheet-owner square. -/
theorem squareRootOwner_topNonzero : ∀ index : Fin 3, ∀ sheet : Fin 2,
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      (squareRootParameter index) (squareRootOwnerBox index sheet).yUpper ≠
        0 := by
  decide +revert

/-- Each displayed sheet-owner square has quadrupled quadratic winding four. -/
theorem squareRootOwner_windingFour :
    ∀ index : Fin 3, ∀ sheet : Fin 2,
    Box.Basic.quadrupledBoxWinding (squareRootPolynomial index)
      (squareRootOwnerBox index sheet) = 4 := by
  decide +revert

/-- Construct the exact quadratic sheet owner from its displayed square and four nonzero boundary determinants. -/
@[expose] def squareRootOwner (index : Fin 3) (sheet : Fin 2) :
    Topology.SquareRootContinuationChain.Owner
      (squareRootParameter index) :=
  SquareRoot.Clearance.ExactQuadraticOwnerClearance.directOwnerOfBox
    (squareRootParameter index) (squareRootParameter_nonzero index)
    (squareRootOwnerBox index sheet)
    (Centered.centeredSquare_proper
      (squareRootCenter index sheet) (by decide))
    (squareRootOwner_leftNonzero index sheet)
    (squareRootOwner_rightNonzero index sheet)
    (squareRootOwner_bottomNonzero index sheet)
    (squareRootOwner_topNonzero index sheet)
    (squareRootOwner_windingFour index sheet)

/-- Transport the selected exact quadratic owner to the retained branch-track anchor. -/
@[expose] def branchSquareRootOwner (index : Fin 3) (sheet : Fin 2) :
    Topology.SquareRootContinuationChain.Owner
      (curve.polynomial.eval
        (Hyperelliptic.Branches.Cuts.refinedTrackAnchor branchData degreeGtOne
          (branchIndex index) 0)) := by
  rw [refinedTrackAnchor_eq_squareRootEndpointPoint]
  exact squareRootOwner index sheet

/-! ## Bounded prepared genus-one cycle banks -/

/-- The outer connector subdivision depth, fixed at five. -/
@[expose] def connectorOuterDepth : Nat := 5
/-- The outer boundary subdivision depth, fixed at three. -/
@[expose] def boundaryOuterDepth : Nat := 3
/-- The inner prepared-bank subdivision depth, fixed at three. -/
@[expose] def workingInnerDepth : Nat := 3
/-- The root diameter target, fixed at three. -/
@[expose] def workingRootDiameter : Coordinate := 3

/-- The retained root diameter target is positive. -/
theorem workingRootDiameter_positive : 0 < workingRootDiameter := by decide

/-- A checked dyadic bank at the fixed inner depth and diameter for the exact clear path and starting quadratic owner.
-/
abbrev WorkingBank {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish)
    (owner : Topology.SquareRootContinuationChain.Owner
      (curve.polynomial.eval start)) :=
  DyadicBank
    workingInnerDepth workingRootDiameter workingRootDiameter_positive path
      owner

/-- A finite direct execution retaining the original path, start owner and fixed working request.

Incomplete execution keeps the prepared prefix and its dependent finish owner
for inspection or continuation. -/
abbrev WorkingAttempt {ambient : Rational.Box} {start finish : Gaussian.Basic.Canonical}
    (path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish)
    (within : path.WithinAmbient)
    (owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)) :=
  DyadicBank.Execution .direct workingInnerDepth
    workingRootDiameter workingRootDiameter_positive path within owner

/-- The original depth-zero clear connector between the selected retained branch tracks. -/
@[expose] def rawConnector (left right : Fin 3) :=
  Hyperelliptic.Branches.Cuts.connectorAt branchData degreeGtOne
    (branchIndex left) (branchIndex right) 0

/-- The retained original connector stays within its original ambient square. -/
theorem rawConnector_withinAmbient (left right : Fin 3) :
    (rawConnector left right).WithinAmbient :=
  Hyperelliptic.Branches.Cuts.connectorAt_withinAmbient branchData
    degreeGtOne (branchIndex left) (branchIndex right) 0

/-- The original branch connector refined to the fixed outer connector depth. -/
@[expose] def workingConnector (left right : Fin 3) :=
  Paths.PreparedClearPathModels.dyadicRefinePath
    (rawConnector left right) (rawConnector_withinAmbient left right)
      connectorOuterDepth

/-- The retained refined connector stays within its original ambient square. -/
theorem workingConnector_withinAmbient (left right : Fin 3) :
    (workingConnector left right).WithinAmbient :=
  Paths.PreparedClearPathModels.dyadicRefinePath_withinAmbient
    (rawConnector left right) (rawConnector_withinAmbient left right)
      connectorOuterDepth

/-- Reverse the retained refined connector while preserving its exact endpoints. -/
@[expose] def workingBackwardConnector (left right : Fin 3) :=
  Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse (workingConnector left right)

/-- The retained reversed refined connector stays within its original ambient square. -/
theorem workingBackwardConnector_withinAmbient (left right : Fin 3) :
    (workingBackwardConnector left right).WithinAmbient :=
  Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse_withinAmbient
    (workingConnector left right) (workingConnector_withinAmbient left right)

/-- The selected retained branch state at refinement depth zero. -/
@[expose] def branchState (index : Fin 3) :=
  Hyperelliptic.Branches.Cuts.refinedState branchData degreeGtOne
    (branchIndex index) 0

/-- The original clear boundary path of the selected retained branch state. -/
@[expose] def rawBoundary (index : Fin 3) :=
  Hyperelliptic.Branches.BranchCutLifts.ownerBoundaryPath (branchState index)

/-- The retained original owner boundary stays within its original ambient square. -/
theorem rawBoundary_withinAmbient (index : Fin 3) :
    (rawBoundary index).WithinAmbient :=
  Hyperelliptic.Branches.BranchCutLifts.ownerBoundaryPath_withinAmbient
    (branchState index)

/-- The original branch-owner boundary refined to the fixed outer boundary depth. -/
@[expose] def workingBoundary (index : Fin 3) :=
  Paths.PreparedClearPathModels.dyadicRefinePath
    (rawBoundary index) (rawBoundary_withinAmbient index) boundaryOuterDepth

/-- The retained refined owner boundary stays within its original ambient square. -/
theorem workingBoundary_withinAmbient (index : Fin 3) :
    (workingBoundary index).WithinAmbient :=
  Paths.PreparedClearPathModels.dyadicRefinePath_withinAmbient
    (rawBoundary index) (rawBoundary_withinAmbient index) boundaryOuterDepth

/-- Attempt the fixed-depth checked dyadic bank for the A forward connector from root -1 to zero on sheet zero.

A successful result retains the exact path and starting owner; failure leaves this bounded attempt inconclusive. -/
@[expose] def aForwardAttempt (_ : Unit) :=
  DyadicBank.execute
    (workingConnector 0 1) (workingConnector_withinAmbient 0 1)
    (branchSquareRootOwner 0 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

/-- Attempt the fixed-depth checked dyadic bank for the A right boundary at root zero on sheet zero.

A successful result retains the exact path and starting owner; failure leaves this bounded attempt inconclusive. -/
@[expose] def aRightBoundaryAttempt (_ : Unit) :=
  DyadicBank.execute
    (workingBoundary 1) (workingBoundary_withinAmbient 1)
    (branchSquareRootOwner 1 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

/-- Attempt the fixed-depth checked dyadic bank for the A reversed connector from root zero to -1 on sheet one.

A successful result retains the exact path and starting owner; failure leaves this bounded attempt inconclusive. -/
@[expose] def aBackwardAttempt (_ : Unit) :=
  DyadicBank.execute
    (workingBackwardConnector 0 1)
    (workingBackwardConnector_withinAmbient 0 1)
    (branchSquareRootOwner 1 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

/-- Attempt the fixed-depth checked dyadic bank for the A left boundary at root -1 on sheet one.

A successful result retains the exact path and starting owner; failure leaves this bounded attempt inconclusive. -/
@[expose] def aLeftBoundaryAttempt (_ : Unit) :=
  DyadicBank.execute
    (workingBoundary 0) (workingBoundary_withinAmbient 0)
    (branchSquareRootOwner 0 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

/-- Assemble the A-cycle double boundary path from four already checked dyadic banks.

The forward and backward connector banks and the two owner-boundary banks retain their original paths, sheet owners,
depths and root diameter. -/
@[expose] def executedABoundaryData
    (forward : WorkingBank (workingConnector 0 1)
      (branchSquareRootOwner 0 0))
    (rightBoundary : WorkingBank (workingBoundary 1)
      (branchSquareRootOwner 1 0))
    (backward : WorkingBank (workingBackwardConnector 0 1)
      (branchSquareRootOwner 1 1))
    (leftBoundary : WorkingBank (workingBoundary 0)
      (branchSquareRootOwner 0 1)) :
    Topology.PreparedCycleModels.PreparedBoundaryDoublePath curve :=
  { leftAmbient := Hyperelliptic.Branches.Cuts.Ambient curve
    rightAmbient := Hyperelliptic.Branches.Cuts.Ambient curve
    connectorAmbient := Hyperelliptic.Branches.Cuts.Ambient curve
    leftState := branchState 0
    rightState := branchState 1
    connector := workingConnector 0 1
    rightBoundaryPath := workingBoundary 1
    leftBoundaryPath := workingBoundary 0
    forwardDepth := workingInnerDepth
    rightBoundaryDepth := workingInnerDepth
    backwardDepth := workingInnerDepth
    leftBoundaryDepth := workingInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    rightBoundaryOwner := branchSquareRootOwner 1 0
    rightBoundaryChecked := rightBoundary
    backwardOwner := branchSquareRootOwner 1 1
    backwardChecked := backward
    leftBoundaryOwner := branchSquareRootOwner 0 1
    leftBoundaryChecked := leftBoundary }

/-- The unsubdivided owner-boundary cycle represented by the prepared
Legendre A-cycle data. -/
@[expose] def rawACycleTarget : Path.Gaussian.Lifted.Closed.ClosedLiftedPath 2 :=
  Hyperelliptic.Branches.BranchCutLifts.doubleLiftWithBoundaryOwners
    (branchState 0) (branchState 1) (rawConnector 0 1)

set_option genInjectivity false in
/-- Prepared Legendre cycle data cached together with its raw geometric
realization. -/
structure RealizedPreparedCycle
    (raw : Path.Gaussian.Lifted.Closed.ClosedLiftedPath 2) where
  /-- The cached prepared cycle data on the exact displayed curve. -/ data :
    Topology.PreparedCycleModels.PreparedCycleData curve
  /-- The retained certificate that these exact prepared data realize the original raw lifted cycle. -/ realizes :
    Topology.PreparedCycleModels.PreparedCycleData.RealizesRaw data raw

constructive_injectivity RealizedPreparedCycle

section
/-- Conservative total A-cycle construction retained as a proof-producing
fallback if an explicitly bounded execution reports failure. -/
@[expose] def totalPreparedACycleWitness (_ : Unit) :
    RealizedPreparedCycle rawACycleTarget := by
  let boundary :=
    Topology.PreparedCycleModels.PreparedBoundaryDoublePath.ofConnectorAtWithOwners
      branchData degreeGtOne (branchIndex 0) (branchIndex 1) 0
      (branchSquareRootOwner 0 0) (branchSquareRootOwner 1 0)
      (branchSquareRootOwner 1 1) (branchSquareRootOwner 0 1)
  exact
    { data := .finiteCut boundary
      realizes := by
        unfold rawACycleTarget rawConnector branchState branchIndex
        exact .finiteCut boundary rfl rfl }

/-- Data projection of the conservative A-cycle witness. -/
@[expose] def totalPreparedACycle (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData curve :=
  (totalPreparedACycleWitness token).data

set_option genInjectivity false in
/-- The first unfinished A-cycle path with all earlier completed bank certificates.

The retained report keeps the actual finite prefix, unresolved suffix and
stopping reason on the original path and sheet owner. -/
inductive ABankFailure where
  /-- The original forward bank stopped after the retained earlier banks. -/
  | forward
      (attempt : WorkingAttempt (workingConnector 0 1) (workingConnector_withinAmbient 0 1) (branchSquareRootOwner 0 0))
      (unfinished : attempt.bank? = none)
  /-- The original rightBoundary bank stopped after the retained earlier banks. -/
  | rightBoundary
      (forward : WorkingBank (workingConnector 0 1) (branchSquareRootOwner 0 0))
      (attempt : WorkingAttempt (workingBoundary 1) (workingBoundary_withinAmbient 1) (branchSquareRootOwner 1 0))
      (unfinished : attempt.bank? = none)
  /-- The original backward bank stopped after the retained earlier banks. -/
  | backward
      (forward : WorkingBank (workingConnector 0 1) (branchSquareRootOwner 0 0))
      (rightBoundary : WorkingBank (workingBoundary 1) (branchSquareRootOwner 1 0))
      (attempt : WorkingAttempt (workingBackwardConnector 0 1) (workingBackwardConnector_withinAmbient 0 1)
        (branchSquareRootOwner 1 1))
      (unfinished : attempt.bank? = none)
  /-- The original leftBoundary bank stopped after the retained earlier banks. -/
  | leftBoundary
      (forward : WorkingBank (workingConnector 0 1) (branchSquareRootOwner 0 0))
      (rightBoundary : WorkingBank (workingBoundary 1) (branchSquareRootOwner 1 0))
      (backward : WorkingBank (workingBackwardConnector 0 1) (branchSquareRootOwner 1 1))
      (attempt : WorkingAttempt (workingBoundary 0) (workingBoundary_withinAmbient 0) (branchSquareRootOwner 0 1))
      (unfinished : attempt.bank? = none)

/-- Construct the measured A-cycle witness or retain the first incomplete path execution.

The original ordered banks are acquired once. Failure retains earlier banks
and the unfinished report; the total fallback remains a separate operation. -/
@[expose] def attemptPreparedACycle (token : Unit) :
    Except ABankFailure (RealizedPreparedCycle rawACycleTarget) :=
  let attempt := aForwardAttempt token
  match unfinished : attempt.bank? with
  | none => .error (.forward attempt unfinished)
  | some forward =>
      let attempt := aRightBoundaryAttempt token
      match unfinished : attempt.bank? with
      | none => .error (.rightBoundary forward attempt unfinished)
      | some rightBoundary =>
          let attempt := aBackwardAttempt token
          match unfinished : attempt.bank? with
          | none => .error (.backward forward rightBoundary attempt unfinished)
          | some backward =>
              let attempt := aLeftBoundaryAttempt token
              match unfinished : attempt.bank? with
              | none => .error (.leftBoundary forward rightBoundary backward attempt unfinished)
              | some leftBoundary =>
                  let boundary := executedABoundaryData forward rightBoundary backward leftBoundary
                  .ok
                    { data := .finiteCut boundary
                      realizes :=
                        .finiteCutDyadic boundary (rawConnector 0 1)
                          (rawConnector_withinAmbient 0 1) connectorOuterDepth rfl
                          (rawBoundary_withinAmbient 1) boundaryOuterDepth rfl
                          (rawBoundary_withinAmbient 0) boundaryOuterDepth rfl }

/-- Canonical cached A-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback.  Opacity shares the
checked selection across downstream elaboration while preserving the same
compiled finite program. -/
opaque preparedACycleWitness (token : Unit) :
    RealizedPreparedCycle rawACycleTarget :=
  match attemptPreparedACycle token with
  | .ok witnessed => witnessed
  | .error _failure => totalPreparedACycleWitness token

/-- Canonical genus-one A cut.  The measured executable banks are preferred;
the total finite theorem remains the constructive fallback. -/
@[expose] def preparedACycle (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData curve :=
  (preparedACycleWitness token).data

/-- Attempt the fixed-depth checked dyadic bank for the B forward connector from root -1 to one on sheet zero.

A successful result retains the exact path and starting owner; failure leaves this bounded attempt inconclusive. -/
@[expose] def bForwardAttempt (_ : Unit) :=
  DyadicBank.execute
    (workingConnector 0 2) (workingConnector_withinAmbient 0 2)
    (branchSquareRootOwner 0 0) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

/-- Attempt the fixed-depth checked dyadic bank for the B reversed connector from root one to -1 on sheet one.

A successful result retains the exact path and starting owner; failure leaves this bounded attempt inconclusive. -/
@[expose] def bBackwardAttempt (_ : Unit) :=
  DyadicBank.execute
    (workingBackwardConnector 0 2)
    (workingBackwardConnector_withinAmbient 0 2)
    (branchSquareRootOwner 2 1) workingInnerDepth workingRootDiameter
      workingRootDiameter_positive

/-- Assemble the B-cycle double path from the checked forward and backward connector banks.

The original connector, endpoints and opposite-sheet owners are retained with the fixed inner depth and root diameter.
-/
@[expose] def executedBDoubleData
    (forward : WorkingBank (workingConnector 0 2)
      (branchSquareRootOwner 0 0))
    (backward : WorkingBank (workingBackwardConnector 0 2)
      (branchSquareRootOwner 2 1)) :
    Topology.PreparedCycleModels.PreparedDoublePath curve :=
  { ambient := Hyperelliptic.Branches.Cuts.Ambient curve
    start := (branchState 0).box.anchor
    finish := (branchState 2).box.anchor
    basePath := workingConnector 0 2
    depth := workingInnerDepth
    rootDiameter := workingRootDiameter
    rootDiameterPositive := workingRootDiameter_positive
    forwardOwner := branchSquareRootOwner 0 0
    forwardChecked := forward
    backwardOwner := branchSquareRootOwner 2 1
    backwardChecked := backward }

/-- The unsubdivided double lift represented by the prepared Legendre
B-cycle data. -/
@[expose] def rawBCycleTarget : Path.Gaussian.Lifted.Closed.ClosedLiftedPath 2 :=
  Hyperelliptic.Branches.BranchCutLifts.doubleLift (rawConnector 0 2)

/-- Conservative total B-cycle construction retained as a fallback. -/
@[expose] def totalPreparedBCycleWitness (_ : Unit) :
    RealizedPreparedCycle rawBCycleTarget := by
  let bridge :=
    Topology.PreparedCycleModels.PreparedDoublePath.ofConnectorAtWithOwners
      branchData degreeGtOne (branchIndex 0) (branchIndex 2) 0
      (branchSquareRootOwner 0 0) (branchSquareRootOwner 2 1)
  exact
    { data := .bridge bridge
      realizes := by
        unfold rawBCycleTarget rawConnector branchIndex
        exact .bridge bridge }

/-- Data projection of the conservative B-cycle witness. -/
@[expose] def totalPreparedBCycle (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData curve :=
  (totalPreparedBCycleWitness token).data

set_option genInjectivity false in
/-- The first unfinished B-cycle path with all earlier completed bank certificates.

The retained report keeps the actual finite prefix, unresolved suffix and
stopping reason on the original path and sheet owner. -/
inductive BBankFailure where
  /-- The original forward bank stopped after the retained earlier banks. -/
  | forward
      (attempt : WorkingAttempt (workingConnector 0 2) (workingConnector_withinAmbient 0 2) (branchSquareRootOwner 0 0))
      (unfinished : attempt.bank? = none)
  /-- The original backward bank stopped after the retained earlier banks. -/
  | backward
      (forward : WorkingBank (workingConnector 0 2) (branchSquareRootOwner 0 0))
      (attempt : WorkingAttempt (workingBackwardConnector 0 2) (workingBackwardConnector_withinAmbient 0 2)
        (branchSquareRootOwner 2 1))
      (unfinished : attempt.bank? = none)

/-- Construct the measured B-cycle witness or retain the first incomplete path execution.

The original ordered banks are acquired once. Failure retains earlier banks
and the unfinished report; the total fallback remains a separate operation. -/
@[expose] def attemptPreparedBCycle (token : Unit) :
    Except BBankFailure (RealizedPreparedCycle rawBCycleTarget) :=
  let attempt := bForwardAttempt token
  match unfinished : attempt.bank? with
  | none => .error (.forward attempt unfinished)
  | some forward =>
      let attempt := bBackwardAttempt token
      match unfinished : attempt.bank? with
      | none => .error (.backward forward attempt unfinished)
      | some backward =>
          let bridge := executedBDoubleData forward backward
          .ok
            { data := .bridge bridge
              realizes :=
                .bridgeDyadic bridge (rawConnector 0 2)
                  (rawConnector_withinAmbient 0 2) connectorOuterDepth rfl }

/-- Canonical cached B-cycle witness, preferring the measured executable
banks and retaining the constructive total fallback.  This is the B-cycle
counterpart of the A-cycle elaboration cache boundary. -/
opaque preparedBCycleWitness (token : Unit) :
    RealizedPreparedCycle rawBCycleTarget :=
  match attemptPreparedBCycle token with
  | .ok witnessed => witnessed
  | .error _failure => totalPreparedBCycleWitness token

/-- Canonical genus-one B bridge, preferring the measured executable banks. -/
@[expose] def preparedBCycle (token : Unit) :
    Topology.PreparedCycleModels.PreparedCycleData curve :=
  (preparedBCycleWitness token).data

/-- The finite branch-cut family constructed from the exact displayed curve and retained branch data. -/
@[expose] def branchFamily :=
  Hyperelliptic.Branches.BranchCutLifts.familyOfData curve branchData

end

end Purelib.Examples.Curves.Legendre.Prepared.RealMinusOne

end
