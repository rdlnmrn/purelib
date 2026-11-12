module

public import Purelib.Polynomial.Winding.Circle
import Purelib.Polynomial.Winding.Circle.Comparison
import Purelib.Polynomial.Winding.Circle.Product
import Purelib.Polynomial.Winding.Circle.LinearFactor
import Purelib.Polynomial.Clearance.Circle
import Purelib.Polynomial.Clearance.Circle.Factor
import Purelib.Polynomial.Clearance.Circle.Collar
import Purelib.Geometry.Rational.Circle
import Purelib.System.IO
import Purelib.Tactic.Ring

/-!
# Complete rational-circle boundary regressions

These fixtures use the actual retained bounded preparation and the original
independent phase-resolution constructor. Zero-depth inconclusivity and exact
boundary contact remain different explained outcomes.
-/

namespace TestPurelib.Polynomial.Winding.Circle

open Purelib
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open RationalFunctions.Curve.Canonical.Circle
open Polynomial.Winding
open Polynomial.Clearance.Circle (Margin Certificate)
open Polynomial.Clearance.Circle (FactorMargin Collar)
open Geometry.Rational.Circle (Retraction)

/-- A fixed nonzero constant polynomial. -/
private def constant : CoefficientPolynomial := ⟨[1]⟩

/-- The coordinate polynomial with one simple root at zero. -/
private def coordinate : CoefficientPolynomial := ⟨[1, 0]⟩

/-- A polynomial meeting the unit boundary at the displayed rational point one. -/
private def contact : CoefficientPolynomial := ⟨[1, -1]⟩

/-- A repeated-root polynomial with multiplicity two at zero. -/
private def square : CoefficientPolynomial := ⟨[1, 0, 0]⟩

/-- A small genuine coefficient perturbation of the original coordinate. -/
private def shifted : CoefficientPolynomial := ⟨[1, -(1 / 8)]⟩

/-- The original coordinate has exact unit quadrance on the same whole rational circle. -/
private def coordinate_clearance : Certificate coordinate :=
  { bound := 1
    positive := by decide
    lower := by
      intro point unit
      have value : coordinate.eval point = point := by
        change (0 * point + 1) * point + 0 = point
        ring1
      rewrite [value, Data.Gaussian.Norm.Basic.normSq_eq_canonical, unit]
      exact le_refl _ }

/-- The original coefficient perturbation pays the explicit whole-circle source margin. -/
private theorem shifted_close : coordinate_clearance.Close shifted := by
  intro point _
  have residual : shifted.eval point - coordinate.eval point = -(1 / 8 : Data.Gaussian.Basic.Canonical) := by
    change ((0 * point + 1) * point + -(1 / 8)) - ((0 * point + 1) * point + 0) = -(1 / 8)
    ring1
  rewrite [residual]
  decide +kernel

/-- The repeated-root fixture retains its original exact coefficient factorization. -/
private theorem square_factorization :
    Polynomial.Dense.Gaussian.Factorization.Identity.ProductIdentity square coordinate coordinate := by decide +kernel

/-- Read only the constructor of an explained bounded boundary result. -/
private def tag {polynomial : CoefficientPolynomial} {attempt : Boundary.Attempt polynomial} :
    Boundary.Outcome attempt → Nat
  | .clear _ => 0
  | .contact _ _ _ => 1
  | .inconclusive _ _ _ _ _ => 2

/-- A constant clears both full chart cells without subdivision. -/
private theorem constant_prepared : tag (Boundary.prepare constant 0).2 = 0 := by decide +kernel

/-- A genuine boundary contact is proved, even at zero refinement depth. -/
private theorem contact_prepared : tag (Boundary.prepare contact 0).2 = 1 := by decide +kernel

/-- Insufficient depth preserves unresolved obligations rather than manufacturing a zero. -/
private theorem coordinate_unresolved : tag (Boundary.prepare coordinate 0).2 = 2 := by decide +kernel

/-- The imaginary-axis retraction computes an exact rational point on the other half-circle. -/
private theorem imaginary_retraction :
    (Retraction.prepare (⟨0, 2⟩ : Data.Gaussian.Basic.Canonical)).point = ⟨-3 / 5, 4 / 5⟩ := by decide +kernel

/-- The aligned negative sign preserves the original negative real half-circle. -/
private theorem negative_retraction : (Retraction.prepare (-2)).point = -1 := by decide +kernel

/-- The original oriented chart-event raw reading of the coordinate is positive four. -/
public theorem coordinate_raw :
    Circle.raw (Boundary.Substitutions.prepare (⟨[1, 0]⟩ : CoefficientPolynomial)) = 4 := by decide +kernel

/-- The original oriented chart-event raw reading of a nonzero constant is zero. -/
public theorem constant_raw :
    Circle.raw (Boundary.Substitutions.prepare (⟨[1]⟩ : CoefficientPolynomial)) = 0 := by decide +kernel

/-- Independent chart-event winding agrees across the actual small coefficient perturbation. -/
private theorem shifted_raw : Circle.raw (Boundary.Substitutions.prepare shifted) = 4 :=
  (Circle.Comparison.raw_eq_of_close coordinate_clearance (Boundary.Substitutions.prepare coordinate)
    (Boundary.Substitutions.prepare shifted) shifted_close).trans coordinate_raw

/-- A nonreal rational interior root has one independent positive turn. -/
private theorem interior_linear_raw :
    Circle.raw (Boundary.Substitutions.prepare
      (Polynomial.Dense.Gaussian.LinearFactor.linearFactor (⟨1 / 2, 1 / 3⟩ : Data.Gaussian.Basic.Canonical))) = 4 :=
  Circle.raw_linearInside _ (by decide +kernel) _

/-- A nonreal rational exterior root has zero independent turns. -/
private theorem exterior_linear_raw :
    Circle.raw (Boundary.Substitutions.prepare
      (Polynomial.Dense.Gaussian.LinearFactor.linearFactor (⟨2, 1⟩ : Data.Gaussian.Basic.Canonical))) = 0 :=
  Circle.raw_linearOutside _ (by decide +kernel) _

/-- The original product reading is additive even for independently supplied retained substitutions. -/
private theorem retained_product_raw (left right : CoefficientPolynomial)
    (leftMargin : Certificate left)
    (rightMargin : Certificate right)
    (leftPaths : Boundary.Substitutions left) (rightPaths : Boundary.Substitutions right)
    (productPaths : Boundary.Substitutions (left * right)) :
    Circle.raw productPaths = Circle.raw leftPaths + Circle.raw rightPaths :=
  Circle.raw_mul leftMargin rightMargin leftPaths rightPaths productPaths

/-- Execute the original independent reading directly from a certified whole-circle margin. -/
private def checkMargin (polynomial : CoefficientPolynomial)
    (margin : Certificate polynomial) (expected : Int) : IO Unit := do
  let paths := Boundary.Substitutions.prepare polynomial
  let reading := Circle.Reading.prepare paths (margin.onBoundary paths)
  unless reading.winding == expected && Circle.raw paths == 4 * expected do
    throw (IO.userError "a rational linear factor lost its independent chart-event winding")

/-- Check actual independent winding construction after bounded whole-boundary preparation. -/
private def check (polynomial : CoefficientPolynomial) (depth : Nat) (expected : Int) : IO Unit := do
  let prepared := Boundary.prepare polynomial depth
  match prepared.2 with
  | .clear clearance =>
      let reading := Circle.Reading.prepare prepared.1.paths clearance
      let margin := Margin.prepare prepared.1.paths clearance
      let collar := Collar.prepare margin.toCertificate Geometry.Rational.Circle.boundingBox
      unless reading.winding == expected && Circle.raw prepared.1.paths == 4 * expected do
        throw (IO.userError "complete rational-circle winding changed its orientation or normalization")
      unless decide (0 < margin.bound) &&
          margin.ceiling == (4 : Data.Rat.Fraction.Rational) ^ polynomial.coeffs.length do
        throw (IO.userError "whole-circle residual margin lost its original coefficient denominator bound")
      unless decide (0 < collar.width) && decide (collar.width ≤ 1) do
        throw (IO.userError "coefficient-computed rational circle collar lost its positive payment")
  | .contact _ _ _ => throw (IO.userError "a clear circle fixture was incorrectly reported as contact")
  | .inconclusive _ _ _ _ _ => throw (IO.userError "a sufficient circle fixture retained unresolved leaves")

/-- Run the complete-chart constructor and independent winding fixtures. -/
public def run : IO Unit := do
  check constant 0 0
  check coordinate 3 1
  check square 5 2
  check shifted 3 1
  checkMargin _ (Certificate.linearInside
    (⟨1 / 2, 1 / 3⟩ : Data.Gaussian.Basic.Canonical) (by decide +kernel)) 1
  checkMargin _ (Certificate.linearOutside
    (⟨2, 1⟩ : Data.Gaussian.Basic.Canonical) (by decide +kernel)) 0
  let repeated := Boundary.prepare square 5
  match repeated.2 with
  | .clear clearance =>
      let margin := Margin.prepare repeated.1.paths clearance
      let focused := FactorMargin.prepare margin.toCertificate square_factorization
      let collar := Collar.prepare focused.toCertificate Geometry.Rational.Circle.boundingBox
      unless decide (0 < focused.bound) && decide (0 < collar.width) do
        throw (IO.userError "repeated-factor transfer lost its original source margin or cofactor payment")
  | _ => throw (IO.userError "repeated-root polynomial lacked whole-circle clearance")
  unless tag (Boundary.prepare contact 0).2 == 1 && tag (Boundary.prepare coordinate 0).2 == 2 do
    throw (IO.userError "contact and unfinished rational-circle preparation were conflated")
  for source in ([0, -2, ⟨0, 2⟩, ⟨3 / 5, 4 / 5⟩] : List Data.Gaussian.Basic.Canonical) do
    let retracted := Retraction.prepare source
    unless decide (retracted.point.normSq = 1) && decide (1 ≤ retracted.denominatorNorm) &&
        decide ((source - retracted.point).normSq ≤ (source.normSq - 1) ^ 2) do
      throw (IO.userError "rational circle retraction lost its exact norm-defect payment")

end TestPurelib.Polynomial.Winding.Circle
