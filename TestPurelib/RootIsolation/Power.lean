module

public import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.Squarefree
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Dense.Rational.Bezout.GCD
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# Local winding owners of the positive square and cube roots of two

The original coefficient tables and finite line-clearance certificates define
the same small local owners for both refinement diagnostics. The winding
states retain their four actual ambient-line caches and exact initial boxes.
-/

public section

namespace TestPurelib.RootIsolation.Power

open Purelib
open Purelib.RootIsolation
open Purelib.Polynomial
open Purelib.Geometry.Rational
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Clearance.Box

/-- The common small ambient box around both positive real roots. -/
@[expose] def ambient : Box := ⟨1, 3 / 2, -1 / 16, 1 / 16, by decide, by decide⟩

/-- The finite squarefree input for the original power polynomial at two. -/
def powerInput (degree : RootDegree) (higher : 2 ≤ degree.value) :
    FTA.Squarefree.Input (Power.Gaussian.rootPolynomial 2 degree) where
  squarefree := Power.Gaussian.Squarefree.squarefree (by decide) degree
  degreeAtLeastTwo := by
    rewrite [Power.Gaussian.rootPolynomial_degree]
    exact higher

/-- The original coefficient polynomial for the positive square root of two. -/
@[expose] def squarePolynomial := Power.Gaussian.rootPolynomial 2 ⟨2, by decide⟩

/-- The kernel-checked local winding owner for the positive square root of two. -/
def squareInitial : WindingOneState squarePolynomial ambient := by
  let left := Line.Bezout.verticalOfCoprime squarePolynomial ambient ambient.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal squarePolynomial ambient.xLower)
      (Path.Axis.verticalPathImag squarePolynomial ambient.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime squarePolynomial ambient ambient.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal squarePolynomial ambient.xUpper)
      (Path.Axis.verticalPathImag squarePolynomial ambient.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime
    squarePolynomial ambient ambient.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal squarePolynomial ambient.yLower)
      (Path.Axis.horizontalPathImag squarePolynomial ambient.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime squarePolynomial ambient ambient.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal squarePolynomial ambient.yUpper)
      (Path.Axis.horizontalPathImag squarePolynomial ambient.yUpper)
      (by decide +kernel) (by decide +kernel))
  exact
    { box := ambient
      refinesAmbient := Box.refines_refl ambient
      proper := by constructor <;> decide
      clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
      rawWindingFour := by decide +kernel
      ambientLeftClearance := left
      ambientRightClearance := right
      ambientBottomClearance := bottom
      ambientTopClearance := top }

/-- The original coefficient polynomial for the positive cube root of two. -/
@[expose] def cubePolynomial := Power.Gaussian.rootPolynomial 2 ⟨3, by decide⟩

/-- The kernel-checked local winding owner for the positive cube root of two. -/
def cubeInitial : WindingOneState cubePolynomial ambient := by
  let left := Line.Bezout.verticalOfCoprime cubePolynomial ambient ambient.xLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal cubePolynomial ambient.xLower)
      (Path.Axis.verticalPathImag cubePolynomial ambient.xLower)
      (by decide +kernel) (by decide +kernel))
  let right := Line.Bezout.verticalOfCoprime cubePolynomial ambient ambient.xUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.verticalPathReal cubePolynomial ambient.xUpper)
      (Path.Axis.verticalPathImag cubePolynomial ambient.xUpper)
      (by decide +kernel) (by decide +kernel))
  let bottom := Line.Bezout.horizontalOfCoprime
    cubePolynomial ambient ambient.yLower
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal cubePolynomial ambient.yLower)
      (Path.Axis.horizontalPathImag cubePolynomial ambient.yLower)
      (by decide +kernel) (by decide +kernel))
  let top := Line.Bezout.horizontalOfCoprime cubePolynomial ambient ambient.yUpper
    (Dense.Rational.Bezout.certificateOfConstantGCD
      (Path.Axis.horizontalPathReal cubePolynomial ambient.yUpper)
      (Path.Axis.horizontalPathImag cubePolynomial ambient.yUpper)
      (by decide +kernel) (by decide +kernel))
  exact
    { box := ambient
      refinesAmbient := Box.refines_refl ambient
      proper := by constructor <;> decide
      clearance := Clearance.Box.Boundary.Lines.boundaryOfLines left right bottom top
      rawWindingFour := by decide +kernel
      ambientLeftClearance := left
      ambientRightClearance := right
      ambientBottomClearance := bottom
      ambientTopClearance := top }

/-- Exact local box readback of the retained square-root state. -/
private theorem squareInitial_box_readback : squareInitial.box = ambient := rfl

/-- The square-root state retains the original small local box exactly. -/
theorem squareInitial_box : squareInitial.box = ambient := squareInitial_box_readback

/-- Exact local box readback of the retained cube-root state. -/
private theorem cubeInitial_box_readback : cubeInitial.box = ambient := rfl

/-- The cube-root state retains that same original small local box exactly. -/
theorem cubeInitial_box : cubeInitial.box = ambient := cubeInitial_box_readback

end TestPurelib.RootIsolation.Power

end
