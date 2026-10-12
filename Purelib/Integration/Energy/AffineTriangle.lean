module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Energy.Polygon
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.Integration.Energy.AffineTriangle

section
open Purelib.Data.Rat
open Purelib.Topology.Polygon
/-- One quarter of the imaginary wedge area on the original oriented triangle's retained primitive values. -/
def triangleEnergy {vertexCount : Nat}
    (primitive : Fin vertexCount -> Stokes.PrimitivePoint)
    (triangle :
      Stokes.OrientedTriangle vertexCount) :
    Fraction.Rational :=
  (Stokes.triangleWedgeArea
    (primitive triangle.first) (primitive triangle.second)
      (primitive triangle.third)).im / 4

/-- One quarter of the imaginary wedge area of the three ordered primitive points. -/
def primitiveTriangleEnergy
    (first second third : Stokes.PrimitivePoint) : Fraction.Rational :=
  (Stokes.triangleWedgeArea first second third).im / 4

end

section
open Purelib.Data.Gaussian
open Purelib.Integration.Energy in
open Purelib.Topology.Polygon in
/-- Form the paired energy primitive of the exact coefficient-times-point value. -/
def affineEnergyPrimitive (coefficient point : Basic.Canonical) :
  Stokes.PrimitivePoint :=
  Polygon.energyPrimitivePoint (coefficient * point)

open Purelib.Data.Rat in
/-- The signed rational area of the three ordered Gaussian coordinate points. -/
def coordinateTriangleArea
    (first second third : Basic.Canonical) : Fraction.Rational :=
  ((second.re - first.re) * (third.im - first.im) -
    (second.im - first.im) * (third.re - first.re)) / 2

open Purelib.Data.Rat in
open Purelib.Integration.Energy in
open Purelib.Topology.Polygon in
/-- An affine primitive triangle has energy equal to coordinate area times the coefficient's squared norm. -/
theorem affinePrimitiveTriangleEnergy_eq
    (coefficient first second third : Basic.Canonical) :
    primitiveTriangleEnergy
        (affineEnergyPrimitive coefficient first)
        (affineEnergyPrimitive coefficient second)
        (affineEnergyPrimitive coefficient third) =
      coordinateTriangleArea first second third *
        Data.Gaussian.Norm.Basic.normSq coefficient := by
  have wedgeImaginary :
      (Stokes.triangleWedgeArea
        (affineEnergyPrimitive coefficient first)
        (affineEnergyPrimitive coefficient second)
        (affineEnergyPrimitive coefficient third)).im =
      2 *
        ((second.re - first.re) * (third.im - first.im) -
          (second.im - first.im) * (third.re - first.re)) *
        Data.Gaussian.Norm.Basic.normSq coefficient := by
    unfold affineEnergyPrimitive Polygon.energyPrimitivePoint
      Stokes.triangleWedgeArea
      Data.Gaussian.Basic.conj
      Data.Gaussian.Norm.Basic.normSq
    simp only [Basic.sub_re,
      Basic.sub_im,
      Basic.mul_re,
      Basic.mul_im]
    ring1
  unfold primitiveTriangleEnergy
  rw [wedgeImaginary]
  unfold coordinateTriangleArea
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  calc
    (2 *
          ((second.re - first.re) * (third.im - first.im) -
            (second.im - first.im) * (third.re - first.re)) *
          Data.Gaussian.Norm.Basic.normSq coefficient) * 4⁻¹ =
        ((second.re - first.re) * (third.im - first.im) -
          (second.im - first.im) * (third.re - first.re)) *
          Data.Gaussian.Norm.Basic.normSq coefficient *
            (2 * 4⁻¹) := by ring1
    _ = ((second.re - first.re) * (third.im - first.im) -
          (second.im - first.im) * (third.re - first.re)) *
          Data.Gaussian.Norm.Basic.normSq coefficient * 2⁻¹ := by
      rw [show (2 : Fraction.Rational) * 4⁻¹ = 2⁻¹ by decide]
    _ = (((second.re - first.re) * (third.im - first.im) -
          (second.im - first.im) * (third.re - first.re)) * 2⁻¹) *
          Data.Gaussian.Norm.Basic.normSq coefficient := by ring1

open Purelib.Data.Rat in
/-- Half the imaginary part of the conjugate-first-times-second Gaussian product. -/
def crossEnergy (first second : Basic.Canonical) : Fraction.Rational :=
  (Data.Gaussian.Basic.conj first * second).im / 2

open Purelib.Data.Rat in
open Purelib.Integration.Energy in
open Purelib.Topology.Polygon in
/-- The energy of three paired Gaussian primitives is the cross energy of their two directed increments. -/
theorem primitiveTriangleEnergy_energyPrimitivePoint_eq_crossEnergy
    (first second third : Basic.Canonical) :
    primitiveTriangleEnergy (Polygon.energyPrimitivePoint first)
        (Polygon.energyPrimitivePoint second) (Polygon.energyPrimitivePoint third) =
      crossEnergy (second - first) (third - first) := by
  unfold primitiveTriangleEnergy Polygon.energyPrimitivePoint crossEnergy
    Stokes.triangleWedgeArea
    Data.Gaussian.Basic.conj
  simp only [Basic.sub_re,
    Basic.sub_im,
    Basic.mul_im,
    Fraction.Field.div_eq_mul_inv_direct]
  rw [show (2 : Fraction.Rational)⁻¹ = 2 * (4 : Fraction.Rational)⁻¹ by decide]
  ring1

section
open Purelib.Data.Rat
open Purelib.Integration.Energy
/-- Expand cross energy under two additive errors into the original value and three separate error contributions. -/
theorem crossEnergy_add_add (first second firstError secondError :
  Basic.Canonical) :
    crossEnergy (first + firstError) (second + secondError) =
      crossEnergy first second + crossEnergy firstError second +
        crossEnergy first secondError + crossEnergy firstError secondError := by
  unfold crossEnergy Data.Gaussian.Basic.conj
  simp only [Basic.add_re,
    Basic.add_im,
    Basic.mul_im,
    Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Cross energy squared is bounded by one quarter of the product of the two squared norms. -/
theorem crossEnergy_sq_le (first second : Basic.Canonical) :
    crossEnergy first second ^ 2 <=
      Data.Gaussian.Norm.Basic.normSq first *
        Data.Gaussian.Norm.Basic.normSq second / 4 := by
  let product := Data.Gaussian.Basic.conj first * second
  have imaginarySquare : product.im ^ 2 <=
      Data.Gaussian.Norm.Basic.normSq product := by
    unfold Data.Gaussian.Norm.Basic.normSq
    exact le_add_of_nonneg_left
      (Fraction.Order.Arithmetic.sq_nonneg_direct product.re)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    imaginarySquare (show (0 : Fraction.Rational) <= (4 : Fraction.Rational)⁻¹ by decide)
  dsimp only [product] at scaled
  rw [Norm.Basic.normSq_mul,
    Norm.Basic.normSq_conj] at scaled
  unfold crossEnergy
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  have halfSquare : (2 : Fraction.Rational)⁻¹ ^ 2 = (4 : Fraction.Rational)⁻¹ := by decide
  calc
    ((Data.Gaussian.Basic.conj first * second).im * 2⁻¹) ^ 2 =
        (Data.Gaussian.Basic.conj first * second).im ^ 2 *
          4⁻¹ := by
      rw [← halfSquare]
      ring1
    _ <= Data.Gaussian.Norm.Basic.normSq first *
          Data.Gaussian.Norm.Basic.normSq second * 4⁻¹ := scaled

/-- A nonnegative budget whose square bounds the quarter norm product bounds cross energy from below by its negative. -/
theorem neg_budget_le_crossEnergy (first second : Basic.Canonical)
    (budget : Fraction.Rational) (budgetNonnegative : 0 <= budget)
    (productBound :
      Data.Gaussian.Norm.Basic.normSq first *
          Data.Gaussian.Norm.Basic.normSq second / 4 <=
        budget ^ 2) :
    -budget <= crossEnergy first second :=
  Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct budgetNonnegative
    ((crossEnergy_sq_le first second).trans productBound)

/-- Separate first, second and mixed nonnegative error budgets give a lower bound for perturbed cross energy.

Each original norm-product estimate remains attached to its own error term, preserving all three payments. -/
theorem crossEnergy_sub_budget_le_add_add
    (first second firstError secondError : Basic.Canonical)
    (firstBudget secondBudget mixedBudget : Fraction.Rational)
    (firstBudgetNonnegative : 0 <= firstBudget)
    (secondBudgetNonnegative : 0 <= secondBudget)
    (mixedBudgetNonnegative : 0 <= mixedBudget)
    (firstProductBound :
      Data.Gaussian.Norm.Basic.normSq firstError *
          Data.Gaussian.Norm.Basic.normSq second / 4 <=
        firstBudget ^ 2)
    (secondProductBound :
      Data.Gaussian.Norm.Basic.normSq first *
          Data.Gaussian.Norm.Basic.normSq secondError / 4 <=
        secondBudget ^ 2)
    (mixedProductBound :
      Data.Gaussian.Norm.Basic.normSq firstError *
          Data.Gaussian.Norm.Basic.normSq secondError / 4 <=
        mixedBudget ^ 2) :
    crossEnergy first second -
        (firstBudget + secondBudget + mixedBudget) <=
      crossEnergy (first + firstError) (second + secondError) := by
  rw [crossEnergy_add_add]
  have firstLower := neg_budget_le_crossEnergy firstError second firstBudget
    firstBudgetNonnegative firstProductBound
  have secondLower := neg_budget_le_crossEnergy first secondError secondBudget
    secondBudgetNonnegative secondProductBound
  have mixedLower := neg_budget_le_crossEnergy firstError secondError
    mixedBudget mixedBudgetNonnegative mixedProductBound
  calc
    crossEnergy first second -
          (firstBudget + secondBudget + mixedBudget) =
        crossEnergy first second + -firstBudget + -secondBudget +
          -mixedBudget := by ring1
    _ <= crossEnergy first second + crossEnergy firstError second +
          crossEnergy first secondError + crossEnergy firstError secondError :=
      add_le_add
        (add_le_add (add_le_add le_rfl firstLower) secondLower) mixedLower

end

/-- The exact coefficient-scaled finish value minus the coefficient-scaled start value. -/
def affinePrimitiveIncrement
    (coefficient start finish : Basic.Canonical) : Basic.Canonical :=
  coefficient * finish - coefficient * start

section
open Purelib.Integration.Energy
/-- The original primitive displacement minus its exact affine coordinate increment. -/
def affinePrimitiveIncrementError
    (coefficient coordinateStart coordinateFinish
      primitiveStart primitiveFinish : Basic.Canonical) : Basic.Canonical :=
  (primitiveFinish - primitiveStart) -
    affinePrimitiveIncrement coefficient coordinateStart coordinateFinish

/-- Adding the retained affine increment error reconstructs the original primitive displacement. -/
theorem affinePrimitiveIncrement_add_error
    (coefficient coordinateStart coordinateFinish
      primitiveStart primitiveFinish : Basic.Canonical) :
    affinePrimitiveIncrement coefficient coordinateStart coordinateFinish +
        affinePrimitiveIncrementError coefficient coordinateStart
          coordinateFinish primitiveStart primitiveFinish =
      primitiveFinish - primitiveStart := by
  unfold affinePrimitiveIncrementError affinePrimitiveIncrement
  apply Basic.ext <;>
    simp only [Basic.add_re,
      Basic.add_im,
      Basic.sub_re,
      Basic.sub_im,
      Basic.mul_re,
      Basic.mul_im] <;> ring1

end

open Purelib.Data.Rat in
open Purelib.Integration.Energy in
/-- The original coordinate area times coefficient norm squared, less three paid errors, bounds primitive triangle
energy.

The coordinate and primitive vertices remain separate, with distinct first, second and mixed increment-error budgets and
their norm-product certificates. -/
theorem affineTriangleEnergy_sub_budget_le
    (coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Basic.Canonical)
    (firstBudget secondBudget mixedBudget : Fraction.Rational)
    (firstBudgetNonnegative : 0 <= firstBudget)
    (secondBudgetNonnegative : 0 <= secondBudget)
    (mixedBudgetNonnegative : 0 <= mixedBudget)
    (firstProductBound :
      Data.Gaussian.Norm.Basic.normSq
            (affinePrimitiveIncrementError coefficient coordinateFirst
              coordinateSecond primitiveFirst primitiveSecond) *
          Data.Gaussian.Norm.Basic.normSq
            (affinePrimitiveIncrement coefficient coordinateFirst
              coordinateThird) / 4 <= firstBudget ^ 2)
    (secondProductBound :
      Data.Gaussian.Norm.Basic.normSq
            (affinePrimitiveIncrement coefficient coordinateFirst
              coordinateSecond) *
          Data.Gaussian.Norm.Basic.normSq
            (affinePrimitiveIncrementError coefficient coordinateFirst
              coordinateThird primitiveFirst primitiveThird) / 4 <=
        secondBudget ^ 2)
    (mixedProductBound :
      Data.Gaussian.Norm.Basic.normSq
            (affinePrimitiveIncrementError coefficient coordinateFirst
              coordinateSecond primitiveFirst primitiveSecond) *
          Data.Gaussian.Norm.Basic.normSq
            (affinePrimitiveIncrementError coefficient coordinateFirst
              coordinateThird primitiveFirst primitiveThird) / 4 <=
        mixedBudget ^ 2) :
    coordinateTriangleArea coordinateFirst coordinateSecond coordinateThird *
          Data.Gaussian.Norm.Basic.normSq coefficient -
        (firstBudget + secondBudget + mixedBudget) <=
      primitiveTriangleEnergy
        (Polygon.energyPrimitivePoint primitiveFirst)
        (Polygon.energyPrimitivePoint primitiveSecond)
        (Polygon.energyPrimitivePoint primitiveThird) := by
  let first := affinePrimitiveIncrement coefficient coordinateFirst
    coordinateSecond
  let second := affinePrimitiveIncrement coefficient coordinateFirst
    coordinateThird
  let firstError := affinePrimitiveIncrementError coefficient coordinateFirst
    coordinateSecond primitiveFirst primitiveSecond
  let secondError := affinePrimitiveIncrementError coefficient coordinateFirst
    coordinateThird primitiveFirst primitiveThird
  have referenceEnergy :
      crossEnergy first second =
        coordinateTriangleArea coordinateFirst coordinateSecond coordinateThird *
          Data.Gaussian.Norm.Basic.normSq coefficient := by
    calc
      crossEnergy first second =
          primitiveTriangleEnergy
            (Polygon.energyPrimitivePoint (coefficient * coordinateFirst))
            (Polygon.energyPrimitivePoint (coefficient * coordinateSecond))
            (Polygon.energyPrimitivePoint (coefficient * coordinateThird)) := by
        rw [primitiveTriangleEnergy_energyPrimitivePoint_eq_crossEnergy]
        rfl
      _ = coordinateTriangleArea coordinateFirst coordinateSecond
            coordinateThird *
          Data.Gaussian.Norm.Basic.normSq coefficient :=
        affinePrimitiveTriangleEnergy_eq coefficient coordinateFirst
          coordinateSecond coordinateThird
  have stable := crossEnergy_sub_budget_le_add_add first second firstError
    secondError firstBudget secondBudget mixedBudget firstBudgetNonnegative
    secondBudgetNonnegative mixedBudgetNonnegative firstProductBound
    secondProductBound mixedProductBound
  calc
    coordinateTriangleArea coordinateFirst coordinateSecond coordinateThird *
            Data.Gaussian.Norm.Basic.normSq coefficient -
          (firstBudget + secondBudget + mixedBudget) =
        crossEnergy first second -
          (firstBudget + secondBudget + mixedBudget) := by rw [referenceEnergy]
    _ <= crossEnergy (first + firstError) (second + secondError) := stable
    _ = crossEnergy (primitiveSecond - primitiveFirst)
          (primitiveThird - primitiveFirst) := by
      rw [affinePrimitiveIncrement_add_error coefficient coordinateFirst
          coordinateSecond primitiveFirst primitiveSecond,
        affinePrimitiveIncrement_add_error coefficient coordinateFirst
          coordinateThird primitiveFirst primitiveThird]
    _ = primitiveTriangleEnergy
          (Polygon.energyPrimitivePoint primitiveFirst)
          (Polygon.energyPrimitivePoint primitiveSecond)
          (Polygon.energyPrimitivePoint primitiveThird) :=
      (primitiveTriangleEnergy_energyPrimitivePoint_eq_crossEnergy
        primitiveFirst primitiveSecond primitiveThird).symm

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Energy in
set_option genInjectivity false in
/-- Three nonnegative budgets certifying affine primitive-triangle increment errors.

The exact coefficient and both ordered triples of coordinate and primitive vertices are indexed; each retained budget
pays its corresponding first, second or mixed norm product. -/
structure AffineTriangleErrorCertificate
    (coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Basic.Canonical) where
  /-- The retained allowance for the first increment error against the second affine increment. -/ firstBudget :
    Fraction.Rational
  /-- The retained allowance for the first affine increment against the second increment error. -/ secondBudget :
    Fraction.Rational
  /-- The retained allowance for the interaction of both increment errors. -/ mixedBudget : Fraction.Rational
  /-- The first retained error allowance is nonnegative. -/ firstBudget_nonnegative : 0 <= firstBudget
  /-- The second retained error allowance is nonnegative. -/ secondBudget_nonnegative : 0 <= secondBudget
  /-- The retained mixed-error allowance is nonnegative. -/ mixedBudget_nonnegative : 0 <= mixedBudget
  /-- The first error and second affine increment's quarter norm product is bounded by the first allowance squared. -/
    firstProductBound :
    Data.Gaussian.Norm.Basic.normSq
          (affinePrimitiveIncrementError coefficient coordinateFirst
            coordinateSecond primitiveFirst primitiveSecond) *
        Data.Gaussian.Norm.Basic.normSq
          (affinePrimitiveIncrement coefficient coordinateFirst
            coordinateThird) / 4 <= firstBudget ^ 2
  /-- The first affine increment and second error's quarter norm product is bounded by the second allowance squared. -/
    secondProductBound :
    Data.Gaussian.Norm.Basic.normSq
          (affinePrimitiveIncrement coefficient coordinateFirst
            coordinateSecond) *
        Data.Gaussian.Norm.Basic.normSq
          (affinePrimitiveIncrementError coefficient coordinateFirst
            coordinateThird primitiveFirst primitiveThird) / 4 <=
      secondBudget ^ 2
  /-- The two errors' quarter norm product is bounded by the mixed allowance squared. -/ mixedProductBound :
    Data.Gaussian.Norm.Basic.normSq
          (affinePrimitiveIncrementError coefficient coordinateFirst
            coordinateSecond primitiveFirst primitiveSecond) *
        Data.Gaussian.Norm.Basic.normSq
          (affinePrimitiveIncrementError coefficient coordinateFirst
            coordinateThird primitiveFirst primitiveThird) / 4 <=
      mixedBudget ^ 2

constructive_injectivity AffineTriangleErrorCertificate

namespace AffineTriangleErrorCertificate

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Energy in
/-- Sum the retained first, second and mixed affine-triangle error budgets. -/
def totalBudget
    {coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Basic.Canonical}
    (certificate : AffineTriangle.AffineTriangleErrorCertificate coefficient coordinateFirst
      coordinateSecond coordinateThird primitiveFirst primitiveSecond
      primitiveThird) : Fraction.Rational :=
  certificate.firstBudget + certificate.secondBudget + certificate.mixedBudget

open Purelib.Data.Gaussian
open Purelib.Integration.Energy
/-- The retained total affine-triangle error budget is nonnegative. -/
theorem totalBudget_nonnegative
    {coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Basic.Canonical}
    (certificate : AffineTriangle.AffineTriangleErrorCertificate coefficient coordinateFirst
      coordinateSecond coordinateThird primitiveFirst primitiveSecond
      primitiveThird) :
    0 <= certificate.totalBudget :=
  add_nonneg
    (add_nonneg certificate.firstBudget_nonnegative
      certificate.secondBudget_nonnegative)
    certificate.mixedBudget_nonnegative

/-- The retained certificate bounds primitive triangle energy below by affine coordinate energy less its exact total
budget. -/
theorem affineEnergy_sub_totalBudget_le
    {coefficient coordinateFirst coordinateSecond coordinateThird
      primitiveFirst primitiveSecond primitiveThird : Basic.Canonical}
    (certificate : AffineTriangle.AffineTriangleErrorCertificate coefficient coordinateFirst
      coordinateSecond coordinateThird primitiveFirst primitiveSecond
      primitiveThird) :
    AffineTriangle.coordinateTriangleArea coordinateFirst coordinateSecond coordinateThird *
          Data.Gaussian.Norm.Basic.normSq coefficient -
        certificate.totalBudget <=
      AffineTriangle.primitiveTriangleEnergy
        (Polygon.energyPrimitivePoint primitiveFirst)
        (Polygon.energyPrimitivePoint primitiveSecond)
        (Polygon.energyPrimitivePoint primitiveThird) :=
  AffineTriangle.affineTriangleEnergy_sub_budget_le coefficient coordinateFirst
    coordinateSecond coordinateThird primitiveFirst primitiveSecond
    primitiveThird certificate.firstBudget certificate.secondBudget
    certificate.mixedBudget certificate.firstBudget_nonnegative
    certificate.secondBudget_nonnegative certificate.mixedBudget_nonnegative
    certificate.firstProductBound certificate.secondProductBound
    certificate.mixedProductBound

end AffineTriangleErrorCertificate

open Purelib.Data.Gaussian
open Purelib.Integration.Energy
open Purelib.Topology.Polygon
/-- The triangle from zero through the first primitive to their sum has the directed primitive cross-product energy. -/
theorem primitiveTriangleEnergy_zero_left_add
    (left right : Stokes.PrimitivePoint) :
    primitiveTriangleEnergy
        Stokes.PrimitivePoint.zero left
          (left.add right) =
      (left.left * right.right - right.left * left.right).im / 4 := by
  unfold primitiveTriangleEnergy
    Stokes.triangleWedgeArea
    Stokes.PrimitivePoint.zero
    Stokes.PrimitivePoint.add
  dsimp only
  apply congrArg (fun value : Basic.Canonical => value.im / 4)
  ring1

/-- The triangle from zero through the primitive sum to the second primitive has the same directed cross-product energy.
-/
theorem primitiveTriangleEnergy_zero_add_right
    (left right : Stokes.PrimitivePoint) :
    primitiveTriangleEnergy
        Stokes.PrimitivePoint.zero
          (left.add right) right =
      (left.left * right.right - right.left * left.right).im / 4 := by
  unfold primitiveTriangleEnergy
    Stokes.triangleWedgeArea
    Stokes.PrimitivePoint.zero
    Stokes.PrimitivePoint.add
  dsimp only
  apply congrArg (fun value : Basic.Canonical => value.im / 4)
  ring1

end Purelib.Integration.Energy.AffineTriangle

end
