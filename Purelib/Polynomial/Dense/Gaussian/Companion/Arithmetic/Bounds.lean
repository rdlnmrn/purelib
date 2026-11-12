module

public import Purelib.Polynomial.Dense.Companion.Arithmetic
public import Purelib.Polynomial.Dense.Gaussian.Companion.Bounds
public import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.NatCast
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Computed quantitative bounds for original polynomial arithmetic

The actual input companion bounds control both original power vectors and
normalized source residuals. The selected operation combines those residuals.
Its output reading uses the same retained inverse coefficient polynomials.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Companion.Arithmetic

open Purelib.Data.Rat.Fraction
open Purelib
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Algebra.FiniteSum
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.Polynomial.Dense.Companion (Operation Elimination)

/-- Scale a bounded original product quadrance by its computed nonnegative upper factors. -/
private theorem product_bound (first second : Canonical) (left right : Fraction.Rational)
    (firstBound : Norm.Basic.normSq first ≤ left) (secondBound : Norm.Basic.normSq second ≤ right)
    (leftNonnegative : 0 ≤ left) : Norm.Basic.normSq (first * second) ≤ left * right := by
  rewrite [Norm.Basic.normSq_mul]
  exact Order.Arithmetic.mul_le_mul_direct firstBound secondBound
    (Norm.Basic.normSq_nonneg second) leftNonnegative

/-- The selected operation's finite residual factor from both original disk/power/normalization bounds. -/
@[expose] def residualFactor (operation : Operation)
    (leftRadius rightRadius leftPowers rightPowers leftLeading rightLeading rightSource : Fraction.Rational) :
    Fraction.Rational :=
  match operation with
  | .add => 2 * (leftLeading * rightPowers + leftPowers * rightLeading)
  | .mul => 3 * (leftLeading * rightRadius * rightPowers +
      leftRadius * leftPowers * rightLeading + leftLeading * rightSource * rightLeading)

/-- Nonnegative original input bounds give a nonnegative selected residual factor. -/
theorem residualFactor_nonnegative (operation : Operation)
    (leftRadius rightRadius leftPowers rightPowers leftLeading rightLeading rightSource : Fraction.Rational)
    (leftRadiusNonnegative : 0 ≤ leftRadius) (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftPowersNonnegative : 0 ≤ leftPowers) (rightPowersNonnegative : 0 ≤ rightPowers)
    (leftLeadingNonnegative : 0 ≤ leftLeading) (rightLeadingNonnegative : 0 ≤ rightLeading)
    (rightSourceNonnegative : 0 ≤ rightSource) :
    0 ≤ residualFactor operation leftRadius rightRadius leftPowers rightPowers leftLeading rightLeading
      rightSource := by
  cases operation with
  | add =>
      exact Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2)
        (add_nonneg
          (Order.Arithmetic.mul_nonneg_direct leftLeadingNonnegative rightPowersNonnegative)
          (Order.Arithmetic.mul_nonneg_direct leftPowersNonnegative rightLeadingNonnegative))
  | mul =>
      exact Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 3)
        (add_nonneg (add_nonneg
          (Order.Arithmetic.mul_nonneg_direct
            (Order.Arithmetic.mul_nonneg_direct leftLeadingNonnegative rightRadiusNonnegative)
            rightPowersNonnegative)
          (Order.Arithmetic.mul_nonneg_direct
            (Order.Arithmetic.mul_nonneg_direct leftRadiusNonnegative leftPowersNonnegative)
            rightLeadingNonnegative))
          (Order.Arithmetic.mul_nonneg_direct
            (Order.Arithmetic.mul_nonneg_direct leftLeadingNonnegative rightSourceNonnegative)
            rightLeadingNonnegative))

/-- Both original residual readings bound the selected sum/product residual at any retained scalar-vector position.

The product cross term uses the same second source's computed disk value
bound. All point and power readings remain original inputs; no small-error
assumption or supplied output-zero conclusion is needed.
-/
theorem normSq_residual_le (operation : Operation)
    (firstPoint secondPoint firstPower secondPower firstResidual secondResidual : Canonical)
    (error leftRadius rightRadius leftPowers rightPowers leftLeading rightLeading rightSource : Fraction.Rational)
    (errorNonnegative : 0 ≤ error)
    (leftRadiusNonnegative : 0 ≤ leftRadius) (rightRadiusNonnegative : 0 ≤ rightRadius)
    (leftPowersNonnegative : 0 ≤ leftPowers) (_rightPowersNonnegative : 0 ≤ rightPowers)
    (leftLeadingNonnegative : 0 ≤ leftLeading) (rightLeadingNonnegative : 0 ≤ rightLeading)
    (_rightSourceNonnegative : 0 ≤ rightSource)
    (firstPointBound : Norm.Basic.normSq firstPoint ≤ leftRadius)
    (secondPointBound : Norm.Basic.normSq secondPoint ≤ rightRadius)
    (firstPowerBound : Norm.Basic.normSq firstPower ≤ leftPowers)
    (secondPowerBound : Norm.Basic.normSq secondPower ≤ rightPowers)
    (firstResidualBound : Norm.Basic.normSq firstResidual ≤ error * leftLeading)
    (secondResidualBound : Norm.Basic.normSq secondResidual ≤ error * rightLeading)
    (secondSourceBound : Norm.Basic.normSq secondResidual ≤ rightSource * rightLeading) :
    Norm.Basic.normSq (operation.residual firstPoint secondPoint firstPower secondPower firstResidual secondResidual) ≤
      error * residualFactor operation leftRadius rightRadius leftPowers rightPowers leftLeading rightLeading
        rightSource := by
  have firstResidualNonnegative := Order.Arithmetic.mul_nonneg_direct errorNonnegative leftLeadingNonnegative
  have secondResidualNonnegative := Order.Arithmetic.mul_nonneg_direct errorNonnegative rightLeadingNonnegative
  cases operation with
  | add =>
      have first := product_bound firstResidual secondPower _ _ firstResidualBound secondPowerBound
        firstResidualNonnegative
      have second := product_bound firstPower secondResidual _ _ firstPowerBound secondResidualBound
        leftPowersNonnegative
      have combined := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct first second) (by decide : (0 : Fraction.Rational) ≤ 2)
      exact (Norm.Bounds.normSq_add_le_two _ _).trans (combined.trans_eq (by
        dsimp only [residualFactor]
        ring0))
  | mul =>
      have firstPair := product_bound firstResidual secondPoint _ _ firstResidualBound secondPointBound
        firstResidualNonnegative
      have first := product_bound (firstResidual * secondPoint) secondPower _ _ firstPair secondPowerBound
        (Order.Arithmetic.mul_nonneg_direct firstResidualNonnegative rightRadiusNonnegative)
      have secondPair := product_bound firstPoint firstPower _ _ firstPointBound firstPowerBound leftRadiusNonnegative
      have second := product_bound (firstPoint * firstPower) secondResidual _ _ secondPair secondResidualBound
        (Order.Arithmetic.mul_nonneg_direct leftRadiusNonnegative leftPowersNonnegative)
      have cross := product_bound firstResidual secondResidual _ _ firstResidualBound secondSourceBound
        firstResidualNonnegative
      have negativeCross : Norm.Basic.normSq (-(firstResidual * secondResidual)) ≤
          (error * leftLeading) * (rightSource * rightLeading) := by
        rewrite [Norm.Basic.normSq_neg]
        exact cross
      have combined := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct
          (Order.Arithmetic.add_le_add_direct first second) negativeCross)
        (by decide : (0 : Fraction.Rational) ≤ 3)
      have estimate := (Norm.Sum.Indexed.normSq_add_add_le
        (firstResidual * secondPoint * secondPower) (firstPoint * firstPower * secondResidual)
        (-(firstResidual * secondResidual))).trans combined
      change Norm.Basic.normSq
        (firstResidual * secondPoint * secondPower + firstPoint * firstPower * secondResidual -
          firstResidual * secondResidual) ≤ _
      exact estimate.trans_eq (by
        dsimp only [residualFactor]
        ring0)

/-- The computed squared-radius bound of the selected operation on both original input disks. -/
@[expose] def resultRadius (operation : Operation) (first second : Fraction.Rational) : Fraction.Rational :=
  match operation with
  | .add => 2 * (first + second)
  | .mul => first * second

/-- Original nonnegative squared radii give a nonnegative computed result radius. -/
theorem resultRadius_nonnegative (operation : Operation) (first second : Fraction.Rational)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) :
    0 ≤ resultRadius operation first second := by
  cases operation with
  | add => exact Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg firstNonnegative secondNonnegative)
  | mul => exact Order.Arithmetic.mul_nonneg_direct firstNonnegative secondNonnegative

/-- Each original contained scalar pair produces a reading in the computed result disk. -/
theorem normSq_value_le_resultRadius (operation : Operation) (first second : Canonical)
    (firstRadius secondRadius : Fraction.Rational) (firstNonnegative : 0 ≤ firstRadius)
    (firstBound : Norm.Basic.normSq first ≤ firstRadius) (secondBound : Norm.Basic.normSq second ≤ secondRadius) :
    Norm.Basic.normSq (operation.value first second) ≤ resultRadius operation firstRadius secondRadius := by
  cases operation with
  | add =>
      exact (Norm.Bounds.normSq_add_le_two first second).trans
        (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Order.Arithmetic.add_le_add_direct firstBound secondBound) (by decide))
  | mul => exact product_bound first second firstRadius secondRadius firstBound secondBound firstNonnegative

variable {firstPolynomial secondPolynomial : DensePolynomial Canonical}
variable {first : Dense.Companion firstPolynomial} {second : Dense.Companion secondPolynomial}
variable {operation : Operation}

set_option genInjectivity false in
/-- Computed disk and inverse-row budgets for one original retained arithmetic elimination.

Both complete original companion-bound caches are retained. The result radius
comes from those same input requests, and each inverse-row Horner fold consumes
the actual stored elimination coefficient at its original bounded position.
-/
structure Bounds (elimination : Elimination operation first second)
    (firstRadius secondRadius : Fraction.Rational) where
  /-- The original first input's complete retained disk and power bounds. -/
  first : Gaussian.Companion.Bounds elimination.first firstRadius
  /-- The original second input's complete retained disk and power bounds. -/
  second : Gaussian.Companion.Bounds elimination.second secondRadius
  /-- The actual selected-operation result radius. -/
  radius : Fraction.Rational
  /-- The radius was computed from the original two input requests. -/
  radius_eq : radius = resultRadius operation firstRadius secondRadius
  /-- The actual inverse-row coefficient Horner folds at the original product dimension. -/
  inverse : Data.Vector Polynomial.Bounds.Horner (firstPolynomial.natDegree * secondPolynomial.natDegree)
  /-- Each fold consumes that same retained inverse coefficient and computed result radius. -/
  inverse_eq : ∀ index, inverse index = Gaussian.Bounds.Horner.onDisk
    (elimination.pencil.data.inverse
      (Fin.mkDivMod elimination.first.firstIndex elimination.second.firstIndex) index) radius
  /-- The cached positive common ceiling of all inverse-row coefficient readings. -/
  inverseBound : Fraction.Rational
  /-- The ceiling retains its unit floor and the actual finite total of those same folds. -/
  inverseBound_eq : inverseBound = 1 + Fin.sumFin (fun index => (inverse index).value)
  /-- The cached selected-operation source residual multiplier. -/
  residual : Fraction.Rational
  /-- The multiplier consumes the same retained input bounds. -/
  residual_eq : residual = residualFactor operation firstRadius secondRadius
    first.powerBound second.powerBound first.leadingInverse second.leadingInverse second.source.value
  /-- The actual final arithmetic polynomial residual multiplier. -/
  multiplier : Fraction.Rational
  /-- The multiplier uses the original squared dimension, same inverse ceiling and source residual factor. -/
  multiplier_eq : multiplier =
    ((firstPolynomial.natDegree * secondPolynomial.natDegree : Nat) : Fraction.Rational) ^ 2 *
      inverseBound * residual

constructive_injectivity Bounds

/-- Compute original input, result-disk and inverse-row bounds once at the supplied nonnegative radii. -/
def Bounds.prepare (elimination : Elimination operation first second) (firstRadius secondRadius : Fraction.Rational)
    (firstNonnegative : 0 ≤ firstRadius) (secondNonnegative : 0 ≤ secondRadius) :
    Bounds elimination firstRadius secondRadius :=
  let first := Gaussian.Companion.Bounds.prepare elimination.first firstRadius firstNonnegative
  let second := Gaussian.Companion.Bounds.prepare elimination.second secondRadius secondNonnegative
  let radius := resultRadius operation firstRadius secondRadius
  let index := Fin.mkDivMod elimination.first.firstIndex elimination.second.firstIndex
  let inverse := vectorOfFn fun column : Fin (firstPolynomial.natDegree * secondPolynomial.natDegree) =>
    Gaussian.Bounds.Horner.onDisk (elimination.pencil.data.inverse index column) radius
  let inverseBound := 1 + Fin.sumFin (fun index => (inverse index).value)
  let residual := residualFactor operation firstRadius secondRadius first.powerBound second.powerBound
    first.leadingInverse second.leadingInverse second.source.value
  let multiplier := ((firstPolynomial.natDegree * secondPolynomial.natDegree : Nat) : Fraction.Rational) ^ 2 *
    inverseBound * residual
  ⟨first, second, radius, rfl, inverse, fun column => vectorOfFn_apply _ column,
    inverseBound, rfl, residual, rfl, multiplier, rfl⟩

namespace Bounds

variable {elimination : Elimination operation first second} {firstRadius secondRadius : Fraction.Rational}

/-- The original computed result-disk radius is nonnegative. -/
theorem radius_nonnegative (bounds : Bounds elimination firstRadius secondRadius) : 0 ≤ bounds.radius := by
  rewrite [bounds.radius_eq]
  exact resultRadius_nonnegative operation firstRadius secondRadius bounds.first.radius_nonnegative
    bounds.second.radius_nonnegative

/-- Every retained inverse-row value ceiling is nonnegative. -/
theorem inverse_nonnegative (bounds : Bounds elimination firstRadius secondRadius)
    (index : Fin (firstPolynomial.natDegree * secondPolynomial.natDegree)) : 0 ≤ (bounds.inverse index).value := by
  rewrite [bounds.inverse_eq index]
  exact (Gaussian.Bounds.Horner.onDisk_nonnegative _ bounds.radius bounds.radius_nonnegative).1

/-- The common retained inverse-row ceiling is nonnegative. -/
theorem inverseBound_nonnegative (bounds : Bounds elimination firstRadius secondRadius) : 0 ≤ bounds.inverseBound := by
  rewrite [bounds.inverseBound_eq]
  exact add_nonneg (by decide) (Rational.Order.weight_sum_nonnegative _ bounds.inverse_nonnegative)

/-- The original selected-operation residual factor is nonnegative. -/
theorem residual_nonnegative (bounds : Bounds elimination firstRadius secondRadius) : 0 ≤ bounds.residual := by
  rewrite [bounds.residual_eq]
  exact residualFactor_nonnegative operation _ _ _ _ _ _ _ bounds.first.radius_nonnegative
    bounds.second.radius_nonnegative bounds.first.powerBound_positive.le bounds.second.powerBound_positive.le
    bounds.first.leadingInverse_nonnegative bounds.second.leadingInverse_nonnegative bounds.second.source_nonnegative

/-- The actual final arithmetic polynomial multiplier is nonnegative. -/
theorem multiplier_nonnegative (bounds : Bounds elimination firstRadius secondRadius) : 0 ≤ bounds.multiplier := by
  rewrite [bounds.multiplier_eq]
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (Order.Arithmetic.sq_nonneg_direct _)
      bounds.inverseBound_nonnegative) bounds.residual_nonnegative

/-- Each original inverse coefficient reading in the computed result disk is bounded by the same retained ceiling. -/
theorem normSq_inverse_le (bounds : Bounds elimination firstRadius secondRadius) (point : Canonical)
    (inside : Norm.Basic.normSq point ≤ bounds.radius)
    (index : Fin (firstPolynomial.natDegree * secondPolynomial.natDegree)) :
    Norm.Basic.normSq ((elimination.pencil.data.inverse
      (Fin.mkDivMod elimination.first.firstIndex elimination.second.firstIndex) index).eval point) ≤
      bounds.inverseBound := by
  have reading : Norm.Basic.normSq ((elimination.pencil.data.inverse
      (Fin.mkDivMod elimination.first.firstIndex elimination.second.firstIndex) index).eval point) ≤
      (bounds.inverse index).value := by
    rewrite [bounds.inverse_eq index]
    exact Gaussian.Bounds.Horner.normSq_eval_le_onDisk _ bounds.radius bounds.radius_nonnegative point inside
  have retained := Rational.Order.entry_le_sumFin (fun index => (bounds.inverse index).value)
    bounds.inverse_nonnegative index
  have floor : Fin.sumFin (fun index => (bounds.inverse index).value) ≤ bounds.inverseBound := by
    rewrite [bounds.inverseBound_eq]
    have ordered := Order.Arithmetic.add_le_add_direct
      (by decide : (0 : Fraction.Rational) ≤ 1)
      (show Fin.sumFin (fun index => (bounds.inverse index).value) ≤
        Fin.sumFin (fun index => (bounds.inverse index).value) from le_rfl)
    rewrite [Fraction.zero_add] at ordered
    exact ordered
  exact reading.trans (retained.trans floor)

/-- Both original contained source readings bound every actual arithmetic residual component. -/
theorem normSq_component_le (bounds : Bounds elimination firstRadius secondRadius)
    (firstPoint secondPoint : Canonical)
    (firstInside : Norm.Basic.normSq firstPoint ≤ firstRadius)
    (secondInside : Norm.Basic.normSq secondPoint ≤ secondRadius)
    (row : Fin (firstPolynomial.natDegree * secondPolynomial.natDegree)) :
    Norm.Basic.normSq (operation.residual firstPoint secondPoint
      (elimination.first.powers firstPoint (Data.Fin.divNat row))
      (elimination.second.powers secondPoint (Data.Fin.modNat row))
      (elimination.first.residual firstPoint (Data.Fin.divNat row))
      (elimination.second.residual secondPoint (Data.Fin.modNat row))) ≤
      (Norm.Basic.normSq (firstPolynomial.eval firstPoint) + Norm.Basic.normSq (secondPolynomial.eval secondPoint)) *
        bounds.residual := by
  let error := Norm.Basic.normSq (firstPolynomial.eval firstPoint) +
    Norm.Basic.normSq (secondPolynomial.eval secondPoint)
  have errorNonnegative : 0 ≤ error := add_nonneg (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _)
  have firstError : Norm.Basic.normSq (firstPolynomial.eval firstPoint) ≤ error := by
    have ordered := Order.Arithmetic.add_le_add_direct (show
      Norm.Basic.normSq (firstPolynomial.eval firstPoint) ≤ Norm.Basic.normSq (firstPolynomial.eval firstPoint)
        from le_rfl) (Norm.Basic.normSq_nonneg (secondPolynomial.eval secondPoint))
    rewrite [add_zero] at ordered
    exact ordered
  have secondError : Norm.Basic.normSq (secondPolynomial.eval secondPoint) ≤ error := by
    have ordered := Order.Arithmetic.add_le_add_direct
      (Norm.Basic.normSq_nonneg (firstPolynomial.eval firstPoint))
      (show Norm.Basic.normSq (secondPolynomial.eval secondPoint) ≤
        Norm.Basic.normSq (secondPolynomial.eval secondPoint) from le_rfl)
    rewrite [Fraction.zero_add] at ordered
    exact ordered
  have firstResidual := (bounds.first.normSq_residual_le firstPoint (Data.Fin.divNat row)).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct firstError bounds.first.leadingInverse_nonnegative)
  have secondResidual := (bounds.second.normSq_residual_le secondPoint (Data.Fin.modNat row)).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct secondError bounds.second.leadingInverse_nonnegative)
  rewrite [bounds.residual_eq]
  exact normSq_residual_le operation firstPoint secondPoint _ _ _ _ error _ _ _ _ _ _ _ errorNonnegative
    bounds.first.radius_nonnegative bounds.second.radius_nonnegative bounds.first.powerBound_positive.le
    bounds.second.powerBound_positive.le bounds.first.leadingInverse_nonnegative
    bounds.second.leadingInverse_nonnegative
    bounds.second.source_nonnegative firstInside secondInside
    (bounds.first.normSq_power_le firstPoint firstInside (Data.Fin.divNat row))
    (bounds.second.normSq_power_le secondPoint secondInside (Data.Fin.modNat row)) firstResidual secondResidual
    (bounds.second.normSq_residual_le_source secondPoint secondInside (Data.Fin.modNat row))

/-- The actual quadrance sum of both original polynomial residual readings. -/
@[expose] def sourceErrors (firstPoint secondPoint : Canonical) : Fraction.Rational :=
  Norm.Basic.normSq (firstPolynomial.eval firstPoint) + Norm.Basic.normSq (secondPolynomial.eval secondPoint)

/-- The exact original arithmetic residual vector at the retained product dimension. -/
def residualVector (elimination : Elimination operation first second) (firstPoint secondPoint : Canonical) :
    Data.Vector Canonical (firstPolynomial.natDegree * secondPolynomial.natDegree) :=
  vectorOfFn fun row => operation.residual firstPoint secondPoint
    (elimination.first.powers firstPoint (Data.Fin.divNat row))
    (elimination.second.powers secondPoint (Data.Fin.modNat row))
    (elimination.first.residual firstPoint (Data.Fin.divNat row))
    (elimination.second.residual secondPoint (Data.Fin.modNat row))

/-- The exact original polynomial-reading budget from the retained multiplier and both source errors. -/
@[expose] def polynomialBudget (bounds : Bounds elimination firstRadius secondRadius)
    (firstPoint secondPoint : Canonical) : Fraction.Rational :=
  bounds.multiplier * sourceErrors (firstPolynomial := firstPolynomial) (secondPolynomial := secondPolynomial)
    firstPoint secondPoint

/-- The exact quantitative assertion for the original cached arithmetic polynomial reading. -/
@[expose] def PolynomialBound (bounds : Bounds elimination firstRadius secondRadius)
    (firstPoint secondPoint : Canonical) : Prop :=
  Norm.Basic.normSq (elimination.polynomial.eval (operation.value firstPoint secondPoint)) ≤
    bounds.polynomialBudget firstPoint secondPoint

/-- The original cached arithmetic polynomial reading is bounded by its computed multiplier times both original errors.

The same retained inverse-row Horner folds and original source/power bounds
pay the finite sum budget. The conclusion holds at every contained pair of
scalar readings, including nonroots, with no supplied output-zero equation.
-/
theorem normSq_polynomial_le (bounds : Bounds elimination firstRadius secondRadius)
    (firstPoint secondPoint : Canonical)
    (firstInside : Norm.Basic.normSq firstPoint ≤ firstRadius)
    (secondInside : Norm.Basic.normSq secondPoint ≤ secondRadius) : PolynomialBound bounds firstPoint secondPoint := by
  let point := operation.value firstPoint secondPoint
  let index := Fin.mkDivMod elimination.first.firstIndex elimination.second.firstIndex
  let errors := sourceErrors (firstPolynomial := firstPolynomial) (secondPolynomial := secondPolynomial)
    firstPoint secondPoint
  let residuals := residualVector elimination firstPoint secondPoint
  have pointInside : Norm.Basic.normSq point ≤ bounds.radius := by
    rewrite [bounds.radius_eq]
    exact normSq_value_le_resultRadius operation firstPoint secondPoint firstRadius secondRadius
      bounds.first.radius_nonnegative firstInside secondInside
  have sourceReading : elimination.polynomial.eval point =
      SquareMatrix.Multiplication.matrixVector
        (Evaluation.evalMatrix point elimination.pencil.data.inverse) residuals index :=
    elimination.polynomial_residual firstPoint secondPoint
  have terms : ∀ row, Norm.Basic.normSq
      (Evaluation.evalMatrix point elimination.pencil.data.inverse index row * residuals row) ≤
        bounds.inverseBound * (errors * bounds.residual) := by
    intro row
    have original := bounds.normSq_component_le firstPoint secondPoint firstInside secondInside row
    have residualBound : Norm.Basic.normSq (residuals row) ≤ errors * bounds.residual := by
      change Norm.Basic.normSq ((residualVector elimination firstPoint secondPoint) row) ≤ _
      dsimp only [residualVector]
      rewrite [vectorOfFn_apply]
      exact original
    have inverseBound : Norm.Basic.normSq
        (Evaluation.evalMatrix point elimination.pencil.data.inverse index row) ≤ bounds.inverseBound := by
      rewrite [Evaluation.evalMatrix_apply]
      exact bounds.normSq_inverse_le point pointInside row
    exact product_bound _ _ _ _ inverseBound residualBound bounds.inverseBound_nonnegative
  have estimate := Norm.Sum.Indexed.normSq_sumFin_le
    (fun row => Evaluation.evalMatrix point elimination.pencil.data.inverse index row * residuals row)
    (bounds.inverseBound * (errors * bounds.residual)) terms
  have matrixReading : Norm.Basic.normSq (SquareMatrix.Multiplication.matrixVector
      (Evaluation.evalMatrix point elimination.pencil.data.inverse) residuals index) ≤
      ((firstPolynomial.natDegree * secondPolynomial.natDegree : Nat) : Fraction.Rational) ^ 2 *
        (bounds.inverseBound * (errors * bounds.residual)) := by
    rewrite [SquareMatrix.Multiplication.matrixVector_apply]
    exact estimate
  have payment : ((firstPolynomial.natDegree * secondPolynomial.natDegree : Nat) : Fraction.Rational) ^ 2 *
      (bounds.inverseBound * (errors * bounds.residual)) = bounds.polynomialBudget firstPoint secondPoint := by
    dsimp only [polynomialBudget]
    rewrite [bounds.multiplier_eq]
    ring0
  unfold PolynomialBound
  exact (congrArg Norm.Basic.normSq sourceReading).le.trans (matrixReading.trans_eq payment)

end Bounds

end Purelib.Polynomial.Dense.Gaussian.Companion.Arithmetic

end
