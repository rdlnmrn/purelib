module

public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
public import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

/-! # Polynomial changes retaining an original uniform differential observation

The original finite reading, Point, sheet, denotation, channel and state
remain unchanged. One supplied cached polynomial difference changes only
the error decomposition. The actual target model keeps its own endpoints,
polynomial and derived local allowance.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel LocalObservation)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds RegionClearance)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model Polynomial Box)
open Purelib.Riemann.Normalization.InverseModelOverlap (OverlapSample)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Dense.Power (OddPowers)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : OddPowerDifferential curve.polynomial}
  {start finish : LiftedPoint 2} {lifted : LiftedCell start finish} {source : CellModel} {parameter : Rational}

/-- The exact local charge for one original uniform reading and a polynomial-gap bound. -/
def polynomialCharge (allowance gap : Rational) : Rational := 2 * allowance + 4 * gap

/-- The retained polynomial-change charge has its original scalar formula. -/
theorem polynomialCharge_eq (allowance gap : Rational) :
    polynomialCharge allowance gap = 2 * allowance + 4 * gap := by
  unfold polynomialCharge
  rfl

/-- Nonnegative original allowance and polynomial gap give a nonnegative actual changed charge. -/
theorem polynomialCharge_nonnegative {allowance gap : Rational}
    (allowanceNonnegative : 0 ≤ allowance) (gapNonnegative : 0 ≤ gap) :
    0 ≤ polynomialCharge allowance gap := by
  exact (Field.zero_add (0 : Rational)).symm.trans_le
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2) allowanceNonnegative)
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 4) gapNonnegative))

/-- The original error and polynomial difference fit the exact derived local charge. -/
private theorem changed_error_le {error difference : Canonical} {allowance gap : Rational}
    (old : normSq error ≤ allowance) (bounded : normSq difference ≤ gap) :
    normSq (error + difference) ≤ polynomialCharge allowance gap := by
  have gapNonnegative := (Norm.Basic.normSq_nonneg difference).trans bounded
  have twiceGap : 2 * gap ≤ 4 * gap :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) gapNonnegative
  calc
    _ ≤ 2 * (normSq error + normSq difference) := Norm.Bounds.normSq_add_le_two error difference
    _ ≤ 2 * (allowance + gap) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct old bounded)
        (by decide : (0 : Rational) ≤ 2)
    _ = 2 * allowance + 2 * gap := by ring1
    _ ≤ polynomialCharge allowance gap := Arithmetic.add_le_add_direct (Order.Basic.le_refl _) twiceGap

/-- The actual retained channel radius and changed error fit the same exact local charge. -/
private theorem changed_semantic_le {error difference : Canonical} {radius allowance gap : Rational}
    (radiusNonnegative : 0 ≤ radius)
    (old : 2 * (4 * radius + normSq error) ≤ allowance) (bounded : normSq difference ≤ gap) :
    2 * (4 * radius + normSq (error + difference)) ≤ polynomialCharge allowance gap := by
  have changed := (Norm.Bounds.normSq_add_le_two error difference).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct (Order.Basic.le_refl _) bounded) (by decide))
  have twiceOld := Arithmetic.mul_le_mul_of_nonneg_left_direct old (by decide : (0 : Rational) ≤ 2)
  calc
    _ ≤ 2 * (4 * radius + 2 * (normSq error + gap)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct (Order.Basic.le_refl _) changed) (by decide)
    _ ≤ 2 * (2 * (4 * radius + normSq error)) + 4 * gap := by
      apply Arithmetic.le_of_sub_nonneg_direct
      have nonnegative := Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 8) radiusNonnegative
      exact nonnegative.trans_eq (by ring1)
    _ ≤ polynomialCharge allowance gap := Arithmetic.add_le_add_direct twiceOld (Order.Basic.le_refl _)

/-- Change the polynomial of an actual uniform observation using one retained scalar difference.

Both target endpoint equations are exact geometry readbacks. Its allowance
is the displayed derived charge, rather than a supplied final accuracy
claim. The polynomial difference is a certified cache supplied by the actual
model comparison; no original query, model, root or reading is executed here.
-/
def changePolynomial (original : UniformObservation curve differential lifted source parameter)
    (target : CellModel) (startEq : target.start = source.start) (finishEq : target.finish = source.finish)
    (difference : {value : Canonical // value =
      Evaluation.eval source.polynomial ⟨parameter, 0⟩ - Evaluation.eval target.polynomial ⟨parameter, 0⟩})
    (gap : Rational) (bounded : normSq difference.val ≤ gap)
    (charge : target.localAllowance = polynomialCharge source.localAllowance gap) :
    UniformObservation curve differential lifted target parameter := by
  let error := original.observation.error + difference.val
  have oldError : normSq original.observation.error ≤ source.localAllowance := by
    simpa only [Norm.Basic.normSq_eq_canonical] using original.observation.error_le
  let observation : LocalObservation target.polynomial target.localAllowance :=
    { parameter := parameter
      integrandReading := original.observation.integrandReading
      error := error
      decomposition := by
        have old := (congrArg (fun value : Rational => original.observation.integrandReading -
          Evaluation.eval source.polynomial ⟨value, 0⟩) original.parameter_eq).symm.trans
            original.observation.decomposition
        change original.observation.integrandReading - Evaluation.eval target.polynomial ⟨parameter, 0⟩ =
          original.observation.error + difference.val
        rewrite [difference.property, ← old]
        ring1
      error_le := by
        have paid := (changed_error_le oldError bounded).trans_eq charge.symm
        simpa only [Norm.Basic.normSq_eq_canonical] using paid }
  have displacement : target.displacement = source.displacement := by
    unfold CellModel.displacement
    rewrite [startEq, finishEq]
    rfl
  have pointEq : original.algebraic.point = target.observationPoint observation := by
    apply original.algebraic.point_eq.trans
    unfold CellModel.observationPoint
    rewrite [original.parameter_eq, startEq, displacement]
    rfl
  exact
    { observation := observation
      parameter_eq := rfl
      algebraic :=
        { point := original.algebraic.point
          point_eq := pointEq
          sheetValue := original.algebraic.sheetValue
          chosenSheet_eq := original.algebraic.chosenSheet_eq
          interpretation := original.algebraic.interpretation
          readingState := original.algebraic.readingState
          readingPossible := original.algebraic.readingPossible }
      semantic_error_le :=
        (changed_semantic_le
          (original.algebraic.interpretation.channel.name.process.ball original.algebraic.readingState).radiusSq_nonneg
          original.semantic_error_le bounded).trans_eq charge.symm }

/-- A polynomial change retains the original finite integrand reading literally. -/
theorem changePolynomial_reading (original : UniformObservation curve differential lifted source parameter)
    (target : CellModel) (startEq : target.start = source.start) (finishEq : target.finish = source.finish)
    (difference : {value : Canonical // value =
      Evaluation.eval source.polynomial ⟨parameter, 0⟩ - Evaluation.eval target.polynomial ⟨parameter, 0⟩})
    (gap : Rational) (bounded : normSq difference.val ≤ gap)
    (charge : target.localAllowance = polynomialCharge source.localAllowance gap) :
    (original.changePolynomial target startEq finishEq difference gap bounded charge).observation.integrandReading =
      original.observation.integrandReading := by
  unfold changePolynomial
  rfl

/-- A polynomial change retains the original Point and its exact algebraic root name. -/
theorem changePolynomial_root_name (original : UniformObservation curve differential lifted source parameter)
    (target : CellModel) (startEq : target.start = source.start) (finishEq : target.finish = source.finish)
    (difference : {value : Canonical // value =
      Evaluation.eval source.polynomial ⟨parameter, 0⟩ - Evaluation.eval target.polynomial ⟨parameter, 0⟩})
    (gap : Rational) (bounded : normSq difference.val ≤ gap)
    (charge : target.localAllowance = polynomialCharge source.localAllowance gap) :
    (original.changePolynomial target startEq finishEq difference gap bounded charge).algebraic.sheetValue.value.name =
      original.algebraic.sheetValue.value.name := by
  unfold changePolynomial
  rfl

/-- Change to an actual full-numerator model coefficient using its genuine unflipped overlap.

The given original observation is consumed once. Its cached polynomial
value is recovered from that SAME reading and error; only the supplied
actual target coefficient value is read separately. Both compilation laws
are original model/power factory readbacks. The coefficient gap and local
charge are derived internally, before the original target pullback is used.
-/
def changeFromOverlap
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {leftBox rightBox : Box} {numerator targetSource originalSource : Polynomial}
    {clearance : RegionClearance curve.polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model curve.polynomial leftBox} {right : Model curve.polynomial rightBox}
    (exponent : Nat) (original : UniformObservation curve differential lifted source parameter)
    (sourceStart : source.start = start.coordinate) (sourceFinish : source.finish = finish.coordinate)
    (sourceEvaluation : Evaluation.eval source.polynomial ⟨parameter, 0⟩ =
      originalSource.eval (coordinate.point parameter))
    (targetPullback : Spatial.Pullback coordinate targetSource
      (polynomialCharge source.localAllowance (bounds.powerScale exponent * (left.bound + right.bound))))
    (sample : OverlapSample left right (coordinate.point parameter))
    (leftInside : leftBox.Contains (coordinate.point parameter))
    (rightInside : rightBox.Contains (coordinate.point parameter))
    (unflipped : sample.alignment.flip = false)
    (targetCompiled : targetSource.eval (coordinate.point parameter) =
      numerator.eval (coordinate.point parameter) * (left.value.eval (coordinate.point parameter)) ^ exponent)
    (originalCompiled : originalSource.eval (coordinate.point parameter) =
      numerator.eval (coordinate.point parameter) * (right.value.eval (coordinate.point parameter)) ^ exponent)
    (targetValue : {value : Canonical // value = targetSource.eval (coordinate.point parameter)}) :
    UniformObservation curve differential lifted targetPullback.model parameter := by
  let sourceValue := original.observation.integrandReading - original.observation.error
  have sourceScalar : sourceValue = Evaluation.eval source.polynomial ⟨parameter, 0⟩ := by
    have old := (congrArg (fun value : Rational => original.observation.integrandReading -
      Evaluation.eval source.polynomial ⟨value, 0⟩) original.parameter_eq).symm.trans
        original.observation.decomposition
    change original.observation.integrandReading - original.observation.error = _
    rewrite [← old]
    ring1
  have targetScalar : targetValue.val = Evaluation.eval targetPullback.model.polynomial ⟨parameter, 0⟩ :=
    targetValue.property.trans (targetPullback.eval_point parameter).symm
  let difference := sourceValue - targetValue.val
  have differenceEq : difference = Evaluation.eval source.polynomial ⟨parameter, 0⟩ -
      Evaluation.eval targetPullback.model.polynomial ⟨parameter, 0⟩ :=
    congrArg₂ (fun first last : Canonical => first - last) sourceScalar targetScalar
  have gap := bounds.coefficient_power_gap_le sample leftInside rightInside unflipped exponent
  rewrite [← targetCompiled, ← originalCompiled] at gap
  have bounded : normSq difference ≤ bounds.powerScale exponent * (left.bound + right.bound) := by
    have cached : difference = originalSource.eval (coordinate.point parameter) -
        targetSource.eval (coordinate.point parameter) :=
      congrArg₂ (fun first last : Canonical => first - last)
        (sourceScalar.trans sourceEvaluation) targetValue.property
    exact (congrArg normSq cached).trans_le
      ((Norm.Bounds.normSq_sub_symm _ _).trans_le gap)
  have charge : targetPullback.model.localAllowance =
      polynomialCharge source.localAllowance
        (bounds.powerScale exponent * (left.bound + right.bound)) := targetPullback.allowance_eq
  exact original.changePolynomial targetPullback.model
    (targetPullback.start_eq.trans sourceStart.symm)
    (targetPullback.finish_eq.trans sourceFinish.symm)
    ⟨difference, differenceEq⟩ _ bounded charge

/-- The actual overlap change retains its original finite reading. -/
theorem changeFromOverlap_reading
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {leftBox rightBox : Box} {numerator targetSource originalSource : Polynomial}
    {clearance : RegionClearance curve.polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model curve.polynomial leftBox} {right : Model curve.polynomial rightBox}
    (exponent : Nat) (original : UniformObservation curve differential lifted source parameter)
    (sourceStart : source.start = start.coordinate) (sourceFinish : source.finish = finish.coordinate)
    (sourceEvaluation : Evaluation.eval source.polynomial ⟨parameter, 0⟩ =
      originalSource.eval (coordinate.point parameter))
    (targetPullback : Spatial.Pullback coordinate targetSource
      (polynomialCharge source.localAllowance (bounds.powerScale exponent * (left.bound + right.bound))))
    (sample : OverlapSample left right (coordinate.point parameter))
    (leftInside : leftBox.Contains (coordinate.point parameter))
    (rightInside : rightBox.Contains (coordinate.point parameter))
    (unflipped : sample.alignment.flip = false)
    (targetCompiled : targetSource.eval (coordinate.point parameter) =
      numerator.eval (coordinate.point parameter) * (left.value.eval (coordinate.point parameter)) ^ exponent)
    (originalCompiled : originalSource.eval (coordinate.point parameter) =
      numerator.eval (coordinate.point parameter) * (right.value.eval (coordinate.point parameter)) ^ exponent)
    (targetValue : {value : Canonical // value = targetSource.eval (coordinate.point parameter)}) :
    (changeFromOverlap bounds exponent original sourceStart sourceFinish sourceEvaluation targetPullback
      sample leftInside rightInside unflipped targetCompiled originalCompiled
      targetValue).observation.integrandReading =
      original.observation.integrandReading := by
  unfold changeFromOverlap changePolynomial
  rfl

/-- The actual overlap change retains its original signed root generator. -/
theorem changeFromOverlap_root_name
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {leftBox rightBox : Box} {numerator targetSource originalSource : Polynomial}
    {clearance : RegionClearance curve.polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model curve.polynomial leftBox} {right : Model curve.polynomial rightBox}
    (exponent : Nat) (original : UniformObservation curve differential lifted source parameter)
    (sourceStart : source.start = start.coordinate) (sourceFinish : source.finish = finish.coordinate)
    (sourceEvaluation : Evaluation.eval source.polynomial ⟨parameter, 0⟩ =
      originalSource.eval (coordinate.point parameter))
    (targetPullback : Spatial.Pullback coordinate targetSource
      (polynomialCharge source.localAllowance (bounds.powerScale exponent * (left.bound + right.bound))))
    (sample : OverlapSample left right (coordinate.point parameter))
    (leftInside : leftBox.Contains (coordinate.point parameter))
    (rightInside : rightBox.Contains (coordinate.point parameter))
    (unflipped : sample.alignment.flip = false)
    (targetCompiled : targetSource.eval (coordinate.point parameter) =
      numerator.eval (coordinate.point parameter) * (left.value.eval (coordinate.point parameter)) ^ exponent)
    (originalCompiled : originalSource.eval (coordinate.point parameter) =
      numerator.eval (coordinate.point parameter) * (right.value.eval (coordinate.point parameter)) ^ exponent)
    (targetValue : {value : Canonical // value = targetSource.eval (coordinate.point parameter)}) :
    (changeFromOverlap bounds exponent original sourceStart sourceFinish sourceEvaluation targetPullback
      sample leftInside rightInside unflipped targetCompiled originalCompiled
      targetValue).algebraic.sheetValue.value.name =
      original.algebraic.sheetValue.value.name := by
  unfold changeFromOverlap changePolynomial
  rfl

/-- Change the original observation using the SAME actual inverse-model coefficient.

The given source cell and its original observation remain retained values,
including when that cell is an actual cached polynomial restriction. Its
endpoint and evaluation readbacks identify the same physical coordinate.
The actual target pullback uses the internally derived gap and local charge;
no model, power table, Point, root witness or source query is rebuilt.
-/
def changeInverse
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {leftBox rightBox : Box} {numerator targetSource originalSource : Polynomial}
    {clearance : RegionClearance curve.polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model curve.polynomial leftBox} {right : Model curve.polynomial rightBox}
    (original : UniformObservation curve differential lifted source parameter)
    (sourceStart : source.start = start.coordinate) (sourceFinish : source.finish = finish.coordinate)
    (sourceEvaluation : Evaluation.eval source.polynomial ⟨parameter, 0⟩ =
      originalSource.eval (coordinate.point parameter))
    (targetPullback : Spatial.Pullback coordinate targetSource
      (polynomialCharge source.localAllowance (bounds.powerScale 1 * (left.bound + right.bound))))
    (sample : OverlapSample left right (coordinate.point parameter))
    (leftInside : leftBox.Contains (coordinate.point parameter))
    (rightInside : rightBox.Contains (coordinate.point parameter))
    (unflipped : sample.alignment.flip = false)
    (targetSourceEq : targetSource = numerator * left.value)
    (originalSourceEq : originalSource = numerator * right.value)
    (targetValue : {value : Canonical // value = targetSource.eval (coordinate.point parameter)}) :
    UniformObservation curve differential lifted targetPullback.model parameter :=
  changeFromOverlap bounds 1 original sourceStart sourceFinish sourceEvaluation
    targetPullback sample leftInside rightInside unflipped
    (by rewrite [targetSourceEq, DensePolynomial.eval_mul, pow_one]; rfl)
    (by rewrite [originalSourceEq, DensePolynomial.eval_mul, pow_one]; rfl) targetValue

/-- Change the original observation using the SAME two retained cubic polynomial caches.

The given source cell and its original observation remain retained values,
including when that cell is an actual cached polynomial restriction. Its
endpoint and evaluation readbacks identify the same physical coordinate.
The actual target pullback uses the internally derived gap and local charge;
no model, power table, Point, root witness or source query is rebuilt.
-/
def changeCube
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {leftBox rightBox : Box} {numerator targetSource originalSource : Polynomial}
    {clearance : RegionClearance curve.polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model curve.polynomial leftBox} {right : Model curve.polynomial rightBox}
    (leftPowers : OddPowers left.value) (rightPowers : OddPowers right.value)
    (original : UniformObservation curve differential lifted source parameter)
    (sourceStart : source.start = start.coordinate) (sourceFinish : source.finish = finish.coordinate)
    (sourceEvaluation : Evaluation.eval source.polynomial ⟨parameter, 0⟩ =
      originalSource.eval (coordinate.point parameter))
    (targetPullback : Spatial.Pullback coordinate targetSource
      (polynomialCharge source.localAllowance (bounds.powerScale 3 * (left.bound + right.bound))))
    (sample : OverlapSample left right (coordinate.point parameter))
    (leftInside : leftBox.Contains (coordinate.point parameter))
    (rightInside : rightBox.Contains (coordinate.point parameter))
    (unflipped : sample.alignment.flip = false)
    (targetSourceEq : targetSource = numerator * leftPowers.cube)
    (originalSourceEq : originalSource = numerator * rightPowers.cube)
    (targetValue : {value : Canonical // value = targetSource.eval (coordinate.point parameter)}) :
    UniformObservation curve differential lifted targetPullback.model parameter :=
  changeFromOverlap bounds 3 original sourceStart sourceFinish sourceEvaluation
    targetPullback sample leftInside rightInside unflipped
    (by rewrite [targetSourceEq, DensePolynomial.eval_mul, leftPowers.cube_eval]; rfl)
    (by rewrite [originalSourceEq, DensePolynomial.eval_mul, rightPowers.cube_eval]; rfl) targetValue

/-- Change the original observation using the SAME two retained fifth-power polynomial caches.

The given source cell and its original observation remain retained values,
including when that cell is an actual cached polynomial restriction. Its
endpoint and evaluation readbacks identify the same physical coordinate.
The actual target pullback uses the internally derived gap and local charge;
no model, power table, Point, root witness or source query is rebuilt.
-/
def changeFifth
    {coordinate : Spatial.Coordinate start.coordinate finish.coordinate}
    {leftBox rightBox : Box} {numerator targetSource originalSource : Polynomial}
    {clearance : RegionClearance curve.polynomial leftBox}
    (bounds : PrimitiveOverlapBounds clearance numerator)
    {left : Model curve.polynomial leftBox} {right : Model curve.polynomial rightBox}
    (leftPowers : OddPowers left.value) (rightPowers : OddPowers right.value)
    (original : UniformObservation curve differential lifted source parameter)
    (sourceStart : source.start = start.coordinate) (sourceFinish : source.finish = finish.coordinate)
    (sourceEvaluation : Evaluation.eval source.polynomial ⟨parameter, 0⟩ =
      originalSource.eval (coordinate.point parameter))
    (targetPullback : Spatial.Pullback coordinate targetSource
      (polynomialCharge source.localAllowance (bounds.powerScale 5 * (left.bound + right.bound))))
    (sample : OverlapSample left right (coordinate.point parameter))
    (leftInside : leftBox.Contains (coordinate.point parameter))
    (rightInside : rightBox.Contains (coordinate.point parameter))
    (unflipped : sample.alignment.flip = false)
    (targetSourceEq : targetSource = numerator * leftPowers.fifth)
    (originalSourceEq : originalSource = numerator * rightPowers.fifth)
    (targetValue : {value : Canonical // value = targetSource.eval (coordinate.point parameter)}) :
    UniformObservation curve differential lifted targetPullback.model parameter :=
  changeFromOverlap bounds 5 original sourceStart sourceFinish sourceEvaluation
    targetPullback sample leftInside rightInside unflipped
    (by rewrite [targetSourceEq, DensePolynomial.eval_mul, leftPowers.fifth_eval]; rfl)
    (by rewrite [originalSourceEq, DensePolynomial.eval_mul, rightPowers.fifth_eval]; rfl) targetValue

end Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation

end
