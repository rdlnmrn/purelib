module

public import Purelib.Polynomial.Recurrence.Mode.Reading.Selected
public import Purelib.Data.Vector.Dependent
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Weight
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Synchronized decay of original selected finite combinations

One finite maximum synchronizes the retained inside thresholds. Original
coefficient weights, mode errors and actual product-error coefficients then
prepare one positive endpoint tolerance for the reading of the same formal
combination at every coordinate of that common finite window.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Reading

open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots

variable {K : Type*} [CommRing K]

namespace Combination

/-- The original common-window coordinate stays within its retained complete source horizon. -/
@[expose] def index (start : Nat) {count : Nat} (offset : Fin count) : Fin (start + count) :=
  ⟨start + offset.val, Nat.add_lt_add_left offset.isLt start⟩

set_option genInjectivity false in
/-- Cached source-fixed product discrepancies for one weighted mode on a common window.

The original root, order and coefficient weight remain indices. The mode's
original complete power/error parameters are prepared once. Actual source
mode-weight bounds and their product-error coefficients are materialized only at
the requested common-window coordinates, before observing a reading.
-/
structure Column (weight : Weight K) (root : K) (gain : Rational) (order : Nat)
    (coefficientWeight : Rational) (start count : Nat) where
  /-- The fixed original gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- The original finite mode parameters cover the same common window. -/
  parameters : Parameters weight root gain order (start + count)
  /-- The original parameters use the same retained complete source horizon. -/
  parameters_eq : parameters = Parameters.prepare weight root gain gainNonnegative order (start + count)
  /-- The original cached source-mode weight bounds at the common-window coordinates. -/
  modeWeights : Vec Rational count
  /-- Every bound consumes the same original retained power table and Pascal scalar. -/
  modeWeights_eq : ∀ offset, modeWeights offset = parameters.weightCoefficient (index start offset)
  /-- Materialized original weighted-product discrepancy coefficients. -/
  coefficients : Vec Rational count
  /-- Each coefficient pays both actual product error and the original mode discrepancy. -/
  coefficients_eq : ∀ offset, coefficients offset = 2 * (coefficientWeight * modeWeights offset +
    gain * coefficientWeight * parameters.coefficients (index start offset))
  /-- The once-computed total of those actual common-window error coefficients. -/
  total : Rational
  /-- The total consumes the same retained coefficient table. -/
  total_eq : total = sumFin (fun offset => coefficients offset)

constructive_injectivity Column

namespace Column

/-- Prepare one weighted mode's original finite coefficients without observing a reading. -/
@[expose] def prepare (weight : Weight K) (root : K) (gain : Rational) (gainNonnegative : 0 ≤ gain)
    (order : Nat) (coefficientWeight : Rational) (start count : Nat) :
    Column weight root gain order coefficientWeight start count :=
  let parameters := Parameters.prepare weight root gain gainNonnegative order (start + count)
  let modeWeights := vectorOfFn (fun offset : Fin count => parameters.weightCoefficient (index start offset))
  let coefficients := vectorOfFn (fun offset : Fin count => 2 * (coefficientWeight * modeWeights offset +
    gain * coefficientWeight * parameters.coefficients (index start offset)))
  let total := sumFin (fun offset => coefficients offset)
  { gainNonnegative, parameters, parameters_eq := rfl, modeWeights
    modeWeights_eq := fun offset => vectorOfFn_apply _ offset
    coefficients, coefficients_eq := fun offset => vectorOfFn_apply _ offset, total, total_eq := rfl }

variable {weight : Weight K} {root : K} {gain coefficientWeight : Rational} {order start count : Nat}

/-- Each stored discrepancy coefficient is nonnegative when its same source coefficient weight is. -/
theorem coefficient_nonnegative (retained : Column weight root gain order coefficientWeight start count)
    (nonnegative : 0 ≤ coefficientWeight) (offset : Fin count) : 0 ≤ retained.coefficients offset := by
  rewrite [retained.coefficients_eq, retained.modeWeights_eq]
  exact Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 2)
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_nonneg_direct nonnegative (retained.parameters.weightCoefficient_nonnegative _))
      (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct retained.gainNonnegative nonnegative)
        (retained.parameters.coefficient_nonnegative _)))

/-- The same retained coefficient total is nonnegative. -/
theorem total_nonnegative (retained : Column weight root gain order coefficientWeight start count)
    (nonnegative : 0 ≤ coefficientWeight) : 0 ≤ retained.total := by
  rewrite [retained.total_eq]
  exact weight_sum_nonnegative _ (retained.coefficient_nonnegative nonnegative)

/-- The retained total bounds every actual common-window discrepancy coefficient. -/
theorem coefficient_le_total (retained : Column weight root gain order coefficientWeight start count)
    (nonnegative : 0 ≤ coefficientWeight) (offset : Fin count) : retained.coefficients offset ≤ retained.total := by
  rewrite [retained.total_eq]
  exact entry_le_sumFin _ (retained.coefficient_nonnegative nonnegative) offset

/-- The actual same formal weighted mode pays its retained product and mode error at a common-window index. -/
theorem bound (retained : Column weight root gain order coefficientWeight start count)
    (coefficient : K) (coefficientWeight_eq : coefficientWeight = weight.value coefficient)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (offset : Fin count) :
    Norm.Basic.normSq (reading.read (coefficient * entry root order (start + offset.val)) -
      reading.read coefficient * entry (reading.read root) order (start + offset.val)) ≤
        reading.error * retained.coefficients offset := by
  have bounded := retained.parameters.weighted_entry_bound reading gain_eq coefficient (index start offset)
  have modeWeightBound : weight.value (entry root order (start + offset.val)) ≤ retained.modeWeights offset :=
    (retained.parameters.weight_bound (index start offset)).trans_eq (retained.modeWeights_eq offset).symm
  have first := Arithmetic.mul_le_mul_of_nonneg_left_direct modeWeightBound (weight.nonnegative coefficient)
  have sumBound := Arithmetic.add_le_add_direct first
    (le_refl (gain * weight.value coefficient * retained.parameters.coefficients (index start offset)))
  have multiplied := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound (by decide : (0 : Rational) ≤ 2))
      reading.errorNonnegative
  exact bounded.trans (multiplied.trans_eq (by
    rewrite [retained.coefficients_eq]
    exact congrArg (fun value => reading.error * (2 *
      (value * retained.modeWeights offset +
        gain * value * retained.parameters.coefficients (index start offset)))) coefficientWeight_eq.symm))

end Column

variable [DecidableEq K] {polynomial : DensePolynomial K} {bank : Bank polynomial}

/-- The dependent original inside thresholds at the same selected-word occurrence orders. -/
abbrev Thresholds (selection : Word.Selection bank) (occurrences : Occurrences selection.word)
    (ceilings : Vec Rational bank.blocks.length) (target : Rational) :=
  DependentVector (fun column : Fin selection.word.length =>
    Inside (ceilings (Selected.original selection column)) (occurrences.orders column) target)

/-- The source-fixed columns retain the same original roots, orders, coefficient weights and common window. -/
abbrev Columns (selection : Word.Selection bank) (occurrences : Occurrences selection.word)
    (weight : Weight K) (gain : Rational) (coefficientWeights : Vec Rational selection.word.length)
    (start count : Nat) :=
  DependentVector (fun column : Fin selection.word.length => Column weight
    (bank.block (Selected.original selection column)).point gain (occurrences.orders column)
    (coefficientWeights column) start count)

end Combination

set_option genInjectivity false in
/-- A source-fixed synchronized window and paid error request for an actual selected formal combination.

The selection, occurrence orders and original coefficient vector are retained
as indices. One finite maximum synchronizes all original inside thresholds;
one complete table of weighted-mode errors then supplies the common positive
endpoint tolerance. The construction neither chooses observations nor infers
physical nonvanishing from a nonzero formal coefficient.
-/
structure Combination [DecidableEq K] {polynomial : DensePolynomial K} {bank : Bank polynomial}
    (selection : Word.Selection bank) (occurrences : Occurrences selection.word)
    (weight : Weight K) (gain : Rational) (ceilings : Vec Rational bank.blocks.length)
    (coefficients : Vec K selection.word.length) (epsilon : Rational) (count : Nat) where
  /-- The fixed original gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- The actual requested combination quadrance is strictly positive. -/
  epsilonPositive : 0 < epsilon
  /-- Each selected original-block ceiling is nonnegative. -/
  ceilingsNonnegative : ∀ original, selection.labels original = true → 0 ≤ ceilings original
  /-- Each selected original-block ceiling is strictly below one. -/
  ceilingsInside : ∀ original, selection.labels original = true → ceilings original < 1
  /-- The same original coefficients' source weights, each computed once. -/
  coefficientWeights : Vec Rational selection.word.length
  /-- Every stored coefficient weight belongs to its exact original payload. -/
  coefficientWeights_eq : ∀ column, coefficientWeights column = weight.value (coefficients column)
  /-- The retained total of the actual original coefficient weights. -/
  coefficientTotal : Rational
  /-- The total is the ordered sum of the same coefficient cache. -/
  coefficientTotal_eq : coefficientTotal = sumFin (fun column => coefficientWeights column)
  /-- The fixed finite squared-triangle factor on the original selected length. -/
  sumFactor : Rational
  /-- The factor belongs to precisely the original selected coordinate count. -/
  sumFactor_eq : sumFactor = (2 : Rational) ^ selection.word.length
  /-- The original gain and retained coefficient total supply a physical model bound. -/
  amplitude : Rational
  /-- The bound uses the same fixed coefficient weights and gain. -/
  amplitude_eq : amplitude = sumFactor * gain * coefficientTotal
  /-- The retained positive shrinking width for each Gaussian mode. -/
  modeWidth : Rational
  /-- The same original sufficient width pays one quarter of the requested combination bound. -/
  modeWidth_eq : modeWidth = SmallWidth.shrinkingWidth amplitude (epsilon / 4)
  /-- The actual per-mode squared target, before choosing any reading. -/
  modeTarget : Rational
  /-- The per-mode target is the square of that same retained width. -/
  modeTarget_eq : modeTarget = modeWidth ^ 2
  /-- The same computed per-mode target is strictly positive. -/
  modeTargetPositive : 0 < modeTarget
  /-- All original inside thresholds, materialized once at their original occurrence orders. -/
  thresholds : Combination.Thresholds selection occurrences ceilings modeTarget
  /-- The thresholds retain the exact original automatic construction. -/
  thresholds_eq : thresholds = DependentVector.ofFn (fun column => Inside.prepare
    (ceilings (Selected.original selection column))
    (ceilingsNonnegative _ (selection.accepted column)) (ceilingsInside _ (selection.accepted column))
    (occurrences.orders column) modeTarget modeTargetPositive)
  /-- The once-computed common start for every selected weighted mode. -/
  start : Nat
  /-- The common start is the finite maximum of those same retained thresholds. -/
  start_eq : start = thresholds.maximum (fun _ retained => retained.index)
  /-- The retained original common-window weighted-mode error tables. -/
  columns : Combination.Columns selection occurrences weight gain coefficientWeights start count
  /-- Every original error table is prepared on the same retained common horizon. -/
  columns_eq : columns = DependentVector.ofFn (fun column => Combination.Column.prepare weight
    (bank.block (Selected.original selection column)).point gain gainNonnegative (occurrences.orders column)
    (coefficientWeights column) start count)
  /-- The once-computed total original weighted discrepancy coefficient over all common coordinates. -/
  errorTotal : Rational
  /-- The total reads only the same retained column totals and finite sum factor. -/
  errorTotal_eq : errorTotal = sumFactor * sumFin (fun column => (columns.get column).total)
  /-- The original shrinking width for the common endpoint multiplication error. -/
  errorWidth : Rational
  /-- The error width pays one quarter of the same requested combination bound. -/
  errorWidth_eq : errorWidth = SmallWidth.shrinkingWidth errorTotal (epsilon / 4)
  /-- The positive sufficient common endpoint multiplication-error tolerance. -/
  tolerance : Rational
  /-- The endpoint tolerance uses the same retained sufficient error width. -/
  tolerance_eq : tolerance = errorWidth ^ 2

constructive_injectivity Combination

namespace Combination

variable [DecidableEq K] {polynomial : DensePolynomial K} {bank : Bank polynomial}

/-- Prepare a common finite decay window and every weighted error coefficient before selecting observations. -/
@[expose] def prepare (selection : Word.Selection bank) (occurrences : Occurrences selection.word)
    (weight : Weight K) (gain : Rational) (gainNonnegative : 0 ≤ gain)
    (ceilings : Vec Rational bank.blocks.length)
    (ceilingsNonnegative : ∀ original, selection.labels original = true → 0 ≤ ceilings original)
    (ceilingsInside : ∀ original, selection.labels original = true → ceilings original < 1)
    (coefficients : Vec K selection.word.length) (epsilon : Rational) (epsilonPositive : 0 < epsilon) (count : Nat) :
    Combination selection occurrences weight gain ceilings coefficients epsilon count :=
  let coefficientWeights := vectorOfFn (fun column => weight.value (coefficients column))
  let coefficientTotal := sumFin (fun column => coefficientWeights column)
  let sumFactor := (2 : Rational) ^ selection.word.length
  let amplitude := sumFactor * gain * coefficientTotal
  let modeWidth := SmallWidth.shrinkingWidth amplitude (epsilon / 4)
  let modeTarget := modeWidth ^ 2
  have amplitudeNonnegative : 0 ≤ amplitude := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (Arithmetic.pow_nonneg_direct (by decide) _) gainNonnegative)
    (weight_sum_nonnegative _ fun column => (vectorOfFn_apply _ column).symm ▸ weight.nonnegative _)
  have modeTargetPositive := Arithmetic.pow_pos_direct
    (SmallWidth.shrinkingWidth_pos amplitudeNonnegative
      (Field.div_pos_direct epsilonPositive (by decide : (0 : Rational) < 4))) 2
  let thresholds := DependentVector.ofFn (fun column => Inside.prepare
    (ceilings (Selected.original selection column))
    (ceilingsNonnegative _ (selection.accepted column)) (ceilingsInside _ (selection.accepted column))
    (occurrences.orders column) modeTarget modeTargetPositive)
  let start := thresholds.maximum (fun _ retained => retained.index)
  let columns := DependentVector.ofFn (fun column => Column.prepare weight
    (bank.block (Selected.original selection column)).point gain gainNonnegative (occurrences.orders column)
    (coefficientWeights column) start count)
  let errorTotal := sumFactor * sumFin (fun column => (columns.get column).total)
  let errorWidth := SmallWidth.shrinkingWidth errorTotal (epsilon / 4)
  let tolerance := errorWidth ^ 2
  { gainNonnegative, epsilonPositive, ceilingsNonnegative, ceilingsInside
    coefficientWeights, coefficientWeights_eq := fun column => vectorOfFn_apply _ column
    coefficientTotal, coefficientTotal_eq := rfl, sumFactor, sumFactor_eq := rfl
    amplitude, amplitude_eq := rfl, modeWidth, modeWidth_eq := rfl, modeTarget, modeTarget_eq := rfl, modeTargetPositive
    thresholds, thresholds_eq := rfl, start, start_eq := rfl, columns, columns_eq := rfl
    errorTotal, errorTotal_eq := rfl, errorWidth, errorWidth_eq := rfl, tolerance, tolerance_eq := rfl }

variable {selection : Word.Selection bank} {occurrences : Occurrences selection.word}
variable {weight : Weight K} {gain : Rational} {ceilings : Vec Rational bank.blocks.length}
variable {coefficients : Vec K selection.word.length} {epsilon : Rational} {count : Nat}

/-- Each stored original coefficient weight is nonnegative. -/
theorem coefficientWeight_nonnegative
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    (column : Fin selection.word.length) : 0 ≤ retained.coefficientWeights column :=
  (retained.coefficientWeights_eq column).symm ▸ weight.nonnegative _

/-- The same original coefficient total is nonnegative, including an empty selection. -/
theorem coefficientTotal_nonnegative
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count) :
    0 ≤ retained.coefficientTotal := by
  rewrite [retained.coefficientTotal_eq]
  exact weight_sum_nonnegative _ retained.coefficientWeight_nonnegative

/-- The original finite sum factor is positive, including an empty selection. -/
theorem sumFactor_positive
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count) :
    0 < retained.sumFactor := by
  rewrite [retained.sumFactor_eq]
  exact Arithmetic.pow_pos_direct (by decide) _

/-- The same fixed physical coefficient bound is nonnegative. -/
theorem amplitude_nonnegative
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count) :
    0 ≤ retained.amplitude := by
  rewrite [retained.amplitude_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct retained.sumFactor_positive.le retained.gainNonnegative)
    retained.coefficientTotal_nonnegative

/-- The common original Gaussian mode target is strictly positive. -/
theorem modeTarget_positive
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count) :
    0 < retained.modeTarget := by
  rewrite [retained.modeTarget_eq, retained.modeWidth_eq]
  exact Arithmetic.pow_pos_direct (SmallWidth.shrinkingWidth_pos retained.amplitude_nonnegative
    (Field.div_pos_direct retained.epsilonPositive (by decide))) 2

/-- Every retained original inside threshold is below the same computed common start. -/
theorem threshold_le_start
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    (column : Fin selection.word.length) : (retained.thresholds.get column).index ≤ retained.start := by
  rewrite [retained.start_eq]
  exact DependentVector.get_le_maximum (fun _ retained => retained.index) retained.thresholds column

/-- The same original retained finite total of weighted discrepancies is nonnegative. -/
theorem errorTotal_nonnegative
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count) :
    0 ≤ retained.errorTotal := by
  rewrite [retained.errorTotal_eq]
  exact Arithmetic.mul_nonneg_direct retained.sumFactor_positive.le
    (weight_sum_nonnegative _ fun column =>
      (retained.columns.get column).total_nonnegative (retained.coefficientWeight_nonnegative column))

/-- The single computed endpoint tolerance is strictly positive before observing a reading. -/
theorem tolerance_positive
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count) :
    0 < retained.tolerance := by
  rewrite [retained.tolerance_eq, retained.errorWidth_eq]
  exact Arithmetic.pow_pos_direct (SmallWidth.shrinkingWidth_pos retained.errorTotal_nonnegative
    (Field.div_pos_direct retained.epsilonPositive (by decide))) 2

/-- Read the original formal combination at one coordinate of its actual common window. -/
@[expose] def value
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    (offset : Fin count) : K :=
  sumFin (fun column => coefficients column * entry (bank.block (Selected.original selection column)).point
    (occurrences.orders column) (retained.start + offset.val))

/-- Each synchronized value is the same weighted sum of original finite mode-window coordinates. -/
theorem value_eq_windows
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    (offset : Fin count) :
    retained.value offset = sumFin (fun column => coefficients column *
      window (bank.block (Selected.original selection column)).point (occurrences.orders column)
        (retained.start + count) (index retained.start offset)) := by
  exact sumFin_congr fun column => congrArg (fun value => coefficients column * value)
    (window_at (bank.block (Selected.original selection column)).point (occurrences.orders column)
      (retained.start + count) (index retained.start offset)).symm

/-- The actual Gaussian model uses the same coefficient readings, root readings and synchronized indices. -/
@[expose] def model
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) (offset : Fin count) : Canonical :=
  sumFin (fun column => reading.read (coefficients column) *
    entry (reading.read (bank.block (Selected.original selection column)).point)
      (occurrences.orders column) (retained.start + offset.val))

/-- The same reading's actual common-window discrepancy pays the original cached total. -/
theorem discrepancy_bound
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (offset : Fin count) :
    Norm.Basic.normSq (reading.read (retained.value offset) - retained.model reading offset) ≤
      reading.error * retained.errorTotal := by
  have bounded := reading.sum_discrepancy_bound
    (fun column => coefficients column * entry (bank.block (Selected.original selection column)).point
      (occurrences.orders column) (retained.start + offset.val))
    (fun column => reading.read (coefficients column) *
      entry (reading.read (bank.block (Selected.original selection column)).point)
        (occurrences.orders column) (retained.start + offset.val))
    (fun column => (retained.columns.get column).total)
    (fun column => ((retained.columns.get column).bound (coefficients column)
      (retained.coefficientWeights_eq column) reading gain_eq offset).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          ((retained.columns.get column).coefficient_le_total
            (retained.coefficientWeight_nonnegative column) offset) reading.errorNonnegative))
  exact bounded.trans_eq (by rewrite [retained.errorTotal_eq, retained.sumFactor_eq]; rfl)

/-- Each actual original Gaussian mode is small at every coordinate of the same common window. -/
theorem mode_bound
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar)
    (pointBounds : ∀ column, Norm.Basic.normSq
      (reading.read (bank.block (Selected.original selection column)).point) ≤
        ceilings (Selected.original selection column))
    (column : Fin selection.word.length) (offset : Fin count) :
    Norm.Basic.normSq (entry (reading.read (bank.block (Selected.original selection column)).point)
      (occurrences.orders column) (retained.start + offset.val)) ≤ retained.modeTarget :=
  (retained.thresholds.get column).bound _ (pointBounds column) _
    ((retained.threshold_le_start column).trans (Nat.le_add_right _ _))

/-- Actual coefficient readings and the original synchronized modes pay the retained physical bound. -/
theorem model_bound
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (pointBounds : ∀ column, Norm.Basic.normSq
      (reading.read (bank.block (Selected.original selection column)).point) ≤
        ceilings (Selected.original selection column)) (offset : Fin count) :
    Norm.Basic.normSq (retained.model reading offset) ≤ retained.amplitude * retained.modeTarget := by
  have bounded := Norm.normSq_sumFin_mul_le
    (fun column => reading.read (coefficients column))
    (fun column => entry (reading.read (bank.block (Selected.original selection column)).point)
      (occurrences.orders column) (retained.start + offset.val))
    (fun column => gain * retained.coefficientWeights column) (fun _ => retained.modeTarget)
    (fun column => (reading.gainBound (coefficients column)).trans_eq (by
      rewrite [gain_eq, retained.coefficientWeights_eq]; rfl))
    (retained.mode_bound reading pointBounds · offset)
  rewrite [sumFin_mul_right, sumFin_mul_left] at bounded
  exact bounded.trans_eq (by
    rewrite [retained.amplitude_eq, retained.coefficientTotal_eq, retained.sumFactor_eq]
    ring1)

/-- A paid same model reads the actual formal combination below its positive request on every common-window coordinate.

Both source-product discrepancy and Gaussian binomial decay are paid from the
retained pre-observation data. All columns share the same finite start and
window; formal coefficient nonvanishing is neither used nor inferred.
-/
theorem window_lt
    (retained : Combination selection occurrences weight gain ceilings coefficients epsilon count)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) (gain_eq : reading.gain = gain)
    (paid : reading.error ≤ retained.tolerance)
    (pointBounds : ∀ column, Norm.Basic.normSq
      (reading.read (bank.block (Selected.original selection column)).point) ≤
        ceilings (Selected.original selection column)) (offset : Fin count) :
    Norm.Basic.normSq (reading.read (retained.value offset)) < epsilon := by
  have quarterPositive := Field.div_pos_direct retained.epsilonPositive (by decide : (0 : Rational) < 4)
  have discrepancy := (retained.discrepancy_bound reading gain_eq offset).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct paid retained.errorTotal_nonnegative)
  have errorSmall := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt retained.errorTotal_nonnegative quarterPositive
  rewrite [← retained.errorWidth_eq, ← retained.tolerance_eq] at errorSmall
  have discrepancySmall := discrepancy.trans_lt ((Fraction.Field.mul_comm _ _).trans_lt errorSmall)
  have modelSmall := (retained.model_bound reading gain_eq pointBounds offset).trans_lt (by
    have bound := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt retained.amplitude_nonnegative quarterPositive
    rewrite [← retained.modeWidth_eq, ← retained.modeTarget_eq] at bound
    exact bound)
  have identity : reading.read (retained.value offset) =
      (reading.read (retained.value offset) - retained.model reading offset) + retained.model reading offset := by ring1
  have sumSmall := Arithmetic.add_lt_add_right_direct discrepancySmall
    (Norm.Basic.normSq (retained.model reading offset))
  have modelSumSmall := Arithmetic.add_lt_add_left_direct modelSmall (epsilon / 4)
  have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2)
    (sumSmall.trans modelSumSmall)
  rewrite [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans_lt (scaled.trans_eq (by
    calc
      _ = (epsilon / 4) * 4 := by ring1
      _ = epsilon := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide +kernel)))

end Combination
end Purelib.Polynomial.Recurrence.Mode.Reading

end
