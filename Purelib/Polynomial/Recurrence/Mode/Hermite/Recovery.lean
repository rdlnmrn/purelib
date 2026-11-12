module

public import Purelib.Polynomial.Recurrence.Mode.Hermite.Solution
public import Purelib.Polynomial.Recurrence.Mode.Hermite.Shift.Inverse
public import Purelib.LinearAlgebra.Matrix.Reading.Power
public import Purelib.Data.Rat.SmallWidth
public import Purelib.Data.List.Search
public import Purelib.Data.List.OfFn.Basic
import Purelib.Tactic.Ring

/-!
# Paid recovery from an original complete late mode window

The original full Hermite inverse and transition remain the source owners.
A source-fixed request chooses a late window and a multiplication-error
tolerance before a Gaussian reading is supplied. Only physically outside
tags are inverted; a positive physical coefficient bound is separate from
formal nonzeroness in the original coefficient ring.
-/

public section

namespace Purelib.Polynomial.Recurrence.Mode.Hermite.Recovery

open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix
open Purelib.Polynomial.Dense.Roots

variable {K : Type*} [CommRing K]
variable {blocks : List (Block K)} {differences : SquareMatrix K blocks.length}
variable {word : List (Fin blocks.length)}

/-- The original complete late row table at a retained natural starting index. -/
abbrev LateMatrix (basis : Hermite blocks differences word) (start : Nat) :=
  basis.horizonFrom start word.length

/-- The same original coefficient vector combined through its complete late row table. -/
abbrev LateValues (matrix : Rectangular K word.length word.length) (coefficients : Vec K word.length) :=
  Rectangular.apply matrix coefficients

/-- The original finite transition at the same retained root occurrences. -/
abbrev Transition (basis : Hermite blocks differences word) :=
  Shift.transition (point blocks) word basis.occurrences

/-- The same retained original full inverse, without constructing another coordinate basis. -/
abbrev Coordinates (basis : Hermite blocks differences word) := basis.inverse.inverse

set_option genInjectivity false in
/-- Source-fixed caches paying recovery of one queried physical outside coordinate.

The physical coefficient threshold and desired window bound precede every
observation. The original late table, combined vector and source-weight
tables are materialized once. Rational propagation bounds use the original
transition without computing a second formal power trajectory.
-/
structure Request (basis : Hermite blocks differences word) (weight : Weight K) (gain : Rational)
    (coefficients : Vec K word.length) (selected : Fin blocks.length → Bool)
    (floor lower target : Rational) where
  /-- The fixed reading gain is nonnegative. -/
  gainNonnegative : 0 ≤ gain
  /-- The common original outside floor is strictly above one. -/
  floorAboveOne : 1 < floor
  /-- The queried physical coefficient threshold is positive. -/
  lowerPositive : 0 < lower
  /-- The desired finite-window quadrance bound is positive. -/
  targetPositive : 0 < target
  /-- Source weights of the same original coordinate inverse. -/
  coordinateWeights : Rectangular Rational word.length word.length
  /-- The stored inverse-entry weights read the original inverse exactly. -/
  coordinateWeights_eq : ∀ row column, coordinateWeights row column = weight.value (Coordinates basis row column)
  /-- Source weights of the same original coefficient vector. -/
  coefficientWeights : Vec Rational word.length
  /-- Each stored coefficient weight reads the original coefficient exactly. -/
  coefficientWeights_eq : ∀ column, coefficientWeights column = weight.value (coefficients column)
  /-- The common original finite squared-triangle factor. -/
  factor : Rational
  /-- The factor uses the original complete word dimension. -/
  factor_eq : factor = (2 : Rational) ^ word.length
  /-- A once-computed original inverse-weight total. -/
  coordinateTotal : Rational
  /-- The total consumes the same stored inverse-entry weights. -/
  coordinateTotal_eq : coordinateTotal = sumFin (fun row => sumFin (fun column => coordinateWeights row column))
  /-- The source-fixed amplification bound from a small complete window to its recovered coordinate. -/
  amplification : Rational
  /-- Amplification uses the same finite factor, fixed gain and original inverse weights. -/
  amplification_eq : amplification = factor * factor * gain * coordinateTotal
  /-- The retained positive width selecting the partial-inverse entry bound. -/
  inverseWidth : Rational
  /-- The width pays the original requested window bound and physical coefficient threshold. -/
  inverseWidth_eq : inverseWidth = SmallWidth.shrinkingWidth (amplification * target) (lower / 8)
  /-- One original common reciprocal-mode request, prepared before root observations. -/
  inverse : InverseRequest floor word.length (inverseWidth ^ 2)
  /-- That request is the original producer on the retained source-fixed width. -/
  inverse_eq : inverse = InverseRequest.prepare floor floorAboveOne word.length
    (inverseWidth ^ 2) inverse.epsilonPositive
  /-- The selected common late starting index. -/
  start : Nat
  /-- The complete late window starts at the original inverse request's sufficient common index. -/
  start_eq : start = inverse.index
  /-- The actual original complete late mode row table, computed once. -/
  matrix : Rectangular K word.length word.length
  /-- The row table belongs to the same basis and late index. -/
  matrix_eq : matrix = LateMatrix basis start
  /-- The same actual formal combination over that retained late table. -/
  values : Vec K word.length
  /-- The combined vector consumes the retained late matrix exactly once. -/
  values_eq : values = LateValues matrix coefficients
  /-- Paid source weights for the same retained late matrix and coefficient vector. -/
  application : Reading.Application weight matrix coefficients
  /-- Paid source weights for the original full inverse acting on the retained late combination. -/
  extraction : Reading.Application weight (Coordinates basis) values
  /-- The one original transition matrix. -/
  transition : SquareMatrix K word.length
  /-- The transition retains the original roots, word and occurrence table. -/
  transition_eq : transition = Transition basis
  /-- Paid source weights for the same original transition and coefficient vector. -/
  propagation : Reading.Application weight transition coefficients
  /-- One rational error scan through the original late index, without formal trajectory evaluation. -/
  powers : Reading.Power.Parameters propagation gain start
  /-- The computed per-row discrepancy coefficients after exact full-basis recovery. -/
  errors : Vec Rational word.length
  /-- Every error coefficient consumes the original extraction and retained power-error endpoint. -/
  errors_eq : errors = extraction.outputCoefficients
    (vectorOfFn fun _ => (powers.table ⟨start, Nat.lt_succ_self start⟩).2)
  /-- The once-computed total of those same discrepancy coefficients. -/
  errorTotal : Rational
  /-- The total consumes the retained row-error vector. -/
  errorTotal_eq : errorTotal = sumFin (fun row => errors row)
  /-- The original source-fixed multiplication-error tolerance width. -/
  width : Rational
  /-- The tolerance pays the same partial inverse and original row-error total. -/
  width_eq : width = SmallWidth.shrinkingWidth (factor * inverseWidth ^ 2 * errorTotal) (lower / 8)

namespace Request

variable {basis : Hermite blocks differences word} {weight : Weight K} {gain : Rational}
variable {coefficients : Vec K word.length} {selected : Fin blocks.length → Bool} {floor lower target : Rational}

/-- The same stored coordinate-entry weights are nonnegative. -/
theorem coordinateWeight_nonnegative (request : Request basis weight gain coefficients selected floor lower target)
    (row column : Fin word.length) : 0 ≤ request.coordinateWeights row column := by
  rewrite [request.coordinateWeights_eq]
  exact weight.nonnegative _

/-- The original retained coordinate-weight total is nonnegative. -/
theorem coordinateTotal_nonnegative (request : Request basis weight gain coefficients selected floor lower target) :
    0 ≤ request.coordinateTotal := by
  rewrite [request.coordinateTotal_eq]
  exact weight_sum_nonnegative _ fun row => weight_sum_nonnegative _ (request.coordinateWeight_nonnegative row)

/-- The original finite amplification coefficient is nonnegative. -/
theorem amplification_nonnegative (request : Request basis weight gain coefficients selected floor lower target) :
    0 ≤ request.amplification := by
  rewrite [request.amplification_eq, request.factor_eq]
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
      (Arithmetic.pow_nonneg_direct (by decide) _) (Arithmetic.pow_nonneg_direct (by decide) _))
      request.gainNonnegative) request.coordinateTotal_nonnegative

/-- The retained source-fixed row discrepancy coefficients are nonnegative. -/
theorem error_nonnegative (request : Request basis weight gain coefficients selected floor lower target)
    (row : Fin word.length) : 0 ≤ request.errors row := by
  rewrite [request.errors_eq]
  exact request.extraction.outputCoefficient_nonnegative _
    (fun column => (vectorOfFn_apply _ column).symm ▸ (request.powers.table_nonnegative _).2) row

/-- The same retained row-error total is nonnegative. -/
theorem errorTotal_nonnegative (request : Request basis weight gain coefficients selected floor lower target) :
    0 ≤ request.errorTotal := by
  rewrite [request.errorTotal_eq]
  exact weight_sum_nonnegative _ request.error_nonnegative

/-- The source-fixed recovery tolerance is the square of its retained positive width. -/
@[expose] def tolerance (request : Request basis weight gain coefficients selected floor lower target) : Rational :=
  request.width ^ 2

/-- The original computed endpoint tolerance is strictly positive. -/
theorem tolerance_positive (request : Request basis weight gain coefficients selected floor lower target) :
    0 < request.tolerance := by
  apply Arithmetic.pow_pos_direct
  rewrite [request.width_eq]
  exact SmallWidth.shrinkingWidth_pos
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
      (by rewrite [request.factor_eq]; exact Arithmetic.pow_nonneg_direct (by decide) _)
      (Arithmetic.sq_nonneg_direct _)) request.errorTotal_nonnegative)
    (Field.div_pos_direct request.lowerPositive (by decide))

/-- Prepare one complete original late-window recovery request before any Gaussian observation.

All formal matrices and the combined late vector are retained once. The
three original application caches reuse the same original coefficient
weights, and extraction uses the certified combined-vector weight bounds
instead of reading that vector's source weights again.
-/
@[expose] def prepare (basis : Hermite blocks differences word) (weight : Weight K)
    (gain : Rational) (gainNonnegative : 0 ≤ gain) (coefficients : Vec K word.length)
    (selected : Fin blocks.length → Bool) (floor : Rational) (floorAboveOne : 1 < floor)
    (lower : Rational) (lowerPositive : 0 < lower) (target : Rational) (targetPositive : 0 < target) :
    Request basis weight gain coefficients selected floor lower target := by
  let coordinateWeights := Rectangular.ofFn fun row column => weight.value (Coordinates basis row column)
  have coordinateBound : ∀ row column, weight.value (Coordinates basis row column) ≤
      coordinateWeights row column := fun row column =>
        (Rectangular.ofFn_apply (fun row column => weight.value (Coordinates basis row column)) row column).symm.le
  let coefficientWeights := vectorOfFn fun column => weight.value (coefficients column)
  have coefficientBound : ∀ column, weight.value (coefficients column) ≤ coefficientWeights column :=
    fun column => (vectorOfFn_apply (fun column => weight.value (coefficients column)) column).symm.le
  let factor := (2 : Rational) ^ word.length
  let coordinateTotal := sumFin fun row => sumFin fun column => coordinateWeights row column
  let amplification := factor * factor * gain * coordinateTotal
  have coordinateNN : 0 ≤ coordinateTotal := weight_sum_nonnegative _ fun row =>
    weight_sum_nonnegative _ fun column => (weight.nonnegative _).trans (coordinateBound row column)
  have amplificationNN : 0 ≤ amplification := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
      (Arithmetic.pow_nonneg_direct (by decide) _) (Arithmetic.pow_nonneg_direct (by decide) _))
      gainNonnegative) coordinateNN
  have eighthPositive : 0 < lower / 8 := Field.div_pos_direct lowerPositive (by decide)
  let inverseWidth := SmallWidth.shrinkingWidth (amplification * target) (lower / 8)
  have inversePositive : 0 < inverseWidth ^ 2 := Arithmetic.pow_pos_direct
    (SmallWidth.shrinkingWidth_pos (Arithmetic.mul_nonneg_direct amplificationNN targetPositive.le)
      eighthPositive) 2
  let inverse := InverseRequest.prepare floor floorAboveOne word.length (inverseWidth ^ 2) inversePositive
  let start := inverse.index
  let matrix := LateMatrix basis start
  let values := LateValues matrix coefficients
  let matrixWeights := Rectangular.ofFn fun row column => weight.value (matrix row column)
  let application := Reading.Application.prepare weight matrix coefficients matrixWeights
    (fun row column => (Rectangular.ofFn_apply (fun row column => weight.value (matrix row column))
      row column).symm.le) coefficientWeights coefficientBound
  let valueWeights := vectorOfFn fun row => weight.multiplier * application.coefficients row
  let extraction := Reading.Application.prepare weight (Coordinates basis) values coordinateWeights coordinateBound
    valueWeights (fun row => (application.weight_bound row).trans_eq
      (vectorOfFn_apply (fun row => weight.multiplier * application.coefficients row) row).symm)
  let transition := Transition basis
  let transitionWeights := Rectangular.ofFn fun row column => weight.value (transition row column)
  let propagation := Reading.Application.prepare weight transition coefficients transitionWeights
    (fun row column => (Rectangular.ofFn_apply (fun row column => weight.value (transition row column))
      row column).symm.le) coefficientWeights coefficientBound
  let powers := Reading.Power.Parameters.prepare propagation gain gainNonnegative start
  let errors := extraction.outputCoefficients
    (vectorOfFn fun _ => (powers.table ⟨start, Nat.lt_succ_self start⟩).2)
  let errorTotal := sumFin fun row => errors row
  let width := SmallWidth.shrinkingWidth (factor * inverseWidth ^ 2 * errorTotal) (lower / 8)
  exact
    { gainNonnegative, floorAboveOne, lowerPositive, targetPositive
      coordinateWeights, coordinateWeights_eq := fun row column =>
        Rectangular.ofFn_apply (fun row column => weight.value (Coordinates basis row column)) row column
      coefficientWeights, coefficientWeights_eq := fun column =>
        vectorOfFn_apply (fun column => weight.value (coefficients column)) column
      factor, factor_eq := rfl, coordinateTotal, coordinateTotal_eq := rfl
      amplification, amplification_eq := rfl, inverseWidth, inverseWidth_eq := rfl
      inverse, inverse_eq := rfl, start, start_eq := rfl, matrix, matrix_eq := rfl
      values, values_eq := rfl, application, extraction, transition, transition_eq := rfl
      propagation, powers, errors, errors_eq := rfl, errorTotal, errorTotal_eq := rfl, width, width_eq := rfl }

/-- The retained late combination is recovered by the same original transition power.

This identity is entirely in the original ring. It requires no root
inverse, physical reading, lower coefficient bound or field assumption.
-/
theorem extraction_eq (request : Request basis weight gain coefficients selected floor lower target) :
    Rectangular.apply (Coordinates basis) request.values =
      Reading.Power.trajectory request.transition coefficients request.start := by
  rewrite [request.values_eq, request.matrix_eq, request.transition_eq]
  exact basis.coordinates_horizonFrom request.start coefficients

/-- The original partial inverse entry bound pays a small observed late window with a strict margin. -/
theorem inverse_margin (request : Request basis weight gain coefficients selected floor lower target) :
    request.inverseWidth ^ 2 * request.amplification * target < lower / 8 := by
  have sufficient := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt
    (Arithmetic.mul_nonneg_direct request.amplification_nonnegative request.targetPositive.le)
    (Field.div_pos_direct request.lowerPositive (by decide : (0 : Rational) < 8))
  rewrite [← request.inverseWidth_eq] at sufficient
  exact (show request.inverseWidth ^ 2 * request.amplification * target =
    request.amplification * target * request.inverseWidth ^ 2 by ring1).trans_lt sufficient

/-- The computed endpoint multiplication tolerance pays all retained recovery row errors. -/
theorem error_margin (request : Request basis weight gain coefficients selected floor lower target)
    (error : Rational) (paid : error ≤ request.tolerance) :
    error * (request.factor * request.inverseWidth ^ 2 * request.errorTotal) < lower / 8 := by
  have coefficientNN : 0 ≤ request.factor * request.inverseWidth ^ 2 * request.errorTotal :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
      (by rewrite [request.factor_eq]; exact Arithmetic.pow_nonneg_direct (by decide) _)
      (Arithmetic.sq_nonneg_direct _)) request.errorTotal_nonnegative
  have sufficient := SmallWidth.coefficient_mul_shrinkingWidth_sq_lt coefficientNN
    (Field.div_pos_direct request.lowerPositive (by decide : (0 : Rational) < 8))
  rewrite [← request.width_eq] at sufficient
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct paid coefficientNN).trans_lt
    ((mul_comm request.tolerance _).trans_lt sufficient)

/-- The Gaussian product of the same original inverse and late-vector readings pays exact formal recovery.

The physical transition and coefficient vector are pointwise readbacks of
the retained originals. The original algebraic identity transports the
power bound; it does not assert multiplicativity of the Gaussian reading.
-/
theorem output_bound (request : Request basis weight gain coefficients selected floor lower target)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) (gainEq : reading.gain = gain)
    (observedTransition : SquareMatrix Canonical word.length)
    (transitionEq : ∀ row column, observedTransition row column = reading.read (request.transition row column))
    (observedCoefficients : Vec Canonical word.length)
    (coefficientEq : ∀ column, observedCoefficients column = reading.read (coefficients column))
    (row : Fin word.length) :
    Norm.Basic.normSq (sumFin (fun column => reading.read (Coordinates basis row column) *
      reading.read (request.values column)) -
        Reading.Power.trajectory observedTransition observedCoefficients request.start row) ≤
      reading.error * request.errors row := by
  rewrite [request.errors_eq]
  apply request.extraction.output_bound reading _ _ _ row
  intro index
  rewrite [vectorOfFn_apply]
  exact request.powers.bound_of_trajectories reading gainEq observedTransition transitionEq
    observedCoefficients coefficientEq ⟨request.start, Nat.lt_succ_self request.start⟩
    (Rectangular.apply (Coordinates basis) request.values) request.extraction_eq
    (Reading.Power.trajectory observedTransition observedCoefficients request.start) rfl index

end Request

variable {basis : Hermite blocks differences word} {weight : Weight K} {gain : Rational}
variable {coefficients : Vec K word.length} {selected : Fin blocks.length → Bool} {floor lower target : Rational}

set_option genInjectivity false in
/-- One actual Gaussian observation of the same requested original complete late window.

The root readbacks, coordinate matrix, coefficient vector and late values
are materialized once. Reciprocals are computed only after the original
outside-tag branch succeeds. The retained recovered vector uses the same
partial inverse and the same observed late window.
-/
structure Observation (request : Request basis weight gain coefficients selected floor lower target)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) where
  /-- Original root readings, once per original block. -/
  roots : Vec Canonical blocks.length
  /-- Every root cache reads the same original block point. -/
  roots_eq : ∀ tag, roots tag = reading.read (point blocks tag)
  /-- Actual Gaussian reciprocals only at selected original outside tags. -/
  reciprocals : Vec Canonical blocks.length
  /-- Unselected tags store zero without computing their reciprocal. -/
  reciprocals_eq : ∀ tag, reciprocals tag = if selected tag = true then Field.inv (roots tag) else 0
  /-- The original transition interpreted at the same cached physical roots. -/
  transition : SquareMatrix Canonical word.length
  /-- The physical transition uses the same original word and occurrence cache. -/
  transition_eq : transition = Shift.transition (fun tag => roots tag) word basis.occurrences
  /-- The same original full inverse read once per entry. -/
  coordinates : SquareMatrix Canonical word.length
  /-- Every observed inverse entry reads the retained original full inverse. -/
  coordinates_eq : ∀ row column, coordinates row column = reading.read (Coordinates basis row column)
  /-- The same original coefficient vector read once per entry. -/
  coefficientValues : Vec Canonical word.length
  /-- Every physical coefficient reads the same original formal coefficient. -/
  coefficientValues_eq : ∀ column, coefficientValues column = reading.read (coefficients column)
  /-- The actual original late combination read once per entry. -/
  values : Vec Canonical word.length
  /-- Every observed late entry reads the same retained original combination. -/
  values_eq : ∀ row, values row = reading.read (request.values row)
  /-- The physically outside-only partial inverse at the same late index. -/
  inverse : SquareMatrix Canonical word.length
  /-- Every inverse coefficient uses the same original tags, orders and retained outside reciprocals. -/
  inverse_eq : inverse = Shift.inversePower (fun tag => reciprocals tag) selected word basis.occurrences request.start
  /-- The observed original inverse acting on the actual observed late window. -/
  extracted : Vec Canonical word.length
  /-- The first observed action consumes the retained coordinate and late-value caches. -/
  extracted_eq : extracted = Rectangular.apply coordinates values
  /-- The same physically projected recovered coefficient vector. -/
  recovered : Vec Canonical word.length
  /-- The second observed action consumes the retained partial inverse and extracted vector. -/
  recovered_eq : recovered = Rectangular.apply inverse extracted
  /-- The original finite search over this same observed late window, computed once. -/
  search : Option (Fin word.length)
  /-- The cached search retains the original increasing window-index order and requested bound. -/
  search_eq : search = (List.ofFn fun index : Fin word.length => index).find?
    (fun index => decide (target < Norm.Basic.normSq (values index)))

namespace Observation

variable {request : Request basis weight gain coefficients selected floor lower target}
variable {scalar : Canonical → K} {reading : GaussianReading weight scalar}

/-- Observe each original source cache once and invert only the selected physical root tags. -/
@[expose] def prepare (request : Request basis weight gain coefficients selected floor lower target)
    {scalar : Canonical → K} (reading : GaussianReading weight scalar) : Observation request reading :=
  let roots := vectorOfFn fun tag => reading.read (point blocks tag)
  let reciprocals := vectorOfFn fun tag => if selected tag = true then Field.inv (roots tag) else 0
  let transition := Shift.transition (fun tag => roots tag) word basis.occurrences
  let coordinates := matrixOfFn fun row column => reading.read (Coordinates basis row column)
  let observedCoefficients := vectorOfFn fun column => reading.read (coefficients column)
  let values := vectorOfFn fun row => reading.read (request.values row)
  let inverse := Shift.inversePower (fun tag => reciprocals tag) selected word basis.occurrences request.start
  let extracted := Rectangular.apply coordinates values
  let recovered := Rectangular.apply inverse extracted
  let search := (List.ofFn fun index : Fin word.length => index).find?
    (fun index => decide (target < Norm.Basic.normSq (values index)))
  { roots, roots_eq := fun tag => vectorOfFn_apply _ tag
    reciprocals, reciprocals_eq := fun tag => vectorOfFn_apply _ tag
    transition, transition_eq := rfl, coordinates, coordinates_eq := fun row column => matrixOfFn_apply _ row column
    coefficientValues := observedCoefficients, coefficientValues_eq := fun column => vectorOfFn_apply _ column
    values, values_eq := fun row => vectorOfFn_apply _ row, inverse, inverse_eq := rfl
    extracted, extracted_eq := rfl, recovered, recovered_eq := rfl, search, search_eq := rfl }

/-- The physical transition is an entrywise reading of the same original transition without product assumptions. -/
theorem transition_readback (observed : Observation request reading) (row column : Fin word.length) :
    observed.transition row column = reading.read (request.transition row column) := by
  rewrite [observed.transition_eq, request.transition_eq]
  exact (Shift.map_transition_at reading.read reading.mapZero reading.mapOne (point blocks)
    (fun tag => observed.roots tag) (fun tag => (observed.roots_eq tag).symm)
    word basis.occurrences row column).symm

/-- The observed first action pays the same retained original row discrepancy coefficients. -/
theorem extraction_bound (observed : Observation request reading) (gainEq : reading.gain = gain)
    (row : Fin word.length) :
    Norm.Basic.normSq (observed.extracted row -
      Reading.Power.trajectory observed.transition observed.coefficientValues request.start row) ≤
        reading.error * request.errors row := by
  have readback : observed.extracted row = sumFin (fun column => reading.read (Coordinates basis row column) *
      reading.read (request.values column)) := by
    rewrite [observed.extracted_eq, Rectangular.apply_at]
    apply sumFin_congr
    intro column
    rewrite [observed.coordinates_eq, observed.values_eq]
    rfl
  rewrite [readback]
  exact request.output_bound reading gainEq observed.transition observed.transition_readback
    observed.coefficientValues observed.coefficientValues_eq row

/-- Every selected physical root is nonzero by its paid original outside floor. -/
theorem root_nonzero (observed : Observation request reading)
    (outside : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (observed.roots tag))
    (tag : Fin blocks.length) (chosen : selected tag = true) : observed.roots tag ≠ 0 := by
  intro zero
  have positive := ((by decide : (0 : Rational) < 1).trans request.floorAboveOne).trans_le (outside tag chosen)
  rewrite [zero, Norm.Basic.normSq_zero] at positive
  exact (lt_irrefl (0 : Rational)) positive

/-- The actual partial inverse recovers precisely the same original outside-coordinate projector. -/
theorem inverse_apply (observed : Observation request reading)
    (outside : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (observed.roots tag)) :
    Rectangular.apply observed.inverse
      (Reading.Power.trajectory observed.transition observed.coefficientValues request.start) =
        Rectangular.apply (Shift.projection selected word) observed.coefficientValues := by
  rewrite [observed.inverse_eq, observed.transition_eq]
  apply Shift.inversePower_apply
  intro column chosen
  rewrite [observed.reciprocals_eq, if_pos chosen]
  rewrite [← Field.inv_eq]
  exact Canonical.inv_mul_cancel _ (observed.root_nonzero outside _ chosen)

/-- Every physically outside-only inverse entry meets the original request's computed common bound. -/
theorem inverse_bound (observed : Observation request reading)
    (outside : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (observed.roots tag))
    (row column : Fin word.length) : Norm.Basic.normSq (observed.inverse row column) ≤ request.inverseWidth ^ 2 := by
  rewrite [observed.inverse_eq]
  exact Shift.inversePower_bound word request.inverse (fun tag => observed.roots tag)
    (fun tag => observed.reciprocals tag) selected basis.occurrences
    (fun tag chosen => (observed.reciprocals_eq tag).trans (if_pos chosen)) outside request.start
    request.start_eq.symm.le row column

/-- The actual recovered coefficient differs from its physical outside projection by the paid row errors. -/
theorem recovery_bound (observed : Observation request reading) (gainEq : reading.gain = gain)
    (outside : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (observed.roots tag))
    (row : Fin word.length) :
    Norm.Basic.normSq (observed.recovered row -
      Rectangular.apply (Shift.projection selected word) observed.coefficientValues row) ≤
        reading.error * (request.factor * request.inverseWidth ^ 2 * request.errorTotal) := by
  let model := Reading.Power.trajectory observed.transition observed.coefficientValues request.start
  have identity : observed.recovered row -
      Rectangular.apply (Shift.projection selected word) observed.coefficientValues row =
        sumFin (fun column => observed.inverse row column * (observed.extracted column - model column)) := by
    rewrite [observed.recovered_eq, ← observed.inverse_apply outside, Rectangular.apply_at, Rectangular.apply_at,
      ← sumFin_sub]
    apply sumFin_congr
    intro column
    ring1
  rewrite [identity]
  have bounded := Norm.normSq_sumFin_mul_le (fun column => observed.inverse row column)
    (fun column => observed.extracted column - model column) (fun _ => request.inverseWidth ^ 2)
    (fun column => reading.error * request.errors column)
    (observed.inverse_bound outside row) (observed.extraction_bound gainEq)
  apply bounded.trans_eq
  rewrite [← request.factor_eq]
  calc
    _ = request.factor * sumFin (fun column =>
        (request.inverseWidth ^ 2 * reading.error) * request.errors column) :=
      congrArg (request.factor * ·) (sumFin_congr fun _ => by ring1)
    _ = _ := by rewrite [sumFin_mul_left, request.errorTotal_eq]; ring1

/-- A small actual complete window bounds the same physically recovered vector with its source-fixed amplification. -/
theorem small_window_bound (observed : Observation request reading) (gainEq : reading.gain = gain)
    (outside : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (observed.roots tag))
    (small : ∀ column, Norm.Basic.normSq (observed.values column) ≤ target) (row : Fin word.length) :
    Norm.Basic.normSq (observed.recovered row) ≤ request.inverseWidth ^ 2 * request.amplification * target := by
  have coordinatesBound (index column : Fin word.length) : Norm.Basic.normSq (observed.coordinates index column) ≤
      gain * request.coordinateWeights index column := by
    rewrite [observed.coordinates_eq, request.coordinateWeights_eq, ← gainEq]
    exact reading.gainBound _
  have extractedBound (index : Fin word.length) : Norm.Basic.normSq (observed.extracted index) ≤
      request.factor * sumFin (fun column => gain * request.coordinateWeights index column * target) := by
    rewrite [observed.extracted_eq, Rectangular.apply_at, request.factor_eq]
    exact Norm.normSq_sumFin_mul_le _ _ _ _ (coordinatesBound index) small
  rewrite [observed.recovered_eq, Rectangular.apply_at]
  have bounded := Norm.normSq_sumFin_mul_le (fun index => observed.inverse row index)
    (fun index => observed.extracted index) (fun _ => request.inverseWidth ^ 2)
    (fun index => request.factor * sumFin (fun column => gain * request.coordinateWeights index column * target))
    (observed.inverse_bound outside row) extractedBound
  apply bounded.trans_eq
  rewrite [← request.factor_eq]
  have rowSum (index : Fin word.length) :
      sumFin (fun column => gain * request.coordinateWeights index column * target) =
        (gain * target) * sumFin (fun column => request.coordinateWeights index column) := by
    calc
      _ = sumFin (fun column => (gain * target) * request.coordinateWeights index column) :=
        sumFin_congr fun _ => by ring1
      _ = _ := sumFin_mul_left _ _
  calc
    _ = request.factor * sumFin (fun index =>
        (request.inverseWidth ^ 2 * request.factor * gain * target) *
          sumFin (fun column => request.coordinateWeights index column)) := by
      apply congrArg (request.factor * ·)
      apply sumFin_congr
      intro index
      rewrite [rowSum]
      ring1
    _ = _ := by
      rewrite [sumFin_mul_left, ← request.coordinateTotal_eq, request.amplification_eq]
      ring1

/-- If the same complete late window is small, every queried outside coefficient falls below its physical threshold.

The result concerns the actual Gaussian coefficient value. It does not
identify a formally zero coefficient or assert a faithful reading of the
original coefficient ring.
-/
theorem coefficient_small (observed : Observation request reading) (gainEq : reading.gain = gain)
    (outside : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (observed.roots tag))
    (paid : reading.error ≤ request.tolerance)
    (small : ∀ column, Norm.Basic.normSq (observed.values column) ≤ target)
    (column : Fin word.length) (chosen : selected (word[column.val]'column.isLt) = true) :
    Norm.Basic.normSq (observed.coefficientValues column) < lower := by
  have first := (observed.small_window_bound gainEq outside small column).trans_lt request.inverse_margin
  have second := (observed.recovery_bound gainEq outside column).trans_lt (request.error_margin reading.error paid)
  rewrite [Shift.projection_apply, if_pos chosen] at second
  have identity : observed.coefficientValues column = observed.recovered column -
      (observed.recovered column - observed.coefficientValues column) := by ring1
  have estimate := Norm.Bounds.normSq_sub_le_two (observed.recovered column)
    (observed.recovered column - observed.coefficientValues column)
  have smallSum := Arithmetic.add_lt_add_direct first second
  have strict := Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rational) < 2) smallSum
  have halfLess : lower / 2 < lower := by
    have halfPositive := Field.div_pos_direct request.lowerPositive (by decide : (0 : Rational) < 2)
    have moved := Arithmetic.add_lt_add_left_direct halfPositive (lower / 2)
    exact (show lower / 2 = lower / 2 + 0 by ring1).trans_lt
      (moved.trans_eq (show lower / 2 + lower / 2 = lower from by
        rewrite [Fraction.Field.div_eq_mul_inv_direct]
        calc
          _ = lower * ((2 : Rational)⁻¹ + (2 : Rational)⁻¹) := by ring1
          _ = lower * 1 := congrArg (lower * ·) (by decide)
          _ = lower := mul_one _))
  have desired : 2 * (lower / 8 + lower / 8) < lower :=
    (show 2 * (lower / 8 + lower / 8) = lower / 2 from by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = lower * (2 * ((8 : Rational)⁻¹ + (8 : Rational)⁻¹)) := by ring1
        _ = _ := congrArg (lower * ·) (by decide)).trans_lt halfLess
  rewrite [identity]
  exact estimate.trans_lt (strict.trans desired)

set_option genInjectivity false in
/-- The actual finite-window search either exhibits a large reading or retains the physical threshold failure.

Inconclusivity concerns the same observed coefficient only. It establishes
neither formal coefficient vanishing nor impossibility of another large
reading or of a different finite request.
-/
inductive Outcome (observed : Observation request reading) (column : Fin word.length) where
  /-- A retained original late-window coordinate exceeds the requested physical bound. -/
  | obstruction (index : Fin word.length) (exceeds : target < Norm.Basic.normSq (observed.values index))
  /-- This complete observed window is small and the queried physical coefficient falls below its threshold. -/
  | inconclusive (small : ∀ index, Norm.Basic.normSq (observed.values index) ≤ target)
      (coefficientSmall : Norm.Basic.normSq (observed.coefficientValues column) < lower)

/-- Search the same retained complete late window and certify the exact obstruction or inconclusive outcome.

Only the original finite list search is used. Rejection supplies a bound
at every retained window index; the paid recovery theorem then supplies
the physical coefficient threshold failure.
-/
@[expose] def check (observed : Observation request reading) (gainEq : reading.gain = gain)
    (outside : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (observed.roots tag))
    (paid : reading.error ≤ request.tolerance) (column : Fin word.length)
    (chosen : selected (word[column.val]'column.isLt) = true) : Outcome observed column := by
  let indices := List.ofFn fun index : Fin word.length => index
  let accepts := fun index : Fin word.length => decide (target < Norm.Basic.normSq (observed.values index))
  match result : observed.search with
  | some index =>
      have found : indices.find? accepts = some index := observed.search_eq.symm.trans result
      have accepted : accepts index = true := Search.find?_eq_some_accepts_certificate found
      exact .obstruction index (of_decide_eq_true accepted)
  | none =>
      have found : indices.find? accepts = none := observed.search_eq.symm.trans result
      have small (index : Fin word.length) : Norm.Basic.normSq (observed.values index) ≤ target := by
        have rejected := Search.find?_eq_none.mp found index
          (OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩)
        have notLarge : ¬ target < Norm.Basic.normSq (observed.values index) := of_decide_eq_false rejected
        exact le_of_not_gt notLarge
      exact .inconclusive small (observed.coefficient_small gainEq outside paid small column chosen)

/-- A genuine positive same-reading coefficient bound forces an actual large coordinate in the requested late window.

The evidence concerns the physical Gaussian reading of the queried
coefficient. Formal nonzeroness is deliberately insufficient. The returned
bounded index belongs to the same already observed complete late window.
-/
@[expose] def obstruction (observed : Observation request reading) (gainEq : reading.gain = gain)
    (outside : ∀ tag, selected tag = true → floor ≤ Norm.Basic.normSq (observed.roots tag))
    (paid : reading.error ≤ request.tolerance) (column : Fin word.length)
    (chosen : selected (word[column.val]'column.isLt) = true)
    (coefficientBound : lower ≤ Norm.Basic.normSq (observed.coefficientValues column)) :
    {index : Fin word.length // target < Norm.Basic.normSq (observed.values index)} :=
  match observed.check gainEq outside paid column chosen with
  | .obstruction index exceeds => ⟨index, exceeds⟩
  | .inconclusive _ small => False.elim ((not_lt_of_ge coefficientBound) small)

end Observation

end Purelib.Polynomial.Recurrence.Mode.Hermite.Recovery

end
