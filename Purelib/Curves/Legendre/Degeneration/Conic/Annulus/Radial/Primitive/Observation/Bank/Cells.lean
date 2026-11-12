module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry.Accuracy
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Taylor.Observation.Bounds
public import Purelib.Integration.Polynomial.Gaussian.Cell.Taylor
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Sampling
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Factorization
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Transport
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Actual shared-bank arithmetic certificates against the original chart cells

The bank, layer and later cofactor observations are already retained inputs.
Exact request/time transports reuse its adjacent complete primitive entries.
Each node constructs one genuine independent spatial derivative cache and
one actual derivative arithmetic Reading. The existing retained-reading
Taylor constructor then consumes those caches and both bank observations.

The resulting certificate is compared to the same original refined scalar
cell, then to the literal unchanged old cell. Every local error is derived
from original request payments and uniform bounds. No sheet continuation,
return-sheet, geometric integral or parameter-derivative law is asserted.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Layer Piece)
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Integration
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive}
variable {data : Waist.Differential.Bounds.Data site parameter specification.differential}
variable {initialAccuracy : AccuracyRequest} {initial : Piece data actual initialAccuracy} {depth : Nat}
variable {layer : Layer initial depth} {initialPositive : 0 < initial.span.width}
variable {samples : Layer.RefinedSamples layer initialPositive}
variable {upper : Transport.Reading actual initial.span.upper
  (initial.within _ ⟨initial.span.valid, Fraction.Order.Basic.le_refl _⟩)}

/-- Each original node's residual request is exactly the bank request, by their independently retained tolerances. -/
theorem nodeRequest_eq (layer : Layer initial depth) (initialPositive : 0 < initial.span.width)
    (index : Fin layer.pieces.length) :
    (layer.node index).cell.fourthRequest (layer.node_width_positive initialPositive index) =
      request layer initialPositive :=
  AccuracyRequest.eq_of_tolerance_eq
    (((layer.node index).cell.fourthRequest_tolerance
      (layer.node_width_positive initialPositive index)).trans (request_tolerance layer initialPositive index).symm)

/-- Read the identical stored later cofactor sample through its exact common-request index. -/
@[expose] def sourceSample (_bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :
    CertifiedSquareRoot.Sampling.ResidualObservation (layer.node index).source.lift.unitRoot
      (request layer initialPositive) :=
  CertifiedSquareRoot.Sampling.ResidualObservation.castAccuracy (nodeRequest_eq layer initialPositive index)
    (samples.get index).val.sample

/-- Exact request alignment preserves the actual original later root witness at that node. -/
theorem sourceSample_reading (bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :
    (bank.sourceSample index).reading = (samples.get index).val.sample.reading :=
  CertifiedSquareRoot.Sampling.ResidualObservation.castAccuracy_reading
    (nodeRequest_eq layer initialPositive index) (samples.get index).val.sample

/-- The aligned source sample keeps the original requestAfter stage and actual selected comparison index. -/
theorem sourceSample_index_ge (bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :
    (layer.node index).cell.sample.comparison.leftIndex ≤ (bank.sourceSample index).comparison.leftIndex :=
  CertifiedSquareRoot.Sampling.ResidualObservation.castAccuracy_index_ge
    (nodeRequest_eq layer initialPositive index) (samples.get index).val.sample (samples.get index).property

/-- Read the whole stored source Entry after exact root-request alignment without a second arithmetic comparison. -/
@[expose] def sourceEntry (bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :
    Entry primitive (layer.node index).source initial.cell.regular (bank.sourceSample index)
      (request layer initialPositive) :=
  (bank.nodes.get index).castRootAccuracy (nodeRequest_eq layer initialPositive index)

/-- The aligned source Entry retains the identical bank vertex witness. -/
theorem sourceEntry_value (bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :
    (bank.sourceEntry index).value = (bank.nodes.get index).value :=
  Entry.castRootAccuracy_value (nodeRequest_eq layer initialPositive index) (bank.nodes.get index)

/-- The actual original span's upper endpoint supplies its equal lower-plus-width chart index. -/
theorem target_inside (_bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :
    FixedRootBoxPath.Inside ((layer.node index).span.lower + (layer.node index).span.width) := by
  have equal : (layer.node index).span.upper =
      (layer.node index).span.lower + (layer.node index).span.width := by
    change (layer.node index).span.upper =
      (layer.node index).span.lower + ((layer.node index).span.upper - (layer.node index).span.lower)
    ring1
  exact equal ▸ (layer.node index).within _
    ⟨(layer.node index).span.valid, Fraction.Order.Basic.le_refl _⟩

/-- A target view retains the original Reading, cofactor sample and complete arithmetic Entry. -/
@[expose] def Target (bank : Bank primitive samples upper) (index : Fin layer.pieces.length) :=
  Σ reading : Transport.Reading actual ((layer.node index).span.lower + (layer.node index).span.width)
      (bank.target_inside index),
    Σ sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot (request layer initialPositive),
      Entry primitive reading initial.cell.regular sample (request layer initialPositive)

/-- Select the identical next stored Entry or terminal Entry and transport its exact chart/request indices.

The actual interval Chain supplies the time identity. Each branch retains
its original complete Reading, root observation and arithmetic comparison;
there is no query, root sample or evaluator observation in this selector.
-/
def target (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Piece.chartIntervals layer.pieces)) (index : Fin layer.pieces.length) :
    Target bank index := by
  if nextBound : index.val + 1 < layer.pieces.length then
    let next : Fin layer.pieces.length := ⟨index.val + 1, nextBound⟩
    have equal : (layer.node next).span.lower =
        (layer.node index).span.lower + (layer.node index).span.width := by
      calc
        _ = (layer.node index).span.upper := (layer.seam chain index.val index.isLt nextBound).symm
        _ = _ := by change _ = _ + (_ - _); ring1
    let reading := (layer.node next).source.castTime (lastInside := bank.target_inside index) equal
    let sample := (layer.node next).source.castTimeSample
      (lastInside := bank.target_inside index) equal (bank.sourceSample next)
    let entry := (bank.sourceEntry next).castTime (otherInside := bank.target_inside index) equal
    exact ⟨reading, sample, entry⟩
  else
    have finish : index.val + 1 = layer.pieces.length :=
      Nat.le_antisymm (Nat.succ_le_of_lt index.isLt) (Nat.le_of_not_gt nextBound)
    have equal : initial.span.upper =
        (layer.node index).span.lower + (layer.node index).span.width := by
      calc
        _ = (layer.node index).span.upper := (layer.finish_eq chain index.val index.isLt finish).symm
        _ = _ := by change _ = _ + (_ - _); ring1
    let reading := upper.castTime (lastInside := bank.target_inside index) equal
    let sample := upper.castTimeSample (lastInside := bank.target_inside index) equal bank.terminal.sample
    let entry := bank.terminal.entry.castTime (otherInside := bank.target_inside index) equal
    exact ⟨reading, sample, entry⟩

/-- Both target branches preserve the identical actual selected endpoint witness in the bank's successor vertex. -/
theorem target_value (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Piece.chartIntervals layer.pieces)) (index : Fin layer.pieces.length) :
    (bank.target chain index).2.2.value = bank.vertex index.succ := by
  by_cases nextBound : index.val + 1 < layer.pieces.length
  · rewrite [target, dif_pos nextBound]
    exact (Entry.castTime_value _ (bank.sourceEntry ⟨index.val + 1, nextBound⟩)).trans
      ((bank.sourceEntry_value ⟨index.val + 1, nextBound⟩).trans
        (bank.successor_value index nextBound).symm)
  · rewrite [target, dif_neg nextBound]
    have finish : index.val + 1 = layer.pieces.length :=
      Nat.le_antisymm (Nat.succ_le_of_lt index.isLt) (Nat.le_of_not_gt nextBound)
    have lastIndex : index.succ = Fin.last layer.pieces.length := Fin.ext finish
    exact (Entry.castTime_value _ bank.terminal.entry).trans
      (by rewrite [lastIndex, bank.vertex_finish]; rfl)

variable (specification)

/-- One actual node cache keeps its genuine derivative and observed expansion tied to the exact shared bank entries. -/
@[expose] def Cell (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Piece.chartIntervals layer.pieces)) (index : Fin layer.pieces.length) :=
  let source := bank.sourceEntry index
  let target := bank.target chain index
  Σ values : DerivativeValues specification source.endpoint,
    { expansion : Taylor.Observation.Expansion primitive (layer.node index).source target.1 initial.cell.regular
        (request layer initialPositive) (bank.sourceSample index) target.2.1 source.endpoint target.2.2.endpoint
        specification values //
      expansion.sourceValue = source.selected ∧ expansion.targetValue = target.2.2.selected ∧
        expansion.derivative = derivativeRequest specification source.endpoint values
          (bank.sourceSample index) (request layer initialPositive) }

variable {specification}

namespace Cell

open Purelib.Data.Rat.Fraction.Order

variable (specification)

/-- Construct one independent derivative and observation, then assemble the retained endpoint Readings. -/
def build (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Piece.chartIntervals layer.pieces)) (index : Fin layer.pieces.length) :
    Cell specification bank chain index := by
  let source := bank.sourceEntry index
  let target := bank.target chain index
  let values := DerivativeValues.build specification source.endpoint
  let scalar := Taylor.build primitive (layer.node index).source target.1 initial.cell.regular
    (request layer initialPositive) (bank.sourceSample index) target.2.1
    (request_tolerance layer initialPositive index)
  let derivative := derivativeRequest specification source.endpoint values
    (bank.sourceSample index) (request layer initialPositive)
  let expansion := Taylor.Observation.ofReadings primitive (layer.node index).source target.1 initial.cell.regular
    (request layer initialPositive) (bank.sourceSample index) target.2.1 source.endpoint target.2.2.endpoint
    specification values scalar rfl source.selected target.2.2.selected derivative
  exact ⟨values, ⟨expansion,
    Taylor.Observation.ofReadings_sourceValue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Taylor.Observation.ofReadings_targetValue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Taylor.Observation.ofReadings_derivative _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩⟩

variable {specification}
variable {bank : Bank primitive samples upper}
variable {chain : Partition.Interval.Chain initial.span.lower initial.span.upper
  (Piece.chartIntervals layer.pieces)} {index : Fin layer.pieces.length}

/-- Read the one retained genuine spatial-derivative cache on the bank's original source primitive evaluator. -/
@[expose] def values (cache : Cell specification bank chain index) := cache.1

/-- Read the actual arithmetic expansion with its complete independent derivative Reading and all payments. -/
@[expose] def expansion (cache : Cell specification bank chain index) := cache.2.val

/-- The source arithmetic Reading is the complete unchanged aligned source bank Reading. -/
theorem source_eq (cache : Cell specification bank chain index) :
    cache.expansion.sourceValue = (bank.sourceEntry index).selected := cache.2.property.1

/-- The target arithmetic Reading is the complete unchanged aligned adjacent or terminal bank Reading. -/
theorem target_eq (cache : Cell specification bank chain index) :
    cache.expansion.targetValue = (bank.target chain index).2.2.selected := cache.2.property.2.1

/-- The derivative arithmetic Reading is the exact original single request on the retained genuine derivative cache. -/
theorem derivative_eq (cache : Cell specification bank chain index) :
    cache.expansion.derivative = derivativeRequest specification (bank.sourceEntry index).endpoint cache.values
      (bank.sourceSample index) (request layer initialPositive) := cache.2.property.2.2

/-- The actual observed source coefficient is the identical selected source bank witness. -/
theorem source_value (cache : Cell specification bank chain index) :
    cache.expansion.sourceValue.reading = bank.vertex index.castSucc := by
  have retained := congrArg
    (fun selected : Taylor.Observation.PrimitiveReading (bank.sourceEntry index).endpoint
      (bank.sourceSample index) => selected.reading) cache.source_eq
  exact retained.trans ((bank.sourceEntry_value index).trans (bank.vertex_source index).symm)

/-- The actual observed target coefficient is the identical selected next or terminal bank witness. -/
theorem target_value (cache : Cell specification bank chain index) :
    cache.expansion.targetValue.reading = bank.vertex index.succ := by
  let target := bank.target chain index
  have retained := congrArg
    (fun selected : Taylor.Observation.PrimitiveReading target.2.2.endpoint target.2.1 => selected.reading)
    cache.target_eq
  exact retained.trans (bank.target_value chain index)

/-- The observed certificate retains the original shared bank's exact selected arithmetic endpoint increment. -/
theorem increment_eq (cache : Cell specification bank chain index) :
    cache.expansion.targetValue.reading - cache.expansion.sourceValue.reading = bank.increment index := by
  rewrite [cache.target_value, cache.source_value]
  rfl

/-- The genuine derivative Reading pays its arithmetic discrepancy from the same actual refined scalar coefficient. -/
theorem derivative_error_le (cache : Cell specification bank chain index) :
    Norm.Basic.normSq (cache.expansion.derivative.reading - (samples.get index).val.center) ≤
      Taylor.Observation.derivativeCeiling site parameter specification * (layer.node index).span.width ^ 4 := by
  let source := (layer.node index).source
  let sample := bank.sourceSample index
  have paid := cache.expansion.derivative.reading_close.le.trans
    (OddPower.Observation.Factorization.errorBound_le_factor specification.differential
      (point site parameter 2 (Waist.direction quarter (layer.node index).span.lower) positive).base
      (point site parameter 2 (Waist.direction quarter (layer.node index).span.lower) positive).ordinate
      (Stereographic.Tangent.logarithmicVelocity (layer.node index).span.lower) source.lift.unitRoot sample
      cache.expansion.derivative.positive)
  rewrite [Primitive.Observation.derivative_scalar_eq] at paid
  have witness : (bank.sourceSample index).observation.witness = (samples.get index).val.sample.reading :=
    bank.sourceSample_reading index
  rewrite [witness, ← (samples.get index).val.center_eq, request_tolerance layer initialPositive index] at paid
  have fourthNonnegative : (0 : Fraction.Rational) ≤ (layer.node index).span.width ^ 4 :=
    ((Arithmetic.sq_nonneg_direct
      ((layer.node index).span.width * (layer.node index).span.width)).trans_eq (by ring1))
  have factor := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Taylor.Observation.derivativeFactor_le_ceiling specification source initial.cell.regular) fourthNonnegative
  exact paid.trans factor

/-- Actual observed primitive increments pay the original unchanged refined scalar cell, without an endpoint law. -/
theorem refined_integral_error_le (cache : Cell specification bank chain index) :
    Norm.Basic.normSq (bank.increment index - (samples.get index).val.cell.integralSample) ≤
      2 * (Taylor.Observation.ceiling site parameter primitive specification initial.cell.regular +
        Taylor.Observation.derivativeCeiling site parameter specification) * (layer.node index).span.width ^ 4 := by
  let step := Stereographic.Tangent.increment (layer.node index).span.width
  have displacement : (samples.get index).val.cell.displacement = step := by
    apply Gaussian.Basic.ext
    · rfl
    · change (0 : Fraction.Rational) - 0 = 0
      ring1
  have original := CellModel.quadratic_integral_error_le cache.expansion.certificate
    (samples.get index).val.cell (samples.get index).val.center displacement rfl
  rewrite [cache.expansion.base_eq, cache.expansion.output_eq, cache.expansion.slope_eq,
    cache.increment_eq, Stereographic.Tangent.increment_fourth,
    Stereographic.Tangent.increment_normSq] at original
  have fourthNonnegative : (0 : Fraction.Rational) ≤ (layer.node index).span.width ^ 4 :=
    (Arithmetic.sq_nonneg_direct
      ((layer.node index).span.width * (layer.node index).span.width)).trans_eq (by ring1)
  have factor := Arithmetic.mul_le_mul_of_nonneg_right_direct cache.expansion.factor_le
    fourthNonnegative
  have coefficient := Arithmetic.mul_le_mul_of_nonneg_left_direct cache.derivative_error_le
    (Arithmetic.sq_nonneg_direct (layer.node index).span.width)
  have coefficientSmall := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (layer.node index).width_sq_le_one
    (Arithmetic.mul_nonneg_direct
      (Taylor.Observation.derivativeCeiling_nonnegative site parameter specification initial.cell.regular)
      fourthNonnegative)
  exact original.trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct factor
        (coefficient.trans (coefficientSmall.trans_eq (Fraction.Field.one_mul _))))
      (by decide +kernel)).trans_eq (by ring1))

end Cell

variable (specification)

/-- Materialized node-indexed genuine derivative and primitive observation certificates on the same bank. -/
abbrev Cells (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Piece.chartIntervals layer.pieces)) :=
  Data.Vector.DependentVector (fun index => Cell specification bank chain index)

/-- Materialize each actual derivative cache, derivative Reading and observed chart certificate exactly once. -/
def cells (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Piece.chartIntervals layer.pieces)) : Cells specification bank chain :=
  Data.Vector.DependentVector.ofFn (fun index => Cell.build specification bank chain index)

/-- Reading the materialized cells returns the exact original single construction at that retained node index. -/
theorem cells_get (bank : Bank primitive samples upper)
    (chain : Partition.Interval.Chain initial.span.lower initial.span.upper
      (Piece.chartIntervals layer.pieces)) (index : Fin layer.pieces.length) :
    (cells specification bank chain).get index = Cell.build specification bank chain index :=
  Data.Vector.DependentVector.ofFn_get _ index

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank

end
