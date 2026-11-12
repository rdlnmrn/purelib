module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter.Realization
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Entry.Seam
import Purelib.Data.Fin
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Actual whole-quarter banks and finite scalar circuit payment

Each finite stage keeps the four original quarter realizations, all their
literal Banks and cell certificates, and four actual old-observation seam
Comparisons. Their original scalar samples remain unchanged. Exact
whole-entry time/request transports connect those same endpoint values.
A computed finite quarter-radius selection pays the aggregate sample.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Circuit

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat

/-- Four Gaussian summands have the same displayed left and right association. -/
private theorem four_sum_eq (first second third fourth : Canonical) :
    first + (second + (third + (fourth + 0))) = first + second + third + fourth := by ring1

/-- Eight times a nonnegative rational, increased by eighty, is nonnegative. -/
private theorem scale_value_nonnegative (value : Fraction.Rational) (nonnegative : 0 ≤ value) :
    0 ≤ 80 + 8 * value := by
  have base : (0 : Fraction.Rational) ≤ 80 := by
    change (0 : Fraction.Rational) ≤ ((80 : Nat) : Fraction.Rational)
    exact Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 80) (Nat.zero_le 80)
  have coefficient : (0 : Fraction.Rational) ≤ 8 :=
    Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 8) (Nat.zero_le 8)
  have scaled : (0 : Fraction.Rational) ≤ 8 * value :=
    Arithmetic.mul_nonneg_direct coefficient nonnegative
  have combined : (0 : Fraction.Rational) + 0 ≤ 80 + 8 * value :=
    Arithmetic.add_le_add_direct
      (first := 0) (second := 80) (third := 0) (fourth := 8 * value) base scaled
  rewrite [Fraction.zero_add] at combined
  exact combined

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {primitive : OddPowerDifferential (Paths.polynomial parameter)}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) primitive}
variable {data : Waist.Differential.Bounds.Data site parameter specification.differential}
variable {initialAccuracy : AccuracyRequest}
variable {source : Differential.Circuit.Cells data circuit initialAccuracy} {depth : Nat}

/-- Four complete original finite whole-quarter bank realizations keep the identical supplied source-cell caches. -/
abbrev Quarters (source : Differential.Circuit.Cells data circuit initialAccuracy) (depth : Nat) :=
  Quarter.Realization (specification := specification) (source.piece .first) rfl depth ×
  Quarter.Realization (specification := specification) (source.piece .second) rfl depth ×
  Quarter.Realization (specification := specification) (source.piece .third) rfl depth ×
  Quarter.Realization (specification := specification) (source.piece .fourth) rfl depth

namespace Quarters

/-- Build each finite original quarter realization once on the supplied original source cells. -/
def build (source : Differential.Circuit.Cells data circuit initialAccuracy) (depth : Nat) :
    Quarters (specification := specification) source depth :=
  ⟨Quarter.Realization.build (specification := specification) (source.piece .first) rfl depth,
    ⟨Quarter.Realization.build (specification := specification) (source.piece .second) rfl depth,
      ⟨Quarter.Realization.build (specification := specification) (source.piece .third) rfl depth,
        Quarter.Realization.build (specification := specification) (source.piece .fourth) rfl depth⟩⟩⟩

/-- Read the complete original first quarter realization without invoking any retained producer. -/
@[expose] def first (retained : Quarters (specification := specification) source depth) :
    Quarter.Realization (specification := specification) (source.piece .first) rfl depth := retained.1

/-- Read the complete original second quarter realization without invoking any retained producer. -/
@[expose] def second (retained : Quarters (specification := specification) source depth) :
    Quarter.Realization (specification := specification) (source.piece .second) rfl depth := retained.2.1

/-- Read the complete original third quarter realization without invoking any retained producer. -/
@[expose] def third (retained : Quarters (specification := specification) source depth) :
    Quarter.Realization (specification := specification) (source.piece .third) rfl depth := retained.2.2.1

/-- Read the complete original fourth quarter realization without invoking any retained producer. -/
@[expose] def fourth (retained : Quarters (specification := specification) source depth) :
    Quarter.Realization (specification := specification) (source.piece .fourth) rfl depth := retained.2.2.2

end Quarters

/-- The four original Comparison cache type uses these exact eight OLD endpoint Entries. -/
abbrev Seams (quarters : Quarters (specification := specification) source depth) :=
  Entry.Circuit.Comparison
    quarters.first.endpoints.first quarters.first.endpoints.last
    quarters.second.endpoints.first quarters.second.endpoints.last
    quarters.third.endpoints.first quarters.third.endpoints.last
    quarters.fourth.endpoints.first quarters.fourth.endpoints.last

/-- Construct the actual four old-observation seam comparisons once on the same literal quarter Banks. -/
def seamsFor (quarters : Quarters (specification := specification) source depth) : Seams quarters :=
  Entry.Circuit.build (circuit := circuit)
    quarters.first.endpoints.first quarters.first.endpoints.last
    quarters.second.endpoints.first quarters.second.endpoints.last
    quarters.third.endpoints.first quarters.third.endpoints.last
    quarters.fourth.endpoints.first quarters.fourth.endpoints.last

/-- One actual stage retains the same four quarter realizations and its complete four-Comparison factory cache. -/
@[expose] def Stage (source : Differential.Circuit.Cells data circuit initialAccuracy) (depth : Nat) :=
  Σ quarters : Quarters (specification := specification) source depth,
    { seams : Seams quarters // seams = seamsFor quarters }

namespace Stage

/-- Consume four already retained original quarter realizations and cache their actual seam comparisons once. -/
@[expose] def ofQuarters (quarters : Quarters (specification := specification) source depth) :
    Stage (specification := specification) source depth :=
  let seams := seamsFor quarters
  ⟨quarters, ⟨seams, rfl⟩⟩

/-- Build one finite stage, retaining the original quarter producers before constructing any seam comparison. -/
@[expose] def build (source : Differential.Circuit.Cells data circuit initialAccuracy) (depth : Nat) :
    Stage (specification := specification) source depth :=
  let quarters := Quarters.build (specification := specification) source depth
  ofQuarters (specification := specification) quarters

/-- Read the complete original quarter caches stored in this actual finite stage. -/
@[expose] def quarters (stage : Stage (specification := specification) source depth) :
    Quarters (specification := specification) source depth := stage.1

/-- Read the same complete four original seam Comparisons without acquiring another arithmetic observation. -/
@[expose] def seams (stage : Stage (specification := specification) source depth) : Seams stage.quarters := stage.2.val

/-- The actual retained four-Comparison cache is its exact original factory on the same quarter Banks. -/
theorem seams_eq (stage : Stage (specification := specification) source depth) :
    stage.seams = seamsFor stage.quarters := stage.2.property

/-- Consuming supplied quarter caches preserves those complete original caches literally. -/
theorem ofQuarters_quarters (quarters : Quarters (specification := specification) source depth) :
    (ofQuarters quarters).quarters = quarters := rfl

/-- The retained fresh quarter cache is the original finite four-quarter producer on the same source cells and depth. -/
theorem build_quarters (source : Differential.Circuit.Cells data circuit initialAccuracy) (depth : Nat) :
    (build (specification := specification) source depth).quarters =
      Quarters.build (specification := specification) source depth := rfl

/-- The four actual original scalar layer samples retain their geometric circuit order. -/
@[expose] def samples (stage : Stage (specification := specification) source depth) : Fin 4 → Canonical :=
  Data.Fin.cases stage.quarters.first.layer.val.model.integralSample
    (Data.Fin.cases stage.quarters.second.layer.val.model.integralSample
      (Data.Fin.cases stage.quarters.third.layer.val.model.integralSample
        (fun _ : Fin 1 => stage.quarters.fourth.layer.val.model.integralSample)))

/-- The four actual OLD bank boundary differences retain their original oriented quarter order. -/
@[expose] def boundaries (stage : Stage (specification := specification) source depth) : Fin 4 → Canonical :=
  Data.Fin.cases (stage.quarters.first.endpoints.last.value - stage.quarters.first.endpoints.first.value)
    (Data.Fin.cases (stage.quarters.second.endpoints.last.value - stage.quarters.second.endpoints.first.value)
      (Data.Fin.cases (stage.quarters.third.endpoints.last.value - stage.quarters.third.endpoints.first.value)
        (fun _ : Fin 1 => (stage.quarters.fourth.endpoints.last.value - stage.quarters.fourth.endpoints.first.value))))

/-- Read each actual old boundary minus the SAME stored original scalar layer sample. -/
@[expose] def errors (stage : Stage (specification := specification) source depth) (index : Fin 4) : Canonical :=
  stage.boundaries index - stage.samples index

/-- Sum the original actual scalar layer samples in their geometric circuit order. -/
@[expose] def sampleSum (stage : Stage (specification := specification) source depth) : Canonical :=
  FiniteSum.Fin.sumFin stage.samples

/-- Sum the original OLD boundary differences in their geometric circuit order. -/
@[expose] def boundarySum (stage : Stage (specification := specification) source depth) : Canonical :=
  FiniteSum.Fin.sumFin stage.boundaries

/-- Sum the four actual boundary-versus-original-sample errors with the same retained finite index table. -/
@[expose] def errorSum (stage : Stage (specification := specification) source depth) : Canonical :=
  FiniteSum.Fin.sumFin stage.errors

/-- The same four original finite sums give the exact boundary-minus-sample error decomposition. -/
theorem errorSum_eq (stage : Stage (specification := specification) source depth) :
    stage.errorSum = stage.boundarySum - stage.sampleSum :=
  FiniteSum.Fin.sumFin_sub stage.boundaries stage.samples

/-- The actual old quarter boundaries equal the sum of the SAME four retained seam residuals. -/
theorem boundarySum_eq (stage : Stage (specification := specification) source depth) :
    stage.boundarySum = stage.seams.sum := by
  rewrite [stage.seams.sum_eq_boundary]
  unfold boundarySum
  rewrite [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
  change (stage.quarters.first.endpoints.last.value - stage.quarters.first.endpoints.first.value) +
    ((stage.quarters.second.endpoints.last.value - stage.quarters.second.endpoints.first.value) +
      ((stage.quarters.third.endpoints.last.value - stage.quarters.third.endpoints.first.value) +
        ((stage.quarters.fourth.endpoints.last.value - stage.quarters.fourth.endpoints.first.value) + 0))) =
      (stage.quarters.first.endpoints.last.value - stage.quarters.first.endpoints.first.value) +
        (stage.quarters.second.endpoints.last.value - stage.quarters.second.endpoints.first.value) +
        (stage.quarters.third.endpoints.last.value - stage.quarters.third.endpoints.first.value) +
        (stage.quarters.fourth.endpoints.last.value - stage.quarters.fourth.endpoints.first.value)
  exact four_sum_eq _ _ _ _

/-- The actual stored scalar sample sum has the original full-circuit program's exact model-sample readback.

Each retained whole Layer has its own original layerAt factory identity.
This is an exact model readback, not a claim that an earlier unretained
program-model execution shares runtime caches with this new realization.
-/
theorem sampleSum_eq (stage : Stage (specification := specification) source depth) :
    stage.sampleSum = (source.program.model depth).integralSample := by
  rewrite [source.program_sample]
  unfold sampleSum
  rewrite [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
  change stage.quarters.first.layer.val.model.integralSample +
    (stage.quarters.second.layer.val.model.integralSample +
      (stage.quarters.third.layer.val.model.integralSample +
        (stage.quarters.fourth.layer.val.model.integralSample + 0))) = _
  rewrite [stage.quarters.first.sample_eq, stage.quarters.second.sample_eq,
    stage.quarters.third.sample_eq, stage.quarters.fourth.sample_eq]
  ring1

end Stage

/-- The four computed original cell ceilings retain the same source cells and oriented quarter order. -/
@[expose] def ceilings (source : Differential.Circuit.Cells data circuit initialAccuracy) : Fin 4 → Fraction.Rational :=
  Data.Fin.cases (cellCeiling specification (source.piece .first))
    (Data.Fin.cases (cellCeiling specification (source.piece .second))
      (Data.Fin.cases (cellCeiling specification (source.piece .third))
        (fun _ : Fin 1 => cellCeiling specification (source.piece .fourth))))

/-- Every computed original source-cell ceiling is nonnegative under its retained regularity and request. -/
theorem ceilings_nonnegative (source : Differential.Circuit.Cells data circuit initialAccuracy) (index : Fin 4) :
    0 ≤ ceilings (specification := specification) source index := by
  refine Data.Fin.cases_induction ?_ (fun remaining => ?_) index
  · exact cellCeiling_nonnegative specification (source.piece .first)
  · refine Data.Fin.cases_induction ?_ (fun remaining => ?_) remaining
    · exact cellCeiling_nonnegative specification (source.piece .second)
    · refine Data.Fin.cases_induction ?_ (fun _remaining => ?_) remaining
      · exact cellCeiling_nonnegative specification (source.piece .third)
      · exact cellCeiling_nonnegative specification (source.piece .fourth)

/-- The sum of the original four fixed cell ceilings is computed independently of the finite stage. -/
@[expose] def ceilingSum (source : Differential.Circuit.Cells data circuit initialAccuracy) : Fraction.Rational :=
  FiniteSum.Fin.sumFin (ceilings (specification := specification) source)

/-- The original nonnegative source-cell ceilings have nonnegative finite total. -/
theorem ceilingSum_nonnegative (source : Differential.Circuit.Cells data circuit initialAccuracy) :
    0 ≤ ceilingSum (specification := specification) source :=
  FiniteSum.Rational.Order.weight_sum_nonnegative _ (ceilings_nonnegative (specification := specification) source)

/-- The original source cells determine the full four-bank/four-seam scalar contraction scale. -/
@[expose] def scale (source : Differential.Circuit.Cells data circuit initialAccuracy) : Fraction.Rational :=
  80 + 8 * ceilingSum (specification := specification) source

/-- The internally computed scalar contraction scale is nonnegative. -/
theorem scale_nonnegative (source : Differential.Circuit.Cells data circuit initialAccuracy) :
    0 ≤ scale (specification := specification) source :=
  scale_value_nonnegative (ceilingSum (specification := specification) source)
    (ceilingSum_nonnegative (specification := specification) source)

namespace Stage

/-- Each actual retained Bank.Cells family pays its SAME old-boundary/original-sample error at the original scale. -/
theorem errors_le (stage : Stage (specification := specification) source depth) (index : Fin 4) :
    Norm.Basic.normSq (stage.errors index) ≤
      ceilings (specification := specification) source index * Geometric.Basic.quarterRadius 1 depth := by
  refine Data.Fin.cases_induction ?_ (fun remaining => ?_) index
  · exact stage.quarters.first.endpoints.boundary_error_le stage.quarters.first.cells
  · refine Data.Fin.cases_induction ?_ (fun remaining => ?_) remaining
    · exact stage.quarters.second.endpoints.boundary_error_le stage.quarters.second.cells
    · refine Data.Fin.cases_induction ?_ (fun _remaining => ?_) remaining
      · exact stage.quarters.third.endpoints.boundary_error_le stage.quarters.third.cells
      · exact stage.quarters.fourth.endpoints.boundary_error_le stage.quarters.fourth.cells

/-- The four actual retained cell-error sums pay four times the original ceiling sum and common quarter radius. -/
theorem errorSum_le (stage : Stage (specification := specification) source depth) :
    Norm.Basic.normSq stage.errorSum ≤
      4 * ceilingSum (specification := specification) source * Geometric.Basic.quarterRadius 1 depth := by
  have bound := Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin stage.errors
    (fun index => ceilings (specification := specification) source index * Geometric.Basic.quarterRadius 1 depth)
    stage.errors_le
  rewrite [FiniteSum.Fin.sumFin_mul_right] at bound
  change Norm.Basic.normSq stage.errorSum ≤
    (4 : Fraction.Rational) *
      (ceilingSum (specification := specification) source * Geometric.Basic.quarterRadius 1 depth) at bound
  exact bound.trans_eq (by ring1)

/-- The SAME actual retained four seam Comparisons pay the four old boundary differences at squared quarter radius. -/
theorem boundarySum_le (stage : Stage (specification := specification) source depth) :
    Norm.Basic.normSq stage.boundarySum ≤ 40 * Geometric.Basic.quarterRadius 1 depth ^ 2 := by
  rewrite [stage.boundarySum_eq]
  exact stage.seams.error_le

/-- The actual finite scalar sample sum contracts at the computed original-data quarter-radius scale.

The old boundary payment and the four actual Bank.Cells errors are combined
on the SAME values and model samples. The bank arithmetic tolerance itself
is the squared original quarter radius; shrinking only the auxiliary
comparison target is not used to shrink fixed old observations.
-/
theorem sampleSum_le (stage : Stage (specification := specification) source depth) :
    Norm.Basic.normSq stage.sampleSum ≤
      Geometric.Basic.quarterRadius (scale (specification := specification) source) depth := by
  let radius := Geometric.Basic.quarterRadius 1 depth
  have radiusNonnegative : 0 ≤ radius :=
    Geometric.Basic.quarterRadius_nonneg (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1) depth
  have radiusUpper : radius ≤ 1 :=
    Geometric.Basic.quarterRadius_le_scale (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1) depth
  have squared : radius ^ 2 ≤ radius := by
    calc
      _ = radius * radius := by ring1
      _ ≤ radius * 1 :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct radiusUpper radiusNonnegative
      _ = _ := Fraction.Field.mul_one_direct _
  have decomposition : stage.sampleSum = stage.boundarySum - stage.errorSum := by
    rewrite [stage.errorSum_eq]
    ring1
  rewrite [decomposition]
  have total := (Norm.Bounds.normSq_sub_le_two stage.boundarySum stage.errorSum).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct stage.boundarySum_le stage.errorSum_le)
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2))
  have shrink := Arithmetic.mul_le_mul_of_nonneg_left_direct squared
    (Fraction.Cast.Order.natCast_le_direct (m := 0) (n := 40) (Nat.zero_le 40))
  calc
    _ ≤ 2 * (40 * radius ^ 2 + 4 * ceilingSum (specification := specification) source * radius) := total
    _ ≤ 2 * (40 * radius + 4 * ceilingSum (specification := specification) source * radius) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct shrink (Fraction.Order.Basic.le_refl _))
        (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)
    _ = _ := by
      unfold scale radius
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1

/-- The actual original full-circuit scalar program sample obeys the SAME finite bank/seam contraction bound. -/
theorem program_sample_le (stage : Stage (specification := specification) source depth) :
    Norm.Basic.normSq (source.program.model depth).integralSample ≤
      Geometric.Basic.quarterRadius (scale (specification := specification) source) depth := by
  rewrite [← stage.sampleSum_eq]
  exact stage.sampleSum_le

/-- Each actual bank/seam cache at or beyond the retained sufficient depth pays the original scalar program request. -/
theorem requested_sample_lt (stage : Stage (specification := specification) source depth)
    {current : Nat} (request : AccuracyRequest)
    (selected : Geometric.Search.Selection (scale (specification := specification) source) current request.tolerance)
    (after : selected.stage ≤ depth) :
    Norm.Basic.normSq (source.program.model depth).integralSample < request.tolerance :=
  stage.program_sample_le.trans_lt (selected.later_accurate after)

end Stage

/-- Compute and retain the sufficient finite depth from the original source-cell scale and positive request. -/
def selection (source : Differential.Circuit.Cells data circuit initialAccuracy) (current : Nat)
    (request : AccuracyRequest) :
    Geometric.Search.Selection (scale (specification := specification) source) current request.tolerance :=
  Geometric.Search.Selection.build (scale (specification := specification) source)
    (scale_nonnegative (specification := specification) source) current request.tolerance request.positive

/-- One finite request retains its computed sufficient schedule and the actual bank/seam stage acquired there. -/
@[expose] def Acquisition (source : Differential.Circuit.Cells data circuit initialAccuracy)
    (current : Nat) (request : AccuracyRequest) :=
  Σ selected : { retained : Geometric.Search.Selection
      (scale (specification := specification) source) current request.tolerance //
      retained = selection (specification := specification) source current request },
    { stage : Stage (specification := specification) source selected.val.stage //
      stage = Stage.build (specification := specification) source selected.val.stage }

namespace Acquisition

/-- Compute the sufficient schedule, then construct one actual finite stage with its original shrinking requests. -/
def build (source : Differential.Circuit.Cells data circuit initialAccuracy) (current : Nat)
    (request : AccuracyRequest) : Acquisition (specification := specification) source current request :=
  let selected := selection (specification := specification) source current request
  let stage := Stage.build (specification := specification) source selected.stage
  ⟨⟨selected, rfl⟩, ⟨stage, rfl⟩⟩

variable {current : Nat} {request : AccuracyRequest}

/-- Read the actual computed finite depth selection with its retained quotient, fuel and attained allowance. -/
@[expose] def selected (retained : Acquisition (specification := specification) source current request) :
    Geometric.Search.Selection (scale (specification := specification) source) current request.tolerance :=
  retained.1.val

/-- Read the actual complete bank/seam stage constructed at that SAME retained sufficient depth. -/
@[expose] def stage (retained : Acquisition (specification := specification) source current request) :
    Stage (specification := specification) source retained.selected.stage := retained.2.val

/-- The retained depth selection is its exact original finite producer on the same source cells and request. -/
theorem selected_eq (retained : Acquisition (specification := specification) source current request) :
    retained.selected = selection (specification := specification) source current request := retained.1.property

/-- The retained whole bank/seam stage is its exact original producer at the actual selected depth. -/
theorem stage_eq (retained : Acquisition (specification := specification) source current request) :
    retained.stage = Stage.build (specification := specification) source retained.selected.stage := retained.2.property

/-- The SAME actual retained sufficient stage strictly pays the original full-circuit scalar sample request. -/
theorem sample_lt (retained : Acquisition (specification := specification) source current request) :
    Norm.Basic.normSq (source.program.model retained.selected.stage).integralSample < request.tolerance :=
  retained.stage.requested_sample_lt request retained.selected (Nat.le_refl _)

end Acquisition

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Circuit

end
