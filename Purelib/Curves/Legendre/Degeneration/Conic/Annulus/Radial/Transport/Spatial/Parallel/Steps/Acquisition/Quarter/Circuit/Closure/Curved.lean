module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Quarter.Paid
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure.Descent
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation.Bank.Circuit
import Purelib.Data.Fin
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Four old curved banks on one identical paid closed primitive execution

Each quarter's actual retained Bank.Cells and two endpoint Comparisons
pay its scalar sample against the SAME literal old paid quarter increment.
The exact old shared vertices telescope those four increments. The single
original closing Comparison pays their returned-minus-initial value. Both
old bank and old vertex request radii remain explicit in the final bound.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive.Observation
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter}
variable {firstReading : ReadingAt circuit.first.actual UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginal : Steps.Quarter circuit.first.actual circuit.first.regular
  UniformPrimitiveMesh.firstEndpoint firstReading firstOriginalOwner}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {agreement : InitialAgreement UniformPrimitiveMesh.firstEndpoint firstReading sourceOwner}
variable {initial : Quarter firstOriginal sourceOwner agreement}
variable {secondReading : ReadingAt circuit.second.actual UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
  UniformPrimitiveMesh.firstEndpoint secondReading secondOriginalOwner}
variable {thirdReading : ReadingAt circuit.third.actual UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginalOwner : OwnerAt site parameter .third (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginal : Steps.Quarter circuit.third.actual circuit.third.regular
  UniformPrimitiveMesh.firstEndpoint thirdReading thirdOriginalOwner}
variable {fourthReading : ReadingAt circuit.fourth.actual UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginalOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginal : Steps.Quarter circuit.fourth.actual circuit.fourth.regular
  UniformPrimitiveMesh.firstEndpoint fourthReading fourthOriginalOwner}
variable {execution : Execution initial secondOriginal thirdOriginal fourthOriginal}

open Purelib.Algebra
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Primitive
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

namespace Closure.Result.Curved

variable {result : Closure.Result execution} {row : Row}
variable {specification : OddPower.Derivative.Specification (Paths.polynomial parameter) (row.form parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter specification.differential}
variable {initialAccuracy : AccuracyRequest} {source : Differential.Circuit.Cells data circuit initialAccuracy}
variable {depth : Nat} {request : AccuracyRequest}
variable {defined : OwnerPath.Primitive.Defined (row.expression parameter) result.traced.path}
variable (partition : Partitioned result (row.expression parameter) defined request)
variable (descended : Partitioned.Descent partition)
variable (banks : Bank.Circuit.Quarters (specification := specification) source depth)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

set_option genInjectivity false in
/-- Four complete old endpoint-comparison caches retain the identical bank and paid-quarter observation executions.

Every child is an original Entry.Quarter.Compared with two actual old
observation owners and both exact operational factory equations. The old
partition, its complete physical descent and all four Banks remain indices.
No new path, source attachment, old observation or closing join is acquired.
-/
structure Compared where
  /-- The first old bank and literal first paid-quarter spine share these two actual endpoint Comparisons. -/
  first : Bank.Quarter.Paid.Compared execution.first banks.first descended.first.original rfl
  /-- The second old bank and actual second paid-quarter spine retain their separate old observations. -/
  second : Bank.Quarter.Paid.Compared execution.second.paid banks.second descended.second.original rfl
  /-- The third old bank and actual third paid-quarter spine retain their original full-cubic comparison owners. -/
  third : Bank.Quarter.Paid.Compared execution.third.paid banks.third descended.third.original rfl
  /-- The fourth old bank and actual returned paid-quarter spine retain the original endpoint request payment. -/
  fourth : Bank.Quarter.Paid.Compared execution.fourth.paid banks.fourth descended.fourth.original rfl

constructive_injectivity Compared

namespace Compared

/-- Construct each original pair of endpoint comparisons once on the same supplied old bank and paid-spine caches. -/
def build : Compared partition descended banks :=
  let first := Bank.Quarter.Paid.compare execution.first banks.first descended.first.original rfl
  let second := Bank.Quarter.Paid.compare execution.second.paid banks.second descended.second.original rfl
  let third := Bank.Quarter.Paid.compare execution.third.paid banks.third descended.third.original rfl
  let fourth := Bank.Quarter.Paid.compare execution.fourth.paid banks.fourth descended.fourth.original rfl
  ⟨first, second, third, fourth⟩

end Compared

/-- Read the SAME four actual original bank model samples in their original oriented quarter order. -/
@[expose] def samples : Fin 4 → Canonical :=
  Data.Fin.cases banks.first.layer.val.model.integralSample
    (Data.Fin.cases banks.second.layer.val.model.integralSample
      (Data.Fin.cases banks.third.layer.val.model.integralSample
        (fun _ : Fin 1 => banks.fourth.layer.val.model.integralSample)))

/-- Read the actual old primitive increments from the complete retained physical quarter views. -/
@[expose] def increments : Fin 4 → Canonical :=
  Data.Fin.cases (descended.first.original.last.value - descended.first.original.first.value)
    (Data.Fin.cases (descended.second.original.last.value - descended.second.original.first.value)
      (Data.Fin.cases (descended.third.original.last.value - descended.third.original.first.value)
        (fun _ : Fin 1 => descended.fourth.original.last.value - descended.fourth.original.first.value)))

/-- Each actual scalar residual uses the SAME original model sample and literal old quarter increment. -/
@[expose] def residuals (index : Fin 4) : Canonical := samples banks index - increments partition descended index

/-- The four same-cache endpoint pairs and original cell bounds pay each quarter's actual scalar residual. -/
theorem residuals_le (compared : Compared partition descended banks) (index : Fin 4) :
    Norm.Basic.normSq (residuals partition descended banks index) ≤
      2 * Bank.Circuit.ceilings (specification := specification) source index *
          Geometric.Basic.quarterRadius 1 depth +
        8 * (Bank.Quarter.request depth).tolerance +
          6 * partition.observed.observations.accuracy.tolerance := by
  refine Data.Fin.cases_induction ?_ (fun remaining => ?_) index
  · exact Bank.Quarter.Paid.residual_le execution.first banks.first descended.first.original compared.first
  · refine Data.Fin.cases_induction ?_ (fun remaining => ?_) remaining
    · exact Bank.Quarter.Paid.residual_le
        execution.second.paid banks.second descended.second.original compared.second
    · refine Data.Fin.cases_induction ?_ (fun _remaining => ?_) remaining
      · exact Bank.Quarter.Paid.residual_le
          execution.third.paid banks.third descended.third.original compared.third
      · exact Bank.Quarter.Paid.residual_le
          execution.fourth.paid banks.fourth descended.fourth.original compared.fourth

/-- The actual four retained bank samples sum to their unchanged original curved full-circuit program sample. -/
theorem samples_sum_eq : FiniteSum.Fin.sumFin (samples banks) = (source.program.model depth).integralSample := by
  rewrite [source.program_sample]
  unfold samples
  rewrite [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
  change banks.first.layer.val.model.integralSample +
    (banks.second.layer.val.model.integralSample +
      (banks.third.layer.val.model.integralSample + (banks.fourth.layer.val.model.integralSample + 0))) = _
  rewrite [banks.first.sample_eq, banks.second.sample_eq, banks.third.sample_eq, banks.fourth.sample_eq]
  ring1

/-- Four Gaussian scalar increments telescope when the three old adjacent endpoint values are the same. -/
private theorem four_increments (first second third fourth last : Canonical) :
    (second - first) + ((third - second) + ((fourth - third) + ((last - fourth) + 0))) = last - first := by ring1

/-- Exact original seam transports and shared old vertices telescope the SAME four actual physical increments.

Complete old spines are used through their retained original identities.
The endpoint/readback operations change no observation, state, request or
primitive constant. No new trace or equality by vertex-list comparison is
used. The literal returned and initial old vertices remain distinct.
-/
theorem increments_sum_eq : FiniteSum.Fin.sumFin (increments partition descended) =
    partition.quarters.fourth.last.value - partition.quarters.first.first.value := by
  have first := (congrArg (fun old : Primitive.Spine (row.expression parameter)
      partition.observed.observations.accuracy execution.first.receipt.trace => old.last.value - old.first.value)
      descended.first.original_eq).trans
    ((congrArg₂ (fun last first : Canonical => last - first)
      (execution.second.seam.quarterSpine_last_value partition.firstInput)
      (execution.second.seam.quarterSpine_first_value partition.firstInput)).trans
      (congrArg₂ (fun last first : Canonical => last - first)
        (Primitive.Spine.castPath_last_value result.traced.first_eq partition.quarters.first)
        (Primitive.Spine.castPath_first_value result.traced.first_eq partition.quarters.first)))
  have second := (congrArg (fun old : Primitive.Spine (row.expression parameter)
      partition.observed.observations.accuracy execution.second.paid.receipt.trace => old.last.value - old.first.value)
      descended.second.original_eq).trans
    ((congrArg₂ (fun last first : Canonical => last - first)
      (execution.third.seam.quarterSpine_last_value partition.secondInput)
      (execution.third.seam.quarterSpine_first_value partition.secondInput)).trans
      (congrArg₂ (fun last first : Canonical => last - first)
        (Primitive.Spine.castPath_last_value result.traced.second_eq partition.quarters.second)
        (Primitive.Spine.castPath_first_value result.traced.second_eq partition.quarters.second)))
  have third := (congrArg (fun old : Primitive.Spine (row.expression parameter)
      partition.observed.observations.accuracy execution.third.paid.receipt.trace => old.last.value - old.first.value)
      descended.third.original_eq).trans
    ((congrArg₂ (fun last first : Canonical => last - first)
      (execution.fourth.seam.quarterSpine_last_value partition.thirdInput)
      (execution.fourth.seam.quarterSpine_first_value partition.thirdInput)).trans
      (congrArg₂ (fun last first : Canonical => last - first)
        (Primitive.Spine.castPath_last_value result.traced.third_eq partition.quarters.third)
        (Primitive.Spine.castPath_first_value result.traced.third_eq partition.quarters.third)))
  have fourth := (congrArg (fun old : Primitive.Spine (row.expression parameter)
      partition.observed.observations.accuracy execution.fourth.paid.receipt.trace => old.last.value - old.first.value)
      descended.fourth.original_eq).trans
    ((congrArg₂ (fun last first : Canonical => last - first)
      (execution.closing.quarterSpine_last_value partition.fourthInput)
      (execution.closing.quarterSpine_first_value partition.fourthInput)).trans
      (congrArg₂ (fun last first : Canonical => last - first)
        (Primitive.Spine.castPath_last_value result.traced.fourth_eq partition.quarters.fourth)
        (Primitive.Spine.castPath_first_value result.traced.fourth_eq partition.quarters.fourth)))
  have firstSecond := congrArg (fun vertex => vertex.value) partition.quarters.first_second
  have secondThird := congrArg (fun vertex => vertex.value) partition.quarters.second_third
  have thirdFourth := congrArg (fun vertex => vertex.value) partition.quarters.third_fourth
  unfold increments
  rewrite [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
  change (descended.first.original.last.value - descended.first.original.first.value) +
    ((descended.second.original.last.value - descended.second.original.first.value) +
      ((descended.third.original.last.value - descended.third.original.first.value) +
        ((descended.fourth.original.last.value - descended.fourth.original.first.value) + 0))) = _
  rewrite [first, second, third, fourth, firstSecond, secondThird, thirdFourth]
  exact four_increments _ _ _ _ _

/-- The single SAME old closing Comparison pays the actual sum of the retained four quarter increments. -/
theorem increments_sum_lt : Norm.Basic.normSq (FiniteSum.Fin.sumFin (increments partition descended)) <
    partition.observed.observations.accuracy.tolerance := by
  rewrite [increments_sum_eq partition descended, Norm.Bounds.normSq_sub_symm]
  exact partition.closing_jump_lt

/-- The finite sum of four identical rational entries is four times that unchanged entry. -/
private theorem four_constant (value : Rational) : FiniteSum.Fin.sumFin (fun _ : Fin 4 => value) = 4 * value := by
  rewrite [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ,
    FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
  change value + (value + (value + (value + 0))) = 4 * value
  ring1

/-- The four actual quarter residuals have a count-paid bound from their original ceilings and BOTH old accuracies. -/
theorem residuals_sum_le (compared : Compared partition descended banks) :
    Norm.Basic.normSq (FiniteSum.Fin.sumFin (residuals partition descended banks)) ≤
      8 * Bank.Circuit.ceilingSum (specification := specification) source *
          Geometric.Basic.quarterRadius 1 depth +
        128 * (Bank.Quarter.request depth).tolerance +
          96 * partition.observed.observations.accuracy.tolerance := by
  have bounded := Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin (residuals partition descended banks)
    (fun index => 2 * Bank.Circuit.ceilings (specification := specification) source index *
        Geometric.Basic.quarterRadius 1 depth +
      8 * (Bank.Quarter.request depth).tolerance +
        6 * partition.observed.observations.accuracy.tolerance) (residuals_le partition descended banks compared)
  rewrite [FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_add,
    FiniteSum.Fin.sumFin_mul_right, FiniteSum.Fin.sumFin_mul_left] at bounded
  change Norm.Basic.normSq (FiniteSum.Fin.sumFin (residuals partition descended banks)) ≤
    (4 : Rational) * (2 * Bank.Circuit.ceilingSum (specification := specification) source *
      Geometric.Basic.quarterRadius 1 depth +
      FiniteSum.Fin.sumFin (fun _ : Fin 4 => 8 * (Bank.Quarter.request depth).tolerance) +
      FiniteSum.Fin.sumFin (fun _ : Fin 4 => 6 * partition.observed.observations.accuracy.tolerance)) at bounded
  have scalar (ceiling radius bankAccuracy vertexAccuracy : Rational) :
      4 * (2 * ceiling * radius + FiniteSum.Fin.sumFin (fun _ : Fin 4 => 8 * bankAccuracy) +
        FiniteSum.Fin.sumFin (fun _ : Fin 4 => 6 * vertexAccuracy)) =
      8 * ceiling * radius + 128 * bankAccuracy + 96 * vertexAccuracy := by
    rewrite [four_constant, four_constant]
    ring1
  exact bounded.trans_eq (scalar _ _ _ _)

/-- The actual unchanged curved relation-program sample is paid by four old banks and the single literal closing.

This is a finite bound on the original model sample. Both old arithmetic
request contributions remain separate. No source residual, final integral
agreement, sample inequality or connection comparison is an input.
-/
theorem program_sample_le (compared : Compared partition descended banks) :
    Norm.Basic.normSq (source.program.model depth).integralSample ≤
      16 * Bank.Circuit.ceilingSum (specification := specification) source *
          Geometric.Basic.quarterRadius 1 depth +
        256 * (Bank.Quarter.request depth).tolerance +
          194 * partition.observed.observations.accuracy.tolerance := by
  have errors := residuals_sum_le partition descended banks compared
  have closing := increments_sum_lt partition descended
  have decomposition : FiniteSum.Fin.sumFin (samples banks) =
      FiniteSum.Fin.sumFin (residuals partition descended banks) +
        FiniteSum.Fin.sumFin (increments partition descended) := by
    have retained := FiniteSum.Fin.sumFin_sub (samples banks) (increments partition descended)
    change FiniteSum.Fin.sumFin (residuals partition descended banks) =
      FiniteSum.Fin.sumFin (samples banks) - FiniteSum.Fin.sumFin (increments partition descended) at retained
    rewrite [retained]
    ring1
  rewrite [← samples_sum_eq banks, decomposition]
  have bound := (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct errors closing.le) (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  exact bound.trans_eq (by ring1)

end Closure.Result.Curved

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
