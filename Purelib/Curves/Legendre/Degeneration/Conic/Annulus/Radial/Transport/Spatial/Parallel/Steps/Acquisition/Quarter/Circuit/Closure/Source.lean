module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation.Source
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure.Request
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Schedule
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Payment
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # The actual same-cache four-quarter affine source telescope

Shared original source families are independent of the primitive row.
Each actual old quarter retains its complete source comparison and original
error/integral lists. Exact old seam vertex identities give the global
finite telescope. The SAME literal closing comparison pays its return jump,
then the already selected original source allocation pays the actual sum.
No curved, numerical-period or canonical-cycle identification is inferred.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

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

open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Legendre.Periods.Jets.Source (Row)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge

open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Execution

variable (execution : Execution initial secondOriginal thirdOriginal fourthOriginal)
variable {stage : Nat} {sourceTargets : CellEndpoints.Targets sourcePath stage}

/-- The SAME four actual paid quarters retain the original shared source family at their literal old input branch. -/
abbrev Sources :=
  Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount) (floor := floor) (sheet := sheet)
    (sourceTargets := sourceTargets) execution

namespace Sources

/-- Execute the single shared source-family producer on the SAME four original old-quarter inputs. -/
def build : Sources (frame := frame) (basis := basis) (modelCount := modelCount) (floor := floor) (sheet := sheet)
    (sourceTargets := sourceTargets) execution :=
  Cache.Sources.build (frame := frame) (basis := basis) (modelCount := modelCount) (floor := floor) (sheet := sheet)
    (sourceTargets := sourceTargets) execution

/-- The shared old-input producer returns the SAME complete four source families as the original ordered factories.

The proof compares whole values for all original inputs. It does not claim
literal ConstantInfo identity or execution reuse from a readback equation;
the single shared producer is the actual implementation used by build.
-/
theorem build_eq_original :
    build (frame := frame) (basis := basis) (modelCount := modelCount) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) execution =
      (Quarter.Sources.build (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
          (sheet := sheet) (sourceTargets := sourceTargets) execution.first,
        (Quarter.Sources.build (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
            (sheet := sheet) (sourceTargets := sourceTargets) execution.second.paid,
          (Quarter.Sources.build (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
              (sheet := sheet) (sourceTargets := sourceTargets) execution.third.paid,
            Quarter.Sources.build (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
              (sheet := sheet) (sourceTargets := sourceTargets) execution.fourth.paid))) := by
  unfold build
  apply (Cache.Sources.build_eq (frame := frame) (basis := basis) (modelCount := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution).trans
  have first := Input.Realization.Sources.build_ofSteps (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) rfl execution.first
  have second := Input.Realization.Sources.build_ofSteps (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) rfl execution.second.paid
  have third := Input.Realization.Sources.build_ofSteps (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) rfl execution.third.paid
  have fourth := Input.Realization.Sources.build_ofSteps (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) rfl execution.fourth.paid
  exact congrArg₂ (fun first rest => (first, rest)) first
    (congrArg₂ (fun second rest => (second, rest)) second
      (congrArg₂ (fun third fourth => (third, fourth)) third fourth))

end Sources

end Execution

namespace Closure.Result.Requested

variable {result : Closure.Result execution} {row : Row} {currentStage : Nat} {request : AccuracyRequest}
variable (allocated : Requested result row sourcePath currentStage request)
variable (sources : Execution.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) execution)

set_option genInjectivity false in
/-- Four actual quarter comparisons retain the SAME old allocation/closing input and original shared source families.

Each completed comparison has its own exact factory law. No source model,
primitive vertex, observation, trace or closing cache is rerun. The four
original full-block error lists remain actual retained comparison outputs.
The nominal cache boundary keeps native type conversion from reopening
all four concrete quarter observation families at every production use.
-/
structure Compared where
  /-- The complete row-independent original source family is the SAME supplied shared input. -/
  cachedSources : { value : Execution.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) execution // value = sources }
  /-- The actual complete first-quarter comparison retains its identical old view/source inputs and factory. -/
  cachedFirst : { value : Quarter.Compared (frame := frame) (basis := basis) (count := modelCount)
        (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) row execution.first
        allocated.descended.first cachedSources.val.1 allocated.allocation //
      value = Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
        (sheet := sheet) (sourceTargets := allocated.targets) row execution.first
        allocated.descended.first cachedSources.val.1 allocated.allocation }
  /-- The actual complete second-quarter comparison retains its identical old view/source inputs and factory. -/
  cachedSecond : { value : Quarter.Compared (frame := frame) (basis := basis) (count := modelCount)
        (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) row execution.second.paid
        allocated.descended.second cachedSources.val.2.1 allocated.allocation //
      value = Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
        (sheet := sheet) (sourceTargets := allocated.targets) row execution.second.paid
        allocated.descended.second cachedSources.val.2.1 allocated.allocation }
  /-- The actual complete third-quarter comparison retains its identical old view/source inputs and factory. -/
  cachedThird : { value : Quarter.Compared (frame := frame) (basis := basis) (count := modelCount)
        (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) row execution.third.paid
        allocated.descended.third cachedSources.val.2.2.1 allocated.allocation //
      value = Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
        (sheet := sheet) (sourceTargets := allocated.targets) row execution.third.paid
        allocated.descended.third cachedSources.val.2.2.1 allocated.allocation }
  /-- The actual complete fourth-quarter comparison retains its identical old view/source inputs and factory. -/
  cachedFourth : { value : Quarter.Compared (frame := frame) (basis := basis) (count := modelCount)
        (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) row execution.fourth.paid
        allocated.descended.fourth cachedSources.val.2.2.2 allocated.allocation //
      value = Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
        (sheet := sheet) (sourceTargets := allocated.targets) row execution.fourth.paid
        allocated.descended.fourth cachedSources.val.2.2.2 allocated.allocation }

constructive_injectivity Compared

/-- Compare each actual old quarter once against its SAME prepared sources, preserving the literal original closing. -/
def compare : Compared allocated sources :=
  let first := Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
    (sheet := sheet) (sourceTargets := allocated.targets) row execution.first
    allocated.descended.first sources.1 allocated.allocation
  let second := Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
    (sheet := sheet) (sourceTargets := allocated.targets) row execution.second.paid
    allocated.descended.second sources.2.1 allocated.allocation
  let third := Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
    (sheet := sheet) (sourceTargets := allocated.targets) row execution.third.paid
    allocated.descended.third sources.2.2.1 allocated.allocation
  let fourth := Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
    (sheet := sheet) (sourceTargets := allocated.targets) row execution.fourth.paid
    allocated.descended.fourth sources.2.2.2 allocated.allocation
  { cachedSources := ⟨sources, rfl⟩
    cachedFirst := ⟨first, rfl⟩
    cachedSecond := ⟨second, rfl⟩
    cachedThird := ⟨third, rfl⟩
    cachedFourth := ⟨fourth, rfl⟩ }

namespace Compared

variable {allocated sources}
variable (compared : Compared allocated sources)

/-- Read the exact original shared source families, independent of this selected primitive row. -/
@[expose] def prepared : Execution.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) execution := compared.cachedSources.val

/-- Read the complete actual old first-quarter source comparison and its original per-Route caches. -/
@[expose] def first : Quarter.Compared (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) row execution.first
    allocated.descended.first compared.prepared.1 allocated.allocation := compared.cachedFirst.val

/-- Read the complete actual old second-quarter source comparison and its original per-Route caches. -/
@[expose] def second : Quarter.Compared (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) row execution.second.paid
    allocated.descended.second compared.prepared.2.1 allocated.allocation := compared.cachedSecond.val

/-- Read the complete actual old third-quarter source comparison and its original per-Route caches. -/
@[expose] def third : Quarter.Compared (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) row execution.third.paid
    allocated.descended.third compared.prepared.2.2.1 allocated.allocation := compared.cachedThird.val

/-- Read the complete actual old fourth-quarter source comparison and its original per-Route caches. -/
@[expose] def fourth : Quarter.Compared (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (sourceTargets := allocated.targets) row execution.fourth.paid
    allocated.descended.fourth compared.prepared.2.2.2 allocated.allocation := compared.cachedFourth.val

/-- The whole prepared source family remains the supplied original input with no per-row source preparation. -/
theorem prepared_eq : compared.prepared = sources := compared.cachedSources.property

/-- The complete first comparison is the original factory on these identical old views and source inputs. -/
theorem first_eq : compared.first =
    Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (sourceTargets := allocated.targets) row execution.first
      allocated.descended.first compared.prepared.1 allocated.allocation := compared.cachedFirst.property

/-- The complete second comparison is the original factory on these identical old views and source inputs. -/
theorem second_eq : compared.second =
    Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (sourceTargets := allocated.targets) row execution.second.paid
      allocated.descended.second compared.prepared.2.1 allocated.allocation := compared.cachedSecond.property

/-- The complete third comparison is the original factory on these identical old views and source inputs. -/
theorem third_eq : compared.third =
    Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (sourceTargets := allocated.targets) row execution.third.paid
      allocated.descended.third compared.prepared.2.2.1 allocated.allocation := compared.cachedThird.property

/-- The complete fourth comparison is the original factory on these identical old views and source inputs. -/
theorem fourth_eq : compared.fourth =
    Quarter.compare (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (sourceTargets := allocated.targets) row execution.fourth.paid
      allocated.descended.fourth compared.prepared.2.2.2 allocated.allocation := compared.cachedFourth.property

/-- Read the SAME original source integrals in literal first, second, third and fourth-quarter order. -/
@[expose] def integrals : List Canonical := compared.first.integrals ++
  (compared.second.integrals ++ (compared.third.integrals ++ compared.fourth.integrals))

/-- Read every actual full-block error without omitting any old stationary occurrence or moving source integral. -/
@[expose] def errors : List Canonical := compared.first.errors ++
  (compared.second.errors ++ (compared.third.errors ++ compared.fourth.errors))

/-- Each SAME actual full-block error is paid by its original retained per-Route cache and exact source allocation. -/
theorem errors_bounded : ∀ error ∈ compared.errors, Norm.Basic.normSq error ≤ 26 * allocated.targets.endpoint := by
  intro error member
  rcases Membership.mem_append.mp member with first | following
  · exact compared.first.errors_bounded error first
  · rcases Membership.mem_append.mp following with second | following
    · exact compared.second.errors_bounded error second
    · rcases Membership.mem_append.mp following with third | fourth
      · exact compared.third.errors_bounded error third
      · exact compared.fourth.errors_bounded error fourth

/-- The actual flattened global list has the SAME retained original paid four-quarter prepared-request count. -/
theorem errors_length : compared.errors.length = execution.requestCount := by
  change (compared.first.errors ++ (compared.second.errors ++
    (compared.third.errors ++ compared.fourth.errors))).length = _
  rewrite [Append.length_append, Append.length_append, Append.length_append,
    compared.first.errors_length, compared.second.errors_length, compared.third.errors_length,
    compared.fourth.errors_length]
  rfl

/-- The actual error list has the global count selected before the original source and observer acquisitions. -/
theorem errors_count : compared.errors.length = allocated.count :=
  compared.errors_length.trans allocated.count_eq.symm

/-- The original quarter errors telescope on the SAME old whole closed-spine endpoints and source sums. -/
theorem errors_sum_eq : Norm.Sum.Basic.gaussianSum compared.errors =
    allocated.partition.observed.observations.observed.last.value -
      allocated.partition.observed.observations.observed.first.value -
        Norm.Sum.Basic.gaussianSum compared.integrals := by
  have sumAppend (a b c d : List Canonical) :
      Norm.Sum.Basic.gaussianSum (a ++ (b ++ (c ++ d))) =
        Norm.Sum.Basic.gaussianSum a + (Norm.Sum.Basic.gaussianSum b +
          (Norm.Sum.Basic.gaussianSum c + Norm.Sum.Basic.gaussianSum d)) := by
    rewrite [Norm.Sum.Basic.gaussianSum_append a (b ++ (c ++ d)),
      Norm.Sum.Basic.gaussianSum_append b (c ++ d), Norm.Sum.Basic.gaussianSum_append c d]
    rfl
  have firstBlock := compared.first.errors_sum_eq
  have firstStart : (execution.second.seam.quarterSpine allocated.partition.firstInput).first.value =
      allocated.partition.quarters.first.first.value :=
    (execution.second.seam.quarterSpine_first_value allocated.partition.firstInput).trans
      (Primitive.Spine.castPath_first_value result.traced.first_eq allocated.partition.quarters.first)
  have firstFinish : (execution.second.seam.quarterSpine allocated.partition.firstInput).last.value =
      allocated.partition.quarters.first.last.value :=
    (execution.second.seam.quarterSpine_last_value allocated.partition.firstInput).trans
      (Primitive.Spine.castPath_last_value result.traced.first_eq allocated.partition.quarters.first)
  rewrite [firstStart, firstFinish] at firstBlock
  have secondBlock := compared.second.errors_sum_eq
  have secondStart : (execution.third.seam.quarterSpine allocated.partition.secondInput).first.value =
      allocated.partition.quarters.second.first.value :=
    (execution.third.seam.quarterSpine_first_value allocated.partition.secondInput).trans
      (Primitive.Spine.castPath_first_value result.traced.second_eq allocated.partition.quarters.second)
  have secondFinish : (execution.third.seam.quarterSpine allocated.partition.secondInput).last.value =
      allocated.partition.quarters.second.last.value :=
    (execution.third.seam.quarterSpine_last_value allocated.partition.secondInput).trans
      (Primitive.Spine.castPath_last_value result.traced.second_eq allocated.partition.quarters.second)
  rewrite [secondStart, secondFinish] at secondBlock
  have thirdBlock := compared.third.errors_sum_eq
  have thirdStart : (execution.fourth.seam.quarterSpine allocated.partition.thirdInput).first.value =
      allocated.partition.quarters.third.first.value :=
    (execution.fourth.seam.quarterSpine_first_value allocated.partition.thirdInput).trans
      (Primitive.Spine.castPath_first_value result.traced.third_eq allocated.partition.quarters.third)
  have thirdFinish : (execution.fourth.seam.quarterSpine allocated.partition.thirdInput).last.value =
      allocated.partition.quarters.third.last.value :=
    (execution.fourth.seam.quarterSpine_last_value allocated.partition.thirdInput).trans
      (Primitive.Spine.castPath_last_value result.traced.third_eq allocated.partition.quarters.third)
  rewrite [thirdStart, thirdFinish] at thirdBlock
  have fourthBlock := compared.fourth.errors_sum_eq
  have fourthStart : (execution.closing.quarterSpine allocated.partition.fourthInput).first.value =
      allocated.partition.quarters.fourth.first.value :=
    (execution.closing.quarterSpine_first_value allocated.partition.fourthInput).trans
      (Primitive.Spine.castPath_first_value result.traced.fourth_eq allocated.partition.quarters.fourth)
  have fourthFinish : (execution.closing.quarterSpine allocated.partition.fourthInput).last.value =
      allocated.partition.quarters.fourth.last.value :=
    (execution.closing.quarterSpine_last_value allocated.partition.fourthInput).trans
      (Primitive.Spine.castPath_last_value result.traced.fourth_eq allocated.partition.quarters.fourth)
  rewrite [fourthStart, fourthFinish] at fourthBlock
  have first_second := congrArg (fun vertex : Primitive.Vertex (row.expression parameter)
    _ execution.second.seam.owner allocated.partition.observed.observations.accuracy => vertex.value)
      allocated.partition.quarters.first_second
  have second_third := congrArg (fun vertex : Primitive.Vertex (row.expression parameter)
    _ execution.third.seam.owner allocated.partition.observed.observations.accuracy => vertex.value)
      allocated.partition.quarters.second_third
  have third_fourth := congrArg (fun vertex : Primitive.Vertex (row.expression parameter)
    _ execution.fourth.seam.owner allocated.partition.observed.observations.accuracy => vertex.value)
      allocated.partition.quarters.third_fourth
  have first := congrArg (fun vertex : Primitive.Vertex (row.expression parameter)
    _ sourceOwner allocated.partition.observed.observations.accuracy => vertex.value)
      allocated.partition.quarters.first_eq
  have last := congrArg (fun vertex : Primitive.Vertex (row.expression parameter)
    _ execution.returnOwner allocated.partition.observed.observations.accuracy => vertex.value)
      allocated.partition.quarters.last_eq
  have blocks := congrArg₂ (fun first rest : Canonical => first + rest) firstBlock
    (congrArg₂ (fun second rest : Canonical => second + rest) secondBlock
      (congrArg₂ (fun third fourth : Canonical => third + fourth) thirdBlock fourthBlock))
  have telescope (a b c d e f g h start finish i j k l : Canonical)
      (firstSecond : c = b) (secondThird : e = d) (thirdFourth : g = f)
      (firstStart : a = start) (lastFinish : h = finish) :
      (b - a - i) + ((d - c - j) + ((f - e - k) + (h - g - l))) =
        finish - start - (i + (j + (k + l))) := by
    rewrite [firstSecond, secondThird, thirdFourth, firstStart, lastFinish]
    ring1
  exact (sumAppend compared.first.errors compared.second.errors compared.third.errors compared.fourth.errors).trans
    (blocks.trans ((telescope _ _ _ _ _ _ _ _ _ _ _ _ _ _
      first_second second_third third_fourth first last).trans
        (congrArg (fun total : Canonical =>
          allocated.partition.observed.observations.observed.last.value -
            allocated.partition.observed.observations.observed.first.value - total)
          (sumAppend compared.first.integrals compared.second.integrals
            compared.third.integrals compared.fourth.integrals).symm)))

/-- The actual flattened full-block count pays this SAME whole-spine return residual and original affine source sum. -/
theorem return_error_le : Norm.Basic.normSq
    (allocated.partition.observed.observations.observed.last.value -
      allocated.partition.observed.observations.observed.first.value -
        Norm.Sum.Basic.gaussianSum compared.integrals) ≤
      (allocated.count : Rational) * ((allocated.count : Rational) * (26 * allocated.targets.endpoint)) := by
  have paid := Norm.Sum.Bounds.normSq_sum_le compared.errors (26 * allocated.targets.endpoint) compared.errors_bounded
  rewrite [compared.errors_sum_eq, compared.errors_count] at paid
  exact paid

/-- The SAME original literal closing comparison and actual full-block errors pay the original affine source sum.

The return residual and the singular stored closing jump contain exactly
the same old last/first values. Their signed cancellation uses the original
Closing.Comparison law; no new join or primitive observation is acquired.
-/
theorem integral_error_le : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum compared.integrals) ≤
    PreparedParents.Trace.closedScale allocated.count * allocated.targets.endpoint := by
  have closing := allocated.partition.observed.closing.integral_le_return_residual
    (Norm.Sum.Basic.gaussianSum compared.integrals)
  have quarterSmall : (PreparedParents.Trace.localAccuracy allocated.targets).tolerance ≤
      allocated.targets.endpoint :=
    Order.Field.divide_le_self allocated.targets.endpoint_positive.le
      (of_decide_eq_true rfl : (1 : Rational) ≤ 4)
  have localSmall : allocated.partition.observed.observations.accuracy.tolerance ≤ allocated.targets.endpoint :=
    (congrArg AccuracyRequest.tolerance allocated.observed_accuracy).trans_le quarterSmall
  have payment := closing.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct compared.return_error_le localSmall)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))
  have scalar (n t : Rational) : 2 * (n * (n * (26 * t)) + t) = 2 * (n * (n * 26) + 1) * t := by ring1
  have coefficient := scalar (allocated.count : Rational) allocated.targets.endpoint
  rewrite [← PreparedParents.Trace.telescopeScale_eq allocated.count] at coefficient
  change _ = PreparedParents.Trace.closedScale allocated.count * allocated.targets.endpoint at coefficient
  exact payment.trans_eq coefficient

/-- The selected allocation pays the retained affine source integral sum without an aggregate premise. -/
theorem integral_error_lt : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum compared.integrals) < request.tolerance :=
  compared.integral_error_le.trans_lt allocated.source_payment

end Compared

end Closure.Result.Requested

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
