module

import Purelib.Data.Nat.Order
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial.Occurrences.Requested
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Origin.Quotients
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedGeometry.Between.Reference.Accuracy
import Purelib.Calculus.Jet.DifferenceQuotient
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Approximation.AccuracyRequest.Scaling
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Actual ordered-period base readings in the retained moving-source quotient

The original source, zero member, moving member and paid source-quotient
cache are given unchanged. One original model-stream comparison computes
its two increment-dependent floors before readings. Its source floor is
maxed with the existing quotient floor, while the period and moving stages
remain independent. The generic quotient perturbation derives the final
bound from those actual caches, without output-name resampling.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib.Data.Nat

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (Comparison)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents (ParameterRange sources)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt (Requested OccurrenceCompletion)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested (LocalMember)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source} {spine : PolynomialSpine walk}
    {parent : CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1))}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) (PeriodMatrix.standardDifferential (0 : Fin 1)))}
    {same : spine.parents = parent :: parents} {current floor rootStage : Nat} {reference : AccuracyRequest}
    {requested : Requested (spine.sourceCovered same) (spine.sourceChain same) current floor rootStage reference}
    {ranges : ParameterRange (spine.sourceCovered same)} {allocation : ParameterRange.StripAllocation ranges}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat}
    (actual : SynchronizedPeriodJet frame)
    {increment : Canonical} {zeroAdmitted : Norm.Basic.normSq (0 : Canonical) ≤ allocation.bound}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    (zero : LocalMember requested ranges allocation (spine.sourceRoots same) widths
      targetCurrent targetFloor targetRootStage 0 zeroAdmitted)
    (last : LocalMember requested ranges allocation (spine.sourceRoots same) widths
      targetCurrent targetFloor targetRootStage increment admitted)

/-- Every later source, period and moving-stage reading satisfies the actual value-zero period quotient bound.

The source first channel remains at its original source index. The base is
the original walk's independent period-model reading, and the output is the
SAME supplied completed moving-stage cell list. Its whole factory remains
an explicit argument for each permitted later moving stage.
-/
@[expose] def PeriodQuotientBounds (accuracy : AccuracyRequest)
    (sourceFloor periodFloor movingFloor : Nat) : Prop :=
  ∀ (sourceIndex periodIndex movingIndex : Nat),
    sourceFloor ≤ sourceIndex → periodFloor ≤ periodIndex → movingFloor ≤ movingIndex →
    ∀ (retained : LocalMember.StageData last movingIndex), retained = (last.completed movingIndex).val →
      Norm.Basic.normSq
        (((PathModel.mk ((sources last.member.requested.request.covered retained.1.preparations
            last.member.requested.request.chain).cells (Jets.Specification.Table.valueIndex 0))).integralSample -
          ((walk.program 0).integral.model periodIndex).integralSample) / increment -
          ((actual.first 0).integral.model sourceIndex).integralSample) < accuracy.tolerance

/-- The actual paid source quotient and original period comparison pay every later three-index quotient internally.

The source-quotient cache pays one sixteenth of the error. The actual
comparison pays the base discrepancy by that same share times increment
quadrance; reversing its original source-minus-period orientation only
negates the difference. The slope stays unchanged, so its perturbation is
zero. The original radius payment supplies the unit increment needed by
the generic quotient perturbation.
-/
theorem periodQuotient_accurate (accuracy : AccuracyRequest) (nonzero : increment ≠ 0) (originStart : Nat)
    (small : Norm.Basic.normSq increment ≤
      (LocalMember.sourceQuotientRequest
        (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
        (count := 1) (parent := parent) (parents := parents) (covered := spine.sourceCovered same)
        (ranges := ranges) (allocation := allocation) (accuracy.divide 16 (by decide +kernel))).tolerance)
    (paid : LocalMember.SourceQuotientFloors
      (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (count := 1) (parent := parent) (parents := parents) (covered := spine.sourceCovered same)
      (chain := spine.sourceChain same) (current := current) (floor := floor) (rootStage := rootStage)
      (reference := reference) (source := requested) (ranges := ranges) (allocation := allocation)
      (root := ownerName owner) (roots := spine.sourceRoots same) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      actual zero last (accuracy.divide 16 (by decide +kernel)) nonzero originStart)
    {sourceStart periodStart : Nat}
    (compared : Comparison (actual.value 0).integral.geometric.toApproximation
      (walk.program 0).integral.geometric.toApproximation sourceStart periodStart
      ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)) :
    PeriodQuotientBounds
      (parameter := parameter) (frame := frame) (ambient := ambient) (grid := grid) (base := base)
      (owner := owner) (source := source) (walk := walk) (spine := spine) (parent := parent) (parents := parents)
      (same := same) (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (requested := requested) (ranges := ranges) (allocation := allocation) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      (increment := increment) (admitted := admitted) (actual := actual) (last := last) accuracy
      (Nat.max paid.2.2.val.1 compared.leftIndex) compared.rightIndex paid.2.2.val.2 := by
  intro sourceIndex periodIndex movingIndex sourceAfter periodAfter movingAfter retained factory
  let share := accuracy.divide 16 (by decide +kernel)
  let base := ((walk.program 0).integral.model periodIndex).integralSample
  let oldBase := ((actual.value 0).integral.model sourceIndex).integralSample
  let slope := ((actual.first 0).integral.model sourceIndex).integralSample
  let output := (PathModel.mk ((sources last.member.requested.request.covered retained.1.preparations
    last.member.requested.request.chain).cells (Jets.Specification.Table.valueIndex 0))).integralSample
  have sourcePaid := (Order.le_max_left paid.2.2.val.1 compared.leftIndex).trans sourceAfter
  have comparisonPaid := (Order.le_max_right paid.2.2.val.1 compared.leftIndex).trans sourceAfter
  have original := LocalMember.stageQuotient_lt
    (offset := increment) (admitted := admitted) (zeroAdmitted := zeroAdmitted)
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
    (count := 1) (parent := parent) (parents := parents) (covered := spine.sourceCovered same)
    (chain := spine.sourceChain same) (current := current) (floor := floor) (rootStage := rootStage)
    (reference := reference) (source := requested) (ranges := ranges) (allocation := allocation)
    (root := ownerName owner) (roots := spine.sourceRoots same) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    last actual zero share nonzero originStart paid
  have originalPaid : Norm.Basic.normSq ((output - oldBase) / increment - slope) < accuracy.tolerance / 16 :=
    original 0 0 sourceIndex movingIndex sourcePaid movingAfter retained factory
  have comparison : Norm.Basic.normSq (oldBase - base) <
      (accuracy.tolerance / 16) * Norm.Basic.normSq increment :=
    compared.close comparisonPaid periodAfter
  have basePaid : Norm.Basic.normSq (base - oldBase) <
      (accuracy.tolerance / 16) * Norm.Basic.normSq increment :=
    ((congrArg Norm.Basic.normSq (Gaussian.Field.sub_eq_neg_sub base oldBase)).trans
      (Norm.Basic.normSq_neg (oldBase - base))).trans_lt comparison
  have sharePositive : 0 < accuracy.tolerance / 16 := share.positive
  have slopePaid : Norm.Basic.normSq (slope - slope) <
      (accuracy.tolerance / 16) * Norm.Basic.normSq increment := by
    rewrite [Basic.sub_self, Norm.Basic.normSq_zero]
    exact Order.Arithmetic.mul_pos_direct sharePositive (Norm.Basic.normSq_pos nonzero)
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    small.trans ((LocalMember.sourceQuotientRequest_le_reference
      (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (count := 1) (parent := parent) (parents := parents) (covered := spine.sourceCovered same)
      (ranges := ranges) (allocation := allocation) share).trans
      (Jets.Source.Cell.PreparedParents.ShiftedGeometry.BetweenRows.referenceRequest_le_unit
        (covered := spine.sourceCovered same) (share.divide 16 (by decide +kernel))))
  exact Calculus.Jet.DifferenceQuotient.perturbation_lt accuracy increment base output slope oldBase slope
    nonzero unit basePaid slopePaid originalPaid

/-- Select the actual source/period model comparison once before exposing its all-later quotient certificate.

The supplied whole source jet factory and original paid zero/member cache
are consumed unchanged. The returned Comparison is the same executable
sourcePeriodEquivalent procedure at tolerance/16 times increment quadrance, with its complete
factory equality. Only the source floor is enlarged by the original
quotient floor; period and moving stages remain independent.
-/
def selectPeriodQuotient (completed : requested.attempt.OccurrenceFamily)
    (factory : actual = OccurrenceCompletion.jet (parameter := parameter) (frame := frame)
      (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor) (rootStage := rootStage)
      (spine.sourceCovered same) (spine.sourceChain same) (fun stage => (completed stage).val))
    (accuracy : AccuracyRequest) (nonzero : increment ≠ 0) (originStart : Nat)
    (small : Norm.Basic.normSq increment ≤
      (LocalMember.sourceQuotientRequest
        (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
        (count := 1) (parent := parent) (parents := parents) (covered := spine.sourceCovered same)
        (ranges := ranges) (allocation := allocation) (accuracy.divide 16 (by decide +kernel))).tolerance)
    (paid : LocalMember.SourceQuotientFloors
      (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
      (count := 1) (parent := parent) (parents := parents) (covered := spine.sourceCovered same)
      (chain := spine.sourceChain same) (current := current) (floor := floor) (rootStage := rootStage)
      (reference := reference) (source := requested) (ranges := ranges) (allocation := allocation)
      (root := ownerName owner) (roots := spine.sourceRoots same) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      actual zero last (accuracy.divide 16 (by decide +kernel)) nonzero originStart)
    (sourceStart periodStart : Nat) :
    { compared : Comparison (actual.value 0).integral.geometric.toApproximation
        (walk.program 0).integral.geometric.toApproximation sourceStart periodStart
        ((accuracy.tolerance / 16) * Norm.Basic.normSq increment) //
      compared = (spine.sourcePeriodEquivalent
        (parameter := parameter) (frame := frame) (walk := walk) (parent := parent) (parents := parents)
        (current := current) (floor := floor) (rootStage := rootStage) (accuracy := reference)
        same requested completed actual factory).compare sourceStart periodStart
        ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)
        (Order.Arithmetic.mul_pos_direct
          (accuracy.divide 16 (by decide +kernel)).positive (Norm.Basic.normSq_pos nonzero)) ∧
      PeriodQuotientBounds
      (parameter := parameter) (frame := frame) (ambient := ambient) (grid := grid) (base := base)
      (owner := owner) (source := source) (walk := walk) (spine := spine) (parent := parent) (parents := parents)
      (same := same) (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
      (requested := requested) (ranges := ranges) (allocation := allocation) (widths := widths)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      (increment := increment) (admitted := admitted) (actual := actual) (last := last) accuracy
        (Nat.max paid.2.2.val.1 compared.leftIndex) compared.rightIndex paid.2.2.val.2 } :=
  let compared := (spine.sourcePeriodEquivalent
    (parameter := parameter) (frame := frame) (walk := walk) (parent := parent) (parents := parents)
    (current := current) (floor := floor) (rootStage := rootStage) (accuracy := reference)
    same requested completed actual factory).compare sourceStart periodStart
    ((accuracy.tolerance / 16) * Norm.Basic.normSq increment)
    (Order.Arithmetic.mul_pos_direct
      (accuracy.divide 16 (by decide +kernel)).positive (Norm.Basic.normSq_pos nonzero))
  ⟨compared, rfl, periodQuotient_accurate
    (parameter := parameter) (frame := frame) (ambient := ambient) (grid := grid) (base := base)
    (owner := owner) (source := source) (walk := walk) (spine := spine) (parent := parent) (parents := parents)
    (same := same) (current := current) (floor := floor) (rootStage := rootStage) (reference := reference)
    (requested := requested) (ranges := ranges) (allocation := allocation) (widths := widths)
    (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
    (increment := increment) (zeroAdmitted := zeroAdmitted) (admitted := admitted)
    (actual := actual) (zero := zero) (last := last) accuracy nonzero originStart small paid compared⟩

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
