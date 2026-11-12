module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Sample.Readback

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Polynomial
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Coefficient readbacks and factor bounds for retained two-target query samples -/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace BetweenSample

/-- The fixed rational multiplier of each polynomial-row factor is nonnegative. -/
private theorem four_nonnegative : (0 : Rational) ≤ 4 := by decide +kernel

end BetweenSample

variable {parameter firstOffset lastOffset : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (sourcePrepared : PreparedParent patch count floor covered targets)
    {range : Variation.Point.Range (patch.neighborhood count)}
    {firstFrame : Paths.Frame (parameter + firstOffset)} {lastFrame : Paths.Frame (parameter + lastOffset)}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ range.shiftedBound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ range.shiftedBound}
    {firstStrip : Norm.Basic.normSq firstOffset ≤ range.stripBound}
    {lastStrip : Norm.Basic.normSq lastOffset ≤ range.stripBound} {firstWidth lastWidth : AccuracyRequest}
    (firstLinked : Linked sourcePrepared range firstFrame firstAdmitted firstStrip firstWidth)
    (lastLinked : Linked sourcePrepared range lastFrame lastAdmitted lastStrip lastWidth)
    (firstAligned : Acquisition.Segment.RootComparisons.Alignment
      firstLinked.comparison.paths firstLinked.comparison.firstReference)
    (lastAligned : Acquisition.Segment.RootComparisons.Alignment
      lastLinked.comparison.paths lastLinked.comparison.firstReference)
    {firstChild : CenteredEdge (Fibre.frameCurve firstFrame) basis}
    {lastChild : CenteredEdge (Fibre.frameCurve lastFrame) basis}
    {firstPatch : PreparedPatch firstChild} {lastPatch : PreparedPatch lastChild}
    {firstCount lastCount firstFloor lastFloor : Nat}
    {firstCovered : (firstPatch.neighborhood firstCount).box.Contains (firstChild.edge.point 1)}
    {lastCovered : (lastPatch.neighborhood lastCount).box.Contains (lastChild.edge.point 1)}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat} {firstTargets : CellEndpoints.Targets firstPath firstStage}
    {lastTargets : CellEndpoints.Targets lastPath lastStage}
    (firstPrepared : PreparedParent firstPatch firstCount firstFloor firstCovered firstTargets)
    (lastPrepared : PreparedParent lastPatch lastCount lastFloor lastCovered lastTargets)
    (firstIndex : Fin firstLinked.shifted.acquired.mesh.edges.length)
    (lastIndex : Fin lastLinked.shifted.acquired.mesh.edges.length)
    (firstChild_eq : firstChild = firstLinked.shifted.childAt (firstLinked.shifted.dyadicIndex firstIndex))
    (lastChild_eq : lastChild = lastLinked.shifted.childAt (lastLinked.shifted.dyadicIndex lastIndex))
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1)
    (firstInside : (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).left.parameter ≤ time ∧
      time ≤ (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).right.parameter)
    (lastInside : (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).left.parameter ≤ time ∧
      time ≤ (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).right.parameter)
    (firstInput lastInput : Rational)
    (firstInput_eq : firstInput = Data.Rat.Interval.ConvexCombination.segmentParameter
      (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).left.parameter
      (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).right.parameter time)
    (lastInput_eq : lastInput = Data.Rat.Interval.ConvexCombination.segmentParameter
      (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).left.parameter
      (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).right.parameter time)
    (firstInputInside : 0 ≤ firstInput ∧ firstInput ≤ 1) (lastInputInside : 0 ≤ lastInput ∧ lastInput ≤ 1)
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest)
    (firstPaid : ∀ channel : Fin 6, (firstPrepared.preparation.cell.models.cell channel).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)
    (lastPaid : ∀ channel : Fin 6, (lastPrepared.preparation.cell.models.cell channel).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)

namespace BetweenSample

variable {sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared}
    {firstIndex lastIndex firstChild_eq lastChild_eq time inside firstInside lastInside firstInput lastInput}
    {firstInput_eq lastInput_eq firstInputInside lastInputInside unit nonzero spatial firstPaid lastPaid}
    (answer : BetweenSample sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared firstIndex lastIndex firstChild_eq lastChild_eq time inside firstInside lastInside
    firstInput lastInput firstInput_eq lastInput_eq firstInputInside lastInputInside unit nonzero spatial
    firstPaid lastPaid)

/-- The base reads its SAME original target polynomial at the retained firstInput query time. -/
theorem certificate_base (order coordinate : Fin 2) :
    (answer.certificates order coordinate).base =
      Evaluation.eval (firstPrepared.preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).polynomial (Cast.Path.ofCoordinate firstInput) :=
  (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.base)
    (answer.certificate_eq order coordinate)).trans
      (betweenPolynomialCertificate_base
        (sourcePrepared := sourcePrepared) (firstStep := answer.first) (lastStep := answer.last)
        (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
        (firstObserved := answer.firstObserved) (lastObserved := answer.lastObserved)
        (paid := answer.request.paid) (retained := answer.comparisons) (order := order) (coordinate := coordinate)
        (answer.request.allowancePaid _ (firstPaid (Specification.Table.baseIndex order coordinate)))
        (answer.request.allowancePaid _ (lastPaid (Specification.Table.baseIndex order coordinate)))
        (answer.request.allowancePaid _ (firstPaid (Specification.Table.slopeIndex order coordinate))))

/-- The output reads its SAME original target polynomial at the retained lastInput query time. -/
theorem certificate_output (order coordinate : Fin 2) :
    (answer.certificates order coordinate).output =
      Evaluation.eval (lastPrepared.preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).polynomial (Cast.Path.ofCoordinate lastInput) :=
  (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.output)
    (answer.certificate_eq order coordinate)).trans
      (betweenPolynomialCertificate_output
        (sourcePrepared := sourcePrepared) (firstStep := answer.first) (lastStep := answer.last)
        (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
        (firstObserved := answer.firstObserved) (lastObserved := answer.lastObserved)
        (paid := answer.request.paid) (retained := answer.comparisons) (order := order) (coordinate := coordinate)
        (answer.request.allowancePaid _ (firstPaid (Specification.Table.baseIndex order coordinate)))
        (answer.request.allowancePaid _ (lastPaid (Specification.Table.baseIndex order coordinate)))
        (answer.request.allowancePaid _ (firstPaid (Specification.Table.slopeIndex order coordinate))))

/-- The slope reads its SAME original target polynomial at the retained firstInput query time. -/
theorem certificate_slope (order coordinate : Fin 2) :
    (answer.certificates order coordinate).slope =
      Evaluation.eval (firstPrepared.preparation.cell.models.cell
        (Specification.Table.slopeIndex order coordinate)).polynomial (Cast.Path.ofCoordinate firstInput) :=
  (congrArg (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.slope)
    (answer.certificate_eq order coordinate)).trans
      (betweenPolynomialCertificate_slope
        (sourcePrepared := sourcePrepared) (firstStep := answer.first) (lastStep := answer.last)
        (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
        (firstObserved := answer.firstObserved) (lastObserved := answer.lastObserved)
        (paid := answer.request.paid) (retained := answer.comparisons) (order := order) (coordinate := coordinate)
        (answer.request.allowancePaid _ (firstPaid (Specification.Table.baseIndex order coordinate)))
        (answer.request.allowancePaid _ (lastPaid (Specification.Table.baseIndex order coordinate)))
        (answer.request.allowancePaid _ (firstPaid (Specification.Table.slopeIndex order coordinate))))

/-- The SAME polynomial certificate has one computed original-box ceiling independent of both absolute times.

Both target models and numerical certificates are unchanged. The actual
source Cell factory transports its scalar patch ceiling to the original
retained neighborhood; all original query state and evaluator owners remain
in answer. No bound for a changing later patch or selected-node minimum is
used, and no loose recorded factor is replaced.
-/
theorem certificate_factor_le (order coordinate : Fin 2) :
    (answer.certificates order coordinate).factor ≤
      4 * (Variation.Point.Step.Joint.rowCeiling (patch.neighborhood count) 0 order coordinate +
        7 / 2 + 7 / 2 + 7 / 2) := by
  have factor := (congrArg
    (fun certificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) => certificate.factor)
      (answer.certificate_eq order coordinate)).trans
        (betweenPolynomialCertificate_factor
          (sourcePrepared := sourcePrepared) (firstStep := answer.first) (lastStep := answer.last)
          (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
          (firstObserved := answer.firstObserved) (lastObserved := answer.lastObserved)
          (paid := answer.request.paid) (retained := answer.comparisons) (order := order) (coordinate := coordinate)
          (answer.request.allowancePaid _ (firstPaid (Specification.Table.baseIndex order coordinate)))
          (answer.request.allowancePaid _ (lastPaid (Specification.Table.baseIndex order coordinate)))
          (answer.request.allowancePaid _ (firstPaid (Specification.Table.slopeIndex order coordinate))))
  have pointInside := sourcePrepared.preparation.cell.models.coordinate.point_inside
    sourcePrepared.preparation.cell.startInside sourcePrepared.preparation.cell.finishInside inside.1 inside.2
  have numerical := answer.request.row_factor_le order coordinate pointInside
  have originalPatch := congrArg
    (fun cell : Source.Cell (parameter := parameter) (liftedCell parent) =>
      Variation.Point.Step.Joint.rowCeiling cell.patch 0 order coordinate) sourcePrepared.preparation.cell_eq
  have fixed : (answer.request.paid.rowCertificate order coordinate).factor ≤
      Variation.Point.Step.Joint.rowCeiling (patch.neighborhood count) 0 order coordinate :=
    numerical.trans_eq originalPatch
  exact factor.trans_le (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.add_le_add_direct fixed
          (Order.Basic.le_refl (7 / 2)))
        (Order.Basic.le_refl (7 / 2)))
      (Order.Basic.le_refl (7 / 2))) four_nonnegative)

end BetweenSample

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
