module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Sample.Query

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Polynomial
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Stored projections and whole factory readback for two-target query samples -/

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

/-- The SAME actual old source bundle and its original retained sample. -/
@[expose, macro_inline]
def old : Old (sourcePrepared := sourcePrepared) (time := time) :=
  answer.1.val

/-- The first absolute Step constructed from that identical old sample. -/
@[expose, macro_inline]
def first : First (sourcePrepared := sourcePrepared) (time := time) (firstOffset := firstOffset) answer.old :=
  answer.2.1.val

/-- The second absolute Step constructed independently from that identical old sample. -/
@[expose, macro_inline]
def last : Last (sourcePrepared := sourcePrepared) (time := time) (lastOffset := lastOffset) answer.old :=
  answer.2.2.1.val

/-- The SAME actual first-target observation bundle, without querying it again. -/
@[expose, macro_inline]
def firstObserved : FirstObserved (firstFrame := firstFrame) (firstPrepared := firstPrepared) (firstInput :=
  firstInput) :=
  answer.2.2.2.1.val

/-- The SAME independently paid second-target observation bundle. -/
@[expose, macro_inline]
def lastObserved : LastObserved (lastFrame := lastFrame) (lastPrepared := lastPrepared) (lastInput :=
  lastInput) :=
  answer.2.2.2.2.1.val

/-- The original retained direct Query on the first actual target child. -/
@[expose, macro_inline]
def firstDirect : FirstDirect (firstChild := firstChild) (firstInput := firstInput) (firstInputInside :=
  firstInputInside) :=
  answer.2.2.2.2.2.1.val

/-- The original retained direct Query on the second actual target child. -/
@[expose, macro_inline]
def lastDirect : LastDirect (lastChild := lastChild) (lastInput := lastInput) (lastInputInside :=
  lastInputInside) :=
  answer.2.2.2.2.2.2.1.val

/-- The SAME new local-difference root requests, scalar core and arithmetic reobservations. -/
@[expose, macro_inline]
def request : Request (sourcePrepared := sourcePrepared) (time := time)
    (firstOffset := firstOffset) (lastOffset := lastOffset)
      (unit := unit) (nonzero := nonzero) (spatial := spatial) answer.old answer.first answer.last :=
  answer.2.2.2.2.2.2.2.1.val

/-- The SAME actual ten-comparison bank on both original observation bundles. -/
@[expose, macro_inline]
def comparisons : Comparisons
    (sourcePrepared := sourcePrepared) (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
    (time := time) (firstInput := firstInput) (lastInput := lastInput)
    (firstOffset := firstOffset) (lastOffset := lastOffset)
      (unit := unit) (nonzero := nonzero) (spatial := spatial)
    answer.old answer.first answer.last answer.firstObserved answer.lastObserved answer.request :=
  answer.2.2.2.2.2.2.2.2.1.val

/-- The four already materialized polynomial Taylor certificates on those actual queries. -/
@[expose, macro_inline]
def certificates : Certificates (firstOffset := firstOffset) (lastOffset := lastOffset) :=
  answer.2.2.2.2.2.2.2.2.2.val

/-- The stored polynomial rows retain their complete factory on the same original observations.

All original owners, bounded inputs, caches and coefficient indices are
quantified together, preserving their original dependency order.
-/
@[expose] def CertificateFactoryLaw : Prop :=
  ∀
    {parameter firstOffset lastOffset : Canonical}
    {frame : Paths.Frame parameter}
    {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {patch : PreparedPatch parent}
    {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2}
    {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    {sourcePrepared : PreparedParent patch count floor covered targets}
    {range : Variation.Point.Range (patch.neighborhood count)}
    {firstFrame : Paths.Frame (parameter + firstOffset)}
    {lastFrame : Paths.Frame (parameter + lastOffset)}
    {firstAdmitted : Norm.Basic.normSq firstOffset ≤ range.shiftedBound}
    {lastAdmitted : Norm.Basic.normSq lastOffset ≤ range.shiftedBound}
    {firstStrip : Norm.Basic.normSq firstOffset ≤ range.stripBound}
    {lastStrip : Norm.Basic.normSq lastOffset ≤ range.stripBound}
    {firstWidth lastWidth : AccuracyRequest}
    {firstLinked : Linked sourcePrepared range firstFrame firstAdmitted firstStrip firstWidth}
    {lastLinked : Linked sourcePrepared range lastFrame lastAdmitted lastStrip lastWidth}
    {firstAligned : Acquisition.Segment.RootComparisons.Alignment
      firstLinked.comparison.paths firstLinked.comparison.firstReference}
    {lastAligned : Acquisition.Segment.RootComparisons.Alignment
      lastLinked.comparison.paths lastLinked.comparison.firstReference}
    {firstChild : CenteredEdge (Fibre.frameCurve firstFrame) basis}
    {lastChild : CenteredEdge (Fibre.frameCurve lastFrame) basis}
    {firstPatch : PreparedPatch firstChild}
    {lastPatch : PreparedPatch lastChild}
    {firstCount lastCount firstFloor lastFloor : Nat}
    {firstCovered : (firstPatch.neighborhood firstCount).box.Contains (firstChild.edge.point 1)}
    {lastCovered : (lastPatch.neighborhood lastCount).box.Contains (lastChild.edge.point 1)}
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish}
    {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets firstPath firstStage}
    {lastTargets : CellEndpoints.Targets lastPath lastStage}
    {firstPrepared : PreparedParent firstPatch firstCount firstFloor firstCovered firstTargets}
    {lastPrepared : PreparedParent lastPatch lastCount lastFloor lastCovered lastTargets}
    {firstIndex : Fin firstLinked.shifted.acquired.mesh.edges.length}
    {lastIndex : Fin lastLinked.shifted.acquired.mesh.edges.length}
    {firstChild_eq : firstChild = firstLinked.shifted.childAt (firstLinked.shifted.dyadicIndex firstIndex)}
    {lastChild_eq : lastChild = lastLinked.shifted.childAt (lastLinked.shifted.dyadicIndex lastIndex)}
    {time : Rational}
    {inside : 0 ≤ time ∧ time ≤ 1}
    {firstInside : (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).left.parameter ≤ time ∧
      time ≤ (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).right.parameter}
    {lastInside : (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).left.parameter ≤ time ∧
      time ≤ (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).right.parameter}
    {firstInput lastInput : Rational}
    {firstInput_eq : firstInput = Data.Rat.Interval.ConvexCombination.segmentParameter
      (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).left.parameter
      (firstLinked.shifted.acquired.mesh.edges[firstIndex.val]'firstIndex.isLt).right.parameter time}
    {lastInput_eq : lastInput = Data.Rat.Interval.ConvexCombination.segmentParameter
      (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).left.parameter
      (lastLinked.shifted.acquired.mesh.edges[lastIndex.val]'lastIndex.isLt).right.parameter time}
    {firstInputInside : 0 ≤ firstInput ∧ firstInput ≤ 1}
    {lastInputInside : 0 ≤ lastInput ∧ lastInput ≤ 1}
    {unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1}
    {nonzero : lastOffset - firstOffset ≠ 0}
    {spatial : AccuracyRequest}
    {firstPaid : ∀ channel : Fin 6, (firstPrepared.preparation.cell.models.cell channel).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance}
    {lastPaid : ∀ channel : Fin 6, (lastPrepared.preparation.cell.models.cell channel).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance}
    (answer : BetweenSample sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared firstIndex lastIndex firstChild_eq lastChild_eq time inside firstInside lastInside
    firstInput lastInput firstInput_eq lastInput_eq firstInputInside lastInputInside unit nonzero spatial
    firstPaid lastPaid)
    (order coordinate : Fin 2),
    answer.certificates order coordinate =
      betweenPolynomialCertificate sourcePrepared answer.first answer.last firstPrepared lastPrepared
        answer.firstObserved answer.lastObserved answer.request.paid answer.comparisons order coordinate
        (answer.request.allowancePaid _ (firstPaid (Specification.Table.baseIndex order coordinate)))
        (answer.request.allowancePaid _ (lastPaid (Specification.Table.baseIndex order coordinate)))
        (answer.request.allowancePaid _ (firstPaid (Specification.Table.slopeIndex order coordinate)))

/-- The stored row keeps the whole original polynomial-certificate factory on its same retained comparisons. -/
theorem certificate_eq : CertificateFactoryLaw := by
  unfold CertificateFactoryLaw
  intro parameter firstOffset lastOffset frame basis parent patch count floor covered baseStart baseFinish
    original stage targets sourcePrepared range firstFrame lastFrame firstAdmitted lastAdmitted firstStrip
    lastStrip firstWidth lastWidth firstLinked lastLinked firstAligned lastAligned firstChild lastChild
    firstPatch lastPatch firstCount lastCount firstFloor lastFloor firstCovered lastCovered firstStart
    firstFinish lastStart lastFinish firstPath lastPath firstStage lastStage firstTargets lastTargets
    firstPrepared lastPrepared firstIndex lastIndex firstChild_eq lastChild_eq time inside firstInside
    lastInside firstInput lastInput firstInput_eq lastInput_eq firstInputInside lastInputInside unit nonzero
    spatial firstPaid lastPaid answer order coordinate
  exact
    (congrArg (fun certificates : Data.Vector
        (Data.Vector (Quadratic.Basic.Certificate (lastOffset - firstOffset)) 2) 2 =>
      certificates order coordinate) answer.2.2.2.2.2.2.2.2.2.property).trans
      (betweenPolynomialRows_apply
        (sourcePrepared := sourcePrepared) (firstStep := answer.first) (lastStep := answer.last)
        (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
        (firstObserved := answer.firstObserved) (lastObserved := answer.lastObserved)
        (paid := answer.request.paid) (retained := answer.comparisons) (order := order) (coordinate := coordinate)
        (fun channel => answer.request.allowancePaid _ (firstPaid channel))
        (fun channel => answer.request.allowancePaid _ (lastPaid channel)))

end BetweenSample

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
