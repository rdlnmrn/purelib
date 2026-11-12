module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Sample
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Between.Dyadic
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Refinement.Parameters
public import Purelib.Integration.Polynomial.Gaussian.Cell.ParameterVariation
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs.Cells
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Actual common-dyadic Taylor integrals between two absolute targets

Both retained acquisitions remain over the same original source patch.
The stored refinement pair derives the query normalization and all physical
endpoint incidences. Three existing restriction banks supply the actual
base, output and slope polynomial integrals. One original Sample family
provides every pointwise Taylor certificate without a later Range payment.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Interval.ConvexCombination
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

/-- The computed polynomial factor ceiling on the SAME fixed original patch for an adjacent derivative row. -/
@[expose] def betweenPointwiseCeiling
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} (patch : PreparedPatch parent) (count : Nat)
    (order coordinate : Fin 2) : Rational :=
  4 * (Variation.Point.Step.Joint.rowCeiling (patch.neighborhood count) 0 order coordinate +
    7 / 2 + 7 / 2 + 7 / 2)

/-- The actual fixed original patch computes a nonnegative four-row polynomial ceiling. -/
theorem betweenPointwiseCeiling_nonnegative
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} (patch : PreparedPatch parent) (count : Nat)
    (order coordinate : Fin 2) : 0 ≤ betweenPointwiseCeiling patch count order coordinate := by
  have base := Variation.Point.Step.Joint.rowCeiling_nonnegative (patch.neighborhood count) 0 order coordinate
  have half : (0 : Rational) ≤ 7 / 2 := by decide +kernel
  have total := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.add_le_add_direct (Order.Arithmetic.add_le_add_direct base half) half) half
  have nonnegative : 0 ≤ Variation.Point.Step.Joint.rowCeiling (patch.neighborhood count) 0 order coordinate +
      7 / 2 + 7 / 2 + 7 / 2 :=
    (show (0 : Rational) = 0 + 0 + 0 + 0 by ring1).trans_le total
  exact Order.Arithmetic.mul_nonneg_direct (show (0 : Rational) ≤ 4 by decide +kernel) nonnegative

/-- The fixed physical parent and its original patch compute the full width-density for the actual integral row. -/
@[expose] def betweenDensity
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} (patch : PreparedPatch parent) (count : Nat)
    (order coordinate : Fin 2) : Rational :=
  2 * betweenPointwiseCeiling patch count order coordinate * cost parent

/-- The same original-parent density is nonnegative, including stationary physical parents. -/
theorem betweenDensity_nonnegative
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} (patch : PreparedPatch parent) (count : Nat)
    (order coordinate : Fin 2) : 0 ≤ betweenDensity patch count order coordinate :=
  Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (betweenPointwiseCeiling_nonnegative patch count order coordinate)) (cost_nonnegative parent)

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
    (index : Fin (dyadicEdges
      (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
        UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length)
    (pair : RefinementPair firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index)
    (firstSelected : firstChild = firstLinked.shifted.childAt
      (firstLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex pair.1)))
    (lastSelected : lastChild = lastLinked.shifted.childAt
      (lastLinked.shifted.dyadicIndex (refinementOccurrence.coarseIndex pair.2)))
    (unit : Norm.Basic.normSq (lastOffset - firstOffset) ≤ 1) (nonzero : lastOffset - firstOffset ≠ 0)
    (spatial : AccuracyRequest)
    (firstPaid : ∀ channel : Fin 6, (firstPrepared.preparation.cell.models.cell channel).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)
    (lastPaid : ∀ channel : Fin 6, (lastPrepared.preparation.cell.models.cell channel).localAllowance ≤
      (spatial.minimum (Variation.Sampling.incrementRequest (lastOffset - firstOffset) nonzero)).tolerance)

/-- The exact original Sample bundle at each bounded query of the SAME retained common refined edge.

This is the existing dependent function of BetweenSample values. Every
bundle retains its old answer, both Steps, both target observations/direct
Queries, genuinely new Reobservations, ten comparisons and four certificates
with all original whole factory equations. No desired error bound is input.
-/
@[expose] def BetweenDyadicSamples :=
  (input : Rational) → (inside : Cell.Primitive.unitInterval.Contains input) →
    BetweenSample sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      (refinementOccurrence.coarseIndex pair.1) (refinementOccurrence.coarseIndex pair.2)
      firstSelected lastSelected (refinementOccurrence.parameter pair.1 input)
      (refinementOccurrence.parameter_inside pair.1 input inside)
      (refinementOccurrence.parameter_bounds pair.1 (show (0 : Rational) ≤ 1 by decide +kernel) input inside)
      (pair.last_bounds (show (0 : Rational) ≤ 1 by decide +kernel) input inside)
      (refinementOccurrence.input pair.1 input) (refinementOccurrence.input pair.2 input)
      (refinementOccurrence.input_eq pair.1 input) (pair.last_input_eq input)
      (refinementOccurrence.input_inside pair.1 (show (0 : Rational) ≤ 1 by decide +kernel) input inside)
      (refinementOccurrence.input_inside pair.2 (show (0 : Rational) ≤ 1 by decide +kernel) input inside)
      unit nonzero spatial firstPaid lastPaid

/-- Construct the original query work once per invocation at the SAME actual common physical fraction.

The complete pair supplies both raw child occurrences and all normalized
query parameters. No endpoint/sheet equality, second acquisition, later
range or final pointwise certificate is supplied by a caller.
-/
def betweenDyadicSamples : BetweenDyadicSamples sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared index pair firstSelected lastSelected unit nonzero spatial firstPaid lastPaid :=
  fun input inside => sampleBetween sourcePrepared firstLinked lastLinked firstAligned lastAligned
    firstPrepared lastPrepared
      (refinementOccurrence.coarseIndex pair.1) (refinementOccurrence.coarseIndex pair.2)
      firstSelected lastSelected (refinementOccurrence.parameter pair.1 input)
      (refinementOccurrence.parameter_inside pair.1 input inside)
      (refinementOccurrence.parameter_bounds pair.1 (show (0 : Rational) ≤ 1 by decide +kernel) input inside)
      (pair.last_bounds (show (0 : Rational) ≤ 1 by decide +kernel) input inside)
      (refinementOccurrence.input pair.1 input) (refinementOccurrence.input pair.2 input)
      (refinementOccurrence.input_eq pair.1 input) (pair.last_input_eq input)
      (refinementOccurrence.input_inside pair.1 (show (0 : Rational) ≤ 1 by decide +kernel) input inside)
      (refinementOccurrence.input_inside pair.2 (show (0 : Rational) ≤ 1 by decide +kernel) input inside)
      unit nonzero spatial firstPaid lastPaid

variable
    (samples : BetweenDyadicSamples sourcePrepared firstLinked lastLinked firstAligned lastAligned
      firstPrepared lastPrepared index pair firstSelected lastSelected unit nonzero spatial firstPaid lastPaid)
    (order coordinate : Fin 2)
    (firstBase : ParameterEdge.Restrictions
      (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (refinementOccurrence.coarseEdge pair.1) lastLinked.shifted.acquired.mesh.depth)
    (lastBase : ParameterEdge.Restrictions
      (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (refinementOccurrence.coarseEdge pair.2) firstLinked.shifted.acquired.mesh.depth)
    (firstSlope : ParameterEdge.Restrictions
      (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate))
      (refinementOccurrence.coarseEdge pair.1) lastLinked.shifted.acquired.mesh.depth)

/-- Construct the actual three-restriction integral Taylor certificate on the SAME retained common physical child.

The original refinement pair derives all four endpoint equations. Its
bounded query parameters feed the supplied original Sample family, whose
actual polynomial certificates and original-box ceiling are read unchanged.
The existing Cell.ParameterVariation factory computes the integral residual.
No restriction, query, arithmetic comparison or continuation is rebuilt.
-/
def betweenDyadicCertificate : Quadratic.Basic.Certificate (lastOffset - firstOffset) := by
  let firstInner := refinementOccurrence.localIndex pair.1
  let lastInner := refinementOccurrence.localIndex pair.2
  let base := Cell.Restriction.model
    (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
    (firstBase.cache firstInner)
  let output := Cell.Restriction.model
    (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
    (lastBase.cache lastInner)
  let slope := Cell.Restriction.model
    (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate))
    (firstSlope.cache firstInner)
  let common := (dyadicEdges
    (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)[index.val]'index.isLt
  have firstFine := (refinementOccurrence.edge_eq pair.1).symm
  have lastFine := (refinementOccurrence.edge_eq pair.2).symm.trans
    (commutedIndex_edge firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index)
  have baseStart : base.start = parent.edge.point common.left.parameter :=
    (firstLinked.shifted.dyadicRestriction_start (refinementOccurrence.coarseIndex pair.1)
      lastLinked.shifted.acquired.mesh.depth firstInner firstSelected firstPrepared
      (Specification.Table.baseIndex order coordinate) firstBase).trans
        (congrArg (fun edge : ParameterEdge => parent.edge.point edge.left.parameter) firstFine)
  have baseFinish : base.finish = parent.edge.point common.right.parameter :=
    (firstLinked.shifted.dyadicRestriction_finish (refinementOccurrence.coarseIndex pair.1)
      lastLinked.shifted.acquired.mesh.depth firstInner firstSelected firstPrepared
      (Specification.Table.baseIndex order coordinate) firstBase).trans
        (congrArg (fun edge : ParameterEdge => parent.edge.point edge.right.parameter) firstFine)
  have outputStart : output.start = parent.edge.point common.left.parameter :=
    (lastLinked.shifted.dyadicRestriction_start (refinementOccurrence.coarseIndex pair.2)
      firstLinked.shifted.acquired.mesh.depth lastInner lastSelected lastPrepared
      (Specification.Table.baseIndex order coordinate) lastBase).trans
        (congrArg (fun edge : ParameterEdge => parent.edge.point edge.left.parameter) lastFine)
  have outputFinish : output.finish = parent.edge.point common.right.parameter :=
    (lastLinked.shifted.dyadicRestriction_finish (refinementOccurrence.coarseIndex pair.2)
      firstLinked.shifted.acquired.mesh.depth lastInner lastSelected lastPrepared
      (Specification.Table.baseIndex order coordinate) lastBase).trans
        (congrArg (fun edge : ParameterEdge => parent.edge.point edge.right.parameter) lastFine)
  have slopeStart : slope.start = parent.edge.point common.left.parameter :=
    (firstLinked.shifted.dyadicRestriction_start (refinementOccurrence.coarseIndex pair.1)
      lastLinked.shifted.acquired.mesh.depth firstInner firstSelected firstPrepared
      (Specification.Table.slopeIndex order coordinate) firstSlope).trans
        (congrArg (fun edge : ParameterEdge => parent.edge.point edge.left.parameter) firstFine)
  have slopeFinish : slope.finish = parent.edge.point common.right.parameter :=
    (firstLinked.shifted.dyadicRestriction_finish (refinementOccurrence.coarseIndex pair.1)
      lastLinked.shifted.acquired.mesh.depth firstInner firstSelected firstPrepared
      (Specification.Table.slopeIndex order coordinate) firstSlope).trans
        (congrArg (fun edge : ParameterEdge => parent.edge.point edge.right.parameter) firstFine)
  let pointwise := fun input inside => (samples input inside).certificates order coordinate
  have base_eq (input : Rational) (inside : Cell.Primitive.unitInterval.Contains input) :
      (pointwise input inside).base = Evaluation.eval base.polynomial (Cast.Path.ofCoordinate input) :=
    ((samples input inside).certificate_base order coordinate).trans
      (Cell.Restriction.eval_eq _ (firstBase.cache firstInner) input).symm
  have output_eq (input : Rational) (inside : Cell.Primitive.unitInterval.Contains input) :
      (pointwise input inside).output = Evaluation.eval output.polynomial (Cast.Path.ofCoordinate input) :=
    ((samples input inside).certificate_output order coordinate).trans
      (Cell.Restriction.eval_eq _ (lastBase.cache lastInner) input).symm
  have slope_eq (input : Rational) (inside : Cell.Primitive.unitInterval.Contains input) :
      (pointwise input inside).slope = Evaluation.eval slope.polynomial (Cast.Path.ofCoordinate input) :=
    ((samples input inside).certificate_slope order coordinate).trans
      (Cell.Restriction.eval_eq _ (firstSlope.cache firstInner) input).symm
  have factor_le (input : Rational) (inside : Cell.Primitive.unitInterval.Contains input) :
      (pointwise input inside).factor ≤ betweenPointwiseCeiling patch count order coordinate :=
    (samples input inside).certificate_factor_le order coordinate
  exact Cell.ParameterVariation.certificate base output slope (lastOffset - firstOffset)
    (baseStart.trans outputStart.symm) (baseFinish.trans outputFinish.symm)
    (slopeStart.trans outputStart.symm) (slopeFinish.trans outputFinish.symm)
    (betweenPointwiseCeiling patch count order coordinate)
    (betweenPointwiseCeiling_nonnegative patch count order coordinate)
    pointwise base_eq output_eq slope_eq factor_le

/-- The certificate base is the SAME first target's retained base restriction integral. -/
theorem betweenDyadicCertificate_base :
    (betweenDyadicCertificate sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      index pair firstSelected lastSelected unit nonzero spatial firstPaid lastPaid samples order coordinate
        firstBase lastBase firstSlope).base =
      (Cell.Restriction.model
        (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (firstBase.cache (refinementOccurrence.localIndex pair.1))).integralSample := by
  unfold betweenDyadicCertificate
  apply Cell.ParameterVariation.certificate_base
    (base := Cell.Restriction.model
      (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (firstBase.cache (refinementOccurrence.localIndex pair.1)))
    (output := Cell.Restriction.model
      (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (lastBase.cache (refinementOccurrence.localIndex pair.2)))
    (slope := Cell.Restriction.model
      (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate))
      (firstSlope.cache (refinementOccurrence.localIndex pair.1)))

/-- The certificate output is the SAME independent second target's retained base restriction integral. -/
theorem betweenDyadicCertificate_output :
    (betweenDyadicCertificate sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      index pair firstSelected lastSelected unit nonzero spatial firstPaid lastPaid samples order coordinate
        firstBase lastBase firstSlope).output =
      (Cell.Restriction.model
        (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (lastBase.cache (refinementOccurrence.localIndex pair.2))).integralSample := by
  unfold betweenDyadicCertificate
  apply Cell.ParameterVariation.certificate_output
    (base := Cell.Restriction.model
      (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (firstBase.cache (refinementOccurrence.localIndex pair.1)))
    (output := Cell.Restriction.model
      (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (lastBase.cache (refinementOccurrence.localIndex pair.2)))
    (slope := Cell.Restriction.model
      (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate))
      (firstSlope.cache (refinementOccurrence.localIndex pair.1)))

/-- The certificate slope is the SAME first target's independent derivative restriction integral. -/
theorem betweenDyadicCertificate_slope :
    (betweenDyadicCertificate sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      index pair firstSelected lastSelected unit nonzero spatial firstPaid lastPaid samples order coordinate
        firstBase lastBase firstSlope).slope =
      (Cell.Restriction.model
        (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate))
        (firstSlope.cache (refinementOccurrence.localIndex pair.1))).integralSample := by
  unfold betweenDyadicCertificate
  apply Cell.ParameterVariation.certificate_slope
    (base := Cell.Restriction.model
      (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (firstBase.cache (refinementOccurrence.localIndex pair.1)))
    (output := Cell.Restriction.model
      (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
      (lastBase.cache (refinementOccurrence.localIndex pair.2)))
    (slope := Cell.Restriction.model
      (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate))
      (firstSlope.cache (refinementOccurrence.localIndex pair.1)))

/-- The SAME actual integral factor is its original fixed-parent density times the common squared width.

Both restriction banks and original polynomial certificates are unchanged.
The original dyadic displacement readback and pair's whole edge identity
supply the width factor, without strict physical displacement or a count bound.
-/
theorem betweenDyadicCertificate_factor :
    (betweenDyadicCertificate sourcePrepared firstLinked lastLinked firstAligned lastAligned firstPrepared lastPrepared
      index pair firstSelected lastSelected unit nonzero spatial firstPaid lastPaid samples order coordinate
        firstBase lastBase firstSlope).factor =
      betweenDensity patch count order coordinate *
        (((dyadicEdges (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
          UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)[index.val]'index.isLt).right.parameter -
          ((dyadicEdges (firstLinked.shifted.acquired.mesh.depth + lastLinked.shifted.acquired.mesh.depth)
            UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)[
              index.val]'index.isLt).left.parameter) ^ 2 := by
  have original :
      (betweenDyadicCertificate sourcePrepared firstLinked lastLinked firstAligned lastAligned
        firstPrepared lastPrepared
        index pair firstSelected lastSelected unit nonzero spatial firstPaid lastPaid samples order coordinate
          firstBase lastBase firstSlope).factor =
        2 * betweenPointwiseCeiling patch count order coordinate * Norm.Basic.normSq
          (Cell.Restriction.model
            (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
            (lastBase.cache (refinementOccurrence.localIndex pair.2))).displacement := by
    unfold betweenDyadicCertificate
    apply Cell.ParameterVariation.certificate_factor
      (base := Cell.Restriction.model
        (firstPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (firstBase.cache (refinementOccurrence.localIndex pair.1)))
      (output := Cell.Restriction.model
        (lastPrepared.preparation.cell.models.cell (Specification.Table.baseIndex order coordinate))
        (lastBase.cache (refinementOccurrence.localIndex pair.2)))
      (slope := Cell.Restriction.model
        (firstPrepared.preparation.cell.models.cell (Specification.Table.slopeIndex order coordinate))
        (firstSlope.cache (refinementOccurrence.localIndex pair.1)))
  have lastFine := (refinementOccurrence.edge_eq pair.2).symm.trans
    (commutedIndex_edge firstLinked.shifted.acquired.mesh.depth lastLinked.shifted.acquired.mesh.depth
      UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint index)
  have displacement :=
    (lastLinked.shifted.dyadicRestriction_normSq (refinementOccurrence.coarseIndex pair.2)
      firstLinked.shifted.acquired.mesh.depth (refinementOccurrence.localIndex pair.2) lastSelected lastPrepared
      (Specification.Table.baseIndex order coordinate) lastBase sourcePrepared).trans
        (congrArg (fun edge : ParameterEdge => (edge.right.parameter - edge.left.parameter) ^ 2 * cost parent) lastFine)
  exact original.trans ((congrArg (fun value : Rational =>
    2 * betweenPointwiseCeiling patch count order coordinate * value) displacement).trans (by
      unfold betweenDensity
      ring1))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
