module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Path.JoinedTrace
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJoinedFans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges

@[expose] public section

/-! Exact joining-area cancellation for the even reciprocal chart. The
actual common-cover owner joins identify physical endpoints, not root reads. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartJoins

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (ChartRequest junctionLeft junctionRight)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest (Evaluation)

variable {genus count otherCount depth floor index : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve
  genus}
  {differential other : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover.CommonCover cover otherCover}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {request :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest regular common depth target floor}
  (evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation request
    index)

/-- Every actual original common-interval joining area vanishes in the unramified reciprocal chart.

The retained physical endpoint owner identification supplies the cancellation without identifying independently sampled
roots. -/
theorem regular_connector_zero (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (i : Fin (common.intervals.length - 1)) :
    FanBankRequest.ConnectorArea
      (evaluated := evaluated) i = 0 := by
  let left := evaluated.entries.get (CommonChartBank.junctionLeft common i)
  let right := evaluated.entries.get (CommonChartBank.junctionRight common i)
  exact Evaluation.regular_join_area
    (left.evaluated.chart.retained.area.evaluated.readings.get
    (Fin.last (request.plans.get (CommonChartBank.junctionLeft common i)).geometry.tail.length))
    (right.evaluated.chart.retained.area.evaluated.readings.get 0) (request.junctions.get i).owners.first rfl rfl
      unramified

/-- The full joined trace retains each interval's complete uncentered area. No radial estimate or equality of
independently sampled roots is required. -/
theorem regular_chartTrace_area (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    (Evaluation.chartTrace evaluated).area id = evaluated.chartArea := by
  rw [Evaluation.chartTrace_area evaluated,
    FiniteSum.Fin.sumFin_congr
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartJoins.regular_connector_zero evaluated unramified),
    FiniteSum.Fin.sumFin_zero, add_zero]

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartJoins
