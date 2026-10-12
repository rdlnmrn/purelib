module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels

public section

open Purelib.Curves
open Purelib.Geometry
open Purelib.Riemann

/-!
# Common chart stages for the existing side request spine

Each parent retains its original controlled request. The extra chart plans
choose source, fine and reading maxima before their corresponding samples.
Evaluation returns the original side-evaluation type together with typed
chart replacements, all using the same cap sample and reading stage.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

set_option genInjectivity false in
/-- Chart replacement requests indexed by the exact original side-request spine. -/
inductive ChartRequests (target : Normalization.InverseRootPolynomial.Coordinate) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} →
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared → Type 2
  /-- The empty original chart-request spine. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target .nil
  /-- One original chart request followed by its dependent retained tail. -/ | cons {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
    (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
        Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch genus}
      {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
        Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
      {head : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover} {tail :
        Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers}
      {request : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest head sourceTarget reciprocalTarget
        coefficientTarget totalTarget areaTarget minimum}
      {remaining : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
        coefficientTarget totalTarget areaTarget minimum tail}
      (replacement : ChartReplacementRequest head target
        minimum) (rest : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target
        remaining) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target (.cons request
        remaining)

constructive_injectivity ChartRequests

namespace ChartRequests

/-- Prepare one original chart replacement request for each retained side request. -/
@[expose] def build (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → (requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared) →
    Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target requests
  | _, _, _, .nil => .nil
  | _, _, _, .cons _ rest => .cons
    (ChartReplacementRequest.build _ target positive
    minimum) (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests.build target positive
    rest)

variable {target : Normalization.InverseRootPolynomial.Coordinate}

/-- Take the maximum model stage of the original requests and the supplied floor. -/
@[expose] def maximum : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target requests → Nat
  | _, _, _, _, .nil => minimum
  | _, _, _, _, .cons head tail => max head.charts.maximum tail.maximum

/-- Take the maximum subdivision depth of the original requests, with zero for an empty spine. -/
@[expose] def depthMaximum : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  → {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target requests → Nat
  | _, _, _, _, .nil => 0
  | _, _, _, _, .cons head tail => max head.charts.depthMaximum tail.depthMaximum

end ChartRequests

variable {target : Normalization.InverseRootPolynomial.Coordinate} {index depth readingIndex : Nat} {box :
  Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- Chart plans on one shared cap sample, indexed by the retained original requests. -/
inductive ChartPlans (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target requests → Type 2
  /-- The empty original chart-plan spine. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartPlans sample .nil
  /-- One original chart plan followed by its dependent retained tail. -/ | cons {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
    (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
        Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch genus}
      {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
        Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
      {head : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover} {tail :
        Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers}
      {request : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest head sourceTarget reciprocalTarget
        coefficientTarget totalTarget areaTarget minimum}
      {remaining : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
        coefficientTarget totalTarget areaTarget minimum tail}
      {replacement : ChartReplacementRequest head target
        minimum} {rest : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target remaining}
      (plan : Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartPlan request replacement sample) (plans :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartPlans sample rest) :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartPlans sample (.cons (request :=
        request) replacement rest)

constructive_injectivity ChartPlans

set_option genInjectivity false in
/-- Actual chart replacements indexed by the original side evaluations at the common stage. -/
inductive ChartReplacements (target : Normalization.InverseRootPolynomial.Coordinate) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex requests → Type 2
  /-- The empty original evaluated replacement spine. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target .nil
  /-- One actual original replacement followed by the exact dependent tail. -/ | cons {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {parents : List
    (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
        Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch genus}
      {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
        Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
      {head : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover} {tail :
        Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers}
      {request : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest head sourceTarget reciprocalTarget
        coefficientTarget totalTarget areaTarget minimum}
      {remaining : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
        coefficientTarget totalTarget areaTarget minimum tail}
      {evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.Evaluation request sample depth
        readingIndex} {rest : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth
        readingIndex remaining}
      (replacement : ChartReplacementRequest head target
        minimum) (chart : Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartReplacement replacement
        evaluated)
      (charts : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target rest) :
        Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target (.cons evaluated
        rest)

constructive_injectivity ChartReplacements

namespace ChartPlans

/-- Build each original chart plan on the same supplied cap sample. -/
@[expose] def build (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) :
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} → {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    (charts : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target requests) →
      Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartPlans sample charts
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail => .cons (Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartPlan.build _
    head sample) (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartPlans.build sample tail)

/-- Take the maximum reading stage of the original plans and the supplied floor. -/
@[expose] def maximum : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    {charts : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target requests} →
      Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartPlans sample charts → Nat
  | _, _, _, _, _, .nil => minimum
  | _, _, _, _, _, .cons head tail => max head.stage tail.maximum

/-- Evaluate the original proper parents once at the common stage and return their exact dependent chart replacements.
-/
@[expose] def evaluate : {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
  {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} →
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} → {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared} →
    {charts : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartRequests target requests} → (plans :
      Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartPlans sample charts) →
      Integration.PreparedDyadicRefinements.AllParentsProper parents →
    requests.maximum ≤ index → charts.maximum ≤ index → charts.depthMaximum ≤ depth → plans.maximum ≤ readingIndex →
    Σ evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
      requests, Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target evaluated
  | _, _, _, _, _, .nil, _, _, _, _, _ => ⟨.nil, .nil⟩
  | _, _, _, _, _, .cons head tail, proper, later, chartLater, fineLater, readingLater =>
      let first := Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartPlan.evaluate head proper.1
        ((Data.Nat.Order.le_max_left _ _).trans later) ((Data.Nat.Order.le_max_left _ _).trans chartLater)
        ((Data.Nat.Order.le_max_left _ _).trans fineLater) ((Data.Nat.Order.le_max_left _ _).trans readingLater)
      let rest := Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartPlans.evaluate tail
        proper.2 ((Data.Nat.Order.le_max_right _ _).trans later) ((Data.Nat.Order.le_max_right _ _).trans chartLater)
        ((Data.Nat.Order.le_max_right _ _).trans fineLater) ((Data.Nat.Order.le_max_right _ _).trans readingLater)
      ⟨.cons first.1 rest.1, .cons _ first.2 rest.2⟩

end ChartPlans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
