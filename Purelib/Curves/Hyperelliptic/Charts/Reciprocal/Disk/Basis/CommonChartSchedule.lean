module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Riemann.Normalization

public section

/-! Polynomial and reading schedules on the original common-interval spine.
Every cell keeps its own paid request and shares the eventual numerical bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget (BasisIntervalChartBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Cover data}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {depth : Nat} {allowance : Coordinate}

set_option genInjectivity false in
/-- The ordered chart-budget requests on the retained common-interval spine. -/
inductive BasisCommonChartRequests (regular : RegularBounds.Data cap)
    (depth : Nat) (target allowance : Coordinate) (floor sourceFloor : Nat) :
    List (BasisCommonInterval cover covers) → Type 2
  /-- The empty common-interval chart request bank. -/ | nil :
    CommonChartSchedule.BasisCommonChartRequests regular depth
    target allowance floor sourceFloor []
  /-- Retain the first interval's paid chart budget and the request bank for the remaining intervals. -/ | cons
    {interval : BasisCommonInterval cover covers} {remaining : List (BasisCommonInterval cover
    covers)}
      (head : BasisIntervalChartBudget interval regular depth target allowance floor sourceFloor)
      (tail : CommonChartSchedule.BasisCommonChartRequests
        regular depth target allowance floor sourceFloor remaining) :
      CommonChartSchedule.BasisCommonChartRequests regular
        depth target allowance floor sourceFloor (interval :: remaining)

constructive_injectivity BasisCommonChartRequests

namespace BasisCommonChartRequests

/-- Prepare the paid chart budget on every retained common interval in order. -/
@[expose] def build (regular : RegularBounds.Data cap) (depth : Nat) (target allowance :
  Coordinate)
    (positive : 0 < target) (allowancePositive : 0 < allowance) (floor sourceFloor : Nat) :
    (intervals : List (BasisCommonInterval cover covers)) →
      BasisCommonChartRequests regular depth
      target allowance floor sourceFloor intervals
  | [] => .nil
  | interval :: remaining => .cons
      (BasisIntervalChartBudget.build interval regular depth target allowance positive allowancePositive floor
        sourceFloor)
      (BasisCommonChartRequests.build
        regular depth target allowance positive allowancePositive floor sourceFloor remaining)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests in
/-- The common polynomial stage paying all retained requests and both original floors. -/
@[expose] def index : {intervals : List (BasisCommonInterval cover covers)} →
    BasisCommonChartRequests regular depth target
      allowance floor sourceFloor intervals → Nat
  | _, .nil => max floor sourceFloor
  | _, .cons head tail => max head.request.index tail.index

variable {index minimum : Nat} {box : Geometry.Rational.Box}
  {capSample : Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests in
/-- The plans reuse the supplied polynomial samples on every interval. -/
@[expose] def Plans (capSample : Primitives.Sample cap differential index box)
    (polynomials : RegularBasisPolynomials cap index box) (minimum : Nat) :
    {intervals : List (BasisCommonInterval cover covers)} →
    BasisCommonChartRequests regular depth target
      allowance floor sourceFloor intervals → Type 2
  | _, .nil => PUnit
  | _, .cons head tail => Plan head.request capSample polynomials minimum ×
    BasisCommonChartRequests.Plans
    capSample polynomials minimum tail

namespace Plans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests in
/-- Plan every retained interval using the same supplied cap and basis polynomial samples. -/
@[expose] def build (capSample : Primitives.Sample cap differential index box)
    (polynomials : RegularBasisPolynomials cap index box) (minimum : Nat) :
    {intervals : List (BasisCommonInterval cover covers)} →
    (requests : BasisCommonChartRequests regular
      depth target allowance floor sourceFloor intervals) →
      Plans capSample
      polynomials minimum requests
  | _, .nil => ⟨⟩
  | _, .cons head tail => ⟨Plan.build head.request capSample polynomials minimum,
      Plans.build
        capSample polynomials minimum tail⟩

/-- The maximum actual reading stage across all retained interval plans, respecting the supplied minimum. -/
@[expose] def stage : {intervals : List (BasisCommonInterval cover covers)} →
    (requests : BasisCommonChartRequests regular
      depth target allowance floor sourceFloor intervals) →
    Plans capSample
      polynomials minimum requests → Nat
  | _, .nil, _ => minimum
  | _, .cons _ tail, plans => max plans.1.stage
    (Plans.stage
    tail plans.2)

end Plans
end BasisCommonChartRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
