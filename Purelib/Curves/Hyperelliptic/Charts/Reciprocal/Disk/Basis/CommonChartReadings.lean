module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitiveReadback

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

public section

/-! Acquire a parent chart bank in common-interval order. All intervals read
the retained anchor and basis inverse banks at the same polynomial stage. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule (BasisCommonChartRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests (Plans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest (Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest (BasisIntervalChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest.Plan
  (Evaluation)

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
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {depth : Nat} {allowance : Coordinate}

variable {index minimum stage : Nat} {box : Geometry.Rational.Box}
  {capSample : Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}

namespace BasisIntervalChartRequest.Plan

/-- The anchor geometry is the common interval's retained original cell. -/
@[expose] def AnchorSample (interval : BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap)
    (capSample : Primitives.Sample cap differential index box) :=
  ArcSamples.Sample (ArcSamples.Data.build regular interval.anchor.cell) capSample

/-- Read the common interval's actual anchor primitive from the retained bank and attach the supplied cap sample. -/
@[expose] def anchorSample (interval : BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap)
    (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (capSample : Primitives.Sample cap differential index box) :
      AnchorSample
      interval regular capSample :=
  let retained := anchorBank.readCell interval.anchor.cell interval.anchor.member
  ArcSamples.Sample.ofPrimitive (ArcSamples.Data.build regular interval.anchor.cell)
    capSample retained.primitive retained.cell_eq

variable {interval : BasisCommonInterval cover
  covers}
  {request : BasisIntervalChartRequest
    interval regular depth target sourceTarget floor sourceFloor}

set_option genInjectivity false in
/-- The actual anchor sample and acquired chart readings for one common interval.

The retained sample equality binds evaluation to the original anchor bank, while all basis transports consume the same
supplied sample bank and stage. -/
structure Acquisition (plan : Plan request capSample polynomials minimum)
    (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (bank : BasisSourceLocations.SampleBank covers index) (stage : Nat) where
  /-- The retained actual anchor sample on the original interval. -/ sample :
    AnchorSample
    interval regular capSample
  /-- The sample is exactly the anchor-bank readback for this interval and cap sample. -/ sample_eq : sample =
    anchorSample
    interval regular anchorBank capSample
  /-- The acquired chart readings and basis transports at the retained stage. -/ evaluated : Evaluation plan sample
    bank stage

constructive_injectivity Acquisition

/-- Acquire one interval's actual anchor and basis readings after both the model and reading thresholds are paid. -/
@[expose] def acquire (plan : Plan request capSample polynomials minimum)
    (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (bank : BasisSourceLocations.SampleBank covers index)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : request.index ≤ index) (stage : Nat) (readingLater : plan.stage ≤ stage) :
      Acquisition
      plan anchorBank bank stage :=
  let sample :=
    anchorSample
    interval regular anchorBank capSample
  ⟨sample, rfl, plan.evaluate sample bank branch modelLater stage readingLater⟩

end BasisIntervalChartRequest.Plan

namespace BasisCommonChartRequests.Plans

/-- Each entry retains its actual sample, acquired root readings and basis transports. The list index enforces the
original common-interval order. -/
@[expose] def Readings (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (bank : BasisSourceLocations.SampleBank covers index) (stage : Nat) :
    {intervals : List (BasisCommonInterval cover covers)} →
    (requests : BasisCommonChartRequests regular depth target allowance floor sourceFloor intervals)
      →
    Plans capSample polynomials minimum requests → Type 2
  | _, .nil, _ => PUnit
  | _, .cons _ tail, plans =>
    BasisIntervalChartRequest.Plan.Acquisition
    plans.1 anchorBank bank stage ×
    Readings
    anchorBank bank stage tail plans.2

/-- Acquire the complete common-interval request spine at one shared reading stage.

Every recursive entry reuses the original anchor and basis sample banks and inherits its paid model and reading
thresholds. -/
@[expose] def read (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (bank : BasisSourceLocations.SampleBank covers index)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (readingStage : Nat) :
    {intervals : List (BasisCommonInterval cover covers)} →
    (requests : BasisCommonChartRequests regular depth target allowance floor sourceFloor intervals)
      →
    (plans : Plans capSample polynomials minimum requests) →
    requests.index ≤ index → Plans.stage requests plans ≤ readingStage →
      Readings
      anchorBank bank readingStage requests plans
  | _, .nil, _, _, _ => ⟨⟩
  | _, .cons head tail, plans, modelLater, readingLater =>
      ⟨BasisIntervalChartRequest.Plan.acquire
        plans.1 anchorBank bank branch ((Data.Nat.Order.le_max_left head.request.index tail.index).trans
        modelLater)
        readingStage ((Data.Nat.Order.le_max_left ..).trans readingLater),

          read
          anchorBank bank branch readingStage tail plans.2 ((Data.Nat.Order.le_max_right ..).trans modelLater)
          ((Data.Nat.Order.le_max_right ..).trans readingLater)⟩

end BasisCommonChartRequests.Plans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
