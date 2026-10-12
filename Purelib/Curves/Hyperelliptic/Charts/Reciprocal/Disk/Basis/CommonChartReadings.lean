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

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter target sourceTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor sourceFloor :
    Nat}
  {covers : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {depth : Nat} {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

variable {index minimum stage : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

namespace BasisIntervalChartRequest.Plan

/-- The anchor geometry is the common interval's retained original cell. -/
@[expose] def AnchorSample (interval : CommonCover.BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap)
    (capSample : Primitives.Sample cap differential index box) :=
  ArcSamples.Sample (ArcSamples.Data.build regular interval.anchor.cell) capSample

/-- Read the common interval's actual anchor primitive from the retained bank and attach the supplied cap sample. -/
@[expose] def anchorSample (interval : CommonCover.BasisCommonInterval cover covers)
    (regular : RegularBounds.Data cap)
    (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (capSample : Primitives.Sample cap differential index box) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.AnchorSample
      interval regular capSample :=
  let retained := anchorBank.readCell interval.anchor.cell interval.anchor.member
  ArcSamples.Sample.ofPrimitive (ArcSamples.Data.build regular interval.anchor.cell)
    capSample retained.primitive retained.cell_eq

variable {interval : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest
    interval regular depth target sourceTarget floor sourceFloor}

set_option genInjectivity false in
/-- The actual anchor sample and acquired chart readings for one common interval.

The retained sample equality binds evaluation to the original anchor bank, while all basis transports consume the same
supplied sample bank and stage. -/
structure Acquisition (plan : BasisIntervalChartRequest.Plan request capSample polynomials minimum)
    (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (bank : BasisSourceLocations.SampleBank covers index) (stage : Nat) where
  /-- The retained actual anchor sample on the original interval. -/ sample :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.AnchorSample
    interval regular capSample
  /-- The sample is exactly the anchor-bank readback for this interval and cap sample. -/ sample_eq : sample =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.anchorSample
    interval regular anchorBank capSample
  /-- The acquired chart readings and basis transports at the retained stage. -/ evaluated : Plan.Evaluation plan sample
    bank stage

constructive_injectivity Acquisition

/-- Acquire one interval's actual anchor and basis readings after both the model and reading thresholds are paid. -/
@[expose] def acquire (plan : BasisIntervalChartRequest.Plan request capSample polynomials minimum)
    (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (bank : BasisSourceLocations.SampleBank covers index)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : request.index ≤ index) (stage : Nat) (readingLater : plan.stage ≤ stage) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition
      plan anchorBank bank stage :=
  let sample :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.anchorSample
    interval regular anchorBank capSample
  ⟨sample, rfl, plan.evaluate sample bank branch modelLater stage readingLater⟩

end BasisIntervalChartRequest.Plan

namespace BasisCommonChartRequests.Plans

/-- Each entry retains its actual sample, acquired root readings and basis transports. The list index enforces the
original common-interval order. -/
@[expose] def Readings (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (bank : BasisSourceLocations.SampleBank covers index) (stage : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth target allowance floor sourceFloor intervals)
      →
    BasisCommonChartRequests.Plans capSample polynomials minimum requests → Type 2
  | _, .nil, _ => PUnit
  | _, .cons _ tail, plans =>
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.Acquisition
    plans.1 anchorBank bank stage ×
    Readings
    anchorBank bank stage tail plans.2

/-- Acquire the complete common-interval request spine at one shared reading stage.

Every recursive entry reuses the original anchor and basis sample banks and inherits its paid model and reading
thresholds. -/
@[expose] def read (anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges)
    (bank : BasisSourceLocations.SampleBank covers index)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (readingStage : Nat) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth target allowance floor sourceFloor intervals)
      →
    (plans : BasisCommonChartRequests.Plans capSample polynomials minimum requests) →
    requests.index ≤ index → Plans.stage requests plans ≤ readingStage →
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings
      anchorBank bank readingStage requests plans
  | _, .nil, _, _, _ => ⟨⟩
  | _, .cons head tail, plans, modelLater, readingLater =>
      ⟨Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisIntervalChartRequest.Plan.acquire
        plans.1 anchorBank bank branch ((Purelib.Data.Nat.Order.le_max_left head.request.index tail.index).trans
        modelLater)
        readingStage ((Purelib.Data.Nat.Order.le_max_left ..).trans readingLater),

          read
          anchorBank bank branch readingStage tail plans.2 ((Purelib.Data.Nat.Order.le_max_right ..).trans modelLater)
          ((Purelib.Data.Nat.Order.le_max_right ..).trans readingLater)⟩

end BasisCommonChartRequests.Plans
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
