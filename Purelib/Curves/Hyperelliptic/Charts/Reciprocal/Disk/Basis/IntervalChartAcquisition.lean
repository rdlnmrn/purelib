module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
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
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests.BasisSourceRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

public section

/-! A shared reading stage for the chart roots and all basis transports.
Each endpoint and midpoint root is sampled once and retained with its owner. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Prepared Reading Chart)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartTree)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (TreeReadings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule (EndpointSources BasisTreeSources)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest (BasisIntervalChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest (Model)

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

namespace BasisIntervalChartRequest

variable {interval : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover
  covers} {depth index minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest.BasisIntervalChartRequest
    interval regular depth target sourceTarget floor sourceFloor}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

set_option genInjectivity false in
/-- The complete original chart and basis-source reading schedule on one retained common interval.

One shared cap and basis polynomial bank supply all endpoint and midpoint plans before their common root-reading stage
is chosen. -/
structure Plan (request : IntervalChartRequest.BasisIntervalChartRequest interval regular depth target sourceTarget
  floor sourceFloor)
    (capSample : Primitives.Sample cap differential index box)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) (minimum : Nat) where
  /-- The original first endpoint chart plan on the supplied retained cap sample. -/ first : VertexRequests.Chart
    request.first capSample minimum
  /-- The original last endpoint chart plan on that same retained cap sample. -/ last : VertexRequests.Chart
    request.last capSample minimum
  /-- The original midpoint chart plans on the retained request tree. -/ tree : VertexTree.ChartTree capSample minimum
    request.tree
  /-- The original first endpoint basis-source transport plans on the supplied polynomial bank. -/ firstSources :
    BasisSourceRequest.ChartRequest request.firstSources.request polynomials minimum
  /-- The original last endpoint basis-source transport plans on that same polynomial bank. -/ lastSources :
    BasisSourceRequest.ChartRequest request.lastSources.request polynomials minimum
  /-- The original midpoint basis-source transport plans on the retained chart tree. -/ treeSources :
    BasisTreeSources.Plans polynomials minimum request.tree request.treeSources
  /-- The cached common reading stage paying every original chart and source transport plan. -/ stage : Nat
  /-- The common stage is exactly the maximum of the retained original endpoint, midpoint and source stages. -/ stage_eq
    : stage = max (max first.stage (max last.stage tree.stage))
    (max firstSources.stage (max lastSources.stage (Plans.stage request.tree request.treeSources treeSources)))

constructive_injectivity Plan

namespace Plan

/-- Prepare all original chart and source transports on the supplied polynomial banks and cache their shared paid
reading stage. -/
@[expose] def build (request : IntervalChartRequest.BasisIntervalChartRequest interval regular depth target sourceTarget
  floor sourceFloor)
    (capSample : Primitives.Sample cap differential index box)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest.Plan request
      capSample polynomials minimum :=
  let first := Chart.build request.first capSample minimum
  let last := Chart.build request.last capSample minimum
  let tree := ChartTree.build capSample minimum request.tree
  let firstSources := ChartRequest.build request.firstSources.request polynomials minimum
  let lastSources := ChartRequest.build request.lastSources.request polynomials minimum
  let treeSources := Plans.build polynomials minimum request.tree request.treeSources
  let stage := max (max first.stage (max last.stage tree.stage))
    (max firstSources.stage (max lastSources.stage (Plans.stage request.tree request.treeSources treeSources)))
  ⟨first, last, tree, firstSources, lastSources, treeSources, stage, rfl⟩

variable {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular interval.anchor.cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {bank : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank
    covers index} {stage : Nat}

/-- The actual chart reading type at the retained original common interval's first endpoint. -/
@[expose] def FirstReading (_request : IntervalChartRequest.BasisIntervalChartRequest interval regular depth target
  sourceTarget floor sourceFloor)
    (sample : ArcSamples.Sample comparison capSample) (stage : Nat) :=
  VertexRequests.Reading regular (BasisIntervalChartRequest.Model interval) sample interval.edge.left.parameter target
    floor stage

/-- The actual chart reading type at the retained original common interval's last endpoint. -/
@[expose] def LastReading (_request : IntervalChartRequest.BasisIntervalChartRequest interval regular depth target
  sourceTarget floor sourceFloor)
    (sample : ArcSamples.Sample comparison capSample) (stage : Nat) :=
  VertexRequests.Reading regular (BasisIntervalChartRequest.Model interval) sample interval.edge.right.parameter target
    floor stage

set_option genInjectivity false in
/-- The actual original endpoint and midpoint root readings with every basis transport attached to those same readings.
-/
structure Evaluation (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest.Plan request
  capSample polynomials minimum)
    (sample : ArcSamples.Sample comparison capSample)
    (bank : BasisSourceLocations.SampleBank covers index) (stage : Nat) where
  /-- The actual first original endpoint root reading, acquired once. -/ first :
    FirstReading
    request sample stage
  /-- The actual last original endpoint root reading, acquired once. -/ last :
    LastReading
    request sample stage
  /-- The first actual reading retains exactly the original first prepared chart request. -/ first_owner :
    first.prepared = request.first
  /-- The last actual reading retains exactly the original last prepared chart request. -/ last_owner : last.prepared =
    request.last
  /-- The complete actual midpoint root readings on the original retained request tree. -/ readings :
    VertexPaths.TreeReadings sample stage request.tree
  /-- The original first endpoint basis transports consuming that exact retained root reading. -/ firstSources :
    EndpointSources.Evaluation request.firstSources plan.firstSources bank first
  /-- The original last endpoint basis transports consuming that exact retained root reading. -/ lastSources :
    EndpointSources.Evaluation request.lastSources plan.lastSources bank last
  /-- All original midpoint basis transports consuming the same retained midpoint root readings. -/ treeSources :
    Plans.Evaluation bank request.tree request.treeSources plan.treeSources readings

constructive_injectivity Evaluation

/-- All basis comparisons consume the root readings already retained by the chart path. The caller can raise the shared
stage without changing ownership. -/
@[expose] def evaluate (plan :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest.Plan request
  capSample polynomials minimum)
    (sample : ArcSamples.Sample comparison capSample)
    (bank : BasisSourceLocations.SampleBank covers index)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : request.index ≤ index) (stage : Nat) (readingLater : plan.stage ≤ stage) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition.BasisIntervalChartRequest.Plan.Evaluation
      plan sample bank stage := by
  have stages := plan.stage_eq ▸ readingLater
  have geometry := (Purelib.Data.Nat.Order.le_max_left ..).trans stages
  have sources := (Purelib.Data.Nat.Order.le_max_right ..).trans stages
  let first := plan.first.evaluate sample (request.first_le.trans modelLater) stage ((Purelib.Data.Nat.Order.le_max_left
    ..).trans geometry)
  let last := plan.last.evaluate sample (request.last_le.trans modelLater) stage
    ((Purelib.Data.Nat.Order.le_max_left ..).trans ((Purelib.Data.Nat.Order.le_max_right ..).trans geometry))
  let readings := ChartTree.read sample stage plan.tree (request.tree_le.trans modelLater)
    ((Purelib.Data.Nat.Order.le_max_right ..).trans ((Purelib.Data.Nat.Order.le_max_right ..).trans geometry))
  let firstSources := request.firstSources.evaluate plan.firstSources bank first rfl branch
    (request.firstSources_le.trans modelLater) ((Purelib.Data.Nat.Order.le_max_left ..).trans sources)
  let lastSources := request.lastSources.evaluate plan.lastSources bank last rfl branch
    (request.lastSources_le.trans modelLater) ((Purelib.Data.Nat.Order.le_max_left ..).trans
      ((Purelib.Data.Nat.Order.le_max_right ..).trans sources))
  let treeSources := Plans.evaluate bank branch request.tree request.treeSources plan.treeSources readings
    (request.treeSources_le.trans modelLater) ((Purelib.Data.Nat.Order.le_max_right ..).trans
      ((Purelib.Data.Nat.Order.le_max_right ..).trans sources))
  exact ⟨first, last, rfl, rfl, readings, firstSources, lastSources, treeSources⟩

end Plan
end BasisIntervalChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
