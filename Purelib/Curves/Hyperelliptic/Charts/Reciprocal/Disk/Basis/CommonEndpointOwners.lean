module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
import Purelib.Riemann.RootContinuation.RootRadialBoundary
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Common-parent boundary owners are selected from the original requests.
Their root views reuse acquired readings and retain chart/potential readbacks. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

variable {originals :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace BasisCommonChartRequests

/-- The retained endpoint chain relation composes across the original concatenated parameter-edge lists. -/
private theorem from_append {first middle last : Normalization.InverseRootPolynomial.Coordinate}
    {left right : List Branches.ClearSheetContinuation.Subdivision.ParameterEdge}
    (before : Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first left middle) (after :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From middle right last) :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first (left ++ right) last := by
  induction left generalizing first with
  | nil => exact before ▸ after
  | cons edge rest ih => exact ⟨before.1, ih before.2⟩

/-- The original dyadic subdivision connects exactly its supplied first and last parameters. -/
private theorem dyadic_from (depth : Nat)
    (first last : Branches.ClearSheetContinuation.Subdivision.Endpoint) :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From first.parameter
      (Branches.ClearSheetContinuation.Subdivision.dyadicEdges depth first last)
      last.parameter := by
  induction depth generalizing first last with
  | zero => exact ⟨rfl, rfl⟩
  | succ depth ih =>
    exact Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.from_append (ih _ _)
      (ih _ _)

/-- The retained common interval traversal connects the original parent parameters zero and one. -/
theorem common_from {coverFloor : Nat} (common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover
  cover covers coverFloor) :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From 0 (common.intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) 1 := by
  rw [common.edges_eq]
  exact Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.dyadic_from
    common.depth Meshes.UniformPrimitiveMesh.firstEndpoint
    Meshes.UniformPrimitiveMesh.lastEndpoint

/-- Select the first original endpoint owner of a nonempty common request chain. -/
@[expose] def firstView : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} →
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish → intervals ≠ [] →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView regular data start
  | _, .nil, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons head _, _, _, chain, _ =>
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.ofPoint head.request.first.point
        head.request.first.bounds chain.1.symm

/-- Select the last original endpoint owner by traversing the retained nonempty common request chain. -/
@[expose] def lastView : {intervals : List (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} →
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish → intervals ≠ [] →
    Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView regular data finish
  | _, .nil, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons head .nil, _, _, chain, _ =>
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.ofPoint head.request.last.point
        head.request.last.bounds chain.2
  | _, .cons _ (.cons next remaining), _, _, chain, _ =>
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.lastView
        (.cons next remaining) chain.2 (by intro empty; cases empty)

namespace Plans

/-- Read the first retained endpoint owner using the already acquired original root reading. -/
@[expose] def firstReading : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} → (chain :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish) → (nonempty : intervals ≠
      []) →
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.firstView requests chain
      nonempty).RootReading capSample stage
  | _, .nil, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons head _, _, readings, _, _, chain, _ =>
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.rootReading head.request.first.bounds
        chain.1.symm
        (Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.ofEqual (congrArg
          Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared.point readings.1.evaluated.first_owner)
          readings.1.evaluated.first.root).reading

/-- Read the last retained endpoint owner using the original acquired root readings. -/
@[expose] def lastReading : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} → (chain :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish) → (nonempty : intervals ≠
      []) →
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.lastView requests chain
      nonempty).RootReading capSample stage
  | _, .nil, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons head .nil, _, readings, _, _, chain, _ =>
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.rootReading head.request.last.bounds chain.2
        (Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.ofEqual (congrArg
          Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared.point readings.1.evaluated.last_owner)
          readings.1.evaluated.last.root).reading
  | _, .cons _ (.cons next remaining), _, readings, _, _, chain, _ =>

        lastReading
        (.cons next remaining) readings.2 chain.2 (by intro empty; cases empty)

/-- The first original chart value is evaluated at the coordinate of its retained endpoint root reading. -/
theorem firstReading_chart : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} → (chain :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish) → (nonempty : intervals ≠
      []) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.Readings.firstChartValue coefficients requests
      readings =
      polynomials.value coefficients
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.firstReading
        requests readings chain nonempty).reading.coordinate
  | _, .nil, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ _, _, readings, _, _, chain, _ => by
      simp only [-eq_self, -iff_self,
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.Readings.firstChartValue,
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.firstReading,
        Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.rootReading_coordinate,
        Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq]
      rfl

/-- The last original chart value is evaluated at the coordinate of its retained endpoint root reading. -/
theorem lastReading_chart : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} → (chain :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish) → (nonempty : intervals ≠
      []) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.Readings.lastChartValue coefficients requests
      readings =
      polynomials.value coefficients
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.lastReading
        requests readings chain nonempty).reading.coordinate
  | _, .nil, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ .nil, _, readings, _, _, chain, _ => by
      simp only [-eq_self, -iff_self,
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.Readings.lastChartValue,
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.lastReading,
        Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.rootReading_coordinate,
        Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq]
      rfl
  | _, .cons _ (.cons next remaining), _, readings, _, _, chain, _ =>

        lastReading_chart
        (.cons next remaining) readings.2 chain.2 (by intro empty; cases empty)

/-- The first original energy potential is the radial area of its retained endpoint coordinate at the requested depth.
-/
theorem firstReading_radial : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} → (chain :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish) → (nonempty : intervals ≠
      []) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.EnergySamples.firstPotential requests samples =
      RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.firstReading
        requests readings chain nonempty).reading.coordinate
  | _, .nil, _, _, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ _, _, readings, energies, samples, _, _, chain, _ => by
      rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.EnergySamples.firstPotential,
        samples.1.first_eq, energies.1.property,
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.firstReading,
        Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.rootReading_coordinate,
          Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq]

/-- The squared first retained endpoint coordinate lies in the original padded chart domain. -/
theorem firstReading_inside : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Inside requests plans readings →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} → (chain :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish) → (nonempty : intervals ≠
      []) →
    regular.padded.Contains
      ((Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.firstReading
      requests readings chain nonempty).reading.coordinate *
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.firstReading
        requests readings chain nonempty).reading.coordinate)
  | _, .nil, _, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ _, _, readings, inside, _, _, chain, _ => by
      rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.firstReading,
        Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.rootReading_coordinate,
        Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq]
      exact inside.1

/-- The last original energy potential is the radial area of its retained endpoint coordinate at the requested depth. -/
theorem lastReading_radial : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} → (chain :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish) → (nonempty : intervals ≠
      []) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.EnergySamples.lastPotential requests samples =
      RootContinuation.RootRadialGeometry.radialArea (polynomials.value coefficients) energyDepth
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.lastReading
        requests readings chain nonempty).reading.coordinate
  | _, .nil, _, _, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ .nil, _, readings, energies, samples, _, _, chain, _ => by
      rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback.EnergySamples.lastPotential, samples.1.last_eq,
        energies.1.property,
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.lastReading,
        Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.rootReading_coordinate,
          Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq]
  | _, .cons _ (.cons next remaining), _, readings, energies, samples, _, _, chain, _ =>

        lastReading_radial
        (.cons next remaining) readings.2 energies.2 samples.2 chain.2 (by intro empty; cases empty)

/-- The squared last retained endpoint coordinate lies in the original padded chart domain. -/
theorem lastReading_inside : {intervals : List
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers)} →
    (requests : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests.Plans.Readings anchorBank
      bank stage requests plans) →
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank.Inside requests plans readings →
    {start finish : Normalization.InverseRootPolynomial.Coordinate} → (chain :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.From start (intervals.map
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval.edge) finish) → (nonempty : intervals ≠
      []) →
    regular.padded.Contains
      ((Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.lastReading
      requests readings chain nonempty).reading.coordinate *
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.lastReading
        requests readings chain nonempty).reading.coordinate)
  | _, .nil, _, _, _, _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ .nil, _, readings, inside, _, _, chain, _ => by
      rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners.BasisCommonChartRequests.Plans.lastReading,
        Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners.EndpointView.rootReading_coordinate,
        Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point.ReadingView.coordinate_eq]
      exact inside.2.1
  | _, .cons _ (.cons next remaining), _, readings, inside, _, _, chain, _ =>

        lastReading_inside
        (.cons next remaining) readings.2 inside.2.2 chain.2 (by intro empty; cases empty)

end Plans
end BasisCommonChartRequests
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEndpointOwners
