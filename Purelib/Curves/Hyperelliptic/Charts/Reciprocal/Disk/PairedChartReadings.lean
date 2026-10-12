module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings

open Purelib.Riemann.Normalization

public section

/-! Paired cap readings use one retained coordinate. Moving the second
owner onto that coordinate has a requested finite error, not an asserted
equality of independently sampled roots. Both degree parities are retained. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap (Endpoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings (ChartRequest)
open Purelib.Approximation.Gaussian.Equivalence (Equivalent Comparison)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus count otherCount index : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherParent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve other}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge}
  {cell : Cell data edge} {otherCell :
    Cell otherData otherEdge}
  {model : RootModel cell} {otherModel :
    RootModel otherCell} {parameter
    otherParameter : Coordinate}
  {leftPoint : Point cap model parameter} {rightPoint :
    Point cap otherModel otherParameter}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}

set_option genInjectivity false in
/-- Paired differential chart readings on one retained cap coordinate.

The original second owner remains separately cached with an operational transport budget; one shared reading stage pays
both chart requests and the actual owner comparison. -/
structure PairedChartRequest (joined : ArcOwners.Join leftPoint rightPoint)
    (sample : Primitives.Sample cap differential index box)
    (otherSample : Primitives.Sample cap other index otherBox) (target : InverseRootPolynomial.Coordinate) (floor : Nat)
      where
  /-- The first differential endpoint or reading on the original shared coordinate. -/ first :
    Coordinates.Overlap.Endpoint leftPoint.coordinates sample
  /-- The second differential endpoint or reading using that same retained coordinate. -/ other :
    Coordinates.Overlap.Endpoint leftPoint.coordinates otherSample
  /-- The separately retained second endpoint or reading on its original coordinate owner. -/ originalOther :
    Coordinates.Overlap.Endpoint rightPoint.coordinates otherSample
  /-- The first original differential's retained chart request or its certified evaluation. -/ firstChart :
    ChartReadings.ChartRequest first target floor
  /-- The second original differential's retained chart request or its certified evaluation. -/ otherChart :
    ChartReadings.ChartRequest other target floor
  /-- The requested operational comparison from the original second owner to the shared coordinate reading. -/ transport
    : Gaussian.Equivalence.Comparison originalOther.approximation other.approximation floor floor target
  /-- The cached common stage paying both chart and owner-transport requests. -/ stage : Nat
  /-- The stage is the maximum of both original chart floors and both transport reading indices. -/ stage_eq : stage =
    max firstChart.stage (max otherChart.stage (max transport.leftIndex transport.rightIndex))

constructive_injectivity PairedChartRequest

namespace PairedChartRequest
variable {joined : Join leftPoint rightPoint} {target :
  Coordinate} {floor stage : Nat}

/-- Retain both original differential endpoints on the first coordinate, the separate second endpoint and the paid
transport between them. -/
@[expose] def build (joined : ArcOwners.Join leftPoint rightPoint)
    (sample : Primitives.Sample cap differential index box)
    (otherSample : Primitives.Sample cap other index otherBox)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest joined sample otherSample
      target floor := by
  let firstEndpoint := Coordinates.Overlap.Endpoint.build leftPoint.coordinates sample
  let otherEndpoint := Coordinates.Overlap.Endpoint.build leftPoint.coordinates otherSample
  let originalOther := Coordinates.Overlap.Endpoint.build rightPoint.coordinates otherSample
  let firstChart := ChartRequest.build firstEndpoint target positive floor
  let otherChart := ChartRequest.build otherEndpoint target positive floor
  have agrees : Gaussian.Equivalence.Equivalent originalOther.approximation otherEndpoint.approximation :=
    originalOther.sampled_agreement.symm.trans
      (Equivalent.trans (joined.primitiveEquivalent otherSample).symm otherEndpoint.sampled_agreement)
  let transport := agrees.compare floor floor target positive
  exact ⟨firstEndpoint, otherEndpoint, originalOther, firstChart, otherChart, transport,
    max firstChart.stage (max otherChart.stage (max transport.leftIndex transport.rightIndex)), rfl⟩

set_option genInjectivity false in
/-- Paired readings at one later retained stage with exact shared coordinate identity and paid original-owner transport.
-/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest
  joined sample otherSample target floor) (stage : Nat) where
  /-- The first differential endpoint or reading on the original shared coordinate. -/ first :
    ChartReadings.Endpoint.Reading request.first stage
  /-- The second differential endpoint or reading using that same retained coordinate. -/ other :
    ChartReadings.Endpoint.Reading request.other stage
  /-- Both evaluated differential readings use exactly the same retained coordinate value. -/ coordinate_eq :
    first.coordinate = other.coordinate
  /-- The separately retained second endpoint or reading on its original coordinate owner. -/ originalOther :
    ChartReadings.Endpoint.Reading request.originalOther stage
  /-- The first original differential's retained chart request or its certified evaluation. -/ firstChart :
    ChartRequest.Evaluation request.firstChart first
  /-- The second original differential's retained chart request or its certified evaluation. -/ otherChart :
    ChartRequest.Evaluation request.otherChart other
  /-- The original second-owner reading differs from the shared-coordinate reading by less than the original target. -/
    transported : Data.Gaussian.Norm.Basic.normSq (originalOther.value - other.value) < target

constructive_injectivity Evaluation

/-- Read the common coordinate once, evaluate both retained differential factors and certify transport from the original
second owner. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest
  joined sample otherSample target floor) (stage : Nat)
    (later : request.stage ≤ stage) :
      Evaluation request stage := by
  let firstReading := ChartReadings.Endpoint.Reading.build request.first stage
  let otherReading : ChartReadings.Endpoint.Reading request.other stage :=
    ⟨firstReading.coordinate, firstReading.coordinate_eq, firstReading.coordinate * request.other.coefficient, rfl⟩
  let originalOther := ChartReadings.Endpoint.Reading.build request.originalOther stage
  have after := request.stage_eq.symm.trans_le later
  have firstLater := (Purelib.Data.Nat.Order.le_max_left _ _).trans after
  have otherLater := (Purelib.Data.Nat.Order.le_max_left _ _).trans ((Purelib.Data.Nat.Order.le_max_right _ _).trans
    after)
  have transportLater := (Purelib.Data.Nat.Order.le_max_right _ _).trans ((Purelib.Data.Nat.Order.le_max_right _
    _).trans after)
  have bounded := request.transport.close ((Purelib.Data.Nat.Order.le_max_left _ _).trans transportLater)
    ((Purelib.Data.Nat.Order.le_max_right _ _).trans transportLater)
  have transported : Data.Gaussian.Norm.Basic.normSq (originalOther.value - otherReading.value) < target := by
    rw [originalOther.sample_eq, otherReading.sample_eq]
    exact bounded
  exact ⟨firstReading, otherReading, rfl, originalOther,
    request.firstChart.evaluate firstReading firstLater, request.otherChart.evaluate otherReading otherLater,
      transported⟩

/-- Evaluate the paired original chart request at its retained common stage. -/
@[expose] def acquire (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest
  joined sample otherSample target floor) :
  Evaluation request request.stage :=
  request.evaluate request.stage le_rfl

end PairedChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
