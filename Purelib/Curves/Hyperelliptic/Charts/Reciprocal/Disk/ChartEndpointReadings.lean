module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
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

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs

/-!
# Original endpoint-pair certificates from the retained chart readings

The full chart polygon already owns its endpoint samples. Transport those
same records through the certified owner equalities, then construct the
original pair certificate without another polynomial or root evaluation.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap (Endpoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {model : UniformReciprocalRootChannels.RootModel cell} {parameter :
    Coordinate}
  {index stage : Nat} {box : Geometry.Rational.Box} {sample :
    Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- An endpoint reading of the actual retained cap point at the supplied polynomial sample and reading stage. -/
structure ReadingView (point : Point cap model parameter)
    (sample : Primitives.Sample cap differential index box) (stage : Nat) where
  /-- The actual endpoint determined by this retained point and cap polynomial sample. -/ endpoint :
    Endpoint point.coordinates sample
  /-- The cached coordinate and primitive reading on this exact endpoint at the supplied stage. -/ reading :
    ChartReadings.Endpoint.Reading endpoint stage

constructive_injectivity ReadingView

namespace ReadingView

variable {first last : Point cap model parameter}
  {endpoint : Endpoint first.coordinates sample}

/-- Transport the retained endpoint reading along equality of its actual point owner without evaluating a second
reading. -/
@[expose] def ofEqual (equal : first = last) (reading : ChartReadings.Endpoint.Reading endpoint stage) :
  ReadingView last sample stage := by
  cases equal
  exact ⟨endpoint, reading⟩

/-- Transport along equal point owners preserves the exact cached primitive value. -/
theorem value_eq (equal : first = last) (reading : ChartReadings.Endpoint.Reading endpoint stage) :
    (ofEqual equal
      reading).reading.value = reading.value := by
  cases equal
  rfl

/-- Transport along equal point owners preserves the exact cached coordinate value. -/
theorem coordinate_eq (equal : first = last) (reading : ChartReadings.Endpoint.Reading endpoint stage) :
    (ofEqual equal
      reading).reading.coordinate = reading.coordinate := by
  cases equal
  rfl

end ReadingView
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Evaluation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs (PairRequest)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {owners :
    ParentOwners.OwnedEndpoints regular cell}
  {comparison : ArcSamples.Data regular cell} {target pairTarget :
    Coordinate} {floor pairFloor : Nat}
  {index depth stage minimum : Nat} {box : Geometry.Rational.Box}
  {capSample : Primitives.Sample cap differential index box}
  {source : UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : AreaRequest comparison owners target
    floor}
  {charts : ChartMesh request.mesh capSample minimum}
  {original : ParentCells.ComparedCell comparison source capSample
    depth}

set_option genInjectivity false in
/-- The original pair-request evaluation on the actual first and last cached chart readings.

Coordinate and primitive-value equalities identify both retained endpoint readings with the complete chart path, without
replacing either owner. -/
structure EndpointPair (evaluated : Evaluation charts original stage) (pairRequest :
  PairRequest owners.bounds pairTarget pairFloor) where
  /-- The cached evaluation of the original pair request at this retained sample and stage. -/ pair :
    PairRequest.Evaluation pairRequest original.sample stage
  /-- The first retained pair coordinate is exactly the original chart path's first root coordinate. -/ first_coordinate
    : pair.firstReading.coordinate = evaluated.vertices.first.root.coordinate
  /-- The last retained pair coordinate is exactly the original chart path's last root coordinate. -/ last_coordinate :
    pair.lastReading.coordinate = evaluated.vertices.last.root.coordinate
  /-- The first retained pair value is exactly the original chart path's first primitive value. -/ first_value :
    pair.firstValue = evaluated.vertices.first.root.value
  /-- The last retained pair value is exactly the original chart path's last primitive value. -/ last_value :
    pair.lastValue = evaluated.vertices.last.root.value

constructive_injectivity EndpointPair

/-- Evaluate the original endpoint-pair request using the chart's exact cached first and last readings and their
point-owner equalities. -/
@[expose] def endpointPair (evaluated : Evaluation charts original stage) (pairRequest :
  PairRequest owners.bounds pairTarget pairFloor)
    (modelLater : pairRequest.index ≤ index) (readingLater : pairRequest.readingIndex ≤ stage) :
      EndpointPair evaluated pairRequest :=
      by
  let first := ReadingView.ofEqual
    evaluated.first_owner evaluated.vertices.first.root
  let last := ReadingView.ofEqual
    evaluated.last_owner evaluated.vertices.last.root
  let pair := pairRequest.evaluateWithReadings original.sample first.reading last.reading modelLater readingLater
  exact ⟨pair, ReadingView.coordinate_eq _ _,
    ReadingView.coordinate_eq _ _,
    ReadingView.value_eq _ _,
    ReadingView.value_eq _ _⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Evaluation
