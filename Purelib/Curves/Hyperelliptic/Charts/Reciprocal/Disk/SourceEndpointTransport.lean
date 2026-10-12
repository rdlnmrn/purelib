module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Riemann

public section

/-! Transport actual cell pullback endpoints to the basis bank's retained
root owner. Root-owner agreement is operational, never equality of samples. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Approximation.Gaussian.Equivalence (Equivalent Comparison)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus count otherCount index : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherParent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve other}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge}
  {cell : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge} {otherCell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell otherData otherEdge}
  {model : Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell} {otherModel :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel otherCell} {parameter otherParameter :
    Normalization.InverseRootPolynomial.Coordinate}
  {anchor : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter} {source :
    Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap otherModel otherParameter}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {bounds : Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular source}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index box}

set_option genInjectivity false in
/-- The source request precedes polynomial selection. Only owner transport
is selected afterwards, and it changes the reading stage, not the polynomials. -/
structure SourceEndpointTransport (joined : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join anchor source)
    (request : Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request bounds target floor) (destination :
      Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint anchor.coordinates sample) where
  /-- The endpoint of the original source root owner with the same retained primitive sample. -/ original :
    Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint source.coordinates sample
  /-- The requested comparison between the original and destination endpoint approximation streams. -/ comparison :
    Gaussian.Equivalence.Comparison original.approximation destination.approximation floor floor target
  /-- The cached sufficient stage for the source reading and both comparison readings. -/ stage : Nat
  /-- The stage is exactly the maximum of the original coordinate and retained comparison indices. -/ stage_eq : stage =
    max request.coordinate.rightIndex (max comparison.leftIndex comparison.rightIndex)

constructive_injectivity SourceEndpointTransport

namespace SourceEndpointTransport

variable {joined : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join anchor source} {request :
  Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request bounds target floor}
  {destination : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint anchor.coordinates sample}

/-- Construct the original source endpoint and its owner-agreement comparison to the retained destination, then cache
one sufficient reading stage. -/
@[expose] def build (joined : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join anchor source) (request :
  Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request bounds target floor)
    (destination : Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint anchor.coordinates sample) :
      SourceEndpointTransport joined request destination :=
  let original := Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint.build source.coordinates sample
  let agrees : Equivalent original.approximation destination.approximation :=
    original.sampled_agreement.symm.trans
      (Equivalent.trans (joined.primitiveEquivalent sample).symm destination.sampled_agreement)
  let comparison := agrees.compare floor floor target request.positive
  ⟨original, comparison, max request.coordinate.rightIndex (max comparison.leftIndex comparison.rightIndex), rfl⟩

/-- The source cell keeps its own inverse polynomial. The destination is
the same endpoint later consumed by the shared-coordinate basis evaluation. -/
theorem accurate (transport : SourceEndpointTransport
  joined request destination)
    {comparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular otherCell}
    (retained : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison sample)
    (modelLater : request.index ≤ index) {stage : Nat} (later : transport.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (retained.pullback.value.eval (otherParent.edge.point otherParameter)⁻¹ -
      destination.approximation.sample stage) < 4 * target := open Purelib.Data.Rat in by
  have indices := transport.stage_eq.symm.trans_le later
  have originalClose := request.accurate retained transport.original modelLater ((Purelib.Data.Nat.Order.le_max_left _
    _).trans indices)
  have transportIndices := (Purelib.Data.Nat.Order.le_max_right _ _).trans indices
  have transported := transport.comparison.close ((Purelib.Data.Nat.Order.le_max_left _ _).trans transportIndices)
    ((Purelib.Data.Nat.Order.le_max_right _ _).trans transportIndices)
  exact (Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct originalClose transported)).trans_eq (by ring1))

end SourceEndpointTransport

namespace SourceEndpointTransport

/-- Specialize owner transport to a cached basis entry, preserving both
the original source sample and the root coordinate used by the energy fan. -/
theorem basis_source_accurate
    {row : Fin genus} {otherParent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve
      (Periods.PeriodMatrix.standardDifferential row)}
    {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch otherParent}
    {otherData : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
    {otherCell : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell otherData otherEdge} {otherModel :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel otherCell}
    {source : Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap otherModel otherParameter} (joined :
      Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Join anchor source)
    {bounds : Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Data regular source}
    {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
    {basisTarget : Normalization.InverseRootPolynomial.Coordinate} {basisFloor : Nat}
    {basis : Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings.BasisChartRequest anchor.coordinates polynomials
      basisTarget basisFloor}
    {request : Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison.Request bounds target floor}
    (transport : SourceEndpointTransport joined request
      (basis.entries.get row).endpoint)
    {comparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular otherCell}
    (retained : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison (polynomials.get row))
    {coordinate : Normalization.InverseRootPolynomial.Gaussian} {stage : Nat} (evaluated : basis.Evaluation coordinate
      stage)
    (modelLater : request.index ≤ index) (later : transport.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (retained.pullback.value.eval (otherParent.edge.point otherParameter)⁻¹ -
      evaluated.direct row) < 4 * target := by
  rw [evaluated.direct_eq]
  exact transport.accurate retained modelLater later

end SourceEndpointTransport

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
