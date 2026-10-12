module
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedVertices
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Mathlib.Order.Basic

@[expose] public section

/-! Requested parent endpoint errors refer to the actual paired numerical totals. -/
namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {areaTarget :
    Purelib.Data.Rat.Fraction.Rational}

open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- The original paired primitive totals are within the retained endpoint target of their numerical total.

The two stored comparison increments and exact paired increment list determine the componentwise bound. -/
def RequestedPrimitiveParent.EndpointBounded {parent : CenteredEdge curve differential}
    (prepared : RequestedPrimitiveParent request parent other count areaTarget) : Prop :=
    PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((⟨prepared.2.2.1.2.2.increment, prepared.2.2.2.val.2.2.increment⟩ : PrimitivePoint).sub
      (PairedIncrementArea.total
        (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments prepared.1))) areaTarget
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Every original requested primitive parent retains its paid paired endpoint comparison. -/
theorem RequestedPrimitiveParent.endpoint_bounded {parent : CenteredEdge curve differential}
    (prepared : RequestedPrimitiveParent request parent other count areaTarget) : prepared.EndpointBounded := by
  constructor
  · rw [← Norm.Basic.normSq_eq_canonical]
    exact Eq.mpr (congrArg (fun total => Data.Gaussian.Norm.Basic.normSq (prepared.2.2.1.2.2.increment - total) ≤
      areaTarget)
      (PreparedNewtonPairedIncrements.PairedBoundaryParent.total_left prepared.1)) (prepared.2.2.1.2.2.bounded.trans
        prepared.2.2.2.property.2.1)
  · rw [← Norm.Basic.normSq_eq_canonical]
    exact Eq.mpr (congrArg (fun total => Data.Gaussian.Norm.Basic.normSq (prepared.2.2.2.val.2.2.increment - total) ≤
      areaTarget)
      (PreparedNewtonPairedIncrements.PairedBoundaryParent.total_right prepared.1))
        (prepared.2.2.2.val.2.2.bounded.trans prepared.2.2.2.property.2.2)
end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent
