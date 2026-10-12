module
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

@[expose] public section

/-! Full paired area on the actual common Newton-parent child mesh. -/
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedArea

open Purelib.RootIsolation.Newton.Band
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement movement_nonnegative)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)

namespace PairedBoundaryParent
variable {request : PreparedBandRequest fixed target} {parent : CenteredEdge curve differential}
  {other : Differential genus}

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
open Purelib.Riemann.RootContinuation
/-- Bound the original paired increment area by both retained differential densities.

The exact shared dyadic depth and parent movement give four times the square of their density sum times movement. -/
theorem paired_area_density_bound (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area
      (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments
      paired)) ≤
      4 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
        PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) *
        movement parent)^2 :=
  PairedIncrementArea.dyadic_area_bound (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired)
    paired.refinement.first.block.depth
    (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_length paired)
    (add_nonneg (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed
      request.errorPositive.le)
      (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample otherProfile
        request.errorPositive.le))
    (movement_nonnegative parent)
    (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_bounded paired otherProfile)

/-- The original zero-anchored paired trace satisfies the same retained density-area bound. -/
theorem paired_trace_density_bound (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.traceArea PrimitivePoint.zero
      (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired)) ≤
      4 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
        PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) *
        movement parent)^2 := by
  rw [← PairedIncrementArea.area_eq_trace]
  exact PreparedNewtonPairedArea.PairedBoundaryParent.paired_area_density_bound paired otherProfile

end

open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- Cache the paired-area summary of the exact original increment list. -/
def areaSample (paired : PairedBoundaryParent request parent other) :
    PairedIncrementArea.Summary (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired) :=
  PairedIncrementArea.Summary.build (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired)

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- The cached original area value satisfies the retained paired density bound. -/
theorem areaSample_bound (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent) :
    Data.Gaussian.Norm.Basic.normSq (areaSample paired).areaValue ≤
      4 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
        PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) *
        movement parent)^2 := by
  calc
    Data.Gaussian.Norm.Basic.normSq (areaSample paired).areaValue = Data.Gaussian.Norm.Basic.normSq
      (PairedIncrementArea.area
      (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired)) :=
      congrArg Data.Gaussian.Norm.Basic.normSq (areaSample paired).area_eq
    _ ≤ 4 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
      PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) *
      movement parent)^2 := PreparedNewtonPairedArea.PairedBoundaryParent.paired_area_density_bound paired otherProfile

end PairedBoundaryParent
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedArea
