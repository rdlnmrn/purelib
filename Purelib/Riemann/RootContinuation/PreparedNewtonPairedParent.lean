module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.RootIsolation.State.Raw

import Purelib.Riemann.RootContinuation.PreparedNewtonBandRefinement
public import Purelib.Riemann.Integration.PreparedPairedModelAccuracy

public section

/-! Both differential samples on a Newton parent reuse one checked root mesh. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent

open Purelib
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)

open Purelib.RootIsolation.Newton.Band
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
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

open Purelib.Riemann in
open Purelib.Curves in
set_option genInjectivity false in
/-- Retain two differential samples on one original Newton-boundary parent and checked root mesh.

The original boundary certificate and paired refinement use the same retained Newton request and its model-error
allowance. -/
structure PairedBoundaryParent (request : PreparedBandRequest fixed target)
    (parent : CenteredEdge curve differential) (other : Hyperelliptic.Differentials.Basic.Differential genus) where
  /-- The original parent lies on the retained Newton sample's boundary. -/ boundary : ParentOnBoundary parent
    request.sample.output.box
  /-- The paired differential refinement sharing the original parent and request allowance. -/ refinement :
    Integration.PreparedPairedModelAccuracy.PairedRequest parent other request.error

constructive_injectivity PairedBoundaryParent

namespace PairedBoundaryParent
variable {request : PreparedBandRequest fixed target} {parent : CenteredEdge curve differential}
  {other : Differential genus}

open Purelib.Riemann in
open Purelib.Curves in
/-- Build both differential refinements from the same proper boundary parent.

The retained Newton error supplies both accuracy targets while the original boundary and root geometry are reused. -/
@[expose] def build (request : PreparedBandRequest fixed target) (parent : CenteredEdge curve differential)
    (other : Hyperelliptic.Differentials.Basic.Differential genus) (boundary : ParentOnBoundary parent
      request.sample.output.box)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) :
    PairedBoundaryParent request parent other :=
  ⟨boundary, Integration.PreparedPairedModelAccuracy.PairedRequest.build parent other proper request.error request.error
    request.errorPositive le_rfl 0⟩

open Purelib.Riemann
open Purelib.Integration
open Purelib.Data
/-- The first actual refined integral sample is bounded by its retained Newton density times original parent movement.
-/
theorem first_integral_density_bound (paired : PairedBoundaryParent request parent other) :
    Data.Gaussian.Norm.Basic.normSq (Polynomial.Gaussian.Path.Basic.PathModel.mk
      (paired.refinement.first.block.children.map CenteredEdge.model)).integralSample ≤
      RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error *
        Readings.PreparedPrimitiveRequests.movement parent := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact RootContinuation.PreparedNewtonBandSamples.Sample.dyadic_prepared_integral_bound request.sample fixed
    paired.refinement.first.block.children
    paired.refinement.first.block.depth paired.refinement.first.block.childCount
    (Readings.PreparedPrimitiveRequests.movement parent) request.error request.errorPositive.le
    (paired.boundary.child_starts paired.refinement.first.block)
    (fun _ member => paired.refinement.first_error member) request.error_accurate
    (fun _ member => Paths.PreparedPrimitivePaths.block_movement_le paired.refinement.first.block member)

/-- The second actual refined integral sample satisfies its own differential-profile density bound.

Recasting preserves the same original parent movement and boundary geometry. -/
theorem second_integral_density_bound (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent) :
    Data.Gaussian.Norm.Basic.normSq (Polynomial.Gaussian.Path.Basic.PathModel.mk
      (paired.refinement.second.block.children.map CenteredEdge.model)).integralSample ≤
      RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error *
        Readings.PreparedPrimitiveRequests.movement parent := by
  have boundary : ParentOnBoundary (recastCenteredEdge other parent) request.sample.output.box :=
    ⟨paired.boundary.startInside, paired.boundary.finishInside, paired.boundary.side⟩
  have bound := RootContinuation.PreparedNewtonBandSamples.Sample.dyadic_prepared_integral_bound request.sample
    otherProfile paired.refinement.second.block.children
    paired.refinement.second.block.depth paired.refinement.second.block.childCount
    (Readings.PreparedPrimitiveRequests.movement (recastCenteredEdge other parent)) request.error
      request.errorPositive.le
    (boundary.child_starts paired.refinement.second.block)
    (fun _ member => (paired.refinement.second.child_error member).trans paired.refinement.accuracy_le)
      request.error_accurate
    (fun _ member => Paths.PreparedPrimitivePaths.block_movement_le paired.refinement.second.block member)
  have movement_eq : Readings.PreparedPrimitiveRequests.movement (recastCenteredEdge other parent) =
      Readings.PreparedPrimitiveRequests.movement parent := rfl
  rw [movement_eq] at bound
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bound

end PairedBoundaryParent
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
