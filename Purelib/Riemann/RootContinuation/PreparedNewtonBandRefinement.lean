module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
public import Purelib.Riemann.Integration.PreparedModelAccuracy
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Mathlib.Order.Basic

public section

/-!
# Executed prepared refinements on a requested Newton boundary

The returned numerical error is consumed by a total direct subdivision of
an existing boundary parent. All child boundary, count, movement and error
obligations are derived from the retained subdivision. No primitive model or
caller-supplied analytic inequality is added; the existing direct refinement
owns all root preparation.

The parent must belong to the chosen band boundary. Constructing the complete
boundary parent bank and relating it to punctured-grid holes are separate
geometric tasks.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonBandRefinement

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
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
  {profile : Profile curve.squarefree current.box} {fixed :
    DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

set_option genInjectivity false in
open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
/-- An original boundary parent with a retained accuracy profile and its exact prepared refinement request.

The boundary certificate refers to the original Newton-band box, and the refinement pays the same retained band error
allowance. -/
structure RefinedBoundaryParent (request : PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (parent : CenteredEdge curve differential) where
  /-- The original parent lies on the exact retained Newton-band boundary. -/ boundary : ParentOnBoundary parent
    request.sample.output.box
  /-- The retained movement/error profile of the original parent. -/ accuracyProfile : PreparedModelAccuracy.Profile
    parent
  /-- The exact original child-block request paying the retained band error allowance. -/ refinement :
    PreparedModelAccuracy.Request accuracyProfile request.error

constructive_injectivity RefinedBoundaryParent

open Purelib.Riemann.Integration in
open Purelib.Riemann.RootContinuation in
/-- Refine the original proper boundary parent to the retained Newton-band error allowance.

The exact parent supplies the cached accuracy profile; its retained positive band error drives the original refinement
request. -/
@[expose] def PreparedBandRequest.refineParent (request : PreparedNewtonBandSamples.PreparedBandRequest fixed target)
    (parent : CenteredEdge curve differential)
    (boundary : ParentOnBoundary parent request.sample.output.box)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) :
    PreparedNewtonBandRefinement.RefinedBoundaryParent request parent :=
  let accuracyProfile := PreparedModelAccuracy.Profile.build parent
  { boundary := boundary
    accuracyProfile := accuracyProfile
    refinement := accuracyProfile.request proper request.errorPositive }

namespace RefinedBoundaryParent

open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.Paths
open Purelib.Riemann.Readings
open Purelib.Riemann.RootContinuation
/-- The exact retained refined child integral is bounded by the original prepared density times parent movement. -/
theorem integral_density_bound {request : PreparedNewtonBandSamples.PreparedBandRequest fixed target}
    {parent : CenteredEdge curve differential}
    (refined : PreparedNewtonBandRefinement.RefinedBoundaryParent request parent) :
    Data.Gaussian.Norm.Basic.normSq (Basic.PathModel.mk (refined.refinement.block.children.map
      CenteredEdge.model)).integralSample ≤
      PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error *
        PreparedPrimitiveRequests.movement parent := by
  rw [Norm.Basic.normSq_eq_canonical]
  exact PreparedNewtonBandSamples.Sample.dyadic_prepared_integral_bound request.sample fixed
    refined.refinement.block.children
    refined.refinement.block.depth refined.refinement.block.childCount
    (PreparedPrimitiveRequests.movement parent) request.error request.errorPositive.le
    (refined.boundary.child_starts refined.refinement.block)
    (fun _ member => refined.refinement.child_error member)
    request.error_accurate (fun _ member => PreparedPrimitivePaths.block_movement_le refined.refinement.block member)

/-- The exact retained refined child integral satisfies the original Newton-band target.

Original boundary containment bounds movement by the retained band diameter, while the same child block supplies exact
count, error and geometric movement certificates. -/
theorem bound {request : PreparedNewtonBandSamples.PreparedBandRequest fixed target}
    {parent : CenteredEdge curve differential}
    (refined : PreparedNewtonBandRefinement.RefinedBoundaryParent request parent) :
    Data.Gaussian.Norm.Basic.normSq (Basic.PathModel.mk (refined.refinement.block.children.map
      CenteredEdge.model)).integralSample ≤ target := by
  rw [Norm.Basic.normSq_eq_canonical]
  exact request.bound refined.refinement.block.children refined.refinement.block.depth
    refined.refinement.block.childCount
    (PreparedPrimitiveRequests.movement parent)
    (refined.boundary.movement_le.trans (request.sample.output.band.diagonalSq_le request.sample.output.radiusPositive))
    (refined.boundary.child_starts refined.refinement.block)
    (fun _ member => refined.refinement.child_error member)
    (fun _ member => PreparedPrimitivePaths.block_movement_le refined.refinement.block member)

end RefinedBoundaryParent

end Purelib.Riemann.RootContinuation.PreparedNewtonBandRefinement
