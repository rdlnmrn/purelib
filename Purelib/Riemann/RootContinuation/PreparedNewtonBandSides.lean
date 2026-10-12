module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandBank
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.RootIsolation.Newton.Band.Basic
import Mathlib.Order.Basic

public section

/-!
# Complete prepared Newton-band sides

The initial complete subdivision is constructed, not assumed. Its retained
mesh pays the initial parent count, and the requested direct refinements pay
their individual child counts. The cached model is the actual flattened
integrator. Existing or generated covered subdivisions can be reused without
agreement with the automatic root search.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonBandSides

open Purelib.RootIsolation.Newton.Band
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredSegment Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBank (RefinedBoundaryParents)
open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Basic.Canonical
/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial in
/-- An original cleared band side with a retained covered preparation, exact parent refinements and cached path model.

The source owner and sheet remain original indices, and the stored model equals the exact retained refined child-model
list. -/
structure RefinedBoundarySide (request : PreparedBandRequest fixed target) {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish)
    (within : segment.WithinAmbient) (owner : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval start))
      (sheet : Fin 2) where
  /-- The original covered side preparation from the retained start owner and sheet. -/ covered :
    Observation.UniformPreparedMesh.CoveredSegment segment within (ownerAtStart segment owner) differential sheet 0
  /-- The exact retained refinements of the original covered parent list. -/ refined : RefinedBoundaryParents request
    covered.parents
  /-- The cached path model of the exact original refined children. -/ model : Basic.PathModel
  /-- The cache equals the exact model list of the retained direct child blocks. -/ model_eq : model =
    Basic.PathModel.mk (refined.blocks.children.map CenteredEdge.model)

constructive_injectivity RefinedBoundarySide

namespace RefinedBoundarySide

variable {request : PreparedBandRequest fixed target} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish}
  {within : segment.WithinAmbient} {owner :
    Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval start)} {sheet
    : Fin 2}

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
/-- Refine the original covered side's parents using its exact same-side boundary condition.

Original parent properness and geometry supply the refinement certificates; the path model consumes those exact stored
child blocks. -/
@[expose] def ofCovered (covered : Observation.UniformPreparedMesh.CoveredSegment segment within (ownerAtStart segment
  owner) differential sheet 0)
    (side : SameSide request.sample.output.box start finish) : RefinedBoundarySide request segment within owner sheet :=
  let refined := RefinedBoundaryParents.build request covered.parents
    (fun _ member => UniformPreparedBoundarySegments.CoveredSegment.parent_boundary covered side member) (fun _ member
      => covered.parent_proper member)
  { covered := covered
    refined := refined
    model := Basic.PathModel.mk (refined.blocks.children.map CenteredEdge.model)
    model_eq := rfl }

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Polynomial in
/-- Construct and refine an original cleared Newton-band side from its retained starting owner.

The original covered preparation determines the parent list and uniform mesh, which are passed unchanged to the boundary
refinement constructor. -/
@[expose] def build (request : PreparedBandRequest fixed target)
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish) (within :
      segment.WithinAmbient)
    (side : SameSide request.sample.output.box start finish) (owner : Observation.UniformPreparedMesh.Owner
      (curve.polynomial.eval start)) (sheet : Fin 2) :
    RefinedBoundarySide request segment within owner sheet :=
  ofCovered (Observation.UniformPreparedMesh.CoveredSegment.build segment within (ownerAtStart segment owner)
    differential sheet 0) side

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Paths in
/-- The exact original terminal owner of the retained covered side. -/
@[expose] def finishOwner (side : RefinedBoundarySide request segment within owner sheet) :
  Observation.UniformPreparedMesh.Owner (curve.polynomial.eval finish) :=
  UniformPreparedBoundarySegments.CoveredSegment.finishOwner side.covered

open Purelib.Riemann.Integration in
/-- The connected geometric chain of the exact retained child refinements with original source endpoints and sheet. -/
@[expose] def chain (side : RefinedBoundarySide request segment within owner sheet) :
    PreparedDirectDyadicRefinements.DirectPathChain side.refined.blocks.children
      (start := { coordinate := start, sheet := sheet }) (finish := { coordinate := finish, sheet := sheet }) :=
  side.refined.blocks.refinedChain side.covered.chain.toDirectPathChain

open Purelib.Geometry.Path.Gaussian in
/-- The original algebraic lifted path attached to the exact retained direct refinements. -/
@[expose] def lifted (side : RefinedBoundarySide request segment within owner sheet) :
    Lifted.Basic.LiftedPath 2 { coordinate := start, sheet := sheet } { coordinate := finish, sheet := sheet } :=
  side.refined.blocks.refinedPath side.covered.chain

open Purelib.Curves.Hyperelliptic.Integration in
/-- The original uniform path certificates for the retained child model and its exact algebraic lift. -/
@[expose] def certificates (side : RefinedBoundarySide request segment within owner sheet) :
    Algebraic.Path.Basis.UniformPathCertificates curve differential side.model.cells side.lifted := by
  rw [side.model_eq]
  exact side.refined.blocks.refinedCertificates side.covered.chain

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
/-- The retained original side-model integral satisfies the exact Newton-band target.

The original uniform parent count and movement equations supply the finite refinement-bank estimate on the same retained
band boundary. -/
theorem bound (side : RefinedBoundarySide request segment within owner sheet) : normSq side.model.integralSample ≤
  target := by
  rw [side.model_eq]
  have first : request.sample.output.box.Contains start := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_zero] using segment.pointAt_contains within 0 (by decide)
  have last : request.sample.output.box.Contains finish := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_one] using segment.pointAt_contains within 1 (by decide)
  have movementLe : Data.Gaussian.Norm.Basic.normSq (finish - start) ≤
      32 * request.sample.output.radius ^ 2 :=
    (request.sample.output.box.normSq_sub_le_diagonalSq last first).trans
      (request.sample.output.band.diagonalSq_le request.sample.output.radiusPositive)
  have movements : ∀ parent ∈ side.covered.parents,
      PreparedPrimitiveRequests.movement parent ≤
        Geometric.Basic.quarterRadius
          (Data.Gaussian.Norm.Basic.normSq (finish - start)) side.covered.mesh.depth := by
    intro parent member
    rw [Norm.Basic.normSq_eq_canonical (finish - start)]
    exact (UniformPreparedBoundarySegments.CoveredSegment.parent_movement side.covered member).le
  have bounded := side.refined.bound
    (Data.Gaussian.Norm.Basic.normSq (finish - start)) side.covered.mesh.depth
    (side.covered.parents_length.trans side.covered.mesh.edgeCount_eq) movementLe movements
  rw [Norm.Basic.normSq_eq_canonical] at bounded
  exact bounded

end RefinedBoundarySide

end Purelib.Riemann.RootContinuation.PreparedNewtonBandSides
