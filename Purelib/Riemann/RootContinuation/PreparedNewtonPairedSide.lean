module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSides
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
public import Purelib.Riemann.Paths.TracedCoveredSegment
public import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic

open Purelib.Data

public section

/-! Complete paired Newton sides share covered geometry and cache the full area. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide

open Purelib.RootIsolation.Newton.Band
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredSegment Owner)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)
open Purelib.Riemann.Paths.UniformPreparedBoundarySegments.CoveredSegment (finishOwner parent_boundary parent_movement)
open _root_.Purelib.Riemann.Paths (TracedCoveredSegment)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank.PairedBoundaryParents (incrementBlocks)
open Purelib.Integration.Path.PairedIncrementArea (Summary)
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
set_option genInjectivity false in
/-- An original covered side with retained trace budget, paired refinements and cached area summary.

The source owner, segment, sheet and band request index the actual covered parents and their shared ordered paired
increments. -/
structure PairedBoundarySide (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential
  genus)
    {start finish : Basic.Canonical} (segment : Geometry.ClearPath.ClearSegment curve.polynomial
      request.sample.output.box start finish)
    (within : segment.WithinAmbient) (owner : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval start))
      (sheet : Fin 2) where
  /-- The original covered segment at the retained owner, differential and sheet. -/ covered :
    Observation.UniformPreparedMesh.CoveredSegment segment within (ownerAtStart segment owner) differential sheet 0
  /-- The retained trace budget for the original segment endpoints. -/ traceBudget :
    Paths.PreparedTraceBudget segment firstEndpoint lastEndpoint
  /-- The actual cached subdivision requests fit the retained trace budget. -/ traceFits : traceBudget.RequestsFit
    firstEndpoint covered.subdivision.requests
  /-- The paired refinement bank for the exact original covered-parent list. -/ refined : PairedBoundaryParents request
    other covered.parents
  /-- The cached summary of the retained flattened paired increments. -/ summary : PairedIncrementArea.Summary
    refined.incrementBlocks.flatten

constructive_injectivity PairedBoundarySide

namespace PairedBoundarySide
variable {request : PreparedBandRequest fixed target} {other :
  Differential genus} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment curve.polynomial request.sample.output.box start finish}
  {within : segment.WithinAmbient} {owner :
    Owner (curve.polynomial.eval start)} {sheet
    : Fin 2}

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- Retain a traced covered side and build its original paired-parent bank.

The same-side witness supplies each parent's boundary condition; original properness proofs determine the refinements
and cached flattened summary. -/
@[expose] def ofTraced (traced : TracedCoveredSegment segment within (ownerAtStart segment owner) differential sheet 0)
    (other : Differentials.Basic.Differential genus) (side : SameSide request.sample.output.box start finish) :
    PairedBoundarySide request other segment within owner sheet :=
  let covered := traced.covered
  let refined := PreparedNewtonPairedBank.PairedBoundaryParents.build request other covered.parents
    (fun _ member => UniformPreparedBoundarySegments.CoveredSegment.parent_boundary covered side member)
    (fun _ member => Observation.UniformPreparedMesh.CoveredSegment.parent_proper covered member)
  ⟨covered, traced.budget, traced.fits, refined, PairedIncrementArea.Summary.build refined.incrementBlocks.flatten⟩

open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Prepare the original traced side and its paired boundary refinements.

The original start owner, sheet, segment and same-side witness remain indices of the retained covered segment and area
cache. -/
@[expose] def build (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential genus)
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish) (within :
      segment.WithinAmbient)
    (side : SameSide request.sample.output.box start finish) (owner : Observation.UniformPreparedMesh.Owner
      (curve.polynomial.eval start)) (sheet : Fin 2) :
    PairedBoundarySide request other segment within owner sheet :=
  ofTraced (Paths.TracedCoveredSegment.build segment within (ownerAtStart segment owner) differential
    sheet 0) other side

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Riemann.Paths in
/-- Read the actual terminal owner of the original covered side. -/
@[expose] def finishOwner (side : PairedBoundarySide request other segment within owner sheet) :
  Observation.UniformPreparedMesh.Owner (curve.polynomial.eval finish) :=
    UniformPreparedBoundarySegments.CoveredSegment.finishOwner side.covered

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Bound the retained side's cached paired area by its original endpoint movement.

The original covered mesh count and parent movement bounds give factor 16 times the squared product of both densities
and endpoint distance squared. -/
theorem area_density_bound (side : PairedBoundarySide request other segment within owner sheet)
    (otherProfile : DifferentialProfile profile other.exponent) :
    normSq side.summary.areaValue ≤
      16 * ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
        PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) * normSq (finish -
          start))^2 := by
  rw [side.summary.area_eq]
  have nonnegative : 0 ≤ normSq (finish - start) :=
    Basic.Canonical.normSq_nonneg _
  have movements : ∀ parent ∈ side.covered.parents,
      PreparedPrimitiveRequests.movement parent ≤
        Geometric.Basic.quarterRadius
          (normSq (finish - start)) side.covered.mesh.depth := by
    intro parent member
    exact (UniformPreparedBoundarySegments.CoveredSegment.parent_movement side.covered member).le
  have bounded := PreparedNewtonPairedBank.PairedBoundaryParents.area_density_bound
    side.refined otherProfile (normSq (finish - start)) side.covered.mesh.depth
    nonnegative (side.covered.parents_length.trans side.covered.mesh.edgeCount_eq) movements
  rw [Norm.Basic.normSq_eq_canonical] at bounded
  exact bounded

end PairedBoundarySide
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
