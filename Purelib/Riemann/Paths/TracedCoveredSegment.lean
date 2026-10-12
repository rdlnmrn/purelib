module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Paths.OwnerTracePath
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedDyadicTrace

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

open Purelib.Data

public section

/-! Primitive coverage and root tracing share one retained prepared subdivision. -/
namespace Purelib.Riemann.Paths

namespace TracedCoveredSegment

open Purelib.Data in
/-- The canonical Gaussian rational scalar type. -/
private abbrev Gaussian := Gaussian.Basic.Canonical
open Purelib.Geometry in
/-- A rational rectangular box. -/
private abbrev Box := Rational.Box
open Purelib.Data in
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational

end TracedCoveredSegment

open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredSegment Owner)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh firstEndpoint lastEndpoint)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish} {within :
    segment.WithinAmbient}
  {owner : Owner (curve.polynomial.eval
    (segment.pointAt firstEndpoint.parameter))} {sheet : Fin 2} {count : Nat}

open Purelib.Curves in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- Retain primitive coverage and root tracing on one prepared subdivision.

The coverage keeps the original source owner and sheet, and the trace budget certifies that its exact subdivision
requests fit. -/
structure TracedCoveredSegment
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval (segment.pointAt
      firstEndpoint.parameter)))
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) (count : Nat) where
  /-- The retained covered segment with its original source owner, differential and sheet. -/ covered :
    Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment segment within owner differential sheet
    count
  /-- The root-tracing budget for the original segment endpoints. -/ budget : PreparedTraceBudget segment firstEndpoint
    lastEndpoint
  /-- The actual retained subdivision requests satisfy the root-tracing budget. -/ fits : budget.RequestsFit
    firstEndpoint covered.subdivision.requests

constructive_injectivity TracedCoveredSegment

namespace TracedCoveredSegment

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.Polynomial in
/-- Construct a covered and traced segment at one sufficient dyadic depth.

The depth meets the primitive cover, root safety and tracing floors, while one checked subdivision supplies both the
primitive models and the certified trace requests. -/
@[expose] def build (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) (within :
  segment.WithinAmbient)
    (owner : Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval (segment.pointAt
      firstEndpoint.parameter)))
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) (count : Nat) :
    TracedCoveredSegment segment within owner differential sheet count := by
  let bounds := Bounds.build segment
  let cover := Mesh.build bounds
  let budget := PreparedTraceBudget.build segment firstEndpoint lastEndpoint
  let diameter := min bounds.rootDiameter budget.rootDiameter
  have positive : 0 < diameter := Rat.Fraction.Order.Basic.lt_min bounds.rootDiameter_positive
    budget.rootDiameter_positive
  let safeDepth := Branches.PreparedSheetContinuation.Subdivision.sufficientDyadicDepth segment firstEndpoint
    lastEndpoint diameter
  let depth := max cover.depth (max safeDepth budget.depth)
  let mesh : Mesh bounds :=
    ⟨depth, 2 ^ depth, rfl,
      (quarterRadius_antitone
        (Gaussian.Basic.Canonical.normSq_nonneg (finish - start)) (Nat.Order.le_max_left _ _)).trans_lt cover.small⟩
  have enough : safeDepth ≤ depth := (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)
  have tracedEnough : budget.depth ≤ depth := (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)
  have safe := Branches.PreparedSheetContinuation.Subdivision.dyadicMeshSafe_of_sufficientDepth_le segment
    firstEndpoint lastEndpoint owner depth diameter positive (by decide) enough
  let subdivision := Branches.PreparedSheetContinuation.Subdivision.checkedDyadic segment within firstEndpoint
    lastEndpoint owner
    depth diameter positive safe
  have success := Branches.PreparedSheetContinuation.Subdivision.tryDyadic_eq_some_checkedDyadic segment within
    firstEndpoint lastEndpoint owner depth diameter positive safe
  have meshEq : subdivision.parameterEdges = mesh.edges :=
    Branches.PreparedSheetContinuation.Subdivision.tryDyadic_parameterEdges segment within firstEndpoint lastEndpoint
      owner
      depth diameter positive success
  have endpointEq := Branches.PreparedSheetContinuation.Subdivision.tryDyadic_endpoint segment within firstEndpoint
    lastEndpoint owner
    depth diameter positive success
  let covered := Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment.ofSubdivision bounds mesh
    subdivision meshEq endpointEq
    (Integration.PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet subdivision) count
  refine ⟨covered, budget, ?_⟩
  change budget.RequestsFit firstEndpoint subdivision.requests
  rw [Branches.PreparedSheetContinuation.Subdivision.tryDyadic_requests segment within firstEndpoint lastEndpoint owner
    depth diameter positive success]
  apply budget.dyadicRequests_fit_of_variation (by decide) depth diameter positive
    (Rat.Fraction.Order.Basic.min_le_right _ _)
  have variationNonnegative : 0 ≤ budget.variation := by
    rw [budget.variation_eq]
    exact Branches.ClearSheetContinuation.variationBound_nonneg segment _ _
  apply (quarterRadius_antitone variationNonnegative tracedEnough).trans
  rw [← budget.leafVariation_eq]
  exact budget.leafSmall.le.trans (Rat.Fraction.Order.Basic.min_le_right _ _)

open Purelib.Riemann
/-- The owner path traced along the exact requests of the retained covered subdivision. -/
@[expose] def ownerPath (traced : TracedCoveredSegment segment within owner differential sheet count) :
    Paths.OwnerTracePath.OwnerPath curve.polynomial (segment.pointAt firstEndpoint.parameter) owner
      (segment.pointAt traced.covered.subdivision.endpoint.parameter) traced.covered.subdivision.terminalOwner :=
  Paths.PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath traced.budget traced.covered.subdivision traced.fits

/-- The owner path uses exactly the trace vertices of the retained subdivision requests. -/
theorem vertices_eq (traced : TracedCoveredSegment segment within owner differential sheet count) :
    traced.ownerPath.vertices = Paths.PreparedSubdivisionTrace.PreparedTraceBudget.traceVertices segment firstEndpoint
      traced.covered.subdivision.requests :=
  Paths.PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath_vertices traced.budget traced.covered.subdivision
    traced.fits

end TracedCoveredSegment
end Purelib.Riemann.Paths
