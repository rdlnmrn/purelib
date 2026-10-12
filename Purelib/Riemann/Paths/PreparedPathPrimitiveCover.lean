module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
public import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation

import Purelib.RootIsolation.SquareRoot.Preparation.Terminal
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

public section

/-!
# Primitive coverage and root traces on one retained prepared path

Choose a preferred mesh paying both the uniform primitive radius and the
root-trace budget, with a proved-safe fallback for the actual owner checker.
The accepted preparation and terminal owner are retained together. Coverage
is indexed by that stored preparation, not by a separately generated path.
-/

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedTraceBudget

open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Basic.Canonical
/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Polynomial.Dense.Gaussian in
/-- The dense Gaussian polynomial carrier. -/
private abbrev GaussianPolynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- Increase the retained trace depth while preserving its original variation, clearance and movement budget.

The leaf variation is recomputed at the new depth; geometric antitonicity transfers the existing strict smallness
certificate. -/
@[expose] def atDepth {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {start finish :
  Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish} {left right : Endpoint}
    (budget : PreparedTraceBudget segment left right) (depth : Nat) (later : budget.depth ≤ depth) :
    PreparedTraceBudget segment left right :=
  { budget with
    depth := depth
    leafVariation := Geometric.Basic.quarterRadius budget.variation depth
    leafVariation_eq := rfl
    leafSmall := by
      have nonnegative : 0 ≤ budget.variation := by
        rw [budget.variation_eq]
        exact ClearSheetContinuation.variationBound_nonneg segment _ _
      have small := budget.leafSmall
      rw [budget.leafVariation_eq] at small
      exact (quarterRadius_antitone nonnegative later).trans_lt small }

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedTraceBudget

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels

open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint ownerAtStart PreparedPath CompleteSegment
  Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath (AllEdgesProper dyadicEdges_strictParameterEdges)

open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents CoveredSegment)
open _root_.Purelib.Riemann.Paths (PreparedTraceBudget)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.RootIsolation.SquareRoot.Preparation.Terminal (AcquiredDyadic)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath TracedSegment)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)

set_option genInjectivity false in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- A common subdivision budget for a primitive cover and its original root trace.

The safe mesh and trace retain an exact common depth. A separate preferred mesh carries the movement certificate used by
the finite acquisition attempt. -/
structure PrimitiveTraceBudget {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {start finish :
  Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) where
  /-- The uniform primitive bounds for the original cleared segment. -/ bounds : Bounds segment
  /-- The retained safe primitive mesh for those exact bounds. -/ mesh : Mesh bounds
  /-- The retained root trace budget on the original unit parameter interval. -/ trace : PreparedTraceBudget segment
    zeroEndpoint oneEndpoint
  /-- The safe primitive mesh and trace have exactly the same depth. -/ depth_eq : trace.depth = mesh.depth
  /-- The primitive mesh proposed before using the certified safe fallback. -/ preferred : Mesh bounds
  /-- The preferred depth satisfies the retained trace movement budget. -/ preferred_movement :
    Geometric.Basic.quarterRadius trace.variation preferred.depth ≤ trace.movementBudget

constructive_injectivity PrimitiveTraceBudget

namespace PrimitiveTraceBudget

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Paths in
/-- Build compatible primitive and trace budgets for the original cleared segment.

The safe depth is the maximum of the original two depths. The preferred mesh instead uses the geometric movement search,
retaining each original bound and exact dyadic edge count. -/
@[expose] def build {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Box} {start finish : Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : PrimitiveTraceBudget segment :=
  let bounds := Bounds.build segment
  let mesh := Mesh.build bounds
  let trace := PreparedTraceBudget.build segment zeroEndpoint oneEndpoint
  let movementDepth := Geometric.Search.firstQuarterBelow trace.variation 0 trace.movementBudget
  let preferredDepth := max mesh.depth movementDepth
  let depth := max mesh.depth trace.depth
  { bounds := bounds
    mesh :=
      { depth := depth
        edgeCount := 2 ^ depth
        edgeCount_eq := rfl
        small := (quarterRadius_antitone
          (Basic.Canonical.normSq_nonneg (finish - start)) (Purelib.Data.Nat.Order.le_max_left _ _)).trans_lt mesh.small
            }
    trace := PreparedPathPrimitiveCover.PreparedTraceBudget.atDepth trace depth (Purelib.Data.Nat.Order.le_max_right _
      _)
    depth_eq := rfl
    preferred :=
      { depth := preferredDepth
        edgeCount := 2 ^ preferredDepth
        edgeCount_eq := rfl
        small := (quarterRadius_antitone
          (Basic.Canonical.normSq_nonneg (finish - start)) (Purelib.Data.Nat.Order.le_max_left _ _)).trans_lt mesh.small
            }
    preferred_movement := by
      have nonnegative : 0 ≤ trace.variation := by
        rw [trace.variation_eq]
        exact ClearSheetContinuation.variationBound_nonneg segment _ _
      exact ((quarterRadius_antitone nonnegative (Purelib.Data.Nat.Order.le_max_right
        mesh.depth movementDepth)).trans_lt
        (Geometric.Search.firstQuarterBelow_accurate trace.variation nonnegative 0 trace.movementBudget
          trace.movementBudget_positive)).le }

end PrimitiveTraceBudget

namespace PreparedPath

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Primitive neighborhood meshes attached to the exact segments of an original prepared path.

Every nonempty step retains its bounds, mesh and exact equation identifying the prepared subdivision edges, followed by
the cover of the original tail. -/
inductive PrimitiveCover {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} :
    {start finish : Basic.Canonical} → {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} →
      {owner : Owner (polynomial.eval start)} → PreparedPath path owner → Type
  /-- The empty cover retains the exact original point and root owner. -/ | nil (point : Basic.Canonical) (owner : Owner
    (polynomial.eval point)) : PrimitiveCover (.nil point owner)
  /-- Retain the original segment bounds, exact mesh-edge equation and covered tail. -/ | cons {start middle finish :
    Basic.Canonical} {head : Geometry.ClearPath.ClearSegment polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath polynomial ambient middle finish} {owner : Owner (polynomial.eval start)}
      {within : head.WithinAmbient} {first : CompleteSegment head within owner}
      {rest : PreparedPath tail first.finishOwner}
      (bounds : Bounds head) (mesh : Mesh bounds)
      (mesh_eq : first.subdivision.parameterEdges = mesh.edges)
      (remaining : PrimitiveCover rest) : PrimitiveCover (.cons head tail owner within first rest)

constructive_injectivity PrimitiveCover

namespace PrimitiveCover

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- Transport a primitive cover along equality of its original starting owner. -/
@[expose] def castOwner {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {start finish :
  Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath polynomial ambient start finish} {first second : Owner (polynomial.eval
      start)}
    (equal : first = second) {prepared : PreparedPath path first} (cover : PrimitiveCover prepared) :
    PrimitiveCover (PreparedPathTrace.PreparedPath.castOwner equal prepared) := by
  cases equal
  exact cover

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Every original prepared edge in a primitive-covered path has strictly ordered parameters. -/
theorem proper {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box} :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
      {owner : Owner (polynomial.eval start)} {prepared : PreparedPath path owner},
      PrimitiveCover prepared → AllEdgesProper prepared
  | _, _, _, _, _, .nil _ _ => trivial
  | _, _, _, _, _, .cons _ mesh meshEq remaining => by
      refine ⟨?_, remaining.proper⟩
      rw [meshEq]
      exact dyadicEdges_strictParameterEdges mesh.depth zeroEndpoint oneEndpoint (by decide)

end PrimitiveCover

end PreparedPath

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- An original traced path together with primitive meshes covering its exact retained preparation.

The cover is indexed by the stored prepared path, preserving all segment owners, subdivisions and ordered endpoints. -/
structure CoveredTracedPath {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    {start finish : Basic.Canonical} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (owner : Owner (polynomial.eval start)) where
  /-- The original prepared path and its retained owner trace. -/ traced : TracedPath path owner
  /-- The primitive cover indexed by the exact stored preparation. -/ cover : PreparedPath.PrimitiveCover
    traced.prepared

constructive_injectivity CoveredTracedPath

namespace CoveredTracedPath

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- Acquire a traced path with primitive covers along its original cleared segments.

Each step tries the preferred mesh with a certified safe fallback, reuses the acquired requests and finish owner, and
transports the recursively retained tail cover along that exact owner equality. -/
@[expose] def build {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient
  : Box} :
    ∀ {start finish : Basic.Canonical} (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
      (_within : path.WithinAmbient) (owner : Owner (polynomial.eval start)), CoveredTracedPath path owner
  | _, _, .nil point, _, owner =>
      ⟨TracedPath.build (.nil point) (.nil point) owner, .nil point owner⟩
  | _, _, .cons head tail, within, owner => by
      let budget := PrimitiveTraceBudget.build head
      let acquired := SquareRoot.Preparation.Terminal.AcquiredDyadic.acquire head within.head owner
        budget.trace.rootDiameter budget.trace.rootDiameter_positive
        budget.preferred.depth budget.trace.depth (budget.trace.meshSafe (ownerAtStart head owner) (by decide))
      let first := acquired.val.prepared
      have fits : budget.trace.RequestsFit zeroEndpoint first.subdivision.requests := by
        rw [PreparedSheetContinuation.Subdivision.tryDyadic_requests head within.head
          zeroEndpoint oneEndpoint (ownerAtStart head owner) acquired.val.depth budget.trace.rootDiameter
          budget.trace.rootDiameter_positive acquired.val.success]
        rcases acquired.property with preferred | safe
        · rw [preferred]
          exact budget.trace.dyadicRequests_fit_of_variation (by decide) _ _ _ le_rfl budget.preferred_movement
        · rw [safe]
          exact budget.trace.dyadicRequests_fit (by decide)
      let mesh : Mesh budget.bounds :=
        { depth := acquired.val.depth
          edgeCount := 2 ^ acquired.val.depth
          edgeCount_eq := rfl
          small := by
            rcases acquired.property with preferred | safe
            · rw [preferred]
              exact budget.preferred.small
            · rw [safe, budget.depth_eq]
              exact budget.mesh.small }
      let firstTrace := TracedSegment.ofPrepared budget.trace first fits acquired.val.requests acquired.val.requests_eq
        acquired.val.finishOwner acquired.val.finishOwner_eq
      let rest := build tail within.tail firstTrace.finishOwner
      let traced := TracedPath.cons firstTrace rest.traced
      have meshEq : first.subdivision.parameterEdges = mesh.edges := by
        rw [PreparedSheetContinuation.Subdivision.tryDyadic_parameterEdges head within.head
          zeroEndpoint oneEndpoint (ownerAtStart head owner) acquired.val.depth budget.trace.rootDiameter
          budget.trace.rootDiameter_positive acquired.val.success]
        rfl
      exact ⟨traced, .cons budget.bounds mesh meshEq (rest.cover.castOwner firstTrace.finishOwner_eq)⟩

end CoveredTracedPath

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels
