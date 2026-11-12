module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition
public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Covered centered parents of the same actual paid acquisition

The original paid Segment supplies its identical subdivision, primitive
bounds and selected Mesh. New canonical center observations on that exact
subdivision are constructed once and retained. The original CoveredSegment
factory consumes those same caches; no continuation, width preparation,
source attachment or trace is acquired again. The existing covered-parent
and connected-path consumers then read the stored original result directly.

These affine parents record the moving subdivision cells. The original
paid trace still retains its stationary Owner handoffs; their independent
primitive observations require separate comparison payments. No path-list
identity or primitive cancellation follows from this materialization.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredSegment CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates centeredEdges)
open Purelib.Riemann.Meshes
open Purelib.Riemann.Paths.PreparedClearPathModels (ownerAtStart CompleteSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {genus : Nat} {curve : HyperellipticCurve genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
variable (differential : Differential genus) (sheet : Fin 2) (count : Nat)
variable (retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Parents

/-- The same actual stored complete subdivision ends at the certified unit endpoint, with its whole cache unchanged. -/
theorem endpoint_eq : retained.traced.prepared.subdivision.endpoint = UniformPrimitiveMesh.lastEndpoint := by
  have equal := retained.traced.prepared.endpoint_eq
  generalize retained.traced.prepared.subdivision.endpoint = endpoint at equal ⊢
  cases endpoint with
  | mk value inside =>
      cases equal
      rfl

/-- The newly retained center observations are the original canonical factory on the identical paid subdivision. -/
@[irreducible, expose] def CentersCache
    (centers : CenterStates curve differential sheet retained.traced.prepared.subdivision) : Prop :=
  centers = PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet
    retained.traced.prepared.subdivision

/-- Construct the existing covered-segment container from the exact paid geometry and supplied complete center cache. -/
@[expose] def coveredOfCenters
    (centers : CenterStates curve differential sheet retained.traced.prepared.subdivision) :
    CoveredSegment segment within (ownerAtStart segment sourceOwner) differential sheet count :=
  CoveredSegment.ofSubdivision retained.prepared.budget.bounds retained.mesh retained.traced.prepared.subdivision
    retained.edges_eq (endpoint_eq retained) centers count

/-- The entire covered segment is the original factory on these identical paid caches and stored centers. -/
@[irreducible, expose] def CoveredCache
    (centers : CenterStates curve differential sheet retained.traced.prepared.subdivision)
    (covered : CoveredSegment segment within (ownerAtStart segment sourceOwner) differential sheet count) : Prop :=
  covered = coveredOfCenters differential sheet count retained centers

end Parents

/-- One materialized covered parent family retaining the identical paid subdivision and its new actual center caches.

The original paid Segment is an input throughout. The first stored value
is the complete canonical center family on its actual traced subdivision;
the second is the existing CoveredSegment constructed from that same family,
original primitive bounds and selected Mesh. Neither a new root Owner nor
a replacement subdivision is introduced.
-/
@[expose] def Parents :=
  Σ centers : { cache : CenterStates curve differential sheet retained.traced.prepared.subdivision //
      Parents.CentersCache differential sheet retained cache },
    { covered : CoveredSegment segment within (ownerAtStart segment sourceOwner) differential sheet count //
      Parents.CoveredCache differential sheet count retained centers.val covered }

namespace Parents

/-- Construct and store canonical centers once, then cover those same actual original paid subdivision parents. -/
def build : Parents differential sheet count retained :=
  let centers := PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet
    retained.traced.prepared.subdivision
  let covered := coveredOfCenters differential sheet count retained centers
  ⟨⟨centers, by unfold CentersCache; rfl⟩, ⟨covered, by unfold CoveredCache; rfl⟩⟩

variable (parents : Parents differential sheet count retained)

/-- Read the complete newly selected original center observations on the identical actual paid subdivision. -/
@[expose] def centers : CenterStates curve differential sheet retained.traced.prepared.subdivision := parents.1.val

/-- Read the existing covered-segment result containing the same original paid subdivision, bounds, Mesh and centers. -/
@[expose] def covered : CoveredSegment segment within (ownerAtStart segment sourceOwner)
    differential sheet count := parents.2.val

/-- The newly materialized center family has the exact original canonical-observation factory identity. -/
theorem centers_eq : parents.centers = PreparedSubdivisionAutomaticModels.canonicalCenterStates
    curve differential sheet retained.traced.prepared.subdivision := by
  have cached := parents.1.property
  unfold CentersCache at cached
  exact cached

/-- The whole covered-segment result consumes the exact retained paid caches and same persisted center family. -/
theorem covered_eq : parents.covered = coveredOfCenters differential sheet count retained parents.centers := by
  have cached := parents.2.property
  unfold CoveredCache at cached
  exact cached

/-- The covered consumer uses the literal original actual traced subdivision, without another preparation. -/
theorem subdivision_eq : parents.covered.subdivision = retained.traced.prepared.subdivision := by
  rewrite [parents.covered_eq]
  rfl

/-- The covered consumer retains the exact original primitive bounds of the same paid acquisition. -/
theorem bounds_eq : parents.covered.bounds = retained.prepared.budget.bounds := by
  rewrite [parents.covered_eq]
  rfl

/-- The covered consumer retains the same actual chosen Mesh, including its original depth and edge-count cache. -/
theorem mesh_heq : HEq parents.covered.mesh retained.mesh := by
  rewrite [parents.covered_eq]
  rfl

/-- The covered consumer uses the identical whole center family already materialized on this actual subdivision. -/
theorem covered_centers_heq : HEq parents.covered.centers parents.centers := by
  rewrite [parents.covered_eq]
  rfl

/-- The original parent extraction consumes the same paid subdivision and identical stored new center observations. -/
theorem parents_eq : parents.covered.parents = centeredEdges curve differential sheet
    retained.traced.prepared.subdivision parents.centers := by
  rewrite [parents.covered_eq]
  rfl

/-- Read the original cover on this actual stored parent list, preserving each patch and endpoint certificate. -/
@[expose] def coveredParents : CoveredParents count parents.covered.parents := parents.covered.covered

/-- The original stored trace finish and the exact covered consumer's terminal Owner name the same full root. -/
theorem finishName_eq : ownerRootName retained.traced.finishOwner.parameterNonzero retained.traced.finishOwner =
    ownerRootName parents.covered.subdivision.terminalOwner.parameterNonzero
      parents.covered.subdivision.terminalOwner := by
  rewrite [parents.covered_eq]
  change ownerRootName retained.traced.finishOwner.parameterNonzero retained.traced.finishOwner =
    ownerRootName retained.traced.prepared.subdivision.terminalOwner.parameterNonzero
      retained.traced.prepared.subdivision.terminalOwner
  have terminals := congrArg (fun prepared : CompleteSegment segment within sourceOwner =>
    ownerRootName prepared.subdivision.terminalOwner.parameterNonzero prepared.subdivision.terminalOwner)
    retained.traced_prepared_eq
  exact (Segment.finishName_eq retained).trans terminals.symm

end Parents

end Acquisition.Segment

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
