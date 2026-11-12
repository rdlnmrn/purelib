module

public import Purelib.RootIsolation.SquareRoot.Preparation.Terminal.Width
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # New acquisitions with internally paid physical widths

Both candidate depths include the computed positive width request's finite
minimum. The original acquisition factory keeps the same source Owner and
root diameter, reuses its original prepared requests and finish cache, and
returns width, root-trace and primitive-mesh payments for its actual chosen
depth. This construction makes no claim about a distinct older execution.
-/

public section

namespace Purelib.RootIsolation.SquareRoot.Preparation.Terminal.AcquiredDyadic

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment GaussianPolynomial)
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint ownerAtStart)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (PrimitiveTraceBudget)
open Purelib.Riemann.Paths
open Purelib.Riemann.Meshes
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment polynomial ambient start finish} {within : segment.WithinAmbient}
variable {owner : Owner (polynomial.eval start)}

namespace WidthAcquisition

/-- The original positive physical width request determines one executable finite minimum depth. -/
def minimum (request : AccuracyRequest) : Nat :=
  Geometric.Search.firstQuarterBelow 1 0 request.tolerance

/-- Increase the original primitive-preferred depth to include the same supplied width minimum. -/
@[expose] def preferredDepth (budget : PrimitiveTraceBudget segment) (required : Nat) : Nat :=
  max budget.preferred.depth required

/-- Increase the original trace-safe depth to include that identical width minimum. -/
@[expose] def safeDepth (budget : PrimitiveTraceBudget segment) (required : Nat) : Nat :=
  max budget.trace.depth required

/-- The increased safe depth preserves the original source Owner's certified trace mesh safety.

The existing original atDepth construction keeps the original clearance,
variation, movement budget and root diameter. Quarter-radius antitonicity
pays its new depth, without preparing or re-isolating another source root.
-/
theorem safe (budget : PrimitiveTraceBudget segment) (required : Nat) :
    Subdivision.DyadicMeshSafe segment zeroEndpoint oneEndpoint (ownerAtStart segment owner)
      (safeDepth budget required) budget.trace.rootDiameter budget.trace.rootDiameter_positive := by
  let later := PreparedPathPrimitiveCover.PreparedTraceBudget.atDepth budget.trace (safeDepth budget required)
    (Data.Nat.Order.le_max_left _ _)
  exact later.meshSafe (ownerAtStart segment owner) (by decide +kernel)

/-- The original complete acquisition result with its unchanged candidate-depth selection certificate. -/
@[expose] def Result (budget : PrimitiveTraceBudget segment) (required : Nat) :=
  { retained : AcquiredDyadic segment within owner budget.trace.rootDiameter budget.trace.rootDiameter_positive //
      retained.depth = preferredDepth budget required ∨ retained.depth = safeDepth budget required }

/-- Run the original acquisition factory once at the two internally strengthened candidate depths. -/
def factory (budget : PrimitiveTraceBudget segment) (required : Nat) :
    Result (within := within) (owner := owner) budget required :=
  AcquiredDyadic.acquire segment within owner budget.trace.rootDiameter budget.trace.rootDiameter_positive
    (preferredDepth budget required) (safeDepth budget required) (safe budget required)

/-- The retained factory is the original complete acquisition with both computed candidate depths. -/
theorem factory_eq (budget : PrimitiveTraceBudget segment) (required : Nat) :
    factory (within := within) (owner := owner) budget required =
      AcquiredDyadic.acquire segment within owner budget.trace.rootDiameter budget.trace.rootDiameter_positive
        (preferredDepth budget required) (safeDepth budget required) (safe budget required) := by
  unfold factory
  rfl

/-- The exact retained complete acquisition is the original strengthened candidate-depth factory result. -/
@[irreducible, expose] def FactoryCache (budget : PrimitiveTraceBudget segment) (required : Nat)
    (retained : Result (within := within) (owner := owner) budget required) : Prop :=
  retained = factory budget required

end WidthAcquisition

/-- An original width-paid acquisition retaining its computed minimum and entire original successful result.

The original primitive/trace budget, segment, source Owner and request remain
indices. The complete factory identity preserves the chosen depth witness,
prepared subdivision, exact requests and terminal Owner caches together.
-/
@[expose] def WidthAcquisition (budget : PrimitiveTraceBudget segment) (request : AccuracyRequest) :=
  Σ required : { retained : Nat // retained = WidthAcquisition.minimum request },
    { retained : WidthAcquisition.Result (within := within) (owner := owner) budget required.val //
        WidthAcquisition.FactoryCache budget required.val retained }

namespace WidthAcquisition

variable {budget : PrimitiveTraceBudget segment} {request : AccuracyRequest}

/-- Retain the completed minimum and entire original strengthened acquisition without executing them again. -/
@[expose] def ofCompleted (required : Nat) (required_eq : required = minimum request)
    (retained : Result (within := within) (owner := owner) budget required)
    (retained_eq : FactoryCache budget required retained) :
    WidthAcquisition (within := within) (owner := owner) budget request :=
  ⟨⟨required, required_eq⟩, ⟨retained, retained_eq⟩⟩

/-- Compute the width minimum and original acquisition once while preserving every completed factory cache. -/
def build (budget : PrimitiveTraceBudget segment) (request : AccuracyRequest) :
    WidthAcquisition (within := within) (owner := owner) budget request :=
  let required := minimum request
  let retained := factory budget required
  ofCompleted required rfl retained (by unfold FactoryCache; rfl)

/-- Automatically cache the original primitive/trace budget and construct a new internally width-paid acquisition.

The admitted original clear segment, ambient containment and complete source
Owner are the only geometric inputs. The same original budget is computed
once and returned with its complete factory equation; no success, depth or
endpoint-equivalence certificate is requested from the consumer.
-/
def prepare (segment : ClearSegment polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Owner (polynomial.eval start)) (request : AccuracyRequest) :
    Σ budget : { retained : PrimitiveTraceBudget segment // retained = PrimitiveTraceBudget.build segment },
      WidthAcquisition (within := within) (owner := owner) budget.val request :=
  let budget := PrimitiveTraceBudget.build segment
  let retained := build budget request
  ⟨⟨budget, rfl⟩, retained⟩

/-- Read the exact computed finite width minimum retained by this acquisition. -/
@[expose] def required (retained : WidthAcquisition (within := within) (owner := owner) budget request) : Nat :=
  retained.1.val

/-- Read the original complete chosen acquisition together with its candidate-depth witness. -/
@[expose] def selected (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    Result (within := within) (owner := owner) budget retained.required := retained.2.val

/-- Read the identical complete acquired result, including its original requests and cached terminal Owner. -/
@[expose] def acquired (retained : WidthAcquisition (within := within) (owner := owner) budget request) :=
  retained.selected.val

/-- Retaining completed caches preserves the identical whole acquired result and its actual terminal Owner. -/
theorem ofCompleted_acquired (required : Nat) (required_eq : required = minimum request)
    (retained : Result (within := within) (owner := owner) budget required)
    (retained_eq : FactoryCache budget required retained) :
    (ofCompleted required required_eq retained retained_eq).acquired = retained.val := rfl

/-- The retained finite minimum is the original complete executable search on the same request. -/
theorem required_eq (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    retained.required = minimum request := retained.1.property

/-- The selected result retains its entire original acquisition-factory identity. -/
theorem selected_eq (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    retained.selected = factory budget retained.required := by
  have cache := retained.2.property
  unfold FactoryCache at cache
  exact cache

/-- The actual acquired depth is one of the two computed strengthened candidate depths. -/
theorem depth_eq (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    retained.acquired.depth = preferredDepth budget retained.required ∨
      retained.acquired.depth = safeDepth budget retained.required := retained.selected.property

/-- Either actual selected depth includes the identical computed finite width minimum. -/
theorem required_le_depth (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    retained.required ≤ retained.acquired.depth := by
  rcases retained.depth_eq with preferred | safeEq
  · rewrite [preferred]
    exact Data.Nat.Order.le_max_right _ _
  · rewrite [safeEq]
    exact Data.Nat.Order.le_max_right _ _

/-- The actual retained request list meets the positive physical width request internally. -/
theorem widthsFit (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    Subdivision.WidthsFit request.tolerance zeroEndpoint retained.acquired.requests := by
  have depthBound := Geometric.Basic.quarterRadius_antitone
    (by decide +kernel : (0 : Fraction.Rational) ≤ 1) retained.required_le_depth
  have paid : Geometric.Basic.quarterRadius 1 retained.required < request.tolerance := by
    rewrite [retained.required_eq]
    exact Geometric.Search.firstQuarterBelow_accurate 1 (by decide +kernel) 0 request.tolerance request.positive
  exact Subdivision.WidthsFit.mono (depthBound.trans paid.le) zeroEndpoint retained.acquired.requests
    retained.acquired.requests_widthsFit

/-- The same actual retained requests preserve the unchanged original trace diameter and movement payments. -/
theorem requestsFit (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    budget.trace.RequestsFit zeroEndpoint retained.acquired.requests := by
  have nonnegative : 0 ≤ budget.trace.variation := by
    rewrite [budget.trace.variation_eq]
    exact Riemann.Branches.ClearSheetContinuation.variationBound_nonneg segment _ _
  rewrite [retained.acquired.requests_eq, Subdivision.tryDyadic_requests segment within zeroEndpoint oneEndpoint
    (ownerAtStart segment owner) retained.acquired.depth budget.trace.rootDiameter budget.trace.rootDiameter_positive
      retained.acquired.success]
  apply budget.trace.dyadicRequests_fit_of_variation (by decide +kernel) _ _ _
    (Fraction.Order.Basic.le_refl _)
  rcases retained.depth_eq with preferred | safeEq
  · rewrite [preferred]
    exact (Geometric.Basic.quarterRadius_antitone nonnegative
      (Data.Nat.Order.le_max_left _ _)).trans budget.preferred_movement
  · rewrite [safeEq]
    have old := budget.trace.leafSmall.le.trans (Fraction.Order.Basic.min_le_right _ _)
    rewrite [budget.trace.leafVariation_eq] at old
    exact (Geometric.Basic.quarterRadius_antitone nonnegative (Data.Nat.Order.le_max_left _ _)).trans old

/-- The actual chosen depth also preserves the original primitive bounds' common-neighborhood payment. -/
theorem meshSmall (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    Geometric.Basic.quarterRadius (Canonical.normSq (finish - start)) retained.acquired.depth <
      budget.bounds.radius ^ 2 := by
  rcases retained.depth_eq with preferred | safeEq
  · rewrite [preferred]
    exact (Geometric.Basic.quarterRadius_antitone (Canonical.normSq_nonneg _)
      (Data.Nat.Order.le_max_left _ _)).trans_lt budget.preferred.small
  · rewrite [safeEq]
    have depth : budget.mesh.depth ≤ safeDepth budget retained.required := by
      rewrite [← budget.depth_eq]
      exact Data.Nat.Order.le_max_left _ _
    exact (Geometric.Basic.quarterRadius_antitone (Canonical.normSq_nonneg _) depth).trans_lt budget.mesh.small

/-- Construct the original primitive Mesh view at the actual selected depth with the same unchanged Bounds owner. -/
def mesh (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    UniformPrimitiveMesh.Mesh budget.bounds :=
  { depth := retained.acquired.depth
    edgeCount := 2 ^ retained.acquired.depth
    edgeCount_eq := rfl
    small := retained.meshSmall }

/-- The original mesh view uses the identical actual selected depth from the retained acquisition. -/
theorem mesh_depth (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    retained.mesh.depth = retained.acquired.depth := by
  unfold mesh
  rfl

/-- The mesh view's original edges are exactly the same prepared subdivision's retained parameter edges. -/
theorem mesh_eq (retained : WidthAcquisition (within := within) (owner := owner) budget request) :
    retained.acquired.prepared.subdivision.parameterEdges = retained.mesh.edges := by
  change retained.acquired.prepared.subdivision.parameterEdges =
    Riemann.Branches.ClearSheetContinuation.Subdivision.dyadicEdges retained.acquired.depth zeroEndpoint oneEndpoint
  exact Subdivision.tryDyadic_parameterEdges segment within zeroEndpoint oneEndpoint (ownerAtStart segment owner)
    retained.acquired.depth budget.trace.rootDiameter budget.trace.rootDiameter_positive retained.acquired.success

end WidthAcquisition

end Purelib.RootIsolation.SquareRoot.Preparation.Terminal.AcquiredDyadic
