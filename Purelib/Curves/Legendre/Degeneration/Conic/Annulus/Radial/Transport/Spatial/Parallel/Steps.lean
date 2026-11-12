module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
public import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.Meshes.UniformPrimitiveMesh
public import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Data.List.Membership
import Purelib.Data.List.Map

/-! # Retained original-quarter spatial cover steps

An ordered endpoint list drives original requested-time Reading caches from
one unchanged prepared radial quarter. Each completed target Reading is the
next step's identical source cache. The actual covered spatial block hands
its cached finishOwner to the next block without root re-attachment. Existing
dyadic targets at depth seven pay the sharp spatial geometry internally.

The Steps receipt retains complete Geometry and Covered values, including
the original reading pair, region clearance, Route and primitive preparation.
The existing varying-box Blocks chain is a derived view. Agreement with
original endpoint cubic channels and canonical integral/cut attachment remain
separate geometric certificates. No full-loop runtime receipt is claimed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Approximation.Rational

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
  (Endpoint ParameterEdge parameterEdgesFrom finalTarget dyadicTargets)
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Meshes
open Purelib.Approximation

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}

/-- The exact original requested-time Reading type at a retained subdivision endpoint. -/
@[expose] def ReadingAt (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (endpoint : Endpoint) : Type 1 :=
  Reading actual endpoint.parameter endpoint.inside

/-- The exact original full-cubic continuation Owner type at a retained subdivision endpoint. -/
@[expose] def OwnerAt (site : Fin 2) (parameter : Canonical) (unitQuarter : UnitCircuitQuarter)
    (positive : (0 : Fraction.Rational) < 2) (endpoint : Endpoint) : Type :=
  SquareRootContinuationChain.Owner
    ((Paths.polynomial parameter).eval (coordinate site parameter 2 unitQuarter positive endpoint.parameter))

/-- A complete original endpoint and its retained requested-time Reading cache. -/
@[expose] def Node (actual : Transport.Quarter site parameter 2 unitQuarter positive) : Type 1 :=
  Σ endpoint : Endpoint, ReadingAt actual endpoint

/-- The original target cache is the completed query factory on the identical retained quarter preparation.

The named proposition prevents dependent constructors from expanding the
whole time-query and cubic/cofactor owner construction while retaining its
complete factory identity for consumers.
-/
@[irreducible, expose] def QueryCache (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (endpoint : Endpoint) (reading : ReadingAt actual endpoint) : Prop :=
  reading = Reading.build actual endpoint.parameter endpoint.inside

namespace QueryCache

/-- The actual original built target Reading satisfies its complete retained query-factory identity. -/
theorem built (actual : Transport.Quarter site parameter 2 unitQuarter positive) (endpoint : Endpoint) :
    QueryCache actual endpoint (Reading.build actual endpoint.parameter endpoint.inside) := by
  unfold QueryCache
  rfl

/-- Read the original endpoint Reading's whole query-factory identity, including cofactor and lift caches. -/
theorem readback {actual : Transport.Quarter site parameter 2 unitQuarter positive} {endpoint : Endpoint}
    {reading : ReadingAt actual endpoint} (retained : QueryCache actual endpoint reading) :
    reading = Reading.build actual endpoint.parameter endpoint.inside := by
  unfold QueryCache at retained
  exact retained

end QueryCache

/-- Every original consecutive parameter edge pays the same depth-seven squared-width allowance. -/
@[expose] def WidthPayments (current : Endpoint) (targets : List Endpoint) : Prop :=
  ∀ edge ∈ parameterEdgesFrom current targets,
    (edge.right.parameter - edge.left.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7

namespace Steps

/-- The original spatial receipt family indexed first by its unchanged target-list spine.

Only the list is matched structurally. The original current endpoint,
Reading and source Owner remain parameters within each branch, avoiding
unrelated dependent discrimination of their complete cached objects.
-/
@[expose] def Spine (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) : List Endpoint →
    (current : Endpoint) → ReadingAt actual current → OwnerAt site parameter unitQuarter positive current → Type 1
  | [] => fun _ _ _ => PUnit
  | target :: targets => fun current reading sourceOwner =>
      PSigma fun payment : (target.parameter - current.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7 =>
        Σ targetReading : { retained : ReadingAt actual target // QueryCache actual target retained },
          Σ geometry : Geometry reading targetReading.val regular payment,
            Σ covered : Covered geometry sourceOwner,
              Spine actual regular targets target targetReading.val covered.finishOwner

end Steps

/-- Ordered original quarter queries and complete covered spatial blocks with actual cached owner handoffs.

The exact spine alias retains the current endpoint, Reading, source Owner
and target list in their original order. Each indexed sigma entry retains
the actual payment, authenticated target Reading, complete Geometry and
Covered values, and dependent tail on the identical target cache and actual
finishOwner. No new datatype equality family is generated.
-/
@[expose] def Steps (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint) (reading : ReadingAt actual current)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) (targets : List Endpoint) : Type 1 :=
  Steps.Spine actual regular targets current reading sourceOwner

namespace Steps

variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {current : Endpoint} {reading : ReadingAt actual current}
variable {sourceOwner : OwnerAt site parameter unitQuarter positive current} {targets : List Endpoint}

/-- The stationary end preserves the original endpoint, Reading and continuation Owner in its exact indices. -/
@[expose] def nil (current : Endpoint) (reading : ReadingAt actual current)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) :
    Steps actual regular current reading sourceOwner [] := PUnit.unit

/-- Retain a completed paid spatial block and the unchanged dependent tail with exact reading and owner handoffs.

This nonrecursive constructor stores the supplied original Geometry and
Covered caches directly. It consumes their existing factories' data rather
than rebuilding either factory inside the recursive quarter assembly.
-/
@[expose] def cons {target : Endpoint} {targetReading : ReadingAt actual target}
    {payment : (target.parameter - current.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (queried : QueryCache actual target targetReading)
    (geometry : Geometry reading targetReading regular payment) (covered : Covered geometry sourceOwner)
    (tail : Steps actual regular target targetReading covered.finishOwner targets) :
    Steps actual regular current reading sourceOwner (target :: targets) :=
  ⟨payment, ⟨⟨targetReading, queried⟩, ⟨geometry, ⟨covered, tail⟩⟩⟩⟩

/-- Read the entire original target Reading cache retained by the first completed spatial step. -/
@[expose] def nextReading {target : Endpoint}
    (steps : Steps actual regular current reading sourceOwner (target :: targets)) : ReadingAt actual target :=
  steps.2.1.val

/-- The first target is the completed original query on the same retained quarter preparation and exact endpoint. -/
theorem nextReading_eq {target : Endpoint}
    (steps : Steps actual regular current reading sourceOwner (target :: targets)) :
    steps.nextReading = Reading.build actual target.parameter target.inside :=
  QueryCache.readback steps.2.1.property

/-- Read the entire original Geometry cache of the first completed spatial step. -/
@[expose] def headGeometry {target : Endpoint}
    (steps : Steps actual regular current reading sourceOwner (target :: targets)) :
    Geometry reading steps.nextReading regular steps.1 := steps.2.2.1

/-- Read the entire original Covered cache of the first step, retaining its exact supplied continuation Owner. -/
@[expose] def headCovered {target : Endpoint}
    (steps : Steps actual regular current reading sourceOwner (target :: targets)) :
    Covered steps.headGeometry sourceOwner := steps.2.2.2.1

/-- Read the actual original remaining receipt on the first target cache and the first cover's genuine finishOwner. -/
@[expose] def tail {target : Endpoint}
    (steps : Steps actual regular current reading sourceOwner (target :: targets)) :
    Steps actual regular target steps.nextReading steps.headCovered.finishOwner targets := steps.2.2.2.2

/-- Retaining a completed first step preserves its identical complete target Reading. -/
theorem cons_nextReading {target : Endpoint} {targetReading : ReadingAt actual target}
    {payment : (target.parameter - current.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (queried : QueryCache actual target targetReading)
    (geometry : Geometry reading targetReading regular payment) (covered : Covered geometry sourceOwner)
    (remaining : Steps actual regular target targetReading covered.finishOwner targets) :
    (cons queried geometry covered remaining).nextReading = targetReading := rfl

/-- Retaining a completed first step preserves its identical entire original Geometry cache. -/
theorem cons_headGeometry {target : Endpoint} {targetReading : ReadingAt actual target}
    {payment : (target.parameter - current.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (queried : QueryCache actual target targetReading)
    (geometry : Geometry reading targetReading regular payment) (covered : Covered geometry sourceOwner)
    (remaining : Steps actual regular target targetReading covered.finishOwner targets) :
    (cons queried geometry covered remaining).headGeometry = geometry := rfl

/-- Retaining a completed first step preserves its identical entire original Covered cache. -/
theorem cons_headCovered {target : Endpoint} {targetReading : ReadingAt actual target}
    {payment : (target.parameter - current.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (queried : QueryCache actual target targetReading)
    (geometry : Geometry reading targetReading regular payment) (covered : Covered geometry sourceOwner)
    (remaining : Steps actual regular target targetReading covered.finishOwner targets) :
    (cons queried geometry covered remaining).headCovered = covered := rfl

/-- Retaining a completed first step preserves the actual tail and its exact reading/owner handoff indices. -/
theorem cons_tail {target : Endpoint} {targetReading : ReadingAt actual target}
    {payment : (target.parameter - current.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (queried : QueryCache actual target targetReading)
    (geometry : Geometry reading targetReading regular payment) (covered : Covered geometry sourceOwner)
    (remaining : Steps actual regular target targetReading covered.finishOwner targets) :
    (cons queried geometry covered remaining).tail = remaining := rfl

/-- Build on the original endpoint-list spine without discriminating unrelated dependent source caches. -/
private def buildSpine (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) :
    (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
      (sourceOwner : OwnerAt site parameter unitQuarter positive current) → WidthPayments current targets →
        Steps actual regular current reading sourceOwner targets
  | [] => fun current reading sourceOwner _ => nil current reading sourceOwner
  | target :: targets => fun current reading sourceOwner payments =>
      let targetReading := Reading.build actual target.parameter target.inside
      have payment := payments ⟨current, target⟩ (List.Mem.head (parameterEdgesFrom target targets))
      let geometry := Geometry.build reading targetReading regular payment
      let covered := Covered.build geometry sourceOwner
      let remaining := buildSpine actual regular targets target targetReading covered.finishOwner
        (by
          intro edge member
          apply payments edge
          change edge ∈ ({ left := current, right := target } : ParameterEdge) :: parameterEdgesFrom target targets
          exact List.Mem.tail ({ left := current, right := target } : ParameterEdge) member)
      cons (QueryCache.built actual target) geometry covered remaining

/-- Build original spatial cover steps while querying each target once from the same retained prepared quarter.

The original query result becomes both the stored Geometry target and the
recursive source cache. Covered.build consumes the supplied actual source
Owner; its finishOwner is passed onward directly. Later nodes acquire no
additional Source attachment; their original Reading and Covered factories
perform their normal lift construction and genuine spatial preparation.
-/
def build (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint) (reading : ReadingAt actual current)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) (targets : List Endpoint)
    (payments : WidthPayments current targets) : Steps actual regular current reading sourceOwner targets :=
  buildSpine actual regular targets current reading sourceOwner payments

namespace Spine

/-- Read original caches by the same endpoint-list spine, carrying unchanged dependent source arguments. -/
@[expose] def nodes : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
      Steps actual regular current reading sourceOwner targets → List (Node actual)
  | [] => fun current reading _ _ => [⟨current, reading⟩]
  | target :: targets => fun current reading _ steps =>
      ⟨current, reading⟩ :: nodes targets target (Steps.nextReading steps)
        (Steps.headCovered steps).finishOwner (Steps.tail steps)

/-- Read the final original Reading cache on the unchanged endpoint-list spine. -/
@[expose] def finishReading : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
      Steps actual regular current reading sourceOwner targets → ReadingAt actual (finalTarget current targets)
  | [] => fun _ reading _ _ => reading
  | target :: targets => fun _ _ _ steps =>
      finishReading targets target (Steps.nextReading steps)
        (Steps.headCovered steps).finishOwner (Steps.tail steps)

/-- Read the genuine final covered Owner on the unchanged endpoint-list spine. -/
@[expose] def finishOwner : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
      Steps actual regular current reading sourceOwner targets →
        OwnerAt site parameter unitQuarter positive (finalTarget current targets)
  | [] => fun _ _ sourceOwner _ => sourceOwner
  | target :: targets => fun _ _ _ steps =>
      finishOwner targets target (Steps.nextReading steps)
        (Steps.headCovered steps).finishOwner (Steps.tail steps)

/-- Compose completed original covers on the endpoint-list spine and exact cached owner handoffs. -/
@[expose] def blocks : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (steps : Steps actual regular current reading sourceOwner targets) →
      CoveredTracedPath.Blocks (Paths.polynomial parameter)
        (coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner
        (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)
        (finishOwner targets current reading sourceOwner steps)
  | [] => fun _ _ sourceOwner _ => .nil _ sourceOwner
  | target :: targets => fun _ _ _ steps =>
      (Steps.headCovered steps).blocks.append
        (blocks targets target (Steps.nextReading steps) (Steps.headCovered steps).finishOwner (Steps.tail steps))

end Spine

/-- Read the complete original endpoint/Reading caches in order, retaining every shared middle cache once. -/
@[expose] def nodes (steps : Steps actual regular current reading sourceOwner targets) : List (Node actual) :=
  Spine.nodes targets current reading sourceOwner steps

/-- The final original Reading is the exact cache retained by the last step, with the original finalTarget index. -/
@[expose] def finishReading (steps : Steps actual regular current reading sourceOwner targets) :
    ReadingAt actual (finalTarget current targets) := Spine.finishReading targets current reading sourceOwner steps

/-- The final full-cubic continuation Owner is the exact cached handoff from the last actual covered block. -/
@[expose] def finishOwner (steps : Steps actual regular current reading sourceOwner targets) :
    OwnerAt site parameter unitQuarter positive (finalTarget current targets) :=
  Spine.finishOwner targets current reading sourceOwner steps

/-- Retain the unchanged completed covers as the existing Blocks view with exact terminal-owner indices. -/
@[expose] def blocks (steps : Steps actual regular current reading sourceOwner targets) :
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner
      (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter) steps.finishOwner :=
  Spine.blocks targets current reading sourceOwner steps

/-- The original spine projection preserves its same endpoint sequence. -/
private theorem endpointsSpine : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (steps : Steps actual regular current reading sourceOwner targets) →
      (steps.nodes.map fun node => node.1) = current :: targets
  | [] => fun _ _ _ _ => rfl
  | target :: targets => fun current _ _ steps =>
      congrArg (List.cons current)
        (endpointsSpine targets target (nextReading steps) (headCovered steps).finishOwner (tail steps))

/-- The complete retained query caches have exactly the original source and ordered target endpoints. -/
theorem nodes_endpoints (steps : Steps actual regular current reading sourceOwner targets) :
    (steps.nodes.map fun node => node.1) = current :: targets :=
  endpointsSpine targets current reading sourceOwner steps

/-- The original cache spine retains one entry for its source and every unchanged target. -/
private theorem lengthSpine : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (steps : Steps actual regular current reading sourceOwner targets) → steps.nodes.length = targets.length + 1
  | [] => fun _ _ _ _ => rfl
  | target :: targets => fun _ _ _ steps =>
      congrArg Nat.succ
        (lengthSpine targets target (nextReading steps) (headCovered steps).finishOwner (tail steps))

/-- The retained query-cache list contains the original source and one cache for each actual target endpoint. -/
theorem nodes_length (steps : Steps actual regular current reading sourceOwner targets) :
    steps.nodes.length = targets.length + 1 := lengthSpine targets current reading sourceOwner steps

/-- The spatial owner trace is the existing complete Blocks trace of those same original covered/prepared caches. -/
@[expose] def trace (steps : Steps actual regular current reading sourceOwner targets) :
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) sourceOwner
      (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter) steps.finishOwner :=
  steps.blocks.trace

/-- Read the exact ordered original moving-vertex cache through the existing covered Blocks view. -/
@[expose] def movingVertices (steps : Steps actual regular current reading sourceOwner targets) : List Canonical :=
  steps.blocks.movingVertices

/-- The complete original moving cache terminates at the final original quarter coordinate. -/
theorem moving_terminal (steps : Steps actual regular current reading sourceOwner targets) :
    Polygon.Chain.terminal (coordinate site parameter 2 unitQuarter positive current.parameter)
      steps.movingVertices = coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter :=
  steps.blocks.moving_terminal

/-- The actual retained owner trace and original moving-vertex caches have the same raw full-cubic winding. -/
theorem trace_winding_eq (steps : Steps actual regular current reading sourceOwner targets) :
    Polynomial.Winding.Polygon.Basic.chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) steps.trace.vertices =
    Polynomial.Winding.Polygon.Basic.chainRaw (Paths.polynomial parameter)
      (coordinate site parameter 2 unitQuarter positive current.parameter) steps.movingVertices :=
  steps.blocks.trace_winding_eq

/-- Reindex the original cached final Owner along an exact endpoint identity without acquiring another owner. -/
@[expose] def finishOwnerAt (steps : Steps actual regular current reading sourceOwner targets) (endpoint : Endpoint)
    (endpoint_eq : finalTarget current targets = endpoint) : OwnerAt site parameter unitQuarter positive endpoint :=
  RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
    (congrArg (fun endpoint : Endpoint => (Paths.polynomial parameter).eval
      (coordinate site parameter 2 unitQuarter positive endpoint.parameter)) endpoint_eq) steps.finishOwner

/-- Exact endpoint reindexing preserves the complete original final Owner, track and clearance data. -/
theorem finishOwnerAt_heq (steps : Steps actual regular current reading sourceOwner targets) (endpoint : Endpoint)
    (endpoint_eq : finalTarget current targets = endpoint) :
    HEq (steps.finishOwnerAt endpoint endpoint_eq) steps.finishOwner :=
  RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ _

/-- Reindex the identical complete final Reading along an exact retained endpoint identity. -/
@[expose] def finishReadingAt (steps : Steps actual regular current reading sourceOwner targets) (endpoint : Endpoint)
    (endpoint_eq : finalTarget current targets = endpoint) : ReadingAt actual endpoint :=
  endpoint_eq ▸ steps.finishReading

/-- Exact endpoint reindexing preserves the entire original final Reading and its preparation/owner caches. -/
theorem finishReadingAt_heq (steps : Steps actual regular current reading sourceOwner targets) (endpoint : Endpoint)
    (endpoint_eq : finalTarget current targets = endpoint) :
    HEq (steps.finishReadingAt endpoint endpoint_eq) steps.finishReading := by
  cases endpoint_eq
  rfl

/-- The original dyadic target list at depth seven internally pays every actual consecutive chart edge. -/
theorem dyadic_widthPayments :
    WidthPayments UniformPrimitiveMesh.firstEndpoint
      (dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint) := by
  intro edge member
  rewrite [Subdivision.parameterEdgesFrom_dyadicTargets] at member
  have paid := UniformPrimitiveMesh.dyadicEdges_width 7
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint edge member
  have unit : (UniformPrimitiveMesh.lastEndpoint.parameter - UniformPrimitiveMesh.firstEndpoint.parameter) ^ 2 =
      (1 : Fraction.Rational) := by decide +kernel
  rewrite [unit] at paid
  exact paid.le

/-- The exact original depth-seven unit-quarter target list, retained without dependent spine normalization.

This named list is the unchanged original dyadicTargets result. Its opaque
readback prevents a consumer signature from expanding all one hundred
twenty-eight complete dependent spatial steps while preserving exact targets.
-/
@[irreducible, expose] def quarterTargets : List Endpoint :=
  dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint

/-- Read the exact original dyadic target list retained by the unit-quarter receipt. -/
theorem quarterTargets_eq :
    quarterTargets = dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint := by
  unfold quarterTargets
  rfl

/-- The retained original unit-quarter target list pays every actual consecutive parameter edge internally. -/
theorem quarter_widthPayments : WidthPayments UniformPrimitiveMesh.firstEndpoint quarterTargets := by
  rewrite [quarterTargets_eq]
  exact dyadic_widthPayments

/-- An exact retained original unit-quarter target list and its complete dyadic factory identity. -/
@[expose] def TargetCache : Type :=
  { targets : List Endpoint //
      targets = dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint }

namespace TargetCache

/-- Retain a completed original target list without recomputing its dyadic factory. -/
@[expose] def ofCompleted (targets : List Endpoint)
    (retained : targets = dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint) :
    TargetCache := ⟨targets, retained⟩

/-- Compute the original unit-quarter dyadic target list once and retain its whole factory identity. -/
opaque build : TargetCache :=
  let targets := dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
  ofCompleted targets rfl

/-- Read the whole original dyadic factory identity of the exact retained target cache. -/
theorem factory_eq (cache : TargetCache) :
    cache.val = dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint := cache.property

/-- The original retained target cache is the identical exact unit-quarter target-list alias. -/
theorem targets_eq (cache : TargetCache) : cache.val = quarterTargets :=
  cache.factory_eq.trans quarterTargets_eq.symm

/-- The retained original target cache pays every consecutive original unit-quarter parameter edge internally. -/
theorem widthPayments (cache : TargetCache) : WidthPayments UniformPrimitiveMesh.firstEndpoint cache.val := by
  rewrite [cache.targets_eq]
  exact quarter_widthPayments

/-- Retaining a completed target list preserves that identical original list cache. -/
theorem ofCompleted_value (targets : List Endpoint)
    (retained : targets = dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint) :
    (ofCompleted targets retained).val = targets := rfl

end TargetCache

/-- Build paid original spatial steps from one existing source attachment at its unchanged original endpoint.

The identical source continuation Owner enters the existing Steps builder.
The original source certificate, preparation and attachment remain retained
inputs; this operation neither attaches a second owner nor queries the source.
-/
def ofSource (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint) (reading : ReadingAt actual current)
    (prepared : Gaussian.Division.Prepared reading.lift.value) (source : Source reading prepared)
    (targets : List Endpoint) (payments : WidthPayments current targets) :
    Steps actual regular current reading source.attached.owner targets :=
  build actual regular current reading source.attached.owner targets payments

/-- Construct paid original quarter steps on the exact supplied dyadic target cache and existing Source attachment.

The cache's original factory identity and exact initial endpoint derive every
width payment internally. The original cached list itself indexes the Steps;
no target-list recomputation or additional source attachment occurs here.
-/
def ofTargetCache (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) (reading : ReadingAt actual current)
    (prepared : Gaussian.Division.Prepared reading.lift.value) (source : Source reading prepared)
    (cache : TargetCache) : Steps actual regular current reading source.attached.owner cache.val :=
  ofSource actual regular current reading prepared source cache.val (by
    rewrite [initial]
    exact cache.widthPayments)

/-- A completed original quarter retaining one exact target cache and Steps on that identical cached list.

The existing sigma retains the entire target cache with its original factory
identity. Its dependent Steps value preserves the current endpoint, original
Reading and actual supplied continuation Owner while handing genuine cached
finish owners through every covered spatial block.
-/
@[expose] def Quarter (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint) (reading : ReadingAt actual current)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) : Type 1 :=
  Σ cache : TargetCache, Steps actual regular current reading sourceOwner cache.val

namespace Quarter

/-- Retain one completed original target cache and the already constructed Steps on its identical list. -/
@[expose] def ofCompleted (cache : TargetCache)
    (steps : Steps actual regular current reading sourceOwner cache.val) :
    Quarter actual regular current reading sourceOwner := ⟨cache, steps⟩

/-- Read the entire unchanged original target cache retained beside the quarter's completed spatial steps. -/
@[expose] def cache (completed : Quarter actual regular current reading sourceOwner) : TargetCache := completed.1

/-- Read the complete original Steps receipt indexed by the identical retained target-list cache. -/
@[expose] def steps (completed : Quarter actual regular current reading sourceOwner) :
    Steps actual regular current reading sourceOwner completed.cache.val := completed.2

/-- Retaining completed quarter data preserves the whole identical original target cache. -/
theorem ofCompleted_cache (cache : TargetCache)
    (steps : Steps actual regular current reading sourceOwner cache.val) :
    (ofCompleted cache steps).cache = cache := rfl

/-- Retaining completed quarter data preserves the complete original spatial Steps receipt and its cache indices. -/
theorem ofCompleted_steps (cache : TargetCache)
    (steps : Steps actual regular current reading sourceOwner cache.val) :
    (ofCompleted cache steps).steps = steps := rfl

/-- Build a completed original quarter on an unchanged supplied continuation Owner, caching targets internally.

The owner can be the preceding quarter's actual finishOwner after exact
spatial endpoint transport. The original target cache is constructed once and
passed directly to the existing Steps builder; no Source attachment or source
root-channel query is performed. The original Reading remains a separate
retained geometric cache rather than identifying it with the supplied owner.
-/
@[expose] def build (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) (reading : ReadingAt actual current)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) :
    Quarter actual regular current reading sourceOwner :=
  let cache := TargetCache.build
  let payments : WidthPayments current cache.val := by
    rewrite [initial]
    exact cache.widthPayments
  let steps := Steps.build actual regular current reading sourceOwner cache.val payments
  ofCompleted cache steps

/-- Building an original quarter on a retained source Owner preserves the whole identical completed target cache. -/
theorem build_cache (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) (reading : ReadingAt actual current)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) :
    (build actual regular current initial reading sourceOwner).cache = TargetCache.build := by
  unfold build
  exact ofCompleted_cache _ _

end Quarter

/-- Construct a completed actual spatial quarter from one existing Source attachment, caching dyadic targets once.

The original quarter preparation and initial Source remain supplied inputs.
The original dyadic factory is computed once; its exact result is retained and
passed directly to the Steps builder. Every later covered block consumes the
preceding actual finishOwner, with no additional Source attachment. No full
quarter execution or endpoint-channel equivalence is asserted by this factory.
-/
@[expose] def fromInitial (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) (reading : ReadingAt actual current)
    (prepared : Gaussian.Division.Prepared reading.lift.value) (source : Source reading prepared) :
    Quarter actual regular current reading source.attached.owner :=
  Quarter.build actual regular current initial reading source.attached.owner

/-- The automatic quarter factory retains the identical original target cache without recomputing it per step. -/
theorem fromInitial_cache (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (current : Endpoint)
    (initial : current = UniformPrimitiveMesh.firstEndpoint) (reading : ReadingAt actual current)
    (prepared : Gaussian.Division.Prepared reading.lift.value) (source : Source reading prepared) :
    (fromInitial actual regular current initial reading prepared source).cache = TargetCache.build := by
  unfold fromInitial
  exact Quarter.build_cache _ _ _ _ _ _

/-- Construct the completed spatial quarter on its original certified initial endpoint and existing Source attachment.

The exact initial endpoint identity is reflexive. The original target cache is
computed and retained internally by the existing automatic quarter factory.
No raw endpoint-list identity or additional geometric comparison is required.
-/
@[expose] def quarter (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (reading : ReadingAt actual UniformPrimitiveMesh.firstEndpoint)
    (prepared : Gaussian.Division.Prepared reading.lift.value) (source : Source reading prepared) :
    Quarter actual regular UniformPrimitiveMesh.firstEndpoint reading source.attached.owner :=
  fromInitial actual regular UniformPrimitiveMesh.firstEndpoint rfl reading prepared source

/-- The original initial-endpoint quarter factory retains its whole completed original target cache. -/
theorem quarter_cache (actual : Transport.Quarter site parameter 2 unitQuarter positive)
    (regular : parameter ≠ criticalValue site) (reading : ReadingAt actual UniformPrimitiveMesh.firstEndpoint)
    (prepared : Gaussian.Division.Prepared reading.lift.value) (source : Source reading prepared) :
    (quarter actual regular reading prepared source).cache = TargetCache.build :=
  fromInitial_cache actual regular UniformPrimitiveMesh.firstEndpoint rfl reading prepared source

/-- The original retained finite dyadic target spine has exactly one hundred twenty-eight entries. -/
theorem dyadic_target_count :
    (dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint).length = 128 :=
  (Subdivision.dyadicTargets_length _ _ _).trans (by decide +kernel)

/-- The original finalTarget operation returns the same retained certified unit endpoint after this quarter. -/
theorem dyadic_finish :
    finalTarget UniformPrimitiveMesh.firstEndpoint
      (dyadicTargets 7 UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint) =
      UniformPrimitiveMesh.lastEndpoint :=
  Subdivision.dyadicTargets_finalTarget _ _ _

/-- The retained original unit-quarter target spine contains exactly one hundred twenty-eight entries. -/
theorem quarter_target_count : quarterTargets.length = 128 := by
  rewrite [quarterTargets_eq]
  exact dyadic_target_count

/-- The retained original unit-quarter target spine ends at the original certified unit endpoint. -/
theorem quarter_finish : finalTarget UniformPrimitiveMesh.firstEndpoint quarterTargets =
    UniformPrimitiveMesh.lastEndpoint := by
  rewrite [quarterTargets_eq]
  exact dyadic_finish

/-- A retained original initial endpoint and the unchanged quarter target spine finish at the original unit endpoint. -/
theorem quarter_finish_from {current : Endpoint} (initial : current = UniformPrimitiveMesh.firstEndpoint) :
    finalTarget current quarterTargets = UniformPrimitiveMesh.lastEndpoint := by
  rewrite [initial]
  exact quarter_finish

/-- An exact retained original quarter target list has one hundred twenty-eight entries. -/
theorem retained_target_count {targets : List Endpoint} (retained : targets = quarterTargets) :
    targets.length = 128 := by
  rewrite [retained]
  exact quarter_target_count

/-- An exact retained original quarter endpoint and target list finish at the original certified unit endpoint. -/
theorem retained_finish {current : Endpoint} {targets : List Endpoint}
    (initial : current = UniformPrimitiveMesh.firstEndpoint) (retained : targets = quarterTargets) :
    finalTarget current targets = UniformPrimitiveMesh.lastEndpoint := by
  rewrite [retained]
  exact quarter_finish_from initial

end Steps

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
