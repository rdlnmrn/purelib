module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Points
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
public import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.Paths.OwnerTracePath.Join
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Actual source-Point readings sewn through the original signed root chain

The supplied source product and its independent Point-owned observations
remain unchanged. Each actual stationary join consumes both original
requests; its signed residual precedes the SAME child moving residual.
The empty inner word still constructs a real endpoint comparison. Exact
telescoping and the finite charge retain both outer request tolerances.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The actual mixed-request stationary charge, computed before either comparison or new observation. -/
@[expose] def junctionCharge (first last request : AccuracyRequest) : Rational :=
  16 * ((Primitive.vertexRequest first).tolerance + (Primitive.vertexRequest last).tolerance) +
    4 * request.tolerance

section Junction

variable {row : Row} {firstPoint lastPoint : Canonical}
variable {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint)}
variable {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint)}
variable {firstAccuracy lastAccuracy : AccuracyRequest}
variable (first : Primitive.Vertex (row.expression parameter) firstPoint firstOwner firstAccuracy)
variable (last : Primitive.Vertex (row.expression parameter) lastPoint lastOwner lastAccuracy)
variable (same : firstPoint = lastPoint)
variable (roots : NamedEquivalent (ownerName firstOwner) (ownerName lastOwner)) (request : AccuracyRequest)

/-- One genuine stationary OwnerJoin and its actual comparison of both unchanged primitive requests.

The exact physical coordinate transport and signed root comparison remain
indices. Both retained whole factories consume the original Vertices;
no request, denotation, Point or root owner is reconstructed.
-/
@[expose] def Junction :=
  (join : {value : OwnerJoin
      (castOwnerParameter (congrArg (Paths.polynomial parameter).eval same) firstOwner) lastOwner //
    value = OwnerJoin.acquireAt (polynomial := Paths.polynomial parameter) same roots}) ×
  {value : Observation.Comparison first.observation last.observation request.tolerance //
    value = Primitive.Vertex.compareRequestedAt (polynomial := Paths.polynomial parameter)
      (expression := row.expression parameter) first last same join.val request}

namespace Junction

/-- Acquire this exact signed join once and compare the two original requests once. -/
def build : Junction (parameter := parameter) (row := row) first last same roots request :=
  let join := OwnerJoin.acquireAt (polynomial := Paths.polynomial parameter) same roots
  let compared := Primitive.Vertex.compareRequestedAt (polynomial := Paths.polynomial parameter)
      (expression := row.expression parameter) first last same join request
  ⟨⟨join, rfl⟩, ⟨compared, rfl⟩⟩

variable {first last same roots request}
variable (retained : Junction (parameter := parameter) (row := row) first last same roots request)

/-- Read the actual original-owner stationary join with its coordinate transport unchanged. -/
@[expose] def join : OwnerJoin
    (castOwnerParameter (congrArg (Paths.polynomial parameter).eval same) firstOwner) lastOwner := retained.1.val

/-- Read the actual comparison on the two original observation caches. -/
@[expose] def compared : Observation.Comparison first.observation last.observation request.tolerance :=
  retained.2.val

/-- The stationary join retains the exact producer and both original owners. -/
theorem join_eq : retained.join =
    OwnerJoin.acquireAt (polynomial := Paths.polynomial parameter) same roots := retained.1.property

/-- The retained observation comparison consumes the SAME actual join and both unchanged requests. -/
theorem compared_eq : retained.compared =
    Primitive.Vertex.compareRequestedAt (polynomial := Paths.polynomial parameter)
      (expression := row.expression parameter) first last same retained.join request := retained.2.property

/-- Orient the actual stationary residual from the incoming observation to the next observation. -/
@[expose] def error : Canonical := -retained.compared.residual

/-- The stationary sign is next minus incoming, with both original readings retained. -/
theorem error_eq : retained.error = last.value - first.value := by
  have original := retained.compared.residual_eq
  change retained.compared.residual = first.value - last.value at original
  exact (congrArg (fun value : Canonical => -value) original).trans (by ring1)

/-- Both original request tolerances and this actual comparison request pay the signed stationary residual. -/
theorem error_le : Norm.Basic.normSq retained.error ≤ junctionCharge firstAccuracy lastAccuracy request := by
  have paid := (Primitive.Vertex.requested_error_lt_at (polynomial := Paths.polynomial parameter)
    (expression := row.expression parameter) first last request retained.compared).le
  have original := retained.compared.residual_eq
  change retained.compared.residual = first.value - last.value at original
  have normEq : Norm.Basic.normSq retained.error = Norm.Basic.normSq (first.value - last.value) :=
    (Norm.Basic.normSq_neg retained.compared.residual).trans (congrArg Norm.Basic.normSq original)
  exact normEq.trans_le paid

end Junction

end Junction

/-- Original occurrence-indexed Point-reading caches on the SAME complete supplied source preparations. -/
abbrev Readings (row : Row) {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets) :=
  DependentProduct parents (fun index => PreparedParent.Points.Compared row (prepared.entry index))

namespace Readings

/-- Observe each supplied source's two actual Point denotations once, preserving every original list occurrence. -/
def build (row : Row) {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets) :
    Readings row covered prepared :=
  DependentProduct.ofFn parents (fun index => PreparedParent.Points.build row (prepared.entry index))

/-- Read one SAME retained Point cache at its exact original bounded source occurrence. -/
@[expose] def entry {row : Row} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} {prepared : PreparedParents covered floor targets}
    (retained : Readings row covered prepared) (index : Fin parents.length) :
    PreparedParent.Points.Compared row (prepared.entry index) := DependentProduct.get parents retained index

/-- Materialization retains the original whole Point-observation factory at each unchanged occurrence. -/
theorem build_entry (row : Row) {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    (index : Fin parents.length) :
    (build row covered prepared).entry index = PreparedParent.Points.build row (prepared.entry index) :=
  DependentProduct.get_ofFn parents (fun index => PreparedParent.Points.build row (prepared.entry index)) index

end Readings

/-- Adding one child and its incoming join preserves the exact twice-plus-one residual count. -/
private theorem count_step {count size : Nat} (same : count = 2 * size + 1) :
    count + 2 = 2 * (size + 1) + 1 := by omega0

/-- One incoming jump and one child residual telescope with the literal remaining scalar increment. -/
private theorem sew_scalar (first incoming outgoing last sample following : Canonical) :
    (incoming - first) + ((outgoing - incoming - sample) + (last - outgoing - following)) =
      last - first - (sample + following) := by ring1

/-- The original empty geometric chain proves its two coordinate roles equal, without constructing a new owner. -/
theorem empty_point {first last : LiftedPoint 2}
    (geometry : Nonempty (DirectPathChain (curve := Fibre.frameCurve frame) (differential := basis) []
      (start := first) (finish := last))) : first.coordinate = last.coordinate := by
  obtain ⟨geometry⟩ := geometry
  cases geometry
  rfl

/-- The actual nonempty chain places the incoming role at this original source's starting coordinate. -/
theorem head_point {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {first last : LiftedPoint 2}
    (geometry : Nonempty (DirectPathChain (parent :: parents) (start := first) (finish := last))) :
    first.coordinate = (PreparedParent.startPoint parent).coordinate :=
  (DirectPathChain.head_coordinate geometry).symm.trans parent.edge.point_zero

/-- The exact finite total of actual stationary request charges and actual child moving-error charges.

This depends only on the original child count, both outer request owners,
the selected new source accuracy and the independent comparison request.
It is computable before any new coefficient observation is selected.
-/
@[expose] def charge (targets : CellEndpoints.Targets original stage) (request : AccuracyRequest) :
    Nat → AccuracyRequest → AccuracyRequest → Rational
  | 0, first, last => junctionCharge first last request
  | remaining + 1, first, last =>
      junctionCharge first (PreparedParents.Trace.localAccuracy targets) request + 12 * targets.endpoint +
        charge targets request remaining (PreparedParents.Trace.localAccuracy targets) last

/-- The actual ordered join caches on the SAME source product, Point readings, geometric chain and signed root chain.

Only proof-valued endpoint identities are extracted from geometric
Nonempty. Every runtime source, Point reading, root equivalence and
stationary comparison is the actual retained input or newly executed join.
The recursion passes the literal source and reading tails unchanged.
-/
@[expose] def Cache (row : Row) (request : AccuracyRequest) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) → {firstPoint lastPoint : LiftedPoint 2} →
    (geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))) →
    {firstAccuracy lastAccuracy : AccuracyRequest} →
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)} →
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)} →
    (first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy) →
    (last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy) →
    (roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)) → Type 1
  | [], .nil, _, _, _, _, geometry, _, _, _, _, first, last, roots =>
      Junction (parameter := parameter) (row := row) first last (empty_point geometry) roots.emptyEquivalent request
  | _ :: _, .cons _ _ covered, prepared, readings, _, _, geometry, _, _, _, _, first, last, roots =>
      Junction (parameter := parameter) (row := row) first readings.1.first (head_point geometry)
        (roots.firstEquivalent.trans readings.1.firstRoots) request ×
      Cache row request covered prepared.2 readings.2 (DirectPathChain.tail_chain geometry) readings.1.last last
        (roots.remaining.changeStart readings.1.lastRoots.symm)
termination_by structural _ covered _ _ _ _ _ _ _ _ _ _ _ _ => covered

namespace Cache

/-- Construct each actual signed stationary comparison once, consuming all SAME child and root-chain tails. -/
def build (row : Row) (request : AccuracyRequest) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) → {firstPoint lastPoint : LiftedPoint 2} →
    (geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))) →
    {firstAccuracy lastAccuracy : AccuracyRequest} →
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)} →
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)} →
    (first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy) →
    (last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy) →
    (roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)) →
      Cache row request covered prepared readings geometry first last roots
  | [], .nil, _, _, _, _, geometry, _, _, _, _, first, last, roots =>
      Junction.build (parameter := parameter) (row := row) first last (empty_point geometry)
        roots.emptyEquivalent request
  | _ :: _, .cons _ _ covered, prepared, readings, _, _, geometry, _, _, _, _, first, last, roots =>
      let front := Junction.build (parameter := parameter) (row := row) first readings.1.first (head_point geometry)
        (roots.firstEquivalent.trans readings.1.firstRoots) request
      let following := build row request covered prepared.2 readings.2 (DirectPathChain.tail_chain geometry)
        readings.1.last last (roots.remaining.changeStart readings.1.lastRoots.symm)
      ⟨front, following⟩
termination_by structural _ covered _ _ _ _ _ _ _ _ _ _ _ _ => covered

/-- Read all SAME cached source integrals in original child order, including stationary and repeated occurrences. -/
@[expose] def integrals (row : Row) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    Readings row covered prepared → List Canonical
  | [], .nil, _, _ => []
  | _ :: _, .cons _ _ covered, prepared, readings =>
      readings.1.sample :: integrals row covered prepared.2 readings.2
termination_by structural _ covered _ _ => covered

/-- Read the SAME supplied source model integrals without observing their Point denotations.

The ordered source product determines these integrals before new Point
requests or stationary comparisons. Repeated and stationary source
occurrences retain their own original model and primitive caches.
-/
@[expose] def sourceIntegrals (row : Row) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → PreparedParents covered floor targets → List Canonical
  | [], .nil, _ => []
  | _ :: _, .cons _ _ covered, prepared =>
      (row.cell prepared.1.preparation.models).integralSample :: sourceIntegrals row covered prepared.2
termination_by structural _ covered _ => covered

/-- Each retained Point cache reads exactly the integral of its SAME supplied source model in original order. -/
theorem integrals_eq (row : Row) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) →
      integrals row covered prepared readings = sourceIntegrals row covered prepared
  | [], .nil, _, _ => rfl
  | _ :: _, .cons _ _ covered, prepared, readings =>
      congrArg₂ List.cons readings.1.sample_eq (integrals_eq row covered prepared.2 readings.2)
termination_by structural _ covered _ _ => covered

/-- Read actual signed junction residuals interleaved with the SAME actual child moving residuals. -/
@[expose] def errors (row : Row) (request : AccuracyRequest) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) → {firstPoint lastPoint : LiftedPoint 2} →
    (geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))) →
    {firstAccuracy lastAccuracy : AccuracyRequest} →
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)} →
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)} →
    (first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy) →
    (last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy) →
    (roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)) →
    Cache row request covered prepared readings geometry first last roots → List Canonical
  | [], .nil, _, _, _, _, _, _, _, _, _, _, _, _roots, retained => [retained.error]
  | _ :: _, .cons _ _ covered, prepared, readings, _, _, geometry, _, _, _, _, _, last, roots, retained =>
      retained.1.error :: readings.1.error ::
        errors row request covered prepared.2 readings.2 (DirectPathChain.tail_chain geometry)
          readings.1.last last (roots.remaining.changeStart readings.1.lastRoots.symm) retained.2
termination_by structural _ covered _ _ _ _ _ _ _ _ _ _ _ _ _ => covered

/-- Read only the actual signed opening, adjacent and final comparison residuals, in their original order. -/
@[expose] def junctionErrors (row : Row) (request : AccuracyRequest) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) → {firstPoint lastPoint : LiftedPoint 2} →
    (geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))) →
    {firstAccuracy lastAccuracy : AccuracyRequest} →
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)} →
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)} →
    (first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy) →
    (last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy) →
    (roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)) →
    Cache row request covered prepared readings geometry first last roots → List Canonical
  | [], .nil, _, _, _, _, _, _, _, _, _, _, _, _roots, retained => [retained.error]
  | _ :: _, .cons _ _ covered, prepared, readings, _, _, geometry, _, _, _, _, _, last, roots, retained =>
      retained.1.error ::
        junctionErrors row request covered prepared.2 readings.2 (DirectPathChain.tail_chain geometry)
          readings.1.last last (roots.remaining.changeStart readings.1.lastRoots.symm) retained.2
termination_by structural _ covered _ _ _ _ _ _ _ _ _ _ _ _ _ => covered

/-- Exactly one actual requested join follows every child, together with the opening join, even for no children. -/
theorem junctionErrors_length (row : Row) (request : AccuracyRequest) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) → {firstPoint lastPoint : LiftedPoint 2} →
    (geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))) →
    {firstAccuracy lastAccuracy : AccuracyRequest} →
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)} →
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)} →
    (first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy) →
    (last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy) →
    (roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)) →
    (retained : Cache row request covered prepared readings geometry first last roots) →
      (junctionErrors row request covered prepared readings geometry first last roots retained).length =
        parents.length + 1
  | [], .nil, _, _, _, _, _, _, _, _, _, _, _, _roots, _ => rfl
  | _ :: _, .cons _ _ covered, prepared, readings, _, _, geometry, _, _, _, _, _, last, roots, retained =>
      congrArg Nat.succ (junctionErrors_length row request covered prepared.2 readings.2
        (DirectPathChain.tail_chain geometry) readings.1.last last
        (roots.remaining.changeStart readings.1.lastRoots.symm) retained.2)
termination_by structural _ covered _ _ _ _ _ _ _ _ _ _ _ _ _ => covered

/-- The error word retains one child residual and every opening, adjacent and final junction residual. -/
theorem errors_length (row : Row) (request : AccuracyRequest) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) → {firstPoint lastPoint : LiftedPoint 2} →
    (geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))) →
    {firstAccuracy lastAccuracy : AccuracyRequest} →
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)} →
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)} →
    (first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy) →
    (last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy) →
    (roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)) →
    (retained : Cache row request covered prepared readings geometry first last roots) →
      (errors row request covered prepared readings geometry first last roots retained).length =
        2 * parents.length + 1
  | [], .nil, _, _, _, _, _, _, _, _, _, _, _, _roots, _ => rfl
  | _ :: parents, .cons _ _ covered, prepared, readings, _, _, geometry, _, _, _, _, _, last, roots, retained => by
      have following := errors_length row request covered prepared.2 readings.2
        (DirectPathChain.tail_chain geometry) readings.1.last last
        (roots.remaining.changeStart readings.1.lastRoots.symm) retained.2
      change (errors row request covered prepared.2 readings.2 (DirectPathChain.tail_chain geometry)
        readings.1.last last (roots.remaining.changeStart readings.1.lastRoots.symm) retained.2).length + 2 =
          2 * (parents.length + 1) + 1
      exact count_step following
termination_by structural _ covered _ _ _ _ _ _ _ _ _ _ _ _ _ => covered

/-- The SAME signed residuals telescope exactly to the original outer increment minus all actual source integrals. -/
theorem sum_errors (row : Row) (request : AccuracyRequest) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) → {firstPoint lastPoint : LiftedPoint 2} →
    (geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))) →
    {firstAccuracy lastAccuracy : AccuracyRequest} →
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)} →
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)} →
    (first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy) →
    (last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy) →
    (roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)) →
    (retained : Cache row request covered prepared readings geometry first last roots) →
      Norm.Sum.Basic.gaussianSum (errors row request covered prepared readings geometry first last roots retained) =
        last.value - first.value - Norm.Sum.Basic.gaussianSum (integrals row covered prepared readings)
  | [], .nil, _, _, _, _, _, _, _, _, _, _, _, _roots, retained => by
      change retained.error + 0 = _
      have original := retained.error_eq
      rewrite [original]
      change _ = _ - _ - 0
      ring1
  | _ :: _, .cons _ _ covered, prepared, readings, _, _, geometry, _, _, _, _, first, last, roots, retained => by
      have following := sum_errors row request covered prepared.2 readings.2
        (DirectPathChain.tail_chain geometry) readings.1.last last
        (roots.remaining.changeStart readings.1.lastRoots.symm) retained.2
      change retained.1.error + (readings.1.error + Norm.Sum.Basic.gaussianSum
        (errors row request covered prepared.2 readings.2 (DirectPathChain.tail_chain geometry)
          readings.1.last last (roots.remaining.changeStart readings.1.lastRoots.symm) retained.2)) =
        last.value - first.value - (readings.1.sample +
          Norm.Sum.Basic.gaussianSum (integrals row covered prepared.2 readings.2))
      have opening := retained.1.error_eq
      have moving := readings.1.error_eq
      exact (congrArg₂ (fun first last : Canonical => first + last) opening
        (congrArg₂ (fun first last : Canonical => first + last) moving following)).trans
        (sew_scalar first.value readings.1.first.value readings.1.last.value last.value readings.1.sample
          (Norm.Sum.Basic.gaussianSum (integrals row covered prepared.2 readings.2)))
termination_by structural _ covered _ _ _ _ _ _ _ _ _ _ _ _ _ => covered

/-- The norm sum is paid by the pre-observation charge at the exact retained child count and both endpoint requests. -/
theorem normSum_le (row : Row) (request : AccuracyRequest) :
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    (readings : Readings row covered prepared) → {firstPoint lastPoint : LiftedPoint 2} →
    (geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))) →
    {firstAccuracy lastAccuracy : AccuracyRequest} →
    {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)} →
    {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)} →
    (first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy) →
    (last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy) →
    (roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)) →
    (retained : Cache row request covered prepared readings geometry first last roots) →
      Norm.Sum.Basic.gaussianNormSqSum
        (errors row request covered prepared readings geometry first last roots retained) ≤
          charge targets request parents.length firstAccuracy lastAccuracy
  | [], .nil, _, _, _, _, _, firstAccuracy, lastAccuracy, _, _, _, _, _roots, retained => by
      have paid := (Norm.Basic.normSq_eq_canonical retained.error).symm.trans_le retained.error_le
      change Canonical.normSq retained.error + 0 ≤ junctionCharge firstAccuracy lastAccuracy request
      exact (Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct paid
        (Data.Rat.Fraction.Order.Basic.le_refl 0)).trans_eq (by ring1)
  | _ :: _, .cons _ _ covered, prepared, readings, _, _, geometry, _, _, _, _, _, last, roots, retained => by
      have following := normSum_le row request covered prepared.2 readings.2
        (DirectPathChain.tail_chain geometry) readings.1.last last
        (roots.remaining.changeStart readings.1.lastRoots.symm) retained.2
      have firstBound := (Norm.Basic.normSq_eq_canonical retained.1.error).symm.trans_le retained.1.error_le
      have movingBound := (Norm.Basic.normSq_eq_canonical readings.1.error).symm.trans_le readings.1.error_le
      have paid := Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct firstBound
        (Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct movingBound following)
      change Canonical.normSq retained.1.error + (Canonical.normSq readings.1.error + _) ≤ _
      exact paid.trans_eq (by change _ = (_ + _) + _; ring1)
termination_by structural _ covered _ _ _ _ _ _ _ _ _ _ _ _ _ => covered

variable {row : Row} {request : AccuracyRequest}
variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {covered : CoveredParents count parents} {prepared : PreparedParents covered floor targets}
variable {readings : Readings row covered prepared} {firstPoint lastPoint : LiftedPoint 2}
variable {geometry : Nonempty (DirectPathChain parents (start := firstPoint) (finish := lastPoint))}
variable {firstAccuracy lastAccuracy : AccuracyRequest}
variable {firstOwner : Owner ((Paths.polynomial parameter).eval firstPoint.coordinate)}
variable {lastOwner : Owner ((Paths.polynomial parameter).eval lastPoint.coordinate)}
variable {first : Primitive.Vertex (row.expression parameter) firstPoint.coordinate firstOwner firstAccuracy}
variable {last : Primitive.Vertex (row.expression parameter) lastPoint.coordinate lastOwner lastAccuracy}
variable {roots : RootChain parents (ownerName firstOwner) (ownerName lastOwner)}

/-- Cauchy's finite bound pays the actual old outer increment against the SAME refined source integrals.

The exact residual count is twice the actual child count plus one. The
charge keeps both old outer request tolerances and every new stationary
request. No normalization of unrelated primitive constants is asserted.
-/
theorem integral_error_le (retained : Cache row request covered prepared readings geometry first last roots) :
    Norm.Basic.normSq (last.value - first.value -
      Norm.Sum.Basic.gaussianSum (integrals row covered prepared readings)) ≤
        ((2 * parents.length + 1 : Nat) : Rational) *
          charge targets request parents.length firstAccuracy lastAccuracy := by
  let actual := errors row request covered prepared readings geometry first last roots retained
  have cauchy := (Norm.Basic.normSq_eq_canonical (Norm.Sum.Basic.gaussianSum actual)).trans_le
    (Norm.Sum.Basic.normSq_gaussianSum_le actual)
  have normEq : Norm.Basic.normSq (Norm.Sum.Basic.gaussianSum actual) =
      Norm.Basic.normSq (last.value - first.value -
        Norm.Sum.Basic.gaussianSum (integrals row covered prepared readings)) :=
    congrArg Norm.Basic.normSq (sum_errors row request covered prepared readings geometry first last roots retained)
  have paid := Data.Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (normSum_le row request covered prepared readings geometry first last roots retained)
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le actual.length))
  have bound := normEq.symm.trans_le (cauchy.trans paid)
  exact bound.trans_eq (congrArg (fun length : Nat =>
    (length : Rational) * charge targets request parents.length firstAccuracy lastAccuracy)
      (errors_length row request covered prepared readings geometry first last roots retained))

end Cache

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Points

end
