module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Rational.Squares
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Chord
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Topology.Mesh.TriangleSourceUniqueness
public import Purelib.Topology.Surface.Cut.ChordJumps
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Tactic.Ring

/-!
# Actual cut jumps compared with original triangle increments

Geometry retains the source triangle occurrence of every forward or reversed
cut edge. Later readings reuse that ownership and the sewn face bank. Finite
Cauchy--Schwarz pays the full path length, including repeated occurrences,
against the inherited face allowances. Projected closure does not set the
cut jump to zero, and no smallness of these computed allowances is assumed.
-/

public section

namespace Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

open Purelib.Algebra.FiniteSum.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Data
open Purelib.Data.Gaussian.Norm.Basic
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Topology.Chain
open Purelib.Topology.Mesh.TriangleSourceUniqueness
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Cut.Chord
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary.FaceBank
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts.FaceBank
open Purelib.Topology.Surface.Sewing.VertexSewing

namespace SewnPrimitiveFaces

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary (TriangleEdgeOwner)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary}

set_option genInjectivity false in
/-- A retained positive triangle occurrence, with an explicit traversal sign.

The retained boundary owner identifies the original triangle and its two corners; the Boolean only records traversal
reversal. -/
structure OrientedOwner (patch : Patch.CutPatch faces indices boundary) where
  /-- Positive edge occurrence in the retained cut triangulation. -/ edge : Stokes.OrientedEdge patch.count
  /-- Original triangle occurrence and corners owning the positive edge. -/ owner :
    SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge
  /-- Whether the path traverses the retained edge in reverse. -/ reversed : Bool

constructive_injectivity OrientedOwner

namespace OrientedOwner

/-- Read the retained triangle edge with its explicit traversal orientation. -/
@[expose] def cutEdge (route : OrientedOwner patch) : Stokes.OrientedEdge patch.count :=
  if route.reversed then route.edge.reverse else route.edge

/-- Read the original source face corners in the retained traversal order. -/
@[expose] def sourceEdge (route : OrientedOwner patch) : SewnPrimitiveContacts.SourceEdge faceCount
  :=
  let source := TriangleEdgeOwner.sourceEdge route.owner
  if route.reversed then ⟨source.source, source.last, source.first⟩ else source

/-- Original source corners project to the oriented retained cut edge. -/
theorem sourceEdge_project (route : OrientedOwner patch) :
    route.sourceEdge.project faces = OrientedEdge.map patch.vertexLabels route.cutEdge := by
  rcases route with ⟨edge, owner, reversed⟩
  cases reversed
  · exact TriangleEdgeOwner.sourceEdge_project owner
  · exact congrArg OrientedEdge.reverse (TriangleEdgeOwner.sourceEdge_project owner)

/-- Select a positive boundary owner for a supported edge or its reverse. -/
@[expose] def build (edge : Stokes.OrientedEdge patch.count) (supported : edge ∈ patch.boundary ∨ edge.reverse ∈
  patch.boundary) :
    OrientedOwner patch :=
  if forward : edge ∈ patch.boundary then ⟨edge, SewnPrimitiveBoundary.boundaryOwner patch edge forward, false⟩
  else ⟨edge.reverse, SewnPrimitiveBoundary.boundaryOwner patch edge.reverse (supported.resolve_left forward), true⟩

/-- The selected owner reads back the exact requested oriented edge. -/
theorem cutEdge_build (edge : Stokes.OrientedEdge patch.count) (supported : edge ∈ patch.boundary ∨ edge.reverse ∈
  patch.boundary) :
    (build edge supported).cutEdge = edge := by
  unfold build
  split
  · rfl
  · exact edge.reverse_reverse

/-- A forward boundary occurrence selects a positive original source edge. -/
theorem build_positive (edge : Stokes.OrientedEdge patch.count)
    (supported : edge ∈ patch.boundary ∨ edge.reverse ∈ patch.boundary) (forward : edge ∈ patch.boundary) :
    SourceEdge.Positive (build edge supported).sourceEdge faces := by
  rw [build, dif_pos forward]
  exact TriangleEdgeOwner.sourceEdge_positive (SewnPrimitiveBoundary.boundaryOwner patch edge forward)

end OrientedOwner

set_option genInjectivity false in
/-- Geometry is selected before primitive accuracy.

One owner is retained for each ordered edge occurrence, and its cached source edge is linked to that same owner by an
exact readback equation. -/
structure PathSources (patch : Patch.CutPatch faces indices boundary) (edges : List (Stokes.OrientedEdge patch.count))
  where
  /-- One retained oriented owner per original path occurrence. -/ entries : List (OrientedOwner
    patch)
  /-- The owner readbacks reproduce the exact original edge list. -/ edges_eq : entries.map
    SewnPrimitiveFaces.OrientedOwner.cutEdge = edges
  /-- Cached list of original source-face increments. -/ sources : List (SewnPrimitiveContacts.SourceEdge faceCount)
  /-- The cached sources are exactly the retained owners' source readbacks. -/ sources_eq : sources = entries.map
    SewnPrimitiveFaces.OrientedOwner.sourceEdge

constructive_injectivity PathSources

namespace PathSources

/-- Select one retained oriented owner for each supported path occurrence.

Support supplies a boundary occurrence of each edge or its reverse. The recursion keeps the supplied list order and the
exact owner chosen by `OrientedOwner.build`. -/
@[expose] def owners : (edges : List (Stokes.OrientedEdge patch.count)) → CutPath.Supported patch.boundary edges → List
  (OrientedOwner patch)
  | [], _ => []
  | edge :: edges, supported => SewnPrimitiveFaces.OrientedOwner.build edge (supported edge List.mem_cons_self) ::
      owners edges (fun next member =>
        supported next (List.mem_cons_of_mem _ member))

/-- The selected oriented owners read back the original edge list.

The readback keeps repeated occurrences and traversal signs; each list entry is reduced using its retained owner
certificate. -/
theorem owners_edges : ∀ (edges : List (Stokes.OrientedEdge patch.count)) (supported : CutPath.Supported patch.boundary
  edges),
    (owners edges supported).map SewnPrimitiveFaces.OrientedOwner.cutEdge = edges
  | [], _ => rfl
  | edge :: edges, supported => congrArg₂ List.cons (SewnPrimitiveFaces.OrientedOwner.cutEdge_build edge _)
      (owners_edges edges (fun next
        member => supported next (List.mem_cons_of_mem _ member)))

/-- Cache supported path owners and their original source edges before numeric sampling.

The source list is computed from the retained owner list once, with equations recording both the requested edge word and
the source projection. -/
@[expose] def build (patch : Patch.CutPatch faces indices boundary) (edges : List (Stokes.OrientedEdge patch.count))
    (supported : CutPath.Supported patch.boundary edges) : PathSources patch edges :=
  let entries := owners edges supported
  ⟨entries, owners_edges edges supported, entries.map SewnPrimitiveFaces.OrientedOwner.sourceEdge, rfl⟩

/-- Owners selected for a forward boundary path retain positive source occurrences. -/
private theorem owners_positive : ∀ (edges : List (Stokes.OrientedEdge patch.count)) (supported : CutPath.Supported
  patch.boundary edges),
    (∀ edge ∈ edges, edge ∈ patch.boundary) → ∀ route ∈ owners edges supported, SourceEdge.Positive
      route.sourceEdge faces
  | [], _, _, _, member => (List.not_mem_nil member).elim
  | edge :: edges, supported, positive, route, member => by
      rcases Membership.mem_cons.mp member with same | remaining
      · cases same
        exact SewnPrimitiveFaces.OrientedOwner.build_positive edge _ (positive edge List.mem_cons_self)
      · exact owners_positive edges _
          (fun next member => positive next (List.mem_cons_of_mem _ member)) route remaining

/-- Forward boundary paths retain positive original face occurrences. This semantic property also admits independently
generated source banks. -/
@[expose] def Positive {edges : List (Stokes.OrientedEdge patch.count)} (sources : PathSources patch
  edges) : Prop :=
  ∀ source ∈ sources.sources, SourceEdge.Positive source faces

/-- Building sources for a forward boundary path produces a positive source bank. -/
theorem build_positive (patch : Patch.CutPatch faces indices boundary) (edges : List (Stokes.OrientedEdge patch.count))
    (supported : CutPath.Supported patch.boundary edges) (positive : ∀ edge ∈ edges, edge ∈ patch.boundary) :
    Positive (build patch edges supported) := by
  intro source member
  obtain ⟨route, member, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  exact owners_positive edges supported positive route member

variable {edges : List (Stokes.OrientedEdge patch.count)}

/-- The cached original source list projects to the actual oriented cut path. -/
theorem sources_project (sources : PathSources patch edges) :
    sources.sources.map (fun source => source.project faces) = edges.map (OrientedEdge.map patch.vertexLabels) := by
  have projected := congrArg (List.map (OrientedEdge.map patch.vertexLabels)) sources.edges_eq
  rw [Map.map_map] at projected
  rw [sources.sources_eq, Map.map_map]
  exact (Map.map_congr_left (fun route _ => route.sourceEdge_project)).trans projected

end PathSources

variable {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3} {values : PrimitiveSewing.PrimitiveValues
  patch.count}

set_option genInjectivity false in
/-- Numeric data for one already selected occurrence.

The increment and discrepancy are cached for that exact oriented owner, together with the squared-error allowance from
its face trace. -/
structure PathTerm (bank : SewnPrimitiveFaces.FaceBank patch localValues values) where
  /-- Original oriented owner sampled by this term. -/ route : OrientedOwner patch
  /-- Cached original local increment in the route's orientation. -/ increment : Gaussian.Basic.Canonical
  /-- The cached increment is the route's original source-edge reading. -/ increment_eq : increment =
    route.sourceEdge.increment localValues
  /-- Cached discrepancy between the actual sewn and original source increments. -/ error : Gaussian.Basic.Canonical
  /-- The discrepancy subtracts the cached source reading from the actual oriented sewn increment. -/ error_eq : error =
    (values route.cutEdge.finish - values route.cutEdge.start) - increment
  /-- Retained squared-error allowance inherited from the original face trace. -/ allowance : Fraction.Rational
  /-- The cached discrepancy's squared norm is at most the retained allowance. -/ error_bound :
    Data.Gaussian.Norm.Basic.normSq error ≤
    allowance

constructive_injectivity PathTerm

namespace PathTerm

/-- Sample a retained oriented owner from the existing face bank.

Traversal reversal negates both the local increment and discrepancy while retaining the same inherited allowance. -/
@[expose] def build (bank : SewnPrimitiveFaces.FaceBank patch localValues values) (route :
  OrientedOwner patch) : PathTerm bank :=
  let reading := EdgeReading.build bank route.owner
  { route := route
    increment := if route.reversed then -reading.localIncrement else reading.localIncrement
    increment_eq := by
      rw [EdgeReading.source_increment reading]
      rcases route with ⟨edge, owner, reversed⟩
      cases reversed
      · rfl
      · simp only [SewnPrimitiveFaces.OrientedOwner.sourceEdge, SourceEdge.increment,
          if_pos (Eq.refl true), -eq_self, -iff_self]
        ring1
    error := if route.reversed then -reading.error else reading.error
    error_eq := by
      rw [reading.error_eq]
      rcases route with ⟨edge, owner, reversed⟩
      cases reversed
      · rfl
      · change -((values edge.finish - values edge.start) - reading.localIncrement) =
          (values edge.start - values edge.finish) - -reading.localIncrement
        ring1
    allowance := reading.allowance
    error_bound := by
      split
      · rw [Gaussian.Norm.Basic.normSq_neg]; exact reading.error_bound
      · exact reading.error_bound }

/-- Squared norms of all path-term errors sum to at most their retained allowances. -/
private theorem norms_le (terms : List (PathTerm (patch := patch) (localValues := localValues)
  (values := values) bank)) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (terms.map
      Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.error) ≤ Squares.coordinateSum
      (terms.map Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.allowance) := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms ih =>
      have scalar := term.error_bound
      rw [Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
      exact add_le_add scalar ih

/-- The sum of path-term discrepancies is the sewn increment sum minus the source increment sum. -/
private theorem error_sum (terms : List (PathTerm (patch := patch) (localValues := localValues)
  (values := values) bank)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
      Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.error) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map (fun term => values term.route.cutEdge.finish - values
        term.route.cutEdge.start)) -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
          Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.increment) := by
  induction terms with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons term terms ih =>
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, term.error_eq, ih]
      ring1

end PathTerm

namespace PathSources

variable {edges : List (Stokes.OrientedEdge patch.count)}

set_option genInjectivity false in
/-- A numeric reading of an already retained path-source bank.

The sample keeps each occurrence's term, the original local-value sum, the actual sewn discrepancy and the
count-weighted allowance. -/
structure Sample (sources : PathSources patch edges) (bank : SewnPrimitiveFaces.FaceBank patch
  localValues values) where
  /-- Cached numeric terms for the retained route occurrences. -/ terms : List (PathTerm bank)
  /-- The terms retain exactly the original source bank's owner list. -/ routes_eq : terms.map
    Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.route = sources.entries
  /-- Cached Gaussian sum of original source increments. -/ value : Gaussian.Basic.Canonical
  /-- The cached value is the exact sum of the term increments. -/ value_eq : value =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
    Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.increment)
  /-- Cached Gaussian sum of actual occurrence discrepancies. -/ error : Gaussian.Basic.Canonical
  /-- The cached discrepancy is the exact sum of the term errors. -/ error_eq : error =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
    Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.error)
  /-- Cached finite-sum squared-error allowance. -/ bound : Fraction.Rational
  /-- The bound is the occurrence count times the sum of term allowances. -/ bound_eq : bound = (terms.length :
    Fraction.Rational) * Squares.coordinateSum (terms.map
    Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.allowance)

constructive_injectivity Sample

namespace Sample

variable {sources : PathSources patch edges} {bank
  : SewnPrimitiveFaces.FaceBank patch localValues values}

/-- Sample each retained route once and cache its value, discrepancy and finite-sum bound. -/
@[expose] def build (sources : PathSources patch edges) (bank : SewnPrimitiveFaces.FaceBank patch
  localValues values) : Sample sources bank :=
  let terms := sources.entries.map (SewnPrimitiveFaces.PathTerm.build bank)
  { terms := terms
    routes_eq := by
      dsimp only [terms]
      rw [Map.map_map]
      change sources.entries.map (fun route => route) = sources.entries
      induction sources.entries with
      | nil => rfl
      | cons route routes ih => exact congrArg (List.cons route) ih
    value := Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
      Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.increment)
    value_eq := rfl
    error := Data.Gaussian.Norm.Sum.Basic.gaussianSum (terms.map
      Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.error)
    error_eq := rfl
    bound := Aggregate.countCoordinate terms.length * Squares.coordinateSum (terms.map
      Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.allowance)
    bound_eq := by rw [Aggregate.countCoordinate_eq] }

/-- The cached sample value is the sum over its exact original source increments. -/
theorem value_eq_sources (sample : Sample sources bank) :
    sample.value = Data.Gaussian.Norm.Sum.Basic.gaussianSum (sources.sources.map (fun source => source.increment
      localValues)) := by
  rw [sample.value_eq, sources.sources_eq, ← sample.routes_eq, Map.map_map, Map.map_map]
  apply congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
  apply Map.map_congr_left
  intro term _
  exact term.increment_eq

/-- The cached discrepancy is the actual sewn path increment sum minus its original source reading. -/
theorem error_eq_difference (sample : Sample sources bank) :
    sample.error = Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => values edge.finish - values
      edge.start)) - sample.value := by
  have routeEdges := (congrArg (List.map SewnPrimitiveFaces.OrientedOwner.cutEdge) sample.routes_eq).trans
    sources.edges_eq
  have increments := congrArg (fun edges : List (Stokes.OrientedEdge patch.count) =>
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => values edge.finish - values edge.start)))
      routeEdges
  simp only [Map.map_map] at increments
  rw [sample.error_eq, SewnPrimitiveFaces.PathTerm.error_sum, sample.value_eq]
  exact congrArg (fun value => value - Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.terms.map
    SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.increment)) increments

/-- Finite Cauchy--Schwarz bounds the cached discrepancy by its retained path allowance. -/
theorem error_bound (sample : Sample sources bank) : Data.Gaussian.Norm.Basic.normSq sample.error ≤
  sample.bound := by
  rw [sample.error_eq, sample.bound_eq]
  have estimate := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le (sample.terms.map
    SewnPrimitivePaths.SewnPrimitiveFaces.PathTerm.error)
  rw [Map.length_map] at estimate
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (SewnPrimitiveFaces.PathTerm.norms_le sample.terms) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))

/-- An oriented path's sum of vertex increments is its endpoint difference. -/
theorem telescope {count : Nat} (values : PrimitiveSewing.PrimitiveValues count) :
    ∀ {edges : List (Stokes.OrientedEdge count)} {start finish : Fin count},
      PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish →
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => values edge.finish - values edge.start)) =
          values finish - values start
  | _, _, _, .nil _ => by change (0 : Gaussian.Basic.Canonical) = _ - _; ring1
  | _, _, _, .cons tail => by
      rw [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
        telescope values tail]
      ring1

/-- The cut endpoints need not agree even if their projected vertices do. -/
theorem jump_error (sample : Sample sources bank) {start finish : Fin patch.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish) :
    sample.error = (values finish - values start) - sample.value := by
  rw [sample.error_eq_difference, telescope values path]

/-- The actual cut-endpoint jump differs from the source reading by at most the retained path allowance. -/
theorem jump_bound (sample : Sample sources bank) {start finish : Fin patch.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish) :
    Data.Gaussian.Norm.Basic.normSq ((values finish - values start) - sample.value) ≤ sample.bound := by
  rw [← sample.jump_error path]
  exact sample.error_bound

/-- The final analytic comparison pays the sewn-path error separately from the error in the original source increments.
Neither is silently zeroed. -/
theorem compare_bound (sample : Sample sources bank) {start finish : Fin patch.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish)
    {target : Gaussian.Basic.Canonical} {tolerance : Fraction.Rational} (accurate : Data.Gaussian.Norm.Basic.normSq
      (sample.value -
      target) ≤ tolerance) :
    Data.Gaussian.Norm.Basic.normSq ((values finish - values start) - target) ≤ 2 * (sample.bound + tolerance) := by
  have equal : (values finish - values start) - target =
      ((values finish - values start) - sample.value) + (sample.value - target) := by ring1
  rw [equal]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (sample.jump_bound path) accurate) (by decide))

/-- A fixed bound on original source increments pays the magnitude of the actual sewn increment sum. Repetitions and
orientations are retained, and the inherited sewing allowance is not discarded. -/
theorem sum_magnitude_bound (sample : Sample sources bank) {magnitude : Fraction.Rational}
    (bounded : Data.Gaussian.Norm.Basic.normSq sample.value ≤ magnitude) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => values
      edge.finish - values
      edge.start))) ≤
      2 * (sample.bound + magnitude) := by
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two sample.error sample.value).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add sample.error_bound bounded) (by decide))
  rw [sample.error_eq_difference, sub_add_cancel] at estimate
  exact estimate

/-- Bound the actual endpoint jump by twice the source magnitude plus inherited path allowance. -/
theorem magnitude_bound (sample : Sample sources bank) {start finish : Fin patch.count}
    (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish)
    {magnitude : Fraction.Rational} (bounded : Data.Gaussian.Norm.Basic.normSq sample.value ≤ magnitude) :
    Data.Gaussian.Norm.Basic.normSq (values finish - values start) ≤ 2 * (sample.bound + magnitude) := by
  have estimate := sample.sum_magnitude_bound bounded
  rw [telescope values path] at estimate
  exact estimate

end Sample
end PathSources

/-- Numerical sampling never repeats the geometry-only ownership lookup. -/
@[expose] def CachedSample.pathSample {patch : SewingTree.SewnPatch faces} {localValues : Fin faceCount →
  PrimitiveSewing.PrimitiveValues 3}
    (sample : SewnPrimitiveSamples.CachedSample patch localValues) {edges : List (Stokes.OrientedEdge patch.cut.count)}
    (sources : PathSources patch.cut edges) : SewnPrimitiveFaces.PathSources.Sample sources
      sample.faces :=
  SewnPrimitiveFaces.PathSources.Sample.build sources sample.faces

end SewnPrimitiveFaces

namespace Chord

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord CutWordEntry)
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord

/-- Every edge in the original chord interval occurs positively in the boundary edge list. -/
theorem interval_positive {source target : Nat} {labels : Fin source → Fin target}
    {edges : List (Stokes.OrientedEdge source)} {word : BoundaryWord.CutBoundaryWord labels edges} {index : Fin
      word.alphabet.count}
    (chord : Cut.Chord.CutBoundaryWord word index) : ∀ edge ∈ chord.interval.map CutWordEntry.edge, edge ∈ edges := by
  intro edge member
  obtain ⟨entry, member, equal⟩ := Map.mem_map.mp member
  rw [← equal]
  exact (congrArg (fun entries => entry.edge ∈ entries) word.alphabet.edges_eq).mp
    (Map.mem_map_of_mem (chord.interval_mem member))

end Chord

namespace Route

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.Chord renaming CutBoundaryWord -> Chord
open Purelib.Topology.Surface.Cut.ChordJumps (Route)

open SewnPrimitiveFaces

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (Stokes.OrientedEdge vertexCount)}
  {patch : Patch.CutPatch faces indices boundary}
  {word : BoundaryWord.CutBoundaryWord patch.vertexLabels patch.boundary} {index : Fin word.alphabet.count}
  {chord : Cut.Chord.CutBoundaryWord word index}

/-- Construct once from the existing occurrence-preserving chord route; later primitive requests consume this retained
ownership bank. -/
@[expose] def sourceBank (route : ChordJumps.Route chord) : PathSources patch route.path.cutEdges :=
  PathSources.build patch route.path.cutEdges (by rw [route.path_eq]; exact chord.interval_supported)

/-- The chord route's retained source bank projects to its original surface-edge list. -/
theorem sourceBank_project (route : ChordJumps.Route chord) :
    (sourceBank route).sources.map (fun source => source.project faces) = route.path.surfaceEdges :=
  (sourceBank route).sources_project.trans route.path.projection_eq.symm

/-- The original chord interval produces only positive source occurrences. -/
theorem sourceBank_positive (route : ChordJumps.Route chord) :
  SewnPrimitivePaths.SewnPrimitiveFaces.PathSources.Positive (sourceBank route) :=
  PathSources.build_positive _ _ _ (by rw [route.path_eq]; exact SewnPrimitivePaths.Chord.interval_positive chord)

end Route

end Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

end
