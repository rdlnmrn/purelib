module
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Order
import Purelib.Data.List.Append
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedEdgeFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# One requested bound for both original lifted walk occurrences

The request retains all paired face placements, every whole-edge accuracy
budget and the actual combined source list. One cached common index pays
the squared finite sum count. Later triangle banks consume these sources
without repeating geometry selection or root preparation.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation

open Purelib.Data.List

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Topology.Polygon.Stokes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}

namespace PairedWalk

/-- The corner-comparison request for the actual retained paired cell and edge kind. -/
abbrev EdgeRequest (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
  base.faces.regulars) (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {start finish : Gaussian.Basic.Canonical} {edge : Geometry.Grid.Walks.Edge base.bank.grid start finish} (paired :
      EdgeOccurrences mesh edge)
    (target : Normalization.InverseRootPolynomial.Coordinate) :=
  Hyperelliptic.Meshes.PuncturedGrid.Face.PairedEdgeRequests.PairedEdgeRequest (domains.get paired.cell.located.index)
    differential
    (Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.point
      base.faces.regulars[paired.cell.located.index.val].cell.box (FaceCorners.quad.edge
      paired.cell.geometry.side.kind).start)
    (Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.point
      base.faces.regulars[paired.cell.located.index.val].cell.box (FaceCorners.quad.edge
      paired.cell.geometry.side.kind).finish) target

set_option genInjectivity false in
/-- The dependent original edge-request spine of a retained paired walk.

Each head request retains its paired edge and the unchanged dependent tail.
The empty spine keeps the original endpoint. -/
inductive Requests (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
  base.faces.regulars) (differential : Hyperelliptic.Differentials.Basic.Differential genus) (target :
  Normalization.InverseRootPolynomial.Coordinate) :
    {start finish : Gaussian.Basic.Canonical} → {walk : Geometry.Grid.Walks.Walk base.bank.grid start finish} →
      Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk → Type
  /-- The empty request spine at the retained original point. -/ | nil (point : Gaussian.Basic.Canonical) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests domains differential
    target (.nil point)
  /-- Prepend the actual original head-edge request to its dependent tail. -/ | cons {start middle finish :
    Gaussian.Basic.Canonical} {edge : Geometry.Grid.Walks.Edge base.bank.grid start middle}
      {walk : Geometry.Grid.Walks.Walk base.bank.grid middle finish} {head :
        EdgeOccurrences mesh edge} {tail :
        Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk}
      (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.EdgeRequest domains differential
        head target) (remaining :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests domains
        differential target tail) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests domains differential
        target (.cons head tail)

constructive_injectivity Requests

namespace Requests

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {target :
  Normalization.InverseRootPolynomial.Coordinate}

/-- Prepare each original paired edge request using its retained geometry.

Every head consumes the same positive target and retained paired geometry;
recursive preparation keeps the exact original tail and endpoint indices. -/
@[expose] def build (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
  base.faces.regulars) (differential : Hyperelliptic.Differentials.Basic.Differential genus) (target :
  Normalization.InverseRootPolynomial.Coordinate)
    (positive : 0 < target) : ∀ {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk
      base.bank.grid start finish}
      (paired : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk),
        Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests domains differential target
        paired
  | _, _, _, .nil point => .nil point
  | _, _, _, .cons head tail => .cons (head.request domains differential target positive)
      (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests.build domains
        differential target positive tail)

/-- Take the maximum of all original edge-request stages.

The empty spine supplies zero. Each retained head stage is combined with
the unchanged recursive tail stage by the original natural maximum. -/
@[expose] def index : ∀ {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid start
  finish} {paired : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk},
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests domains differential target paired →
      Nat
  | _, _, _, _, .nil _ => 0
  | _, _, _, _, .cons head tail => max head.index tail.index

/-- Each original paired edge sum is below its retained allowance at any sufficiently late common stage. -/
theorem term_bound {sampleIndex : Nat} {numerics :
  Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential sampleIndex domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics mesh) :
    ∀ {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid start finish} (paired :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk)
      (requests : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests domains differential
        target paired), requests.index ≤ sampleIndex →
      ∀ element ∈ paired.sums readings.values, Data.Gaussian.Norm.Basic.normSq element < target
  | _, _, _, .nil _, .nil _, _, _, member => (List.not_mem_nil member).elim
  | _, _, _, .cons head tail, .cons request remaining, later, element, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · exact head.accurate readings readings request
          ((Data.Nat.Order.le_max_left _ _).trans later) ((Data.Nat.Order.le_max_left _ _).trans later)
      · exact Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests.term_bound
          readings tail remaining ((Data.Nat.Order.le_max_right _ _).trans later) element member

end Requests
end PairedWalk

set_option genInjectivity false in
/-- A paid cancellation request for an original paired walk.

Retain both ordered source lists, their exact edge count, each local request and the common sufficient stage. -/
structure PairedWalkRequest (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
  base.faces.regulars) (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk base.bank.grid start finish) (target :
      Normalization.InverseRootPolynomial.Coordinate) where
  /-- The original aggregate cancellation target is positive. -/ positive : 0 < target
  /-- The actual retained paired walk and its geometry. -/ paired :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk
  /-- The concatenated original source lists from both retained sheets. -/ sources : List
    (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
  /-- The cached source list equals the exact two original paired-walk projections. -/ sources_eq : sources =
    paired.sources 0 ++ paired.sources 1
  /-- The cached original paired edge count. -/ count : Nat
  /-- The cached count equals the retained paired walk's actual edge count. -/ count_eq : count = walk.edgeCount
  /-- The retained local allowance for one original paired edge. -/ perEdge :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The local allowance equals the original per-term allocation of the aggregate target. -/ perEdge_eq : perEdge =
    Rational.Budget.Aggregate.perTerm target count
  /-- The actual dependent requests for the retained original paired edges. -/ requests :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests domains differential perEdge paired
  /-- The cached common sufficient cancellation stage. -/ index : Nat
  /-- The cached stage equals the maximum of the original edge-request stages. -/ index_eq : index = requests.index

constructive_injectivity PairedWalkRequest

namespace PairedWalkRequest

variable {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid start finish} {target :
    Normalization.InverseRootPolynomial.Coordinate}

/-- A new accuracy may reuse the same paired geometry and source choices.
Only scalar/model budgets depend on the new differential and tolerance. -/
@[expose] def ofPaired (paired : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk)
  (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (target :
      Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := mesh) domains differential
      walk target :=
  let sources := paired.sources 0 ++ paired.sources 1
  let count := walk.edgeCount
  let perEdge := Rational.Budget.Aggregate.perTerm target count
  let requests := Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalk.Requests.build domains
    differential perEdge
    (Rational.Budget.Aggregate.perTerm_positive positive count) paired
  ⟨positive, paired, sources, rfl, count, rfl, perEdge, rfl, requests, requests.index, rfl⟩

/-- Build the original paired geometry once, then allocate and prepare its scalar cancellation requests. -/
@[expose] def build (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (walk : Geometry.Grid.Walks.Walk
      base.bank.grid start finish)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := mesh) domains differential
      walk target :=
  Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest.ofPaired
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.build mesh walk) domains differential target
    positive

/-- Literal lifted edge indices are preserved on both sheets; this is
stronger than equality of projected planar coordinates. -/
theorem sources_project (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh :=
  mesh) domains differential walk target) :
    request.sources.map (fun source => source.project mesh.triangulation.faces) =
      edges.indexedEdges vertices walk 0 ++ edges.indexedEdges vertices walk 1 := by
  rw [request.sources_eq, Data.List.Map.map_append, request.paired.sources_project, request.paired.sources_project]

/-- The retained source list has twice the original paired edge count. -/
theorem sources_length (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh :=
  mesh) domains differential walk target) : request.sources.length = 2 * request.count := by
  have lengths := congrArg List.length request.sources_project
  rw [Data.List.Map.length_map, Data.List.Append.length_append, edges.indexedEdges_length, edges.indexedEdges_length, ←
    request.count_eq] at lengths
  omega

/-- All original occurrences and all edge counts are paid. The result
uses the supplied shared triangle bank at any sufficiently late index. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation.PairedWalkRequest (mesh := mesh)
  domains differential walk target)
    {sampleIndex : Nat} {numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential
      sampleIndex domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings numerics mesh) (later :
      request.index ≤ sampleIndex) :
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (request.sources.map fun source =>
      source.increment readings.values)) < target := by
  rw [request.sources_eq, Data.List.Map.map_append, Data.Gaussian.Norm.Sum.Basic.gaussianSum_append,
    request.paired.sums_eq]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ request.positive
  intro element member
  have bound := (request.requests.term_bound readings request.paired (request.index_eq ▸ later) element member).le
  rw [request.perEdge_eq, request.count_eq, ← request.paired.sums_length readings.values] at bound
  exact bound

end PairedWalkRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkCancellation

end
