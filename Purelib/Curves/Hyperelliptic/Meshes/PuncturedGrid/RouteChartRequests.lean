module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

/-! Prepare all chart changes of an actual route word before sampling its shared
primitive bank. The finite charge includes both occurrence-count factors. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {word : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)}

namespace RouteChartRequests

/-- An actual retained edge route supplies support for its original edge or reversal in the triangulation. -/
theorem route_supported {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count} (route :
  Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
    edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨ edge.reverse ∈
      Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces := by
  cases route with
  | forward location =>
    exact Or.inl (location.sourceEdge_project ▸ Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member
      (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        location))
  | backward location =>
    exact Or.inr (location.sourceEdge_project ▸ Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member
      (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        location))

-- Retain the original nominal RouteChartRequests.RouteChartRequests identity.

end RouteChartRequests

set_option genInjectivity false in
/-- Ordered chart-change requests indexed by their exact retained route spine.

The empty constructor retains the original empty word. Each nonempty constructor
keeps its original route comparison and the unchanged dependent request tail. -/
inductive RouteChartRequests (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (allowance : Fraction.Rational) :
    {word : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)} →
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word → Type 2 where
  /-- The empty original route word requires no chart changes. -/ | nil :
    RouteChartRequests differential domains
    allowance .nil
  /-- Retain the original head route's canonical chart comparison together with the exact tail requests. -/ | cons {edge
    : Topology.Polygon.Stokes.OrientedEdge vertices.count} {word : List (Topology.Polygon.Stokes.OrientedEdge
    vertices.count)}
      (first : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) (rest :
        Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word)
      (request : Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartRequest first
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute mesh edge
        (Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests.route_supported first)) differential domains allowance)
      (remaining : RouteChartRequests differential
        domains allowance rest) :
      RouteChartRequests differential domains
        allowance (.cons first rest)

-- Retain the original constructor certificate names for this nominal owner.

constructive_injectivity RouteChartRequests

namespace RouteChartRequests

variable {allowance : Fraction.Rational} {assigned : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh
  word}

-- Retain the original operation name on RouteChartRequests.RouteChartRequests.
/-- Prepare each original route's canonical chart comparison at the shared positive local allowance. -/
@[expose] def build (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
    {word : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)} → (assigned :
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word) →
      RouteChartRequests differential domains allowance assigned
  | _, .nil => .nil
  | _, .cons first rest => .cons first rest
    (Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts.ChartRequest.build first
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute mesh _
      (Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests.route_supported first)) differential domains allowance
      positive)
    (build differential domains
      allowance positive rest)

-- Retain the original operation name on RouteChartRequests.RouteChartRequests.
/-- The maximum sufficient chart-change stage over the original route word. -/
@[expose] def index : {word : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)} → {assigned :
  Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word} →
    RouteChartRequests differential domains allowance assigned →
      Nat
  | _, _, .nil => 0
  | _, _, .cons _ _ request rest => max request.index rest.index

-- Retain the original operation name on RouteChartRequests.RouteChartRequests.
/-- There is exactly one retained chart-change discrepancy per original word occurrence. -/
theorem errors_length (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3)
  (assigned : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word) :
    (assigned.values fun edge route => route.sourceEdge.increment values -
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh values edge).length =
      word.length := by
  induction assigned with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

-- Retain the original operation name on RouteChartRequests.RouteChartRequests.
/-- At a sufficient shared stage, the sum of actual chart-change squared errors is bounded by the original occurrence
count times its allowance. -/
theorem errors_bound (requests : RouteChartRequests differential
  domains allowance assigned)
    {stage : Nat} (later : requests.index ≤ stage) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (assigned.values fun edge route => route.sourceEdge.increment
      readings.values - Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values edge)
      ≤
      (word.length : Fraction.Rational) * allowance := by
  induction requests with
  | nil => change (0 : Fraction.Rational) ≤ 0 * allowance; rw [zero_mul]
  | cons first rest request remaining ih =>
    have head := request.accurate ((Data.Nat.Order.le_max_left _ _).trans later) readings
    rw [Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.orderedRoute_value] at head
    rw [Gaussian.Norm.Basic.normSq_eq_canonical] at head
    have tail := ih ((Data.Nat.Order.le_max_right _ _).trans later)
    change Gaussian.Basic.Canonical.normSq (_ - _) + Gaussian.Norm.Sum.Basic.gaussianNormSqSum _ ≤ _
    exact (add_le_add head.le tail).trans_eq (by
      simp only [List.length_cons, Nat.cast_succ]
      ring1)

end RouteChartRequests

namespace RouteChartRequests

set_option genInjectivity false in
/-- A count-paid whole-word chart charge with its retained route preparations.

The original per-term allowance pays every signed occurrence. The cached common
stage equals the maximum of the retained requests and remains independent of the final primitive-polynomial index. -/
structure RouteChartRequest (assigned : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word)
  (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) where
  /-- The requested whole-word chart error is positive. -/ positive : 0 < target
  /-- The retained local chart-change allowance. -/ allowance : Fraction.Rational
  /-- The allowance is the original count-paid whole-word allocation. -/ allowance_eq : allowance =
    Rational.Budget.Aggregate.perTerm target word.length
  /-- The actual retained route-by-route chart comparisons. -/ requests :
    RouteChartRequests differential domains allowance assigned
  /-- The cached common sufficient chart-change stage. -/ index : Nat
  /-- The stage is exactly the maximum of the original retained requests. -/ index_eq : index = requests.index

constructive_injectivity RouteChartRequest

end RouteChartRequests

namespace RouteChartRequests.RouteChartRequest

variable {assigned : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word} {target : Fraction.Rational}

/-- Allocate the original word target and cache each route comparison with one sufficient shared stage. -/
@[expose] def build (assigned : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word) (differential :
  Hyperelliptic.Differentials.Basic.Differential genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests.RouteChartRequest assigned differential domains target :=
  let allowance := Rational.Budget.Aggregate.perTerm target word.length
  let requests := RouteChartRequests.build differential domains
    allowance
    (Rational.Budget.Aggregate.perTerm_positive positive _) assigned
  ⟨positive, allowance, rfl, requests, requests.index, rfl⟩

/-- The full original count-weighted sum of actual chart errors is strictly below the requested target. -/
theorem charge_lt (request : Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests.RouteChartRequest assigned
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    let changes := assigned.values fun edge route => route.sourceEdge.increment readings.values -
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values edge
    (changes.length : Fraction.Rational) * Gaussian.Norm.Sum.Basic.gaussianNormSqSum changes < target := by
  dsimp only
  rw [errors_length]
  have bound := request.requests.errors_bound (request.index_eq ▸ later) readings
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le word.length))
  apply paid.trans_lt
  rw [request.allowance_eq]
  exact Rational.Budget.Aggregate.count_mul_perTerm_lt request.positive _

/-- The retained discrepancy sum equals the original assigned-route sum minus the canonical word valuation. -/
private theorem errors_sum (assigned : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine mesh word)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun edge route => route.sourceEdge.increment values -
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh values edge) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment values) -
        Topology.Surface.Sewing.SewingRetraction.wordValue
          (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh values) word := by
  induction assigned with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons first rest ih =>
    change (_ - _) + _ = (_ + _) - (_ + _)
    rw [ih]
    ring1

/-- The canonical original word valuation approximates its assigned-route readings within the retained whole-word
target. -/
theorem accurate (request : Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests.RouteChartRequest assigned
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values) word -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
        readings.values)) < target := by
  have bounded := (Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le _).trans_lt (request.charge_lt later readings)
  rw [Hyperelliptic.Meshes.PuncturedGrid.RouteChartRequests.RouteChartRequest.errors_sum] at bounded
  rw [show Topology.Surface.Sewing.SewingRetraction.wordValue
    (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values) word -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
        readings.values) =
    -(Data.Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
      readings.values) -
      Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation mesh readings.values) word) by ring1,
    Gaussian.Norm.Basic.normSq_neg]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bounded

end RouteChartRequests.RouteChartRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

end
