module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator
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

open Purelib.Topology.Surface
open Purelib.Approximation.Rational
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib
open Purelib.Topology.Polygon.Stokes
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}
  {domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Differentials.Basic.Differential genus}
  {word : List (OrientedEdge vertices.count)}

namespace RouteChartRequests

/-- An actual retained edge route supplies support for its original edge or reversal in the triangulation. -/
theorem route_supported {edge : OrientedEdge vertices.count} (route :
  MeshPathWalks.EdgeRoute mesh edge) :
    edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨ edge.reverse ∈
      Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces := by
  cases route with
  | forward location =>
    exact Or.inl (location.sourceEdge_project ▸ Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member
      (TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        location))
  | backward location =>
    exact Or.inr (location.sourceEdge_project ▸ Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member
      (TriangleSourceUniqueness.LiftedFaces.EdgeLocation.sourceEdge_positive
        location))

-- Retain the original nominal RouteChartRequests.RouteChartRequests identity.

end RouteChartRequests

set_option genInjectivity false in
/-- Ordered chart-change requests indexed by their exact retained route spine.

The empty constructor retains the original empty word. Each nonempty constructor
keeps its original route comparison and the unchanged dependent request tail. -/
inductive RouteChartRequests (differential : Differentials.Basic.Differential genus) (domains :
  Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (allowance : Fraction.Rational) :
    {word : List (OrientedEdge vertices.count)} →
      MeshPathWalks.RouteSpine mesh word →
      (polynomial : optParam (Option (Ordinary curve.polynomial)) none) → Type 2 where
  /-- The empty original route word requires no chart changes. -/ | nil
      {polynomial : Option (Ordinary curve.polynomial)} :
    RouteChartRequests differential domains
    allowance .nil polynomial
  /-- Retain the original head route's canonical chart comparison together with the exact tail requests. -/ | cons {edge
    : OrientedEdge vertices.count} {word : List (OrientedEdge
    vertices.count)}
      {polynomial : Option (Ordinary curve.polynomial)}
      (first : MeshPathWalks.EdgeRoute mesh edge) (rest :
        MeshPathWalks.RouteSpine mesh word)
      (request : RouteChartContacts.ChartRequest first
        (CanonicalEdgeValues.orderedRoute mesh edge
        (RouteChartRequests.route_supported first)) differential domains allowance polynomial)
      (remaining : RouteChartRequests differential
        domains allowance rest polynomial) :
      RouteChartRequests differential domains
        allowance (.cons first rest) polynomial

-- Retain the original constructor certificate names for this nominal owner.

constructive_injectivity RouteChartRequests

namespace RouteChartRequests

variable {allowance : Fraction.Rational} {assigned : MeshPathWalks.RouteSpine mesh
  word}

-- Retain the original operation name on RouteChartRequests.RouteChartRequests.
/-- Prepare each original route's canonical chart comparison at the shared positive local allowance. -/
@[expose] def build (differential : Differentials.Basic.Differential genus) (domains :
  Face.DomainBanks.FaceDomainBank frames base.faces.regulars)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
    {word : List (OrientedEdge vertices.count)} → (assigned :
      MeshPathWalks.RouteSpine mesh word) →
      RouteChartRequests differential domains allowance assigned
  | _, .nil => .nil
  | _, .cons first rest => .cons first rest
    (RouteChartContacts.ChartRequest.build first
      (CanonicalEdgeValues.orderedRoute mesh _
      (RouteChartRequests.route_supported first)) differential domains allowance
      positive)
    (build differential domains
      allowance positive rest)

-- Retain the original operation name on RouteChartRequests.RouteChartRequests.
/-- The maximum sufficient chart-change stage over the original route word. -/
@[expose] def index {polynomial : Option (Ordinary curve.polynomial)} :
    {word : List (OrientedEdge vertices.count)} → {assigned :
  MeshPathWalks.RouteSpine mesh word} →
    RouteChartRequests differential domains allowance assigned polynomial →
      Nat
  | _, _, .nil => 0
  | _, _, .cons _ _ request rest => max request.index rest.index

/-- Reallocate numerical budgets on the SAME ordered route/contact preparations.

Every actual route, source identity and prepared contact is forwarded.
Only the supplied positive allowance and polynomial budgets are selected;
no source classification, contact geometry or observation is repeated.
-/
def rebudget {previous : Fraction.Rational} {previousPolynomial : Option (Ordinary curve.polynomial)}
    (allowance : Fraction.Rational) (positive : 0 < allowance)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
    {word : List (OrientedEdge vertices.count)} → {assigned : MeshPathWalks.RouteSpine mesh word} →
      RouteChartRequests differential domains previous assigned previousPolynomial →
      RouteChartRequests differential domains allowance assigned polynomial
  | _, _, .nil => .nil
  | _, _, .cons first rest request remaining =>
      let head := request.rebudget allowance positive polynomial
      let tail := rebudget allowance positive polynomial remaining
      .cons first rest head tail

/-- The original ordered post-bank contact caches on the literal supplied primitive bank.

Exact chart agreements keep their trivial cache. Contact occurrences keep
the actual full-numerator common-model comparisons, with independent
source/face floors, anchors and offsets, in their original signed order.
-/
@[expose] def Comparisons {polynomial : Option (Ordinary curve.polynomial)}
    {word : List (OrientedEdge vertices.count)} {assigned : MeshPathWalks.RouteSpine mesh word}
    (requests : RouteChartRequests differential domains allowance assigned polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) : Type 2 :=
  match requests with
  | .nil => PUnit
  | .cons _ _ request remaining => request.Comparison shared × remaining.Comparisons shared

/-- Execute each retained contact comparison once on the GIVEN primitive bank, preserving its exact request tail. -/
def compare {polynomial : Option (Ordinary curve.polynomial)}
    {word : List (OrientedEdge vertices.count)} {assigned : MeshPathWalks.RouteSpine mesh word}
    (requests : RouteChartRequests differential domains allowance assigned polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)) :
    requests.Comparisons shared :=
  match requests with
  | .nil => ⟨⟩
  | .cons _ _ request remaining =>
      let head := request.compare shared
      let tail := remaining.compare shared
      ⟨head, tail⟩

/-- Actual cached comparisons pay every retained chart discrepancy at a sufficient common stage.

The finite sum keeps one term per original route occurrence, including
repeated and reversed occurrences. The numerator comes from the literal
supplied polynomial specification and is independent of sheet orientation.
-/
theorem comparison_errors_bound {polynomial : Option (Ordinary curve.polynomial)}
    (requests : RouteChartRequests differential domains allowance assigned polynomial)
    {stage : Nat} (later : requests.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (compared : requests.Comparisons shared)
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (assigned.values fun edge route => route.sourceEdge.increment
      readings.values - CanonicalEdgeValues.edgeValuation mesh readings.values edge) ≤
      (word.length : Fraction.Rational) * allowance := by
  induction requests with
  | nil =>
      change (0 : Fraction.Rational) ≤ 0 * allowance
      rewrite [Fraction.Field.zero_mul_direct allowance]
      exact Fraction.Order.Basic.le_refl 0
  | cons first rest request remaining ih =>
      have head := request.comparison_accurate ((Nat.Order.le_max_left _ _).trans later) compared.1 readings
      rw [CanonicalEdgeValues.orderedRoute_value, Gaussian.Norm.Basic.normSq_eq_canonical] at head
      have tail := ih ((Nat.Order.le_max_right _ _).trans later) compared.2 readings
      change Gaussian.Basic.Canonical.normSq (_ - _) + Gaussian.Norm.Sum.Basic.gaussianNormSqSum _ ≤ _
      exact (Fraction.Order.Arithmetic.add_le_add_direct head.le tail).trans_eq (by
        simp only [List.length_cons, Nat.cast_succ]
        ring1)

-- Retain the original operation name on RouteChartRequests.RouteChartRequests.
/-- There is exactly one retained chart-change discrepancy per original word occurrence. -/
theorem errors_length (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3)
  (assigned : MeshPathWalks.RouteSpine mesh word) :
    (assigned.values fun edge route => route.sourceEdge.increment values -
      CanonicalEdgeValues.edgeValuation mesh values edge).length =
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
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (assigned.values fun edge route => route.sourceEdge.increment
      readings.values - CanonicalEdgeValues.edgeValuation mesh readings.values edge)
      ≤
      (word.length : Fraction.Rational) * allowance := by
  exact requests.comparison_errors_bound (polynomial := none) later (requests.compare shared) readings

end RouteChartRequests

namespace RouteChartRequests

set_option genInjectivity false in
/-- A count-paid whole-word chart charge with its retained route preparations.

The original per-term allowance pays every signed occurrence. The cached common
stage equals the maximum of the retained requests and remains independent of the final primitive-polynomial index. -/
structure RouteChartRequest (assigned : MeshPathWalks.RouteSpine mesh word)
  (differential : Differentials.Basic.Differential genus)
    (domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) (polynomial : Option (Ordinary curve.polynomial) := none) where
  /-- The requested whole-word chart error is positive. -/ positive : 0 < target
  /-- The retained local chart-change allowance. -/ allowance : Fraction.Rational
  /-- The allowance is the original count-paid whole-word allocation. -/ allowance_eq : allowance =
    Budget.Aggregate.perTerm target word.length
  /-- The actual retained route-by-route chart comparisons. -/ requests :
    RouteChartRequests differential domains allowance assigned polynomial
  /-- The cached common sufficient chart-change stage. -/ index : Nat
  /-- The stage is exactly the maximum of the original retained requests. -/ index_eq : index = requests.index

constructive_injectivity RouteChartRequest

end RouteChartRequests

namespace RouteChartRequests.RouteChartRequest

variable {assigned : MeshPathWalks.RouteSpine mesh word} {target : Fraction.Rational}

/-- Allocate the original word target and cache each route comparison with one sufficient shared stage. -/
@[expose] def build (assigned : MeshPathWalks.RouteSpine mesh word) (differential :
  Differentials.Basic.Differential genus)
    (domains : Face.DomainBanks.FaceDomainBank frames base.faces.regulars) (target :
      Fraction.Rational) (positive : 0 < target) :
    RouteChartRequest assigned differential domains target :=
  let allowance := Budget.Aggregate.perTerm target word.length
  let requests := RouteChartRequests.build differential domains
    allowance
    (Budget.Aggregate.perTerm_positive positive _) assigned
  ⟨positive, allowance, rfl, requests, requests.index, rfl⟩

/-- The full original count-weighted sum of actual chart errors is strictly below the requested target. -/
theorem charge_lt (request : RouteChartRequest assigned
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    let changes := assigned.values fun edge route => route.sourceEdge.increment readings.values -
      CanonicalEdgeValues.edgeValuation mesh readings.values edge
    (changes.length : Fraction.Rational) * Gaussian.Norm.Sum.Basic.gaussianNormSqSum changes < target := by
  dsimp only
  rw [errors_length]
  have bound := request.requests.errors_bound (request.index_eq ▸ later) readings
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le word.length))
  apply paid.trans_lt
  rw [request.allowance_eq]
  exact Budget.Aggregate.count_mul_perTerm_lt request.positive _

/-- The retained discrepancy sum equals the original assigned-route sum minus the canonical word valuation. -/
private theorem errors_sum (assigned : MeshPathWalks.RouteSpine mesh word)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun edge route => route.sourceEdge.increment values -
      CanonicalEdgeValues.edgeValuation mesh values edge) =
      Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment values) -
        Sewing.SewingRetraction.wordValue
          (CanonicalEdgeValues.edgeValuation mesh values) word := by
  induction assigned with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - 0; ring1
  | cons first rest ih =>
    change (_ - _) + _ = (_ + _) - (_ + _)
    rw [ih]
    ring1

/-- The canonical original word valuation approximates its assigned-route readings within the retained whole-word
target. -/
theorem accurate (request : RouteChartRequest assigned
  differential domains target)
    {stage : Nat} (later : request.index ≤ stage) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential stage domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Gaussian.Norm.Basic.normSq (Sewing.SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values) word -
      Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
        readings.values)) < target := by
  have bounded := (Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le _).trans_lt (request.charge_lt later readings)
  rw [RouteChartRequest.errors_sum] at bounded
  rw [show Sewing.SewingRetraction.wordValue
    (CanonicalEdgeValues.edgeValuation mesh readings.values) word -
      Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
        readings.values) =
    -(Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
      readings.values) -
      Sewing.SewingRetraction.wordValue
        (CanonicalEdgeValues.edgeValuation mesh readings.values) word) by ring1,
    Gaussian.Norm.Basic.normSq_neg]
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bounded

/-- Select a new count-paid target on the GIVEN route/contact spine before observing its primitive bank.

The retained request supplies every original route and contact preparation.
Their genuine numerical budgets are reselected for the new allowance and
literal polynomial; the geometry and root caches are forwarded unchanged.
-/
@[expose] def rebudget {previous : Fraction.Rational} {previousPolynomial : Option (Ordinary curve.polynomial)}
    (request : RouteChartRequest assigned differential domains previous previousPolynomial)
    (target : Fraction.Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
    RouteChartRequest assigned differential domains target polynomial :=
  let allowance := Budget.Aggregate.perTerm target word.length
  let requests := request.requests.rebudget allowance
    (Budget.Aggregate.perTerm_positive positive word.length) polynomial
  ⟨positive, allowance, rfl, requests, requests.index, rfl⟩

/-- The retargeted chart requests are the actual rebudgeting of the original ordered spine. -/
theorem rebudget_requests {previous : Fraction.Rational}
    {previousPolynomial : Option (Ordinary curve.polynomial)}
    (request : RouteChartRequest assigned differential domains previous previousPolynomial)
    (target : Fraction.Rational) (positive : 0 < target)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
    (request.rebudget target positive polynomial).requests = request.requests.rebudget
      (Budget.Aggregate.perTerm target word.length)
      (Budget.Aggregate.perTerm_positive positive word.length) polynomial := by
  unfold rebudget
  rfl

/-- The actual post-bank contact products together with their once-read ordered discrepancies and sum.

The numerical list retains the literal signed chart changes on the SAME
triangle bank. The supplied primitive bank, its independent offsets and
stages, the whole request and triangle readings remain actual input data.
-/
@[expose] def Comparisons {polynomial : Option (Ordinary curve.polynomial)}
    (request : RouteChartRequest assigned differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial))
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) : Type _ :=
  {value : RouteChartRequest assigned differential domains target polynomial ×
      Face.PrimitiveData.FacePrimitiveBank differential stage domains
        (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial) ×
      TrianglePrimitiveReadings.TriangleReadings shared mesh // value = (request, shared, readings)} ×
  (Σ _cached : {value : request.requests.Comparisons shared // value = request.requests.compare shared},
  Σ errors : {value : List Gaussian.Basic.Canonical // value = assigned.values
      (fun edge route => route.sourceEdge.increment readings.values -
        CanonicalEdgeValues.edgeValuation mesh readings.values edge)},
  {value : Gaussian.Basic.Canonical // value = Gaussian.Norm.Sum.Basic.gaussianSum errors.val})

/-- Compare each retained chart contact once, then cache its actual ordered discrepancies and signed sum. -/
def compare {polynomial : Option (Ordinary curve.polynomial)}
    (request : RouteChartRequest assigned differential domains target polynomial) {stage : Nat}
    (shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial))
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) : request.Comparisons shared readings :=
  let cached : {value : request.requests.Comparisons shared // value = request.requests.compare shared} :=
    ⟨request.requests.compare shared, rfl⟩
  let errors : {value : List Gaussian.Basic.Canonical // value = assigned.values
      (fun edge route => route.sourceEdge.increment readings.values -
        CanonicalEdgeValues.edgeValuation mesh readings.values edge)} :=
    ⟨assigned.values (fun edge route => route.sourceEdge.increment readings.values -
      CanonicalEdgeValues.edgeValuation mesh readings.values edge), rfl⟩
  let total : {value : Gaussian.Basic.Canonical // value = Gaussian.Norm.Sum.Basic.gaussianSum errors.val} :=
    ⟨Gaussian.Norm.Sum.Basic.gaussianSum errors.val, rfl⟩
  ⟨⟨(request, shared, readings), rfl⟩, cached, errors, total⟩

namespace Comparisons

variable {polynomial : Option (Ordinary curve.polynomial)}
    {request : RouteChartRequest assigned differential domains target polynomial} {stage : Nat}
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    {readings : TrianglePrimitiveReadings.TriangleReadings shared mesh}
    (kept : request.Comparisons shared readings)

/-- Read the SAME original request, primitive bank and complete triangle readings. -/
@[expose] def inputs := kept.1.val

/-- The complete original numerical input owners remain the literal supplied caches. -/
theorem inputs_eq : kept.inputs = (request, shared, readings) := kept.1.property

/-- Read the once-executed original ordered contact comparison products. -/
@[expose] def cached : request.requests.Comparisons shared := kept.2.1.val

/-- The retained ordered cache has its one original post-bank factory. -/
theorem cached_eq : kept.cached = request.requests.compare shared := kept.2.1.property

/-- Read the actual ordered signed chart discrepancies without evaluating them again. -/
@[expose] def errors : List Gaussian.Basic.Canonical := kept.2.2.1.val

/-- The discrepancy list reads the original assigned routes and the SAME canonical triangle bank. -/
theorem errors_eq : kept.errors = assigned.values
    (fun edge route => route.sourceEdge.increment readings.values -
      CanonicalEdgeValues.edgeValuation mesh readings.values edge) := kept.2.2.1.property

/-- Read the cached signed discrepancy sum without another numerical fold. -/
@[expose] def sum : Gaussian.Basic.Canonical := kept.2.2.2.val

/-- The cached chart residual is the literal sum of its retained ordered changes. -/
theorem sum_eq : kept.sum = Gaussian.Norm.Sum.Basic.gaussianSum kept.errors := kept.2.2.2.property

/-- Every original route occurrence contributes one retained signed chart discrepancy. -/
theorem errors_length : kept.errors.length = word.length :=
  (congrArg List.length kept.errors_eq).trans (RouteChartRequests.errors_length readings.values assigned)

end Comparisons

/-- Actual retained common-model comparisons pay the whole canonical chart-change target.

Both occurrence-count factors are paid by the original positive per-term
allocation. The signed residual is the retained discrepancy list on the
same primitive/triangle bank, with no zero-gap or common-offset assumption.
-/
theorem comparison_accurate {polynomial : Option (Ordinary curve.polynomial)}
    (request : RouteChartRequest assigned differential domains target polynomial)
    {stage : Nat} (later : request.index ≤ stage)
    {shared : Face.PrimitiveData.FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    {readings : TrianglePrimitiveReadings.TriangleReadings shared mesh}
    (kept : request.Comparisons shared readings) :
    Gaussian.Norm.Basic.normSq (Sewing.SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values) word -
      Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
        readings.values)) < target := by
  have bound := request.requests.comparison_errors_bound (request.index_eq ▸ later) kept.cached readings
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bound
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le word.length))
  have strict : (word.length : Fraction.Rational) *
      Gaussian.Norm.Sum.Basic.gaussianNormSqSum kept.errors < target := by
    rewrite [kept.errors_eq]
    apply paid.trans_lt
    rewrite [request.allowance_eq]
    exact Budget.Aggregate.count_mul_perTerm_lt request.positive _
  have total := (Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le kept.errors).trans_lt (by
    rewrite [kept.errors_length]
    exact strict)
  rewrite [kept.errors_eq, RouteChartRequest.errors_sum] at total
  rewrite [show Sewing.SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation mesh readings.values) word -
      Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
        readings.values) =
      -(Gaussian.Norm.Sum.Basic.gaussianSum (assigned.values fun _ route => route.sourceEdge.increment
        readings.values) - Sewing.SewingRetraction.wordValue
          (CanonicalEdgeValues.edgeValuation mesh readings.values) word) by ring1,
    Gaussian.Norm.Basic.normSq_neg, Gaussian.Norm.Basic.normSq_eq_canonical]
  exact total

end RouteChartRequests.RouteChartRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

end
